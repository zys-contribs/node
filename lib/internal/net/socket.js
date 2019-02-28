'use strict';

const stream = require('stream');
const util = require('util');
const {
  isIP,
  isLegalPort,
  normalizedArgsSymbol,
  makeSyncWrite
} = require('internal/net');
const assert = require('internal/assert');
const {
  UV_EADDRINUSE
} = internalBinding('uv');

const { Buffer } = require('buffer');
const TTYWrap = internalBinding('tty_wrap');
const { ShutdownWrap } = internalBinding('stream_wrap');
const {
  TCP,
  TCPConnectWrap,
  constants: TCPConstants
} = internalBinding('tcp_wrap');
const {
  Pipe,
  PipeConnectWrap,
  constants: PipeConstants
} = internalBinding('pipe_wrap');
const {
  newAsyncId,
  defaultTriggerAsyncIdScope,
  symbols: { async_id_symbol, owner_symbol }
} = require('internal/async_hooks');
const {
  createWriteWrap,
  writevGeneric,
  writeGeneric,
  onStreamRead,
  kAfterAsyncWrite,
  kUpdateTimer,
  setStreamTimeout
} = require('internal/stream_base_commons');
const {
  codes: {
    ERR_INVALID_ADDRESS_FAMILY,
    ERR_INVALID_ARG_TYPE,
    ERR_INVALID_FD_TYPE,
    ERR_INVALID_IP_ADDRESS,
    ERR_SOCKET_BAD_PORT,
    ERR_SOCKET_CLOSED
  },
  errnoException,
  exceptionWithHostPort,
} = require('internal/errors');
const { validateInt32, validateString } = require('internal/validators');
const kLastWriteQueueSize = Symbol('lastWriteQueueSize');

// Lazy loaded to improve startup performance.
let dns;

const { kTimeout } = require('internal/timers');

function noop() {}

function createHandle(fd, is_server) {
  validateInt32(fd, 'fd', 0);
  const type = TTYWrap.guessHandleType(fd);
  if (type === 'PIPE') {
    return new Pipe(
      is_server ? PipeConstants.SERVER : PipeConstants.SOCKET
    );
  }

  if (type === 'TCP') {
    return new TCP(
      is_server ? TCPConstants.SERVER : TCPConstants.SOCKET
    );
  }

  throw new ERR_INVALID_FD_TYPE(type);
}

function getNewAsyncId(handle) {
  return (!handle || typeof handle.getAsyncId !== 'function') ?
    newAsyncId() : handle.getAsyncId();
}


const debug = util.debuglog('net');

function isPipeName(s) {
  return typeof s === 'string' && toNumber(s) === false;
}


// Returns an array [options, cb], where options is an object,
// cb is either a function or null.
// Used to normalize arguments of Socket.prototype.connect() and
// Server.prototype.listen(). Possible combinations of parameters:
//   (options[...][, cb])
//   (path[...][, cb])
//   ([port][, host][...][, cb])
// For Socket.prototype.connect(), the [...] part is ignored
// For Server.prototype.listen(), the [...] part is [, backlog]
// but will not be handled here (handled in listen())
function normalizeArgs(args) {
  var arr;

  if (args.length === 0) {
    arr = [{}, null];
    arr[normalizedArgsSymbol] = true;
    return arr;
  }

  const arg0 = args[0];
  var options = {};
  if (typeof arg0 === 'object' && arg0 !== null) {
    // (options[...][, cb])
    options = arg0;
  } else if (isPipeName(arg0)) {
    // (path[...][, cb])
    options.path = arg0;
  } else {
    // ([port][, host][...][, cb])
    options.port = arg0;
    if (args.length > 1 && typeof args[1] === 'string') {
      options.host = args[1];
    }
  }

  var cb = args[args.length - 1];
  if (typeof cb !== 'function')
    arr = [options, null];
  else
    arr = [options, cb];

  arr[normalizedArgsSymbol] = true;
  return arr;
}


// Called when creating new Socket, or when re-using a closed Socket
function initSocketHandle(self) {
  self._undestroy();
  self._sockname = null;

  // Handle creation may be deferred to bind() or connect() time.
  if (self._handle) {
    self._handle[owner_symbol] = self;
    self._handle.onread = onStreamRead;
    self[async_id_symbol] = getNewAsyncId(self._handle);
  }
}

const kBytesRead = Symbol('kBytesRead');
const kBytesWritten = Symbol('kBytesWritten');

function Socket(options) {
  if (!(this instanceof Socket)) return new Socket(options);

  this.connecting = false;
  // Problem with this is that users can supply their own handle, that may not
  // have _handle.getAsyncId(). In this case an[async_id_symbol] should
  // probably be supplied by async_hooks.
  this[async_id_symbol] = -1;
  this._hadError = false;
  this._handle = null;
  this._parent = null;
  this._host = null;
  this[kLastWriteQueueSize] = 0;
  this[kTimeout] = null;

  if (typeof options === 'number')
    options = { fd: options }; // Legacy interface.
  else
    options = { ...options };

  options.readable = options.readable || false;
  options.writable = options.writable || false;
  const { allowHalfOpen } = options;

  // Prevent the "no-half-open enforcer" from being inherited from `Duplex`.
  options.allowHalfOpen = true;
  // For backwards compat do not emit close on destroy.
  options.emitClose = false;
  // Handle strings directly.
  options.decodeStrings = false;
  stream.Duplex.call(this, options);

  // Default to *not* allowing half open sockets.
  this.allowHalfOpen = Boolean(allowHalfOpen);

  if (options.handle) {
    this._handle = options.handle; // private
    this[async_id_symbol] = getNewAsyncId(this._handle);
  } else if (options.fd !== undefined) {
    const { fd } = options;
    let err;

    // createHandle will throw ERR_INVALID_FD_TYPE if `fd` is not
    // a valid `PIPE` or `TCP` descriptor
    this._handle = createHandle(fd, false);

    err = this._handle.open(fd);

    // While difficult to fabricate, in some architectures
    // `open` may return an error code for valid file descriptors
    // which cannot be opened. This is difficult to test as most
    // un-openable fds will throw on `createHandle`
    if (err)
      throw errnoException(err, 'open');

    this[async_id_symbol] = this._handle.getAsyncId();

    if ((fd === 1 || fd === 2) &&
        (this._handle instanceof Pipe) &&
        process.platform === 'win32') {
      // Make stdout and stderr blocking on Windows
      err = this._handle.setBlocking(true);
      if (err)
        throw errnoException(err, 'setBlocking');

      this._writev = null;
      this._write = makeSyncWrite(fd);
      // makeSyncWrite adjusts this value like the original handle would, so
      // we need to let it do that by turning it into a writable, own property.
      Object.defineProperty(this._handle, 'bytesWritten', {
        value: 0, writable: true
      });
    }
  }

  // shut down the socket when we're finished with it.
  this.on('end', onReadableStreamEnd);

  initSocketHandle(this);

  this._pendingData = null;
  this._pendingEncoding = '';

  // If we have a handle, then start the flow of data into the
  // buffer.  if not, then this will happen when we connect
  if (this._handle && options.readable !== false) {
    if (options.pauseOnCreate) {
      // stop the handle from reading and pause the stream
      this._handle.reading = false;
      this._handle.readStop();
      this.readableFlowing = false;
    } else if (!options.manualStart) {
      this.read(0);
    }
  }

  // Reserve properties
  this.server = null;
  this._server = null;

  // Used after `.destroy()`
  this[kBytesRead] = 0;
  this[kBytesWritten] = 0;
}
util.inherits(Socket, stream.Duplex);

// Refresh existing timeouts.
Socket.prototype._unrefTimer = function _unrefTimer() {
  for (var s = this; s !== null; s = s._parent) {
    if (s[kTimeout])
      s[kTimeout].refresh();
  }
};


// The user has called .end(), and all the bytes have been
// sent out to the other side.
Socket.prototype._final = function(cb) {
  // If still connecting - defer handling `_final` until 'connect' will happen
  if (this.pending) {
    debug('_final: not yet connected');
    return this.once('connect', () => this._final(cb));
  }

  if (!this._handle)
    return cb();

  debug('_final: not ended, call shutdown()');

  var req = new ShutdownWrap();
  req.oncomplete = afterShutdown;
  req.handle = this._handle;
  req.callback = cb;
  var err = this._handle.shutdown(req);

  if (err === 1)  // synchronous finish
    return afterShutdown.call(req, 0);
  else if (err !== 0)
    return this.destroy(errnoException(err, 'shutdown'));
};


function afterShutdown(status) {
  var self = this.handle[owner_symbol];

  debug('afterShutdown destroyed=%j', self.destroyed,
        self._readableState);

  this.callback();

  // callback may come after call to destroy.
  if (self.destroyed)
    return;

  if (!self.readable || self._readableState.ended) {
    debug('readableState ended, destroying');
    self.destroy();
  }
}

// Provide a better error message when we call end() as a result
// of the other side sending a FIN.  The standard 'write after end'
// is overly vague, and makes it seem like the user's code is to blame.
function writeAfterFIN(chunk, encoding, cb) {
  if (typeof encoding === 'function') {
    cb = encoding;
    encoding = null;
  }

  // eslint-disable-next-line no-restricted-syntax
  var er = new Error('This socket has been ended by the other party');
  er.code = 'EPIPE';
  process.nextTick(emitErrorNT, this, er);
  if (typeof cb === 'function') {
    defaultTriggerAsyncIdScope(this[async_id_symbol], process.nextTick, cb, er);
  }
}

Socket.prototype.setTimeout = setStreamTimeout;


Socket.prototype._onTimeout = function() {
  const handle = this._handle;
  const lastWriteQueueSize = this[kLastWriteQueueSize];
  if (lastWriteQueueSize > 0 && handle) {
    // `lastWriteQueueSize !== writeQueueSize` means there is
    // an active write in progress, so we suppress the timeout.
    const { writeQueueSize } = handle;
    if (lastWriteQueueSize !== writeQueueSize) {
      this[kLastWriteQueueSize] = writeQueueSize;
      this._unrefTimer();
      return;
    }
  }
  debug('_onTimeout');
  this.emit('timeout');
};


Socket.prototype.setNoDelay = function(enable) {
  if (!this._handle) {
    this.once('connect',
              enable ? this.setNoDelay : () => this.setNoDelay(enable));
    return this;
  }

  // Backwards compatibility: assume true when `enable` is omitted
  if (this._handle.setNoDelay)
    this._handle.setNoDelay(enable === undefined ? true : !!enable);

  return this;
};


Socket.prototype.setKeepAlive = function(setting, msecs) {
  if (!this._handle) {
    this.once('connect', () => this.setKeepAlive(setting, msecs));
    return this;
  }

  if (this._handle.setKeepAlive)
    this._handle.setKeepAlive(setting, ~~(msecs / 1000));

  return this;
};


Socket.prototype.address = function() {
  return this._getsockname();
};


Object.defineProperty(Socket.prototype, '_connecting', {
  get: function() {
    return this.connecting;
  }
});

Object.defineProperty(Socket.prototype, 'pending', {
  get() {
    return !this._handle || this.connecting;
  },
  configurable: true
});


Object.defineProperty(Socket.prototype, 'readyState', {
  get: function() {
    if (this.connecting) {
      return 'opening';
    } else if (this.readable && this.writable) {
      return 'open';
    } else if (this.readable && !this.writable) {
      return 'readOnly';
    } else if (!this.readable && this.writable) {
      return 'writeOnly';
    } else {
      return 'closed';
    }
  }
});


Object.defineProperty(Socket.prototype, 'bufferSize', {
  get: function() {
    if (this._handle) {
      return this[kLastWriteQueueSize] + this.writableLength;
    }
  }
});

Object.defineProperty(Socket.prototype, kUpdateTimer, {
  get: function() {
    return this._unrefTimer;
  }
});


// Just call handle.readStart until we have enough in the buffer
Socket.prototype._read = function(n) {
  debug('_read');

  if (this.connecting || !this._handle) {
    debug('_read wait for connection');
    this.once('connect', () => this._read(n));
  } else if (!this._handle.reading) {
    // not already reading, start the flow
    debug('Socket._read readStart');
    this._handle.reading = true;
    var err = this._handle.readStart();
    if (err)
      this.destroy(errnoException(err, 'read'));
  }
};


Socket.prototype.end = function(data, encoding, callback) {
  stream.Duplex.prototype.end.call(this, data, encoding, callback);
  DTRACE_NET_STREAM_END(this);
  return this;
};


// Called when the 'end' event is emitted.
function onReadableStreamEnd() {
  if (!this.allowHalfOpen) {
    this.write = writeAfterFIN;
    if (this.writable)
      this.end();
  }
  maybeDestroy(this);
}

// Call whenever we set writable=false or readable=false
function maybeDestroy(socket) {
  if (!socket.readable &&
      !socket.writable &&
      !socket.destroyed &&
      !socket.connecting &&
      !socket.writableLength) {
    socket.destroy();
  }
}


Socket.prototype.destroySoon = function() {
  if (this.writable)
    this.end();

  if (this._writableState.finished)
    this.destroy();
  else
    this.once('finish', this.destroy);
};


Socket.prototype._destroy = function(exception, cb) {
  debug('destroy');

  this.connecting = false;

  this.readable = this.writable = false;

  for (var s = this; s !== null; s = s._parent) {
    clearTimeout(s[kTimeout]);
  }

  debug('close');
  if (this._handle) {
    if (this !== process.stderr)
      debug('close handle');
    var isException = exception ? true : false;
    // `bytesRead` and `kBytesWritten` should be accessible after `.destroy()`
    this[kBytesRead] = this._handle.bytesRead;
    this[kBytesWritten] = this._handle.bytesWritten;

    this._handle.close(() => {
      debug('emit close');
      this.emit('close', isException);
    });
    this._handle.onread = noop;
    this._handle = null;
    this._sockname = null;
  }

  cb(exception);

  if (this._server) {
    debug('has server');
    this._server._connections--;
    if (this._server._emitCloseIfDrained) {
      this._server._emitCloseIfDrained();
    }
  }
};


Socket.prototype._getpeername = function() {
  if (!this._peername) {
    if (!this._handle || !this._handle.getpeername) {
      return {};
    }
    var out = {};
    var err = this._handle.getpeername(out);
    if (err) return {};  // FIXME(bnoordhuis) Throw?
    this._peername = out;
  }
  return this._peername;
};

function protoGetter(name, callback) {
  Object.defineProperty(Socket.prototype, name, {
    configurable: false,
    enumerable: true,
    get: callback
  });
}

protoGetter('bytesRead', function bytesRead() {
  return this._handle ? this._handle.bytesRead : this[kBytesRead];
});

protoGetter('remoteAddress', function remoteAddress() {
  return this._getpeername().address;
});

protoGetter('remoteFamily', function remoteFamily() {
  return this._getpeername().family;
});

protoGetter('remotePort', function remotePort() {
  return this._getpeername().port;
});


Socket.prototype._getsockname = function() {
  if (!this._handle || !this._handle.getsockname) {
    return {};
  }
  if (!this._sockname) {
    var out = {};
    var err = this._handle.getsockname(out);
    if (err) return {};  // FIXME(bnoordhuis) Throw?
    this._sockname = out;
  }
  return this._sockname;
};


protoGetter('localAddress', function localAddress() {
  return this._getsockname().address;
});


protoGetter('localPort', function localPort() {
  return this._getsockname().port;
});


Socket.prototype[kAfterAsyncWrite] = function() {
  this[kLastWriteQueueSize] = 0;
};

Socket.prototype._writeGeneric = function(writev, data, encoding, cb) {
  // If we are still connecting, then buffer this for later.
  // The Writable logic will buffer up any more writes while
  // waiting for this one to be done.
  if (this.connecting) {
    this._pendingData = data;
    this._pendingEncoding = encoding;
    this.once('connect', function connect() {
      this._writeGeneric(writev, data, encoding, cb);
    });
    return;
  }
  this._pendingData = null;
  this._pendingEncoding = '';

  if (!this._handle) {
    this.destroy(new ERR_SOCKET_CLOSED(), cb);
    return false;
  }

  this._unrefTimer();

  var req = createWriteWrap(this._handle);
  if (writev)
    writevGeneric(this, req, data, cb);
  else
    writeGeneric(this, req, data, encoding, cb);
  if (req.async)
    this[kLastWriteQueueSize] = req.bytes;
};

Socket.prototype._writev = function(chunks, cb) {
  this._writeGeneric(true, chunks, '', cb);
};


Socket.prototype._write = function(data, encoding, cb) {
  this._writeGeneric(false, data, encoding, cb);
};


// Legacy alias. Having this is probably being overly cautious, but it doesn't
// really hurt anyone either. This can probably be removed safely if desired.
protoGetter('_bytesDispatched', function _bytesDispatched() {
  return this._handle ? this._handle.bytesWritten : this[kBytesWritten];
});


protoGetter('bytesWritten', function bytesWritten() {
  var bytes = this._bytesDispatched;
  const state = this._writableState;
  const data = this._pendingData;
  const encoding = this._pendingEncoding;

  if (!state)
    return undefined;

  this.writableBuffer.forEach(function(el) {
    if (el.chunk instanceof Buffer)
      bytes += el.chunk.length;
    else
      bytes += Buffer.byteLength(el.chunk, el.encoding);
  });

  if (Array.isArray(data)) {
    // Was a writev, iterate over chunks to get total length
    for (var i = 0; i < data.length; i++) {
      const chunk = data[i];

      if (data.allBuffers || chunk instanceof Buffer)
        bytes += chunk.length;
      else
        bytes += Buffer.byteLength(chunk.chunk, chunk.encoding);
    }
  } else if (data) {
    // Writes are either a string or a Buffer.
    if (typeof data !== 'string')
      bytes += data.length;
    else
      bytes += Buffer.byteLength(data, encoding);
  }

  return bytes;
});


function checkBindError(err, port, handle) {
  // EADDRINUSE may not be reported until we call listen() or connect().
  // To complicate matters, a failed bind() followed by listen() or connect()
  // will implicitly bind to a random port. Ergo, check that the socket is
  // bound to the expected port before calling listen() or connect().
  //
  // FIXME(bnoordhuis) Doesn't work for pipe handles, they don't have a
  // getsockname() method. Non-issue for now, the cluster module doesn't
  // really support pipes anyway.
  if (err === 0 && port > 0 && handle.getsockname) {
    var out = {};
    err = handle.getsockname(out);
    if (err === 0 && port !== out.port) {
      debug(`checkBindError, bound to ${out.port} instead of ${port}`);
      err = UV_EADDRINUSE;
    }
  }
  return err;
}


function internalConnect(
  self, address, port, addressType, localAddress, localPort, flags) {
  // TODO return promise from Socket.prototype.connect which
  // wraps _connectReq.

  assert(self.connecting);

  var err;

  if (localAddress || localPort) {
    if (addressType === 4) {
      localAddress = localAddress || '0.0.0.0';
      err = self._handle.bind(localAddress, localPort);
    } else { // addressType === 6
      localAddress = localAddress || '::';
      err = self._handle.bind6(localAddress, localPort, flags);
    }
    debug('binding to localAddress: %s and localPort: %d (addressType: %d)',
          localAddress, localPort, addressType);

    err = checkBindError(err, localPort, self._handle);
    if (err) {
      const ex = exceptionWithHostPort(err, 'bind', localAddress, localPort);
      self.destroy(ex);
      return;
    }
  }

  if (addressType === 6 || addressType === 4) {
    const req = new TCPConnectWrap();
    req.oncomplete = afterConnect;
    req.address = address;
    req.port = port;
    req.localAddress = localAddress;
    req.localPort = localPort;

    if (addressType === 4)
      err = self._handle.connect(req, address, port);
    else
      err = self._handle.connect6(req, address, port);
  } else {
    const req = new PipeConnectWrap();
    req.address = address;
    req.oncomplete = afterConnect;

    err = self._handle.connect(req, address, afterConnect);
  }

  if (err) {
    var sockname = self._getsockname();
    var details;

    if (sockname) {
      details = sockname.address + ':' + sockname.port;
    }

    const ex = exceptionWithHostPort(err, 'connect', address, port, details);
    self.destroy(ex);
  }
}


Socket.prototype.connect = function(...args) {
  let normalized;
  // If passed an array, it's treated as an array of arguments that have
  // already been normalized (so we don't normalize more than once). This has
  // been solved before in https://github.com/nodejs/node/pull/12342, but was
  // reverted as it had unintended side effects.
  if (Array.isArray(args[0]) && args[0][normalizedArgsSymbol]) {
    normalized = args[0];
  } else {
    normalized = normalizeArgs(args);
  }
  var options = normalized[0];
  var cb = normalized[1];

  if (this.write !== Socket.prototype.write)
    this.write = Socket.prototype.write;

  if (this.destroyed) {
    this._undestroy();
    this._handle = null;
    this._peername = null;
    this._sockname = null;
  }

  const { path } = options;
  var pipe = !!path;
  debug('pipe', pipe, path);

  if (!this._handle) {
    this._handle = pipe ?
      new Pipe(PipeConstants.SOCKET) :
      new TCP(TCPConstants.SOCKET);
    initSocketHandle(this);
  }

  if (cb !== null) {
    this.once('connect', cb);
  }

  this._unrefTimer();

  this.connecting = true;
  this.writable = true;

  if (pipe) {
    validateString(path, 'options.path');
    defaultTriggerAsyncIdScope(
      this[async_id_symbol], internalConnect, this, path
    );
  } else {
    lookupAndConnect(this, options);
  }
  return this;
};


function lookupAndConnect(self, options) {
  var { port, localAddress, localPort } = options;
  var host = options.host || 'localhost';

  if (localAddress && !isIP(localAddress)) {
    throw new ERR_INVALID_IP_ADDRESS(localAddress);
  }

  if (localPort && typeof localPort !== 'number') {
    throw new ERR_INVALID_ARG_TYPE('options.localPort', 'number', localPort);
  }

  if (typeof port !== 'undefined') {
    if (typeof port !== 'number' && typeof port !== 'string') {
      throw new ERR_INVALID_ARG_TYPE('options.port',
                                     ['number', 'string'], port);
    }
    if (!isLegalPort(port)) {
      throw new ERR_SOCKET_BAD_PORT(port);
    }
  }
  port |= 0;

  // If host is an IP, skip performing a lookup
  var addressType = isIP(host);
  if (addressType) {
    defaultTriggerAsyncIdScope(self[async_id_symbol], process.nextTick, () => {
      if (self.connecting)
        defaultTriggerAsyncIdScope(
          self[async_id_symbol],
          internalConnect,
          self, host, port, addressType, localAddress, localPort
        );
    });
    return;
  }

  if (options.lookup && typeof options.lookup !== 'function')
    throw new ERR_INVALID_ARG_TYPE('options.lookup',
                                   'Function', options.lookup);


  if (dns === undefined) dns = require('dns');
  var dnsopts = {
    family: options.family,
    hints: options.hints || 0
  };

  if (process.platform !== 'win32' &&
      dnsopts.family !== 4 &&
      dnsopts.family !== 6 &&
      dnsopts.hints === 0) {
    dnsopts.hints = dns.ADDRCONFIG;
  }

  debug('connect: find host', host);
  debug('connect: dns options', dnsopts);
  self._host = host;
  var lookup = options.lookup || dns.lookup;
  defaultTriggerAsyncIdScope(self[async_id_symbol], function() {
    lookup(host, dnsopts, function emitLookup(err, ip, addressType) {
      self.emit('lookup', err, ip, addressType, host);

      // It's possible we were destroyed while looking this up.
      // XXX it would be great if we could cancel the promise returned by
      // the look up.
      if (!self.connecting) return;

      if (err) {
        // net.createConnection() creates a net.Socket object and
        // immediately calls net.Socket.connect() on it (that's us).
        // There are no event listeners registered yet so defer the
        // error event to the next tick.
        err.host = options.host;
        err.port = options.port;
        err.message = err.message + ' ' + options.host + ':' + options.port;
        process.nextTick(connectErrorNT, self, err);
      } else if (addressType !== 4 && addressType !== 6) {
        err = new ERR_INVALID_ADDRESS_FAMILY(addressType);
        err.host = options.host;
        err.port = options.port;
        err.message = err.message + ' ' + options.host + ':' + options.port;
        process.nextTick(connectErrorNT, self, err);
      } else {
        self._unrefTimer();
        defaultTriggerAsyncIdScope(
          self[async_id_symbol],
          internalConnect,
          self, ip, port, addressType, localAddress, localPort
        );
      }
    });
  });
}


function connectErrorNT(self, err) {
  self.destroy(err);
}


Socket.prototype.ref = function() {
  if (!this._handle) {
    this.once('connect', this.ref);
    return this;
  }

  if (typeof this._handle.ref === 'function') {
    this._handle.ref();
  }

  return this;
};


Socket.prototype.unref = function() {
  if (!this._handle) {
    this.once('connect', this.unref);
    return this;
  }

  if (typeof this._handle.unref === 'function') {
    this._handle.unref();
  }

  return this;
};


function afterConnect(status, handle, req, readable, writable) {
  var self = handle[owner_symbol];

  // callback may come after call to destroy
  if (self.destroyed) {
    return;
  }

  debug('afterConnect');

  assert(self.connecting);
  self.connecting = false;
  self._sockname = null;

  if (status === 0) {
    self.readable = readable;
    if (!self._writableState.ended)
      self.writable = writable;
    self._unrefTimer();

    self.emit('connect');
    self.emit('ready');

    // start the first read, or get an immediate EOF.
    // this doesn't actually consume any bytes, because len=0.
    if (readable && !self.isPaused())
      self.read(0);

  } else {
    self.connecting = false;
    var details;
    if (req.localAddress && req.localPort) {
      details = req.localAddress + ':' + req.localPort;
    }
    var ex = exceptionWithHostPort(status,
                                   'connect',
                                   req.address,
                                   req.port,
                                   details);
    if (details) {
      ex.localAddress = req.localAddress;
      ex.localPort = req.localPort;
    }
    self.destroy(ex);
  }
}


function emitErrorNT(self, err) {
  self.emit('error', err);
}

function toNumber(x) { return (x = Number(x)) >= 0 ? x : false; }

module.exports = {
  checkBindError,
  Socket,
};
