'use strict';
const common = require('../common');
const assert = require('assert');
const StreamWrap = require('internal/wrap_js_stream');
const { PassThrough } = require('stream');
const { Socket } = require('net');

{
  const wrap = new StreamWrap(new PassThrough());
  assert(wrap instanceof Socket);
  wrap.on('data', common.mustCall((d) => assert.strictEqual(`${d}`, 'foo')));
  wrap.on('end', common.mustNotCall());
  wrap.write('foo');
}

{
  const wrap = new StreamWrap(new PassThrough());
  assert(wrap instanceof Socket);
  wrap.on('data', common.mustCall((d) => assert.strictEqual(`${d}`, 'foo')));
  wrap.on('end', common.mustCall());
  wrap.end('foo');
}
