'use strict';
const common = require('../common.js');
const fs = require('fs');
const path = require('path');

const searchStrings = [
  '@',
  'SQ',
  '10x',
  '--l',
  'Alice',
  'Gryphon',
  'Panther',
  'Ou est ma chatte?',
  'found it very',
  'among mad people',
  'neighbouring pool',
  'Soo--oop',
  'aaaaaaaaaaaaaaaaa',
  'venture to go near the house till she had brought herself down to',
  '</i> to the Caterpillar',
];

const bench = common.createBenchmark(main, {
  search: searchStrings,
  encoding: [
    'utf8', 'utf-8', 'UTF8', 'UTF-8',
    'ucs2', 'ucs-2', 'UCS2', 'UCS-2',
    'utf16le', 'utf-16le', 'UTF16LE', 'UTF-16LE',
    'latin1', 'LATIN1', 'binary', 'BINARY', 'base64', 'BASE64',
    'ascii', 'ASCII', 'hex', 'HEX',
  ],
  n: [1000]
});

function main({ n, search, encoding }) {
  const aliceBuffer = fs.readFileSync(
    path.resolve(__dirname, '../fixtures/alice.html')
  );

  bench.start();
  for (let i = 0; i < n; i++) {
    aliceBuffer.indexOf(search, 0, encoding);
  }
  bench.end(n);
}
