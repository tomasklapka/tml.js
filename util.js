// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.

// This is a Javascript rewrite of TML by Tomáš Klapka <tomas@klapka.cz>

const { spawn } = require('child_process');
const { writeFileSync } = require('fs');
const path = require('path');

// internal counters for dot files nad graphvizs
const _counters = { gv:  0, dot: 0 };

// converts bdd to dot, svg and/or png
function bdd_out(b, dict, options = {}) {
  options.svg = options.hasOwnProperty('svg') ? options.svg : true;
  options.png = options.hasOwnProperty('png') ? options.png : false;
  const dot = bdd_to_dot(b, dict, options);
  if (options.svg) graphviz(dot, 'svg');
  if (options.png) graphviz(dot, 'png');
}

// converts bdd to dot (optionally saves the dot file)
function bdd_to_dot(b, dict, options = {}) {
  options.dot = options.hasOwnProperty('dot') ? options.dot : false;
  const nodes = b.V;
  let r = `graph bdd${++_counters.dot}\n{\n`;
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    r += `    n${i} `;
    if (n.v === 0 && n.hi === 0) {
      r += `[label="0 F 0:0/0",shape=box];\n`;
    } else if (n.v === 0 && n.hi === 1) {
      r += `[label="1 T 0:1/1",shape=box];\n`;
    } else {
      r += `[label="${i} ${dict.get(n.v)||'*'} ${n.key}",shape=circle];\n`;
    }
  }
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.v > 0) {
      r += `    n${i} -- n${n.lo} [label="F",style=dashed];\n`
        +  `    n${i} -- n${n.hi} [label="T"];\n`;
    }
  }
  r += `}\n`;
  if (options.dot) {
    writeFileSync(path.resolve(__dirname, `bdd_${_counters.dot}.dot`), r);
  }
  return r;
}

// draws dot into svg or png
function graphviz(dot, format = 'svg') {
  return new Promise((resolve, reject) => {
    const gv = spawn('dot', [ '-T'+format, `-obdd_${_counters.dot}.${format}` ]);
    gv.on('error', (err) => {
      console.log('error: ', err);
      reject(err);
    });
    gv.on('close', (code) => {
      if (code == 0) {
        resolve(true);
      } else {
        reject(`graphviz error:${code}`)
      }
    });
    gv.stdin.write(dot);
    gv.stdin.end();
  });
}

module.exports = {
  bdd_out, bdd_to_dot, graphviz
}