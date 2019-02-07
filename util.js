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

const options = {
  bdd_to_svg: false,
  bdd_to_png: false
};

const counters = {
  gv:  0, // graphviz
  dot: 0  // dots
};

function bdd_out(b, db, dict) {
  const dot = bdd_to_dot(b, db, dict);
  if (options.bdd_to_svg) graphviz(dot, 'svg');
  if (options.bdd_to_png) graphviz(dot, 'png');
}

function bdd_to_dot(b, db, dict) {
  const nodes = b.V;
  let r = [ `graph bdd${++counters.dot} {` ];
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    r.push(`n${i}`);
    if (n.v === 0 && n.hi === 0) {
      r.push('[label=0,shape=box];');
    } else if (n.v === 0 && n.hi === 1) {
      r.push('[label=1,shape=box];');
    } else {
      r.push(`[label="${i} ${dict.get(n.v)||'*'} ${n.key}",shape=circle];`)
    }
  }
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.v > 0) {
      r.push(`n${i} -- n${n.lo} [label="F",style=dashed]; n${i} -- n${n.hi} [label="T"];`)
    }
  }
  r.push('}');
  return r.join(" ");
}

function graphviz(dot, format = 'svg') {
  return new Promise((resolve, reject) => {
    const gv = spawn('dot', [ '-T'+format, `-obdd_${++counters.gv}.${format}` ]);
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