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
// Author of the Javascript rewrite: Tomáš Klapka <tomas@klapka.cz>

"use strict";

const bdds = require('./bdds')({ recursive:false });
const { bdds_rec, node } = bdds;

// debug functions
// JS enum emulated by freezing the object
const _enum = obj => Object.freeze(obj);

// traversing states enum
const s = _enum({ "LO": 1, "HI": 2, "OP": 3 });

// extending bdds class for non recursive algos
class bdds_non_rec extends bdds_rec {
	// apply unary (ie. op_exists(existentials))
	static apply_unary(b, x, r, op) {
		const get = id => op.eval(b, id); // evaluates the operator
		const parents = [];        // path from root to the current node
		let ts = s.LO;                    // current traversing state
		let n = get(x);                   // current node
		let nn = bdds_non_rec.F;          // new node
		let high = bdds_non_rec.F;        // last high leaf
		let low = bdds_non_rec.F;         // last low leaf
		do {                              // traversing the binary tree
			if (ts === s.LO) {                  // search low
				if(bdds_non_rec.leaf(n.lo)) {
					low = n.lo;    // remember last low leaf
					ts = s.HI;     // leaf, go search high
				} else {               // not a leaf
					parents.push(n); // store parent
					n = get(n.lo); // go low (and search low)
				}
			} else if (ts === s.HI) {      // search high
				if (bdds_non_rec.leaf(n.hi)) {
					high = n.hi;   // remember last high leaf
					ts = s.OP;     // leaf, do op
				} else {               // not a leaf
					parents.push(n); // store parent
					n = get(n.hi); // go high
					ts = s.LO;     // and search low
				}
			} else if (ts === s.OP) {     // do op and go UP
				nn = r.add(new node(n.v, high, low));
				if (parents.length === 0)
					break; // we are back at the top -> break inf. loop
				n = parents.pop(); // go up
				if (nn === n.lo) { // if we operated on low
					low = nn; ts = s.HI;  // set new low and go high
				} else {           // else we operated on high already
					high = nn; ts = s.OP; // set new high and go op
				}
			}
		} while (true);
		return nn; // return the last new node
	}
}

module.exports = bdds_non_rec;
