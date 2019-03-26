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

//## include "__common.h"

const { err_proof } = require('./messages');
const { node, bdd } = require('./bdd');
const { query, bdd_and_eq, extents } = require('./query');

function fact(v, bits) {
	ID_TRC('fact');
	DBG(__pfp(`fact(v: ${v}, bits: ${bits})`));
	let r = bdd.T;
	const m = {};
	for (let j = 0; j !== v.length - 1; ++j) {
		if (v[j+1] >= 0) from_int_and(v[j+1], bits, j * bits, r);
		else if (!m.hasOwnProperty(v[j+1])) m[v[j+1]] = j;
		else {
			const pos = m[v[j+1]] * bits;
			for (let b = 0; b !== bits; ++b) {
				r = bdd.and(r, from_eq(j*bits+b, pos+b));
			}
		}
	}
	return v[0] < 0
		? bdd.and_not(bdd.T, r)
		: r;
}

// a P-DATALOG rule in bdd form
class rule {
	constructor(v, bits, dsz, proof, context) {
		DBG(__rule(`new rule() bits: ${bits}, dsz: ${dsz}, v.size: ${v.length} v:`, v));
		const pad = context.pad;
		const openp = context.openp;
		const closep = context.closep;
		this.context = context;
		this.vars_arity = null;
		this.q = []; // array of queries
		this.p = new Set();
		this.proof1 = [];
		this.proof2 = new Set();
		this.varmap = this.get_varmap(v);
		this.ae = new bdd_and_eq(bits, v[0]);
		this.ext = this.get_extents(v, bits, dsz);
		this.neg = v[1][0] < 0;
		const ar = v[0].length - 1;
		v[0].shift();
		for (let i = 0; i !== v.length - 1; ++i) {
			const perm = Array(bits * ar);
			for (let j = 0; j !== bits*ar; ++j) perm[j] = j;
			for (let j = 0; j !== ar; ++j) {
				const t = v[i+1][j+1];
				if (t < 0) for (let b = 0; b !== bits; ++b) {
					perm[b+j*bits] = b+this.varmap.get(t)*bits;
				}
			}
			this.q[this.q.length] = new query(bits, v[i+1], perm);
		}

		if (!proof) return;
		for (let i = 0; i !== v.length; ++i) {
			if (v[i][0] < 0) throw new Error(err_proof);
			else if (i > 0) v[i].shift();
		}
		const vs = new Set();
		for (let i = 0; i !== v[0].length; ++i) { const t = v[0][i];
			if (t < 0) vs.add(t);
		}
		const vars = [ 1 ].concat(v[0]);
		const prule = [ 1, openp ];
		const bprule = [ 1, openp ];
		DBG(__rule(`v.tail:`, v.slice(1)));
		for (let i = 1; i !== v.length; ++i) {
			for (let j = 0; j !== v[i].length; ++j) { const t = v[i][j];
				if (t < 0 && !vs.has(t)) {
					vs.add(t);
					vars[vars.length] = t;
					DBG(__proof(`vs: `, vs));
				}
			}
		}
		for (let i = 0; i !== v.length; ++i) {
			prule[prule.length] = v[i];
			bprule[bprule.length] = v[i];
		}
		prule[prule.length] = closep;
		bprule[bprule.length] = closep;

		DBG(__proof(`vs: `, vs));
		DBG(__proof(`vars: `, vars));
		//DBG(process.exit(0));
		this.proof1 = [ prule,  vars ];
		this.proof2 = new Set();
		const r = [ bprule, prule, [ 1, openp ].concat(v[0], [ closep ]) ];
		for (let i = 1; i !== v.length; ++i) {
			this.proof2.add(
				[ [ 1, openp ].concat(v[i], [ closep ]), prule, r[2] ]);
			DBG(__proof(`proof2[${i-1}]: ${this.proof2.length}`, this.proof2));
			r[r.length] = [ 1, openp ].concat(v[i], [ closep ]);
			DBG(__proof(`r${i}: `, r));
		}
		this.proof2.add(r);
		DBG(__proof(`proof1: (length: ${this.proof1.length})`, this.proof1));
		DBG(__proof(`proof2: (length: ${this.proof2.length})`, this.proof2));
	}

	get_varmap(v) {
		const m = new Map();
		const ar = v[0].length - 1;
		let k = ar;
		for (let j = 0; j !== ar; ++j) { const t = v[0][j+1];
			if (t < 0 && !m.has(t)) m.set(t, j);
		}
		for (let i = 0; i !== v.length - 1; ++i) {
			for (let j = 0; j !== ar; ++j) { const t = v[i+1][j+1];
				if (t < 0 && !m.has(t)) m.set(t, k++);
			}
		}
		this.vars_arity = k;
		return m;
	}

	get_extents(v, bits, dsz) {
		const ar = v[0].length - 1;
		let l = 0;
		const excl = [ this.context.pad, this.context.openp, this.context.closep ];
		const lt = Array(ar).fill(0);
		const gt = Array(ar).fill(0);
		const succ = Array(ar).fill(0);
		const pred = Array(ar).fill(0);
		const dom = [];
		for (let value of this.varmap.values()) {
			dom[dom.length] = value;
			l = Math.max(l, value);
		}
		dom[dom.length] = l + 1;
		for (let n = 1; n !== v.length; ++n) {
			if (v[n][0] < 0) {
				for (let k = 0; k !== ar; ++k) {
					lt[this.varmap[v[n][k+1]]] = dsz;
				}
			}
		}
		return new extents(bits, this.vars_arity, ar*bits, dom, dsz, 0, excl, lt, gt, succ, pred);
	}

	fwd(db, bits, ar) {
		DBG(__pfp(`rule.fwd(db: ${db}, bits: ${bits}, ar: ${ar})`));
		const v = Array(this.q.length);
		let i = 0;
		for (let j = 0; j !== this.q.length; ++j) { const x = this.q[j];
			const t = x.set(db);
			v[i++] = t;
			if (bdd.F === t) return bdd.F;
		}
		let vars = bdd.and_many(v, 0, v.length);
		if (vars === bdd.F) return bdd.F;
		vars = this.ae.set(bdd.deltail(vars, bits*ar));
		vars = this.ae.set(vars);
		if (this.proof2.length !== 0) this.p.add(vars);
		return vars;
	}

	get_varbdd(bits, ar) {
		DBG(__cout('varbdd:',this.p,this.vars_arity));
		let x = bdd.T;
		let y = bdd.F;
		for (let z of this.p) y = bdd.or(y, z);
		for (let n = this.vars_arity; n !== ar; ++n) {
			x = from_int_and(this.context.pad, bits, n * bits, x);
		}
		return bdd.and(x, y);
	}
}

module.exports = { fact, rule }
