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

function fact(v, bits, context) {
	ID_TRC('fact');
	DBG(__pfp(`fact(v: ${v}, bits: ${bits})`));
	let r = bdd.T;
	const m = {};
	for (let j = 0; j != v.length - 1; ++j) {
		if (v[j+1] >= 0) from_int_and(v[j+1], bits, j * bits, r);
		else if (!m.hasOwnProperty(v[j+1])) m[v[j+1]] = j;
		else {
			const pos = m[v[j+1]] * bits;
			for (let b = 0; b != bits; ++b) {
				r = bdd.and(r, from_eq(j*bits+b, pos+b));
			}
		}
	}
	return v[0] < 0
		? bdd.and_not(bdd.T, r)
		: r;
}

function varcount(v) {
	const vars = [];
	for (let i = 0; i != v.length; ++i) {
		for (let j = 1; j != v[i].length; ++j) {
			if (v[i][j] < 0 && !vars.includes(v[i][j])) {
				vars[vars.length] = v[i][j];
			}
		}
	}
	return vars.length;
}

class rule_body {
	constructor(t, ar, bits, dsz, nvars, eqs, context) {
		this.context = context;
		this.eqs = eqs;
		this.neg = t[0] < 0;
		this.sel = bdd.T;
		this.ex = new Array(bits * ar).fill(false);
		this.perm = new Array((ar + nvars) * bits);
		t.shift();
		for (let b = 0; b != (ar + nvars) * bits; ++b) {
			this.perm[b] = b;
		}
		for (let j = 0; j != ar; ++j) {
			if (t[j] >= 0) {
				from_int_and(t[j], bits, j * bits, this.sel);
			}
		}
		const m = {};
		for (let j = 0; j != ar; ++j) {
			this.from_arg(t[j], j, bits, dsz, m)
		}
		DBG(__rule(`rule_body from_arg result:`, m));
	}

	from_arg(vij, j, bits, dsz, m) {
		ID_TRC('from_arg');
		const eq = [];
		const ctx = this.context;
		const exclude = [ ctx.pad, ctx.openp, ctx.closep ];
		if (vij >= 0) { // sym
			this.ex.fill(true, j * bits, (j+1) * bits);
		} else { // var
			if (m.hasOwnProperty(vij)) { // seen
				this.ex.fill(true, j * bits, (j+1) * bits);
				for (let b = 0; b != bits; ++b) {
					eq[eq.length] = [ j * bits + b, m[vij] * bits + b ];
				}
			} else {
				m[vij] = j;
				this.sel = bdd.from_range(dsz, bits, j * bits, exclude, this.sel);
			}
		}
		for (let j = 0; j != eq.length; ++j) {
			if (!(j % 8)) this.eqs[this.eqs.length] = bdd.T;
			const e = this.eqs.length-1;
			this.eqs[e] = bdd.and(
				this.eqs[e],
				from_eq(eq[j][0], eq[j][1]));
		}
	}

	varbdd(db, cache) {
		DBG(__varbdd(`varbdd(db: ${db} cache:`, cache, `)`));
		const c = this.neg ? cache.neg : cache.pos;
		const key = this.sel+'.'+this.ex.join(',');
		if (c.hasOwnProperty(key)) {
			const res = bdd.permute(c[key], this.perm);
			DBG(__varbdd(`varbdd key = ${key} res =`, res));
			return res;
		}
		let r = this.neg
			? bdd.and_not(this.sel, db)
			: bdd.and(this.sel, db);
		ret:do {
			if (r === bdd.F) break;
			let n = this.eqs.length;
			while (n) {
				r = bdd.and(r, this.eqs[--n]);
				if (r === bdd.F) break ret;
			}
			r = bdd.ex(r, this.ex);
		} while (0);
		c[key] = r;
		const res = r === bdd.F ? bdd.F : bdd.permute(r, this.perm);
		DBG(__varbdd("varbdd res =", res));
		return res;
	};
}

// a P-DATALOG rule in bdd form
class rule {
	constructor(v, bits, dsz, proof, context) {
		DBG(__rule(`new rule() bits: ${bits}, dsz: ${dsz}, v.size: ${v.length} v:`, v));
		const pad = context.pad;
		const openp = context.openp;
		const closep = context.closep;
		this.context = context;
		this.hsym = bdd.T;
		this.vars_arity = null;
		this.bd = [];
		this.eqs = [];
		this.p = [];
		this.proof1 = [];
		this.proof2 = new Set();
		const ar = v[0].length - 1;
		let k = ar;
		this.neg = v[0][0] < 0;
		v[0].shift();
		const nvars = varcount(v);
		for (let i = 1; i != v.length; ++i) {
			this.bd[this.bd.length] = new rule_body(v[i], ar, bits, dsz, nvars, this.eqs, context);
		}
		const heq = [];
		const m = {};
		for (let j = 0; j != ar; ++j) {
			if (v[0][j] >= 0) {
				this.hsym = from_int_and(v[0][j], bits, j * bits, this.hsym);
			} else {
				if (m.hasOwnProperty(v[0][j])) {
					for (let b = 0; b != bits; ++b) {
						heq[heq.length] = [ j * bits, m[v[0][j]] * bits + b ];
					}
				} else {
					m[v[0][j]] = j;
				}
			}
		}
		for (let j = 0; j != heq.length; ++j) {
			if (!(j % 8)) this.eqs[this.eqs.length] = bdd.T;
			const e = this.eqs.length-1;
			this.eqs[e] = bdd.and(
				this.eqs[e],
				from_eq(heq[j][0], heq[j][1]));
		}
		for (let i = 0; i != v.length-1; ++i) {
			for (let j = 0; j != ar; ++j) {
				if (v[i+1][j] < 0) {
					if (!m.hasOwnProperty(v[i+1][j])) {
						m[v[i+1][j]] = k++;
					}
					for (let b = 0; b != bits; ++b) {
						this.bd[i].perm[b+j*bits] = b + m[v[i+1][j]] * bits;
					}
				}
			}
		}
		this.vars_arity = k;

		if (!proof) return;
		if (this.neg) throw new Error(err_proof);
		for (let i = 0; i != this.bd.length; ++i) {
			if (this.bd[i].neg) throw new Error(err_proof);
		}

		const vars = [ 1 ].concat(v[0]);
		const prule = [ 1, openp ];
		const bprule = [ 1 ];
		const vs = [];

		DBG(__rule(`v[0]:`, v[0]));
		for (let i = 0; i != v[0].length; ++i) {
			const t = MAX_INT+v[0][i];
			if (v[0][i] < 0 && !vs.includes(t)) {
				vs[vs.length] = t;
				DBG(__proof(`vs: `, vs));
			}
		}
		DBG(__rule(`v.tail:`, v.slice(1)));
		for (let i = 1; i != v.length; ++i) {
			for (let j = 0; j != v[i].length; ++j) {
				const t = MAX_INT+v[i][j];
				if (v[i][j] < 0 && !vs.includes(t)) {
					vs[vs.length] = t;
					vars[vars.length] = v[i][j];
					DBG(__proof(`vs: `, vs));
				}
			}
		}
		DBG(__proof(`vs: `, vs));
		DBG(__proof(`vars: `, vars));
		//DBG(process.exit(0));
		const pusher = Array.prototype.push;
		const push = (into, arr) => { return pusher.apply(into, arr) };
		for (let i = 0; i != v.length; ++i) {
			push(prule, v[i]);
		}
		prule[prule.length] = closep;

		push(bprule, v[0]);
		bprule[bprule.length] = openp;
		for (let i = 1; i != v.length; ++i) {
			push(bprule, v[i]);
		}
		bprule[bprule.length] = closep;

		this.proof1 = [ prule,  vars ];
		this.proof2 = new Set();
		const r = [ bprule, prule, [ 1, openp ].concat(v[0], [ closep ]) ];
		for (let i = 1; i != v.length; ++i) {
			this.proof2.add(
				[ [ 1, openp ].concat(v[i], [ closep ]), prule, r[2] ]);
			DBG(__proof(`proof2[${i-1}]: ${this.proof2.length}`, this.proof2));
			r[r.length] = [ 1, openp ].concat(v[i], [ closep ]);
			DBG(__proof(`r${i}: `, r));
		}
		this.proof2.add(JSON.parse(JSON.stringify(r)));
		DBG(__proof(`proof1: (length: ${this.proof1.length})`, this.proof1));
		DBG(__proof(`proof2: (length: ${this.proof2.length})`, this.proof2));
	}

	fwd(db, bits, ar, s) {
		DBG(__pfp(`rule.fwd(db: ${db}, bits: ${bits}, ar: ${ar}, s:`, s, `)`));
		let vars = bdd.T;
		const v = Array(this.bd.length + this.eqs.length + 1);
		let i = 0;
		for (let j = 0; j != this.bd.length; ++j) {
			vars = this.bd[j].varbdd(db, s)
			if (bdd.F === vars) return bdd.F;
			else v[i++] = vars;
		}
		for (let j = 0; j != this.eqs.length; ++j) {
			v[i++] = this.eqs[j];
		}
		v[i] = this.hsym;
		vars = bdd.and_many(v);
		if (bdd.F === vars) return bdd.F;
		if (this.proof2.length !== 0 && !this.p.includes(vars)) {
			this.p[this.p.length] = vars;
		}
		return bdd.deltail(vars, bits * ar);
	}

	get_varbdd(bits, ar) {
		DBG(__cout('varbdd:',this.p,this.vars_arity));
		let x = bdd.T;
		let y = bdd.F;
		for (let i = 0; i != this.p.length; ++i) {
			y = bdd.or(y, this.p[i]);
		}
		for (let n = this.vars_arity; n != ar; ++n) {
			x = from_int_and(this.context.pad, bits, n * bits, x);
		}
		return bdd.and(x, y);
	}
}

module.exports = { fact, rule }
