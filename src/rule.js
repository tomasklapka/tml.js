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
const { bdds } = require('./bdds');

function varcount(v) {
	const vars = [];
	for (let i = 0; i != v.length; ++i) {
		for (let j = 1; j != v[i].length; ++j) {
			if (v[i][j] < 0 && !vars.includes(v[i][j])) vars.push(v[i][j]);
		}
	}
	return vars.length;
}

class rule_body {
	constructor(t, ar, bits, dsz, nvars, eqs) {
		this.eqs = eqs;
		this.neg = t[0] < 0;
		this.sel = bdds.T;
		this.ex = new Array(bits * ar).fill(false);
		this.perm = new Array((ar + nvars) * bits);
		t.shift();
		for (let b = 0; b != (ar + nvars) * bits; ++b) {
			this.perm[b] = b;
		}
		const m = {};
		DBG(__rule(`rb1`));
		for (let j = 0; j != ar; ++j) {
			DBG(__rule(`rbj`, j));
			this.from_arg(t[j], j, bits, dsz, m)
		}
		DBG(__rule(`rb2`));
	}

	from_arg(vij, j, bits, dsz, m) {
		ID('from_arg');
		TRC(`from_arg-${id}`);
		const eq = [];
		if (vij >= 0) {
			this.ex.fill(true, j * bits, (j+1) * bits);
			this.sel = from_int_and(vij, bits, j * bits, this.sel);
		} else {
			if (m.hasOwnProperty(vij)) {
				this.ex.fill(true, j * bits, (j+1) * bits);
				for (let b = 0; b != bits; ++b) {
					eq.push([ j * bits + b, m[vij] * bits + b ]);
				}
			} else {
				m[vij] = j;
				this.sel = from_range(dsz, bits, j * bits, this.sel);
			}
		}
		for (let j = 0; j != eq.length; ++j) {
			if (!(j % 8)) this.eqs.push(bdds.T);
			const e = this.eqs.length-1;
			this.eqs[e] = bdd.and(
				this.eqs[e],
				from_eq(eq[j][0], eq[j][1]));
		}

	}

	varbdd(db, cache) {
		DBG(__varbdd(`varbdd(db: ${db} cache:`, cache, `this:`, this, `)`));
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
			if (r === bdds.F) break;
			let n = this.eqs.length;
			while (n) {
				r = bdd.and(r, this.eqs[--n]);
				if (r === bdds.F) break ret;
			}
			r = bdd.ex(r, this.ex);
		} while (0);
		c[key] = r;
		const res = r === bdds.F ? bdds.F : bdd.permute(r, this.perm);
		DBG(__varbdd("varbdd res =", res));
		return res;
	};
}

// a P-DATALOG rule in bdd form
class rule {
	// initialize rule
	constructor(v, bits, dsz, proof, nul, pad) {
		DBG(__rule(`new rule() bits: ${bits}, dsz: ${dsz}, v.size: ${v.length} v:`, v));
		this.hsym = bdds.T;
		this.vars_arity = null;
		this.bd = [];
		this.eqs = [];
		this.p = [];
		this.proof1 = [];
		this.proof2 = [];
		const ar = v[0].length - 1;
		let k = ar;
		this.neg = v[0][0] < 0;
		v[0].shift();
		const nvars = varcount(v);
		for (let i = 1; i != v.length; ++i) {
			this.bd.push(new rule_body(v[i], ar, bits, dsz, nvars, this.eqs));
		}
		const heq = [];
		const m = {};
		for (let j = 0; j != ar; ++j) {
			if (v[0][j] >= 0) {
				this.hsym = from_int_and(v[0][j], bits, j * bits, this.hsym);
			} else {
				if (m.hasOwnProperty(v[0][j])) {
					for (let b = 0; b != bits; ++b) {
						heq.push([ j * bits, m[v[0][j]] * bits + b ]);
					}
				} else {
					m[v[0][j]] = j;
				}
			}
		}
		for (let j = 0; j != heq.length; ++j) {
			if (!(j % 8)) this.eqs.push(bdds.T);
			const e = this.eqs.length-1;
			this.eqs[e] = bdd.and(
				this.eqs[e],
				from_eq(heq[j][0], heq[j][1]));
		}
		for (let i = 0; i != v.length-1; ++i) {
			DBG(__rule('i', i));
			for (let j = 0; j != ar; ++j) {
				DBG(__rule('j', j));
				DBG(__rule('v[i+1][j]', v[i+1][j]));
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
		if (neg) throw new Error(err_proof);
		for (let i = 0; i != this.bd.length; ++i) {
			if (this.bd[i].neg) throw new Error(err_proof);
		}
		this.proof1 = [ [ 1, nul], [ 1 ] ];
		this.proof1[0] = this.proof1[0].concat(v[0]);
		this.proof1[1] = this.proof1[1].concat(v[0]);
		for (let i = 0; i != m.length; ++i) {
			if (m[i] >= ar) { this.proof1[1].push(i); }
		}
		for (let i = 0; i != this.bd.length; ++i) {
			this.proof1[0] = this.proof1[0].concat(v[i+1]);
		}
		for (let i = 0; i != this.proof1[0].length; ++i) {
			if (this.proof1[0][i] === pad) {
				this.proof1[0][i] = nul;
			}
		}
		let t = [];
		this.proof2 = [];
		for (let i = 0; i != this.bd.length; ++i) {
			t[0].push(1);
			t[0].push(nul);
			t[0] = t[0].concat(v[i+1]);
			t[1] = this.proof1[0];
			t[0] = t[0].concat(this.proof1[0].slice(2));
			this.proof2.push(JSON.parse(JSON.stringify(t)));
		}
		for (let i = 0; i != v.length; ++i) {
			t[i+2].push(1);
			t[i+2].push(nul);
			t[i+2] = t[i+2].concat(v[i]);
		}
		this.proof2.push(JSON.parse(JSON.stringify(t)));
	}

	fwd(db, bits, ar, s, p) {
		DBG(__pfp(`rule.fwd(db: ${db}, bits: ${bits}, ar: ${ar}, s:`,s,`p:`,p,`)`));
		let vars = bdds.T;
		for (let i = 0; i < this.bd.length; i++) {
			vars = bdd.and(vars, this.bd[i].varbdd(db, s));
			if (bdds.F === vars) return bdds.F;
		}
		for (let n = this.eqs.length; n; ) {
			vars = bdd.and(vars, this.eqs[--n]);
			if (bdds.F === vars) return bdds.F;
		}
		vars = bdd.and(vars, this.hsym);
		if (!this.proof2.length) p[p.length] = vars;
		return bdd.deltail(vars, bits * ar);
	}

	get_varbdd(bits, ar) {
		let x = bdds.T;
		let y = bdds.F;
		for (let i = 0; i != this.p.length; ++i) {
			y = bdd.or(y, this.p[i]);
		}
		for (let n = this.vars_arity; n != ar; ++n) {
			x = from_int_and(pad, bits, n * bits, x);
		}
		return bdd.and(x, y);
	}
}

module.exports = { rule }
