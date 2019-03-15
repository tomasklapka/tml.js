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

const { bdds } = require('./bdds')();

// debug functions

// internal counter for lps (lp._id)
const _counters = { lp: 0, from_int: 0, from_range: 0, from_arg: 0 };

const pad = 0;

// messages
const err_proof = `proof extraction yet unsupported for programs ` +
	`with negation or deletion.`;

const bdd = new bdds();

// function from_eq(src, dst, l, r) {
// 	while (l--) r = bdd.and(r, bdd.from_eq(src + l, dst + l));
// 	return r;
// }

function from_range(max, bits, offset, r) {
	const id = ++_counters.from_range;
	let x = bdds.F;
	for (let n = 1; n != max; ++n) {
		x = bdd.or(x, bdd.from_int(n, bits, offset));
	}
	return bdd.and(r, x);
}

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
		for (let j = 0; j != ar; ++j) {
			this.from_arg(t[j], j, bits, dsz, m)
		}
	}

	from_arg(vij, j, bits, dsz, m) {
		const id = ++_counters.from_arg;
		const eq = [];
		if (vij >= 0) {
			this.ex.fill(true, j * bits, (j+1) * bits);
			this.sel = bdd.from_int_and(vij, bits, j * bits, this.sel);
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
				bdd.from_eq(eq[j][0], eq[j][1]));
		}

	}

	varbdd(db, p) {
		const sb = this.neg ? p.neg : p.pos;
		const key = this.sel+'.'+this.ex.join(',');
		if (sb.hasOwnProperty(key)) {
			const res = bdd.permute(sb[key], this.perm);
			return res;
		}
		let r = this.neg
			? bdd.and_not(this.sel, db)
			: bdd.and(this.sel, db);
		let n = this.eqs.length;
		while (n) {
			r = bdd.and(r, this.eqs[--n]);
			if (bdds.F === r) return bdds.F;
		}
		r = bdd.ex(r, this.ex);
		sb[key] = r;
		const res = bdd.permute(r, this.perm);
		return res;
	};
}

// a P-DATALOG rule in bdd form
class rule {
	// initialize rule
	constructor(v, bits, dsz, proof) {
		this.hsym = bdds.T;
		this.proof_arity = 0;
		this.sels = [];
		this.bd = [];
		this.eqs = [];
		this.p = [];
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
				this.hsym = bdd.from_int_and(v[0][j], bits, j * bits, this.hsym);
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
				bdd.from_eq(heq[j][0], heq[j][1]));
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
		if (!proof || v.length === 1) return;
		if (neg) throw new Error(err_proof);
		for (let i = 0; i != this.bd.length; ++i) {
			if (this.bd[i].neg) throw new Error(err_proof);
		}
		const prf = [ [ 1 ], [ 1 ] ];
		prf[0] = prf[0].concat(v[0]);
		prf[1] = prf[1].concat(v[0]);
		for (let i = 0; i != m.length; ++i) {
			if (m[i] >= ar) { prf[1].push(i); }
		}
		for (let i = 0; i != this.bd.length; ++i) {
			prf[0] = prf[0].concat(v[i+1]);
		}
		for (let j = 0; j != prf[0].length; ++j) {
			if (prf[0][j] === pad) {
				prf[0].splice(j--, 1);
			}
		}
		for (let i = 0; i != prf.length; ++i) {
			this.proof_arity = Math.max(
				this.proof_arity,
				prf[i].length - 1)
		}
		proof.push(prf);
	}

	fwd(db, bits, ar, s, p) {
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
		if (p && !this.p.includes(vars)) this.p.push(vars);
		return bdd.deltail(vars, bits * ar);
	}

	get_varbdd(bits, ar) {
		let x = bdds.T;
		let y = bdds.F;
		for (let i = 0; i != this.p.length; ++i) {
			y = bdd.or(y, this.p[i]);
		}
		for (let n = this.vars_arity; n != ar; ++n) {
			x = bdd.from_int_and(pad, bits, n * bits, x);
		}
		return bdd.and(x, y);
	}
}

// [pfp] logic program
class lp {
	constructor(maxbits, arity, dsz) {
		this._id = ++_counters.lp;
		this.bdd = bdd; // keep link to the bdd
		this.db = bdds.F;
		this.rules = [];     // p-datalog rules
		this.ar = arity;
		this.dsz = dsz;
		this.bits = maxbits;
		this.p = { pos: {}, neg: {} };
		this._proof_arity = null;
	}

	getbdd(t) { return this.from_bits(t); }

	getdb() { return this.getbdd(this.db); }
	// single pfp step
	rule_add(x, proof) {
		if (x.length === 1) {
			const r = new rule(x, this.bits, this.dsz, false);
			this.db = bdd.or(this.db, r.hsym); // fact
		} else {
			const r = new rule(x, this.bits, this.dsz, proof);
			this.rules.push(r);
		}
	}

	fwd(add, del, proof) {
		this.p.pos = {}; this.p.neg = {};
		for (let i = 0; i < this.rules.length; i++) {
			const r = this.rules[i];
			const t = bdd.or(
				r.fwd(this.db, this.bits, this.ar, this.p, proof),
				r.neg ? del.del : add.add);
			if (r.neg) { del.del = t; } else { add.add = t; }
		}
	}

	from_bits(x) {
		const s = bdd.allsat(x, this.bits * this.ar);
		const r = Array(s.length);
		for (let k = 0; k < r.length; k++) {
			r[k] = Array(this.ar).fill(0);
		}
		let n = s.length;
		while (n--) {
			for (let i = 0; i != this.ar; ++i) {
				for (let b = 0; b != this.bits; ++b) {
					if (s[n][i * this.bits + b] > 0) {
						r[n][i] |= 1 << (this.bits - b - 1);
					}
				}
				if (r[n][i] === pad) break;
			}
		}
		return r;
	}

	get_varbdd() {
		let t = bdds.F;
		for (let i = 0; i != this.rules.length; ++i) {
			t = bdd.or(r.get_varbdd(bits, this.proof_arity()), t);
		}
		return t;
	}

	proof_arity() {
		if (this._proof_arity !== null) return this._proof_arity;
		let r = 0;
		for (let i = 0; i != this.rules.length; ++i) {
			r = Math.max(r, this.rules[i].proof_arity);
		}
		this._proof_arity = r;
		return r;
	}
}

module.exports = {
	lp,
	pad
}
