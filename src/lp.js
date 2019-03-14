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
const _dbg_pfp     = require('debug')('tml:pfp');
const _dbg_varbdd  = require('debug')('tml:pfp:varbdd');
const _dbg_rule    = require('debug')('tml:pfp:rule');

// internal counter for lps (lp._id)
const _counters = { lp: 0 };

// messages
const err_proof = `proof extraction yet unsupported for programs ` +
	`with negation or deletion.`;

const bdd = new bdds();

function from_int_and(x, y, o, r) { return bdd.and(r, from_int(x, y, o)); }

function from_int(x, bits, offset) {
	let r = bdds.T;
	let b = bits--;
	while (b--) r = bdd.and(r, bdd.from_bit(bits - b + offset, x & (1 << b)));
	return r;
}

function from_eq(src, dst, l, r) {
	while (l--) r = bdd.and(r, bdd.from_eq(src + l, dst + l));
	return r;
}

function from_range(max, bits, offset, r) {
	let x = bdds.F;
	for (let n = 1; n < max; ++n) {
		x = bdd.or(x, from_int(n, bits, offset));
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
	constructor(t, ar, bits, dsz, nvars) {
		this.neg = t[0] < 0;
		this.sel = bdds.T;
		this.ex = new Array(bits * ar).fill(false);
		this.perm = new Array((ar + nvars) * bits);
		t.shift();
		for (let b = 0; b != (ar + nvars) * bits; ++b) {
			this.perm[b] = b;
		}
		const m = {};
		_dbg_rule(`rb1`);
		for (let j = 0; j != ar; ++j) {
			_dbg_rule(`rbj`, j);
			this.from_arg(t[j], j, bits, dsz, m)
		}
		_dbg_rule(`rb2`);

	}

	from_arg(vij, j, bits, dsz, m) {
		if (vij >= 0) {
			this.ex.fill(true, j * bits, (j+1) * bits);
			this.sel = from_int_and(vij, bits, j * bits, this.sel);
		} else {
			if (m.hasOwnProperty(vij)) {
				this.ex.fill(true, j * bits, (j+1) * bits);
				this.sel = from_eq(j * bits, m[vij] * bits, bits, this.sel)
			} else {
				m[vij] = j;
				this.sel = from_range(dsz, bits, j * bits, this.sel);
			}
		}
	}

	varbdd(db, p) {
		_dbg_varbdd(`varbdd(db: ${db}, p:`, p, `this:`, this);
		const sb = this.neg ? p.neg : p.pos;
		const key = this.sel+'.'+this.ex.join(',');
		if (sb.hasOwnProperty(key)) {
			const res = bdd.permute(sb[key], this.perm);
			_dbg_varbdd(`varbdd key = ${key} res =`, res);
			return res;
		}
		let r = this.neg
			? bdd.and_not(this.sel, db)
			: bdd.and(this.sel, db);
		r = bdd.ex(r, this.ex);
		sb[key] = r;
		const res = bdd.permute(r, this.perm);
		_dbg_varbdd("varbdd res =", res);
		return res;
	};
}

// a P-DATALOG rule in bdd form
class rule {

	// initialize rule
	constructor(v, bits, dsz, proof) {
		_dbg_rule(`new rule() bits: ${bits}, dsz: ${dsz}, v.size: ${v.length} v:`, v);
		this.hsym = bdds.T;
		this.sels = [];
		this.bd = [];
		const ar = v[0].length - 1;
		let k = ar;
		this.neg = v[0][0] < 0;
		v[0].shift(); // = v[0].slice(1);
		const nvars = varcount(v);
		_dbg_rule(`0`);
		for (let i = 1; i != v.length; ++i) {
			this.bd.push(new rule_body(v[i], ar, bits, dsz, nvars));
		}
		_dbg_rule(`1`, this.bd, v);
		let m = {};
		for (let j = 0; j != ar; ++j) {
			if (v[0][j] >= 0) {
				this.hsym = bdd.and(this.hsym, from_int(v[0][j], bits, j * bits));
			} else {
				if (m.hasOwnProperty(v[0][j])) {
					this.hsym = from_eq(j * bits, m[v[0][j]] * bits, bits, this.hsym);
				} else {
					m[v[0][j]] = j;
				}
			}
		}
		_dbg_rule(`2`, v);
		for (let i = 0; i != v.length-1; ++i) {
			_dbg_rule('i', i);
			for (let j = 0; j != ar; ++j) {
				_dbg_rule('j', j);
				_dbg_rule('v[i+1][j]', v[i+1][j]);
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
		_dbg_rule(`3`);
		if (!proof) return;
		if (neg) throw new Error(err_proof);
		for (let i = 0; i != this.bd.length; ++i) {
			if (this.bd[i].neg) throw new Error(err_proof);
		}
		//throw new Error('proof not implemented');
		const prf = [ [1], [1] ];
		prf[0] = prf[0].concat(v[0]);
		prf[1] = prf[1].concat(v[0]);
		for (let i = 0; i != m.length; ++i) {
			if (m[i] >= ar) { prf[1].push(i); }
		}
		for (let i = 0; i < this.bd.length; ++i) {
			prf[0] = prf[0].concat(v[i+1]);
		}
		proof.push(prf);
	}

	fwd(db, bits, ar, s, p) {
		_dbg_pfp(`rule.fwd(db: ${db}, bits: ${bits}, ar: ${ar}, s:`,s,`p:`,p,`)`);
		let vars = bdds.T;
		const v = [];
		do {
			if (this.bd.length === 1) {
				vars = bdd.and(this.hsym, this.bd[0].varbdd(db, s));
				_dbg_pfp(`rule.fwd bd.length === 1`, vars);
				if (bdds.F === vars) return bdds.F;
				break;
			}
			if (this.bd.length === 2) {
				const first = this.bd[1].varbdd(db, s);
				const second = this.bd[0].varbdd(db, s);
				vars = bdd.and(this.hsym, bdd.and(second, first));
				_dbg_pfp(`rule.fwd bd.length === 2`, vars, first, second);
				if (bdds.F === vars) return bdds.F;
				break;
			}
			for (let i = 0; i < this.bd.length; i++) {
				vars = this.bd[i].varbdd(db, s);
				if (bdds.F === vars) return bdds.F;
				v.push(vars);
			}
			v.push(this.hsym);
			_dbg_pfp(`rule.fwd 3 vars, v`, vars, v);
			vars = bdd.and_many(v);
			_dbg_pfp(`rule.fwd 4 vars`, vars);
			if (bdds.F === vars) return bdds.F;
		} while (0);
		if (p) p.push(vars);
		_dbg_pfp(`rule.fwd 5 vars`, vars);
		return bdd.deltail(vars, bits * ar);
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
	}
	getbdd(t) { return this.from_bits(t)}
	getdb() { return this.getbdd(this.db); }
	// single pfp step
	rule_add(x, proof) {
		_dbg_rule(`rule_add() x:`, x, this.bits, this.dsz, proof);
		const r = new rule(x, this.bits, this.dsz, proof);
		if (x.length === 1) {
			_dbg_rule('rule_add fact');
			this.db = bdd.or(this.db, r.hsym); // fact
		} else {
			_dbg_rule('rule_add rule');
			this.rules.push(r);
		}
	}
	fwd(add, del, proof) {
		_dbg_pfp(`lp.fwd(add: ${add.add}, del: ${del.del}, proof: `,proof,`)`)
		this.p.pos = {}; this.p.neg = {};
		for (let i = 0; i < this.rules.length; i++) {
			const r = this.rules[i];
			const t = bdd.or(
				r.fwd(this.db, this.bits, this.ar, this.p, proof),
				r.neg ? del.del : add.add);
			_dbg_pfp(`lp.fwd...i:${i} t:${t}`);
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
			}
		}
		return r;
	}
}

module.exports = {
	lp
}
