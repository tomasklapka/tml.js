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
const _dbg_rule    = require('debug')('tml:pfp:rule');

// internal counter for lps (lp._id)
const _counters = { lp: 0 };

// a P-DATALOG rule in bdd form
class rule {

	from_int(x, bits, offset) {
		let r = bdds.T;
		let b = bits--;
		while (b--) r = this.bdds.and(r, this.bdds.from_bit(bits - b + offset, x & (1 << b)));
		return r;
	}

	from_range(max, bits, offset) {
		let x = bdds.F;
		for (let n = 1; n < max; ++n) {
			x = this.bdds.or(x, this.from_int(n, bits, offset));
		}
		return x;
	}

	// initialize rule
	constructor(bdb, v, bits, dsz) {
		_dbg_rule(`new rule() bits: ${bits}, dsz: ${dsz}, v.size: ${v.length} v:`, v);
		this.bdds = bdb;
		this.neg  = false;
		this.hsym = bdds.T;
		this.sels = [];
		this.bd = [];
		const ar = v[0].length - 1;
		this.neg = v[0][0] < 0;
		v[0] = v[0].slice(1);
		const vars = [];
		for (let i = 0; i != v.length; ++i) {
			const x = v[i];
			for (let j = 0; j != x.length; ++j) {
				const y = x[j];
				if (y < 0 && !vars.includes(y)) {
					vars.push(y);
				}
			}
		}
		const nvars = vars.length;
		let m = {};
		for (let i = 1; i != v.length; ++i) {
			const d = {
				neg: v[i][0] < 0,
				sel: bdds.T,
				perm: [],
				ex: []
			};
			v[i].shift();
			d.ex = new Array(bits*ar).fill(false);
			d.perm = new Array((ar + nvars) * bits);
			for (let b = 0; b != (ar + nvars) * bits; ++b) {
				d.perm[b] = b;
			}
			for (let j = 0; j != ar; ++j) {
				if (v[i][j] >= 0) {
					d.sel = this.bdds.and(d.sel, this.from_int(v[i][j], bits, j * bits));
					for (let b = 0; b != bits; ++b) {
						d.ex[b+j*bits] = true;
					}
				} else {
					if (m.hasOwnProperty(v[i][j])) {
						for (let b = 0; b != bits; ++b) {
							d.ex[b+j*bits] = true;
							d.sel = this.bdds.and(d.sel, this.bdds.from_eq(b+j*bits, b+m[v[i][j]]*bits));
						}
					} else {
						m[v[i][j]] = j;
						d.sel = this.bdds.and(d.sel, this.from_range(dsz, bits, j * bits));
					}
				}
			}
			m = {};
			this.bd.push(d);
		}
		for (let j = 0; j != ar; ++j) {
			if (v[0][j] >= 0) {
				this.hsym = this.bdds.and(this.hsym, this.from_int(v[0][j], bits, j * bits));
			} else {
				if (m.hasOwnProperty(v[0][j])) {
					for (let b = 0; b != bits; ++b) {
						this.hsym = this.bdds.and(this.hsym, this.bdds.from_eq(b+j*bits, b+m[v[0][j]]*bits));
					}
				} else {
					m[v[0][j]] = j;
				}
			}
		}
		let k = ar;
		for (let i = 0; i != v.length-1; ++i) {
			for (let j = 0; j != ar; ++j) {
				if (v[i+1][j] < 0) {
					if (!m.hasOwnProperty(v[i+1][j])) {
						m[v[i+1][j]] = k++;
					}
					for (let b = 0; b != bits; ++b) {
						this.bd[i].perm[b+j*bits]=b+m[v[i+1][j]]*bits;
					}
				}
			}
		}
		if (v.length > 1) {
			this.sels = new Array(v.length-1);
		}
	}

	fwd(db, bits, ar, s) {
		const varbdd = (b, db, s) => {
			const sb = b.neg ? s.neg : s.pos;
			const key = b.sel+'.'+b.ex.join(',');
			if (sb.hasOwnProperty(key)) {
				return this.bdds.permute(sb[key], b.perm);
			}
			const r = b.neg
				? this.bdds.and_not_ex(b.sel, db, b.ex)
				: this.bdds.and_ex(b.sel, db, b.ex);
			sb[key] = r;
			return this.bdds.permute(r, b.perm);
		};

		if (this.bd.length === 1) {
			return this.bdds.deltail(
				this.bdds.and(this.hsym, varbdd(this.bd[0], db, s)),
				bits * ar);
		}
		if (this.bd.length == 2) {
			return this.bdds.deltail(
				this.bdds.and(this.hsym, this.bdds.and(
					varbdd(this.bd[0], db, s),
					varbdd(this.bd[1], db, s)
				),
				bits * ar));
		}
		let vars = bdds.T;
		const v = [];
		for (let i = 0; i < this.bd.length; i++) {
			const b = this.bd[i];
			vars = this.bdds.and(vars, varbdd(b, db, s));
			if (bdds.F === vars) return bdds.F;
			v.push(vars);
		}
		v.push(this.hsym);
		return this.bdds.and_deltail(this.bdds.and_many(v), bits * ar);
	}
}

// [pfp] logic program
class lp {
	constructor(maxbits, arity, dsz) {
		this._id = ++_counters.lp;
		// holds its own dict so we can determine the universe size
		this.bdds = new bdds();
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
	rule_add(x) {
		_dbg_rule(`rule_add() x:`, x);
		const r = new rule(this.bdds, x, this.bits, this.dsz);
		if (x.length === 1) {
			_dbg_rule('rule_add fact');
			this.db = this.bdds.or(this.db, r.hsym); // fact
		} else {
			_dbg_rule('rule_add rule');
			this.rules.push(r);
		}
	}
	fwd() {
		let add = bdds.F;
		let del = bdds.F;
		this.p.pos = {}; this.p.neg = {};
		for (let i = 0; i < this.rules.length; i++) {
			const r = this.rules[i];
			const t = this.bdds.or(
				r.fwd(this.db, this.bits, this.ar, this.p),
				r.neg ? del : add);
			if (r.neg) { del = t; } else { add = t; }
		}
		let s = this.bdds.and_not(add, del);
		_dbg_pfp('db:', this.db, 'add:', add, 'del:', del, 's:', s);
		if (s === bdds.F && add !== bdds.F) {
			this.db = bdds.F; // detect contradiction
			_dbg_pfp('db set (contradiction):', this.db);
		} else {
			this.db = this.bdds.or(this.bdds.and_not(this.db, del), s);
			_dbg_pfp('db set:', this.db);
		}
	}

	from_bits(x) {
		const s = this.bdds.allsat(x, this.bits * this.ar);
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

module.exports = () => {
	lp.rule = rule;
	return lp;
}
