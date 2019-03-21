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

const { bdds } = require('./bdds');
const { rule } = require('./rule');
const { err_goal_arity, err_goal_sym } = require('./messages');

const bdd = new bdds();
const pad = 0;

function fact(v, bits) {
	ID_TRC('fact');
	let r = bdds.T;
	const m = {};
	for (let j = 0; j != v.length; ++j) {
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
		? bdd.and_not(bdds.T, r)
		: r;
}

function align(x, par, pbits, ar, bits) {
	return bdd.pad(bdd.rebit(x, pbits, bits, ar*bits), par, ar, pad, bits);
}

// [pfp] logic program
class lp {
	constructor(r, g, pg, prev, context) {
		ID('lp');
		DBG(this.__id = id);
		DBG(__cout(context));
		if (context) context.bdd = bdd;
		this.context = context;
		this.bdd = bdd; // keep reference to the "global" bdd
		this.pad = pad;
		this.db = bdds.F; // db root
		this.gbdd = bdds.F;
		this.proof1 = null; // lp
		this.proof2 = null; // lp
		this.rules = []; // p-datalog rules
		this.cache = { pos: {}, neg: {} }; // step
		this.goals = [];
		this.pgoals = JSON.parse(JSON.stringify(pg));
		this.prev = prev; // lp
		this.dsz = 0;
		if (prev) this.ar = prev.ar;
		else this.ar = 0;
		for (let i = 0; i != r.length; ++i) {
			for (let j = 0; j != r[i].length; ++j) {
				this.ar = Math.max(this.ar, r[i][j].length -1);
				for (let k = 0; k != r[i][j].length; ++k) {
					if (r[i][j][k] > 0) this.dsz = Math.max(this.dsz, r[i][j][k]);
				}
			}
		}
		this.dsz = Math.max(prev ? prev.dsz : this.dsz+1, this.dsz+1);
		for (let i = 0; i != g.length; ++i) {
			for (let j = 0; j != g[i].length; ++j) {
				const t = g[i][j];
				if (t.length-1 > this.ar) throw new Error(err_goal_arity);
				else for (let k = 0; k != t.length; ++k) {
					if (t[k] > 0 && t[k] >= this.dsz) throw new Error(err_goal_sym);
				}
			}
		}
		for (let i = 0; i != this.pgoals.length; ++i) { const t = this.pgoals[i];
			if (t.length-1 > this.ar) throw new Error(err_goal_arity);
			else for (let k = 0; k != t.length; ++k) {
				if (t[k] > 0 && t[k] >= this.dsz) throw new Error(err_goal_sym);
			}
		}
		r = this.rules_pad(r);
		g = this.rules_pad(g);
		pg = this.rules_pad(pg);
		this.bits = msb(this.dsz);
		for (let i = 0; i != r.length; ++i) {
			if (r[i].length === 1) {
				DBG(__rule('rule_add fact'));
				this.db = bdd.or(this.db, fact(r[i][0], this.bits));
				DBG(__rule('/rule_add fact added db:', this.db));
			} else {
				DBG(__rule('rule_add rule'));
				this.rules[this.rules.length] =
					new rule(r[i], this.bits, this.dsz,
						this.pgoals.length > 0, context);
				DBG(__rule('/rule_add rule:', this.rules[this.rules.length-1]));
			}
		}
		if (this.pgoals.length) {
			this.proof1 = new lp(this.get_proof1(), [], [], this, this.context);
			this.proof2 = new lp(this.get_proof2(), [], [], this.proof1, this.context);
		}
		for (let i = 0; i != g; ++g) {
			this.gbdd = bdd.or(this.gbdd, fact(g[i], this.bits));
		}
	}

	get_proof1() {
		const p = [];
		for (let i = 0; i != this.rules.length; ++i) {
			p[p.length] = this.rules[i].proof1;
		}
		return p;
	}

	get_proof2() {
		const p = [];
		const m = [];
		for (let i = 0; i != this.rules.length; ++i) {
			p[p.length] = this.rules[i].proof2;
		}
		for (let i = 0; i != this.pgoals.length; ++i) {
			m[0] = [ 1, this.context.openp ].concat(
				this.pgoals[i].slice(1),
				[ this.context.closep ]);
			p[p.length] = m;
		}
		return p;
	}

	getdb() { return this.getbdd(this.db); }
	getbdd(t) { return this.from_bits(t, this.bits, this.ar); }
	getbdd_one(t) { return [ this.one_from_bits(t, this.bits, this.ar) ]; }

	term_pad(t) {
		ID_TRC('term_pad');
		const l = t.length;
		if (l < this.ar + 1) {
			t = t.concat(Array(this.ar + 1 - l).fill(pad));
		}
		return t;
	}

	rule_pad(t) {
		ID_TRC('rule_pad');
		const r = [];
		for (let i = 0; i != t.length; ++i) {
			r[i] = this.term_pad(JSON.parse(JSON.stringify(t[i])), this.ar);
		}
		return r;
	}

	rules_pad(t) {
		ID_TRC('rules_pad');
		DBG(__pfp(`t `, t));
		const r = [];
		for (let i = 0; i != t.length; ++i) {
			r[r.length] = this.rule_pad(t[i]);
		}
		return r;
	}

	fwd(add, del) {
		ID_TRC('lp.fwd');
		DBG(__pfp(`lp.fwd(add: ${add.add}, del: ${del.del})`))
		this.cache.pos = {}; this.cache.neg = {};
		for (let i = 0; i < this.rules.length; i++) {
			const r = this.rules[i];
			const t = bdd.or(
				r.fwd(this.db, this.bits, this.ar, this.cache),
				r.neg ? del.del : add.add);
			DBG(__pfp(`lp.fwd...i:${i} t:${t}`));
			if (r.neg) { del.del = t; } else { add.add = t; }
		}
		//DBG(this.drv.printbdd("add:\n", this, add.add));
		//DBG(this.drv.printbdd("del:\n", this, del.del));
	}

	pfp() {
		ID_TRC('lp.pfp');
		if (this.prev) {
			if (!this.prev.pfp()) return false;
			this.db = bdd.or(this.db,
				align(
					this.prev.db, this.prev.ar, this.prev.bits,
					this.ar, this.bits));
		}
		let d;                       // current db root
		let t = 0;
		let step = 0;                // step counter
		const s = [];                // db roots of previous steps
		const add = {};
		const del = {};
		for (;;) {
			add.add = bdds.F;
			del.del = bdds.F;
			d = this.db;       // get current db root
			s[s.length] = d;           // store current db root into steps
			DBG(__pfp(`____________________STEP_${++step}________________________`))
			DBG(__pfp(`                                                     `))
			this.fwd(add, del);         // do pfp step
			DBG(__pfp(`___________________/STEP_${step}________________________`))
			t = bdd.and_not(add.add, del.del);
			DBG(__pfp('db:', this.db, 'add:', add.add, 'del:', del.del, 't:', t))
			if (t === bdds.F && add.add !== bdds.F) {
				DBG(__pfp('db set (contradiction):', this.db));
				return false;
			} else {
				this.db = bdd.or(bdd.and_not(this.db, del.del), t);
				DBG(__pfp('db set:', this.db));
			}
			// if db root already resulted from any previous step
			if (d === this.db) break;
			if (s.includes(this.db)) return false; // unsat
		};
		//DBG(this.drv.printdb("after: ", this));
		if (this.proof1) {
			this.db = this.prove();
			this.ar = this.proof2.ar;
			this.bits = this.proof2.bits;
			return true;
		}
		if (this.gbdd !== bdds.F) this.db = bdd.and(this.gbdd, this.db);
		return true;
	}

	prove() {
		const add = { add: bdds.F };
		const del = { del: bdds.F };
		this.proof1.db = this.get_varbdd(this.proof1.ar);
		this.proof1.fwd(add, del);
		this.proof2.db = bdd.or(this.proof2.db, add.add);
		this.proof2.prev = null;
		if (del.del !== bdds.F) throw new Error('assert del == F');
		if (!proof2.pfp()) throw new Error('proof2.pfp unsat');
		const t = bdd.and_not(this.proof2.db, this.get_sym_bdd(this.context.openp, 0))
		if (this.gbdd === bdds.F) return t;
		return bdd.or(
			align(bdd.and(this.gbdd, this.db),
				this.ar, this.bits,
				this.proof2.ar, this.proof2.bits),
			t);
	}

	get_varbdd(par) {
		let t = bdds.T;
		for (let i = 0; i != this.rules.length; ++i) {
			t = bdd.or(this.rules[i].get_varbdd(this.bits, par), t);
		}
		return t;
	}

	get_sym_bdd(sym, pos) {
		return bdd.from_int(sym, this.bits, this.bits * pos);
	}

	from_bits(x, bits, ar) {
		const s = bdd.allsat(x, bits * ar, bits);
		const r = Array(s.length);
		for (let k = 0; k < r.length; k++) {
			r[k] = Array(ar).fill(0);
		}
		let n = s.length;
		while (n--) {
			for (let i = 0; i != ar; ++i) {
				for (let b = 0; b != bits; ++b) {
					if (s[n][i * bits + b] > 0) {
						r[n][i] |= 1 << (bits - b - 1);
					}
				}
				// if (r[n][i] === pad) break;
			}
		}
		return r;
	}

	one_from_bits(x, bits, ar) {
		const s = Array(bits * ar).fill(true);
		if (!bdd.onesat(x, bits * ar, s)) return [];
		const r = Array(ar).fill(0);
		for (let i = 0; i != ar; ++i) {
			for (let b = 0; b != bits; ++b) {
				if (s[i * bits + b] > 0) {
					r[i] |= 1 << (bits - b - 1);
				}
			}
			// if (r[i] === pad) break;
		}
		return r;
	}

	maxw() {
		let r = 0;
		for (let i = 0; i != this.rules.length; ++i) {
			r = Math.max(r, this.rules[i].bd.length);
		}
		return r;
	}

	get_proof_rules() {
		let r = [];
		for (let i = 0; i != this.rules.length; ++i) {
			r[r.length] = this.rules[i].proof
		}
		return r;
	}
}

lp.pad = pad;
lp.bdd = bdd;

module.exports = {
	lp, pad
}
