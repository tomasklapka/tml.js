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

const { bdd } = require('./bdd');
const { fact, rule } = require('./rule');
const { err_goal_arity, err_goal_sym } = require('./messages');

const pad = 0;

function align(x, par, pbits, ar, bits) {
	return bdd.pad(bdd.rebit(x, pbits, bits, ar*bits), par, ar, pad, bits);
}

// [pfp] logic program
class lp {
	constructor(r, g, pg, prev, context) {
		ID('lp');
		DBG(this.__id = __id);
		DBG()//const drv = context.driver);
		this.context = context;
		this.pad = pad;
		this.db = bdd.F; // db root
		this.gbdd = bdd.F;
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
		for (let m of r) {
			for (let j = 0; j != m.length; ++j) { const t = m[j];
				this.ar = Math.max(this.ar, t.length -1);
				for (let k = 0; k != t.length; ++k) { const e = t[k];
					if (e > 0) this.dsz = Math.max(this.dsz, e);
				}
			}
		}
		this.dsz = Math.max(prev ? prev.dsz : this.dsz+1, this.dsz+1);
		for (let i = 0; i != g.length; ++i) { const t = g[i];
			if (t.length-1 > this.ar) throw new Error(err_goal_arity);
			else for (let j = 0; j != t.length; ++j) { const e = t[j];
				if (e > 0 && e >= this.dsz) throw new Error(err_goal_sym);
			}
		}
		for (let i = 0; i != this.pgoals.length; ++i) { const t = this.pgoals[i];
			if (t.length-1 > this.ar) throw new Error(err_goal_arity);
			else for (let j = 0; j != t.length; ++j) { const e = t[j];
				if (e > 0 && e >= this.dsz) throw new Error(err_goal_sym);
			}
		}
		r = this.rules_pad(r);
		g = this.rule_pad(g);
		this.pgoals = this.rule_pad(this.pgoals);
		this.bits = msb(this.dsz);
		DBG(__rule('r', r));
		DBG(__rule('g', g));
		DBG(__rule('pg', this.pgoals));
		for (let m of r) {
			if (m.length === 1) {
				DBG(__rule('rule_add fact'));
				this.db = bdd.or(this.db, fact(m[0], this.bits, context));
				DBG(__rule('/rule_add fact added db:', this.db));
			} else {
				DBG(__rule('rule_add rule'));
				this.rules[this.rules.length] =
					new rule(m, this.bits, this.dsz,
						this.pgoals.length > 0, context);
				DBG(__rule('/rule_add rule:', this.rules.length));
			}
		}
		DBG(__rule('rules:', this.rules));
		if (this.pgoals.length) {
			this.proof1 = new lp(this.get_proof1(), [], [], this, this.context);
			DBG(drv.printdb('proof1: ', this.proof1));
			DBG(__proof('p1', this.proof1.bdd.V.length));
			this.proof2 = new lp(this.get_proof2(), [], [], this.proof1, this.context);
			DBG(drv.printdb('proof2: ', this.proof2));
			DBG(__proof('p2', this.proof2.bdd.V.length));
			//DBG(process.exit(0));
		}
		for (let i = 0; i != g.length; ++i) {
			this.gbdd = bdd.or(this.gbdd, fact(g[i], this.bits));
		}
	}

	get_proof1() {
		const p = new Set();
		for (let i = 0; i != this.rules.length; ++i) {
			p.add(this.rules[i].proof1);
		}
		DBG(__proof(`get proof1():`, p));
		return p;
	}

	get_proof2() {
		const p = new Set();
		for (let i = 0; i != this.rules.length; ++i) {
			this.rules[i].proof2.forEach(p.add, p);
			DBG(__proof(`      get proof2() r  adding:`, this.rules[i].proof2));
		}
		for (let i = 0; i != this.pgoals.length; ++i) {
			const m = [ 1, this.context.openp ].concat(
				this.pgoals[i].slice(1),
				[ this.context.closep ]);
			p.add([ m ]);
			DBG(__proof(`      get proof2() pg adding:`, [ m ]));
		}
		DBG(__proof(`get proof2():`, p));
		return p;
	}

	getdb() { return this.getbdd(this.db); }
	getbdd(t) { return bdd.from_bits(t, this.bits, this.ar); }
	getbdd_one(t) { return [ bdd.one_from_bits(t, this.bits, this.ar) ]; }

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
		const nm = new Set();
		for (let m of t) {
			nm.add(this.rule_pad(m));
		}
		return nm;
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
			add.add = bdd.F;
			del.del = bdd.F;
			d = this.db;       // get current db root
			s[s.length] = d;           // store current db root into steps
			DBG(__pfp(`____________________STEP_${++step}________________________`))
			DBG(__pfp(`                                                     `))
			this.fwd(add, del);         // do pfp step
			DBG(__pfp(`___________________/STEP_${step}________________________`))
			t = bdd.and_not(add.add, del.del);
			DBG(__pfp('db:', this.db, 'add:', add.add, 'del:', del.del, 't:', t))
			if (t === bdd.F && add.add !== bdd.F) {
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
			DBG(__proof('proof 1 true'));
			this.db = this.prove();
			DBG(__proof('proof 1 db:', this.db));
			this.ar = this.proof2.ar;
			this.bits = this.proof2.bits;
			return true;
		}
		if (this.gbdd !== bdd.F) this.db = bdd.and(this.gbdd, this.db);
		return true;
	}

	prove() {
		const add = { add: bdd.F };
		const del = { del: bdd.F };
		this.proof1.db = this.get_varbdd(this.proof1.ar);
		DBG(__cout('prove proof 1 db:', this.proof1.db));
		this.proof1.fwd(add, del);
		this.proof2.db = bdd.or(this.proof2.db, add.add);
		DBG(__cout('prove proof 2 db:', this.proof2.db));
		this.proof2.prev = null;
		if (del.del !== bdd.F) throw new Error('assert del == F');
		if (!this.proof2.pfp()) throw new Error('proof2.pfp unsat');
		const t = bdd.and_not(this.proof2.db, this.get_sym_bdd(this.context.openp, 0))
		if (this.gbdd === bdd.F) {
			DBG(__proof('prove(gbdd==F) =', t));
			return t;
		}
		const res = bdd.or(
			align(bdd.and(this.gbdd, this.db),
				this.ar, this.bits,
				this.proof2.ar, this.proof2.bits),
			t);
		DBG(__proof('prove =', res));
		//process.exit(0);
		return res;
	}

	get_varbdd(par) {
		let t = bdd.F;
		for (let i = 0; i != this.rules.length; ++i) {
			t = bdd.or(this.rules[i].get_varbdd(this.bits, par), t);
		}
		return t;
	}

	get_sym_bdd(sym, pos) {
		return bdd.from_int(sym, this.bits, this.bits * pos);
	}

}

lp.pad = pad;

module.exports = {
	lp, pad
}
