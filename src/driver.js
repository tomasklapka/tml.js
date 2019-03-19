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

const {
	raw_progs, elem, isspace, isalnum, isalpha, isdigit
} = require('./input');
const { dict } = require('./dict');
const { lp, pad } = require('./lp');

const { err_null_in_head, err_null } = require('./messages');

class driver {
	constructor(rp) {
		ID_TRC('driver');
		// initialize symbols and variables tables
		this.d = new dict();
		this.strs_extra = [];
		this.builtin_rels = [];
		this.builtin_symbdds = [];
		this.prog = null;
		this.mult = false;
		if (!(rp instanceof raw_progs)) {
			try {
				rp = new raw_progs(rp);
			} catch (err) {
				console.log('Parse error:', err);
				return
			}
		}
		for (let n = 0; n != rp.p.length; ++n) {
			this.d.nums = Math.max(this.d.nums, this.get_nums(rp.p[n]))
			this.openp = this.d.get("(");
			this.closep = this.d.get(")");
			this.nul = this.d.get("null");
			this.prog_init(rp.p[n], this.directives_load(rp.p[n]));
		}
	}
	// nsyms = number of stored symbols
	get nsyms() { return this.d.nsyms; }
	// returns bit size of the dictionary
	get bits() { return this.d.bits; }

	from_func(fn, name, from, to, r) {
		ID_TRC('from_func');
		const rel = this.d.get(name);
		this.builtin_rels[this.builtin_rels.length] = rel;
		for (; from !== to; ++from) {
			if (fn(from)) r[r.length] = [ [ 2, rel, from ] ];
		}
	}

	get_char_builtins() {
		ID_TRC('get_char_builtins');
		const m = [];
		this.from_func(isspace, 'space', 0, 255, m);
		this.from_func(isalnum, 'alnum', 0, 255, m);
		this.from_func(isalpha, 'alpha', 0, 255, m);
		this.from_func(isdigit, 'digit', 0, 255, m);
		console.log(m);
		return m;
	}

	get_nums(p) {
		ID_TRC('get_nums');
		let nums = 0;
		for (let i = 0; i != p.d.length; ++i) {
			const d = p.d[i];
			const add = d.fname
				? d.arg.length
				: fsize(d.arg.slice(1, d.arg.length-1));
			nums = Math.max(nums, 256 + add);
		}
		for (let i = 0; i != p.r.length; ++i) { const r = p.r[i];
			for (let j = 0; j != r.b.length; ++j) { const t = r.b[j];
				for (let k = 0; k != t.e.length; ++k) { const e = t.e[k];
					if (e.type === elem.NUM) nums = Math.max(nums, e.num + 256);
				}
			}
		}
		return nums;
	}

	directives_load(p) {
		ID_TRC('directives_load');
		const r = {};
		for (let k = 0; k != p.d.length; ++k) {
			const d = p.d[k];
			const str = d.arg.slice(1, d.arg.length-1);
			r[this.d.get(d.rel)] = d.fname
				? file_read_text(str.replace('\\', ''))
				: str;
		}
		return r;
	}

	get_term(r) {
		ID_TRC('get_term');
		const t = [];
		t[t.length] = r.neg ? -1 : 1;
		for (let i = 0; i != r.e.length; ++i) {
			const e = r.e[i];
			if (e.type === elem.NUM) t[t.length] = e.num + 256;
			else if (e.type === elem.CHR) t[t.length] = e.e[0];
			else if (e.type === elem.OPENP) t[t.length] = this.openp;
			else if (e.type === elem.CLOSEP) t[t.length] = this.closep;
			else t[t.length] = this.d.get(e.e);
		}
		return t;
	}

	get_rule(r) {
		ID_TRC('get_rule');
		const m = [];
		for (let i = 0; i != r.b.length; ++i) {
			m[m.length] = this.get_term(r.b[i])
		}
		if (m[0][0] > 0) {
			for (let i = 1; i < m[0].length; ++i) {
				if (m[0][i] === this.nul) throw new Error(err_null_in_head);
			}
		}
		return m;
	}

	grammar_to_rules(g, m) {
		for (let i = 0; i != g.length; ++i) { const p = g[i]; // production
			if (p.p.length < 2) throw new Error("empty production.\n");
			const t = [];
			let v = -1;
			let x = this.d_get(p.p[0].e);
			if (p.p.length === 2 && p.p[1].type === elem.SYM
			&& nul === this.d.get(p.p[1].e)) {
				m[m.length] = [ [ 1, x, -1, -1 ], [ 1, rel, -2, -1, -3 ] ];
				m[m.length] = [ [ 1, x, -1, -1 ], [ 1, rel, -2, -3, -1 ] ];
				continue;
			}
			t[t.length] = [ 1, x, -1, -p.p.length ];
			for (let n = 1; n < p.p.length; ++n) {
				if (p.p[n].type === elem.SYM) {
					x = this.d.get(p.p[n].e);
					if (nul === x) throw new Error(err_null);
					t[t.length] = [ 1, x, v, v-1 ];
				}
				else if (p.p[n].type === elem.CHR) {
					if (!n) throw new Error("grammar lhs cannot be a terminal.\n");
					t[t.length] = [ 1, rel, p.p[n].e[0]+1, v, v-1 ];
				} else throw new Error("unexpected grammar node.\n");
			}
			m[m.length] = t;
			--v;
		}
	}

	prog_init(p, s) {
		ID_TRC('prog_init');
		let m = [];
		const g = [];
		const pg = [];
		if (p.g.length && s.length > 1) throw new Error("only one string allowed given grammar.\n");
		this.grammar_to_rules(p.g, m, Object.keys(s)[0]);
		if (p.d.length > 0) {
			process.exit(0);
			const rtxt = this.get_char_builtins();
			m = m.concat(rtxt);
		}
		for (let i = 0; i != p.r.length; ++i) { const x = p.r[i];
			if (x.goal && !x.pgoal) {
				if (x.b.length !== 1) throw new Error ('assert x.b.length === 1');
				g[g.length] = this.get_term(x.b[0]);
			} else {
				if (x.pgoal) {
					if (x.b.length !== 1) throw new Error ('assert x.b.length === 1');
					pg[pg.length] = this.get_term(x.b[0]);
				} else {
					m[m.length] = this.get_rule(x);
				}
			}
		}
		const keys = Object.keys(s);
		for (let i = 0; i != keys.length; ++i) {
			const x = s[keys[i]];
			for (let n = 0; n != x.length-1; ++n) {
				m[m.length] = [[ 1, keys[i], x[n]+1, n + 257, n + 258 ]];
			}
			m[m.length] = [[
				1, keys[i], x[x.length-1]+1,
				x.length+256, this.nul ]];
		}
		const context = {
			pad: pad,
			nul: this.nul,
			openp: this.openp,
			closep: this.closep };
		this.prog = new lp(m, g, pg, this.prog, context);
		this.prog.nul = this.nul;
		DBG(this.prog.drv = this);
		if (!s.length) {
			for (let i = 0; i != this.builtin_rels.length; ++i) {
				this.builtin_symbdds[this.builtin_symbdds.length] =
					this.prog.get_sym_bdd(x, 0);
			}
		}
		DBG(__bdd(`prog_read bdd:`, this.prog.bdd.V.map(n=>`${this.prog.bdd.M[n.key]}=(${n.key})`).join(', ')))
		DBG(__bdd(`prog_read bits: ${this.bits}`))
		return p;
	}
	// pfp logic
	pfp(p) {
		ID_TRC('driver.pfp');
		if (!this.prog.pfp()) return false;

		let db = this.prog.db;
		for (let i = 0; i != this.builtin_symbdds.length; ++i) {
			db = bdd.and_not(db, this.builtin_symbdds[i]);
		}
		console.log(this.printbdd_matrix('', this.prog.getbdd(db)));
		return true;
	}

	printbdd_matrices(os = '', t) {
		for (let i = 0; i != t.length; ++i) {
			os = this.printbdd(os, t[i])
		}
		return os;
	}

	// os - output string, p - program, t - db root
	printbdd_matrix(os = '', t = null) {
		ID_TRC('printbdd');
		DBG(__bdd(`printbdd(t: ${t})`))
		const s = [];
		for (let i = 0; i < t.length; i++) { const v = t[i];
			let ss = '';
			for (let j = 0; j < v.length; j++) { const k = v[j];
				if (k === pad) ss += '* ';
				else if (k < this.nsyms) ss += this.d.get(k) + ' ';
				else ss += '[' + k + '] ';
			}
			s[s.length] = ss;
		}
		os += s.sort().join(`\n`);
		return os;
	}

	printbdd(os = '', p, t) {
		return this.printbdd_matrix(os, p.getbdd(t));
	}

	printbdd_one(os = '', t) {
		os += "one of " + this.count(t, this.prog.bits * this.prog.ar) +
			" results: ";
		return this.printbdd(os, this.prog.getbdd_one(t));
	}

	printdb(os, p = null) {
		ID_TRC('printdb');
		p = p || this.prog;
		return this.printbdd(os, p, p.db);
	}
	toString() { return this.printdb(); }

}


module.exports = { driver, lp };
