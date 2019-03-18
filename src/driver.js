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
const { lp } = require('./lp');

const { err_null_in_head } = require('./messages');

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
			for (let j = 0; j != r.h.e.length; ++j) { const e = r.h.e[j];
				if (e.type === elem.NUM) nums = Math.max(nums, e.num + 256);
			}
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
		t.push(r.neg ? -1 : 1);
		for (let i = 0; i != r.e.length; ++i) {
			const e = r.e[i];
			if (e.type === elem.NUM) t.push(e.num + 256);
			else if (e.type === elem.CHR) t.push(e.e[0]);
			else t.push(this.d.get(e.e));
		}
		return t;
	}

	get_rule(r) {
		ID_TRC('get_rule');
		const m = [];
		m.push(this.get_term(r.h));
		if (m[0][0] > 0) {
			for (let i = 1; i < m[0].length; ++i) {
				if (m[0][i] === this.nul) throw new Error(err_null_in_head);
			}
		}
		for (let i = 0; i != r.b.length; ++i) {
			m.push(this.get_term(r.b[i]));
		}
		return m;
	}

	prog_init(p, s) {
		ID_TRC('prog_init');
		let m = [];
		const g = [];
		const pg = [];
		if (!p.d.length) {
			const rtxt = this.get_char_builtins();
			m = m.concat(rtxt);
		}
		for (let i = 0; i != p.r.length; ++i) { const x = p.r[i];
			if (x.goal && !x.pgoal) {
				if (x.b.length) throw new Error ('assert x.b.empty()');
				g[g.length] = this.get_term(x.h);
			} else {
				if (x.pgoal) {
					if (x.b.length) throw new Error ('assert x.b.empty()');
					pg[pg.length] = this.get_term(x.h);
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
		this.prog = new lp(m, g, pg, this.prog);
		this.prog.nul = this.nul;
		DBG(this.prog.drv = this);
		if (!s.length) {
			for (let i = 0; i != this.builtin_rels.length; ++i) {
				this.builtin_symbdds.push(this.prog.get_sym_bdd(x, 0))
			}
		}
		DBG(__bdd(`prog_read bdd:`, p.bdd.V.map(n=>`${p.bdd.M[n.key]}=(${n.key})`).join(', ')))
		DBG(__bdd(`prog_read bits:${this.bits}`))
		return p;
	}
	// pfp logic
	pfp(p) {
		ID_TRC('driver_pfp');
		if (!this.prog.pfp()) return false;

		let db = this.prog.db;
		for (let i = 0; i != this.builtin_symbdds.length; ++i) {
			db = bdd.and_not(db, this.builtin_symbdds[i]);
		}
		this.printdb('', this.prog.getbdd(db));
		return true;
	}

	// os - output string, p - program, t - db root
	// os - output string, t = bdd
	printbdd(os = '', p, t = null) {
		if (t === null) { t = p; p = null; }
		else return this.printbdd(os, p.getbdd(t));
		if (!Array.isArray(t)) {
			t = p.getbdd(this.progs[t].db);
		}
		const s = [];
		for (let i = 0; i < t.length; i++) { const v = t[i];
			let ss = '';
			for (let j = 0; j < v.length; j++) { const k = v[j];
				if (k === pad) ss += '* ';
				else if (k < this.nsyms) ss += this.d.get(k) + ' ';
				else ss += '[' + k + '] ';
			}
			s.push(ss);
		}
		os += s.sort().join(`\n`);
		return os;
	}

	printbdd_one(os = '', t) {
		os += "one of " + this.count(t, this.prog.bits * this.prog.ar) +
			" results: ";
		return this.printbdd(os, this.prog.getbdd_one(t));
	}

	printdb(os, p = null) {
		p = p || this.prog;
		return this.printbdd(os, p, p.getbdd(p.db));
	}
	toString() { return this.printdb(); }

}


module.exports = { driver, lp };
