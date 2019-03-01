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

// DEFAULT OPTIONS
const options = {
	recursive: false, // use rec or non rec algos
}
let bdds = null; // bdds class (to be loaded when required)
// load helper function for exporting bdds to dot, svg and/or png
// const { bdd_out } = require('./util');

// debug functions
// internal counter for lps (lp._id)
const _counters = { lp: 0 };

// messages
const identifier_expected     = `Identifier expected`;
const term_expected           = `Term expected`;
const comma_dot_sep_expected  = `',', '.' or ':-' expected`;
const sep_expected            = `Term or ':-' or '.' expected`;
const unexpected_char         = `Unexpected char`;

// skip_ws or skip 1 or more characters from parsing input
const skip_ws = s           => { s.s = s.s.replace(/^\s+/, ''); };
const skip    = (s, n = 1)  => { s.s = s.s.slice(n); }

// dict represents strings as unique integers
class dict {
	// pad = 0 constant
	static get pad() { return 0; }
	// nsyms = number of stored symbols
	get nsyms() { return this.syms.length; }
	// returns bit size of the dictionary
	get bits() { return 32 - Math.clz32(this.syms.length-1); }
	// initialize symbols and variables tables
	constructor() {
		this.syms = [ dict.pad ];
		this.vars = [ dict.pad ];
	}
	// gets and remembers the identifier and returns it's unique index
	// positive indexes are for symbols and negative indexes are for vars
	get(s) {
		if (typeof(s) === 'number') {     // if s is number
			const r = s >= 0 ? this.syms[s] : this.vars[-s];
			return r;                 //     return symbol by index
		}
		if (s[0] === '?') {               // if s is variable
			const p = this.vars.indexOf(s);
			if (p >= 0) {             //     if variable already in dict
				return -p;        //        return its index negated
			}
			this.vars.push(s);        //     else store the variable in dict
			return -(this.vars.length-1); //     and return its index negated
		}
		const p = this.syms.indexOf(s);   // if s is symbol
		if (p >= 0) {                     //     if is symbol in dict
			return p;                 //         return its index
		}
		this.syms.push(s);                //     else store the symbol in dict
		return this.syms.length-1;        //         and return its index
	}
}

function get_range(bdd, i, j, s, bits, ar) {
	const BIT = (term, arg, b) => (term*ar+arg)*bits+b;
	let rng = bdds.F;
	for (let k = 1; k != s; ++k) {
		let elem = bdds.T;
		for (let b = 0; b != bits; ++b) {
			elem = bdd.bdd_and(elem, bdd.from_bit(BIT(i, j, b), k & (1 << b)));
		}
		rng = bdd.bdd_or(rng, elem);
	}
	return rng;
}

function from_term(bdd, i, s, bits, ar, v, r, m) {
	const BIT = (term, arg, b) => (term*ar+arg)*bits+b;
	let b = bits;
	v.shift();
	for (let j = 0; j != v.length; ++j) {
		if (v[j] < 0) {
			r.hsym = bdd.bdd_and(r.hsym, get_range(bdd, i , j, s, bits, ar));
			if (m.hasOwnProperty(v[j])) {
				while (b-- > 0) {
					r.hsym = bdd.bdd_and(r.hsym, bdd.from_eq(
						BIT(i, j, b),
						BIT(m[v[j]][0], m[v[j]][1], b)));
				}
			} else {
				m[v[j]] = [ i, j ];
			}
		} else {
			while (b-- > 0) {
				r.h = bdd.bdd_and(r.h, bdd.from_bit(BIT(i, j, b), (v[j] & (1 << b)) > 0));
			}
		}
		b = bits;
	}
}
// a P-DATALOG rule in bdd form
class rule {
	// initialize rule
	constructor(bdd, v, bits, ar, dsz) {
		this.neg =  false;
		this.h = bdds.T;   // bdd root
		this.hsym = bdds.T;
		this.npos = 0;
		this.nneg = 0;
		this.neg = v[0][0] < 0;
		const m = {};
		const t = [];
		for (let i = 1; i != v.length; ++i) { if (v[i][0] > 0) { ++this.npos; t.push(v[i].slice()); } }
		for (let i = 1; i != v.length; ++i) { if (v[i][0] < 0) { ++this.nneg; t.push(v[i].slice()); } }
		t.push(v[0].slice());
		v = t;
		for (let i = 0; i != v.length; ++i) {
			from_term(bdd, i, dsz, bits, ar, v[i], this, m);
		}
		if (v.length == 1) {
			this.h = bdd.bdd_and(this.h, this.hsym);
		}
	}

	step(p) {
		p.dbs.setpow(p.db, this.npos, this.nneg, p.maxw, 0);
		const x = bdds.apply_and(p.dbs, p.db, p.prog, this.h);
		const y = p.prog.bdd_and(x, this.hsym);
		const z = p.prog.delhead(y, (this.npos + this.nneg) * p.bits * p.ar);
		p.dbs.setpow(p.db, 1, 0, p.maxw, 0);
		return z;
	}
}

// [pfp] logic program
class lp {
	constructor() {
		this._id = ++_counters.lp;
		// holds its own dict so we can determine the universe size
		this.d = new dict();
		this.dbs = null;     // db bdd (as db has virtual power)
		this.prog = null;    // prog bdd
		this.db = bdds.F;    // db's bdd root
		this.rules = [];     // p-datalog rules
		this.ar = 0;         // arity
		this.maxw = 0;       // number of bodies in db
		this.bits = 0;       // bitsize
	}
	// parse a string and returns its dict id
	str_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let _dbg_match;
		let r = null;
		s.s = s.s.replace(/^\s*(\??[\w|\d]+)\s*/, (_, t) => {
			r = this.d.get(t);
			return '';   // remove match from input
		})
		if (!r) {
			throw new Error(identifier_expected);
		}
		return r;
	}
	// read raw term (no bdd)
	term_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let r = [];
		skip_ws(s);
		if (s.s.length === 0) {
			return r;
		}
		let b;
		if (s.s[0] === '~') {
			b = -1;
			skip(s); skip_ws(s);
		} else {
			b = 1;
		}
		r.push(b);
		let i = 0;
		do {
			const c = s.s[i];
			if (/\s/.test(c)) i++;
			else {
				if (c === ',') {
					if (r.length === 1) {
						throw new Error(term_expected);
					}
					skip(s, ++i);
					return r;
				}
				if (c === '.' || c === ':') {
					if (r.length === 1) {
						throw new Error(term_expected);
					}
					skip(s, i);
					return r;
				}
				r.push(this.str_read(s)); i = 0;
			}
		} while (i < s.s.length);
		throw new Error(comma_dot_sep_expected);
	}
	// read raw rule (no bdd)
	rule_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let t, r = [];
		if ((t = this.term_read(s)).length === 0) {
			return r;
		}
		r.push(t);
		skip_ws(s);
		if (s.s[0] === '.') { // fact
			skip(s);
			return r;
		}
		if (s.s.length < 2 || (s.s[0] !== ':' && s.s[1] !== '-')) {
			throw new Error (sep_expected);
		}
		skip(s, 2);
		do {
			if ((t = this.term_read(s)).length === 0) {
				throw new Error(term_expected);
			}
			r.push(t);
			skip_ws(s);
			if (s.s[0] === '.') {
				skip(s);
				return r;
			}
			if (s.s[0] === ':') {
				throw new Error(unexpected_char);
			};
		} while (true);
	}
	// parses prog
	prog_read(prog) {
		const s   = { s: prog }; // source into string to parse
		this.ar   = 0;           // arity
		this.maxw = 0;           // number of rules
		this.db   = bdds.F;      // set db root to 0
		let l, r  = [];          // length and rules

		for (let t; !((t = this.rule_read(s)).length === 0); r.push(t)) {
			let i = 0;
			for (let x = t[0]; i < t.length; x = t[++i]) {
				this.ar = Math.max(this.ar, x.length - 1);
			}
			this.maxw = Math.max(this.maxw, t.length - 1);
		}
		for (let i = 0; i < r.length; i++) {
			for (let j = 0; j < r[i].length; j++) {
				l = r[i][j].length;
				if (l < (this.ar+1)) {
					r[i][j] = r[i][j]
						.concat(Array(this.ar + 1 - l).fill(dict.pad));
				}
			}
		}

		this.bits = this.d.bits;
		this.dbs = new bdds(this.ar * this.bits);
		this.prog = new bdds((this.maxw + 1) * this.ar * this.bits);

		for (let i = 0; i < r.length; i++) {
			const x = JSON.parse(JSON.stringify(r[i])); // clone through JSON
			if (x.length === 1) {
				this.db = this.dbs.bdd_or(this.db,
					new rule(this.dbs, x, this.bits, this.ar, this.d.nsyms).h);
			} else {
				this.rules.push(
					new rule(this.prog, x, this.bits, this.ar, this.d.nsyms));
			}
		}


		return r; // return raw rules/facts;
	}
	// single pfp step
	step() {
		let add = bdds.F;
		let del = bdds.F;
		for (let i = 0; i < this.rules.length; i++) {
			const r = this.rules[i];
			const x = r.step(this);
			this.prog.setpow(x, 1, 0, 1, -(r.npos + r.nneg) * this.bits * this.ar);
			const t = bdds.apply_or(this.prog, x, this.dbs, r.neg ? del : add);
			if (r.neg) { del = t; } else { add = t; }
			this.prog.setpow(x, 1, 0, 1, 0);
			this.dbs.memos_clear();
			this.prog.memos_clear();
		}
		let s = this.dbs.bdd_and_not(add, del);
		if (s === bdds.F && add !== bdds.F) {
			this.db = bdds.F; // detect contradiction
		} else {
			this.db = this.dbs.bdd_or(this.dbs.bdd_and_not(this.db, del), s);
		}
	}
	// pfp logic
	pfp() {
		let d;                       // current db root
		let t = 0;                   // step counter
		const s = [];                // db roots of previous steps
		do {
			d = this.db;         // get current db root
			s.push(d);           // store current db root into steps
			this.step();         // do pfp step
			// if db root already resulted from previous step
			if (s.includes(this.db)) {
				// this.printdb();
				// return true(sat) or false(unsat)
				return d === this.db;
			}
		} while (true);
	}
	// prints db (bdd -> tml facts)
	printdb(os) {
		console.log(out(os, this.dbs, this.db, this.bits, this.ar, this.dbs.pdim+this.dbs.ndim, this.d));
		if (!os) {
			const o = { dot: true, svg: false };
			// bdd_out(this.dbs, this.d, o);
			// bdd_out(this.prog, this.d, o);
		}
	}
	toString() {
		return out('', this.dbs, this.db, this.bits, this.ar, this.dbs.pdim+this.dbs.ndim, this.d);
	}
}
// removes comments
function string_read_text(data) {
	let s = '', skip = false;
	for (let n = 0; n < data.length; n++) {
		const c = data[n];
		if (c === '#') skip = true;
		else if (c === `\r` || c === `\n`) { skip = false; s += c; }
		else if (!skip) s += c;
	}
	return s;
}
// output content (TML facts) from the db
function out(os, b, db, bits, ar, w, d) {
	os = os || '';
	const t = b.from_bits(db, bits, ar, w);
	const s = [];
	for (let i = 0; i < t.length; i++) {
		const v = t[i];
		let ss = '';
		for (let j = 0; j < v.length; j++) {
			const k = v[j];
			if (k === 0) ss += '* ';
			else if (k < d.nsyms) ss += d.get(k) + ' ';
			else ss += `[${k}]`;
		}
		s.push(ss.slice(0, -1) + '.');
	}
	os += s.sort().join(`\n`);
	return os;
}

module.exports = (o = {}) => {
	options.recursive = o.hasOwnProperty('recursive')
		? o.recursive
		: options.recursive;
	// load rec or non_rec version of bdds class
	bdds = require('./bdds')(options);
	lp.bdds = bdds;
	lp.dict = dict;
	lp.rule = rule;
	lp.options = options
	lp.string_read_text = string_read_text;
	lp.out = out;
	return lp;
}
