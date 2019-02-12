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
	get bits() { return 32 - Math.clz32(this.syms.length); }
	// initialize symbols and variables tables
	constructor() {
		this.syms = [ dict.pad ];
		this.vars = [ dict.pad ];
	}
	// gets and remembers the identifier and returns it's unique index
	// positive indexes are for symbols and negative indexes are for vars
	get(s) {
		if (typeof(s) === 'number') {     // if s is number
			return this.syms[s];      //     return symbol by index
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
// helper class for negs or poss of a rule
class rule_items {
	// initialize
	constructor(bits, ar) {
		this.h = bdds.T;  // bdd root
		this.w = 0;       // nbodies, will determine the virtual power
		this.x = [];      // existentials
		this.hvars = {};  // how to permute body vars to head vars
		this.bits = bits; // bitsize
		this.ar = ar;     // arity
	}

	// from arg
	// i = term's index in a rule
	// j = arg's index in a term
	// k?
	// vij = arg's varid
	// bits = bitsize
	// ar = arity
	// hvars = map of head vars to var's index in the head term
	// m = map of vars to their position in a rule
	// npad?
	from_arg(bdd, i, j, k, vij, bits, ar, hvars, m, npad) {
		// helper fn to count BIT from term, arg and bit
		const BIT = (term, arg, b) => ar*(term*bits+b)+arg;
		let notpad = bdds.T;
		if (m.hasOwnProperty(vij)) {                 // if seen
			for (let b = 0; b != bits; ++b) {    // for all bits
				k.k = bdd.bdd_and(k.k,
					bdd.from_eq(BIT(i, j, b), BIT(m[vij][0], m[vij][1], b)));
				this.x[BIT(i, j, b)] = true; // existential out
			}
		} else {
			m[vij] = [i, j];
			if (vij >= 0) { // sym
				for (let b = 0; b != bits; ++b) {
					k.k = bdd.bdd_and(k.k, bdd.from_bit(BIT(i, j, b), (vij&(1<<b))>0));
					this.x[BIT(i, j, b)] = true;
				}
			} else { // var
				for (let b = 0; b != bits; ++b) {
					notpad = bdd.bdd_and(notpad, bdd.from_bit(BIT(i, j, b), false));
				}
				npad.npad = bdd.bdd_or(npad.npad, notpad);
				if (hvars.hasOwnProperty(vij)) {
					const hvar = hvars[vij];
					for (let b = 0; b != this.bits; ++b) {
						if (BIT(i, j, b) != BIT(0, hvar, b)) {
							this.hvars[BIT(i, j, b)] = BIT(0, hvar, b);
						}
					}
				} else {
					for (let b = 0; b != this.bits; ++b) {
						this.x[BIT(i, j, b)] = true;
					}
				}
			}
		}
	}
	// get heads
	get_heads(p, hsym) {
		let x, y, z;
		p.pdbs.setpow(p.db, this.w, p.maxw);
		if (bdds.leaf(p.db)) {
			x = bdds.trueleaf(p.db) ? this.h : bdds.F;
			// remove nonhead variables
			y = bdds.apply_ex(p.pprog, x, p.pprog, this.x);
		} else {
			// rule/db conjunction
			// optimized apply_and_ex
			y = bdds.apply_and_ex(p.pdbs, p.db, p.pprog, this.h, this.x,
				this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2));
			// not optimized apply_and_ex (does not work)
			// x = bdds.apply_and(p.pdbs, p.db, p.pprog, this.h);
			// _dbg_rule(`     x: after 'and' ${x} p.db:${p.db} this.h:${this.h}`);
			// y = bdds.apply_ex(p.pprog, x, p.pprog, this.x);
		}
		// reorder
		z = p.pprog.permute(y, this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2));
		z = p.pprog.bdd_and(z, hsym);
		p.pdbs.setpow(p.db, 1, p.maxw);
		return z;
	}
}

// a P-DATALOG rule in bdd form
class rule {
	// initialize rule
	constructor(bdd, v, bits, ar) {
		this.hsym = bdds.T;
		this.hasnegs = false;
		this.poss = new rule_items(bits, ar);
		this.negs = new rule_items(bits, ar);
		// hvars = how to permute body vars to head vars
		//   = map of variable's varid to its index in head
		const hvars = {};
		const head = v[v.length-1];
		this.neg = head[0] < 0;
		head.shift();
		for (let i = 0; i != head.length; ++i) {
			if (head[i] < 0) { // var
				hvars[head[i]] = i;
			} else { // term
				for (let b = 0; b != bits; ++b) {
					const BIT = (term, arg, b) => ar*(term*bits+b)+arg;
					const res = bdd.from_bit(BIT(0, i, b), (head[i]&(1<<b))>0);
					const _dbg = this.hsym;
					this.hsym = bdd.bdd_and(this.hsym, res);
				}
			}
		}
		if (v.length === 1) {
			this.poss.h = this.hsym;
			return;
		}
		const m = {};
		for (let i=0; i != v.length-1; ++i) {
			if (v[i][0] < 0) {
				this.hasnegs = true;
				++this.negs.w;
			} else {
				++this.poss.w;
			}
		}
		// init poss' and negs' hvars and x
		const pvars = ((this.poss.w+1)*bits+1)*(ar + 2);
		const nvars = ((this.negs.w+1)*bits+1)*(ar + 2);
		this.poss.x     = Array(pvars).fill(false);
		this.negs.x     = Array(nvars).fill(false);
		this.poss.hvars = Array(pvars);
		this.negs.hvars = Array(nvars);
		for (let i = 0; i < pvars; ++i) { this.poss.hvars[i] = i; }
		for (let i = 0; i < nvars; ++i) { this.negs.hvars[i] = i; }

		// load rule's terms and terms' arguments
		const k = { k: null }; // k & npad are objecs for passing by ref
		const npad = { npad: bdds.F };
		let bneg = false;
		for (let i = 0; i != v.length-1; ++i) {
			k.k = bdds.T;
			bneg = v[i][0] < 0;
			v[i].shift();
			for (let j = 0;	j != v[i].length; ++j) {
				const s = (bneg ? this.negs : this.poss);
				s.from_arg(bdd, i, j, k, v[i][j], bits, ar, hvars, m, npad);
			}
			this.hasnegs = this.hasnegs || bneg;
			const s = bneg ? this.negs : this.poss;
			const h = bdd.bdd_and(k.k, bneg
				? bdd.bdd_and_not(s.h, k.k)
				: bdd.bdd_and(s.h, k.k));
			if (bneg) { this.negs.h = h; } else { this.poss.h = h; }
		}
		const s = bneg ? this.negs : this.poss;
		s.h = bdd.bdd_and_not(s.h, npad.npad);
	}
	// get heads
	get_heads(p) {
		if (this.hasnegs) {
			return p.pdbs.bdd_and(
				this.poss.get_heads(p, this.hsym),
				this.negs.get_heads(p, this.hsym));
		}
		return this.poss.get_heads(p, this.hsym);
	}
}

// [pfp] logic program
class lp {
	constructor() {
		this._id = ++_counters.lp;
		// holds its own dict so we can determine the universe size
		this.d = new dict();
		this.pdbs = null;    // db bdd (as db has virtual power)
		this.pprog = null;   // prog bdd
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
			r.splice(r.length-1, 0, t); // make sure head is last
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
		this.pdbs = new bdds(this.ar * this.bits);
		this.pprog = new bdds(this.maxw * this.ar * this.bits);

		for (let i = 0; i < r.length; i++) {
			const x = r[i];
			if (x.length === 1) {
				this.db = this.pdbs.bdd_or(this.db,
					new rule(this.pdbs, x, this.bits, this.ar).poss.h);
			} else {
				this.rules.push(new rule(this.pprog, x, this.bits, this.ar));
			}
		}


		return r; // return raw rules/facts;
	}
	// single pfp step
	step() {
		let add = bdds.F;
		let del = bdds.F;
		let s;
		const dbs = this.pdbs;
		const prog = this.pprog;
		for (let i = 0; i < this.rules.length; i++) {
			const r = this.rules[i];
			const t = bdds.apply_or(
				this.pprog, r.get_heads(this),
				this.pdbs, r.neg ? del : add);
			if (r.neg) { del = t; } else { add = t; }
		}
		s = dbs.bdd_and_not(add, del);
		if ((s === bdds.F) && (add !== bdds.F)) {
			this.db = bdds.F;
		} else {
			this.db = dbs.bdd_or(dbs.bdd_and_not(this.db, del), s);
		}
		dbs.memos_clear();
		prog.memos_clear();
	}
	// pfp logic
	pfp() {
		let d;                       // current db root
		let t = 0;                   // step counter
		const s = [];                // db roots of previous steps
		do {
			d = this.db;         // get current db root
			s.push(d);           // store current db root into steps
			// show step info
			console.log(`step: ${++t} nodes: ${this.pdbs.length}` +
				` + ${this.pprog.length}\n`)
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
		console.log(out(os, this.pdbs, this.db, this.bits, this.ar, 1, this.d));
		if (!os) {
			const o = { dot: true, svg: false };
			// bdd_out(this.pdbs, this.d, o);
			// bdd_out(this.pprog, this.d, o);
		}
	}
	toString() {
		return out('', this.pdbs, this.db, this.bits, this.ar, 1, this.d);
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
	const t = b.from_bits(db, bits, ar, w)
	os = os || '';
	for (let i = 0; i < t.length; i++) {
		const v = t[i];
		for (let j = 0; j < v.length; j++) {
			const k = v[j];
			if (!k) os += '* ';
			else if (k < d.nsyms) os += d.get(k) + ' ';
			else os += `[${k}]`;
		}
		os += `\n`;
	}
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
	lp.rule_items = rule_items;
	lp.options = options
	lp.string_read_text = string_read_text;
	lp.out = out;
	return lp;
}