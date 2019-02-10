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

// OPTIONS:
const options = {
	recursive: false // use rec or non rec algos
}
let bdds = null; // bdds class (to be loaded when required)
// load helper function for exporting bdds to dot, svg and/or png
// const { bdd_out } = require('./util');
const { int } = require('./int');

// debug functions
const _dbg_parser  = require('debug')('tml:parser');
const _dbg_dict    = require('debug')('tml:dict');
const _dbg_pfp     = require('debug')('tml:pfp');
const _dbg_rule    = require('debug')('tml:pfp:rule');
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
	// initialize syms and vars tables
	constructor() {
		this.syms = [ dict.pad ];
		this.vars = [ dict.pad ];
	}
	// gets/stores identifier (symbol or variable) and returns it's index
	get(s) {
		if (typeof(s) === 'number') {    // if s is number
			_dbg_dict(`get(${s}) by id = ${this.syms[s]}`);
			return this.syms[s];          //   return symbol by index
		}
		if (s[0] === '?') {             // variable...
			const p = this.vars.indexOf(s);
			if (p >= 0) {                 // if variable in this.vars
				_dbg_dict(`get(${s}) variable = -${p}`);
				return -p;                  //   return its index
			}
			this.vars.push(s);            // else store new variable
			_dbg_dict(`get(${s}) variable = -${this.vars.length-1} (created)`);
			return -(this.vars.length-1); //   and return its index
		}
		const p = this.syms.indexOf(s); // symbol...
		if (p >= 0) {                   // if symbol in this.syms
			_dbg_dict(`get(${s}) symbol = ${p}`);
			return p;                     // return its index
		}
		this.syms.push(s);              // else store new symbol
		_dbg_dict(`get(${s}) symbol = ${this.syms.length-1} (created)`);
		return this.syms.length-1;      // and return its index
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
		const BIT = (term, arg, b) => {
			return int(term).mul(int(bits)).add(int(b)).mul(int(ar)).add(int(arg));
		}
		let notpad = bdds.T;
		if (m.hasOwnProperty(vij)) {          // if seen
			_dbg_rule(`next m[vij]:${vij}:${m[vij]}`);
			for (let b = 0; b != bits; ++b) {   // for all bits
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
		_dbg_rule(`get_heads hsym:${hsym}`);
		let x, y, z;
		p.pdbs.setpow(p.db, this.w, p.maxw);
		if (bdds.leaf(p.db)) {
			_dbg_rule(`get_heads p.db:${p.db} (leaf)`);
			x = bdds.trueleaf(p.db) ? this.h : bdds.F;
			_dbg_rule(`     x: ${x} p.db:${p.db} this.h:${this.h}`);
			// remove nonhead variables
			y = bdds.apply_ex(p.pprog, x, p.pprog, this.x);
			_dbg_rule(`     y: ${y} p.db:${p.db} this.h:${this.h}`);
		} else {
			// rule/db conjunction
			_dbg_rule(`get_heads p.db:${p.db} this.h:${this.h}`);
			// optimized apply_and_ex
			y = bdds.apply_and_ex(p.pdbs, p.db, p.pprog, this.h, this.x,
				this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2));
			// not optimized apply_and_ex (does not work)
			// x = bdds.apply_and(p.pdbs, p.db, p.pprog, this.h);
			// _dbg_rule(`     x: after 'and' ${x} p.db:${p.db} this.h:${this.h}`);
			// y = bdds.apply_ex(p.pprog, x, p.pprog, this.x);
			_dbg_rule(`     y: after 'ex' ${y} this.x:`, this.x);
		}
		//y = bdds.apply_ex(p.pprog, x, p.pprog, this.x);
		z = p.pprog.permute(y, this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2)); // reorder
		_dbg_rule(`     z: after permute ${z} this.hvars:[`, this.hvars.join(', '), ']');
		z = p.pprog.bdd_and(z, hsym);
		_dbg_rule(`     z: ${z}`);
		p.pdbs.setpow(p.db, 1, p.maxw);
		return z;
	}
}

// a P-DATALOG rule in bdd form
class rule {
	// initialize rule
	constructor(bdd, v, bits, ar) {
		_dbg_rule(`new rule bits: ${bits}, ar: ${ar}, v:`, v);
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
		_dbg_rule(`    rule head: [ ${head.join(', ')} ]${this.neg?' neg':''}`);
		for (let i = 0; i != head.length; ++i) {
			if (head[i] < 0) { // var
				hvars[head[i]] = i;
				_dbg_rule(`         head[${i}] = ${head[i]} (var)`, hvars);
			} else { // term
				_dbg_rule(`         head[${i}] = ${head[i]} (sym)`);
				for (let b = 0; b != bits; ++b) {
					const BIT = (term,arg,b) => {
						return int(term).mul(int(bits)).add(int(b)).mul(int(ar)).add(int(arg));
					};
					const res = bdd.from_bit(BIT(0, i, b), (head[i]&(1<<b)) > 0);
					const _dbg = this.hsym;
					this.hsym = bdd.bdd_and(this.hsym, res);
					_dbg_rule(`           from_bit(BIT(0,${i},${b}):${BIT(0, i, b)}, ${(head[i]&(1<<b))>0}) = ${res} hsym ${_dbg}->${this.hsym}`);
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
		this.poss.hvars = Array(pvars);
		this.poss.x     = Array(pvars);
		this.negs.hvars = Array(nvars);
		this.negs.x     = Array(nvars);
		for (let i = 0; i < pvars; ++i) { this.poss.x[i] = false; this.poss.hvars[i] = i; }
		for (let i = 0; i < nvars; ++i) { this.negs.x[i] = false; this.negs.hvars[i] = i; }
		// load rule's terms and terms' arguments
		const k = { k: null }; // k and npad are objecs for passing by ref
		const npad = { npad: bdds.F };
		let bneg = false;
		for (let i = 0; i != v.length-1; ++i) {
			k.k = bdds.T;
			bneg = v[i][0] < 0;
			v[i].shift();
			for (let j = 0;	j != v[i].length; ++j) {
				const s = (bneg ? this.negs : this.poss);
				_dbg_rule(`\\from_arg i:${i}, j:${j}, k:${k.k}, vij:${v[i][j]}, bits:${bits}, ar:${ar}, npad:${npad.npad}, hvars:`, hvars);
				_dbg_rule(`m:`, m, 'v:', v);
				s.from_arg(bdd, i, j, k, v[i][j], bits, ar, hvars, m, npad);
				_dbg_rule(`/from_arg i:${i}, j:${j}, k:${k.k}, vij:${v[i][j]}, bits:${bits}, ar:${ar}, npad:${npad.npad}, hvars:`, hvars);
				_dbg_rule(`m:`, m, 'v:', v);
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
		this.dict = new dict(); // holds its own dict so we can determine the universe size
		this.pdbs = null;   // db bdd (as db has virtual power)
		this.pprog = null;  // prog bdd
		this.db = bdds.F;   // db's bdd root
		this.rules = [];    // p-datalog rules
		this.ar = 0;        // arity
		this.maxw = 0;      // number of bodies in db
		this.bits = 0;      // bitsize
	}
	// parse a string and returns its dict id
	str_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let _dbg_match;
		let r = null;
		s.s = s.s.replace(/^\s*(\??[\w|\d]+)\s*/, (_, t) => {
			r = this.dict.get(t);
			_dbg_match = t;
			return ''; // remove match from input
		})
		if (!r) {
			_dbg_parser(`str_read ERR from "${_dbg}..."`);
			throw new Error(identifier_expected);
		}
		_dbg_parser(`str_read "${_dbg_match}" (${r}) from "${_dbg}"`);
		return r;
	}
	// read raw term (no bdd)
	term_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let r = [];
		skip_ws(s);
		if (s.s.length === 0) {
			_dbg_parser(`term_read [] (empty string)`);
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
						_dbg_parser(`term_read ERR from "${_dbg}"`);
						throw new Error(term_expected);
					}
					skip(s, ++i);
					_dbg_parser(`term_read [ ${r.join(', ')} ] from "${_dbg}"`)
					return r;
				}
				if (c === '.' || c === ':') {
					if (r.length === 1) {
						_dbg_parser(`term_read ERR from "${_dbg}"`);
						throw new Error(term_expected);
					}
					skip(s, i);
					_dbg_parser(`term_read [ ${r.join(', ')} ] from "${_dbg}"`)
					return r;
				}
				r.push(this.str_read(s)); i = 0;
			}
		} while (i < s.s.length);
		_dbg_parser(`term_read ERR from "${_dbg}"`);
		throw new Error(comma_dot_sep_expected);
	}
	// read raw rule (no bdd)
	rule_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let t, r = [];
		if ((t = this.term_read(s)).length === 0) {
			_dbg_parser(`rule_read [] (empty string)`)
			return r;
		}
		r.push(t);
		skip_ws(s);
		if (s.s[0] === '.') { // fact
			skip(s);
			_dbg_parser(`rule_read [ ${r.map(sub=>`[ ${sub.join(', ')} ]`).join(', ')} ] from "${_dbg}"`)
			return r;
		}
		if (s.s.length < 2 || (s.s[0] !== ':' && s.s[1] !== '-')) {
			_dbg_parser(`rule_read ERR from "${_dbg}"`)
			throw new Error (sep_expected);
		}
		skip(s, 2);
		do {
			if ((t = this.term_read(s)).length === 0) {
				_dbg_parser(`rule_read ERR from "${_dbg}"`)
				throw new Error(term_expected);
			}
			r.splice(r.length-1, 0, t); // make sure head is last
			skip_ws(s);
			if (s.s[0] === '.') {
				skip(s);
				_dbg_parser(`rule_read [ ${r.map(sub=>`[ ${sub.join(', ')} ]`).join(', ')} ] from "${_dbg}"`)
				return r;
			}
			if (s.s[0] === ':') {
				_dbg_parser(`rule_read ERR from "${_dbg}"`)
				throw new Error(unexpected_char);
			};
		} while (true);
	}
	// parses prog
	prog_read(prog) {
		const s   = { s: prog }; // source into string to parse
		this.ar   = 0;      // arity
		this.maxw = 0;      // number of rules
		this.db   = bdds.F; // set db root to 0
		let l, r  = [];     // length and rules

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

		this.bits = this.dict.bits;
		_dbg_parser(`prog_read bits:${this.bits} ar:${this.ar} maxw:${this.maxw}`);
		this.pdbs = new bdds(this.ar * this.bits);
		this.pprog = new bdds(this.maxw * this.ar * this.bits);

		for (let i = 0; i < r.length; i++) {
			const x = r[i];
			if (x.length === 1) {
				_dbg_parser('prog_read store fact', x);
				this.db = this.pdbs.bdd_or(this.db, new rule(this.pdbs, x, this.bits, this.ar).poss.h);
			} else {
				_dbg_parser('prog_read store rule', x);
				this.rules.push(new rule(this.pprog, x, this.bits, this.ar));
			}
		}

		_dbg_pfp(`prog_read pdbs:`, this.pdbs.V.map(n=>`${this.pdbs.M[n.key]}=(${n.key})`).join(', '));
		_dbg_pfp(`prog_read pprog:`, this.pprog.V.map(n=>`${this.pprog.M[n.key]}=(${n.key})`).join(', '));
		_dbg_pfp(`prog_read bits:${this.bits} ar:${this.ar} maxw:${this.maxw} db(root):${this.db}`);
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
		_dbg_pfp('db:', this.db, 'add:', add, 'del:', del, 's:', s);
		if ((s === bdds.F) && (add !== bdds.F)) {
			this.db = bdds.F;
			_dbg_pfp('t db set:', this.db);
		} else {
			this.db = dbs.bdd_or(dbs.bdd_and_not(this.db, del), s);
			_dbg_pfp('f db set:', this.db);
		}
		dbs.memos_clear();
		prog.memos_clear();
	}
	// pfp logic
	pfp() {
		let d;                        // current db root
		let t = 0;                    // step counter
		const s = [];                 // db roots of previous steps
		do {
			d = this.db;                // get current db root
			s.push(d);                  // store current db root into steps
			// show step info
			this.printdb(`step: ${++t} nodes: ${this.pdbs.length} + ${this.pprog.length}\n`)
			_dbg_pfp(`____________________STEP_${t}________________________`);
			_dbg_pfp(`                                                     `);
			//return; /// only 1 step
			this.step();                // do pfp step
			_dbg_pfp('/STEP');
			if (s.find(db=>db.eq(this.db)) != undefined) {
			//if (s.includes(this.db)) {  // if db root already resulted from previous step
				this.printdb();           // print db
				return d.eq(this.db);     // return true(sat) or false(unsat)
			}
		} while (true);
	}
	// prints db (bdd -> tml facts)
	printdb(os) {
		out(os, this.pdbs, this.db, this.bits, this.ar, 1, this.dict);
		if (!os) {
			const o = { dot: true, svg: false };
			// bdd_out(this.pdbs, this.dict, o);
			// bdd_out(this.pprog, this.dict, o);
		}
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
	console.log(os);
}

module.exports = (o = {}) => {
	options.recursive = o.hasOwnProperty('recursive') ? o.recursive : options.recursive;
	bdds = require('./bdds')(options).bdds // load bdds class
	return {
		lp, string_read_text,
		dict, rule_items, rule,
		options, out
	}
}
