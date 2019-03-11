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

const lp = require("./lp")();

// debug functions
const _dbg_parser  = require('debug')('tml:parser');
const _dbg_dict    = require('debug')('tml:dict');
const _dbg_bdd     = require('debug')('tml:bdd:parsed');
const _dbg_pfp     = require('debug')('tml:pfp');

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
			_dbg_dict(`get(${s}) by id = ${r}`);
			return r;                 //     return symbol by index
		}
		if (s[0] === '?') {               // if s is variable
			const p = this.vars.indexOf(s);
			if (p >= 0) {             //     if variable already in dict
				_dbg_dict(`get(${s}) variable = -${p}`);
				return -p;        //        return its index negated
			}
			this.vars.push(s);        //     else store the variable in dict
			_dbg_dict(`get(${s}) variable = -${this.vars.length-1} (created)`);
			return -(this.vars.length-1); //     and return its index negated
		}
		const p = this.syms.indexOf(s);   // if s is symbol
		if (p >= 0) {                     //     if is symbol in dict
			_dbg_dict(`get(${s}) symbol = ${p}`);
			return p;                 //         return its index
		}
		this.syms.push(s);                //     else store the symbol in dict
		_dbg_dict(`get(${s}) symbol = ${this.syms.length-1} (created)`);
		return this.syms.length-1;        //         and return its index
	}
}

class driver {
	constructor() {
		this.d = new dict();
		this.p = null;
	}
	get db() { return this.p.getdb(); }
	printdb(os = '', t = this.db) {
		const s = [];
		for (let i = 0; i < t.length; i++) {
			const v = t[i];
			let ss = '';
			for (let j = 0; j < v.length; j++) {
				const k = v[j];
				if (k === dict.pad) ;
				else if (k < this.d.nsyms) ss += this.d.get(k) + ' ';
				else ss += '[' + k + '] ';
			}
			s.push(ss.slice(0, -1) + '.');
		}
		os += s.sort().join(`\n`);
		return os;
	}
	toString() { return this.printdb(); }

	// pfp logic
	pfp() {
		let d;                       // current db root
		let t = 0;                   // step counter
		const s = [];                // db roots of previous steps
		do {
			d = this.p.db;       // get current db root
			s.push(d);           // store current db root into steps
			_dbg_pfp(`____________________STEP_${++t}________________________`);
			_dbg_pfp(`                                                     `);
			this.p.fwd();         // do pfp step
			_dbg_pfp(`___________________/STEP_${t}________________________`);
			// if db root already resulted from previous step
			if (s.includes(this.p.db)) {
				if (d === this.p.db) {
					console.log(this.printdb());
					return true;
				} else {
					return false;
				}
			} else {
				this.printdb();
			}
		} while (true);
	}
	// parse a string and returns its dict id
	str_read(s) {
		const _dbg = s.s.slice(0, s.s.indexOf(`\n`));
		let _dbg_match;
		let r = null;
		s.s = s.s.replace(/^\s*(\??[\w|\d]+)\s*/, (_, t) => {
			r = this.d.get(t);
			_dbg_match = t;
			return '';   // remove match from input
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
					_dbg_parser(`term_read [ ${r.join(', ')} ] from "${_dbg}"`);
					return r;
				}
				if (c === '.' || c === ':') {
					if (r.length === 1) {
						_dbg_parser(`term_read ERR from "${_dbg}"`);
						throw new Error(term_expected);
					}
					skip(s, i);
					_dbg_parser(`term_read [ ${r.join(', ')} ] from "${_dbg}"`);
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
			r.push(t);
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
		let ar    = 0;           // arity
		let l, r  = [];          // length and rules

		for (let t; !((t = this.rule_read(s)).length === 0); r.push(t)) {
			let i = 0;
			for (let x = t[0]; i < t.length; x = t[++i]) {
				ar = Math.max(ar, x.length - 1);
			}
		}
		_dbg_dict(this.d);
		this.p = new lp(this.d.bits, ar, this.d.nsyms);
		for (let i = r.length-1; i >= 0; i--) {
			for (let j = 0; j < r[i].length; j++) {
				l = r[i][j].length;
				if (l < ar+1) {
					r[i][j] = r[i][j].concat(Array(ar + 1 - l).fill(dict.pad));
				}
			}
			_dbg_parser(`p.rule_add(r[${i}]):`, r[i]);
			this.p.rule_add(r[i]);
		}
		_dbg_bdd(`prog_read bdd:`, this.p.bdds.V.map(n=>`${this.p.bdds.M[n.key]}=(${n.key})`).join(', '));
		_dbg_bdd(`prog_read bits:${this.d.bits} ar:${ar}`);
		return r; // return raw rules/facts;
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

// loads string from stream
function load_stream(stream) {
	return new Promise((resolve, reject) => {
		let r = '';                         // resulting string
		stream.on('readable', () => {       // if we can read
			let chunk;
			while ((chunk = stream.read()) !== null)
				r += chunk;                 // add stream chunks to string
		});
		stream.on('end', () => resolve(r)); // resolve string
		stream.on('error', reject);         // reject if error
	});
}

// main
async function main() {
	let s = null;
	//// input for IDE debugging (avoids configuration of stdin)
	// s = "e 1 2. e 2 3. e 3 1. e ?x ?y :- e ?x ?z, e ?z ?y.";
	// s = "father Tom Amy. parent ?X ?Y :- father ?X ?Y.";
	// s = "1 2. 2 1. ?x ?y :- ?y ?x.";
	// s = "1 2. 3 4. ?x ?y :- ?y ?x.";
	// unless s, read source from stdin
	if (s === null) {
		try {
			process.stdin.setEncoding('utf8');
			s = string_read_text(await load_stream(process.stdin));
		} catch (err) {   // stdin read error
			console.log('Read error:', err);
			return 4;
		}
	}
	const d = new driver();
	try {
		d.prog_read(s); // parse source from s
	} catch (err) {
		console.log('Parse error:', err);
		return 3;
	}
	let r = false;
	try {
		r = d.pfp();    // run pfp logic program
	} catch (err) {
		console.log('PFP error', err);
		return 2;
	}
	if (!r) {
		console.log('unsat');
		return 1;
	}
	return 0;
}

module.exports = { driver, string_read_text, load_stream, main, dict, lp };
