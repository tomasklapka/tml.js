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

const { pad } = require('./lp');
const { err_sym_digit } = require('./messages');

// dict represents strings as unique integers
class dict {
	constructor() {
		this.syms = [ pad ];
		this.vars = [ pad ];
		this.nums = 0;
		this.last = 1;
		this.str_chr = 'a';
		this.str_nums = null;
	}
	// nsyms = number of stored symbols
	get nsyms() { return this.syms.length + this.nums; }
	// returns bit size of the dictionary
	get bits() { return msb(this.nsyms); }
	// gets and remembers the identifier and returns it's unique index
	// positive indexes are for symbols and negative indexes are for vars
	get(s = null) {
		if (s === null) {
			return get(`%${this.last}`);
		}
		if (typeof(s) === 'number') {     // if s is number
			if (s > this.nums) return this.syms[s - this.nums];
			if (s < 256) {
				this.str_chr = String.fromCharCode(--s);
				return this.str_chr;
			}
			this.str_nums = `${s - 256}`;
			return this.str_nums;
			// if (s < this.syms.length) {
			// 	const r = s < 0 ? this.vars[-s] : this.syms[s];
			// 	DBG(__dict(`get(${s}) by id = ${r}`))
			// 	return r;
			// }
			// const r = s - this.syms.length;
			// DBG(__dict(`get(${s}) number = ${r}`))
			//return r;                 //     return symbol by index
		}
		if (!s || !s.length) return pad;
		if (/\d/.test(s[0])) throw new Error(err_sym_digit);
		if (s[0] === '?') {               // if s is variable
			const p = this.vars.indexOf(s);
			if (p >= 0) {             //     if variable already in dict
				DBG(__dict(`get(${s}) variable = -${p}`));
				return -p;        //        return its index negated
			}
			this.vars[this.vars.length] = s; //     else store the variable in dict
			DBG(__dict(`get(${s}) variable = -${this.vars.length-1} (created)`))
			return -(this.vars.length-1); //     and return its index negated
		}
		const p = this.syms.indexOf(s);   // if s is symbol
		if (p >= 0) {                     //     if is symbol in dict
			DBG(__dict(`get(${s}) symbol = ${p}`))
			return p;                 //         return its index
		}
		this.syms[this.syms.length] = s; //     else store the symbol in dict
		DBG(__dict(`get(${s}) symbol = ${this.syms.length-1} (created)`))
		return this.syms.length-1;        //         and return its index
	}

}

module.exports = { dict };
