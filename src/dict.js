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
	constructor(driver) {
		this.syms = [ pad ];
		this.syms_dict = {};
		this.vars = [ pad ];
		this.nums = 0;
		this.last = 1;
		this.str_chr = 'a';
		this.str_nums = null;
		this.driver = driver;
	}
	// nsyms = number of stored symbols
	get nsyms() { return this.syms.length + this.nums; }
	// returns bit size of the dictionary
	get bits() { return msb(this.nsyms); }

	get_by_int(t = null) {
		DBG(__dict(`get_by_int(${t})`));
		if (t > this.nums) return this.syms[t - this.nums];
		if (t < 256) {
			this.str_chr = String.fromCharCode(--t);
			return this.str_chr;
		}
		this.str_nums = `${t - 256}`;
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

	get_by_lex(s) {
		DBG(__dict(`get_by_lex(${s})`));
		if (!s || s.length === 0) return pad;
		if (/\d/.test(s[0])) throw new Error(err_sym_digit);
		if (s[0] === '?') {
			const p = this.vars.indexOf(s);
			if (p >= 0) {
				DBG(__dict(`get_by_lex(${s}) variable = -${p}`));
				return -p;
			}
			this.vars[this.vars.length] = s;
			DBG(__dict(`get_by_lex(${s}) variable = -${this.vars.length-1} (created)`))
			return -(this.vars.length-1);
		}
		if (this.syms_dict.hasOwnProperty(s)) {
			DBG(__dict(`get_by_lex(${s}) symbol = ${this.syms_dict[s]}`))
			return this.syms_dict[s];
		}
		this.syms[this.syms.length] = s;
		this.syms_dict[s] = this.syms.length + this.nums - 1;
		DBG(__dict(`get_by_lex(${s}) symbol = ${this.syms_dict[s]} (created)`))
		return this.syms_dict[s];
	}

	get_by_str(s = null) {
		DBG(__dict(`get_by_str(${s})`));
		if (s === null) {
			return this.get_by_str(`%${this.last}`);
		}
		if (this.syms_dict.hasOwnProperty(s)) {
			return this.syms_dict[s];
		}
		if (!this.driver.strs_extra.includes(s)) {
			this.driver.strs_extra[this.driver.strs_extra] = s;
		}
		this.syms[this.syms.length] = s;
		this.syms_dict[s] = this.syms.length + this.nums - 1;
		return this.syms_dict[s];
	}

}

module.exports = { dict };
