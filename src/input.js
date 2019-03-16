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

const isalnum = c => {
	return /[\d\w]/.test(c) ||/\p{L}/u.test(c);
}
const isalpha = c => {
	return !(/\d/.test(c)) && (/\w/.test(c) || /\p{L}/u.test(c));
}
// skip_ws or skip 1 or more characters from parsing input
const skip = (s, n = 1) => { s.s = s.s.slice(n); s.p += n; }
const skip_ws = s => {
	const sl = s.s.length;
	s.s = s.s.replace(/^\s+/, '');
	s.p += sl - s.s.length;
};

function lex(s) {
	const ret = t => {
		const r = t.substring(0, s.p);
		s.p = 0;
		return r;
	}
	skip_ws(s);
	s.p = 0;
	if (!s.s.length) return null;
	let t = s.s;
	if (s.s[0] === '"') {
		skip(s);
		while (s.s[0] !== '"') {
			if (!s.s.length) throw new Error(unmatched_quotes);
			else if (s.s[0] === "'" && '\"'.indexOf(s.s[1]) !== -1) {
				throw new Error(err_escape);
			}
		}
		skip(s);
		return ret(t);
	}
	if (s.s[0] === '<') {
		skip(s);
		while (s.s[0] !== '>') {
			if (!s.s.length) throw new Error(err_fname);
			skip(s);
		}
		return ret(t);
	}
	if (s.s[0] === "'") {
		if (s.s[2] !== "'") throw new Error(err_quote);
		skip(s, 3);
		return ret(t);
	}
	if (s.s[0] === ':') {
		skip(s);
		if (s.s[0] == '-') { skip(s); return ':-'; }
		else throw new Error(err_chr);
	}
	if ("~.,{}@".indexOf(s.s[0]) !== -1) { const r = s.s[0]; skip(s); return r; }
	if (s.s[0] === '?' || s.s[0] == '-') skip(s);
	while (isalnum(s.s[0])) skip(s);
	return ret(t);
}

function prog_lex(cws) {
	const s = { s: cws, p: 0 };
	const r = [];
	do {
		let l = lex(s);
		if (l !== null) r.push(l);
	} while (s.s.length);
	return r;
}

class directive {
	constructor() { this.rel = null; this.arg = null; this.fname = false; }
	parse(l, pos) {
		if (l[pos.pos] !== '@') return false;
		rel = l[++pos.pos];
		if (l[++pos.pos] === '<') this.fname = true;
		else if (l[pos.pos] === '"') this.fname = false;
		else throw new Error(err_directive_arg);
		arg = l[pos.pos++];
		if (l[pos.pos++] !== '.') throw new Error(dot_expected);
		return true;
	}
}

function get_int(from) {
	const s = { s: from };
	let r = 0;
	let neg = false;
	if (s.s[0] === '-') {
		neg = true;
		skip(s);
	}
	if (!/\d+/.test(s.s)) throw new Error(err_int);
	r = Number(s.s);
	return neg ? -r : r;
}

const etype = Object.freeze({ SYM: 0, NUM: 1, CHR: 2, VAR: 3 });

class elem {
	parse(l, pos) {
		DBG(__parser(`elem.parse(${l[pos.pos]})`));
		const p = pos.pos;
		if (!isalnum(l[p] &&
			"'-?".indexOf(l[p]) !== -1)) return false;
		this.e = l[p];
		if (l[p] === "'") {
			const ll = l[p].length;
			if (ll !== 3 ||
				l[p][ll-1] !== "'") throw new Error(err_quote);
			this.type = etype.CHR;
			this.e = l[p].slice(1, ll-1);
		} else if (l[p][0] === '?') this.type = etype.VAR;
		else if (isalpha(l[p])) this.type = etype.SYM;
		else {
			this.type = etype.NUM;
			this.num = get_int(l[p]);
		}
		++pos.pos;
		return true;
	}
}

class raw_term {
	constructor() { this.neg = false; this.e = [] }
	parse(l, pos) {
		this.neg = l[pos.pos] === '~';
		if (this.neg) ++pos.pos;
		while ('.:,'.indexOf(l[pos.pos][0]) === -1) {
			const m = new elem()
			if (!m.parse(l, pos)) return false;
			this.e.push(m);
		};
		return true;
	}
}

class raw_rule {
	constructor() { this.h = new raw_term(); this.b = []; }
	parse(l, pos) {
		if (!this.h.parse(l, pos)) return false;
		if (l[pos.pos] === '.') { ++pos.pos; return true; }
		if (l[pos.pos++] !== ':-') throw new Error(err_chr);
		let t = new raw_term();
		while (t.parse(l, pos)) {
			this.b.push(t);
			if (l[pos.pos][0] === '.') { ++pos.pos; return true; }
			if (l[pos.pos][0] !== ',') throw new Error(err_term_or_dot);
			++pos.pos;
			t.e = [];
		}
		throw new Error(err_body);
	}
}

class raw_prog {
	constructor() { this.d = []; this.r = []; }
	parse(l, pos) {
		while (pos.pos < l.length && l[pos.pos] !== '}') {
			const d = new directive();
			const r = new raw_rule();
			if (d.parse(l, pos)) this.d.push(d);
			else if (r.parse(l, pos)) this.r.push(r);
			else return false;
		}
		return true;
	}
}

class raw_progs {
	constructor(str) {
		this.p = [];
		const s = string_read_text(str);
		let pos = { pos: 0 };
		const l = prog_lex(s);
		if (l[0] !== '{') {
			const x = new raw_prog();
			if (!x.parse(l, pos)) throw new Error(err_parse);
			this.p.push(x);
		} else {
			do {
				const x = new raw_prog();
				++pos.pos;
				if (!x.parse(l, pos)) throw new Error(err_parse);
				this.p.push(x);
				if (l[pos.pos++] !== '}') throw new Error(err_close_curly);
			} while (pos.pos < l.length);
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
// read prog from file
function file_read_text(fname) {
	const { readFileSync } = require('fs');
	return string_read_text(readFileSync(fname).toString());
}

module.exports = {
	etype, raw_progs,
	string_read_text, file_read_text
};
