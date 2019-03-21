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
	unmatched_quotes, err_fname, err_quote, err_chr, err_directive_arg,
	dot_expected, err_int, err_term_or_dot, err_parse, err_close_curly,
	err_escape, err_paren, err_rule_dir_prod_expected, err_body
	// err_prod
} = require('./messages');

const isspace = c => /\s/.test(c);
const isdigit = c => /\d/.test(c);
const isalnum = c => /[\d\w]/.test(c); // || /\p{L}/u.test(c); // illegal RE char in FF
const isalpha = c => !isdigit(c) && isalnum(c);

// skip 1 or more characters from parsing input
const skip = (s, n = 1) => { s.s = s.s.slice(n); s.p += n; }
// skip whitespace
const skip_ws = s => {
	const sl = s.s.length;
	s.s = s.s.replace(/^\s+/, '');
	s.p += sl - s.s.length;
};

function lex(s) {
	ID_TRC('lex');
	const ret = (t, n = 0) => {
		if (n > 0) {
			skip(s, n);
			return t;
		}
		const r = t.substring(0, s.p);
		s.p = 0;
		DBG(__lexer(r));
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
			else if (s.s[0] === '\\' && "\\\"".indexOf(s.s[1]) !== -1) {
				throw new Error(err_escape);
			}
			skip(s);
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
		skip(s);
		return ret(t);
	}
	if (s.s[0] === "'") {
		if (s.s[2] !== "'") throw new Error(err_quote);
		skip(s, 3);
		return ret(t);
	}
	if (s.s[0] === ':') {
		skip(s);
		if (s.s[0] === '-'
		|| s.s[0] === '=') { return ret(':-', 1); }
		else throw new Error(err_chr);
	}
	if ("!~.,(){}@".indexOf(s.s[0]) !== -1) { return ret(s.s[0], 1); }
	if ("?-".indexOf(s.s[0]) !== -1) skip(s);
	while (isalnum(s.s[0])) skip(s);
	return ret(t);
}

function prog_lex(cws) {
	ID_TRC('prog_lex');
	const s = { s: cws, p: 0 };
	const r = [];
	do {
		let l = lex(s);
		if (l !== null) r[r.length] = l;
	} while (s.s.length);
	DBG(__lexer('lexemes:', r));
	return r;
}

class directive {
	constructor() {
		this.rel = null;
		this.arg = null;
		this.fname = false; // is filename?
	}
	parse(l, pos) {
		ID_TRC('directive.parse');
		DBG(__parser(`directive.parse(${l[pos.pos]})`));
		if (l[pos.pos][0] !== '@') return false;
		this.rel = l[++pos.pos];
		DBG(__parser('rel', this.rel, 'cur:', l[pos.pos+1][0]));
		if (l[++pos.pos][0] === '<') this.fname = true;
		else if (l[pos.pos][0] === '"') this.fname = false;
		else throw new Error(err_directive_arg);
		this.arg = l[pos.pos++];
		if (l[pos.pos++][0] !== '.') throw new Error(dot_expected);
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
	if (!isdigit(s.s)) throw new Error(err_int);
	r = Number(s.s);
	return neg ? -r : r;
}

const etype = Object.freeze({ SYM: 0, NUM: 1, CHR: 2, VAR: 3, OPENP: 4, CLOSEP: 5 });
class elem {
	constructor() {
		this.num = 0; // number
		this.e = null; // lexeme
	}
	parse(l, pos) {
		ID_TRC('elem.parse');
		DBG(__parser(`elem.parse(${l[pos.pos]})`));
		const p = pos.pos; const c = l[p][0];
		if (c === "(") {
			this.e = l[pos.pos++];
			this.type = etype.OPENP;
			return true;
		}
		if (c === ")") {
			this.e = l[pos.pos++];
			this.type = etype.CLOSEP;
			return true;
		}
		if (!isalnum(c) && "'-?".indexOf(c) === -1) return false;
		this.e = l[p];
		if (c === "'") {
			const ll = l[p].length;
			if (ll !== 3 || l[p][2] !== "'") throw new Error(err_quote);
			this.type = etype.CHR;
			this.e = l[p].slice(1, ll-1);
		} else if (c === '?') this.type = etype.VAR;
		else if (isalpha(c)) this.type = etype.SYM;
		else {
			this.type = etype.NUM;
			this.num = get_int(l[p]);
		}
		++pos.pos;
		return true;
	}
}
elem.SYM = etype.SYM;
elem.NUM = etype.NUM;
elem.CHR = etype.CHR;
elem.VAR = etype.VAR;
elem.OPENP = etype.OPENP;
elem.CLOSEP = etype.CLOSEP;

class raw_term {
	constructor() {
		this.neg = false; // negated term?
		this.e = [] // array of elem
	}
	parse(l, pos) {
		ID_TRC('raw_term.parse');
		DBG(__parser(`raw_term.parse(${l[pos.pos]}, ${pos.pos})`));
		this.neg = l[pos.pos][0] === '~';
		if (this.neg) ++pos.pos;
		while ('.:,'.indexOf(l[pos.pos][0]) === -1) {
			const m = new elem()
			if (!m.parse(l, pos)) return false;
			this.e[this.e.length] = m;
		};
		let dep = 0;
		for (let i = 0; i != this.e.length; ++i) {
			if (this.e[i].type === elem.OPENP) ++dep;
			else if (this.e[i].type === elem.CLOSEP && !--dep)
				throw new Error(err_paren);
		}
		if (dep) throw new Error(err_paren);
		return true;
	}
}

class raw_rule {
	constructor() {
		this.b = [];
	}
	parse(l, pos) {
		ID_TRC('raw_rule.parse');
		DBG(__parser(`raw_rule.parse(${l[pos.pos]})`));
		const curr = pos.pos;
		this.goal = l[pos.pos][0] === '!';
		if (this.goal) {
			this.pgoal = l[++pos.pos][0] === '!';
			if (this.pgoal) { ++pos.pos; }
		}
		this.b[0] = new raw_term();
		if (!this.b[0].parse(l, pos)) { pos.pos = curr; return false; }
		if (l[pos.pos][0] === '.') { ++pos.pos; return true; }
		if (l[pos.pos][0] !== ':'
		||  l[pos.pos][1] !== '-') { pos.pos = curr; return false; }
		++pos.pos;
		let t = new raw_term();
		while (t.parse(l, pos)) {
			this.b[this.b.length] = t;
			if (l[pos.pos][0] === '.') { ++pos.pos; return true; }
			if (l[pos.pos][0] !== ',') throw new Error(err_term_or_dot);
			++pos.pos;
			t = new raw_term();
		}
		throw new Error(err_body);
	}
}

class production {
	constructor() {
		this.p = [];
	}
	parse(l, pos) {
		const curr = pos.pos;
		const e = new elem();
		e.parse(l, pos);
		if (l[pos.pos][0] !== ':' || l[pos.pos][1] !== '=') {
			pos = curr;
			return false;
		}
		++pos.pos;
		this.p[this.p.length] = e;
		for (;;) {
			if (l[pos.pos][0] === '.') { ++pos.pos; return true; }
			const e = new elem();
			if (!e.parse(l, pos)) return false;
			this.p[this.p.length] = e;
		}
		// throw new Error(err_prod); unreachable
	}
}

class raw_prog {
	constructor() {
		this.d = []; // arr of directive
		this.g = []; // arr of production
		this.r = []; // arr of raw_rule
	}
	parse(l, pos) {
		ID_TRC('raw_prog.parse');
		DBG(__parser(`raw_prog.parse(${l[pos.pos]})`));
		while (pos.pos < l.length && l[pos.pos] !== '}') {
			const d = new directive();
			if (d.parse(l, pos)) this.d[this.d.length] = d;
			else {
				const r = new raw_rule();
				if (r.parse(l, pos)) this.r[this.r.length] = r;
				else {
					const p = new production();
					if (p.parse(l, pos)) this.g[this.g.length] = p;
					else return false;
				}
			}
		}
		return true;
	}
}

class raw_progs {
	constructor(str) {
		ID_TRC('new_raw_progs');
		this.p = []; // arr of raw_prog
		const s = string_read_text(str);
		let pos = { pos: 0 };
		const l = prog_lex(s);
		if (l[0] !== '{') {
			const x = new raw_prog();
			if (!x.parse(l, pos)) throw new Error(err_rule_dir_prod_expected);
			this.p[this.p.length] = x;
		} else {
			do {
				const x = new raw_prog();
				++pos.pos;
				if (!x.parse(l, pos)) throw new Error(err_parse);
				this.p[this.p.length] = x;
				if (l[pos.pos++] !== '}') throw new Error(err_close_curly);
			} while (pos.pos < l.length);
		}
	}
}
// removes comments
function string_read_text(data) {
	ID_TRC('string_read_text');
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
	ID_TRC('file_read_text');
	const { readFileSync } = require('fs');
	return string_read_text(readFileSync(fname).toString());
}

module.exports = {
	isspace, isalnum, isalpha, isdigit,
	elem, raw_progs,
	string_read_text, file_read_text
};
