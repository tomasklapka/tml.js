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

//##ifdef DEBUG
//##define DBG(x) x
//##ifdef TRACE
//##define TRC(x) __cout(x)
//##else
//##define TRC(x)
//##endif
//##include "__debug.js"
//##else
//##define DBG(x)
//##define TRC(x)
//##endif

const { etype, raw_progs } = require('./input');
const { bdds } = require('./bdds');
const { lp } = require("./lp");
let pad = require("./lp").pad;

class driver {
	constructor(str, proof) {
		// initialize symbols and variables tables
		this.syms = [ pad ];
		this.vars = [ pad ];
		this.strs = [];
		this.progs = [];
		this.proofs = [];
		this.mult = false;
		this.nums = 0;
		let rp;
		try {
			rp = new raw_progs(str); // parse source from s
		} catch (err) {
			console.log('Parse error:', err);
			return
		}
		for (let n = 0; n != rp.p.length; ++n) {
			this.strs[this.strs.length] = {};
			for (let k = 0; k != rp.p[n].d.length; ++k) {
				const d = rp.p[n].d[k];
				if (d.fname) {
					this.nums = Math.max(this.nums, 256 + d.arg.length-2);
				} else {
					this.nums = Math.max(this.nums, 256 + d.arg.length)
				}
			}
		}
		pad = this.dict_get('', 0);
		let ar = 0;
		for (let n = 0; n != rp.p.length; ++n) {
			for (let k = 0; k != rp.p[n].d.length; ++k) {
				ar = Math.max(ar, 4);
				const d = rp.p[n].d[k];
				const str = d.arg.slice(1, d.arg.length-1);
				this.strs[n][this.dict_get(d.rel)] = d.fname ? file_read_text(str) : str;
			}
			for (let i = 0; i != rp.p[n].r.length; ++i) {
				const x = rp.p[n].r[i];
				ar = Math.max(ar, x.h.e.length);
				for (let j = 0; j != x.h.e.length; ++j) {
					const e = x.h.e[j];
					if (e.type === etype.SYM) {
						this.dict_get(e.e);
					}
				}
				for (let k = 0; k != x.b.length; ++k) {
					const y = x.b[k];
					ar = Math.max(ar, y.e.length);
					for (let j = 0; j != y.e.length; ++j) {
						const e = y.e[j];
						if (e.type === etype.SYM) {
							this.dict_get(e.e);
						}
					}
				}
			}
		}
		for (let n = 0; n != rp.p.length; ++n) {
			const m = [];
			this.proofs.push([]);
			for (let i = 0; i != rp.p[n].r.length; ++i) {
				const x = rp.p[n].r[i];
				m.push(this.get_rule(x));
			}
			this.prog_add(m, ar, this.strs[n], proof ? this.proofs[this.proofs.length] : null);
		}
	}
	// nsyms = number of stored symbols
	get nsyms() { return this.syms.length + this.nums; }
	// returns bit size of the dictionary
	get bits() { return 32 - Math.clz32(this.nsyms); }
	// gets and remembers the identifier and returns it's unique index
	// positive indexes are for symbols and negative indexes are for vars
	dict_get(s) {
		if (typeof(s) === 'number') {     // if s is number
			if (s < this.syms.length) {
				const r = s < 0 ? this.vars[-s] : this.syms[s];
				DBG(__dict(`dict_get(${s}) by id = ${r}`))
				return r;
			}
			const r = s - this.syms.length;
			DBG(__dict(`dict_get(${s}) number = ${r}`))
			return r;                 //     return symbol by index
		}
		if (!s || !s.length) return pad;
		if (/\d/.test(s[0])) throw new Error("symbol name cannot begin with a digit");
		if (s[0] === '?') {               // if s is variable
			const p = this.vars.indexOf(s);
			if (p >= 0) {             //     if variable already in dict
				DBG(__dict(`dict_get(${s}) variable = -${p}`));
				return -p;        //        return its index negated
			}
			this.vars.push(s);        //     else store the variable in dict
			DBG(__dict(`dict_get(${s}) variable = -${this.vars.length-1} (created)`))
			return -(this.vars.length-1); //     and return its index negated
		}
		const p = this.syms.indexOf(s);   // if s is symbol
		if (p >= 0) {                     //     if is symbol in dict
			DBG(__dict(`dict_get(${s}) symbol = ${p}`))
			return p;                 //         return its index
		}
		this.syms.push(s);                //     else store the symbol in dict
		DBG(__dict(`dict_get(${s}) symbol = ${this.syms.length-1} (created)`))
		return this.syms.length-1;        //         and return its index
	}

	printbdd(os = '', t) {
		if (!Array.isArray(t)) {
			t = this.progs[t].db;
		}
		const s = [];
		for (let i = 0; i < t.length; i++) {
			const v = t[i];
			let ss = '';
			for (let j = 0; j < v.length; j++) {
				const k = v[j];
				if (k === pad) ss += '* ';
				else if (k < this.nsyms) ss += this.dict_get(k) + ' ';
				else ss += '[' + k + '] ';
			}
			s.push(ss);
		}
		os += s.sort().join(`\n`);
		return os;
	}
	printdb(os) {
		return this.printbdd(os, this.progs[this.progs.length-1].getdb())
	}
	toString() { return this.printdb(); }

	get_term(r) {
		const t = [];
		t.push(r.neg ? -1 : 1);
		for (let i = 0; i != r.e.length; ++i) {
			const e = r.e[i];
			if (e.type === etype.NUM) t.push(e.num);
			else if (e.type === etype.CHR) t.push(e.e[0]);
			else t.push(this.dict_get(e.e));
		}
		return t;
	}

	get_rule(r) {
		const m = [];
		m.push(this.get_term(r.h));
		for (let i = 0; i != r.b.length; ++i) {
			m.push(this.get_term(r.b[i]));
		}
		return m;
	}

	term_pad(t, ar) {
		const l = t.length;
		if (l < ar+1) {
			t = t.concat(Array(ar + 1 - l).fill(pad));
		}
	}

	rule_pad(t, ar) {
		const r = t.slice();
		for (let i = 0; i != r.length; ++i) {
			this.term_pad(r[i], ar);
		}
		return r;
	}

	prog_add(m, ar, s, proof) {
		const p = new lp(this.bits, ar, this.nsyms);
		this.progs.push(p);
		const keys = Object.keys(s);
		for (let i = 0; i != keys.length; ++i) {
			const x = s[keys[i]];
			for (let n = 0; n != x.length; ++n) {
				p.rule_add(rule_pad([ [ 1, n, n + 256, x[n]] ], ar), proof);
			}
		}
		while (m.length) {
			const x = m.shift();
			p.rule_add(this.rule_pad(x, ar), proof);
		}
		DBG(__bdd(`prog_read bdd:`, p.bdd.V.map(n=>`${p.bdd.M[n.key]}=(${n.key})`).join(', ')))
		DBG(__bdd(`prog_read bits:${this.bits}`))
		return p;
	}
	// pfp logic
	pfp(p, proof = null, add) {
		if (proof === null && (p === true || p === false)) {
			proof = p;
			let r; // = true; // ?
			const sz = this.progs.length;
			const add = { add: 0 };
			this.pfp(this.progs[0], proof ? this.proofs[0] : 0, add);
			for (let n = 1; n != sz; ++n) {
				this.progs[n].db = this.progs[n-1].db;
				r = this.pfp(this.progs[n], proof ? this.proofs[n] : 0, add);
				if (!r) return false;
			}
			console.log(this.printdb('', sz - 1));
			const q = this.progs[this.progs.length-1];
			if (proof) this.printbdd(`proof:\n`, add.add, q.bits, q.proof_arity())
			return true; //r;
		}
		const pf = [];
		let d;                       // current db root
		let t = 0;
		let step = 0;                // step counter
		const s = [];                // db roots of previous steps
		const del = {};
		do {
			add.add = bdds.F;
			del.del = bdds.F;
			d = p.db;       // get current db root
			s.push(d);           // store current db root into steps
			DBG(__pfp(`____________________STEP_${++step}________________________`))
			DBG(__pfp(`                                                     `))
			p.fwd(add, del, proof ? pf : 0);         // do pfp step
			DBG(__pfp(`___________________/STEP_${step}________________________`))
			t = p.bdd.and_not(add.add, del.del);
			DBG(__pfp('db:', p.db, 'add:', add.add, 'del:', del.del, 't:', t))
			if (t === bdds.F && add.add !== bdds.F) {
				DBG(__pfp('db set (contradiction):', p.db));
				return false;
			} else {
				p.db = p.bdd.or(p.bdd.and_not(p.db, del.del), t);
				DBG(__pfp('db set:', p.db));
			}
			// if db root already resulted from any previous step
			if (d === p.db) break;
			if (s.includes(p.db)) return false; // unsat
		} while (true);
		if (!proof) return true;

		const ar = p.proof_arity();
		for (let i = 0; i != proof.length; ++i) { console.log(proof[i]); }
		const q = this.prog_add(
			JSON.parse(JSON.stringify(proof)),
			ar, {}, false);
		q.db = bdds.F;
		add.add = bdds.F;
		del.del = bdds.F;
		q.db = q.get_varbdd();
		q.fwd(add, del, 0);
		console.log(this.printbdd('', add.add));
		return true;
	}
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
	// s = `a b. c d. f e. ?x ?y :- ?y ?x. ?x ?x :- ?x e.`;
	// unless s, read source from stdin
	if (s === null) {
		try {
			process.stdin.setEncoding('utf8');
			s = await load_stream(process.stdin);
		} catch (err) {   // stdin read error
			console.log('Read error:', err);
			return 4;
		}
	}
	const proof = process.argv.length === 3 && process.argv[2] === '-p';
	const d = new driver(s, proof);
	let r = false;
	try {
		r = d.pfp(proof); // run pfp logic program
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

module.exports = { main, driver, lp };
