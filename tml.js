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

// This is a Javascript rewrite of TML by Tomáš Klapka <tomas@klapka.cz>

const { bdds } = require('./bdds');
const { bdd_out } = require('./util');

// debug functions
const _dbg_parser  = require('debug')('tml:parser');
const _dbg_dict    = require('debug')('tml:dict');
const _dbg_pfp     = require('debug')('tml:pfp');

// internal counters for lps
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
  // initialize syms and vars tables
	constructor() {
		this.syms = [ dict.pad ];
		this.vars = [ dict.pad ];
  }
  // gets/stores identifier (symbol or variable) and returns it's index
	get(s) {
    if (typeof(s) == 'number') {
      _dbg_dict(`get(${s}) by id = ${this.syms[s]}`);
      return this.syms[s];                          // if s is number return symbol by index
    }
		if (s[0] === '?') {                             // variable:
      const p = this.vars.indexOf(s);
      if (p > 0) {
        _dbg_dict(`get(${s}) variable = -${p}`);
        return -p;                                  // if variable in this.vars, return its index
      }
      this.vars.push(s);                            // else store new variable
      _dbg_dict(`get(${s}) variable = -${this.vars.length-1} (created)`);
			return -(this.vars.length-1);                 // and return its index
    }
    const p = this.syms.indexOf(s);                 // symbol
    if (p > 0) {
      _dbg_dict(`get(${s}) symbol = ${p}`);
      return p;                                     // if symbol in this.syms, return its index
    }
		this.syms.push(s);                              // else store new symbol
    _dbg_dict(`get(${s}) symbol = ${this.syms.length-1} (created)`);
		return this.syms.length-1;                      // and return its index
  }
  // returns number of stored symbols
	nsyms() { return this.syms.length; }
  // counts bit size of the dictionary
	bits() { return 32 - Math.clz32(this.syms.length); }
}

// helper class for negs or poss of a rule
class rule_items {
  // initialize
  constructor(bits, ar) {
    this.h = bdds.T;            // bdd root
    this.w = 0;                 // nbodies, will determine the virtual power
    this.x = [];                // existentials
    this.hvars = {};            // how to permute body vars to head vars
    this.bits = bits;           // bitsize
    this.ar = ar;               // arity
  }

  // from arg
	from_arg(bdd, i, j, k, vij, bits, ar, hvars, m, npad) {
    // helper fn to count BIT from term, arg and bit
    const BIT = (term, arg, b) => ((term*bits+b)*ar+arg);

    let notpad = bdds.T;
		if (m.hasOwnProperty(vij)) {          // if seen
			for (let b = 0; b != bits; ++b) {   // for all bits
        k.k = bdd.bdd_and(k.k,            // 
          bdd.from_eq(BIT(i, j, b), BIT(m[vij][0], m[vij][1], b)));
        this.x[BIT(i, j, b)] = true; // existential out
      }
		} else {
			m[vij] = [i, j];
			if (vij >= 0)
				for (let b = 0; b != bits; ++b) {
          k.k = bdd.bdd_and(k.k, bdd.from_bit(BIT(i, j, b), vij&(1<<b)));
					this.x[BIT(i, j, b)] = true;
				}
			else {
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
      y = bdds.apply(p.pprog, this.x, p.pprog, // remove nonhead variables
        new op_exists(this.x));
    } else {
      y = bdds.apply_and_ex_perm(p.pdbs, p.db, p.pprog, this.h, this.x,
        this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2)); // rule/db conjunction
    }
    z = p.pprog.permute(y, this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2)); // reorder
    z = p.pprog.bdd_and(z, hsym);
    p.pdbs.setpow(p.db, 1, p.maxw);
    return z;
  }
}

// a P-DATALOG rule in bdd form
class rule {
  // initialize rule
  constructor(bdd, v, bits, ar) {
    this.poss = new rule_items(bits, ar);
    this.negs = new rule_items(bits, ar);
    this.poss.h = this.negs.h = this.hsym = bdds.T;
    this.poss.w = this.negs.w = 0;
    this.hasnegs = false;
    const k = { k: null }; // k and npad are objecs for passing by ref
		const npad = { npad: bdds.F };
		const hvars = {}; // how to permute body vars to head vars
    const head = v[v.length-1];
    let bneg = false;
    this.neg = head[0] < 0;
    head.shift();
		for (let i = 0; i != head.length; ++i) {
			if (head[i] < 0) hvars[head[i]] = i; // var
			else for (let b = 0; b != bits; ++b) {
        const BIT = (term,arg,b)=>((term*bits+b)*ar+arg);
				const res = bdd.from_bit(BIT(0, i, b), (head[i]&(1<<b)) > 0);
			  this.hsym = bdd.bdd_and(this.hsym, res);
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
    const pvars = ((this.poss.w+1)*bits+1)*(ar + 2);
    const nvars = ((this.negs.w+1)*bits+1)*(ar + 2);
    this.poss.hvars = Array(pvars);
    this.poss.x = Array(pvars);
    this.negs.hvars = Array(nvars);
    this.negs.x = Array(nvars);
    for (let i = 0; i < pvars; ++i) { this.poss.x[i] = false; this.poss.hvars[i] = i; }
    for (let i = 0; i < nvars; ++i) { this.negs.x[i] = false; this.negs.hvars[i] = i; }
    for (let i = 0; i != v.length-1; ++i) {
      k.k = bdds.T;
      bneg = v[i][0] < 0;
      v[i].shift();
      for (let j = 0;	j != v[i].length; ++j) {
        const s = (bneg ? this.negs : this.poss);
        s.from_arg(bdd, i, j, k, v[i][j], bits, ar, hvars, m, npad);
      }
      this.hasnegs |= bneg;
      const s = bneg ? this.negs : this.poss;
      s.h = bdd.bdd_and(k.k, bneg
        ? bdd.bdd_and_not(s.h, k.k)
        : bdd.bdd_and(s.h, k.k));
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
    this.id = ++_counters.lp;
		this.dict = new dict(); // holds its own dict so we can determine the universe size
    this.pdbs = null;   // db bdd (as db has virtual power)
    this.pprog = null;  // prog bdd
		this.db = bdds.F;   // db's bdd root
    this.rules = [];
    this.ar = 0;
    this.maxw = 0;
    this.bits = 0;
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
    const s = { s: prog };
		this.ar = 0;
		this.maxw = 0;
		this.db = bdds.F;
		let l, r = [];
		for (let t; !((t = this.rule_read(s)).length === 0); r.push(t)) {
			let i = 0;
			for (let x = t[0]; i < t.length; x = t[++i]) {
				this.ar = Math.max(this.ar, x.length - 1);
			}
			this.maxw = Math.max(this.maxw, t.length - 1);
		}
		for (let i = 0; i < r.length; i++) {
			for (let j = 0; j < r[i].length; j++) {
				if ((l = r[i][j].length) < this.ar+1) {
					r[i][j] = r[i][j]
						.concat(Array(this.ar + 1 - l).fill(dict.pad));
				}
			}
    }

		this.bits = this.dict.bits();
    _dbg_parser(`prog_read bits:${this.bits} ar:${this.ar} maxw:${this.maxw}`);

    this.pdbs = new bdds(this.ar * this.bits);
		this.pprog = new bdds(this.maxw * this.ar * this.bits);

    for (let i = 0; i < r.length; i++) {
			const x = r[i];
			if (x.length === 1) {
				_dbg_parser('prog_read store fact', x);
        this.db = this.pdbs.bdd_or(this.db,
                              new rule(this.pdbs, x, this.bits, this.ar).poss.h);
			} else {
				_dbg_parser('prog_read store rule', x);
				this.rules.push(new rule(this.pprog, x, this.bits, this.ar));
			}
    }

    _dbg_pfp(`prog_read pdbs:`, this.pdbs.V.map(n=>`${this.pdbs.M[n.key]}=(${n.key})`).join(', '));
    _dbg_pfp(`prog_read pprog:`, this.pprog.V.map(n=>`${this.pprog.M[n.key]}=(${n.key})`).join(', '));
    _dbg_pfp(`prog_read bits:${this.bits} ar:${this.ar} maxw:${this.maxw} db(root):${this.db}`);
    return s.s;
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
    // dpfp('db', this.db, add, del, s);
    if ((s == bdds.F) && (add != bdds.F)) {
      this.db = bdds.F;
      // dpfp('db set t', this.db);
    } else {
      this.db = dbs.bdd_or(dbs.bdd_and_not(this.db, del), s);
      // dpfp('db set f', this.db);
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
			this.step();                // do pfp step
      _dbg_pfp('/STEP');
			if (s.includes(this.db)) {  // if db root already resulted from previous step
        this.printdb();           // print db
				return d === this.db;     // return true(sat) or false(unsat)
			}
		} while (true);
	}

  // prints db (bdd -> tml facts)
	printdb(os) {
    out(os, this.pdbs, this.db, this.bits, this.ar, 1, this.dict);
    if (!os) {
      const o = { dot: true, svg: false };
      bdd_out(this.pdbs, this.dict, o);
      bdd_out(this.pprog, this.dict, o);
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
			else if (k < d.nsyms()) os += d.get(k) + ' ';
			else os += `[${k}]`;
    }
    os += `\n`;
	}
  console.log(os);
}

module.exports = {
  lp, string_read_text,
  dict, rule_items, rule, out
}