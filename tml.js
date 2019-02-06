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

const { inspect } = require('util');
const { spawn } = require('child_process');

let lpcounter = 0;
let bddscounter = 0;
let gvcounter = 0;
let stepcounter = 0;

const memoization = false;
const bdd_to_svg = false;
const bdd_to_png = false;

const d    = require('debug')('tml');
const dp   = require('debug')('tml:parser');
const dd   = require('debug')('tml:dict');
const dbd  = require('debug')('tml:bdd');
const dbdl = require('debug')('tml:bdd:leaf');
const dpfp = require('debug')('tml:pfp');
const da   = require('debug')('tml:apply');

const sep_expected = `Term or ':-' or '.' expected`;
const term_expected = 'Term expected';

const _enum = obj => Object.freeze(obj);
const skip_ws = s => { s.s = s.s.replace(/^\s+/, ''); };
const skip = (s, n = 1) => { s.s = s.s.slice(n); }
const er = x => { console.log(x); process.exit(0); }

const op_and      = (x, y) => (x && y)  ? bdds.T : bdds.F;
const op_and_not  = (x, y) => (x && !y) ? bdds.T : bdds.F;
const op_or       = (x, y) => (x || y)  ? bdds.T : bdds.F;

class dict { // represent strings as unique integers
	static get pad() { return 0; }
	constructor() {
		this.syms = [ dict.pad ];
		this.vars = [ dict.pad ];
	}
	get(s) {
    if (typeof(s) == 'number') return this.syms[s];
		if (s[0] === '?') {
      const p = this.vars.indexOf(s);
      if (p > 0) return -p;
      this.vars.push(s);
			return -(this.vars.length-1);
    }
    const p = this.syms.indexOf(s);
    if (p > 0) return p;
		this.syms.push(s);
		return this.syms.length-1;
	}
	bits() { return 32 - Math.clz32(this.syms.length); }
	nsyms() { return this.syms.length; }
}

class node {
	constructor(varid, hi, lo) {
		this.v = varid;
		this.hi = hi;
    this.lo = lo;
  }
  clone() { return new node(this.v, this.hi, this.lo); }
	get key() { return `${this.v}:${this.hi}/${this.lo}`; }
  // get hash() { return this.v + this.hi + this.lo; } // question bellow
}

class rule_items {  // negs/poss of a rule
  constructor(bits, ar) {
    this.h = bdds.T; // bdd root
    this.w = 0; // nbodies, will determine the virtual power
    this.x = []; // existentials
    this.hvars = {}; // how to permute body vars to head vars
    this.bits = bits;
    this.ar = ar;
  }
	from_arg(bdd, i, j, k, vij, bits, ar, hvars, m, npad) {
    // d('from_arg ijk', i, j, k);
    // d('from_arg vij', vij);
    // da('bits', bits);
    // da('ar', ar);
    // d('from arg hvars', hvars);
    // d('m', m);
    // da('r', this);
    // d('npad', npad);

    const BIT = (term,arg,b)=>((term*bits+b)*ar+arg);

    let notpad = bdds.T;
		if (m.hasOwnProperty(vij)) { // if seen
			for (let b = 0; b != bits; ++b) {
        k.k = bdd.bdd_and(k.k,
          bdd.from_eq(BIT(i, j, b), BIT(m[vij][0], m[vij][1], b)));
        // d('r.x[BIT(i, j, b)]1 = true', BIT(i, j, b));
        this.x[BIT(i, j, b)] = true; // existential out
      }
		} else {
			m[vij] = [i, j];
			if (vij >= 0)
				for (let b = 0; b != bits; ++b) {
          k.k = bdd.bdd_and(k.k, bdd.from_bit(BIT(i, j, b), vij&(1<<b)));
          // d('r.x[BIT(i, j, b)]2 = true', BIT(i, j, b));
					this.x[BIT(i, j, b)] = true;
				}
			else {
				for (let b = 0; b != bits; ++b) {
          notpad = bdd.bdd_and(notpad, bdd.from_bit(BIT(i, j, b), false));
        }
				npad.npad = bdd.bdd_or(npad.npad, notpad);
				if (hvars.hasOwnProperty(vij)) {
          const hvar = hvars[vij];
          // d('head var', hvar);
					for (let b = 0; b != this.bits; ++b) {
            // d('BIT(i, j, b)', BIT(i, j, b));
            // d('BIT(i, hvar)', BIT(0, hvar, b));
						if (BIT(i, j, b) != BIT(0, hvar, b)) {
              // d('r.hvars[BIT(i, j, b)] =', BIT(0, hvar, b), BIT(i, j, b));
              this.hvars[BIT(i, j, b)] = BIT(0, hvar, b);
            }
          }
        } else {
          // d('non-head var');
  				for (let b = 0; b != this.bits; ++b) {
            // d('r.x[BIT(i, j, b)]3 = true', BIT(i, j, b));
            this.x[BIT(i, j, b)] = true;
          }
        }
			}
    }
    d('/from_arg k', k);
	}
  get_heads(p, hsym) {
    let x, y, z;
    p.pdbs.setpow(p.db, this.w, p.maxw);
    if (bdds.leaf(p.db)) {
      x = bdds.trueleaf(p.db) ? this.h : bdds.F;
      y = bdds.apply(p.pprog, this.x, p.pprog, // remove nonhead variables
        new op_exists(this.x, ((this.w+1)*p.bits+1)*(p.ar+2)));
    } else {
      y = bdds.apply_and_ex_perm(p.pdbs, p.db, p.pprog, this.h, this.x,
        this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2)); // rule/db conjunction
    }
    z = p.pprog.permute(y, this.hvars, ((this.w+1)*p.bits+1)*(p.ar+2)); // reorder
    d('z', z);
    d('this.hsym', hsym);
    z = p.pprog.bdd_and(z, hsym);
    p.pdbs.setpow(p.db, 1, p.maxw);
    return z;
  }
}

class rule { // a P-DATALOG rule in bdd form
  constructor(bdd, v, bits, ar) {
		d('new rule() v', v, 'bits', bits, 'ar', ar);
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
    d(v);
    this.neg = head[0] < 0;
    head.shift();
		for (let i = 0; i != head.length; ++i) {
			if (head[i] < 0) hvars[head[i]] = i; // var
			else for (let b = 0; b != bits; ++b) {
        const BIT = (term,arg,b)=>((term*bits+b)*ar+arg);
				const res = bdd.from_bit(BIT(0, i, b), (head[i]&(1<<b)) > 0);
			  this.hsym = bdd.bdd_and(this.hsym, res);
				da('/r.hsym', this.hsym);
      }
    }
		if (v.length === 1) {
      this.poss.h = this.hsym;
      da('/from_rule1 r', this);//r.h, r.hsym, r.w, r.neg, r.sz);
      return;
    }
		const m = {};
		d('r before', this);
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
        //d('s', s);
        //d('this', this);
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
    d('/from_rule2 r', this);
  }
  get_heads(p) {
    if (this.hasnegs) {
      return p.pdbs.bdd_and(
        this.poss.get_heads(p, this.hsym),
        this.negs.get_heads(p, this.hsym));
    }
    return this.poss.get_heads(p, this.hsym);
  }
}

class bdds_base {
	static get F() { return 0; }
	static get T() { return 1; }
	static leaf(n) {
		const res = n instanceof node
			?	n.v === 0
			: n === bdds.T || n === bdds.F;
		dbdl("leaf",n,res);
		return res;
	}
	static trueleaf(n) {
		const res = n instanceof node
			? bdds_base.leaf(n) && (n.hi > 0)
			: n === bdds.T;
		dbdl("trueleaf",n.key||n,res);
		return res;
	}
	constructor(nvars) {
    this.id = ++bddscounter;
		this.V = []; // all nodes
		this.M = {}; // node to its index
		this.dim = 1; // used for implicit power
		this.nvars = nvars;
		this.root = 0n;
		this.maxbdd = 0n; // used for implicit power
		this.add_nocheck(new node(0, 0, 0));
		this.add_nocheck(new node(0, 1, 1));
	}
	setpow(root, dim, maxw) {
    this.root = root; this.dim = dim; this.maxbdd = 1n<<BigInt(64/maxw);
    dpfp("pow set to root:", this.root, "dim:", this.dim, "maxbdd:", this.maxbdd);
	}
	add_nocheck(n) {
		dbd('add_nocheck', n.key);
		const r = this.V.length;
		this.M[n.key] = r;
		this.V.push(n);
		return r;
	}
	add(n) {
    dbd('add', n.key, n);
    dbd(this.nvars);
		if (!(n.v <= this.nvars)) throw Error('Node id too big.');
		if (n.hi === n.lo) return n.hi;
		// dbd('n.key', n.key);
		// dbd('res? ', this.M[n.key]);
		return this.M.hasOwnProperty(n.key) ? this.M[n.key] : this.add_nocheck(n);
	}
	getnode(nid) {
    dbd('getnode()', nid, 'dim', this.dim);
		if (this.dim === 1) return this.V[nid];
		const m = Number(BigInt(nid) % this.maxbdd);
		const di = BigInt(nid) / this.maxbdd;
		const dn = Number(di);
    const n = this.V[m];
    dbd('getnode() n.v', n.v, 'm', m, 'di', di, 'maxbdd', this.maxbdd);
    dbd(this.nvars * dn);
    if (n.v > 0) n.v += this.nvars * dn;
    dbd('getnode() after n.v', n.v);
		if (bdds.trueleaf(n.hi)) {
      if (dn < this.dim-1)
        n.hi = BigInt(this.root)+this.maxbdd*(di+1n);
    } else if (!bdds.leaf(n.hi))
      n.hi = BigInt(n.hi) + this.maxbdd * di;
		if (bdds.trueleaf(n.lo)) {
      if (dn < this.dim-1)
        n.lo = BigInt(this.root)+this.maxbdd*(di+1n);
    } else if (!bdds.leaf(n.lo))
      n.lo = BigInt(n.lo) + this.maxbdd * di;
    dbd('getnode() returning', n.key);
		return n;
	}
	out(os, n) {
		if (!(n instanceof node))
			return this.out(`${os}[${n}]`, this.getnode(n)); // colors?
		if (bdds_base.leaf(n)) return os + bdds_base.trueleaf(n) ? 'T' : 'F';
		os = this.out(`${os}${n.v}?`, n.hi);
		return this.out(`${os}:${n.lo}`)
	}
	get length() { return this.V.length; }
}

class bdds extends bdds_base {
	constructor(nvars) {
    super(nvars);
    if (memoization) this.memos_clear();
  }
  
	sat(v, nvars, n, p, r) {
		d(`sat: ${v}, ${nvars}, ${n.key}`, 'p', p, 'r', r);
		if (bdds.leaf(n) && !bdds.trueleaf(n)) return;
		if (v > nvars+1) throw new Error('assert !(v <= nvars+1) '+v+' '+(nvars+1));
		if (v < n.v) {
      p[v-1] = true;
			this.sat(v+1, nvars, n, p, r);
			p[v-1] = false;
			this.sat(v+1, nvars, n, p, r);
    } else if (v === nvars+1) {
      r.push(p.slice());
    }	else {
			p[v-1] = true;
			this.sat(v+1, nvars, this.getnode(n.hi), p, r);
			p[v-1] = false;
			this.sat(v+1, nvars, this.getnode(n.lo), p, r);
		}
  }
  
	allsat(x, nvars) {
		dbd('allsat:', x, nvars);
		const p = Array(nvars).fill(false); const r = [];
    this.sat(1, nvars, this.getnode(x), p, r)
    //dbd('allsat r:', r);
		return r;
  }
  
	from_bit(x, v) {
		dbd('from_bit: ', x, v);
		//v = v > 0;
		const n = v ? new node(x+1, bdds.T, bdds.F) : new node(x+1, bdds.F, bdds.T);
		const res = this.add(n);
		dbd('added from_bit: ', res, n.key);
		return res;
  }
  
	ite(v, t, e) { // if-then-else operator
		const x = this.getnode(t); const y = this.getnode(e);
		if ((bdds.leaf(x)||v<x.v) && (bdds.leaf(y)||v<y.v)) return this.add(new node(v+1, t, e));
		return this.bdd_or(
				this.bdd_and(this.from_bit(v, true), t),
				this.bdd_and(this.from_bit(v, false), e));
  }
  
	copy(b, x) {
    dbd('copy x', x);
		if (bdds.leaf(x)) return x;
    let t;
    if (memoization) {
      t = b.id+'.'+x;
      dbd('copy memo index', t);
      if (this.memo_copy.hasOwnProperty(t)) {
        dbd('copy memo found', this.memo_copy[t]);
        return this.memo_copy[t];
      }  
    }
		const n = b.getnode(x);
    dbd('copy node', n.key);
    const res = this.add(new node(n.v,
      this.copy(b, n.hi),
      this.copy(b, n.lo)));
    dbd('copy added', res.key);
    if (memoization) this.memo_copy[t] = res;
		return res;
  }
  
  static apply(src, x, dst, y, op) {
    d('apply', x, y, op);
    if (op === undefined) {
      op = y;
      return this.apply_unary(src, x, dst, op);
    }
    const Vx = src.getnode(x).clone();
    const Vy = dst.getnode(y).clone();
    let v;
    if (((Vx.v === 0) && (Vy.v > 0)) || ((Vy.v > 0) && (Vx.v > Vy.v))) {
      v = Vy.v;
      Vx.hi = x;
      Vx.lo = x;
    } else if (Vx.v === 0) {
      return op(Vx.hi, Vy.hi);
    } else {
      v = Vx.v
      if ((v < Vy.v) || (Vy.v === 0)) {
        Vy.hi = y;
        Vy.lo = y;
      }
    }
    return dst.add(new node(v,
      this.apply(src, Vx.hi, dst, Vy.hi, op),
      this.apply(src, Vx.lo, dst, Vy.lo, op)));
  }

	static apply_and(src, x, dst, y) {
    return bdds.apply(src, x, dst, y, op_and);
  }
  
	static apply_and_not(src, x, dst, y) {
    return bdds.apply(src, x, dst, y, op_and_not);
  }
  
	static apply_or(src, x, dst, y) {
    return bdds.apply(src, x, dst, y, op_or);
  }
  
	static apply_and_ex_perm(src, x, dst, y, s, p, sz) {
		// da('apply_and_ex_perm x', x, 'y', y, s.slice(0,6));
    let t;
    if (memoization) {
      t = `${dst.id}.${x}.${y}.${s.join(',')}`;
      if (src.memo_and_ex.hasOwnProperty(t)) { 
        dpfp('memo_and_ex found', src.memo_and_ex[t]);
        return src.memo_and_ex[t];
      }
    }
    let r;
    do {
      // dpfp('getnode x', x, src.dim, dst.dim);
      const Vx = src.getnode(x).clone();
      // dpfp('Vx', Vx.key, 'Vy', Vy.key);
      if (bdds.leaf(Vx)) {
        // dpfp('leaf Vx true');
        r = bdds.trueleaf(Vx)
          ? bdds.apply(dst, y, dst, new op_exists(s, sz))
          : bdds.F;
        break;
      }
      const Vy = dst.getnode(y).clone();
      if (bdds.leaf(Vy)) {
        // dpfp('leaf Vy true');
        r = bdds.trueleaf(Vy)
          ? (src === dst
            ? bdds.apply(dst, x, dst, new op_exists(s, sz))
            : bdds.apply(dst, dst.copy(src, x), dst, new op_exists(s, sz)))
          : bdds.F;
        break;
      }
      // dpfp(Vx.v === 0);
      let v;
      if (Vx.v > Vy.v) {
        Vx.hi = x;
        Vx.lo = x;
        v = Vy.v;
        // dpfp(Vx.hi, Vx.lo, x, v, Vy.v);
      } else {
        v = Vx.v;
        if ((v < Vy.v)) {
          Vy.hi = y;
          Vy.lo = y;
        }
      }
      // dpfp("v:",v);
      if ((v <= sz) && s[v-1]) {
        // dpfp("bdd_or apply_and_ex_perm", Vx.hi, Vy.hi, Vx.lo, Vy.lo, sz);
        r = dst.bdd_or(
          bdds.apply_and_ex_perm(src, Vx.hi, dst, Vy.hi, s, p, sz),
          bdds.apply_and_ex_perm(src, Vx.lo, dst, Vy.lo, s, p, sz));
        break;
      }
      // dpfp("add", Vx.hi, Vy.hi, sz);
      r = dst.add(new node(v,
        bdds.apply_and_ex_perm(src, Vx.hi, dst, Vy.hi, s, p, sz),
        bdds.apply_and_ex_perm(src, Vx.lo, dst, Vy.lo, s, p, sz)));
    } while (0);
		if (memoization) src.memo_and_ex[t] = r;
		return r;
  }
  
	static apply_unary(b, x, r, op) {
    const get = id => op.op(b, b.getnode(id)); // evaluates the operator
    const parents = [];                   // path from root to the current node
    const s = _enum({ "LO": 1, "HI": 2, "OP": 3 }); // traversing states
    let ts = s.LO;                        // current traversing state
    let n = get(x);                    // current node
    let nn = 0;                           // new node
    let high = 0;                         // last high leaf
    let low = 0;                          // last low leaf
    do {                                  // traversing the binary tree
      if (ts === s.LO) {                  // search low
        // da('apply LO n', n.key, n.lo);
        if(bdds.leaf(n.lo)) {
          // da('apply LO leaf', n.key, 'go HI');
          low = n.lo;                     // remember last low leaf
          ts = s.HI;                      // leaf, go search high
        } else {                          // not a leaf
          // da('apply LO not leaf', n.key, 'go LO id:', n.lo);
          parents.push(n);                // store parent
          n = get(n.lo);                  // go low (and search low)
        }
      } else if (ts === s.HI) {           // search high
        // da('apply HI n', n.key, n.hi);
        if (bdds.leaf(n.hi)) {
          // da('apply HI leaf', n.key);
          high = n.hi;                    // remember last high leaf
          ts = s.OP;                      // leaf, do op
        } else {                          // not a leaf
          // da('apply HI not leaf', n.key, 'go HI id:', n.hi);
          parents.push(n);                // store parent
          n = get(n.hi);                  // go high
          ts = s.LO;                      // and search low
        }
      } else if (ts === s.OP) {           // do op and go UP
        // da('apply OP', n.key, 'high:', high, 'low:', low);
        nn = r.add(new node(n.v, high, low));
        // da('applied child', nn, n.lo, n.key, x, parents);
        if (parents.length === 0) break;  // we are back at the top -> break inf. loop
        n = parents.pop();                // go up
        if (nn === n.lo) {                // if we operated on low
          low = nn; ts = s.HI;            // set new low and go high
        } else {                          // else we operated on high already
          high = nn; ts = s.OP;           // set new high and go op
        }
      }
    } while (true);
    // da('apply returning', nn, 'n:', n.key, 'nn:', nn);
    return nn; // return the last new node
	}
	// [overlapping] rename
	permute(x, m, sz) {
		dbd('permute x', x, 'm', m[1], 'sz', sz);
    // const t = make_pair(x, m);
    let t;
    if (memoization) {
      t = `${x}.${m.join(',')}`;
      if (this.memo_permute.hasOwnProperty(t))
         return this.memo_permute[t];  
    }
		//dbd(this);
		const n = this.getnode(x);
		dbd('n', n);
		const res = bdds.leaf(n) ? x : this.ite(
																			n.v <= sz ? m[n.v-1] : (n.v-1),
																			this.permute(n.hi, m, sz),
                                      this.permute(n.lo, m, sz));
    dbd('permute res', res);
		if (memoization) this.memo_permute[t] = res;
		return res;
	}
  // helper constructors
	from_eq(x, y) { // a bdd saying "x=y"
		return this.bdd_or(
			this.bdd_and(this.from_bit(x, true), this.from_bit(y, true)),
			this.bdd_and(this.from_bit(x, false), this.from_bit(y, false)));
	}
	from_bits(x, bits, ar, w) {
		const s = this.allsat(x, bits * ar * w);
		const r = Array(s.length);
		dbd('from_bits x', x, 'bits', bits, 'ar', ar, 'w', w, 's', s);

    for (let k = 0; k < r.length; k++) {
      r[k] = Array(w * ar).fill(0);
    }

    let n = 0;
		for (let z = 0; z < s.length; z++) {
			for (let j = 0; j != w; ++j)
				for (let i = 0; i != ar; ++i)
					for (let b = 0; b != bits; ++b) {
            dbd("nzjib:", n, z, j, i, b, 's[z]', s[z]);
            dbd('BITS(j, i)', ((j*bits+b)*ar+i));
            if (s[z][((j*bits+b)*ar+i)] > 0)
							r[n][j * ar + i] |= (1 << b);
          }
			++n;
    }
    dbd('r', r, 'n', n);
		return r;
	}
	bdd_or(x, y) { return this.constructor.apply_or(this, x, this, y); }
	bdd_and(x, y) { return this.constructor.apply_and(this, x, this, y); }
	bdd_and_not(x, y) { return this.constructor.apply_and_not(this, x, this, y); }
	memos_clear() {
		this.memo_and = {};
		this.memo_and_not = {};
		this.memo_or = {};
		this.memo_and_ex = {};
		this.memo_copy = {};
		this.memo_permute = {};
	}
}

class op_exists { // existential quantification, to be used with apply()
	constructor(s) {
    da("op_exists()", s, s.length);
		this.s = s;
	}
	op(b, n) {
    da("op_exists", n.key, this.s.length);
    if ((n.v > 0) && (n.v <= this.s.length) && this.s[n.v-1]) {
      const nn = b.bdd_or(n.hi, n.lo);
      da('op_exists nn', nn, 'n.hi', n.hi, 'n.lo', n.lo);
      return b.getnode(nn);
    }
    da('op_exists n', n.key)
    return n;
	}
}

class lp { // [pfp] logic program
  constructor() {
    this.id = ++lpcounter;
		this.dict = new dict(); // holds its own dict so we can determine the universe size
    this.pdbs = null;  // db bdd (as db has virtual power)
    this.pprog = null; // prog bdd
		this.db = bdds_base.F; // db's bdd root
    this.rules = [];
    this.ar = 0;
    this.maxw = 0;
    this.bits = 0;
	}

	str_read(s) { // parse a string and returns its dict id
		dp('str_read', s.s.slice(0, s.s.indexOf(`\n`)));
		let r = null;
		s.s = s.s.replace(/^\s*(\??[\w|\d]+)\s*/, (_, t) => {
			dp('str_read match:', t);
			r = this.dict.get(t);//, t.length);
			return ''; // remove match from input
		})
		if (!r) throw new Error('Identifier expected');
		dp('str_read r=', r);
		return r;
	}

	term_read(s) { // read raw term (no bdd)
		dp('term_read', s.s.slice(0, s.s.indexOf(`\n`)));
		let r = [];
		skip_ws(s);
    if (s.s.length === 0) return r;
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
          if (r.length === 1) throw new Error('Term expected');
          skip(s, ++i); return r;
        }
				if (c === '.' || c === ':') {
          if (r.length === 1) throw new Error('Term expected');
          skip(s, i); return r;
        }
				r.push(this.str_read(s)); i = 0;
			}
		} while (i < s.s.length);
		throw new Error('\',\', \',\' or \':-\' expected');
	}

	rule_read(s) { // read raw rule (no bdd)
		dp('rule_read', s.s.slice(0, s.s.indexOf(`\n`)));
		let t, r = [];
		if ((t = this.term_read(s)).length === 0) return r;
		r.push(t);
		skip_ws(s);
		if (s.s[0] === '.') { skip(s); dp('rule read fact',r); return r; } // fact
		if (s.s.length < 2 || (s.s[0] !== ':' && s.s[1] !== '-')) throw new Error (sep_expected);
		skip(s, 2);
		do {
			if ((t = this.term_read(s)).length === 0) er(term_expected);
			r.splice(r.length-1, 0, t); // make sure head is last
			skip_ws(s);
			if (s.s[0] === '.') { skip(s); dp('rule read rule',r); return r; }
			if (s.s[0] === ':') throw new Error('\',\' expected');
		} while (true);
	}

	prog_read(s) {
		dp('prog_read', s.s.slice(0, s.s.indexOf(`\n`)));
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
		d('prog_read', r);
		for (let i = 0; i < r.length; i++) {
			for (let j = 0; j < r[i].length; j++) {
				if ((l = r[i][j].length) < this.ar+1) {
					r[i][j] = r[i][j]
						.concat(Array(this.ar + 1 - l).fill(this.dict.pad));
				}
			}
    }
    dd('dict after prog read', this.dict);
		this.bits = this.dict.bits();
		d('stats: ', this.bits, this.ar, this.maxw);
		this.pdbs = new bdds(this.ar * this.bits);
		this.pprog = new bdds(this.maxw * this.ar * this.bits);
		for (let i = 0; i < r.length; i++) {
			const x = r[i];
			if (x.length === 1) {
				dbd('store fact', x);
				// dbd(this);
        this.db = this.pdbs.bdd_or(this.db,
                              new rule(this.pdbs, x, this.bits, this.ar).poss.h);
				// dbd(this);
				// dbd(this.pdbs);
			} else {
				dp('store rule', x);
				this.rules.push(new rule(this.pprog, x, this.bits, this.ar));
			  dbd(this);
			}
		}
	}

	step() { // single pfp step
    dpfp('step');
    console.log('____________________STEP__________________________');
		console.log();
    ++stepcounter;
		let add = bdds.F;	let del = bdds.F;
		let s;
		const dbs = this.pdbs;
    const prog = this.pprog;
		for (let i = 0; i < this.rules.length; i++) {
      const r = this.rules[i];
			const t = bdds.apply_or(this.pprog, r.get_heads(this), this.pdbs, r.neg ? del : add);
			if (r.neg) { del = t; } else { add = t; }
    }
    s = dbs.bdd_and_not(add, del);
    dpfp('db', this.db, add, del, s);
    if ((s == bdds.F) && (add != bdds.F)) {
      this.db = bdds.F;
      dpfp('db set t', this.db);
    } else {
      this.db = dbs.bdd_or(dbs.bdd_and_not(this.db, del), s);
      dpfp('db set f', this.db);
    }
    if (memoization) {
      dbs.memos_clear();
      prog.memos_clear();  
    }
    dpfp('/step');
	}

	pfp() {
    dpfp('pfp');
		let d;
		let t = 0;
		const s = [];
		do {
			d = this.db;
			s.push(d);
			this.printdb(`step: ${++t} nodes: ${this.pdbs.length} + ${this.pprog.length}\n`)
			this.step();
			if (s.includes(this.db)) {
        this.printdb('');
        dpfp('/pfp');
				return d == this.db;
			}
		} while (true);
	}

	printdb(os) {
    out(os, this.pdbs, this.db, this.bits, this.ar, 1, this.dict);
    if (os != '') dbd(bdd_out(this.pprog, this.pprog.length-1, this.dict));
	}
}

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

function bdd_out(b, db, dict) {
  const dot = bdd_to_dot(b, db, dict);
  // dbd(dot);
  if (bdd_to_svg) graphviz(dot, 'svg');
  if (bdd_to_png) graphviz(dot, 'png');
  return;
  dbd(b.M);
  const nodes = b.V;
  let os = '';//'bdd out: ';
  function subtree(b, n) {
    dbd('subtree of ', n);
    return {
      n: n,
      varid: nodes[n].v,
      sym: dict.get(nodes[n].v) || '*',
      hi: nodes[n].hi > 1 ? subtree(b, nodes[n].hi) : nodes[n].hi,
      lo: nodes[n].lo > 1 ? subtree(b, nodes[n].lo) : nodes[n].lo  
    }
  }
  //let tree = {};
  //tree['root'] = subtree(b, db);
  //dbd(inspect(tree, undefined, null, true));
  return os;
}

function graphviz(dot, format = 'svg') {
  return new Promise((resolve, reject) => {
    const gv = spawn('dot', [ '-T'+format, `-obdd_${++gvcounter}.${format}` ]);
    gv.on('error', (err) => {
      console.log('error: ', err);
      reject(err);
    });
    gv.on('close', (code) => {
      if (code == 0) {
        resolve(true);
      } else {
        reject(`graphviz error:${code}`)
      }
    });
    gv.stdin.write(dot);
    gv.stdin.end();
  });
}

function bdd_to_dot(b, db, dict) {
  // const m = b.M;
  dbd(b.M);
  const nodes = b.V;
  dbd(nodes);
  let data = '';

  let parts = ['graph', 'bdd'+stepcounter, '{'];
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    parts.push('n' + i);
    if (n.v === 0 && n.hi === 0) {
      parts.push('[label=0,shape=box];');
    } else if (n.v === 0 && n.hi === 1) {
      parts.push('[label=1,shape=box];');
    } else {
      parts.push(`[label="${i} ${dict.get(n.v)||'*'} ${n.key}",shape=circle];`)
    }
  }
  for (let i = 0; i < nodes.length; i++) {
    const n = nodes[i];
    if (n.v > 0) {
      parts.push('n' + i);
      parts.push('--');
      parts.push('n' + n.lo);
      parts.push('[label="F",style=dashed];');
      parts.push('n' + i);
      parts.push('--');
      parts.push('n' + n.hi);
      parts.push('[label="T"];');
    }
  }
  parts.push('}');
  return parts.join(" ");
}

function out(os, b, db, bits, ar, w, d) {
  dbd('out os', os, 'db', db, 'bits', bits, 'ar', ar, 'w', w, 'd', d, '/out');
  if (os != '') dbd(bdd_out(b, db, d));
	const t = b.from_bits(db, bits, ar, w)
	for (let i = 0; i < t.length; i++) {
		const v = t[i];
		for (let j = 0; j < v.length; j++) {
			const k = v[j];
			if (!k) os += '* ';
			else if (k<d.nsyms()) os += d.get(k) + ' ';
			else os += `[${k}]`;
    }
    os += `\n`;
	}
	console.log(os);
}

module.exports = {
  dict, node, lp, bdds_base, bdds, rule, rule_items,
  op_exists, string_read_text, memoization
}