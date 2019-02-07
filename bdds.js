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

const _dbg_bdd   = require('debug')('tml:bdd');
const _dbg_node  = require('debug')('tml:bdd:node');
const _dbg_leaf  = require('debug')('tml:bdd:leaf');
const _dbg_apply = require('debug')('tml:bdd:apply');

// internal counters for every new bdd and applies
const _counters = { bdds: 0, apply: 0 };

const options = {
  recursive: false,
  memoization: false
}

const _enum = obj => Object.freeze(obj);

class node {
  // initialize node
	constructor(varid, hi, lo) {
		this.v = varid;
		this.hi = hi;
    this.lo = lo;
  }
  // clones the node object
  clone() { return new node(this.v, this.hi, this.lo); }
  // key used for "map" of nodes, or for debugging
	get key() { return `${this.v}:${this.hi}/${this.lo}`; }
}

// existential quantification, to be used with apply()
class op_exists {
  // initialize the existential operator
	constructor(s) {
    this.s = s;
    this._dbg = 'exists';
  }
  // operator evaluation, b = bdd, x = node's index
	eval(b, x) {
    const n = b.getnode(x);
    if ((n.v > 0) && (n.v <= this.s.length) && this.s[n.v-1]) {
      return b.getnode(b.bdd_or(n.hi, n.lo));
    }
    return n;
	}
}
// operator class wrapping evaluation function and helper _dbg string 
class op { constructor(_eval, _dbg) { this.eval = _eval; this._dbg = _dbg; } }
// operators, to be used with apply()
const op_and      = new op((x, y) => (x &&  y) ? bdds_base.T : bdds_base.F, '&&');
const op_and_not  = new op((x, y) => (x && !y) ? bdds_base.T : bdds_base.F, '&&!');
const op_or       = new op((x, y) => (x ||  y) ? bdds_base.T : bdds_base.F, '||');

// bdds base class
class bdds_base {
  // F=0 and T=1 consants
	static get F() { return 0; }
  static get T() { return 1; }
  // initialize bdds
	constructor(nvars) {
    this.id = ++_counters.bdds;
		this.V = [];          // all nodes
		this.M = {};          // node to its index
		this.dim = 1;         // used for implicit power
		this.nvars = nvars;   // number of vars
		this.root = 0n;       // root of bdd
    this.maxbdd = 0n;     // used for implicit power
    // initialize bdd with 0 and 1 terminals
		this.add_nocheck(new node(0, 0, 0));
		this.add_nocheck(new node(0, 1, 1));
  }
  
  // checks if node is terminal (leaf)
	static leaf(n) {
		const res = n instanceof node
			?	n.v === 0
			: n === bdds_base.T || n === bdds_base.F;
		_dbg_leaf(`${res ? ' is' : 'not'} leaf ${n instanceof node ? n.key : n}`);
		return res;
  }

  // checks if node is terminal and is T
	static trueleaf(n) {
		const res = n instanceof node
			? bdds_base.leaf(n) && (n.hi > 0)
			: n === bdds_base.T;
		_dbg_leaf(`    leaf ${n instanceof node ? n.key : n} is ${res}`);
		return res;
  }

  // set virtual power
	setpow(root, dim, maxw) {
    this.root = root; this.dim = dim; this.maxbdd = 1n<<BigInt(64/maxw);
    _dbg_bdd(`setpow to root:${this.root}, dim:${this.dim}, maxw: ${maxw}, maxbdd:${this.maxbdd}`);
  }

  // add node directly without checking
	add_nocheck(n) {
		const r = this.V.length;
		this.M[n.key] = r;
		this.V.push(n);
		return r;
  }
  
  // adds new node
	add(n) {
    let r = null;
    let _dbg = '';
    do {
      if (!(n.v <= this.nvars)) {
        _dbg_node(`add ${n.key} = ERR`);
        throw Error('Node id too big.');
      }
      if (n.hi === n.lo)  {
        r = n.hi;
        break;
      }
      if (this.M.hasOwnProperty(n.key)) {
        r = this.M[n.key];
        break;
      }
      r = this.add_nocheck(n);
      _dbg = ' nocheck'
    } while (0);
    _dbg_node(`add ${r} (${n.key})${_dbg}`);
		return r;
  }
  
  // returns node by its index
	getnode(nid) {
		if (this.dim === 1) return this.V[nid];
		const m = Number(BigInt(nid) % this.maxbdd);
		const di = BigInt(nid) / this.maxbdd;
		const dn = Number(di);
    const n = this.V[m];
    if (n.v > 0) n.v += this.nvars * dn;
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
		return n;
  }
  
  // outputs
	out(os, n) {
		if (!(n instanceof node))
			return this.out(`${os}[${n}]`, this.getnode(n)); // colors?
		if (bdds_base.leaf(n)) return os + bdds_base.trueleaf(n) ? 'T' : 'F';
		os = this.out(`${os}${n.v}?`, n.hi);
		return this.out(`${os}:${n.lo}`)
  }
  // returns bdd's length = number of nodes
	get length() { return this.V.length; }
}

class bdds extends bdds_base {
	constructor(nvars) {
    super(nvars);
    if (options.memoization) this.memos_clear();
  }
  
	sat(v, nvars, n, p, r) {
		//d(`sat: ${v}, ${nvars}, ${n.key}`, 'p', p, 'r', r);
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
		//dbd('allsat:', x, nvars);
		const p = Array(nvars).fill(false); const r = [];
    this.sat(1, nvars, this.getnode(x), p, r)
    //dbd('allsat r:', r);
		return r;
  }
  
	from_bit(x, v) {
		//dbd('from_bit: ', x, v);
		//v = v > 0;
		const n = v ? new node(x+1, bdds_base.T, bdds_base.F) : new node(x+1, bdds_base.F, bdds_base.T);
		const res = this.add(n);
		//dbd('added from_bit: ', res, n.key);
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
    //dbd('copy x', x);
		if (bdds.leaf(x)) return x;
    let t;
    if (options.memoization) {
      t = b.id+'.'+x;
      //dbd('copy memo index', t);
      if (this.memo_copy.hasOwnProperty(t)) {
        //dbd('copy memo found', this.memo_copy[t]);
        return this.memo_copy[t];
      }  
    }
		const n = b.getnode(x);
    //dbd('copy node', n.key);
    const res = this.add(new node(n.v,
      this.copy(b, n.hi),
      this.copy(b, n.lo)));
    //dbd('copy added', res.key);
    if (options.memoization) this.memo_copy[t] = res;
		return res;
  }
  
  static apply(src, x, dst, y, op) {
    ++_counters.apply;
    const apply_id = _counters.apply;
    if (op === undefined) {
      op = y;
      const r = this.apply_unary_recursive(src, x, dst, op);
      _dbg_apply(`apply(${apply_id}) ${r} ${op._dbg}(${x})${src===dst?' on this':''} (unary)`);
      return r
    }
    const Vx = src.getnode(x).clone();
    const Vy = dst.getnode(y).clone();
    let v;
    if (((Vx.v === 0) && (Vy.v > 0)) || ((Vy.v > 0) && (Vx.v > Vy.v))) {
      v = Vy.v;
      Vx.hi = x;
      Vx.lo = x;
    } else if (Vx.v === 0) {
      const r = op.eval(Vx.hi, Vy.hi);
      _dbg_apply(`apply(${apply_id}) ${r} (${x}${op._dbg}${y})${src===dst?' on this':''}`);
      return op.eval(Vx.hi, Vy.hi);
    } else {
      v = Vx.v
      if ((v < Vy.v) || (Vy.v === 0)) {
        Vy.hi = y;
        Vy.lo = y;
      }
    }
    const r = dst.add(new node(v,
      this.apply(src, Vx.hi, dst, Vy.hi, op),
      this.apply(src, Vx.lo, dst, Vy.lo, op)));
    _dbg_apply(`apply(${apply_id}) ${r} (${x}${op._dbg}${y})${src===dst?' on this':''}`);
    return r;
  }

	static apply_and    (src, x, dst, y) { return bdds.apply(src, x, dst, y, op_and); }
	static apply_and_not(src, x, dst, y) { return bdds.apply(src, x, dst, y, op_and_not); }
	static apply_or     (src, x, dst, y) { return bdds.apply(src, x, dst, y, op_or); }
  
	static apply_and_ex_perm(src, x, dst, y, s, p, sz) {
		// da('apply_and_ex_perm x', x, 'y', y, s.slice(0,6));
    let t;
    if (options.memoization) {
      t = `${dst.id}.${x}.${y}.${s.join(',')}`;
      if (src.memo_and_ex.hasOwnProperty(t)) { 
        //dpfp('memo_and_ex found', src.memo_and_ex[t]);
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
          ? bdds.apply(dst, y, dst, new op_exists(s))
          : bdds_base.F;
        break;
      }
      const Vy = dst.getnode(y).clone();
      if (bdds.leaf(Vy)) {
        // dpfp('leaf Vy true');
        r = bdds.trueleaf(Vy)
          ? (src === dst
            ? bdds.apply(dst, x, dst, new op_exists(s))
            : bdds.apply(dst, dst.copy(src, x), dst, new op_exists(s)))
          : bdds_base.F;
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
		if (options.memoization) src.memo_and_ex[t] = r;
		return r;
  }
  
  static apply_unary_recursive(b, x, r, op) {
    const n = op.eval(b, x);
    return r.add(new node(n.v,
      bdds.leaf(n.hi) ? n.hi : bdds.apply(b, n.hi, r, op),
			bdds.leaf(n.lo) ? n.lo : bdds.apply(b, n.lo, r, op)));
  }

	static apply_unary_non_recursive(b, x, r, op) {
    const get = id => op.eval(b, id);     // evaluates the operator
    const parents = [];                   // path from root to the current node
    const s = _enum({ "LO": 1, "HI": 2, "OP": 3 }); // traversing states
    let ts = s.LO;                        // current traversing state
    let n = get(x);                       // current node
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
		//dbd('permute x', x, 'm', m[1], 'sz', sz);
    // const t = make_pair(x, m);
    let t;
    if (options.memoization) {
      t = `${x}.${m.join(',')}`;
      if (this.memo_permute.hasOwnProperty(t))
         return this.memo_permute[t];  
    }
		//dbd(this);
		const n = this.getnode(x);
		//dbd('n', n);
		const res = bdds.leaf(n) ? x : this.ite(
																			n.v <= sz ? m[n.v-1] : (n.v-1),
																			this.permute(n.hi, m, sz),
                                      this.permute(n.lo, m, sz));
    //dbd('permute res', res);
		if (options.memoization) this.memo_permute[t] = res;
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
		//dbd('from_bits x', x, 'bits', bits, 'ar', ar, 'w', w, 's', s);

    for (let k = 0; k < r.length; k++) {
      r[k] = Array(w * ar).fill(0);
    }

    let n = 0;
		for (let z = 0; z < s.length; z++) {
			for (let j = 0; j != w; ++j)
				for (let i = 0; i != ar; ++i)
					for (let b = 0; b != bits; ++b) {
            //dbd("nzjib:", n, z, j, i, b, 's[z]', s[z]);
            //dbd('BITS(j, i)', ((j*bits+b)*ar+i));
            if (s[z][((j*bits+b)*ar+i)] > 0)
							r[n][j * ar + i] |= (1 << b);
          }
			++n;
    }
    //dbd('r', r, 'n', n);
		return r;
	}
	bdd_or(x, y) { return this.constructor.apply_or(this, x, this, y); }
	bdd_and(x, y) { return this.constructor.apply_and(this, x, this, y); }
	bdd_and_not(x, y) { return this.constructor.apply_and_not(this, x, this, y); }
	memos_clear() {
    if (!options.memoization) return;
		this.memo_and = {};
		this.memo_and_not = {};
		this.memo_or = {};
		this.memo_and_ex = {};
		this.memo_copy = {};
		this.memo_permute = {};
	}
}

module.exports = {
  bdds, options,
  node, bdds_base, op, op_exists, op_and, op_and_not, op_or
}