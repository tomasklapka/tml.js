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

// OPTIONS:
const options = {
  memoization: true,
  recursive: false
}
let bdds = null; // bdds class (to be loaded when required)
// debug functions
const _dbg_bdd   = require('debug')('tml:bdd');
const _dbg_node  = require('debug')('tml:bdd:node');
const _dbg_leaf  = require('debug')('tml:bdd:leaf');
const _dbg_apply = require('debug')('tml:bdd:apply');
// internal counters for every bdds, apply calls and ops.
const _counters = { bdds: 0, apply: 0, op: 0 };

// node in a bdd tree
class node {
  // initialize node
	constructor(varid, hi, lo) {
    this.v  = BigInt(varid);
    this.hi = BigInt(hi);
    this.lo = BigInt(lo);
  }
  // clones the node object
  clone() { return new node(this.v, this.hi, this.lo); }
  // key used for "map" of nodes, or for debugging
	get key() { return `${this.v}:${this.hi}/${this.lo}`; }
}

// op class wrapping evaluation function and helper _dbg string
class op {
  constructor(_eval, _dbg) {
    this.eval = _eval;
    this._dbg = _dbg;
    this._id = ++_counters.op;
  }
}
// operators, to be used with apply()
const op_and      = new op((x, y) => (x &&  y) ? bdds_base.T : bdds_base.F, '&&');
const op_and_not  = new op((x, y) => (x && !y) ? bdds_base.T : bdds_base.F, '&&!');
const op_or       = new op((x, y) => (x ||  y) ? bdds_base.T : bdds_base.F, '||');
// existential quantification (initialize with s = existentials)
const op_exists   = s => new op((b, x) => {
  // operator evaluation, b = bdd, x = node's index
  const n = b.getnode(x);
  if ((n.v > 0n) && (n.v <= BigInt(s.length)) && s[n.v-1n]) {
    return b.getnode(b.bdd_or(n.hi, n.lo));
  }
  return n;
}, 'exists?');

// bdds base class
class bdds_base {
  // F=0 and T=1 consants
  static get F() { return 0n; }
  static get T() { return 1n; }
  // initialize bdds
  constructor(nvars) {
    this._id = ++_counters.bdds;
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
      ? n.v === 0n
      : n == bdds_base.T || n == bdds_base.F;
		_dbg_leaf(`${res ? ' is' : 'not'} leaf ${n instanceof node ? n.key : n}`);
		return res;
  }
  // checks if node is terminal and is T
	static trueleaf(n) {
		const res = n instanceof node
			? bdds_base.leaf(n) && (n.hi > 0n)
			: n === bdds_base.T;
		_dbg_leaf(`    leaf ${n instanceof node ? n.key : n} is ${res}`);
		return res;
  }
  // set virtual power
	setpow(root, dim, maxw) {
    this.root = root; this.dim = dim; this.maxbdd = 1n<<BigInt(Math.floor(64/maxw));
    _dbg_bdd(`setpow to root:${this.root}, dim:${this.dim}, maxw:${maxw}, maxbdd:${this.maxbdd}`);
    return this.root;
  }
  // add node directly without checking
	add_nocheck(n) {
		const r = BigInt(this.V.length);
		this.M[n.key] = r;
		this.V.push(n);
		return r;
  }
  // adds new node
	add(n) {
    let r = null;
    let _dbg = '';
    do {
      if (n.v > this.nvars) {
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
    // dim > 1 ...
		const m = Number(BigInt(nid) % this.maxbdd);
		const di = BigInt(nid) / this.maxbdd;
		const dn = Number(di);
    const n = this.V[m].clone(); // this damn clone!!!
    if (n.v > 0) n.v += BigInt(this.nvars) * di;
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
      _dbg_apply( `getnode(${nid}) = ${n.key} di:${di} dn:${dn} ` +
                  `this.V[m=${m}]: `, this.V[m].key);// +
                  // `        ` +
                  // `this.maxbdd:${this.maxbdd} this.nvars:`, this.nvars);
      return n;
  }
  // returns bdd's length = number of nodes
	get length() { return this.V.length; }
}

// bdds class with recursive algos
class bdds_rec extends bdds_base {
	constructor(nvars) {
    super(nvars);
    if (options.memoization) this.memos_clear();
  }
  
	sat(v, nvars, n, p, r) {
		if (bdds.leaf(n) && !bdds.trueleaf(n)) return;
		if (v > nvars+1) throw new Error(`(v = ${v}) > (nvars+1 = ${nvars+1})`);
		if (v < n.v) {
      p[v-1] = true;
			this.sat(v+1, nvars, n, p, r);
			p[v-1] = false;
			this.sat(v+1, nvars, n, p, r);
    } else {
      if (v === nvars+1) {
        r.push(p.slice());
      }	else {
        p[v-1] = true;
        this.sat(v+1, nvars, this.getnode(n.hi), p, r);
        p[v-1] = false;
        this.sat(v+1, nvars, this.getnode(n.lo), p, r);
      }
    }
  }
  
	allsat(x, nvars) {
		const p = Array(nvars).fill(false); const r = [];
    this.sat(1, nvars, this.getnode(x), p, r)
		return r;
  }
  
	from_bit(x, v) {
    const n = v > 0
      ? new node(x+1, bdds_base.T, bdds_base.F)
      : new node(x+1, bdds_base.F, bdds_base.T);
    const res = this.add(n);
    _dbg_bdd(`                    from_bit x:${x}, v:${v}, n:${n.key}, res:${res}`);
		return res;
  }
  // if-then-else operator
	ite(v, t, e) {
		const x = this.getnode(t); const y = this.getnode(e);
		if ((bdds.leaf(x)||v<x.v) && (bdds.leaf(y)||v<y.v)) return this.add(new node(v+1, t, e));
		return this.bdd_or(
				this.bdd_and(this.from_bit(v, true), t),
				this.bdd_and(this.from_bit(v, false), e));
  }
  
	copy(b, x) {
		if (bdds.leaf(x)) return x;
    let t;
    if (options.memoization) {
      t = b._id+'.'+x;
      if (this.memo_copy.hasOwnProperty(t)) {
        return this.memo_copy[t];
      }  
    }
		const n = b.getnode(x);
    const res = this.add(new node(n.v,
      this.copy(b, n.hi),
      this.copy(b, n.lo)));
    if (options.memoization) this.memo_copy[t] = res;
		return res;
  }
  
  static apply(src, x, dst, y, op) {
    const apply_id = ++_counters.apply;
    // unary op
    if (op === undefined) {
      op = y; // take op from the third argument
      const r = bdds.apply_unary(src, x, dst, op);
      _dbg_apply(`unary apply(${apply_id}) ${r} ${op._dbg}(${x})${src===dst?' on this':''} (unary)`);
      return r;
    }
    // binary op
    let t;
    if (options.memoization) {
      t = `${op._id}.${dst._id}.${x}.${y}`;
      if (src.memo_op.hasOwnProperty(t)) {
        _dbg_apply(`apply(${apply_id}) ${src.memo_op[t]} (${x} ${op._dbg} ${y})${src===dst?' on this':''} (memo:${t})`);
        return src.memo_op[t];
      }
    }
    const Vx = src.getnode(x).clone();
    const Vy = dst.getnode(y).clone();
    let v;
    if ((bdds.leaf(Vx) && !bdds.leaf(Vy))
    || (!bdds.leaf(Vy) && (Vx.v > Vy.v))) {
      v = Vy.v;
      Vx.hi = x; Vx.lo = x;
    } else {
      if (bdds.leaf(Vx)) {
        const r = op.eval(Vx.hi, Vy.hi);
        _dbg_apply(`apply(${apply_id}) ${r} (${x} ${op._dbg} ${y})${src===dst?' on this':''} (Vx is leaf)`);
        return r;
      } else {
        v = Vx.v;
        if ((v < Vy.v) || bdds.leaf(Vy)) {
          Vy.hi = y; Vy.lo = y;
        }
      }
    }
    const r = dst.add(new node(v,
      bdds.apply(src, Vx.hi, dst, Vy.hi, op),
      bdds.apply(src, Vx.lo, dst, Vy.lo, op)));
    _dbg_apply(`apply(${apply_id}) ${r} (${x} ${op._dbg} ${y})${src===dst?' on this':''} (recursive)`);
    if (options.memoization) src.memo_op[t] = r;
    return r;
  }

	static apply_ex     (src, x, dst, s) { return bdds.apply(src, x, dst, op_exists(s)); }
	static apply_and    (src, x, dst, y) { return bdds.apply(src, x, dst, y, op_and); }
	static apply_and_not(src, x, dst, y) { return bdds.apply(src, x, dst, y, op_and_not); }
	static apply_or     (src, x, dst, y) { return bdds.apply(src, x, dst, y, op_or); }
  static apply_and_ex (src, x, dst, y, s, p, sz) {
    const apply_id = ++_counters.apply;
    _dbg_apply(`apply_and_ex(${apply_id}) (${x}, ${y})${src===dst?' on this':''}`);
    let t;
    if (options.memoization) {
      t = `${dst._id}.${s.join(',')}.${x}.${y}`;
      if (src.memo_and_ex.hasOwnProperty(t)) {
        _dbg_apply(`    ret from apply_and_ex(${apply_id}) = ${src.memo_and_ex[t]} (${x} ${op._dbg} ${y})${src===dst?' on this':''} (memo:${t})`);
        return src.memo_and_ex[t];
      }
    }
    const Vx = src.getnode(x).clone();
    const Vy = dst.getnode(y).clone();
    let v, res;
    do {
      if (bdds.leaf(Vx)) {
        res = bdds.trueleaf(Vx)
          ? bdds.apply_ex(dst, y, dst, s)
          : bdds.F;
        break;
      }
      if (bdds.leaf(Vy)) {
        res = !bdds.trueleaf(Vy)
          ? bdds.F
          : ((src === dst)
            ? bdds.apply_ex(dst, x, dst, s)
            : bdds.apply_ex(dst, dst.copy(src, x), dst, s));
        break;
      }
      if ((bdds.leaf(Vx) && !bdds.leaf(Vy))
      || (bdds.leaf(Vy) && (Vx.v > Vy.v))) {
        v = Vy.v;
        Vx.hi = x;
        Vx.lo = x;
      } else {
        if (bdds.leaf(Vx)) {
          res = (Vx.hi && Vy.hi) ? bdds.T : bdds.F;
          break;
        } else {
          v = Vx.v;
          if (v < Vy.v || bdds.leaf(Vy)) {
            Vy.hi = y;
            Vy.lo = y;
          }
        }
      }
      if (v <= BigInt(sz) && s[v-1n]) {
        res = dst.bdd_or(
          bdds.apply_and_ex(src, Vx.hi, dst, Vy.hi, s, p, sz),
          bdds.apply_and_ex(src, Vx.lo, dst, Vy.lo, s, p, sz));
        break;
      }
      res = dst.add(new node(v,
        bdds.apply_and_ex(src, Vx.hi, dst, Vy.hi, s, p, sz),
        bdds.apply_and_ex(src, Vx.lo, dst, Vy.lo, s, p, sz)));
    } while(0);
    if (options.memoization) { src.memo_and_ex[t] = res; }
    _dbg_apply(`    ret from apply_and_ex(${apply_id}) ${res} (${x} ${y})${src===dst?' on this':''}`);
    return res;
  }

  static apply_unary(b, x, r, op) {
    const n = op.eval(b, x);
    return r.add(new node(n.v,
      bdds.leaf(n.hi) ? n.hi : bdds.apply(b, n.hi, r, op),
			bdds.leaf(n.lo) ? n.lo : bdds.apply(b, n.lo, r, op)));
  }
	// [overlapping] rename
	permute(x, m, sz) {
    let t;
    if (options.memoization) {
      t = `${x}.${m.join(',')}`;
      if (this.memo_permute.hasOwnProperty(t)) {
         return this.memo_permute[t];
      }
    }
		const n = this.getnode(x);
    const res = bdds.leaf(n)
      ? x
      : this.ite((n.v <= BigInt(sz)) ? m[n.v-1n] : (n.v-1n),
          this.permute(n.hi, m, sz),
          this.permute(n.lo, m, sz));
		if (options.memoization) this.memo_permute[t] = res;
    _dbg_bdd(`permute x:${x} (${n.key}) sz:${sz} m:[ `, m.join(', '), ` ] = ${res}`);
		return res;
	}
  // helper constructors
	from_eq(x, y) { // a bdd saying "x=y"
    const res = this.bdd_or(
      this.bdd_and(this.from_bit(y, false), this.from_bit(x, false)),
      this.bdd_and(this.from_bit(y, true),  this.from_bit(x, true)));
    _dbg_bdd(`from_eq x:${x} y:${y} = ${res}`);
    return res;
  }

	from_bits(x, bits, ar, w) {
		const s = this.allsat(x, bits * ar * w);
		const r = Array(s.length);
    for (let k = 0; k < r.length; k++) {
      r[k] = Array(w * ar).fill(0);
    }
    let n = 0;
		for (let z = 0; z < s.length; z++) {
			for (let j = 0; j != w; ++j) {
				for (let i = 0; i != ar; ++i) {
					for (let b = 0; b != bits; ++b) {
            if (s[z][((j*bits+b)*ar+i)] > 0) {
              r[n][j * ar + i] |= (1 << b);
            }
          }
        }
      }
      ++n;
    }
		return r;
  }

	bdd_or(x, y) { return bdds.apply_or(this, x, this, y); }
	bdd_and(x, y) { return bdds.apply_and(this, x, this, y); }
	bdd_and_not(x, y) { return bdds.apply_and_not(this, x, this, y); }

  memos_clear() {
    if (!options.memoization) return;
    this.memo_op = {};
    this.memo_and_ex = {};
    this.memo_copy = {};
    this.memo_permute = {};
	}
}

module.exports = (o = {}) => {
  options.memoization = o.hasOwnProperty('memoization') ? o.memoization : options.memoization;
  options.recursive = o.hasOwnProperty('recursive') ? o.recursive : options.recursive;
  // load rec or non rec version of bdds class
  bdds = options.recursive ? bdds_rec : require('./bdds_non_rec').bdds_non_rec;
  return {
    options, bdds,
    node, bdds_base, bdds_rec,
    op, op_exists, op_and, op_and_not, op_or
  }
}
