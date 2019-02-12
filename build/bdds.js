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

// DEFAULT OPTIONS
const options = {
	memoization: true,
	recursive: false
}
let bdds = null; // bdds class (to be loaded when required)
// debug functions
// internal counters for every bdds, apply calls and ops.
const _counters = { bdds: 0, apply: 0, apply_and_ex: 0, op: 0 };

// node in a bdd tree
class node {
	// initialize node
	constructor(varid, hi, lo) {
		this.v  = varid;
		this.hi = hi;
		this.lo = lo;
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
const op_and      = new op((x, y) =>
	((x || x>0) && ( y || y>0))   ? bdds_base.T : bdds_base.F, '&&');
const op_and_not  = new op((x, y) =>
	((x || x>0) && (!y || y===0)) ? bdds_base.T : bdds_base.F, '&&!');
const op_or       = new op((x, y) =>
	((x || x>0) || ( y || y>0))   ? bdds_base.T : bdds_base.F, '||');
// existential quantification (initialize with s = existentials)
const op_exists   = s => new op((b, x) => {
	// operator evaluation, b = bdd, x = node's index
	const n = b.getnode(x);
	if ((n.v > 0) && (n.v <= s.length) && s[n.v-1]) {
		return b.getnode(b.bdd_or(n.hi, n.lo));
	}
	return n;
}, 'exists?');

// bdds base class
class bdds_base {
	// F=0 and T=1 consants
	static get F() { return 0; }
	static get T() { return 1; }
	// initialize bdds
	constructor(nvars) {
		this._id = ++_counters.bdds;
		this.V = [];          // all nodes
		this.M = {};          // node to its index
		this.dim = 1;         // used for implicit power
		this.nvars = nvars;   // number of vars
		this.root = 0;        // root of bdd
		this.maxbdd = 0;      // used for implicit power
		// initialize bdd with 0 and 1 terminals
		this.add_nocheck(new node(0, 0, 0));
		this.add_nocheck(new node(0, 1, 1));
	}
	// checks if node is terminal (leaf)
	static leaf(n) {
		const res = n instanceof node
			? n.v === 0
			: n === bdds_base.T || n === bdds_base.F;
		return res;
	}
	// checks if node is terminal and is T
	static trueleaf(n) {
		const res = n instanceof node
			? bdds_base.leaf(n) && (n.hi > 0)
			: n === bdds_base.T;
		return res;
	}
	// set virtual power
	setpow(root, dim, maxw) {
		this.root = root;
		this.dim = dim;
		this.maxbdd = 1<<(Math.floor(32/maxw));
		return this.root;
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
			if (n.v > this.nvars) {
				throw Error('Node id too big.');
			}
			if (n.hi === n.lo) {
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
		return r;
	}
	// returns node by its index
	getnode(nid) {
		if (this.dim === 1) return this.V[nid];
		// dim > 1 ...
		const m = nid % this.maxbdd;
		const d = Math.floor(nid / this.maxbdd);
		const n = this.V[m].clone(); // this damn clone!!!
		if (n.v > 0) n.v += this.nvars * d;
		if (bdds.trueleaf(n.hi)) {
			if (d < this.dim-1) {
				n.hi = this.root + this.maxbdd * (d + 1);
			}
		} else {
			if (!bdds.leaf(n.hi)) {
				n.hi = n.hi + this.maxbdd * d;
			}
		}
		if (bdds.trueleaf(n.lo)) {
			if (d < this.dim-1) {
				n.lo = this.root + this.maxbdd * (d + 1);
			}
		} else {
			if (!bdds.leaf(n.lo)) {
				n.lo = n.lo + this.maxbdd * d;
			}
		}
		// _dbg_apply(`        ` + `this.maxbdd:${this.maxbdd} this.nvars:`, this.nvars);
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
		const n = v
			? new node(x + 1, bdds_base.T, bdds_base.F)
			: new node(x + 1, bdds_base.F, bdds_base.T);
		const res = this.add(n);
		return res;
	}
	// if-then-else operator
	ite(v, t, e) {
		const x = this.getnode(t);
		const y = this.getnode(e);
		if ((bdds.leaf(x) || v < x.v)
		&&  (bdds.leaf(y) || v < y.v)) {
			return this.add(new node(v + 1, t, e));
		}
		const hi = this.bdd_and(this.from_bit(v, true), t);
		const lo = this.bdd_and(this.from_bit(v, false), e);
		return this.bdd_or(hi, lo);
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
		const hi = this.copy(b, n.hi);
		const lo = this.copy(b, n.lo);
		const res = this.add(new node(n.v, hi, lo));
		if (options.memoization) this.memo_copy[t] = res;
		return res;
	}
	static apply(src, x, dst, y, op) {
		const apply_id = ++_counters.apply;
		// unary op
		if (op === undefined) {
			op = y; // take op from the third argument
			const r = bdds.apply_unary(src, x, dst, op);
			return r;
		}
		// binary op
		let t;
		if (options.memoization) {
			t = `${op._id}.${dst._id}.${x}.${y}`;
			if (src.memo_op.hasOwnProperty(t)) {
				return src.memo_op[t];
			}
		}
		const xn = src.getnode(x).clone();
		const yn = dst.getnode(y).clone();
		let v;

		if (((xn.v === 0) && (yn.v > 0))
		|| ((yn.v > 0) && (xn.v > yn.v))) {
			v = yn.v;
			xn.hi = x;
			xn.lo = x;
		} else {
			if (xn.v === 0) {
				const r = op.eval(xn.hi, yn.hi);
				return r;
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y; yn.lo = y;
				}
			}
		}
		const hi  = bdds.apply(src, xn.hi, dst, yn.hi, op);
		const lo = bdds.apply(src, xn.lo, dst, yn.lo, op);
		const r = dst.add(new node(v, hi, lo));
		if (options.memoization) src.memo_op[t] = r;
		return r;
	}
	static apply_ex     (src, x, dst, s) {
		return bdds.apply(src, x, dst, op_exists(s)); }
	static apply_and    (src, x, dst, y) {
		return bdds.apply(src, x, dst, y, op_and); }
	static apply_and_not(src, x, dst, y) {
		return bdds.apply(src, x, dst, y, op_and_not); }
	static apply_or     (src, x, dst, y) {
		return bdds.apply(src, x, dst, y, op_or); }
	static apply_and_ex (src, x, dst, y, s, p, sz) {
		const apply_id = ++_counters.apply_and_ex;
		let t;
		if (options.memoization) {
			t = `${dst._id}.${s.join(',')}.${x}.${y}`;
			if (src.memo_and_ex.hasOwnProperty(t)) {
				return src.memo_and_ex[t];
			}
		}
		const xn = src.getnode(x).clone();
		const yn = dst.getnode(y).clone();
		let v, res, hi, lo;
		do {
			if (bdds.leaf(xn)) {
				res = bdds.trueleaf(xn)
					? bdds.apply_ex(dst, y, dst, s)
					: bdds.F;
				break;
			}
			if (bdds.leaf(yn)) {
				res = !bdds.trueleaf(yn)
					? bdds.F
					: ((src === dst)
						? bdds.apply_ex(dst, x, dst, s)
						: bdds.apply_ex(dst, dst.copy(src, x), dst, s));
				break;
			}
			if (((xn.v === 0) && (yn.v > 0))
			|| ((yn.v > 0) && (xn.v > yn.v))) {
				v = yn.v;
				xn.hi = x;
				xn.lo = x;
			} else {
				if (xn.v === 0) {
					res = (xn.hi > 0) && (yn.hi > 0) ? bdds.T : bdds.F;
					break;
				} else {
					v = xn.v;
					if ((v < yn.v) || yn.v === 0) {
						yn.hi = y; yn.lo = y;
					}
				}
			}
			hi = bdds.apply_and_ex(src, xn.hi, dst, yn.hi, s, p, sz);
			lo = bdds.apply_and_ex(src, xn.lo, dst, yn.lo, s, p, sz);
			if ((v <= sz) && s[v-1]) {
				res = dst.bdd_or(hi, lo);
				break;
			}
			res = dst.add(new node(v, hi, lo));
		} while(0);
		if (options.memoization) { src.memo_and_ex[t] = res; }
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
		let r; // return value
		if (bdds.leaf(n)) {
			r = x;
		} else {
			const hi = this.permute(n.hi, m, sz);
			const lo = this.permute(n.lo, m, sz);
			r = this.ite(n.v <= sz ? m[n.v-1] : n.v-1, hi, lo);
		}
		if (options.memoization) this.memo_permute[t] = r;
		return r;
	}
	// helper constructors
	from_eq(x, y) { // a bdd saying "x=y"
		const res = this.bdd_or(
			this.bdd_and(this.from_bit(y, false), this.from_bit(x, false)),
			this.bdd_and(this.from_bit(y, true),  this.from_bit(x, true)));
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
						if (s[z][(ar*(j*bits+b)+i)] > 0) {
							r[n][ar*j+i] |= (1 << b);
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
	options.memoization = o.hasOwnProperty('memoization')
		? o.memoization
		: options.memoization;
	options.recursive = o.hasOwnProperty('recursive')
		? o.recursive
		: options.recursive;
	// load rec or non rec version of bdds class
	bdds = options.recursive ? bdds_rec : require('./bdds_non_rec');
	bdds.node = node;
	bdds.bdds_rec = bdds_rec;
	bdds.bdds_base = bdds_base;
	bdds.op = op;
	bdds.op_exists = op_exists;
	bdds.op_and = op_and;
	bdds.op_and_not = op_and_not;
	bdds.op_or = op_or;
	bdds.options = options;
	return bdds
}