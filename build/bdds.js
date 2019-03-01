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
// internal counters for every bdd and apply call
const _counters = { bdds: 0, apply: 0 };

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
		this.nvars = nvars;   // number of vars
		this.offset = 0;
		// used for implicit power
		this.pdim = 1;
		this.ndim = 0;
		this.root = 0;        // root of bdd
		this.maxbdd = 0;
		// initialize bdd with 0 and 1 terminals
		this.add_nocheck(new node(0, 0, 0));
		this.add_nocheck(new node(0, 1, 1));
	}
	static flip(n) {
		if (bdds_base.leaf(n)) return bdds_base.trueleaf(n) ? new node(0,0,0) : new node (0,1,1);
		const nn = n.clone();
		if (bdds_base.leaf(nn.hi)) nn.hi = bdds_base.trueleaf(nn.hi) ? bdds_base.F : bdds_base.T;
		if (bdds_base.leaf(nn.lo)) nn.lo = bdds_base.trueleaf(nn.lo) ? bdds_base.F : bdds_base.T;
		return nn;
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
	shift(n) {
		const nn = n.clone();
		if (!bdds_base.leaf(nn)) { nn.v += this.offset; }
		return nn;
	}
	// set virtual power
	setpow(root, p, n, maxw, offset) {
		this.root = root;
		this.pdim = p;
		this.ndim = n;
		this.offset = offset;
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
		if (this.pdim === 1 && this.ndim === 0) {
			const r = this.shift(this.V[nid])
			return r;
		}
		if (this.pdim === 0 && this.ndim === 1) {
			const r = this.shift(bdds_base.leaf(nid) ? this.V[nid] : bdds_base.flip(this.V[nid]));
			return r;
		}
		const m = nid % this.maxbdd;
		const d = Math.floor(nid / this.maxbdd);
		const n = d < this.pdim ? this.V[m].clone() : (bdds_base.leaf(m) ? this.V[m].clone() : bdds_base.flip(this.V[m]));
		if (n.v > 0) n.v += this.nvars * d;
		if (bdds_base.trueleaf(n.hi)) {
			if (d < this.pdim+this.ndim-1) {
				n.hi = this.root + this.maxbdd * (d + 1);
			}
		} else {
			if (!bdds_base.leaf(n.hi)) {
				n.hi = n.hi + this.maxbdd * d;
			}
		}
		if (bdds_base.trueleaf(n.lo)) {
			if (d < this.pdim+this.ndim-1) {
				n.lo = this.root + this.maxbdd * (d + 1);
			}
		} else {
			if (!bdds_base.leaf(n.lo)) {
				n.lo = n.lo + this.maxbdd * d;
			}
		}
		// _dbg_apply(`        ` + `this.maxbdd:${this.maxbdd} this.nvars:`, this.nvars);
		return this.shift(n);
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
			if (v !== nvars+1) {
				p[v-1] = true;
				this.sat(v+1, nvars, this.getnode(n.hi), p, r);
				p[v-1] = false;
				this.sat(v+1, nvars, this.getnode(n.lo), p, r);
			}	else {
				r.push(p.slice());
			}
		}
	}
	allsat(x, nvars) {
		const p = Array(nvars).fill(false); const r = [];
		this.sat(1, nvars, this.getnode(x), p, r)
		return r;
	}
	from_bit(x, v) {
		const n = v === true || v > 0
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
	delhead(x, h) {
		if (bdds.leaf(x)) {
			return x;
		}
		const n = this.getnode(x).clone();
		if (n.v > h) {
			return x;
		}
		const hi = this.delhead(n.hi, h);
		const lo = this.delhead(n.lo, h);
		const r = this.bdd_or(hi, lo);
		return r;
	}

	static apply_and(src, x, dst, y) {
		const apply_id = ++_counters.apply;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${dst._id}.${x}.${y}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (src.memo_and.hasOwnProperty(t)) {
				return src.memo_and[t];
			}
		}
		const xn = src.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? y : bdds.F;
			return apply_ret(r, src.memo_and);
		}
		const yn = dst.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn)
				? bdds.F
				: (src === dst ? x : dst.copy(src, x));
			return apply_ret(r, src.memo_and);
		}
		let v;
		if (((xn.v === 0) && (yn.v > 0))
		|| ((yn.v > 0) && (xn.v > yn.v))) {
			v = yn.v;
			xn.hi = x;
			xn.lo = x;
		} else {
			if (xn.v === 0) {
				const r = (a && b) ? bdds.T : bdds.F;
				return apply_ret(r, src.memo_and);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = bdds.apply_and(src, xn.hi, dst, yn.hi);
		const lo = bdds.apply_and(src, xn.lo, dst, yn.lo);
		const r = dst.add(new node(v, hi, lo));
		return apply_ret(r, src.memo_and);
	}

	static apply_and_not(src, x, dst, y) {
		const apply_id = ++_counters.apply;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${dst._id}.${x}.${y}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (src.memo_and.hasOwnProperty(t)) {
				return src.memo_and[t];
			}
		}
		const xn = src.getnode(x).clone();
		if (bdds.leaf(xn) && !bdds.trueleaf(xn)) {
			return apply_ret(bdds.F, src.memo_and_not);
		}
		const yn = dst.getnode(y).clone(); // copy from src?
		if (bdds.leaf(yn)) {
			const r = bdds.trueleaf(yn)
				? bdds.F
				: (src === dst ? x : dst.copy(src, x));
			return apply_ret(r, src.memo_and_not);
		}
		let v;
		if (((xn.v === 0) && (yn.v > 0))
		|| ((yn.v > 0) && (xn.v > yn.v))) {
			v = yn.v;
			xn.hi = x;
			xn.lo = x;
		} else {
			if (xn.v === 0) {
				const r = (a && !b) ? bdds.T : bdds.F;
				return apply_ret(r, src.memo_and_not);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = bdds.apply_and_not(src, xn.hi, dst, yn.hi);
		const lo = bdds.apply_and_not(src, xn.lo, dst, yn.lo);
		const r = dst.add(new node(v, hi, lo));
		return apply_ret(r, src.memo_and_not);
	}

	static apply_or(src, x, dst, y) {
		const apply_id = ++_counters.apply;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${dst._id}.${x}.${y}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (src.memo_or.hasOwnProperty(t)) {
				return src.memo_or[t];
			}
		}
		const xn = src.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? bdds.T : y;
			return apply_ret(r, src.memo_or);
		}
		const yn = dst.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = bdds.trueleaf(yn)
				? bdds.T
				: (src === dst ? x : dst.copy(src, x));
			return apply_ret(r, src.memo_or);
		}
		let v;
		if (((xn.v === 0) && (yn.v > 0))
		|| ((yn.v > 0) && (xn.v > yn.v))) {
			v = yn.v;
			xn.hi = x;
			xn.lo = x;
		} else {
			if (xn.v === 0) {
				const r = (a && b) ? bdds.T : bdds.F;
				return apply_ret(r, src.memo_or);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = bdds.apply_or(src, xn.hi, dst, yn.hi);
		const lo = bdds.apply_or(src, xn.lo, dst, yn.lo);
		const r = dst.add(new node(v, hi, lo));
		return apply_ret(r, src.memo_or);
	}
	// helper constructors
	from_eq(x, y) { // a bdd saying "x=y"
		const res = this.bdd_or(
			this.bdd_and(this.from_bit(y, false), this.from_bit(x, false)),
			this.bdd_and(this.from_bit(y, true),  this.from_bit(x, true)));
		return res;
	}
	from_bits(x, bits, ar, w) {
		const BIT = (term, arg, b) => (term*ar+arg)*bits+b;
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
						if (s[z][BIT(j, i, b)] > 0) {
							r[n][j * ar + i] |= 1 << b;
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
		this.memo_and = {};
		this.memo_and_not = {};
		this.memo_or = {};
		this.memo_copy = {};
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
	bdds.options = options;
	return bdds
}
