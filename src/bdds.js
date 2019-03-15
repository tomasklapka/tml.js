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
	memoization: false
}

// debug functions
const _dbg_bdd         = require('debug')('tml:bdd');
const _dbg_add         = require('debug')('tml:bdd:add');
const _dbg_leaf        = require('debug')('tml:bdd:leaf');
const _dbg_or          = require('debug')('tml:bdd:or');
const _dbg_ex          = require('debug')('tml:bdd:ex');
const _dbg_and         = require('debug')('tml:bdd:and');
const _dbg_deltail     = require('debug')('tml:bdd:deltail');
const _dbg_and_deltail = require('debug')('tml:bdd:and_deltail');
//const _dbg_and_many    = require('debug')('tml:bdd:and_many');
//const _dbg_and_ex      = require('debug')('tml:bdd:and_ex');
const _dbg_and_not     = require('debug')('tml:bdd:and_not');
//const _dbg_and_not_ex  = require('debug')('tml:bdd:and_not_ex');
const _dbg_permute     = require('debug')('tml:bdd:permute');
const _dbg_ite         = require('debug')('tml:bdd:ite');
const _dbg_fn_enter    = (...a) => 0; //console.log(...a);

// internal counters for apply calls
const _counters = { or: 0, ex: 0, and: 0, deltail: 0, and_many: 0, add: 0,
	and_deltail: 0, and_ex: 0, and_not: 0, and_not_ex: 0, permute: 0, ite: 0,
	sat: 0, add_nocheck: 0 };

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
class bdds {
	// F=0 and T=1 consants
	static get F() { return 0; }
	static get T() { return 1; }
	// length getter
	get length() { return this.V.length; }
	// initialize bdds
	constructor() {
		this._id = ++_counters.bdds;
		this.V = [];          // all nodes
		this.M = {};          // node to its index
		// initialize bdd with 0 and 1 terminals
		this.add_nocheck(new node(0, 0, 0));
		this.add_nocheck(new node(0, 1, 1));
		this.memos_clear();
	}
	_count(x, nvars) {
		const n = this.getnode(x);
		let k;
		let r = 0;
		if (bdds.leaf(n)) return bdds.trueleaf(n) ? 1 : 0;
		k = this.getnode(n.hi);
		r += this.count(n.hi, nvars)*(1<<(((nleaf(k)?nvars+1-n[0]:(k[0]-n[0])))-1));
		k = getnode(n[2]);
		r += count(n[2], nvars)*(1<<(((nleaf(k)?nvars+1-n[0]:(k[0]-n[0])))-1));
		return r;
	}
	count(x, nvars) {
		return x < 2
			? x
				? (1<<(nvars))
				: 0
			: (this._count(x, nvars) << (this.getnode(x).v-1));
	}
	onesat(x, nvars, r) {
		if (bdds.leaf(x)) return bdds.trueleaf(x);
		let n = this.getnode(x);
		if (bdds.leaf(n.lo) && !bdds.trueleaf(n.lo)) {
			r[n.v-1] = true;
			return this.onesat(n.hi, nvars, r);
		}
		r[n.v-1] = false;
		return this.onesat(n.lo, nvars, r);
	}

	from_int_and(x, y, o, r) {
		return this.and(r, this.from_int(x, y, o));
	}

	from_int(x, bits, offset) {
		const id = ++_counters.from_int;
		_dbg_fn_enter(`from_int-${id}`);
		let r = bdds.T;
		let b = bits--;
		while (b--) r = this.and(r, this.from_bit(bits - b + offset, x & (1 << b)));
		return r;
	}

	pad(x, ar1, ar2, p, bits) {
		for (let n = ar1; n != ar2; ++n) {
			x = this.from_int_and(p, bits, n * bits, x);
		}
		return x;
	}

	// add node directly without checking
	add_nocheck(n) {
		const id = ++_counters.add_nocheck;
		_dbg_fn_enter(`add_nocheck-${id}`);
		const r = this.V.length;
		this.M[n.key] = r;
		this.V.push(n);
		return r;
	}
	// returns node by its index
	getnode(nid) { return this.V[nid]; }
	// checks if node is terminal (leaf)
	static leaf(n) {
		const res = n instanceof node
			? n.v === 0
			: n === bdds.T || n === bdds.F;
		_dbg_leaf(`${res ? ' is' : 'not'} leaf ${n instanceof node ? n.key : n}`);
		return res;
	}
	// checks if node is terminal and is T
	static trueleaf(n) {
		const res = n instanceof node
			? bdds.leaf(n) && (n.hi > 0)
			: n === bdds.T;
		_dbg_leaf(`leaf ${n instanceof node ? n.key : n} is ${res}`);
		return res;
	}

	from_bit(x, v) {
		const n = v === true || v > 0
			? new node(x + 1, bdds.T, bdds.F)
			: new node(x + 1, bdds.F, bdds.T);
		const res = this.add(n);
		_dbg_bdd(`from_bit x:${x}, v:${v}, n:${n.key}, res:${res}`);
		return res;
	}
	// adds new node
	add(n) {
		const id = ++_counters.add;
		_dbg_fn_enter(`add-${id}`); _dbg_add(`add-${id} (${n.key})`);
		let r = null;
		let _dbg = '';
		do {
			if (n.hi === n.lo) { r = n.hi; _dbg = 'hi === lo'; break; }
			if (this.M.hasOwnProperty(n.key)) { r = this.M[n.key]; break; }
			r = this.add_nocheck(n);
			_dbg = ' nocheck';
		} while (0);
		_dbg_add(`/add-${id} ${r} (${n.key})${_dbg}`);
		return r;
	}

	sat(v, nvars, n, p, r) {
		const id = ++_counters.sat;
		_dbg_fn_enter(`sat-${id}`);
		if (bdds.leaf(n) && !bdds.trueleaf(n)) return;
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

	or(x, y) {
		const or_id = ++_counters.or;
		_dbg_fn_enter(`or-${or_id} (${x} or ${y})`);
		if (x === y) return x;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = x+'.'+y;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_or.hasOwnProperty(t)) {
				_dbg_or(`/or-${or_id} ${this.memo_or[t]} (${x} or1 ${y}) (memo:${t})`);
				return this.memo_or[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? bdds.T : y;
			_dbg_or(`/or-${or_id} ${r} (${x} or2 ${y}) xn is leaf`);
			return apply_ret(r, this.memo_or);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = bdds.trueleaf(yn) ? bdds.T : x;
			_dbg_or(`/or-${or_id} ${r} (${x} or3 ${y}) yn is leaf`);
			return apply_ret(r, this.memo_or);
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
				_dbg_or(`/or-${or_id} ${r} (${x} or4 ${y})`);
				return apply_ret(r, this.memo_or);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = this.or(xn.hi, yn.hi);
		const lo = this.or(xn.lo, yn.lo);
		const r = this.add(new node(v, hi, lo));
		_dbg_or(`/or-${or_id} ${r} (${x} or5 ${y})`);
		return apply_ret(r, this.memo_or);
	}

	ex(x, b) {
		const ex_id = ++_counters.ex;
		_dbg_fn_enter(`ex-${ex_id} (${x} ex ${b.map(n=>n?'1':'0').join('')})`);
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = x+'.'+b.join(',');
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_ex.hasOwnProperty(t)) {
				_dbg_ex(`/ex(${ex_id}) ${this.memo_ex[t]} (${x} ex1 ${b.map(n=>n?'1':'0').join('')}) (memo:${t})`);
				return this.memo_ex[t];
			}
		}
		if (bdds.leaf(x)) {
			_dbg_ex(`/ex-${ex_id} ${x} (${x} ex2 ${b.map(n=>n?'1':'0').join('')}) x is leaf`);
			return x;
		}
		let n = this.getnode(x);
		while (b[n.v-1] === true || b[n.v-1] > 0) {
			x = this.or(n.hi, n.lo);
			if (bdds.leaf(x)) {
				_dbg_ex(`/ex-${ex_id} ${x} (${x} ex3 ${b.map(n=>n?'1':'0').join('')}) x is leaf2`);
				return apply_ret(x, this.memo_ex);
			}
			n = this.getnode(x);
		}
		const hi = this.ex(n.hi, b);
		const lo = this.ex(n.lo, b);
		const nn = new node(n.v, hi, lo);
		const r = this.add(nn);
		_dbg_ex(`/ex-${ex_id} ${r} (${r} ex4 ${b.map(n=>n?'1':'0').join('')}) n:${nn.key}`);
		return apply_ret(r, this.memo_ex);
	}

	and(x, y) {
		const and_id = ++_counters.and;
		_dbg_fn_enter(`and-${and_id} (${x} and ${y})`);
		if (x === y) return x;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${y}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and.hasOwnProperty(t)) {
				_dbg_and(`/and-${and_id} ${this.memo_and[t]} (${x} and1 ${y}) (memo:${t})`);
				return this.memo_and[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? y : bdds.F;
			_dbg_and(`/and-${and_id} ${r} (${x} and2 ${y}) xn is leaf`);
			return apply_ret(r, this.memo_and);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn) ? bdds.F : x;
			_dbg_and(`/and-${and_id} ${r} (${x} and3 ${y}) yn is leaf`);
			return apply_ret(r, this.memo_and);
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
				_dbg_and(`/and-${and_id} ${r} (${x} and4 ${y})`);
				return apply_ret(r, this.memo_and);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = this.and(xn.hi, yn.hi);
		const lo = this.and(xn.lo, yn.lo);
		const r = this.add(new node(v, hi, lo));
		_dbg_and(`/and-${and_id} ${r} (${x} and5 ${y})`);
		return apply_ret(r, this.memo_and);
	}

	and_not(x, y) {
		const and_not_id = ++_counters.and_not;
		_dbg_fn_enter(`and_not-${and_not_id} (${x} and_not ${y})`);
		if (x === y) return bdds.F;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = x+'.'+y;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and_not.hasOwnProperty(t)) {
				_dbg_and_not(`/and_not-${and_not_id} ${this.memo_and_not[t]} (${x} and not1 ${y}) (memo:${t})`);
				return this.memo_and_not[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn) && !bdds.trueleaf(xn)) {
			_dbg_and_not(`/and_not-${and_not_id} 0 (${x} and not2 ${y}) xn is leaf`);
			return apply_ret(bdds.F, this.memo_and_not);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = bdds.trueleaf(yn) ? bdds.F : x;
			_dbg_and_not(`/and_not-${and_not_id} ${r} (${x} and not3 ${y}) yn is leaf`);
			return apply_ret(r, this.memo_and_not);
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
				_dbg_and_not(`/and_not-${and_not_id} ${r} (${x} and not4 ${y})`);
				return apply_ret(r, this.memo_and_not);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi = this.and_not(xn.hi, yn.hi);
		const lo = this.and_not(xn.lo, yn.lo);
		const r = this.add(new node(v, hi, lo));
		_dbg_and_not(`/and_not-${and_not_id} ${r} (${x} and not5 ${y})`);
		return apply_ret(r, this.memo_and_not);
	}

	deltail(x, h) {
		const deltail_id = ++_counters.deltail;
		_dbg_fn_enter(`deltail-${deltail_id} (${x} deltail ${h})`);
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${h}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_deltail.hasOwnProperty(t)) {
				_dbg_deltail(`/deltail-${deltail_id} ${this.memo_deltail[t]} (${x}, ${h}) (memo:${t})`);
				return this.memo_deltail[t];
			}
		}
		if (bdds.leaf(x)) {
			_dbg_deltail(`/deltail-${deltail_id} ${x} (${x}, ${h}) leaf`);
			return x;
		}
		const n = this.getnode(x).clone();
		if (n.v > h) {
			const r = n.hi === bdds.F && n.lo === bdds.F ? bdds.F : bdds.T;
			_dbg_deltail(`/deltail-${deltail_id} ${r} (${x}, ${h}) (${n.v} > ${h}) n:${n.key}`);
			return apply_ret(r, this.memo_deltail);
		}
		const hi = this.deltail(n.hi, h);
		const lo = this.deltail(n.lo, h);
		const r = this.add(new node(n.v, hi, lo));
		_dbg_deltail(`/deltail-${deltail_id} ${r} (${x}, ${h}) (hi: ${hi}, lo: ${lo})`);
		return apply_ret(r, this.memo_deltail);
	}

	and_deltail(x, y, h) {
		const and_deltail_id = ++_counters.and_deltail;
		_dbg_fn_enter(`and_deltail-${and_deltail_id} (${x} and_deltail ${y}, ${h})`);
		if (x === y) return this.deltail(x, h);
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${y}.${h}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and_deltail.hasOwnProperty(t)) {
				_dbg_and_deltail(`/and_deltail-${and_deltail_id} ${this.memo_and_deltail[t]} (${x} and_deltail1 ${y}, ${h}) (memo:${t})`);
				return this.memo_and_deltail[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? this.deltail(y, h) : bdds.F;
			_dbg_and_deltail(`/and_deltail-${and_deltail_id} ${r} (${x} and_deltail2 ${y}, ${h}) xn is leaf`);
			return apply_ret(r, this.memo_and_deltail);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn) ? bdds.F : this.deltail(x, h);
			_dbg_and_deltail(`/and_deltail-${and_deltail_id} ${r} (${x} and_deltail3 ${y}, ${h}) yn is leaf`);
			return apply_ret(r, this.memo_and_deltail);
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
				_dbg_and_deltail(`/and_deltail-${and_deltail_id} ${r} (${x} and_deltail4 ${y}, ${h})`);
				return apply_ret(r, this.memo_and_deltail);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = this.and_deltail(xn.hi, yn.hi, h);
		const lo = this.and_deltail(xn.lo, yn.lo, h);
		const r = this.deltail(this.add(new node(v, hi, lo)), h);
		_dbg_and_deltail(`/and_deltail-${and_deltail_id} ${r} (${x} and_deltail5 ${y}, ${h})`);
		return apply_ret(r, this.memo_and_deltail);
	}

	and_many(v) {
		const id = ++_counters.and_many;
		_dbg_fn_enter(`and_many-${id} (v:${v.join(',')})`);
		let from = 0;
		if (1 === (v.length - from)) {
			return v[from];
		}
		while (bdds.leaf(v[from])) {
			if (!bdds.trueleaf(v[from])) {
				return bdds.F;
			} else {
				if (1 === (v.length - ++from)) {
					return v[from];
				}
			}
		}
		let t = v[from];
		let m = this.getnode(t).v;
		let b = false;
		let eq = true;
		for (let i = from + 1; i != v.length; ++i) {
			if (bdds.leaf(v[i])) {
				if (!bdds.trueleaf(v[i])) return bdds.F;
				continue;
			}
			const n = this.getnode(v[i]);
			b |= n.v != m;
			eq &= t === v[i];
			if (n.v < m) m = n.v;
		}
		if (eq) return t;
		const v1 = Array(v.length - from);
		const v2 = Array(v.length - from);
		for (let i = from; i != v.length; ++i) {
			if (!b || this.getnode(v[i]).v === m) {
				v1.push(bdds.leaf(v[i]) ? v[i] : this.getnode(v[i]).hi);
			} else {
				v1.push(v[i]);
			}
		}
		for (let i = from; i != v.length; ++i) {
			if (!b || this.getnode(v[i]).v === m) {
				v2.push(bdds.leaf(v[i]) ? v[i] : this.getnode(v[i]).lo);
			} else {
				v2.push(v[i]);
			}
		}
		const hi = this.and_many(v1);
		const lo = this.and_many(v2);
		return this.add(new node(m, hi, lo));
	}

	// and_ex(x, y, s) {
	// 	const and_ex_id = ++_counters.and_ex;
	// 	_dbg_and_ex(`and_ex_id++ = ${and_ex_id} (${x} and_ex ${y}, ${s.join(',')})`);
	// 	if (x === y) return this.ex(x, s);
	// 	let t;
	// 	let apply_ret = r => r;
	// 	if (options.memoization) {
	// 		t = `${x}.${y}.${s.join(',')}`;
	// 		apply_ret = (r, m) => { m[t] = r; return r; }
	// 		if (this.memo_and_ex.hasOwnProperty(t)) {
	// 			_dbg_and_ex(`and_ex(${and_ex_id}) ${this.memo_and_ex[t]} (${x} and_ex1 ${y}, ${s.join(',')}) (memo:${t})`);
	// 			return this.memo_and_ex[t];
	// 		}
	// 	}
	// 	const xn = this.getnode(x).clone();
	// 	if (bdds.leaf(xn)) {
	// 		const r = bdds.trueleaf(xn) ? this.ex(y, s) : bdds.F;
	// 		_dbg_and_ex(`and_ex(${and_ex_id}) ${r} (${x} and_ex2 ${y}, ${s.join(',')}) xn is leaf`);
	// 		return apply_ret(r, this.memo_and_ex);
	// 	}
	// 	const yn = this.getnode(y).clone();
	// 	if (bdds.leaf(yn)) {
	// 		const r = !bdds.trueleaf(yn) ? bdds.F : this.ex(x, s);
	// 		_dbg_and_ex(`and_ex(${and_ex_id}) ${r} (${x} and_ex3 ${y}, ${s.join(',')}) yn is leaf`);
	// 		return apply_ret(r, this.memo_and_ex);
	// 	}
	// 	let v;
	// 	if (((xn.v === 0) && (yn.v > 0))
	// 	|| ((yn.v > 0) && (xn.v > yn.v))) {
	// 		v = yn.v;
	// 		xn.hi = x;
	// 		xn.lo = x;
	// 	} else {
	// 		if (xn.v === 0) {
	// 			const r = (a && b) ? bdds.T : bdds.F;
	// 			_dbg_and_ex(`and_ex(${and_ex_id}) ${r} (${x} and_ex4 ${y}, ${s.join(',')})`);
	// 			return apply_ret(r, this.memo_and_ex);
	// 		} else {
	// 			v = xn.v;
	// 			if ((v < yn.v) || yn.v === 0) {
	// 				yn.hi = y;
	// 				yn.lo = y;
	// 			}
	// 		}
	// 	}
	// 	let r;
	// 	if (s[v-1] === true || s[v-1] > 0) {
	// 		const lo = this.and_ex(xn.lo, yn.lo, s);
	// 		const hi  = this.and_ex(xn.hi, yn.hi, s);
	// 		r = this.or(hi, lo);
	// 	} else {
	// 		const hi  = this.and_ex(xn.hi, yn.hi, s);
	// 		const lo = this.and_ex(xn.lo, yn.lo, s);
	// 		r = this.add(new node(v, hi, lo));
	// 	}
	// 	_dbg_and_ex(`and_ex(${and_ex_id}) ${r} (${x} and_ex5 ${y}, ${s.join(',')})`);
	// 	return apply_ret(r, this.memo_and_ex);
	// }
	// and_not_ex(x, y, s) {
	// 	const and_not_ex_id = ++_counters.and_not_ex;
	// 	_dbg_and_not_ex(`and_not_ex_id++ = ${and_not_ex_id} (${x} and_not_ex ${y}, ${s.join(',')})`);
	// 	if (x === y) return bdds.F;
	// 	let t;
	// 	let apply_ret = r => r;
	// 	if (options.memoization) {
	// 		t = `${x}.${y}.${s.join(',')}`;
	// 		apply_ret = (r, m) => { m[t] = r; return r; }
	// 		if (this.memo_and_not_ex.hasOwnProperty(t)) {
	// 			_dbg_and_not_ex(`and_not_ex(${and_not_ex_id}) ${this.memo_and_not_ex[t]} (${x} and_not_ex1 ${y}, ${s.join(',')}) (memo:${t})`);
	// 			return this.memo_and_not_ex[t];
	// 		}
	// 	}
	// 	const xn = this.getnode(x).clone();
	// 	if (bdds.leaf(xn)) {
	// 		const r = bdds.trueleaf(xn) ? this.ex(y, s) : bdds.F;
	// 		_dbg_and_not_ex(`and_not_ex(${and_not_ex_id}) ${r} (${x} and_not_ex2 ${y}, ${s.join(',')}) xn is leaf`);
	// 		return apply_ret(r, this.memo_and_not_ex);
	// 	}
	// 	const yn = this.getnode(y).clone();
	// 	if (bdds.leaf(yn)) {
	// 		const r = !bdds.trueleaf(yn) ? bdds.F : this.ex(x, s);
	// 		_dbg_and_not_ex(`and_not_ex(${and_not_ex_id}) ${r} (${x} and_not_ex3 ${y}, ${s.join(',')}) yn is leaf`);
	// 		return apply_ret(r, this.memo_and_not_ex);
	// 	}
	// 	let v;
	// 	if (((xn.v === 0) && (yn.v > 0))
	// 	|| ((yn.v > 0) && (xn.v > yn.v))) {
	// 		v = yn.v;
	// 		xn.hi = x;
	// 		xn.lo = x;
	// 	} else {
	// 		if (xn.v === 0) {
	// 			const r = (a && b) ? bdds.T : bdds.F;
	// 			_dbg_and_not_ex(`and_not_ex(${and_not_ex_id}) ${r} (${x} and_not_ex4 ${y}, ${s.join(',')})`);
	// 			return apply_ret(r, this.memo_and_not_ex);
	// 		} else {
	// 			v = xn.v;
	// 			if ((v < yn.v) || yn.v === 0) {
	// 				yn.hi = y;
	// 				yn.lo = y;
	// 			}
	// 		}
	// 	}
	// 	const hi  = this.and_not_ex(xn.hi, yn.hi, s);
	// 	const lo = this.and_not_ex(xn.lo, yn.lo, s);
	// 	const r = s[v-1]
	// 		? this.or(hi, lo)
	// 		: this.add(new node(v, hi, lo));
	// 	_dbg_and_not_ex(`and_not_ex(${and_not_ex_id}) ${r} (${x} and_not_ex5 ${y}, ${s.join(',')})`);
	// 	return apply_ret(r, this.memo_and_not_ex);
	// }
	// if-then-else operator
	ite(v, t, e) {
		const id = ++_counters.ite;
		_dbg_fn_enter(`ite-${id} (v:${v}, t:${t}, e:${e})`);
		const x = this.getnode(t);
		const y = this.getnode(e);
		_dbg_ite(`-ite-${id} (x:${x.key}, y:${y.key})`);
		if ((bdds.leaf(x) || v < x.v)
		&&  (bdds.leaf(y) || v < y.v)) {
			_dbg_ite(`-ite-${id} leafs`);
			const n = new node(v + 1, t, e);
			const r = this.add(n);
			_dbg_ite(`/ite1-${id} (v:${v}, t:${t} ${x.key}, e:${e} ${y.key}) = ${r} (${n.key})`)
			return r;
		}
		_dbg_ite(`-ite-${id} lo`);
		const lo = this.and(this.from_bit(v, false), e);
		_dbg_ite(`-ite-${id} lo: ${lo}`);
		_dbg_ite(`-ite-${id} hi`);
		const hi = this.and(this.from_bit(v, true), t);
		_dbg_ite(`-ite-${id} hi: ${hi}`);
		const r = this.or(hi, lo);
		_dbg_ite(`/ite2-${id} (v:${v}, t:${t} (${x.key}), e:${e}) (${y.key}) = ${r} (hi:${hi}, lo:${lo})`);
		return r;
	}

	permute(x, m) {
		const permute_id = ++_counters.permute;
		_dbg_permute(`permute-${permute_id} (${x} permute ${m.join(',')})`);
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${m.join(',')}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_permute.hasOwnProperty(t)) {
				_dbg_permute(`/permute-${permute_id} ${this.memo_permute[t]} (${x} permute1 ${m.join(',')}) (memo:${t})`);
				return this.memo_permute[t];
			}
		}

		if (bdds.leaf(x)) {
			_dbg_permute(`/permute(${permute_id}) = ${x} (${x} permute2 ${m.join(',')}) x is leaf`);
			return x;
		}
		const n = this.getnode(x);
		const lo = this.permute(n.lo, m);
		_dbg_permute(`-permute-${permute_id} lo: ${lo}`);
		const hi = this.permute(n.hi, m);
		_dbg_permute(`-permute-${permute_id} hi: ${hi}`);
		const r = this.ite(m[n.v-1], hi, lo);
		_dbg_permute(`/permute-${permute_id} = ${r} (${x} permute3 ${m.join(',')}) hi: ${hi}, lo: ${lo}, n.v:${n.v}, m[n.v-1]:${m[n.v-1]}`);
		return apply_ret(r, this.memo_permute);
	}

	from_eq(x, y) { // a bdd saying "x=y"
		const n = new node();
		if (x < y) {
			n.v = x+1;
			n.lo = this.from_bit(y, false);
			n.hi = this.from_bit(y, true);
		} else {
			n.v = y+1;
			n.lo = this.from_bit(x, false);
			n.hi = this.from_bit(x, true);
		}
		const res = this.add(n);
		_dbg_bdd(`from_eq x:${x} y:${y} = ${res}`);
		return res;
	}

	memos_clear() {
		if (!options.memoization) return;
		this.memo_and = {};
		this.memo_and_not = {};
		this.memo_or = {};
		this.memo_permute = {};
		this.memo_and_ex = {};
		this.memo_and_not_ex = {};
		this.memo_deltail = {};
		this.memo_and_deltail = {};
		this.memo_ex = {};
	}
}

module.exports = (o = {}) => {
	options.memoization = o.hasOwnProperty('memoization')
		? o.memoization
		: options.memoization;
	return { node, bdds };
}
