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

// internal counters for apply calls
const _counters = { apply: 0, or: 0, ex: 0, and: 0, deltail: 0,
	and_deltail: 0, and_ex: 0, and_not: 0, and_not_ex: 0, permute: 0 };

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
	// add node directly without checking
	add_nocheck(n) {
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
		return res;
	}
	// checks if node is terminal and is T
	static trueleaf(n) {
		const res = n instanceof node
			? bdds.leaf(n) && (n.hi > 0)
			: n === bdds.T;
		return res;
	}

	from_bit(x, v) {
		const n = v === true || v > 0
			? new node(x + 1, bdds.T, bdds.F)
			: new node(x + 1, bdds.F, bdds.T);
		const res = this.add(n);
		return res;
	}
	// adds new node
	add(n) {
		let r = null;
		let _dbg = '';
		do {
			if (n.hi === n.lo) { r = n.hi; break; }
			if (this.M.hasOwnProperty(n.key)) { r = this.M[n.key]; break; }
			r = this.add_nocheck(n);
			_dbg = ' nocheck';
		} while (0);
		return r;
	}

	sat(v, nvars, n, p, r) {
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
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = x+'.'+y;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_or.hasOwnProperty(t)) {
				return this.memo_or[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? bdds.T : y;
			return apply_ret(r, this.memo_or);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = bdds.trueleaf(yn) ? bdds.T : x;
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
		return apply_ret(r, this.memo_or);
	}

	ex(x, b) {
		const ex_id = ++_counters.ex;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = x+'.'+b.join(',');
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_ex.hasOwnProperty(t)) {
				return this.memo_ex[t];
			}
		}
		let n = this.getnode(x);
		if (bdds.leaf(n)) return x;
		if (b[n.v-1] === true || b[n.v-1] > 0) {
			x = this.or(n.hi, n.lo);
			if (bdds.leaf(x)) { return apply_ret(x, this.memo_ex); }
			n = this.getnode(x);
		}
		const hi = this.ex(n.hi, b);
		const lo = this.ex(n.lo, b);
		const r = this.add(new node(n.v, hi, lo));
		return apply_ret(r, this.memo_ex);
	}

	and(x, y) {
		const and_id = ++_counters.and;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${y}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and.hasOwnProperty(t)) {
				return this.memo_and[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? y : bdds.F;
			return apply_ret(r, this.memo_and);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn) ? bdds.F : x;
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
		return apply_ret(r, this.memo_and);
	}

	deltail(x, h) {
		const deltail_id = ++_counters.deltail;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${h}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_deltail.hasOwnProperty(t)) {
				return this.memo_deltail[t];
			}
		}
		if (bdds.leaf(x)) {
			return x;
		}
		const n = this.getnode(x).clone();
		if (n.v > h) {
			const r = n.hi === bdds.F && n.lo === bdds.F ? bdds.F : bdds.T;
			return apply_ret(r, this.memo_deltail);
		}
		const hi = this.deltail(n.hi, h);
		const lo = this.deltail(n.lo, h);
		const r = this.add(new node(n.v, hi, lo));
		return apply_ret(r, this.memo_deltail);
	}

	and_deltail(x, y, h) {
		const and_deltail_id = ++_counters.and_deltail;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${y}.${h}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and_deltail.hasOwnProperty(t)) {
				return this.memo_and_deltail[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? this.deltail(y, h) : bdds.F;
			return apply_ret(r, this.memo_and_deltail);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn) ? bdds.F : this.deltail(x, h);
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
		return apply_ret(r, this.memo_and_deltail);
	}

	and_ex(x, y, s) {
		const and_ex_id = ++_counters.and_ex;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${y}.${s.join(',')}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and_ex.hasOwnProperty(t)) {
				return this.memo_and_ex[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? this.ex(y, s) : bdds.F;
			return apply_ret(r, this.memo_and_ex);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn) ? bdds.F : this.ex(x, s);
			return apply_ret(r, this.memo_and_ex);
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
				return apply_ret(r, this.memo_and_ex);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		let r;
		if (s[v-1] === true || s[v-1] > 0) {
			const lo = this.and_ex(xn.lo, yn.lo, s);
			const hi  = this.and_ex(xn.hi, yn.hi, s);
			r = this.or(hi, lo);
		} else {
			const hi  = this.and_ex(xn.hi, yn.hi, s);
			const lo = this.and_ex(xn.lo, yn.lo, s);
			r = this.add(new node(v, hi, lo));
		}
		return apply_ret(r, this.memo_and_ex);
	}

	and_not(x, y) {
		const and_not_id = ++_counters.and_not;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = x+'.'+y;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and_not.hasOwnProperty(t)) {
				return this.memo_and_not[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn) && !bdds.trueleaf(xn)) {
			return apply_ret(bdds.F, this.memo_and_not);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = bdds.trueleaf(yn) ? bdds.F : x;
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
		return apply_ret(r, this.memo_and_not);
	}

	and_not_ex(x, y, s) {
		const and_not_ex_id = ++_counters.and_not_ex;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${y}.${s.join(',')}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_and_not_ex.hasOwnProperty(t)) {
				return this.memo_and_not_ex[t];
			}
		}
		const xn = this.getnode(x).clone();
		if (bdds.leaf(xn)) {
			const r = bdds.trueleaf(xn) ? this.ex(y, s) : bdds.F;
			return apply_ret(r, this.memo_and_not_ex);
		}
		const yn = this.getnode(y).clone();
		if (bdds.leaf(yn)) {
			const r = !bdds.trueleaf(yn) ? bdds.F : this.ex(x, s);
			return apply_ret(r, this.memo_and_not_ex);
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
				return apply_ret(r, this.memo_and_not_ex);
			} else {
				v = xn.v;
				if ((v < yn.v) || yn.v === 0) {
					yn.hi = y;
					yn.lo = y;
				}
			}
		}
		const hi  = this.and_not_ex(xn.hi, yn.hi, s);
		const lo = this.and_not_ex(xn.lo, yn.lo, s);
		const r = s[v-1]
			? this.or(hi, lo)
			: this.add(new node(v, hi, lo));
		return apply_ret(r, this.memo_and_not_ex);
	}

	// if-then-else operator
	ite(v, t, e) {
		const x = this.getnode(t);
		const y = this.getnode(e);
		if ((bdds.leaf(x) || v < x.v)
		&&  (bdds.leaf(y) || v < y.v)) {
			return this.add(new node(v + 1, t, e));
		}
		const hi = this.and(this.from_bit(v, true), t);
		const lo = this.and(this.from_bit(v, false), e);
		return this.or(hi, lo);
	}

	permute(x, m) {
		const permute_id = ++_counters.permute;
		let t;
		let apply_ret = r => r;
		if (options.memoization) {
			t = `${x}.${m.join(',')}`;
			apply_ret = (r, m) => { m[t] = r; return r; }
			if (this.memo_permute.hasOwnProperty(t)) {
				return this.memo_permute[t];
			}
		}
		if (bdds.leaf(x)) { return x; }
		const n = this.getnode(x);
		const hi = this.permute(n.hi, m);
		const lo = this.permute(n.lo, m);
		const r = this.ite(m[n.v-1], hi, lo);
		return apply_ret(r, this.memo_permute);
	}

	from_eq(x, y) { // a bdd saying "x=y"
		const res = this.or(
			this.and(this.from_bit(y, false), this.from_bit(x, false)),
			this.and(this.from_bit(y, true),  this.from_bit(x, true)));
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
