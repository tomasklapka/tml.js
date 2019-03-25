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

//## define MEMO

//## ifdef MEMO
//##   define apply_ret(r, m) m[t] = r; return r
//## else
//##   define apply_ret(r, m) return r
//## endif

//## define getnode(x) this.V[x]
//## define leaf(x) (((x) === bdds.T) || ((x) === bdds.F))
//## define nleaf(x) ((x).v === 0)
//## define trueleaf(x) ((x) === bdds.T)
//## define ntrueleaf(x) (nleaf(x) && (x).hi > 0)
//## undef from_bit
//## define from_bit(x, v) (this.add((v) \
//#        ? new node(x+1, bdds.T, bdds.F) \
//#        : new node(x+1, bdds.F, bdds.T)))
//## undef from_int_and
//## define from_int_and(x, y, o, r) r = this.and(r, this.from_int(x, y, o))

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
		ID('bdds')
		DBG(this.__id = id);
		this.V = [];          // all nodes
		this.M = {};          // node to its index
		// initialize bdd with 0 and 1 terminals
		this.add_nocheck(new node(0, 0, 0));
		this.add_nocheck(new node(0, 1, 1));
		this.memos_clear();
	}
	_count(x, nvars) {
		const n = getnode(x);
		let k;
		let r = 0;
		if (nleaf(n)) return ntrueleaf(n) ? 1 : 0;
		k = getnode(n.hi);
		r += this.count(n.hi, nvars)*(1<<(((nleaf(k)?nvars+1-n[0]:(k[0]-n[0])))-1));
		k = getnode(n[2]);
		r += count(n[2], nvars)*(1<<(((nleaf(k)?nvars+1-n[0]:(k[0]-n[0])))-1));
		return r;
	}
	count(x, nvars) {
		return x < 2
			? x
				? (1 << nvars)
				: 0
			: (this._count(x, nvars) << (getnode(x).v-1));
	}
	onesat(x, nvars, r) {
		if (leaf(x)) return trueleaf(x);
		let n = getnode(x);
		if (leaf(n.lo) && !trueleaf(n.lo)) {
			r[n.v-1] = true;
			return this.onesat(n.hi, nvars, r);
		}
		r[n.v-1] = false;
		return this.onesat(n.lo, nvars, r);
	}

	from_int(x, bits, offset) {
		ID_TRC('from_int');
		let r = bdds.T;
		let b = bits--;
		while (b--) r = this.and(r, from_bit(bits-b+offset, x&(1<<b)));
		return r;
	}

	from_range(max, bits, offset, ex, r) {
		ID_TRC('from_range');
		let x = bdds.F;
		for (let n = 0; n != max; ++n) {
			if (!ex.includes(n)) {
				x = this.or(x, this.from_int(n, bits, offset));
			}
		}
		return this.and(r, x);
	}

	pad(x, ar1, ar2, p, bits) {
		for (let n = ar1; n != ar2; ++n) {
			x = from_int_and(p, bits, n * bits, x);
		}
		return x;
	}

	rebit(x, prev, curr, nvars) {
		if (prev == curr) return x;
		if (prev > curr) throw new Error('assert prev < curr');
		const v = Array(nvars);
		let t = bdds.T;
		for (let n = 0; n != nvars; ++n) {
			v[n] = (n % prev) + curr - prev + curr * (n / prev);
			for (let k = 0; k != curr - prev; ++k) {
				t = this.and(t, from_bit((n / prev) * curr + k, false));
			}
		}
		return this.and(t, this.permute(x, v));
	}

	// add node directly without checking
	add_nocheck(n) {
		ID_TRC('add_nocheck');
		const r = this.V.length;
		this.M[n.key] = r;
		this.V[this.V.length] = n;
		return r;
	}

	// adds new node
	add(n) {
		ID_TRC('add');
		DBG(__add(`add-${id} (${n.key})`));
		//TRC(`add-${id}`);
		let r = null;
		DBG()//let __dbg = '');
		do {
			if (n.hi === n.lo) { r = n.hi; DBG(__dbg = 'hi === lo'); break; }
			if (this.M.hasOwnProperty(n.key)) { r = this.M[n.key]; break; }
			r = this.add_nocheck(n);
			DBG(__dbg = ' nocheck');
		} while (0);
		DBG(__add(`/add-${id} ${r} (${n.key})${__dbg}`));
		return r;
	}

	sat(v, nvars, n, p, r) {
		ID_TRC('sat');
		DBG(__bdd(`sat-${id} (v: ${v}, nvars: ${nvars}, n: ${n.key}, r: ${r})`));
		if (nleaf(n) && !ntrueleaf(n)) return;
		if (v < n.v) {
			p[v-1] = true;
			this.sat(v+1, nvars, n, p, r);
			p[v-1] = false;
			this.sat(v+1, nvars, n, p, r);
		} else {
			if (v !== nvars+1) {
				p[v-1] = true;
				this.sat(v+1, nvars, getnode(n.hi), p, r);
				p[v-1] = false;
				this.sat(v+1, nvars, getnode(n.lo), p, r);
			}	else {
				r[r.length] = p.slice();
			}
		}
	}

	allsat(x, nvars) {
		ID_TRC('allsat');
		DBG(__bdd(`allsat-${id} (x: ${x}, nvars: ${nvars})`, x));
		const p = Array(nvars).fill(false); const r = [];
		this.sat(1, nvars, getnode(x), p, r);
		return r;
	}

	or(x, y) {
		ID_TRC('or');
		if (x === y) return x;
//## ifdef MEMO
		const t = x+'.'+y;
		if (this.memo_or.hasOwnProperty(t)) {
			DBG(__or(`/or-${id} ${this.memo_or[t]} (${x} or1 ${y}) (memo:${t})`));
			return this.memo_or[t];
		}
//## endif
		const xn = getnode(x).clone();
		if (nleaf(xn)) {
			const r = ntrueleaf(xn) ? bdds.T : y;
			DBG(__or(`/or-${id} ${r} (${x} or2 ${y}) xn is leaf`));
			apply_ret(r, this.memo_or);
		}
		const yn = getnode(y).clone();
		if (nleaf(yn)) {
			const r = ntrueleaf(yn) ? bdds.T : x;
			DBG(__or(`/or-${id} ${r} (${x} or3 ${y}) yn is leaf`));
			apply_ret(r, this.memo_or);
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
				DBG(__or(`/or-${id} ${r} (${x} or4 ${y})`));
				apply_ret(r, this.memo_or);
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
		DBG(__or(`/or-${id} ${r} (${x} or5 ${y})`));
		apply_ret(r, this.memo_or);
	}

	ex(x, b) {
		ID('ex');
		TRC(`ex-${id} (${x} ex ${b.map(n=>n?'1':'0').join('')})`);
//## ifdef MEMO
		const t = x+'.'+b.join(',');
		if (this.memo_ex.hasOwnProperty(t)) {
			DBG(__ex(`/ex(${id}) ${this.memo_ex[t]} (${x} ex1 ${b.map(n=>n?'1':'0').join('')}) (memo:${t})`));
			return this.memo_ex[t];
		}
//## endif
		if (leaf(x)) {
			DBG(__ex(`/ex-${id} ${x} (${x} ex2 ${b.map(n=>n?'1':'0').join('')}) x is leaf`));
			return x;
		}
		let n = getnode(x);
		while (b[n.v-1] === true || b[n.v-1] > 0) {
			x = this.or(n.hi, n.lo);
			if (leaf(x)) {
				DBG(__ex(`/ex-${id} ${x} (${x} ex3 ${b.map(n=>n?'1':'0').join('')}) x is leaf2`));
				apply_ret(x, this.memo_ex);
			}
			n = getnode(x);
		}
		const hi = this.ex(n.hi, b);
		const lo = this.ex(n.lo, b);
		const nn = new node(n.v, hi, lo);
		const r = this.add(nn);
		DBG(__ex(`/ex-${id} ${r} (${r} ex4 ${b.map(n=>n?'1':'0').join('')}) n:${nn.key}`));
		apply_ret(r, this.memo_ex);
	}

	and(x, y) {
		ID('and');
		TRC(`and-${id} (${x} and ${y})`);
		if (x === y) return x;
//## ifdef MEMO
		const t = `${x}.${y}`;
		if (this.memo_and.hasOwnProperty(t)) {
			DBG(__and(`/and-${id} ${this.memo_and[t]} (${x} and1 ${y}) (memo:${t})`));
			return this.memo_and[t];
		}
//## endif
		const xn = getnode(x).clone();
		if (nleaf(xn)) {
			const r = ntrueleaf(xn) ? y : bdds.F;
			DBG(__and(`/and-${id} ${r} (${x} and2 ${y}) xn is leaf`));
			apply_ret(r, this.memo_and);
		}
		const yn = getnode(y).clone();
		if (nleaf(yn)) {
			const r = !ntrueleaf(yn) ? bdds.F : x;
			DBG(__and(`/and-${id} ${r} (${x} and3 ${y}) yn is leaf`));
			apply_ret(r, this.memo_and);
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
				DBG(__and(`/and-${id} ${r} (${x} and4 ${y})`));
				apply_ret(r, this.memo_and);
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
		DBG(__and(`/and-${id} ${r} (${x} and5 ${y})`));
		apply_ret(r, this.memo_and);
	}

	and_not(x, y) {
		ID('and_not');
		TRC(`and_not-${id} (${x} and_not ${y})`);
		if (x === y) return bdds.F;
//## ifdef MEMO
		const t = x+'.'+y;
		if (this.memo_and_not.hasOwnProperty(t)) {
			DBG(__and_not(`/and_not-${id} ${this.memo_and_not[t]} (${x} and not1 ${y}) (memo:${t})`));
			return this.memo_and_not[t];
		}
//## endif
		const xn = getnode(x).clone();
		if (nleaf(xn) && !ntrueleaf(xn)) {
			DBG(__and_not(`/and_not-${id} 0 (${x} and not2 ${y}) xn is leaf`));
			apply_ret(bdds.F, this.memo_and_not);
		}
		const yn = getnode(y).clone();
		if (nleaf(yn)) {
			const r = ntrueleaf(yn) ? bdds.F : x;
			DBG(__and_not(`/and_not-${id} ${r} (${x} and not3 ${y}) yn is leaf`));
			apply_ret(r, this.memo_and_not);
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
				DBG(__and_not(`/and_not-${id} ${r} (${x} and not4 ${y})`));
				apply_ret(r, this.memo_and_not);
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
		DBG(__and_not(`/and_not-${id} ${r} (${x} and not5 ${y})`));
		apply_ret(r, this.memo_and_not);
	}

	deltail(x, h) {
		ID('deltail');
		TRC(`deltail-${id} (${x} deltail ${h})`);
//## ifdef MEMO
		const t = `${x}.${h}`;
		if (this.memo_deltail.hasOwnProperty(t)) {
			DBG(__deltail(`/deltail-${id} ${this.memo_deltail[t]} (${x}, ${h}) (memo:${t})`));
			return this.memo_deltail[t];
		}
//## endif
		if (leaf(x)) {
			DBG(__deltail(`/deltail-${id} ${x} (${x}, ${h}) leaf`));
			return x;
		}
		const n = getnode(x).clone();
		if (n.v > h) {
			const r = n.hi === bdds.F && n.lo === bdds.F ? bdds.F : bdds.T;
			DBG(__deltail(`/deltail-${id} ${r} (${x}, ${h}) (${n.v} > ${h}) n:${n.key}`));
			apply_ret(r, this.memo_deltail);
		}
		const hi = this.deltail(n.hi, h);
		const lo = this.deltail(n.lo, h);
		const r = this.add(new node(n.v, hi, lo));
		DBG(__deltail(`/deltail-${id} ${r} (${x}, ${h}) (hi: ${hi}, lo: ${lo})`));
		apply_ret(r, this.memo_deltail);
	}

	and_deltail(x, y, h) {
		ID('and_deltail');
		TRC(`and_deltail-${id} (${x} and_deltail ${y}, ${h})`);
		if (x === y) return this.deltail(x, h);
//## ifdef MEMO
		const t = `${x}.${y}.${h}`;
		if (this.memo_and_deltail.hasOwnProperty(t)) {
			DBG(__and_deltail(`/and_deltail-${id} ${this.memo_and_deltail[t]} (${x} and_deltail1 ${y}, ${h}) (memo:${t})`));
			return this.memo_and_deltail[t];
		}
//## endif
		const xn = getnode(x).clone();
		if (nleaf(xn)) {
			const r = ntrueleaf(xn) ? this.deltail(y, h) : bdds.F;
			DBG(__and_deltail(`/and_deltail-${id} ${r} (${x} and_deltail2 ${y}, ${h}) xn is leaf`));
			apply_ret(r, this.memo_and_deltail);
		}
		const yn = getnode(y).clone();
		if (nleaf(yn)) {
			const r = !ntrueleaf(yn) ? bdds.F : this.deltail(x, h);
			DBG(__and_deltail(`/and_deltail-${id} ${r} (${x} and_deltail3 ${y}, ${h}) yn is leaf`));
			apply_ret(r, this.memo_and_deltail);
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
				DBG(__and_deltail(`/and_deltail-${id} ${r} (${x} and_deltail4 ${y}, ${h})`));
				apply_ret(r, this.memo_and_deltail);
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
		DBG(__and_deltail(`/and_deltail-${id} ${r} (${x} and_deltail5 ${y}, ${h})`));
		apply_ret(r, this.memo_and_deltail);
	}

	and_many(v, from = null, to = null) {
		ID('and_many');
		TRC(`and_many-${id} (v.length:${v.length}, from: ${from}, to: ${to})`);
		from = from || 0;
		to = to || v.length;
		if (1 === (to - from)) return v[from];
		if (2 === (to - from)) return this.and(v[from], v[from+1]);
		while (leaf(v[from])) {
			if (!trueleaf(v[from])) {
				return bdds.F;
			} else {
				if (1 === (to - ++from)) {
					return v[from];
				}
			}
		}
		let t = v[from];
		const sz = v.length;
		let m = getnode(t).v;
		let b = false;
		let eq = true;
		for (let i = from + 1; i != to; ++i) {
			if (leaf(v[i])) {
				if (!trueleaf(v[i])) return bdds.F;
				continue;
			}
			const n = getnode(v[i]);
			b |= n.v != m;
			eq &= t === v[i];
			if (n.v < m) m = n.v;
		}
		if (eq) return t;
		for (let i = from; i != to; ++i) {
			if (!b || getnode(v[i]).v === m) {
				v[v.length] = leaf(v[i]) ? v[i] : getnode(v[i]).hi;
			} else {
				v[v.length] = v[i];
			}
		}
		const t1 = v.length;
		for (let i = from; i != to; ++i) {
			if (!b || getnode(v[i]).v === m) {
				v[v.length] = leaf(v[i]) ? v[i] : getnode(v[i]).lo;
			} else {
				v[v.length] = v[i];
			}
		}
		const t2 = v.length;
		const hi = this.and_many(v, sz, t1);
		const lo = this.and_many(v, t1, t2);
		return this.add(new node(m, hi, lo));
	}
	// if-then-else operator
	ite(v, t, e) {
		ID('ite');
		TRC(`ite-${id} (v:${v}, t:${t}, e:${e})`);
		const x = getnode(t);
		const y = getnode(e);
		DBG(__ite(`-ite-${id} (x:${x.key}, y:${y.key})`));
		if ((nleaf(x) || v < x.v)
		&&  (nleaf(y) || v < y.v)) {
			DBG(__ite(`-ite-${id} leafs`));
			const n = new node(v + 1, t, e);
			const r = this.add(n);
			DBG(__ite(`/ite1-${id} (v:${v}, t:${t} ${x.key}, e:${e} ${y.key}) = ${r} (${n.key})`));
			return r;
		}
		const lo = this.and(from_bit(v, false), e);
		DBG(__ite(`-ite-${id} lo: ${lo}`));
		const hi = this.and(from_bit(v, true), t);
		DBG(__ite(`-ite-${id} hi: ${hi}`));
		const r = this.or(hi, lo);
		DBG(__ite(`/ite2-${id} (v:${v}, t:${t} (${x.key}), e:${e}) (${y.key}) = ${r} (hi:${hi}, lo:${lo})`));
		return r;
	}

	permute(x, m) {
		ID_TRC('permute');
		DBG(__permute(`permute-${id} (${x} permute ${m.join(',')})`));
//## ifdef MEMO
		const t = `${x}.${m.join(',')}`;
		if (this.memo_permute.hasOwnProperty(t)) {
			DBG(__permute(`/permute-${id} ${this.memo_permute[t]} (${x} permute1 ${m.join(',')}) (memo:${t})`));
			return this.memo_permute[t];
		}
//## endif
		if (leaf(x)) {
			DBG(__permute(`/permute(${id}) = ${x} (${x} permute2 ${m.join(',')}) x is leaf`));
			return x;
		}
		const n = getnode(x);
		const lo = this.permute(n.lo, m);
		DBG(__permute(`-permute-${id} lo: ${lo}`));
		const hi = this.permute(n.hi, m);
		DBG(__permute(`-permute-${id} hi: ${hi}`));
		const r = this.ite(m[n.v-1], hi, lo);
		DBG(__permute(`/permute-${id} = ${r} (${x} permute3 ${m.join(',')}) hi: ${hi}, lo: ${lo}, n.v:${n.v}, m[n.v-1]:${m[n.v-1]}`));
		apply_ret(r, this.memo_permute);
	}

	memos_clear() {
//## ifdef MEMO
		this.memo_and = {};
		this.memo_and_not = {};
		this.memo_or = {};
		this.memo_permute = {};
		this.memo_and_ex = {};
		this.memo_and_not_ex = {};
		this.memo_deltail = {};
		this.memo_and_deltail = {};
		this.memo_ex = {};
//## endif
	}
}

module.exports = { node, bdds };
