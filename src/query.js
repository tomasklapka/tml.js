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

//## define getnode(x) bdd.V[(x)]

const { bdd } = require('./bdd');

function from_term(t) {
    const r = Array(t.length-1);
    const m = new Map();
    for (let n = 1; n !== t.length; ++n) {
        const e = t[n];
        if (e >= 0) r[n-1] = e+1;
        else if (m.hasOwnProperty(e)) r[n-1] = m[e];
        else m[e] = -n-1;
    }
    return r;
}

function flip(n) {
    if (nleaf(n)) return n;
    const nn = n.clone();
    if (nn.hi === bdd.T) nn.hi = bdd.F; else if (nn.hi === bdd.F) nn.hi = bdd.T;
    if (nn.lo === bdd.T) nn.lo = bdd.F; else if (nn.lo === bdd.F) nn.lo = bdd.T;
    return nn;
}

class query {
    constructor(bits, t, perm) {
        this.neg = t[0] < 0;
        this.bits = bits;
        this.nvars = t.length - 1;
        this.e = from_term(t);
        this.perm = perm;
        this.domain = this.getdom();
        this.path = [ nvars, 0 ];
        this.memo = {};
    }
    compute (x, v) {
        if (leaf(x) && (!trueleaf(x) || v === this.nvars)) return x;
        const n = this.neg ? flip(getnode(x)) : getnode(x).clone();
        if (leaf(x) || v+1 < n.v) { n.v = v+1; n.hi = x; n.lo = x; }
        if (!has(this.domain, v/bits+1))
            return bdd.ite(perm[v], this.compute(n.hi, v+1), this.compute(n.lo, v+1));
        const evbits = e[v/bits];
        if (evbits > 0)
            return this.compute(n[(evbits-1)&(1<<(bits-v%bits-1))?1:2], v+1);
        if (evbits < 0)
            return this.compute(n[this.path[(-evbits-1)*bits+v%bits]===1?1:2], v+1);
        this.path[v] = 1;
        x = this.compute(n.hi, v+1);
        this.path[v] = -1;
        return bdd.ite(this.perm[v], x, this.compute(n.lo, v+1));
    }
    getdom() {
        const r = [];
        for (let n = 0; n !== this.e.length; ++n) {
            if (this.e[n]) {
                r[r.length] = n+1;
                r[r.length] = Math.abs(this.e[n]);
            }
        }
        return r.sort();
    }
}

/*
size_t query::operator()(size_t x) {
    auto it = memo.find(x);
    if (it == memo.end()) return memo[x] = compute(x, 0);
    return it->second;
}
*/

class bdd_and_eq {
    constructor(bits, t) {
        this.bits = bits;
        this.nvars = (t.length-1)*bits;
        this.e = from_term(t);
        this.domain = this.getdom();
        this.path = [ nvars, 0 ];
        this.memo = {};
    }
    getdom() {
        const r = [];
        for (let n = 0; n !== this.e.length; ++n) {
            if (this.e[n]) {
                r[r.length] = n+1;
                r[r.length] = Math.abs(this.e[n]);
            }
        }
        return r.sort();
    }
    compute (x, v) {
        if (leaf(x) && (!trueleaf(x) || v === this.nvars)) return x;
        const n = getnode(x).clone();
        if (leaf(x) || v+1 < n.v) { n.v = v+1; n.hi = x; n.lo = x; }
        if (!has(this.domain, v/bits+1)) {
            ++v;
            return bdd.add(new node(v, this.compute(n.hi, v), this.compute(n.lo, v)));
        }
        const evbits = e[v/bits];
        if (evbits > 0)
            return (evbits-1) & (1 << (bits - v % bits - 1))
                ? bdd.add(new node(v+1, this.compute(n.hi, v+1), bdd.F))
                : bdd.add(new node(v+1, bdd.F, this.compute(n.lo, v+1)));
        if (evbits < 0)
            return this.path[(-evbits-1) * bits+v%bits] === 1
                ? bdd.add(new node(v+1, this.compute(n.hi, v+1, bdd.F))
                : bdd.add(new node(v+1, bdd.F, this.compute(n.lo, v+1))))
        this.path[v] = 1;
        x = this.compute(n.hi, v+1);
        this.path[v++] = -1;
        return bdd.add(new node(v, x, this.compute(n.lo, v)));
    }
}

/*
size_t bdd_and_eq::operator()(size_t x) {
    auto it = memo.find(x);
    if (it == memo.end()) return memo[x] = compute(x, 0);
    return it->second;
}
*/

class extents {
    constructor(bits, ar, tail, domain, glt, ggt, excl, lt, gt, succ, pred) {
        this.bits = bits;
        this.nvars = ar*bits;
        this.tail = tail;
        this.glt = glt;
        this.ggt = ggt;
        this.excl = excl.sort();
        this.lt = lt;
        this.gt = gtl
        this.succ = succ;
        this.pred = pred;
        this.domain = domain.sort();
        this.path = [ nvars, 0 ];
    }
    get_int(v) {
        let r = 0;
        const pos = (v-1) / this.bits;
        for (let n = pos * bits; n !== (pos+1)*bits; ++n) {
            if (this.path[n] === 1) r |= 1 << (bits-1-n%bits);
        }
        return r;
    }
    compute (x, v) {
        if (leaf(x) && (!trueleaf(x) || v === this.nvars+1)) return x;
        const n = getnode(x).clone();
        if (leaf(x) || v+1 < n.v) { n.v = v+1; n.hi = x; n.lo = x; }
        DBG()//if (v > this.nvars)) throw new Error("assert(v <= nvars)");
        if (!has(this.domain, v/bits+1)) {
            ++v;
            return n.hi === n.lo
                ? this.compute(n.hi, v)
                : bdd.add(new node(v, this.compute(n.hi, v), this.compute(n.lo, v)));
        }
        do {
            if (v < bits || (v % bits)) continue;
            const i = this.get_int(v);
            const t = v/bits-1;
            if ((this.glt > 0 && i >= this.glt)
            || (this.ggt > 0 && i <= this.ggt)
            || has(this.excl, i)
            || (this.gt[t] < 0 && i <= this.get_int(bits*-this.gt[t]))
            || (this.gt[t] > 0 && i <= this.gt[t])
            || (this.lt[t] < 0 && i >= this.get_int(bits*-this.lt[t]))
            || (this.lt[t] > 0 && i >= this.lt[t])
            || (this.succ[t] && i !== 1+this.get_int(bits*this.succ[t]))
            || (this.pred[t] && i+1 !== this.get_int(bits*this.pred[t])))
                return bdd.F;
        } while (0);
        this.path[v] = 1;
        x = this.compute(n.hi, v+1);
        this.path[v++] = 0;
        const y = this.compute(n.lo, v);
        return v > this.tail
            ? x === bdd.F && y === bdd.F
                ? bdd.F
                : bdd.T
            : bdd.add(new node(v, x, y));
    }
}

/*
size_t extents::operator()(size_t x) {
    auto it = memo.find(x);
    if (it == memo.end()) return memo[x] = compute(x, 0);
    return it->second;
}
*/