// Author: Tomáš Klapka <tomas@klapka.cz>

// int wrapper for native BigInt or bn.js library

"use strict";

// BigInt is a new native type in JS.
// Currently its supported only in Node and Chrom(e/ium)
// see https://developers.google.com/web/updates/2018/05/bigint
//
// For environments without native support we use bn.js library
// https://github.com/indutny/bn.js

// detect native BigInt
const native = typeof BigInt === "function";

let int_wrapper;
if (native) {
  // native BigInt
  class int_BigInt {
    constructor(n) { this.n = BigInt(n); }
    gt(b)          { return this.n > b; }
    lt(b)          { return this.n < b; }
    gte(b)         { return this.n >= b; }
    lte(b)         { return this.n <= b; }
    eq(b)          { return this.n == b; }
    and(b)         { return (this.n > BigInt(0)) && (b > BigInt(0)); }
    or(b)          { return (this.n > BigInt(0)) || (b > BigInt(0)); }
    not()          { return !(this.n > BigInt(0)); }
    add(b)         { return new int_BigInt(this.n + b); }
    sub(b)         { return new int_BigInt(this.n - b); }
    mul(b)         { return new int_BigInt(this.n * b); }
    div(b)         { return new int_BigInt(this.n / b); }
    mod(b)         { return new int_BigInt(this.n % b); }
    shln(b)        { return new int_BigInt(this.n << BigInt(b)); }
    shrn(b)        { return new int_BigInt(this.n >> BigInt(b)); }
    toString()     { return this.n.toString(); }
    valueOf()      { return this.n; }
  }
  int_wrapper = int_BigInt;
} else {
  // bn.js fallback
  const BN = require('bn.js');
  class int_BN extends BN {
    and(b)  { return this.gt(new BN(0)) && (typeof(b) === 'boolean' ? b : b.gt(new BN(0))); }
    or(b)   { return this.gt(new BN(0)) || (typeof(b) === 'boolean' ? b : b.gt(new BN(0))); }
    not()   { return !this.gt(new BN(0)); }
  }
  int_wrapper = int_BN;
}

// int factory
function int(n) {
  return typeof(n) === 'number' ? new int_wrapper(n) : n;
}

module.exports = {
  int
}