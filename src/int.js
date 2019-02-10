// Author: Tomáš Klapka <tomas@klapka.cz>

"use strict";

// int wrapper for Number, native BigInt or bn.js library  (>32bits)
//
// BigInt is a new native type in JS.
// Currently its supported only in Node and Chrom(e/ium)
// see https://developers.google.com/web/updates/2018/05/bigint
//
// For environments without native support we use bn.js library
// https://github.com/indutny/bn.js

class int_Number {
	constructor(n) { this.n = n; }
	gt(b)          { return this.n > b; }
	lt(b)          { return this.n < b; }
	gte(b)         { return this.n >= b; }
	lte(b)         { return this.n <= b; }
	eq(b)          { return this.n == b; }
	and(b)         { return (this.n > 0) && (typeof(b) === 'boolean' ? b : b > 0); }
	or(b)          { return (this.n > 0) || (typeof(b) === 'boolean' ? b : b > 0); }
	not()          { return !(this.n > 0); }
	add(b)         { return new int_Number(this.n + b); }
	sub(b)         { return new int_Number(this.n - b); }
	mul(b)         { return new int_Number(this.n * b); }
	div(b)         { return new int_Number(this.n / b); }
	mod(b)         { return new int_Number(this.n % b); }
	shln(b)        { return new int_Number(this.n << b); }
	shrn(b)        { return new int_Number(this.n >> b); }
	toString()     { return this.n.toString(); }
	valueOf()      { return this.n; }
}

// native BigInt
class int_BigInt extends int_Number {
	constructor(n) { this.n = BigInt(n); }
	and(b)         { return (this.n > BigInt(0)) && (typeof(b) === 'boolean' ? b : b > BigInt(0)); }
	or(b)          { return (this.n > BigInt(0)) || (typeof(b) === 'boolean' ? b : b > BigInt(0)); }
	not()          { return !(this.n > BigInt(0)); }
	add(b)         { return new int_BigInt(this.n + b); }
	sub(b)         { return new int_BigInt(this.n - b); }
	mul(b)         { return new int_BigInt(this.n * b); }
	div(b)         { return new int_BigInt(this.n / b); }
	mod(b)         { return new int_BigInt(this.n % b); }
	shln(b)        { return new int_BigInt(this.n << BigInt(b)); }
	shrn(b)        { return new int_BigInt(this.n >> BigInt(b)); }
}

// bn.js fallback
const BN = require('bn.js');
class int_BN extends BN {
	and(b)  { return this.gt(new BN(0)) && (typeof(b) === 'boolean' ? b : b.gt(new BN(0))); }
	or(b)   { return this.gt(new BN(0)) || (typeof(b) === 'boolean' ? b : b.gt(new BN(0))); }
	not()   { return !this.gt(new BN(0)); }
}


function int(int_size = 32) {
	return function (n) {
		if (typeof(n) !== 'number') return n; // wrap only a number
		if (int_size <= 32) { // for int sizes up to 32 bits.
			return new int_Number(n); // use Number
		} // 32 should be safe even for bit shifting
		return typeof BigInt === "function" // if native BigInt available
			? new int_BigInt(n) // use native BigInt
			: new int_BN;	// use BN.js
	}
}

module.exports = int;