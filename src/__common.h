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

#ifdef DEBUG
#  include "__debug.js"
#  define ID(x) const id = __counter(x)
#  define DBG(x) x
#  ifdef TRACE
#    define TRC(x) __cout(x)
#  else
#    define TRC(x)
#  endif
#else
#  define ID(x)
#  define DBG(x)
#  define TRC(x)
#endif
#define ID_TRC(x) ID(x); TRC(x+'-'+id)

#define msb(x) (32 - Math.clz32(x))
#define from_int_and(x, y, o, r) (r = bdd.and(r, bdd.from_int(x, y, o)))
#define from_bit(x, v) (bdd.add((v) \
	? new node((x)+1, bdds.T, bdds.F) \
	: new node((x)+1, bdds.F, bdds.T)))
#define from_eq(x, y) ((x) < (y) \
	? bdd.add(new node((x)+1, from_bit((y), true), from_bit((y), false))) \
	: bdd.add(new node((y)+1, from_bit((x), true), from_bit((x), false))))
