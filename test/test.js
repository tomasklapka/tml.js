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
// Author of Javascript rewrite: Tomáš Klapka <tomas@klapka.cz>

"use strict";

// OPTIONS:
const options = {
	memoization: true, 	// use memoization
	recursive: false 		// use non rec algos
}
const lp = require("../src/lp")(options);
const { dict } = lp;
const bdds = require("../src/bdds")(options);
const { node, bdds_base } = bdds;
const assert = require("assert");
const fixtures = require("./test_fixtures");

function clone_through_JSON(obj) {
	const json = JSON.stringify(obj);
	return JSON.parse(json);
}

// fixtures
const dict_f = function () {
	const d = new dict();
	d.get('symbol1'); d.get('symbol2'); d.get('symbol3');
	d.get('?var1'); d.get('?var2'); d.get('?var3');
	return d;
};
// helper for creating bdd
const nn = (b, varid, hi, lo) => { return b.add(new node(varid, hi, lo)); }
// mocks
class dict_m extends dict { constructor(l) { super(); this.syms = { length: l } } };
class dict_m_passthrough extends dict { get(t) { return t; } };
class bdds_m extends bdds {
	bdd_or(x, y) { return bdds_m.apply_or(this, x, this, y); }
	bdd_and(x, y) { return bdds_m.apply_and(this, x, this, y); }
	bdd_and_not(x, y) { return bdds_m.apply_and_not(this, x, this, y); }
	static apply_or(...a) { return [...a]; }
	static apply_and(...a) { return [...a]; }
	static apply_and_not(...a) { return [...a]; }
	add(n) { return n; }
}

// specs
describe('dict', function() {
	it('should have static getter pad returning 0', function() {
		assert.strictEqual(dict.pad, 0);
	});
	it('should initialize syms array by pad element', function() {
		const d = new dict();
		assert.strictEqual(d.get(0), dict.pad);
		assert.strictEqual(d.nsyms, 1);
	});
	describe('get() should', function() {
		it('save a new variable and retrievewhen called again', function() {
			const d = dict_f();
			assert.strictEqual(d.get('?var1'), -1);
			assert.strictEqual(d.get('?var2'), -2);
			assert.strictEqual(d.get('?var3'), -3);
			assert.strictEqual(d.get('?var4'), -4);
			assert.strictEqual(d.get('?var4'), -4);
			assert.strictEqual(d.get('?var5'), -5);
			assert.strictEqual(d.get('?var5'), -5);
		});
		it('save a new symbol and retrievewhen called again', function() {
			const d = dict_f();
			assert.strictEqual(d.get('symbol1'), 1);
			assert.strictEqual(d.get('symbol2'), 2);
			assert.strictEqual(d.get('symbol3'), 3);
			assert.strictEqual(d.get('symbol4'), 4);
			assert.strictEqual(d.get('symbol4'), 4);
			assert.strictEqual(d.get('symbol5'), 5);
			assert.strictEqual(d.get('symbol5'), 5);
		});
		it('return symbol by id', function() {
			const d = dict_f();
			assert.strictEqual(d.get(0), dict.pad);
			assert.strictEqual(d.get(1), 'symbol1');
			assert.strictEqual(d.get(2), 'symbol2');
			assert.strictEqual(d.get(3), 'symbol3');
		});
	});
	it('nsyms getter should return number of symbols', function() {
		const d = dict_f();
		assert.strictEqual(d.nsyms, 4);
		d.get('symbol4');
		assert.strictEqual(d.nsyms, 5);
		d.get('?var4');
		assert.strictEqual(d.nsyms, 5);
		d.get('symbol5');
		assert.strictEqual(d.nsyms, 6);
		assert.strictEqual(new dict().nsyms, 1);
		assert.strictEqual(new dict_m(100).nsyms, 100);
		assert.strictEqual(new dict_m(4294967295).nsyms, 4294967295);
	});
	it('bits getter should return bit size of a dict = 32 - clz32(number of symbols)', function() {
		const d = dict_f();
		assert.strictEqual(d.bits, 3);
		d.get('symbol4');
		assert.strictEqual(d.bits, 3);
		d.get('symbol5');
		assert.strictEqual(d.bits, 3);
		assert.strictEqual(new dict_m(1).bits, 1);
		assert.strictEqual(new dict_m(2).bits, 2);
		assert.strictEqual(new dict_m(3).bits, 2);
		assert.strictEqual(new dict_m(7).bits, 3);
		assert.strictEqual(new dict_m(8).bits, 4);
		assert.strictEqual(new dict_m(15).bits, 4);
		assert.strictEqual(new dict_m(16).bits, 5);
		assert.strictEqual(new dict_m(4294967295).bits, 32);
	});
});
describe("node", function () {
	it("key getter should return node's unique key", function () {
		assert.strictEqual(new node(0, 0, 0).key, '0:0/0');
		assert.strictEqual(new node(1, 0, 1).key, '1:0/1');
		assert.strictEqual(new node(5, 1, 0).key, '5:1/0');
		assert.strictEqual(new node(4294967295, 0, 0).key, '4294967295:0/0');
		assert.strictEqual(new node(0, 4294967295, 0).key, '0:4294967295/0');
		assert.strictEqual(new node(0, 0, 4294967295).key, '0:0/4294967295');
		assert.strictEqual(new node(0, -4294967295, 0).key, '0:-4294967295/0');
		assert.strictEqual(new node(0, 0, -4294967295).key, '0:0/-4294967295');
	})
});
describe("bdds_base", function () {
	it("should have static F = 0 and T = 0 getters", function () {
		assert.strictEqual(bdds_base.F, 0);
		assert.strictEqual(bdds_base.T, 1);
	});
	it("should correctly be initialized", function () {
		const b = new bdds_base(0);
		assert.strictEqual(b.root, 0);
		assert.strictEqual(b.maxbdd, 0);
		assert.strictEqual(b.dim, 1);
		assert.strictEqual(b.nvars, 0);
		assert.deepStrictEqual(b.M['0:0/0'], 0);
		assert.deepStrictEqual(b.M['0:1/1'], 1);

	});
	it("should have length getter", function () {
		const b = new bdds_base();
		assert.strictEqual(b.length, 2);
		b.add_nocheck(new node(100, 42, 24));
		assert.strictEqual(b.length, 3);
		b.add_nocheck(new node(4294967295, -42, 24));
		assert.strictEqual(b.length, 4);
	});
	it("setpow() sets new pow", function () {
		const b = new bdds_base();
		assert.strictEqual(b.dim, 1);
		assert.strictEqual(b.root, 0);
		assert.strictEqual(b.maxbdd, 0);
		b.setpow(10, 2, 2);
		assert.strictEqual(b.dim, 2);
		assert.strictEqual(b.root, 10);
		assert.strictEqual(b.maxbdd, 65536);
		b.setpow(4294967296, 3, 4);
		assert.strictEqual(b.dim, 3);
		assert.strictEqual(b.root, 4294967296);
		assert.strictEqual(b.maxbdd, 256);
		b.setpow(0, 1, 8);
		assert.strictEqual(b.maxbdd, 16);
		b.setpow(0, 1, 16);
		assert.strictEqual(b.maxbdd, 4);
	});
	it("add_nocheck() should add new node withouth checking", function () {
		const b = new bdds_base();
		b.add_nocheck(new node(100, 42, 24));
		assert.strictEqual(b.length, 3);
		b.add_nocheck(new node(4294967295, -42, 24));
		assert.strictEqual(b.length, 4);
		assert.deepStrictEqual(b.M['0:0/0'], 0);
		assert.deepStrictEqual(b.M['0:1/1'], 1);
		assert.deepStrictEqual(b.M['100:42/24'], 2);
		assert.deepStrictEqual(b.M['4294967295:-42/24'], 3);
	
	});
	it("add() should add new node", function () {
		const b = new bdds_base(4294967295);
		assert.strictEqual(b.add(new node(0, 0, 0)), 0);
		assert.strictEqual(b.add(new node(0, 1, 1)), 1);
		assert.strictEqual(b.add(new node(4, 0, 1)), 2);
		assert.strictEqual(b.add(new node(4, 0, 1)), 2);
		assert.strictEqual(b.add(new node(5, 1, 0)), 3);
		assert.strictEqual(b.add(new node(5, 1, 0)), 3);
		assert.strictEqual(b.add(new node(4294967295, 1, 0)), 4);
		assert.strictEqual(b.length, 5);
		assert.deepStrictEqual(b.M['0:0/0'], 0);
		assert.deepStrictEqual(b.M['0:1/1'], 1);
		assert.deepStrictEqual(b.M['4:0/1'], 2);
		assert.deepStrictEqual(b.M['5:1/0'], 3);
		assert.deepStrictEqual(b.M['4294967295:1/0'], 4);

		assert.throws(() => b.add(new node(4294967296, 1, 0)), /^Error: Node id too big.$/);
	});
	describe("getnode()", function() {
		it("should return node by id (dim=1)", function () {
			const b = new bdds_base(4294967295);
			b.add(new node(4, 0, 1));
			b.add(new node(5, 1, 0));
			b.add(new node(4294967295, 1, 0));
			assert.strictEqual(b.getnode(0).key, '0:0/0');
			assert.strictEqual(b.getnode(1).key, '0:1/1');
			assert.strictEqual(b.getnode(2).key, '4:0/1');
			assert.strictEqual(b.getnode(3).key, '5:1/0');
			assert.strictEqual(b.getnode(4).key, '4294967295:1/0');
		});
		it("should return node by id (dim>1)");
	});
	describe("leaf()", function () {
		it("should return true if node (by id) is leaf", function () {
			assert.strictEqual(bdds_base.leaf(new node(0, 0, 0)), true);
			assert.strictEqual(bdds_base.leaf(new node(0, 1, 1)), true);
		});
		it("should return true if node (by id) is leaf", function () {
			assert.strictEqual(bdds_base.leaf(0), true);
			assert.strictEqual(bdds_base.leaf(1), true);
		});
		it("should return false if node (by id) isn\'t leaf", function () {
			assert.strictEqual(bdds_base.leaf(new node(1, 0, 0)), false);
			assert.strictEqual(bdds_base.leaf(new node(-1, 0, 0)), false);
			assert.strictEqual(bdds_base.leaf(new node(4294967295, 0, 0)), false);
			assert.strictEqual(bdds_base.leaf(new node(-4294967295, 0, 0)), false);
		});
		it("should return false if node (by id) isn\'t leaf", function () {
			assert.strictEqual(bdds_base.leaf(2), false);
			assert.strictEqual(bdds_base.leaf(-1), false);
			assert.strictEqual(bdds_base.leaf(4294967295), false);
			assert.strictEqual(bdds_base.leaf(-4294967295), false);
		});
	});
	describe("trueleaf()", function () {
		it("should return true if node (by id) is true leaf", function () {
			assert.strictEqual(bdds_base.trueleaf(new node(0, 1, 1)), true);
			assert.strictEqual(bdds_base.trueleaf(new node(0, 4294967295, 0)), true);
		});
		it("should return true if node (by id) is true leaf", function () {
			assert.strictEqual(bdds_base.trueleaf(1), true);
		});
		it("should return false if node (by id) isn\'t true leaf", function () {
			assert.strictEqual(bdds_base.trueleaf(new node(0, 0, 1)), false);
			assert.strictEqual(bdds_base.trueleaf(new node(0, -4294967295, 1)), false);
			assert.strictEqual(bdds_base.trueleaf(new node(4294967295, 0, 4294967295)), false);
			assert.strictEqual(bdds_base.trueleaf(new node(-4294967295, 0, 1)), false);
		});
		it("should return false if node (by id) isn\'t true leaf", function () {
			assert.strictEqual(bdds_base.trueleaf(0), false);
			assert.strictEqual(bdds_base.trueleaf(2), false);
			assert.strictEqual(bdds_base.trueleaf(-1), false);
			assert.strictEqual(bdds_base.trueleaf(4294967295), false);
			assert.strictEqual(bdds_base.trueleaf(4294967295), false);
		});
	});
});
describe("bdds", function () {
	it("should have static F = 0 and T = 0 getters", function () {
		assert.strictEqual(bdds.F, 0);
		assert.strictEqual(bdds.T, 1);
	});
	it("should correctly be initialized", function () {
		const b = new bdds(0);
		assert.strictEqual(b.root, 0);
		assert.strictEqual(b.maxbdd, 0);
		assert.strictEqual(b.dim, 1);
		assert.strictEqual(b.nvars, 0);
		assert.deepStrictEqual(b.M['0:0/0'], 0);
		assert.deepStrictEqual(b.M['0:1/1'], 1);
		if (options.memoization) {
			const ms = [ 'memo_op', 'memo_and_ex', 'memo_copy', 'memo_permute' ];
			ms.forEach(function (m) {
				assert.deepStrictEqual(b[m], {});
			});
		}
	});
	it("bdd_or() should call static apply_or on itself", function () {
		const b = new bdds_m();
		assert.deepStrictEqual(b.bdd_or(0, 1), [ b, 0, b, 1 ]);
		assert.deepStrictEqual(b.bdd_or(-5, 42), [ b, -5, b, 42 ]);
	});
	it("bdd_and() should call static apply_and on itself", function () {
		const b = new bdds_m();
		assert.deepStrictEqual(b.bdd_and(0, 1), [ b, 0, b, 1 ]);
		assert.deepStrictEqual(b.bdd_and(-5, 42), [ b, -5, b, 42 ]);
	});
	it("bdd_and_not() should call static apply_and_not on itself", function () {
		const b = new bdds_m();
		assert.deepStrictEqual(b.bdd_and_not(0, 1), [ b, 0, b, 1 ]);
		assert.deepStrictEqual(b.bdd_and_not(-5, 42), [ b, -5, b, 42 ]);
	});
	if (options.memoization) {
		it("memos_clear() should clear memos", function () {
			const b = new bdds_m();
			b.memo_op   = { t: 1 }; b.memo_and_ex  = { t: 2 };
			b.memo_copy = { t: 3 }; b.memo_permute = { t: 4 };
			b.memos_clear();
			assert.deepStrictEqual(b.memo_op, {});
			assert.deepStrictEqual(b.memo_and_ex, {});
			assert.deepStrictEqual(b.memo_copy, {});
			assert.deepStrictEqual(b.memo_permute, {});
		});
	}
	it("apply_and");
	it("apply_and_not");
	it("apply_or");
	it("apply_and_ex_perm");
	describe("apply()", function () {
		it("should apply existential op", function () {
			const b = new bdds(5);
			const r = new bdds(4);
			nn(b,1,
				nn(b,2,
					nn(b,3,
						nn(b,4, 0, 1),
						1),
					0),
				nn(b,2,
					nn(b,4,
						0,
						nn(b,5,
							1,
							nn(b,0, 0, 0))),
					2));
			const s = [ true, false, true, false, true ];
			let act;
			act = bdds.apply_ex(b, 0, r, s); assert.strictEqual(act, 0);
			act = bdds.apply_ex(b, 1, r, s); assert.strictEqual(act, 1);
			act = bdds.apply_ex(b, 2, r, s); assert.strictEqual(act, 2);
			act = bdds.apply_ex(b, 3, r, s); assert.strictEqual(act, 1);
			act = bdds.apply_ex(b, 4, r, s); assert.strictEqual(act, 1);
		});
	});
	describe("sat()", function () {
		it("...");
	});
	it("allsat()");
	it("ite()");
	it("permute()");
	it("copy()");
	describe("from_bit()", function () {
		it("adds node with high=true and low=false if value is true", function () {
			const b = new bdds_m();
			assert.deepStrictEqual(b.from_bit(0, true).key, '1:1/0');
			assert.deepStrictEqual(b.from_bit(1, true).key, '2:1/0');
			assert.deepStrictEqual(b.from_bit(4294967294, true).key, '4294967295:1/0');
		});
		it("adds node with high=false and low=true if value is false", function () {
			const b = new bdds_m();
			assert.deepStrictEqual(b.from_bit(0, false).key, '1:0/1');
			assert.deepStrictEqual(b.from_bit(1, false).key, '2:0/1');
			assert.deepStrictEqual(b.from_bit(4294967294, false).key, '4294967295:0/1');
		});
	});
	it("from_eq");
	describe("from_bits()", function () {
		it("from_bits");
	});
});
describe("lp", function() {
	it("should initialize correctly", function () {
		const p = new lp();
		assert.strictEqual(p._id, 1);
		assert.strictEqual(p.db, bdds_base.F);
		assert.strictEqual(p.d instanceof dict, true);
		assert.deepStrictEqual(p.rules, []);
	});
	describe("str_read()", function() {
		it("should throw identifier expected", function () {
			const p = new lp(); const s = {};
			function identifier_expected() {
				assert.throws(() => p.str_read(s), /^Error: Identifier expected$/);
			}
			s.s = '';  identifier_expected();
			s.s = ' '; identifier_expected();
			s.s = '.'; identifier_expected();
			s.s = ':'; identifier_expected();
			s.s = '?'; identifier_expected();
		});
		it("should parse symbols", function () {
			const p = new lp(); p.d = new dict_m_passthrough(); const s = {};
			s.s = 'a symbol ';
			assert.strictEqual(p.str_read(s), 'a');
			assert.strictEqual(s.s, 'symbol ');
			assert.strictEqual(p.str_read(s), 'symbol');
			assert.strictEqual(s.s, '');
		});
		it("should parse variables", function () {
			const p = new lp(); p.d = new dict_m_passthrough(); const s = {};
			s.s = ' ?variable ?x ';
			assert.strictEqual(p.str_read(s), '?variable');
			assert.strictEqual(s.s, '?x ');
			assert.strictEqual(p.str_read(s), '?x');
			assert.strictEqual(s.s, '');
		});
	});
	describe("term_read()", function () {
		it("should throw term expected", function () {
			let p = new lp(); p.d = new dict_m_passthrough(); const s = {};
			function term_expected() {
				assert.throws(() => p.term_read(s), /^Error: Term expected$/);
			}
			s.s = '.'; term_expected();
			s.s = ','; term_expected();
			s.s = ':'; term_expected();
		});
		it("should throw ',', '.' or ':-' expected", function () {
			let p = new lp(); p.d = new dict_m_passthrough(); const s = {};
			function comma_dot_sep_expected() {
				assert.throws(() => p.term_read(s), /^Error: \',\', \'\.\' or \':-\' expected$/);
			}
			s.s = ' a '; comma_dot_sep_expected();
			s.s = ' ?x '; comma_dot_sep_expected();
		});
		it("should parse empty term", function () {
			let p = new lp(); const s = {};
			s.s = ' ';
			assert.deepStrictEqual(p.term_read(s), []);
			assert.strictEqual(s.s, '');
		});
		it("should parse term", function () {
			let p = new lp(); p.d = new dict_m_passthrough(); const s = {};
			s.s = 'symbol.';
			assert.deepStrictEqual(p.term_read(s), [ 1, 'symbol' ]);
			assert.strictEqual(s.s, '.');
			s.s = 'a ?x ?y.';
			assert.deepStrictEqual(p.term_read(s), [ 1, 'a', '?x', '?y' ]);
			assert.strictEqual(s.s, '.');
			s.s = '~ b ?x.';
			assert.deepStrictEqual(p.term_read(s), [ -1, 'b', '?x' ]);
			assert.strictEqual(s.s, '.');
		});
		it("should parse term (dict unmocked)", function () {
			const p = new lp(); const s = {};
			s.s = 'a ?x, b ?y, a ?y.';
			assert.deepStrictEqual(p.term_read(s), [1, 1, -1]);
			assert.strictEqual(s.s, ' b ?y, a ?y.');
			assert.deepStrictEqual(p.term_read(s), [1, 2, -2]);
			assert.strictEqual(s.s, ' a ?y.');
			assert.deepStrictEqual(p.term_read(s), [1, 1, -2]);
			assert.strictEqual(s.s, '.');
		});
	});
	describe("rule_read()", function () {
		it("should throw identifier expected", function () {
			const p = new lp();
			const s = {};
			function identifier_expected() {
				assert.throws(() => p.rule_read(s), /^Error: Identifier expected$/);
			}
			s.s = 'e x? ?y'; identifier_expected();
		});
		it("should throw term expected", function () {
			const p = new lp();
			const s = {};
			function term_expected() {
				assert.throws(() => p.rule_read(s), /^Error: Term expected$/);
			}
			s.s = '0:-1,,'; term_expected();
		});
		it("should throw separator expected", function () {
			const p = new lp();
			const s = {};
			function separator_expected() {
				assert.throws(() => p.rule_read(s), /^Error: Term or ':-' or '.' expected$/);
			}
			s.s = '0,,'; separator_expected();
		});
		it("should throw unexpected char", function () {
			const p = new lp();
			const s = {};
			function unexpected_char() {
				assert.throws(() => p.rule_read(s), /^Error: Unexpected char$/);
			}
			s.s = '0:-0:'; unexpected_char();
			s.s = '?x :- ?x :'; unexpected_char();
		});
		it("should parse empty rule", function () {
			let p = new lp(); const s = {};
			s.s = ' ';
			assert.deepStrictEqual(p.rule_read(s), []);
			assert.strictEqual(s.s, '');
		});
		it("should parse rule", function () {
			let p = new lp(); p.d = new dict_m_passthrough(); const s = {};
			s.s = 'symbol. e 1 2. ~a ?x ?y.';
			assert.deepStrictEqual(p.rule_read(s), [ [ 1, 'symbol' ] ]);
			assert.strictEqual(s.s, ' e 1 2. ~a ?x ?y.');
			assert.deepStrictEqual(p.rule_read(s), [ [ 1, 'e', '1', '2' ] ]);
			assert.strictEqual(s.s, ' ~a ?x ?y.');
			assert.deepStrictEqual(p.rule_read(s), [ [ -1, 'a', '?x', '?y' ] ]);
			assert.strictEqual(s.s, '');
			s.s = 'head :- body.';
			assert.deepStrictEqual(p.rule_read(s), [ [ 1, 'body' ], [ 1, 'head' ] ]);
			assert.strictEqual(s.s, '');
			s.s = 'head :- term1, term2, term3.';
			assert.deepStrictEqual(p.rule_read(s), [
				[ 1, 'term1' ], [ 1, 'term2'], [ 1, 'term3' ], [ 1, 'head' ] ]);
			assert.strictEqual(s.s, '');
			s.s = 'e ?x ?y :- e ?x ?z, e ?z ?y.';
			assert.deepStrictEqual(p.rule_read(s), [
				[ 1, 'e', '?x', '?z' ], [ 1, 'e', '?z', '?y'], [ 1, 'e', '?x', '?y' ] ]);
			assert.strictEqual(s.s, '');
		});
		it("should parse rule (dict unmocked)", function () {
			let p = new lp(); const s = {};
			s.s = 'e ?x ?y :- e ?x ?z, e ?z ?y. a ?x :- b ?x.';
			assert.deepStrictEqual(p.rule_read(s), [
				[ 1, 1, -1, -3 ], [ 1, 1, -3, -2 ], [ 1, 1, -1, -2 ] ]);
			assert.strictEqual(s.s, ' a ?x :- b ?x.');
			assert.deepStrictEqual(p.rule_read(s), [
				[ 1, 3, -1 ], [ 1, 2, -1, ] ]);
			assert.strictEqual(s.s, '');
		});
	});
	describe("prog_read()", function () {
		it("should throw identifier expected", function () {
			const p = new lp();
			const s = {};
			function identifier_expected() {
				assert.throws(() => p.rule_read(s), /^Error: Identifier expected$/);
			}
			s.s = 'e x? ?y'; identifier_expected();
		});
		it("should throw term expected", function () {
			const p = new lp();
			let s;
			function term_expected() {
				assert.throws(() => p.prog_read(s), /^Error: Term expected$/);
			}
			s = '0:-1,,'; term_expected();
		});
		it("should throw separator expected", function () {
			const p = new lp();
			let s;
			function separator_expected() {
				assert.throws(() => p.prog_read(s), /^Error: Term or ':-' or '.' expected$/);
			}
			s = '0,,'; separator_expected();
		});
		it("should throw ',' expected", function () {
			const p = new lp();
			let s;
			function unexpected_char() {
				assert.throws(() => p.prog_read(s), /^Error: Unexpected char$/);
			}
			s = '0:-0:'; unexpected_char();
			s = '?x :- ?x :'; unexpected_char();
		});
		it("should parse empty program", function () {
			const p = new lp();
			const s = '    ';
			p.prog_read(s);
			assert.strictEqual(p.ar, 0);
			assert.strictEqual(p.db, 0);
			assert.strictEqual(p.maxw, 0);
			assert.strictEqual(p.bits, 1);
			assert.strictEqual(p.pdbs.length, 2);
			assert.strictEqual(p.pprog.length, 2);
		});
		it("should parse program", function () {
			const p = new lp();
			const s = 'symbol. ~symbol. e 1 2. e ?x ?y :- e ?x ?z, e ?z ?y.';
			p.prog_read(s);
			assert.strictEqual(p.d.get('symbol'), 1);
			assert.strictEqual(p.d.get('e'), 2);
			assert.strictEqual(p.d.get('1'), 3);
			assert.strictEqual(p.d.get('2'), 4);
			assert.strictEqual(p.d.get('?x'), -1);
			assert.strictEqual(p.d.get('?y'), -2);
			assert.strictEqual(p.d.get('?z'), -3);
			assert.strictEqual(p.pdbs.length, 77);
			assert.strictEqual(p.pprog.length, 493);
			// assert.deepStrictEqual(p.pdbs.M, fixtures.lp1_pdbs_M);
			// assert.deepStrictEqual(p.pprog.M, fixtures.lp1_pprog_M);
			assert.strictEqual(p.ar, 3);
			assert.strictEqual(p.db, 76);
			assert.strictEqual(p.maxw, 2);
			assert.strictEqual(p.bits, 3);
			// const act = clone_through_JSON(p.rules[0])
			// const exp = fixtures.lp1_rules[0];
			// assert.deepStrictEqual(act, exp);
		});
	});
	describe("step()", function () {
		it("should do a pfp step")
	});
	describe("pfp()", function () {
		it("should run steps until a fixed point");
	});
});
