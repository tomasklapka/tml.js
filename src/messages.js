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

const m = {}; module.exports = m;
m.err_proof         = `proof extraction yet unsupported for programs with negation or deletion.\n`;
m.dot_expected      = "'.' expected.\n";
m.sep_expected      = "Term or ':-' or '.' expected.\n";
m.unmatched_quotes  = "Unmatched \"\n";
m.err_inrel         = "Unable to read the input relation symbol.\n";
m.err_src           = "Unable to read src file.\n";
m.err_dst           = "Unable to read dst file.\n";
m.err_quotes        = "expected \".\n";
m.err_dots          = "two consecutive dots, or dot in beginning of document.\n";
m.err_quote         = "' should come before and after a single character only.\n";
m.err_fname         = "malformed filename.\n";
m.err_directive_arg = "invalid directive argument.\n";
m.err_escape        = "invalid escaped character\n";
m.err_int           = "malformed int.\n";
m.err_lex           = "lexer error (please report as a bug).\n";
m.err_parse         = "parser error (please report as a bug).\n";
m.err_chr           = "unexpected character.\n";
m.err_body          = "rules' body expected.\n";
m.err_term_or_dot   = "term or dot expected.\n";
m.err_close_curly   = "'}' expected.\n";
m.err_fnf           = "file not found.\n";
m.err_sym_digit     = "symbol name cannot begin with a digit\n";
m.err_goal_arity    = "goal arity larger than the program's\n";
m.err_goal_sym      = "goal symbol not appearing in program.\n";
m.err_null_in_head  = "'null' not allowed to appear in the head of positive rules.\n";
m.err_null          = "'null' can appear only by itself on the rhs.\n";
m.err_rule_dir_prod_expected = "rule or production or directive expected.\n";
m.err_prod          = "production's body expected.\n";
m.err_paren         = "unbalanced parenthesis.\n";
