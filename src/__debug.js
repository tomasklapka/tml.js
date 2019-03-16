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

const __cout        = console.log;
const __d           = require('debug');
const __dict        = __d('tml:dict');
const __pfp         = __d('tml:pfp');
const __bdd         = __d('tml:bdd');
const __add         = __d('tml:bdd:add');
const __leaf        = __d('tml:bdd:leaf');
const __or          = __d('tml:bdd:or');
const __ex          = __d('tml:bdd:ex');
const __and         = __d('tml:bdd:and');
const __deltail     = __d('tml:bdd:deltail');
const __and_deltail = __d('tml:bdd:and_deltail');
const __and_not     = __d('tml:bdd:and_not');
const __permute     = __d('tml:bdd:permute');
const __ite         = __d('tml:bdd:ite');
const __parser      = __d('tml:parser');
const __varbdd      = __d('tml:pfp:varbdd');
const __rule        = __d('tml:pfp:rule');
