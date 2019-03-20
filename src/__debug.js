const __cout        = console.log;
const __d           = require('debug');
const __dict        = __d('tml:dict');
const __pfp         = __d('tml:pfp');
const __bdd         = __d('tml:bdd');
const __add         = __d('tml:bdd:add');
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
const __driver      = __d('tml:pfp:driver');
const __counters    = {};
const __counter     = name => {
	if (!__counters.hasOwnProperty(name)) __counters[name] = 0;
	return ++__counters[name];
}
