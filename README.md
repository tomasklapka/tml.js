Ongoing Javascript rewrite of [TML](https://github.com/IDNI/tau) from C++.

tml.js is used in [TML playground](https://tml.klapka.cz) ([source](https://github.com/IDNI/tml_playground)).

Can find us on ##idni @freenode

### Building and usage:

Run `make` or `make all` to build all .

#### Node.js

Run `make build` to build library.

Command line usage: `node cli < program.tml`

Or use it as a library by requiring lib's index:
```javascript
const tmljs_path = './lib/tml.js';
const { driver } = require(tmljs_path);
const program = 'agent id007 James Bond. greetings ?surname ?firstname ?surname :- agent id007 ?firstname ?surname.';
const d = new driver(program);
if (!d.pfp()) console.log('unsat');
else console.log(d.toString());
/*
Produces output:

agent id007 James Bond.
greetings Bond James Bond.
*/
```

#### browser

Choose one of these to build browser lib:
* `make tml.min.js` - minified
* `make tml.js` - not minified
* `make tml.wmap.js` - not minified with source map

Usage:
```html
<script src="tml.js"></script>
<script type="text/javascript">
	const { driver } = require('tml');
	// ...
</script>
```

### Building debug and usage

#### Node.js debugging

Run `make debug` to build version for debugging.

Specify debug workers by using DEBUG env: `DEBUG=tml:parser,tml:dict node cli.debug < program.tml`

Library's debug entrypoint is in ./debug.js:
```javascript
const tmljs_path = './lib/tml.js/debug';
// ...
```

* Debug workers are ',' separated.
* '*' works as a wildcard.
* '-' disables the worker.

See [src/__debug.js](./src/debug.js) for the complete list of workers.

#### browser debugging

Choose:
* `make tml.debug.min.js` - minified
* `make tml.debug.js` - not minified
* `make tml.debug.wmap.js` - not minified with source map

And use browser's *localStorage.debug* for selecting workers.
