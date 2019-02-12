Ongoing Javascript rewrite of [TML](https://github.com/IDNI/tau) from C++.

tml.js is used in the [TML playground](https://tml.klapka.cz).


**Nothing here is ready yet.**

Can find us on ##idni @freenode

### Building for browser:

tml.js uses browserify, exorcist (extracting source maps) and terser (minify) for bundling files.

Use `npm run-script build` to create *dist/tml.js*, *dist/tml.wmap.js* (with sourcemaps), *dist/tml.min.js* (minified) and *dist/tml.map.js* (source maps).

For a lib containing debugging output use `npm run-script build_debug` to create *dist/tml.debug.js*, etc.

### Usage:

#### Node.js

tml.js reads a TML source file from standard input:

`cat ./in | node cli`

Where *./in* is a file containing the TML logic program.

#### browser

```html
<script src="tml.js"></script>
<script type="text/javascript">
	const { lp } = require('tml');
	const p = new lp();
	p.prog_read("e 1 2. e 2 3. e 3 1. e ?x ?y :- e ?x ?z, e ?z ?y.");
	if (!p.pfp()) {
		console.log('unsat');
	} else {
		console.log(p.toString());
	}
</script>
```

### Code structure:

#### /

* **index.js** - Loader of a tml.js with stripped debugging.
* **debug.js** - Loader of a tml.js with debugging.
* **cli.js** - Command line executable.

#### /src

* **tml.js** - Loads source input and runs the pfp logic program.
* **lp.js** - Logic program. Contains classes:
  * **dict** - Symbols and variables map to unique integers (varids).
  * **rule** - P-DATALOG rule.
  * **rule_items** - Positive/negative items of a rule.
  * **lp** - Logic program. Parses source into BDDs and into rules and runs PFP steps.

* **bdds.js** - BDD structure and operations, contains classes:
  * **node** - A node in a BDD structure.
  * **bdds_base** - Base class for BDD structures.
  * **bdds_rec** - Class for BDD structure with recursive algos.
  * **op** - Wrapper class for apply operators (op_and, op_and_not, op_or, op_exists).

* **bdds\_non\_rec.js** - bdds extension with non-recursive algos (contains bugs).

#### /test:

* **test.js** - Specs. Run with `mocha` or `npm test`.
* **test_fixtures.js** - Fixtures and data for test.js tests.

### Debugging:

You can use environment variable DEBUG to turn on debugging output when using Node.js.
For debugging in browser load *dist/tml.debug.js* version of lib and use localStorage.debug.

* Use ',' separated debug workers.
* '*' works as a wildcard.
* '-' negates the selection of worker.

###### Debug workers:

* tml:parser - debug from parsing functions *_read and bdd with loaded lp
* tml:dict - dict get() calls
* tml:pfp - loop of PFP steps
* tml:pfp:rule - constructing p-datalog rule, get_heads
* tml:bdd - bdds creation and operations (but apply*)
* tml:bdd:apply - bdds apply* methods
* tml:bdd:node - node creation
* tml:bdd:leaf - leaf and trueleaf tests
* tml:bdd:parsed - displays parsed bdds serialized
* tml:bdd\_non\_rec::apply - non recursive apply* methods

###### Debug usage example:

Turn on all workers but workers matching tml:bdd\*, also turn on debug for tml:bdd:apply:

```
cat ./in | DEBUG=tml:*,-tml:bdd*,tml:bdd:apply node cli
```

Turn on debug for parser (tml:parser) and dict (tml:dict):

```
cat ./in | DEBUG=tml:parser,tml:dict tml:bdd:apply node cli
```
