Ongoing Javascript rewrite of C++ [TML](https://github.com/IDNI/tau).

**Nothing here is ready yet.**

Can find us on ##idni @freenode

### Building for browser:

tml.js uses browserify, exorcist (extracting source maps) and terser (minify) for bundling files.

Use `npm run-script build` to create *dist/tml.js*, *dist/tml.wmap.js* (with sourcemaps), *dist/tml.min.js* (minified) and *dist/tml.map.js* (source maps).

For a lib containing debugging output use `npm run-script build_debug` to create *dist/tml.debug.js*, etc.

For a lib without any dependencies (no debug, no bn.js - works only in chrom\[ium|e\]) use `npm run-script build_nolibs` to create *dist/tml.nolibs.js*, etc.

### Usage:

#### Node.js

tml.js reads a TML source file from standard input:

`cat ./in | node cli`

Where *./in* is a file containing the TML logic program.

#### browser

```html
<script src="../dist/tml.debug.js"></script>
<script>
  const { lp } = require('tml');
  const p = new lp();
  p.prog_read("e 1 2. e 2 3. e 3 1. e ?x ?y :- e ?x ?z, e ?z ?y.");
  if (!p.pfp()) { console.log('unsat'); }
</script>
```

So far the output goes to console.log.


### Code structure:

#### /

* **index.js** - Loader of a tml.js with stripped debugging.
* **index.debug.js** - Loader of a tml.js with debugging.
* **cli.js** - command line executable

#### /src

* **tml.js** - Loads source input and runs the pfp logic program.
* **lp.js** - Logic program. Contains classes:
  * **dict** - Symbols and variables map to integers (varids).
  * **rule** - P-DATALOG rule
  * **rule_items** - Positive/negative items of a rule
  * **lp** - Logic program. Parses source into BDDs and into rules and runs PFP steps.

* **bdds.js** - BDD structure and operations, contains classes:
  * **node** - A node in a BDD structure.
  * **bdds_base** - Base class for BDD structures.
  * **bdds_rec** - Class for BDD structure with recursive algos.
  * **op** - Wrapper class for apply operators.

* **bdds\_non\_rec.js** - BDDs extension with non-recursive algos.
* **int.js** - wrapper for BigInt/bn.js

#### /test:

* **test.js** - Specs. Run with `mocha` or `npm test`.
* **test_fixtures.js** - Fixtures and data for test.js tests.
* **index.html** - Testing page running TML in browser.

### Debugging:

You can use environment variable DEBUG to turn on debugging output when using Node.js.
For debugging in browser load *dist/tml.debug.js* version of lib and use localStorage.debug.

* Use ',' separated debug workers.
* '*' works as a wildcard.
* '-' negates the selection of workers.

###### Debug workers:

* tml:parser
* tml:dict
* tml:pfp
* tml:pfp:rule
* tml:bdd
* tml:bdd:node
* tml:bdd:leaf
* tml:bdd:apply
* tml:bdd\_non\_rec::apply

###### Debug usage example:

Turn on all debug but workers matching tml:bdd\*, also turn on debug for tml:bdd:apply:

```
cat ./in | DEBUG=tml:*,-tml:bdd*,tml:bdd:apply node cli
```

Turn on debug for parser (tml:parser) and dict (tml:dict):

```
cat ./in | DEBUG=tml:parser,tml:dict tml:bdd:apply node cli
```
