Ongoing Javascript rewrite of C++ [TML](https://github.com/IDNI/tau).

**Nothing here is ready yet.**

Can find us on ##idni @freenode

### Code structure:

* **tml.js** - Loads source input and runs the pfp logic program.
* **lp.js** - Logic program. Contains classes:
  * **dict** - Symbols and variables map to integers (varids).
  * **rule** - P-DATALOG rule
  * **rule_items** - Possitive/negative items of a rule
  * **lp** - Logic program. Parses source into BDDs and into rules and runs PFP steps.

* **bdds.js** - BDD structure and operations, contains classes:
  * **node** - A node in a BDD structure.
  * **bdds_base** - Base class for BDD structures.
  * **bdds_rec** - Class for BDD structure with recursive algos.
  * **op** - Wrapper class for apply operators.

* **bdds\_non\_rec.js** - BDDs extension with non-recursive algos.
* **index.js** - Just a loader of tml.js.

### Testing:

* **test.js** - Specs. Run with `mocha` or `npm test`.
* **test_fixtures.js** - Fixtures and data for test.js tests.

### Usage:

tml.js reads a TML source file from standard input:

`cat ./in | node index` (or `cat ./in | npm start`)

Where `./in` is a file containing the TML logic program.

### Debugging:

You can use environment variable DEBUG to turn on debug output.

* Use ',' separated debug tags.
* '*' works as a wildcard.
* '-' negates the selection of tag.

###### Debug tags:

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

Turn on all debug but tags matching tml:bdd*, also turn on debug for tml:bdd:apply:

```
cat ./in | DEBUG=tml:*,-tml:bdd*,tml:bdd:apply node tml
```

Turn on debug for parser (tml:parser) and dict (tml:dict):

```
cat ./in | DEBUG=tml:parser,tml:dict tml:bdd:apply node tml
```
