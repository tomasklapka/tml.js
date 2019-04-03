rootdir = $(realpath .)/
BROWSER_DIR = ${rootdir}browser/
BROWSER_BUILD_DIR = ${BROWSER_DIR}build/
BROWSER_DEBUG_DIR = ${BROWSER_DIR}debug/
DEBUG_DIR = ${rootdir}debug/
BUILD_DIR = ${rootdir}build/
SRC_DIR = ${rootdir}src/
NODE_BIN = ${rootdir}node_modules/.bin/

CD_SRC = cd ${SRC_DIR}
CD_ROOT = cd ${rootdir}

YARN = yarn
MKDIR_P = mkdir -p

# uncommenting directives and DBG() params (JS syntax valid -> cpp syntax valid)
PRECPP = (sed 's_^//\#__g' | sed 's_DBG()//_DBG(_g')

CPPFLAGS = -P -undef -Wundef -std=c99 -nostdinc -Wtrigraphs -fdollars-in-identifiers -C
CPPBROWSERFLAGS = ${CPPFLAGS} -D BROWSER
CPPDEBUGFLAGS = ${CPPFLAGS} -D DEBUG
CPPBROWSERDEBUGFLAGS = ${CPPBROWSERFLAGS} -D DEBUG
CPP = cpp

BROWSERIFYFLAGS = -r ./browser.js:tml -d
BROWSERIFYDEBUGFLAGS = -r ./browser.debug.js:tml -d -r debug
BROWSERIFY = ${NODE_BIN}browserify

MINIFY = ${NODE_BIN}terser
EXORCIST = ${NODE_BIN}exorcist

SRC = input.js driver.js lp.js bdd.js messages.js dict.js rule.js main.js query.js
DEBUG_SRC = input.debug.js driver.debug.js lp.debug.js bdds.debug.js messages.debug.js dict.debug.js rule.debug.js main.debug.js query.debug.js
BROWSER_SRC = browser_input.js browser_driver.js browser_lp.js browser_bdd.js browser_messages.js browser_dict.js browser_rule.js browser_main.js browser_query.js
BROWSER_DEBUG_SRC = browser_input.debug.js browser_driver.debug.js browser_lp.debug.js browser_bdd.debug.js browser_messages.debug.js browser_dict.debug.js browser_rule.debug.js browser_main.debug.js browser_query.debug.js
BROWSER_FILES = tml.min.js tml.debug.min.js tml.js tml.debug.js tml.wmap.js tml.debug.wmap.js tml.map.js tml.debug.map.js

all: tml.min.js tml.debug.min.js build debug

# browser
tml.min.js: tml.js
	${MINIFY} ${BROWSER_DIR}tml.js > ${BROWSER_DIR}tml.min.js
tml.map.js: tml.js
tml.js: tml.wmap.js
	${EXORCIST} ${BROWSER_DIR}tml.map.js < ${BROWSER_DIR}tml.wmap.js > ${BROWSER_DIR}tml.js
tml.wmap.js: node_modules browser_build browser_dir
	${BROWSERIFY} ${BROWSERIFYFLAGS} > ${BROWSER_DIR}tml.wmap.js
browser_dir:
	${MKDIR_P} ${BROWSER_DIR}

# browser with debug
tml.debug.min.js: tml.debug.js
	${MINIFY} ${BROWSER_DIR}tml.debug.js > ${BROWSER_DIR}tml.debug.min.js
tml.debug.map.js: tml.debug.js
tml.debug.js: tml.debug.wmap.js
	${EXORCIST} ${BROWSER_DIR}tml.debug.map.js < ${BROWSER_DIR}tml.debug.wmap.js > ${BROWSER_DIR}tml.debug.js
tml.debug.wmap.js: node_modules browser_debug browser_dir
	${BROWSERIFY} ${BROWSERIFYDEBUGFLAGS} > ${BROWSER_DIR}tml.debug.wmap.js

# build for browser
browser_build: browser_build_dir $(BROWSER_SRC)
browser_build_dir:
		${MKDIR_P} ${BROWSER_BUILD_DIR}
browser_input.js:
	${CD_SRC} && $(PRECPP) < input.js    | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}input.js;    ${CD_ROOT}
browser_driver.js:
	${CD_SRC} && $(PRECPP) < driver.js   | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}driver.js;   ${CD_ROOT}
browser_dict.js:
	${CD_SRC} && $(PRECPP) < dict.js     | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}dict.js;     ${CD_ROOT}
browser_rule.js:
	${CD_SRC} && $(PRECPP) < rule.js     | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}rule.js;     ${CD_ROOT}
browser_lp.js:
	${CD_SRC} && $(PRECPP) < lp.js       | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}lp.js;       ${CD_ROOT}
browser_bdd.js:
	${CD_SRC} && $(PRECPP) < bdd.js      | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}bdd.js;      ${CD_ROOT}
browser_messages.js:
	${CD_SRC} && $(PRECPP) < messages.js | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}messages.js; ${CD_ROOT}
browser_main.js:
	${CD_SRC} && $(PRECPP) < main.js     | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}main.js;     ${CD_ROOT}
browser_query.js:
	${CD_SRC} && $(PRECPP) < query.js    | $(CPP) $(CPPBROWSERFLAGS) > ${BROWSER_BUILD_DIR}query.js;    ${CD_ROOT}

# debug build for browser
browser_debug: browser_debug_dir $(BROWSER_DEBUG_SRC)
browser_debug_dir:
		${MKDIR_P} ${BROWSER_DEBUG_DIR}
browser_input.debug.js:
	${CD_SRC} && $(PRECPP) < input.js    | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}input.js;    ${CD_ROOT}
browser_driver.debug.js:
	${CD_SRC} && $(PRECPP) < driver.js   | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}driver.js;   ${CD_ROOT}
browser_dict.debug.js:
	${CD_SRC} && $(PRECPP) < dict.js     | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}dict.js;     ${CD_ROOT}
browser_rule.debug.js:
	${CD_SRC} && $(PRECPP) < rule.js     | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}rule.js;     ${CD_ROOT}
browser_lp.debug.js:
	${CD_SRC} && $(PRECPP) < lp.js       | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}lp.js;       ${CD_ROOT}
browser_bdd.debug.js:
	${CD_SRC} && $(PRECPP) < bdd.js      | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}bdd.js;      ${CD_ROOT}
browser_messages.debug.js:
	${CD_SRC} && $(PRECPP) < messages.js | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}messages.js; ${CD_ROOT}
browser_main.debug.js:
	${CD_SRC} && $(PRECPP) < main.js     | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}main.js;     ${CD_ROOT}
browser_query.debug.js:
	${CD_SRC} && $(PRECPP) < query.js    | $(CPP) $(CPPBROWSERDEBUGFLAGS) > ${BROWSER_DEBUG_DIR}query.js;    ${CD_ROOT}

# build
build: build_dir $(SRC)
build_dir:
		${MKDIR_P} ${BUILD_DIR}
input.js:
	${CD_SRC} && $(PRECPP) < input.js    | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}input.js;    ${CD_ROOT}
driver.js:
	${CD_SRC} && $(PRECPP) < driver.js   | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}driver.js;   ${CD_ROOT}
dict.js:
	${CD_SRC} && $(PRECPP) < dict.js     | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}dict.js;     ${CD_ROOT}
rule.js:
	${CD_SRC} && $(PRECPP) < rule.js     | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}rule.js;     ${CD_ROOT}
lp.js:
	${CD_SRC} && $(PRECPP) < lp.js       | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}lp.js;       ${CD_ROOT}
bdd.js:
	${CD_SRC} && $(PRECPP) < bdd.js      | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}bdd.js;      ${CD_ROOT}
messages.js:
	${CD_SRC} && $(PRECPP) < messages.js | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}messages.js; ${CD_ROOT}
main.js:
	${CD_SRC} && $(PRECPP) < main.js     | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}main.js;     ${CD_ROOT}
query.js:
	${CD_SRC} && $(PRECPP) < query.js    | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}query.js;    ${CD_ROOT}

# build debug
debug: debug_dir $(DEBUG_SRC)
debug_dir:
	${MKDIR_P} ${DEBUG_DIR}
input.debug.js:
	${CD_SRC} && $(PRECPP) < input.js    | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}input.js;    ${CD_ROOT}
driver.debug.js:
	${CD_SRC} && $(PRECPP) < driver.js   | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}driver.js;   ${CD_ROOT}
dict.debug.js:
	${CD_SRC} && $(PRECPP) < dict.js     | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}dict.js;     ${CD_ROOT}
rule.debug.js:
	${CD_SRC} && $(PRECPP) < rule.js     | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}rule.js;     ${CD_ROOT}
lp.debug.js:
	${CD_SRC} && $(PRECPP) < lp.js       | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}lp.js;       ${CD_ROOT}
bdds.debug.js:
	${CD_SRC} && $(PRECPP) < bdd.js      | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}bdd.js;      ${CD_ROOT}
messages.debug.js:
	${CD_SRC} && $(PRECPP) < messages.js | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}messages.js; ${CD_ROOT}
main.debug.js:
	${CD_SRC} && $(PRECPP) < main.js     | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}main.js;     ${CD_ROOT}
query.debug.js:
	${CD_SRC} && $(PRECPP) < query.js    | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}query.js;    ${CD_ROOT}

test: build
	${YARN} mocha test

node_modules:
	${YARN}

.PHONY: all clean
clean:
	rm -rf node_modules
	cd ${BUILD_DIR} && rm -f ${SRC}; cd ..
	cd ${DEBUG_DIR} && rm -f ${SRC}; cd ..
	cd ${BROWSER_DIR} && rm -f ${BROWSER_FILES}; cd ..

