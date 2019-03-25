rootdir = $(realpath .)/
BROWSER_DIR = ${rootdir}browser/
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
CPPDEBUGFLAGS = ${CPPFLAGS} -D DEBUG
CPP = cpp

BROWSERIFYFLAGS = -r ./index.js:tml -d
BROWSERIFYDEBUGFLAGS = ${BROWSERIFYFLAGS} -r debug
BROWSERIFY = ${NODE_BIN}browserify

MINIFY = ${NODE_BIN}terser
EXORCIST = ${NODE_BIN}exorcist

SRC = input.js driver.js lp.js bdd.js messages.js dict.js rule.js main.js
DEBUG_SRC = input.debug.js driver.debug.js lp.debug.js bdds.debug.js messages.debug.js dict.debug.js rule.debug.js main.debug.js
BROWSER_FILES = tml.min.js tml.debug.min.js tml.js tml.debug.js tml.wmap.js tml.debug.wmap.js tml.map.js tml.debug.map.js

all: tml.min.js tml.debug.min.js

# browser
tml.min.js: tml.js
	${MINIFY} ${BROWSER_DIR}tml.js > ${BROWSER_DIR}tml.min.js
tml.map.js: tml.js
tml.js: tml.wmap.js
	${EXORCIST} ${BROWSER_DIR}tml.map.js < ${BROWSER_DIR}tml.wmap.js > ${BROWSER_DIR}tml.js
tml.wmap.js: node_modules build browser_dir
	${BROWSERIFY} ${BROWSERIFYFLAGS} > ${BROWSER_DIR}tml.wmap.js
browser_dir:
	${MKDIR_P} ${BROWSER_DIR}

# browser with debug
tml.debug.min.js: tml.debug.js
	${MINIFY} ${BROWSER_DIR}tml.debug.js > ${BROWSER_DIR}tml.debug.min.js
tml.debug.map.js: tml.debug.js
tml.debug.js: tml.debug.wmap.js
	${EXORCIST} ${BROWSER_DIR}tml.debug.map.js < ${BROWSER_DIR}tml.debug.wmap.js > ${BROWSER_DIR}tml.debug.js
tml.debug.wmap.js: node_modules debug browser_dir
	${BROWSERIFY} ${BROWSERIFYDEBUGFLAGS} > ${BROWSER_DIR}tml.debug.wmap.js

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
	${CD_SRC} && $(PRECPP) < bdd.js     | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}bdd.js;     ${CD_ROOT}
messages.js:
	${CD_SRC} && $(PRECPP) < messages.js | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}messages.js; ${CD_ROOT}
main.js:
	${CD_SRC} && $(PRECPP) < main.js     | $(CPP) $(CPPFLAGS) > ${BUILD_DIR}main.js;     ${CD_ROOT}

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
	${CD_SRC} && $(PRECPP) < bdd.js     | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}bdd.js;     ${CD_ROOT}
messages.debug.js:
	${CD_SRC} && $(PRECPP) < messages.js | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}messages.js; ${CD_ROOT}
main.debug.js:
	${CD_SRC} && $(PRECPP) < main.js     | $(CPP) $(CPPDEBUGFLAGS) > ${DEBUG_DIR}main.js;     ${CD_ROOT}

test: build
	${NODE_BIN}mocha test

node_modules:
	${YARN}

.PHONY: all clean
clean:
	rm -rf node_modules
	cd ${BUILD_DIR} && rm -f ${SRC}; cd ..
	cd ${DEBUG_DIR} && rm -f ${SRC}; cd ..
	cd ${BROWSER_DIR} && rm -f ${BROWSER_FILES}; cd ..

