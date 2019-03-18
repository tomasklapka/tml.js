#!/bin/bash

current_dir=`pwd`
repo_dir=$current_dir/tau
if [ ! -f $repo_dir/tml.cpp ]; then
	git clone https://github.com/IDNI/tau $repo_dir
fi

# output dir
target_dir=$current_dir/tau.debug

# trace fns
declare -a bdd=(
	bdd.cpp
	#bdd_add
	bdd_add_nocheck
	#bdd_or bdd_ex bdd_and bdd_and_not bdd_deltail
	#bdd_and_deltail bdd_and_many bdd_ite bdd_permute sat allsat from_int
)
declare -a lp=(
	lp.cpp
	pfp fwd rules_pad rule_pad term_pad
)
declare -a driver=(
	driver.cpp
	driver pfp prog_init directives_load get_nums get_char_builtins
	from_func get_rule get_term
)
declare -a input=(
	input.cpp
	parse file_read_text get_int_t
)
declare -a dict=(
	dict.cpp
	dict_get
)

function file_prepend() {
	declare file=$1
	declare prepend=$2
	mv $file ___$file.tmp && \
	{ 	echo -e $prepend; echo;
		cat ___$file.tmp; } > $file && \
	rm ___$file.tmp
}

function inject_debug() {
	declare -a fns=("${!1}")
	file=${fns[0]}
	prepend=$2
	echo "injecting $file"
	for ((i=1; i<${#fns[*]}; i++ )); do
		fn=${fns[i]}
		re='s/^(.*[\s\:]'$fn'\(([^)\n]*)\)\s*\{)/\1\nsize_t id = ++_cnt_'$fn';'
		re=$re' DBG(wcout<<"'$fn'-"<<id<<endl);/mg'
		#echo $re
		perl -p0e "$re" < $file > $file.tmp
		cp $file.tmp $file
		rm $file.tmp
	done
	declare -a tmp=(${fns[*]:2})
	counters=$(printf "%s" "${tmp[*]/#/ = 0,\\n\\t_cnt_}");
	file_prepend $file "${prepend}\nstatic size_t\n\t_cnt_${fns[1]}$counters = 0;"
}

# clean target dir and copy there a code from repository directory
mkdir -p $target_dir && \
rm -rf $target_dir/* $target_dir/.git && \
cp -r $repo_dir/* $target_dir
cd $target_dir

# enable debug
sed -i -E "s/\/\/\#define DEBUG/\#define DEBUG/g" defs.h

# inject fn tracing (inc. fn counters)
inject_debug bdd[@] '#include <cstddef>\n#include <iostream>\n'
inject_debug lp[@] '#include <cstddef>\n'
inject_debug driver[@] '#include <cstddef>\n'
inject_debug input[@] '#include <cstddef>\n'
inject_debug dict[@] '#include <cstddef>\n'

# make
make

# go to the stored current_dir
cd $current_dir
