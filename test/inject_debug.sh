#!/bin/bash

current_dir=`pwd`
repo_dir=$current_dir/tau
if [ ! -f $repo_dir/tml.cpp ]; then
	git clone https://github.com/IDNI/tau $repo_dir
fi

# output dir
target_dir=$current_dir/tau.debug

# bdd.cpp trace fns
declare -a bdd=(
	bdd.cpp bdd_add bdd_add_nocheck bdd_or bdd_ex bdd_and bdd_and_not bdd_deltail
	bdd_and_deltail bdd_and_many bdd_ite bdd_permute sat allsat
)
# tml.cpp trace fns
declare -a tml=(
	tml.cpp from_int #from_eq from_range rule_add body from_arg fwd from_bits
)
# driver.cpp trace fns
declare -a driver=(
	driver.cpp main #driver get_rule get_term
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
	for ((i=1; i<${#fns[*]}; i++ )); do
		fn=${fns[i]}
		re='s/^.* '$fn'\(([^)]*)\)\s*\{.*$/\0\nsize_t id = ++_cnt_'$fn';'
		re=$re' DBG(wcout<<"'$fn'-"<<id<<endl);/g'   # " (\1)"<<
		sed -i -E "$re" $file
	done
	declare -a tmp=(${fns[*]:2})
	counters=$(printf "%s" "${tmp[*]/#/ = 0,\\n\\t_cnt_}");
	file_prepend $file "size_t\n\t_cnt_${fns[1]}$counters = 0;"
}

# clean target dir and copy there a code from repository directory
mkdir -p $target_dir && \
rm -rf $target_dir/* $target_dir/.git && \
cp -r $repo_dir/* $target_dir
cd $target_dir

# enable debug
sed -i -E "s/\/\/\#define DEBUG/\#define DEBUG/g" defs.h

# inject fn tracing (inc. fn counters)
inject_debug bdd[@]
inject_debug tml[@]
inject_debug driver[@]

# add headers required for debug
file_prepend bdd.cpp '#include <cstddef>\n#include <iostream>'
file_prepend driver.cpp '#include <cstddef>'
file_prepend tml.cpp '#include <cstddef>'

# make
make

# go to the stored current_dir
cd $current_dir


