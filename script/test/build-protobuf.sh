#!/bin/bash
export LLVM_COMPILER=clang

CC=wllvm
CXX=wllvm++
script_dir=$(cd `dirname $0`;pwd)
source $script_dir/extract.sh

if [ "$1" = "clean" ]; then
    make clean
    exit
fi
git submodule update --init --recursive
./autogen.sh
CC=wllvm CXX=wllvm++ ./configure
make -j 8

# "extract_bitcode"
# find . -type f -size +1M -size -100M | xargs file | grep "ELF\|current ar archive" | awk '{print $1}'| tr -d ':' | grep -v "\.o$" >exec.txt
# cat exec.txt | grep -v "\.a$" | xargs -I '{}' extract-bc '{}' 2>error.txt
# cat exec.txt | grep "\.a$" | xargs -I '{}' extract-bc -b '{}' 2>>error.txt
# find . -name "*.bc" -size +1M -size -100M ! -name "*.o.bc" | xargs du -h | sort -h > bc-list.txt
echo "===extract bitcode==="
extract .
