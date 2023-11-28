#!/bin/env bash

export LLVM_COMPILER=clang
# export CC=wllvm
# export CXX=wllvm++

script_dir=$(cd `dirname $0`;pwd)
source $script_dir/extract.sh

if [ -n "$1" ]; then
    dir_name=ben-build-$1
else
    dir_name=ben-build
fi
build_dir=../bitcode/$dir_name
echo "build directory is $build_dir"

mkdir -p $build_dir
CC=wllvm CXX=wllvm++ cmake -S llvm -B $build_dir -DLLVM_ENABLE_PROJECTS=clang -DCMAKE_BUILD_TYPE=Debug 
cmake --build $build_dir -j 8

# # 查找10M~100M之间的可执行可链接文件
# find $build_dir -type f -size +10M -size -100M | xargs file | grep "ELF\|current ar archive" | awk '{print $1}'| tr -d ':' | grep -v "\.o$" >exec.txt
# # 对非静态库文件抽取bitcode
# cat exec.txt | grep -v "\.a$" | xargs -I '{}' extract-bc '{}' 2>error.txt
# # 对静态库文件抽取bitcode
# cat exec.txt | grep "\.a$" | xargs -I '{}' extract-bc -b '{}' 2>>error.txt
# # 查找10M~100M之间的bitcode文件，将结果按照文件大小排序后放到bc-list.txt
# find $build_dir -name "*.bc" -size +10M -size -100M | grep -v "\.o\.bc" | xargs du -h | sort -h > bc-list.txt
echo "===extract bitcode==="
extract $build_dir

