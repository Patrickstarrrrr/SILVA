#!/bin/bash
export LLVM_COMPILER=clang

CC=wllvm
CXX=wllvm++
script_dir=$(cd `dirname $0`;pwd)
source $script_dir/extract.sh
gcc_root=$(pwd)

# if [ -n "$1" ]; then
#     gcc_root=$1
# else
#     gcc_root=../gcc
# fi
if [ -n "$1" ]; then
    build_name=ben-build-$1
else
    build_name=ben-build
fi

build_dir=../bitcode/$build_name
mkdir -p $build_dir
cd $build_dir
echo "build directory is $build_dir"
CC=wllvm CXX=wllvm++ $gcc_root/configure --prefix=/opt/gcc --enable-languages=all --disable-bootstrap --disable-multilib
make -j 8

# mkdir -p cur-install
# make DESTDIR=$(pwd)/cur-install install

echo "===extract bitcode==="
extract .
echo "gcc root $gcc_root"
cd $gcc_root