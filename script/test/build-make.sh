#!/bin/bash
export LLVM_COMPILER=clang

CC=wllvm
CXX=wllvm++

if [ "$1" = "clean" ]; then
    make clean # clean the build files
else
    ./bootstrap
    ./autogen.sh
    CC=wllvm CXX=wllvm++ ./configure
    make MAKE_CFLAGS= -j 8    
    extract-bc make
fi

