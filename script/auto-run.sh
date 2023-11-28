#!/bin/bash

ROOT="/home/lry/projects/IS-VFA"
BIN_DIR="$ROOT/Release-build-dev/bin"
cur_time=$(date "+%Y.%m.%d_%Hh-%Mm")

# array=($ROOT/benchmark/omnetpps)
exe_cmd="execute.py -p perf-func -td $cur_time -cmp-mssa -cmp-uvalue"
# exe_cmd="execute.py -p perf-func -td $cur_time -dump-mssa -cmp-leak -cmp-uvalue"
# exe_cmd="execute.py -p function -op compare -td 2022.12.23_01h-16m -cmp-uvalue"

# cd /home/lry/projects/IS-VFA/benchmark/omnetpp/test
# # full old
# $BIN_DIR/wpa --ander /home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-old-f4e499883/lib/libopplayout_dbg.so.bc --write-ander=beforepts.txt --write-consg=beforeconsg.txt --write-callgraph=beforecg.dat --write-mssa=mssa_serial_old.dat -svfg
# # inc
# $BIN_DIR/wpa --irdiff --sourcediff=sourceDiff.txt --beforecpp=/home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-old-f4e499883/src --aftercpp=/home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-new-700c940b5/src --diffresult=result.txt --read-ander=beforepts.txt --read-consg=beforeconsg.txt --write-ander=incpts.txt --write-ander-fs=incpts_fs.txt --write-consg=incconsg.txt --iander -svfg -incfs --read-callgraph=/Users/jiayi/Downloads/omnetpp-net/beforecg.dat --write-mssa=mssa_serial_inc.dat --read-mssa=mssa_serial_old.dat -ptr-only-svfg /home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-old-f4e499883/lib/libopplayout_dbg.so.bc /home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-new-700c940b5/lib/libopplayout_dbg.so.bc
# # full new
# $BIN_DIR/wpa --fspta /home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-new-700c940b5/lib/libopplayout_dbg.so.bc --write-ander=afterpts.txt --write-consg=afterconsg.txt --write-ander-fs=afterpts_fs.txt
# # check
# $BIN_DIR/inccheck -checkpts -ptsfile1=incpts_fs.txt -ptsfile2=afterpts_fs.txt -consg1=incconsg.txt -consg2=afterconsg.txt /home/lry/projects/IS-VFA/benchmark/omnetpp/omnetpp-new-700c940b5/lib/libopplayout_dbg.so.bc

# cd $ROOT/benchmark/omnetpp
# if [ "$1" == "prebuild" ]; then
#     echo "---build omnetpp---"
#     cd omnetpp-old && git checkout -f dbbea3f30
#     build-omnetpp.sh
#     cd ../omnetpp-new && git checkout -f 54b6912ad
#     build-omnetpp.sh
#     cd ..
# fi
# $exe_cmd

cd $ROOT/compile/clang/mnt-clang
if [ "$1" == "prebuild" ]; then
    echo "---build clang---"  
    cd $ROOT/compile/clang/llvm-project-old && git checkout -f c5d012341
    build-llvm-clang.sh c5d012341
    cd $ROOT/compile/clang/llvm-project-new && git checkout -f c52516819
    build-llvm-clang.sh c52516819
    cd $ROOT/compile/clang/mnt-clang      
fi
# execute.py -p function -td 2023.02.15_20h-37m -cmp-leak -cmp-uvalue
$exe_cmd

# cd $ROOT/benchmark/protobuf
# if [ "$1" == "prebuild" ]; then
#     echo "---build protobuf---"  
#     cd protobuf-old && git checkout -f a3e558744
#     build-protobuf.sh
#     cd ../protobuf-new && git checkout -f 1473d7462
#     build-protobuf.sh
#     cd ..  
# fi
# $exe_cmd

# cd $ROOT/benchmark/gcc
# # if [ "$1" == "prebuild" ]; then
# #     echo "---build gcc---"  
# #     cd gcc-old && git checkout -f a044c9d2597
# #     build-gcc.sh a044c9d2597
# #     cd ../gcc-new && git checkout -f 079add3ad39
# #     build-protobuf.sh 079add3ad39
# #     cd ..  
# # fi
# # cd gcc-old && git checkout -f 5c0d171f67d
# # cd ../gcc-new && git checkout -f 6f46d14d498
# # cd .. 
# $exe_cmd

# cd $ROOT/benchmark/make
# echo "test make"
# # cd make-old && git checkout -f cf78e65fda
# # build-make.sh
# # cd ../make-new && git checkout -f 8064aee4f9
# # build-make.sh
# # cd ..
# $exe_cmd

# cd $ROOT/benchmark/make/make-v1
# echo "test make-v1"
# # cd make-old && git checkout -f c46b5a9e0e
# # build-make.sh
# # cd ../make-new && git checkout -f 6f8da5f4b8
# # build-make.sh
# # cd ..
# $exe_cmd


# for path in ${array[@]}
# do
#     echo $path
# done