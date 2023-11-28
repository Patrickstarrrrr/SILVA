#!/bin/env python3

import os
import sys
import shutil
import subprocess

# nameToPro={
#    'clang':'llvm-project',   
#    'omnetpp':'omnetpp',        
#    'protobuf':'protobuf',   
#    'make':'make',   
#    'gcc':'gcc' 
# }
proToUrl={
   'llvm-project':'https://github.com/llvm/llvm-project.git',   
   'omnetpp':'https://github.com/omnetpp/omnetpp.git',        
   'protobuf':'https://github.com/protocolbuffers/protobuf.git',   
   'make':'https://github.com/mirror/make.git',   
   'gcc':'https://github.com/gcc-mirror/gcc.git'     
}
if len(sys.argv) > 1:
    proName=sys.argv[1]
else:
    print("You should select a 'name' for the first argument")
    exit()

cwd = os.getcwd()  #获取当前路径
proOld=os.path.join(cwd,proName+"-old")
proNew=os.path.join(cwd,proName+"-new")

if os.path.exists(proOld):
    shutil.rmtree(proOld)
if os.path.exists(proNew):
    shutil.rmtree(proNew)
       
run_cmd=";".join([
    "git clone "+proToUrl[proName],
    "cp -r {0} {0}-old && mv {0} {0}-new".format(proName)
    ])  

exit_code=subprocess.call(run_cmd,shell=True)