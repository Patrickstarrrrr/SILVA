#!/bin/env python3
import re
import subprocess
import datetime
from pack.config import *

worklist_name='worklist.txt'
saber='~/projects/SVF-2.3/Release-build/bin/saber'
cur_time=datetime.datetime.now().strftime('%Y.%m.%d-%Hh%Mm%Ss')

def get_substr(line):
    match_obj = re.match(r".*ben-build[^/]*/(.+)", line)
    if not match_obj:
        print("match obj is none for %s, so the whole line is used"%line)
        sub_str=line.split()[1].strip('./')
    else:
        sub_str=match_obj.group(1).strip()
    return sub_str

if __name__ == "__main__":
    # print("exe script directory: "+scriptDir)       
    
    with open(worklist_name,'r') as worklist:
        for line in worklist:  
            line=line.strip('\n')
            if not line or line.startswith('#'):
                continue
            sub_str=get_substr(line)
            print("sub str is "+sub_str)
            bc_path_old=os.path.join(build_dir_old,sub_str)
            ll_path_old=bc_path_old.rsplit('.',1)[0]+'.ll'
            stdout_path="%s-stdout.txt"%(cur_time)
            run_cmd=";".join([                
                "llvm-dis %s -o %s"%(bc_path_old,ll_path_old),                
                "/usr/bin/time -v %s -leak %s >> %s 2>&1"%(saber,bc_path_old,stdout_path),
                "wc -l %s >> %s"%(ll_path_old,stdout_path)]) 
            subprocess.call(run_cmd,shell=True)
            print('='*8+'\n\n')