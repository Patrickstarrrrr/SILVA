#!/bin/env python3
import os
import re
import sys
import argparse

scriptDir=os.path.dirname(os.path.abspath(__file__))
# sys.path.append(scriptDir)
from pack.utils import run_wpa,run_comp,testReportPath
from pack.markdown import write_markdown

perfFunc='perf-func'
perfStr='perform'
funcStr='function'
parser = argparse.ArgumentParser(description='Auto test arguments')
parser.add_argument('-p','--pattern', dest='pattern', type=str, choices=[perfFunc, perfStr, funcStr],
    help='Test pattern, eg. perform or function')
# parser.add_argument("-perform",action="store_true",help="Pattern is performance or not.")
# parser.add_argument("-function",action="store_true",help="Pattern is function or not.")
parser.add_argument('-op','--option', dest='option', type=str, default='both', 
    choices=['both', 'full-old', 'full-new', 'inc', 'compare'], help='Wpa run option')
parser.add_argument('-td','--test-dir', dest='test_dir', type=str, default='test', help='Test directory')
parser.add_argument('-wl','--worklist', dest='worklist_name', type=str, default='worklist.txt', help='Path of worklist file')
parser.add_argument('-dump-mssa','--dump-mssa',dest='dump_mssa',default='',action='store_const',const='--dump-mssa',help='Dump MSSA or not.')
parser.add_argument('-dump-svfg','--dump-svfg',dest='dump_svfg',default='',action='store_const',const='--dump-vfg',help='Dump SVFG or not.')
parser.add_argument('-leak','--leak',dest='leak',default='',action='store_const',const='-leak',help='Dump leak check or not.')
parser.add_argument('-uvalue','--uvalue',dest='uvalue',default='',action='store_const',const='-uvalue',help='Dump unused value check or not.')
parser.add_argument('-mem-par','--mem-par', dest='mem_par', type=str, default='intra-disjoint', choices=['distinct', 'intra-disjoint', 'inter-disjoint'], help='Mem partition type')
parser.add_argument('-ptr-only','--ptr-only', dest='ptr_only',default='',action='store_const',const='-ptr-only-svfg',help="build ptr only svfg or not.")
parser.add_argument('-opt-svfg','--opt-svfg', dest='opt_svfg',default='',action='store_const',const='-wpa-opt-svfg',help="build opt svfg or not.")
parser.add_argument('-fs','--flow-sensitive',dest='flow_sensitive',action='store_true',help='Flow sensitive pta.')
parser.add_argument('-cmp-pts',dest='cmp_pts',action='store_true',help='Compare pts or not.')
parser.add_argument('-cmp-mssa',dest='cmp_mssa',action='store_true',help='Compare mssa or not.')
parser.add_argument('-cmp-leak',dest='cmp_leak',action='store_true',help='Compare leak check output or not.')
parser.add_argument('-cmp-uvalue',dest='cmp_uvalue',action='store_true',help='Compare unused value check output or not.')
parser.add_argument('-to-md',dest='to_md',action='store_true',help='Collect SVFG pictures into markdown.')
parser.add_argument('-chty', dest='change_type', type=str, default='insert', choices=['insert', 'delete'], help='Code change type, eg. insert or delete')
# parser.add_argument('-opt-svfg','--opt-svfg', dest='opt_svfg',default='',action='store_const',const='-wpa-opt-svfg',help="Build opt svfg or not.")
# parser.add_argument('--arg-list',dest='arg_list', type=str, nargs='*',default=[], help='WPA arguments list')
args = parser.parse_args()

def perform(args,line):
    ret=True
    print("performance test for "+line) 
    if args.option=="both":
        ret&=run_wpa(args,"full-old",line)
        ret&=run_wpa(args,"inc",line)
    elif args.option!="compare":
        ret&=run_wpa(args,args.option,line)
    else:
        print("option error in performance test")
    return ret

def function(args,line):
    ret=True
    print("function test for "+line)    
    if args.option=="both":            
        ret&=run_wpa(args,"full-new",line)
        ret&=run_comp(args,line)
    elif args.option=="compare":
        ret&=run_comp(args,line)
    else:
        ret&=run_wpa(args,"full-new",line)   
    return ret

if __name__ == "__main__":
    print("exe script directory: "+scriptDir)  
    # test_path=create_test_path(args)  
    # write_file(os.path.join(test_path,'version.txt'),isvfa_version+'\n')
    # with open(os.path.join(test_path,'version.txt'),'a') as version_file:
    #     version_file.write(isvfa_version+'\n')    
    ret=True
    if args.cmp_leak:
        args.leak='-leak'
        # args.ptr_only='-ptr-only-svfg'
        # args.opt_svfg='-wpa-opt-svfg'
    if args.cmp_uvalue:
        args.uvalue='-uvalue'
    with open(args.worklist_name,'r') as worklist:
        for line in worklist:  
            line=line.strip('\n')
            if not line or line.startswith('#'):
                continue
                   
            if args.pattern == perfFunc: 
                args.option="both"            
                args.pattern=perfStr 
                ret&=perform(args,line)
                args.pattern=funcStr
                ret&=function(args,line)   
                args.pattern=perfFunc             
            elif args.pattern == perfStr:
                ret&=perform(args,line)
            else:
                ret&=function(args,line)
    write_markdown(testReportPath,args.change_type)
    if ret:
        print("-"*6+"Congratulations! Everything is OK in %s test"%args.pattern+"-"*6)
    else:
        print("-"*6+"Unfortunately, something is wrong in %s test"%args.pattern+"-"*6)
                
                





