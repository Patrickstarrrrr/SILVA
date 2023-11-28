#!/bin/env python3
import os
import re
import sys
import subprocess
import datetime
from pack.config import *
from pack.filesys import diff_files,dot_to_pic,get_dir_and_name
from pack.markdown import set_md_item

testReportPath=os.path.join(ROOT,'doc/TestReport')
cur_time=datetime.datetime.now().strftime('%Y.%m.%d-%Hh%Mm%Ss')
ret=subprocess.run('git log --oneline | head -1',stdout=subprocess.PIPE,cwd=ROOT,shell=True)
# print("ret",ret)
isvfa_version=cur_time+" "+bytes.decode(ret.stdout)

def get_substr(line):
    match_obj = re.match(r".*ben-build[^/]*/(.+)", line)
    if not match_obj:
        print("match obj is none for %s, so the whole line is used"%line)
        sub_str=line.split()[1].strip('./')
    else:
        sub_str=match_obj.group(1).strip()
    return sub_str

def create_test_path(args):
    test_path=os.path.join(args.pattern,args.test_dir)
    if not os.path.isdir(test_path):
        os.makedirs(test_path)
    test_path=os.path.abspath(test_path)
    return test_path

def create_sub_path(path,sub_str):
    sub_path=os.path.join(path,sub_str.replace("/","_")) 
    if not os.path.isdir(sub_path):
        os.mkdir(sub_path)
    return sub_path

def write_file(path,string,mode='a'):
    with open(path,mode) as file:
        file.write(string)
        
def run_wpa(args,option,line):
    print("="*6+"Run WPA %s Start"%option.upper()+"="*6)
    wpa_path=os.path.join(BUILD_DIR,"bin","wpa") # path for whole program analyse 
    test_path=create_test_path(args)
    # dump_mssa=""
    # if args.dump_mssa:
    #     dump_mssa="--dump-mssa"   
    sub_str=get_substr(line)
    print("sub str is "+sub_str)
    bc_path_old=os.path.join(build_dir_old,sub_str)
    bc_path_new=os.path.join(build_dir_new,sub_str)   
    # run_type, label = option.split('-')
    if option=="inc":
        run_type = "inc"
    else:
        run_type = "full"

    # output_name="%s-name-%s.txt"%(run_type,cur_time)
    output_name="%s-%s-name.txt"%(cur_time,option)   

    log_path=os.path.join(test_path, output_name.replace("name","log",1))
    stdout_path=os.path.join(test_path, output_name.replace("name","stdout",1))
    stderr_path=os.path.join(test_path, output_name.replace("name","stderr",1))
    
    fs=''
    leak=args.leak
    uvalue=args.uvalue
    print("run wpa "+option)
    if option=="inc":  
        if args.flow_sensitive:
            fs='--incfs' 
           
        my_cmd = " ".join([
            "/usr/bin/time -v %s --irdiff"%wpa_path,     
            "--sourcediff=sourceDiff.txt",
            "--beforecpp=%s"%OldBenROOT,
            "--aftercpp=%s"%NewBenROOT,
            "--diffresult=result.txt",
            "--read-ander=pts_old.txt",
            "--write-ander=pts_inc.txt",
            "--read-consg=consg_old.txt",
            "--write-consg=consg_inc.txt",
            "--read-callgraph=cg_old.dat",
            "--write-callgraph=cg_inc.dat",
            "--read-mssa=mssa_serial_old.dat",
            "--write-mssa=mssa_serial_inc.dat",
            "--write-ander-fs=pts_fs_inc.txt",
            "--leak-out=leak_checker_out.yml",
            "--uvalue-out=uvalue_checker_out.yml",
            args.ptr_only,args.opt_svfg,
            args.dump_mssa,args.leak,args.uvalue,
            "-iander -svfg",fs,args.dump_svfg,             
            bc_path_old,bc_path_new])            
    else:         
        run_type, label = option.split('-')
        if label=="old":  
            leak=''
            uvalue=''          
            bc_for_full=bc_path_old
        else:
            if args.flow_sensitive:
                fs='--fspta' 
            bc_for_full=bc_path_new 
        # if args.flow_sensitive and label!="old":
        #     my_cmd=" ".join([
        #         "/usr/bin/time -v %s --fspta"%wpa_path, 
        #         "--write-consg=consg_%s.txt"%label,
        #         "--write-ander-fs=pts_fs_%s.txt"%label,                         
        #         bc_for_full])       
        # else:
        #     my_cmd = " ".join([
        #         "/usr/bin/time -v %s"%wpa_path,    
        #         "--write-ander=pts_%s.txt"%label,
        #         "--write-consg=consg_%s.txt"%label,
        #         "--write-callgraph=cg_%s.dat"%label,
        #         "--write-mssa=mssa_serial_%s.dat"%label,
        #         "--leak-out=leak_checker_out.yml",
        #         "--uvalue-out=uvalue_checker_out.yml",  
        #         args.ptr_only,args.opt_svfg,              
        #         args.dump_mssa,args.dump_svfg,leak,uvalue,
        #         "-ander -svfg",
        #         bc_for_full]) 
        
        my_cmd = " ".join([
            "/usr/bin/time -v %s"%wpa_path,    
            "--write-ander=pts_%s.txt"%label,
            "--write-consg=consg_%s.txt"%label,
            "--write-callgraph=cg_%s.dat"%label,
            "--write-mssa=mssa_serial_%s.dat"%label,
            "--leak-out=leak_checker_out.yml",
            "--uvalue-out=uvalue_checker_out.yml",  
            args.ptr_only,args.opt_svfg,fs,              
            args.dump_mssa,args.dump_svfg,leak,uvalue,
            "-ander -svfg",
            bc_for_full])     
    
    test_sub_path=create_sub_path(test_path,sub_str)
        
    print("sub_path: %s\nmy_cmd:%s"%(test_sub_path,my_cmd))   
    run_cmd=";".join([
        "echo '%s' >> %s"%(line,stdout_path),
        "echo '%s' >> %s"%(line,stderr_path),
        "cd "+test_sub_path, 
        "%s 1>>%s 2>>%s"%(my_cmd,stdout_path,stderr_path)])            
        # my_cmd])            
    
    exit_code=subprocess.call(run_cmd,shell=True,timeout=max_hour*3600)
    time_file_path=os.path.join(test_sub_path,run_type+"_time.csv")
    # add information to markdown item list
    if args.to_md and option!="full-old":
        dir_and_name=get_dir_and_name(sub_str)
        src_rel_path=sub_str[sub_str.find('all_kinds'):]
        src_rel_path=src_rel_path.rsplit('.',1)[0]
        src_code_old=os.path.join(OldBenROOT,src_rel_path)
        src_code_new=os.path.join(NewBenROOT,src_rel_path)
        if option=="inc":
            suffix="_inc"
            src_code=src_code_old
        else:
            suffix="_new"
            src_code=src_code_new
        
        dot_path=os.path.join(test_sub_path,'svfg_final.dot')
        pic_dir=os.path.join(testReportPath,'images',dir_and_name[0],args.change_type)
        if not os.path.isdir(pic_dir):
            os.makedirs(pic_dir)
        svg_pic_path=os.path.join(pic_dir,dir_and_name[1]+suffix+'.svg')
        png_pic_path=os.path.join(pic_dir,dir_and_name[1]+suffix+'.png')
        dot_to_pic(dot_path,svg_pic_path)
        dot_to_pic(dot_path,png_pic_path)
        set_md_item(sub_str,src_code,os.path.relpath(svg_pic_path,testReportPath),
                    os.path.relpath(png_pic_path,testReportPath),option)
            
    total_time="-1"
    if os.path.isfile(time_file_path):        
        with open(time_file_path,'r') as time_file:
            for msg in time_file:
                if msg.startswith("Total time,"):
                    total_time=msg.split(',')[1].strip('\n')
                    break
    else:
        print(time_file_path+" is not found!")
    
    log_out = "exit code %d for %s with %s\ntotal time is %s, which is "%(
        exit_code,line,time_file_path,total_time)
    ret=exit_code==0 and total_time!="-1"
    if ret:      
        log_out+="OK"
    else:
        log_out+="failed"  
    # with open(log_path,'a') as log_file:
    #     log_file.write(log_out+"\n\n")
    write_file(log_path,log_out+"\n\n")
    print(log_out)
    print("="*6+"Run WPA %s End"%option.upper()+"="*6+"\n")
    return ret

def run_comp(args,line):
    print("="*6+"Run Compare Start"+"="*6)
    test_path=create_test_path(args)
    sub_str=get_substr(line)
    test_sub_path=create_sub_path(test_path,sub_str)    
    comp=os.path.join(BUILD_DIR,"bin","compare")
    inccheck=os.path.join(BUILD_DIR,"bin","inccheck")
    
    # path for new
    new_pts_path=os.path.join(test_sub_path,"pts_new.txt")
    new_consg_path=os.path.join(test_sub_path,"consg_new.txt")
    new_mssa_path=os.path.join(test_sub_path,"mssa_serial_new.dat")
    
    rid=os.path.dirname(test_path).rfind(args.pattern)
    perform_sub_dir=os.path.join(test_sub_path[:rid],"perform",test_sub_path[rid+len(args.pattern)+1:])
    # path for inc
    inc_pts_path=os.path.join(perform_sub_dir,"pts_inc.txt")
    inc_consg_path=os.path.join(perform_sub_dir,"consg_inc.txt")
    inc_mssa_path=os.path.join(perform_sub_dir,"mssa_serial_inc.dat") 
    
    # output_name="comp-name-%s.txt"%(cur_time)    
    bc_path_new=os.path.join(build_dir_new,sub_str)
     
    stdout_path=os.path.join(test_sub_path, "%s-comp-res.txt"%(cur_time))
    inccheckout_path=os.path.join(test_sub_path, "%s-inccheck.txt"%(cur_time))
    log_path=os.path.join(test_path, "%s-comp-log.txt"%(cur_time)) 
    stderr_path=os.path.join(test_path, "%s-comp-stderr.txt"%(cur_time)) 
    print("new-mssa: %s \ninc-mssa: %s"%(new_mssa_path,inc_mssa_path))
    
    # inccheck_cmd="time -v %s -pts-file1=%s -pts-file2=%s  %s 1>>%s 2>>%s"%(inccheck,new_mssa_path,inc_mssa_path,
    #                                                                      bc_path_new,stdout_path,stderr_path) 
    if args.flow_sensitive:
        inc_pts_path=os.path.join(perform_sub_dir,"pts_fs_inc.txt")
        new_pts_path=os.path.join(test_sub_path,"pts_fs_new.txt")
    inccheck_cmd=" ".join([
        "/usr/bin/time -v %s -checkpts"%inccheck,
        "-ptsfile1="+inc_pts_path,"-ptsfile2="+new_pts_path,
        "-consg1="+inc_consg_path,"-consg2="+new_consg_path,
        "%s 1>>%s 2>>%s"%(bc_path_new,inccheckout_path,stderr_path)
    ])
    comp_cmd=" ".join([
        "/usr/bin/time -v %s -ander"%comp,
        "--new-mssa=%s --inc-mssa=%s"%(new_mssa_path,inc_mssa_path),
        "%s 1>>%s 2>>%s"%(bc_path_new,stdout_path,stderr_path)
    ])
    # "time -v %s -ander --new-mssa=%s --inc-mssa=%s %s 1>>%s 2>>%s"%(comp,new_mssa_path,inc_mssa_path,
    #                                                                      bc_path_new,stdout_path,stderr_path) 
    ret=True
    log_msg=line+'\n'
    if args.cmp_pts:
        print(inccheck_cmd)
        write_file(stderr_path,line+'\n')
        exit_code=subprocess.call(inccheck_cmd,shell=True,timeout=max_hour*3600) 
        check_msg="compare pts exit code: %d"%exit_code 
        ret&=(exit_code==0)
        # write_file(log_path,check_msg+'\n')
        log_msg+=check_msg+' \n'        
    
    if args.cmp_mssa:
        print(comp_cmd)
        write_file(stderr_path,line+'\n')
        exit_code=subprocess.call(comp_cmd,shell=True,timeout=max_hour*3600)  
        with open(stdout_path,'r') as stdout:
            comp_res=stdout.readline().strip('\n')
        comp_msg="compare mssa exit code %d with compare mssa result that %s"%(exit_code,comp_res)   
        ret&=(exit_code==0 and comp_res.startswith('OK'))
        # write_file(log_path,'\n'.join([line,comp_msg,'\n']))
        log_msg+=comp_msg+' \n'       
    
    if args.cmp_leak:
        file1=os.path.join(test_sub_path,"leak_checker_out.yml")
        file2=os.path.join(perform_sub_dir,"leak_checker_out.yml")        
        print("compare leak checker:\n%s and %s\n"%(file1,file2))
        # try:
        #     leak_ret=diff_files(file1,file2,test_sub_path)
        # except Exception as e:
        #     leak_ret=False
        #     print(e)
        leak_ret=diff_files(file1,file2,test_sub_path,'_new_and_inc')
        leak_msg="leak checker result is "+ ("equal" if leak_ret else "not equal!")
        ret&=leak_ret
        log_msg+=leak_msg+' \n'   
    
    if args.cmp_uvalue:
        file1=os.path.join(test_sub_path,"uvalue_checker_out.yml")
        file2=os.path.join(perform_sub_dir,"uvalue_checker_out.yml")        
        print("compare uvalue checker:\n%s and %s\n"%(file1,file2))
        uvalue_ret=diff_files(file1,file2,test_sub_path,'_new_and_inc')
        uvalue_msg="uvalue checker result is "+ ("equal" if uvalue_ret else "not equal!")
        ret&=uvalue_ret
        log_msg+=uvalue_msg+' \n' 
               
    print(log_msg)
    write_file(log_path,log_msg+'\n')
    print("="*6+"Run Compare End"+"="*6+"\n")   
    return ret
