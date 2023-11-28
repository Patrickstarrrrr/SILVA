#!/bin/env python3
import os
import difflib
import filecmp
import subprocess

def dot_to_pic(dot_path,pic_path):
    type=pic_path.rsplit('.',1)[1]
    cmd="dot %s -T %s -o %s"%(dot_path,type,pic_path)
    subprocess.call(cmd,shell=True)

def get_dir_and_name(path):
    split=os.path.split(path)
    name=split[1]
    dir=os.path.basename(split[0])
    return dir,name

# 为True表示两文件相同
def cmp_files(file_path1,file_path2):
    try:
        return filecmp.cmp(file_path1, file_path2)    
    except IOError as e: 
        # 如果两边路径头文件不都存在，抛异常
        print("Error: File not found or failed to read",e) 
        return None
        # exit()
        
def read_content(file_path):
    with open(file_path) as f:
        content = f.read().splitlines(keepends=True)
    return content

def read_whole(file_path):
    with open(file_path) as f:
        content = f.read()
    return content

# 为True表示两文件相同
def diff_files(file_path1,file_path2,out_dir,msg=''):
    cmp_ret=cmp_files(file_path1,file_path2)
    if cmp_ret:
        return True
    elif cmp_ret==None:
        return False
    split1=os.path.split(file_path1)
    split2=os.path.split(file_path2)
    comp_sub_dir=os.path.split(split1[0])[1]
    name1=split1[1]
    name2=split2[1]
    html_name='diff_'+name1+msg+'.html'
    # out_comp_path=os.path.join(out_dir,comp_sub_dir)
    html_path=os.path.join(out_dir,html_name)
    # if not os.path.exists(out_comp_path):
    #     os.makedirs(out_comp_path) 
    content1=read_content(file_path1)
    content2=read_content(file_path2)
    html_diff = difflib.HtmlDiff()
    htmlcontent = html_diff.make_file(content1, content2)
    with open(html_path, 'w') as f:
        f.write(htmlcontent)
    return False  