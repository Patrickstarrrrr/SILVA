#!/bin/env python3
import os
from pack.config import *
from pack.filesys import read_whole

class MdItem:
    msg=""
    src_old=""
    src_new=""
    svfg_svg_pic_inc=""
    svfg_bit_pic_inc=""
    svfg_svg_pic_new=""
    svfg_bit_pic_new=""
    
    def __init__(self) -> None:
        pass
    
    # def __init__(self,msg,svfg_svg_pic_inc,svfg_svg_pic_new) -> None:
    #     self.msg=msg
    #     self.svfg_svg_pic_inc=svfg_svg_pic_inc
    #     self.svfg_svg_pic_new=svfg_svg_pic_new
        
mdItem=None    
mdItemList=[]  

def set_md_item(msg,src_code,svfg_svg_pic,svfg_bit_pic,option):
    global mdItem    
    # if not mdItem:
    #     mdItem=MdItem()
    if option=="inc":
        mdItem=MdItem()
        mdItem.msg=msg
        mdItem.src_old=src_code
        mdItem.svfg_svg_pic_inc=svfg_svg_pic
        mdItem.svfg_bit_pic_inc=svfg_bit_pic
    elif option=="full-new":
        mdItem.src_new=src_code
        mdItem.svfg_svg_pic_new=svfg_svg_pic
        mdItem.svfg_bit_pic_new=svfg_bit_pic
        mdItemList.append(mdItem)

def write_markdown(out_path,change_type):
    # h2="## "
    # h3="### "
    h4="#### "  
    old_dir=os.path.basename(build_dir_old)  
    new_dir=os.path.basename(build_dir_new)  
    if change_type=="insert":
        string="## Insert\n"
        mode='w'
    else:
        string="## Delete\n"
        mode='a' 
    with open(os.path.join(out_path,'TestReport.md'),mode) as md:
        for mdItem in mdItemList:
            ll_rel_path=mdItem.msg.rsplit('.',1)[0]+".ll"
            string+="\n".join([
                "### "+os.path.basename(mdItem.msg),
                h4+"Old Code",
                "```c++",
                read_whole(mdItem.src_old)+"```",  
                "LLVM Assembly Code: %s/%s"%(old_dir,ll_rel_path),              
                "LLVM Bit Code: %s/%s"%(old_dir,mdItem.msg),              
                h4+"New Code",
                "```c++",
                read_whole(mdItem.src_new)+"```",   
                "LLVM Assembly Code: %s/%s"%(new_dir,ll_rel_path),              
                "LLVM Bit Code: %s/%s"%(new_dir,mdItem.msg),             
                h4+"Incremental SVFG",
                "relative path: "+mdItem.svfg_svg_pic_inc,
                "![SVFG](%s)"%mdItem.svfg_bit_pic_inc,
                h4+"Full New SVFG",
                "relative path: "+mdItem.svfg_svg_pic_new,
                "![SVFG](%s)"%mdItem.svfg_bit_pic_new,
            ])
            string+="\n"
        md.write(string+'\n')             
             
         