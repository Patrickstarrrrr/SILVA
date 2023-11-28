#!/bin/bash

extract(){
    # 查找10M~100M之间的可执行可链接文件
    find $1 -type f -size -100M | xargs file | grep "ELF\|current ar archive" | awk '{print $1}'| tr -d ':' | grep -v "\.o$" > $1/exec.txt
    # 对非静态库文件抽取bitcode
    cat $1/exec.txt | grep -v "\.a$" | xargs -I '{}' extract-bc '{}' 2>$1/error.txt
    # 对静态库文件抽取bitcode
    cat $1/exec.txt | grep "\.a$" | xargs -I '{}' extract-bc -b '{}' 2>>$1/error.txt
    # 查找10M~100M之间的bitcode文件，将结果按照文件大小排序后放到bc-list.txt
    find $1 -name "*.bc" ! -name "*.o.bc" -size -100M | xargs du -h | sort -h > $1/bc-list.txt
}

