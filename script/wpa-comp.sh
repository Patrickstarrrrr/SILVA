#!/bin/bash
if [ -z "$1" ]; then
    test_dir=test
else
    test_dir=$1
fi
execute.py -p perform --test-dir $test_dir
execute.py -p function --test-dir $test_dir -cmp-mssa