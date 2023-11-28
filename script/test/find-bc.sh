#!/bin/bash

find $1 -name "*.bc" ! -name "*.o.bc" -size -100M | xargs du -h | sort -h > $1/bc-list.txt
