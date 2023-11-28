#!/bin/env python3
import os
import json

with open('config.json') as f:
    data = json.load(f)
  
ROOT=data['ROOT'] # root path for IS-VFA
BUILD_DIR=os.path.join(ROOT,data['BUILD_DIR'])
max_hour=data['max_hour'] # maximum run time of wpa, unit is hour

"""test path"""
OldBenROOT=data['OldBenROOT']
NewBenROOT=data['NewBenROOT']
# build directory for old project and build directory should be outside of project root!
build_dir_old=data['build_dir_old']
# build directory for new project and build directory should be outside of project root!
build_dir_new=data['build_dir_new']