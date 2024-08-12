## SILVA: A Scalable Incremental Layered Sparse Value-Flow Analysis

SILVA is an incremental layered sparse value-flow analysis that scales to large, real-world programs efficiently. 

## Get Started

### Set Up

```
sudo apt install cmake gcc g++ libtinfo5 libz-dev libzstd-dev zip wget libncurses5-dev ##(If running on Ubuntu 20.04)

git clone https://github.com/Patrickstarrrrr/SILVA.git
cd SILVA
source ./build.sh
```

### Example

To perform incremental analysis, you need to provide two directories containing the source code of the program before and after modifications (beforeDir & afterDir), as well as the two versions of the binary code files compiled from the source code (before.bc & after.bc).

Run the following command to perform incremental pointer analysis：
```
# wpa \
    -sourcediff=path/to/source/diff/file \
    -beforecpp=path/to/old/version/dir \
    -aftercpp=path/to/new/version/dir \
    -iander \
    -is-new=true \
    -irdiff \
    -relapath=true \
    path/to/new/version/bc/file/newVersion.bc >
```

Run the following command to perform incremental value-flow analysis：
```
# wpa \
    -sourcediff=path/to/source/diff/file \
    -beforecpp=path/to/old/version/dir \
    -aftercpp=path/to/new/version/dir \
    -iander \
    -svfg
    -is-new=true \
    -irdiff \
    -relapath=true \
    path/to/new/version/bc/file/newVersion.bc
```

