# Introduction
This directory contains source code for the translation from rGURA to ARBAC-URA

# Language Specification
Please refer to [examples/sample.txt](sample.txt)

# Installation
## Prerequisites
 C++ compiler supports C++11, `g++` version 5.0+ is required.

## COMPILE
Successfully test on Ubuntu 16.04 x64.
Change to the same directory of README.md, and launch these command lines:

```sh
mkdir build
cd build
cmake ..
make -j8    # assume that you want to build in parallel
```
The executable file `rGURAConverter` will be created in `build` directory.

# Usage
Please launch `rGURAConverter` with `-h` option.

# Note
Please contact me on trucnguyenlam@gmail.com for any problem.

