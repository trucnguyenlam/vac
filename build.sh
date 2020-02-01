#!/bin/bash

folder=$(pwd)

autoreconf --install && \

./configure --prefix="${folder}/vac_static" CFLAGS="" && \
make ${1} && make install 

