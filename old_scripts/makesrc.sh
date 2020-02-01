#!/bin/bash
#

mkdir -p build/VAC
./build.sh clean
cp -r libs build/VAC
cp -r src build/VAC
cp -r tools build/VAC
cp build.sh build/VAC
cp README build/VAC
cp VAC_LICENSE build/VAC
cd build

tar cvf VAC.tar VAC
bzip2 VAC.tar
mv VAC.tar.bz2 ../
cd ..
rm -rf build