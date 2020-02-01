#!/bin/bash

mkdir -p build/vac_static
cp vac_static/vac.sh build/vac_static
cp vac_static/README build/vac_static
cp vac_static/VAC_LICENSE build/vac_static
cp -r vac_static/licenses build/vac_static
cp -r vac_static/bin build/vac_static
cp -r vac_static/formulae build/vac_static
cd build
tar cvf vac_static.tar vac_static
bzip2 vac_static.tar
if [[ $1 = "32" ]]; then
    mv vac_static.tar.bz2 ../vac_32bit.tar.bz2
else
    mv vac_static.tar.bz2 ../vac_64bit.tar.bz2
fi
cd ..
rm -rf build