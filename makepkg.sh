#!/bin/bash
#

mkdir -p build/vac_static
cp vac_static/vac.sh build/vac_static
cp vac_static/README build/vac_static
cp -r vac_static/bin build/vac_static
cd build
tar cvf vac_static.tar vac_static
gzip vac_static.tar
mv vac_static.tar.gz ../
cd ..
rm -rf build