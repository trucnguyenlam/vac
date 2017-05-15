#!/bin/bash

PKG=pkg

mkdir $PKG

cp -r src $PKG
cp -r cmake $PKG
cp -r thirdparty $PKG
cp -r examples $PKG
cp -r licenses $PKG

cp CMakeLists.txt $PKG
cp README.md $PKG

tar cvf $PKG.tar $PKG
gzip $PKG.tar
rm -rf $PKG

