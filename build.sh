#!/bin/bash

# Clean built source files
if [[ $1 = 'clean' ]]; then
	echo "Cleaning built ..."
	cd src/ccl/src
	make clean
	cd ..
	rm -rf lib
	cd ..
	cd ..
	cd src/simplify
	make distclean
	rm -rf autom4te.cache
	cd ..
	cd ..
	cd src/translate
	make distclean
	rm -rf autom4te.cache
	cd ..
	cd ..
	cd src/counterexample
	make distclean
	rm -rf autom4te.cache
	cd ..
	cd ..
	# rm -rf vac_static
	exit 1
fi

echo "Compiling source files..."
# Build ccl library first
cd src/ccl/src
make libccl.a
cd ..
mkdir lib
cp src/libccl.a lib
cd ../..

# Build simplify module
cd src/simplify
aclocal
autoconf
automake -a
./configure
make
cd ../..

# Build translate module
cd src/translate
aclocal
autoconf
automake -a
./configure
make
cd ../..

# Build counterExample module
cd src/counterexample
aclocal
autoconf
automake -a
./configure
make
cd ../..


# Copy file to build directory
echo "Copying executable files to bin directory..."
mkdir -p vac_static/bin
cp src/simplify/src/simplify vac_static/bin
cp src/translate/src/translate vac_static/bin
cp src/counterexample/src/counterexample vac_static/bin
echo "Check your machine architecture....."
if [[ $(uname -m) = 'x86_64' ]]; then
	echo "64bit"
	cp tools/bin_64bit/* vac_static/bin
else
	echo "32bit"
	cp tools/bin_32bit/* vac_static/bin
fi
cp tools/vac.sh vac_static
cp -r tools/formulae vac_static

cp -r tools/licenses vac_static
cp tools/VAC_LICENSE vac_static
cp tools/README vac_static

echo "Done."
echo "You can execute the VAC script from vac.sh in vac_static directory"


