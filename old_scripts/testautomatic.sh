#!/bin/bash
#

cp launchtest.py vac_static
cd vac_static
python launchtest.py ../$1
cd ..