#!/bin/bash
cp singletest.py vac_static/
cd vac_static/
python singletest.py ../regression/original/Hospital/Hospital1.arbac yes
python singletest.py ../regression/original/Hospital/Hospital2.arbac yes
python singletest.py ../regression/original/Hospital/Hospital3.arbac yes
python singletest.py ../regression/original/Hospital/Hospital4.arbac yes
python singletest.py ../regression/original/University/University1.arbac yes
python singletest.py ../regression/original/University/University2.arbac yes
python singletest.py ../regression/original/University/University3.arbac yes
python singletest.py ../regression/original/University/University4.arbac yes
python singletest.py ../regression/original/Bank/Bank1.arbac yes
python singletest.py ../regression/original/Bank/Bank2.arbac yes
python singletest.py ../regression/original/Bank/Bank3.arbac yes
python singletest.py ../regression/original/Bank/Bank4.arbac yes

python singletest.py ../regression/testcases/mixed/test1.arbac no
python singletest.py ../regression/testcases/mixed/test2.arbac no
python singletest.py ../regression/testcases/mixed/test3.arbac no
python singletest.py ../regression/testcases/mixed/test4.arbac no
python singletest.py ../regression/testcases/mixed/test5.arbac no
python singletest.py ../regression/testcases/mixed/test6.arbac no
python singletest.py ../regression/testcases/mixed/test7.arbac no
python singletest.py ../regression/testcases/mixed/test8.arbac no
python singletest.py ../regression/testcases/mixed/test9.arbac no
python singletest.py ../regression/testcases/mixed/test10.arbac no
python singletest.py ../regression/testcases/mixednocr/test1.arbac no
python singletest.py ../regression/testcases/mixednocr/test2.arbac no
python singletest.py ../regression/testcases/mixednocr/test3.arbac no
python singletest.py ../regression/testcases/mixednocr/test4.arbac no
python singletest.py ../regression/testcases/mixednocr/test5.arbac no
python singletest.py ../regression/testcases/mixednocr/test6.arbac no
python singletest.py ../regression/testcases/mixednocr/test7.arbac no
python singletest.py ../regression/testcases/mixednocr/test8.arbac no
python singletest.py ../regression/testcases/mixednocr/test9.arbac no
python singletest.py ../regression/testcases/mixednocr/test10.arbac no
python singletest.py ../regression/testcases/positive/test1.arbac no
python singletest.py ../regression/testcases/positive/test2.arbac no
python singletest.py ../regression/testcases/positive/test3.arbac no
python singletest.py ../regression/testcases/positive/test4.arbac no
python singletest.py ../regression/testcases/positive/test5.arbac no
python singletest.py ../regression/testcases/positive/test6.arbac no
python singletest.py ../regression/testcases/positive/test7.arbac no
python singletest.py ../regression/testcases/positive/test8.arbac no
python singletest.py ../regression/testcases/positive/test9.arbac no
python singletest.py ../regression/testcases/positive/test10.arbac no
cd ..