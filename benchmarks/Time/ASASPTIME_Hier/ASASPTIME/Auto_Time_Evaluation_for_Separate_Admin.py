#!/usr/bin/env python

import sys
import os

r2a1 = { 
1 : 'role0;', 2 : 'role1;', 3 : 'role2;', 4 : 'role2;' , 5 : 'role2;' , 6 : 'role0;', 7 : 'role1;', 
8 : 'role2;', 9 : 'role3;' , 10 : 'role4;' , 11 : 'role3;' , 12 : 'role6;', 13 : 'role8;', 14 : 'role9;', 
15 : 'role14;', 16 : 'role4;', 17 : 'role7;', 18 : 'role9;', 19 : 'role21;', 20 : 'role32;', 21 : 'role19;', 
22 : 'role3;', 23 : 'role6;', 24 : 'role9;', 25 : 'role21;', 26 : 'role145;', 27 : 'role422;', 28 : 'role312;', 29 : 'role98;', 30 : 'role65;' , 31 : 'role87;' , 32 : 'role95;', 33 : 'role154;', 34 : 'role754;', 35 : 'role1146;' , 36 : 'role484;' , 37 : 'role1456;' , 38 : 'role9664;', 39 : 'role8132;', 40 : 'role4546;', 41 : 'role16224;', 42 : 'role4132;', 43 : 'role4543;', 44 : 'role15643;', 45 : 'role5423;', 46 : 'role14324;', 47 : 'role4234;', 48 : 'role7786;', 49 : 'role12657;', 50 : 'role2312;', 51 : 'role21323;', 52 : 'role34532;', 53 : 'role1434;', 54 : 'role41876;', 55 : 'role3634;' 
}

os.system('echo "Start to evaluate now..."' )
folder = 'Test_case/Benchs_Stoller/AGTRBAC'
i = 1

while (i <= 10) :
    p = os.popen('rm agtrbac')
    for line in p.readlines():
        print line
    os.system('echo ""' )
    
    os.system('echo "==========================================="' )
    os.system('echo "Running ' + folder + '/c' + str(i) +'"' )
    j = 1
    goal = "3 5"
    while (j <= 5) :
	os.system('echo "===== Test ' + str(j) + ' ====="' )
     	p = os.popen('time -f "real %E , user %U , sys %S" -a -o AnhGT_Log_c1_c10 ./AGTSystem.py ' + folder + '/c' + str(i) + ' ur 40 10 ' + goal + ' >> TerminalLog_c1_c10.txt')
        for line in p.readlines():
            if (line.find("error") > -1):
		print "Error!!!!"
	    
	if (j == 1) : goal = '15 4'
	elif (j == 2) : goal = '9 2'
	elif (j == 3) : goal = '27 3'
	elif (j == 4) : goal = '19 1'
	j = j + 1
    
    os.system('echo "====================END===================="' )	  

    i = i + 1


i = 11

while (i <= 15) :
    p = os.popen('rm agtrbac')
    for line in p.readlines():
        print line
    os.system('echo ""' )
    
    os.system('echo "==========================================="' )
    os.system('echo "Running ' + folder + '/c' + str(i) +'"' )
    j = 1
    goal = "3 5"
    while (j <= 5) :
	os.system('echo "===== Test ' + str(j) + ' ====="' )
     	p = os.popen('time -f "real %E , user %U , sys %S" -a -o AnhGT_Log_c11_c15 ./AGTSystem.py ' + folder + '/c' + str(i) + ' ur 40 10 ' + goal + ' >> TerminalLog_c11_c15.txt')
        for line in p.readlines():
            if (line.find("error") > -1):
		print "Error!!!!"
	if (j == 1) : goal = '15 8'
	elif (j == 2) : goal = '9 1'
	elif (j == 3) : goal = '27 3'
	elif (j == 4) : goal = '19 10'
	j = j + 1
    
    os.system('echo "====================END===================="' )	  

    i = i + 1



####################################

i = 16
while (i <= 20) :
    p = os.popen('rm agtrbac')
    for line in p.readlines():
        print line
    os.system('echo ""' )
    
    os.system('echo "==========================================="' )
    os.system('echo "Running ' + folder + '/c' + str(i) +'"' )
    j = 1
    goal = "4 2"
    while (j <= 5) :
	os.system('echo "===== Test ' + str(j) + ' ====="' )
     	p = os.popen('time -f "real %E , user %U , sys %S" -a -o AnhGT_Log_c16_c20 ./AGTSystem.py ' + folder + '/c' + str(i) + ' ur 40 20 ' + goal + ' >> TerminalLog_c16_c20.txt')
        for line in p.readlines():
            if (line.find("error") > -1):
		print "Error!!!!"
	if (j == 1) : goal = '7 8'
	elif (j == 2) : goal = '13 4'
	elif (j == 3) : goal = '20 19'
	elif (j == 4) : goal = '31 11'
	j = j + 1
    
    os.system('echo "====================END===================="' )	  

    i = i + 1
	

#################################
i = 21
while (i <= 25) :
    p = os.popen('rm agtrbac')
    for line in p.readlines():
        print line
    os.system('echo ""' )
    
    os.system('echo "==========================================="' )
    os.system('echo "Running ' + folder + '/c' + str(i) +'"' )
    j = 1
    goal = "2 26"
    while (j <= 5) :
	os.system('echo "===== Test ' + str(j) + ' ====="' )
     	p = os.popen('time -f "real %E , user %U , sys %S" -a -o AnhGT_Log_c21_c25 ./AGTSystem.py ' + folder + '/c' + str(i) + ' ur 40 30 ' + goal + ' >> TerminalLog_c21_c25.txt')
        for line in p.readlines():
            if (line.find("error") > -1):
		print "Error!!!!"
	if (j == 1) : goal = '6 3'
	elif (j == 2) : goal = '19 9'
	elif (j == 3) : goal = '25 14'
	elif (j == 4) : goal = '31 21'
	j = j + 1
    
    os.system('echo "====================END===================="' )	  

    i = i + 1



##################
i = 26
while (i <= 30) :
    p = os.popen('rm agtrbac')
    for line in p.readlines():
        print line
    os.system('echo ""' )
    
    os.system('echo "==========================================="' )
    os.system('echo "Running ' + folder + '/c' + str(i) +'"' )
    j = 1
    goal = "7 32"
    while (j <= 5) :
	os.system('echo "===== Test ' + str(j) + ' ====="' )
     	p = os.popen('time -f "real %E , user %U , sys %S" -a -o AnhGT_Log_c26_c30 ./AGTSystem.py ' + folder + '/c' + str(i) + ' ur 40 40 ' + goal + ' >> TerminalLog_c26_c30.txt')
        for line in p.readlines():
            if (line.find("error") > -1):
		print "Error!!!!"
	if (j == 1) : goal = '2 37'
	elif (j == 2) : goal = '17 2'
	elif (j == 3) : goal = '23 11'
	elif (j == 4) : goal = '30 28'
	j = j + 1
    
    os.system('echo "====================END===================="' )	  

    i = i + 1

