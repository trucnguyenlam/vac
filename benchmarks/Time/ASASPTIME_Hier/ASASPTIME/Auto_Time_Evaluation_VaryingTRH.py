#!/usr/bin/env python

import sys
import os

os.system('echo "Start to evaluate now..."' )
folder = 'Test_case/VAC_policies/AGTRBAC/GT_Hierarchies/VaryingTRH/CreateVaryingDepthandCardinalityforJCS/maxt20AddedDEP'

goal = ' 9 17'

i = 1
subFolder = ''
maxtimeslot = '20'
while (i <= 7) :
    if (i == 1):
        fd = '3'
        subFolder = folder + '/3'
    elif (i == 2):
        fd = '5'
        subFolder = folder + '/5'
    elif (i == 3):
        fd = '10'
        subFolder = folder + '/10'
    elif (i == 4):
        fd = '15'
        subFolder = folder + '/15'
    elif (i == 5):
        fd = '20'
        subFolder = folder + '/20'
    elif (i == 6):
        fd = '25'
        subFolder = folder + '/25'
    elif (i == 7):
        fd = '30'
        subFolder = folder + '/30'
    
	
    p = os.popen('rm agtrbac')
    for line in p.readlines():
        print line
    os.system('echo ""' )
    
    kk = 1
    while (kk <= 15):

	##################Testing######################
    	os.system('echo "==========================================="' )
    	os.system('echo "Running ' + subFolder + '/AGTUniv2_' + fd + '_' + str(kk) +'"' )
	
       	p = os.popen('time -f "real %E , user %U , sys %S" -a -o JCSResults/JCS_Log_' + fd  + ' ./mainSystem.py ' + subFolder + '/AGTUniv2_' + fd + '_' +  str(kk) + ' ur 34 ' + maxtimeslot + goal + ' >> JCSResults/TerminalLog_JCS_' + fd  + '.txt')
        for line in p.readlines():
            if (line.find("error") > -1):
		print "Error!!!!"
	 
	kk = kk + 1

    
    
    os.system('echo "====================END===================="' )	  

    i = i + 1


