#!/usr/bin/env python

import sys
import os
import ast


fn = sys.argv[1] #file to be run
qr_mode = sys.argv[2] #query
#sys.argv[3] : maxrole
#sys.argv[4] : maxtime
#sys.argv[5] : goal
#sys.argv[6] : time
qr = qr_mode[:2]
#add transition
mode = qr_mode[3:] #"Linear"
#print qr
#print mode
if (qr == "ur" and mode == "Multi"): 
    #For new approach pre-Processing (also for multiple target approach), comment them if donot want to use new approach
    os.system('./agtHiertoNonHier.py ' + fn + ' inputSystem')
    p = os.popen('./AGTSystem.py inputSystem ur ' + sys.argv[3] + ' ' + sys.argv[4] + ' ' + sys.argv[5] + ' ' + sys.argv[6] + ' ' + mode)
    for line in p.readlines():
        print line
    sys.exit()
   
elif (qr == "ur" and mode == "Linear"): 
    #For new approach pre-Processing (also for multiple target approach), comment them if donot want to use new approach
    os.system('./agtHiertoNonHier.py ' + fn + ' inputSystem')
    p = os.popen('./AGTSystem.py inputSystem ur ' + sys.argv[3] + ' ' + sys.argv[4] + ' ' + sys.argv[5] + ' ' + sys.argv[6] + ' ' + mode)
    for line in p.readlines():
        print line
    sys.exit()
        
elif (qr == "ur" and mode == "Adapt"): 
    #For adaptive approach pre-processing, comment them if donot want to use apadptive approach
    p = os.popen('./agtHiertoNonHierAdapt.py ' + fn + ' inputSystem')
    #Refine goal to set of sub-goals
    nextisTransitive = False
    RelRolesTr = []  #transitive closure of role hierarchies
    for line in p.readlines():
	#print line
        if (line.find("TransitiveRoleHierarchies:=") > -1):
	    nextisTransitive = True
	    continue
	if (nextisTransitive ==True):
	    RelRolesTr = ast.literal_eval(str.strip(line))

    #print RelRolesTr
    #Compute senior roles of the goal (only 1 role in the goal)
    seniorGoalRole = []
    seniorGoalRole.append(sys.argv[5])
    tempSenior = seniorGoalRole
    firsttime =  True
    while (firsttime or len(tempSenior) > len(seniorGoalRole)):	  
	if (firsttime):
	    firsttime = False	    

	if (True):
	    seniorGoalRole = tempSenior
	    j = 0
	    while (j < len(seniorGoalRole)):
		aRole = seniorGoalRole[j]
		
		k = 0
	        while (k < len(RelRolesTr)):
		    
		    if (RelRolesTr[k].find(">" + aRole + ">t" + sys.argv[6]) > -1):
			
			relRole_tok_lst = RelRolesTr[k].split(">")
			if (not (relRole_tok_lst[0] in tempSenior)):
			    tempSenior.append(relRole_tok_lst[0])

		    k = k + 1

		j = j + 1

    sr = 0
    print seniorGoalRole
    while (sr < len(seniorGoalRole)):
        print "Senior: " + seniorGoalRole[sr]
        q = os.popen('./AGTSystem.py inputSystem ur ' + sys.argv[3] + ' ' + sys.argv[4] + ' ' + seniorGoalRole[sr] + ' ' + sys.argv[6] + ' ' + mode)
	isUnsafe = False
	
        for line in q.readlines():
            print line
	    if (line.find("UNSAFE") > -1):
		isUnsafe = True
	if (isUnsafe):
	    print "Final results: System is UNSAFE!"
	    break
	
	sr = sr + 1

    
