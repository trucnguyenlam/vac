#!/usr/bin/env python

import sys
import os

fn = sys.argv[1] #file to be run
qr = sys.argv[2] #query
#sys.argv[3] : maxrole
#sys.argv[4] : maxtime
#sys.argv[5] : goal
#sys.argv[6] : time
mode = sys.argv[7]
#add transition
os.system('echo "Translating now..."' )
os.system('echo "==========================================="' )

if (qr == "ur"): 
    ###13/09/2013: Extract useful actions. Require initial state are empty, no TUA, no RS
    i_file = open(fn, 'r')
    o_file = open('system', 'w')

    i_file.seek(0, 0)
    tr=0
    #get all role in the goal of assignment	
    AssgnGoalTime = []  #format: goal+time
    EnableRoleTime = []	 #format: role+time
    
    CurrentActiveRolesTimes = []    #format: role+time
    CurrentActiveEnableRT = []    #format: role+time
    NextActiveRolesTimes = []
    NextActiveEnableRT = []
    ActiveRolesTimes = []
    ActiveEnableRT = []
    

    UA0Field = False
    for line in i_file:

	if (line.find("[Rules]") > -1):	
	    o_file.write(line)	
	    UA0Field = False
	    continue
	if (line.find("[UA0]") > -1):		
	    UA0Field = True
	    o_file.write(line)
	    continue
	if (line =="\n"):
	    continue

	if (UA0Field == True):
	    tok_lst = line.split(' ')
	    w = 1 #0 is for user identifier  e.g., u1 3 4 5 > t1 t2
	    
	    while w < tok_lst.index('>') :
		
		k = tok_lst.index('>') + 1
		while k < len(tok_lst) :

	            if (line[0] == 'u' and not ((str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k])) in AssgnGoalTime)) :
		    	AssgnGoalTime.append(str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k]))
		    elif (line[0] == 'r' and not ((str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k])) in EnableRoleTime)) :
		    	EnableRoleTime.append(str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k]))
		    k = k + 1

		w = w + 1

	    o_file.write(line)

	    continue


	tok_lst = line.split(' ')
	asgtimeindex = tok_lst.index(";")
	
	if (tok_lst[0] == "can_assign" or tok_lst[0] == "can_assign_h"):  
	    AssgnGoalTime.append(str.strip(tok_lst[asgtimeindex + 3]) + '+' + str.strip(tok_lst[asgtimeindex + 1]))
	if (tok_lst[0] == "can_enable"):  
	    EnableRoleTime.append(str.strip(tok_lst[asgtimeindex + 3]) + '+' + str.strip(tok_lst[asgtimeindex + 1]))
	    

    
    
    CurrentActiveRolesTimes.append(sys.argv[5] + "+t" + sys.argv[6])
    CurrentAction = []
    preCurrentAction = []
    while (True):
	i_file.seek(0, 0)
	preCurrentAction = CurrentAction
	CurrentAction = []	
	UA0Field = False
    	for line in i_file:
	    if (line.find("[Rules]") > -1):		
	        UA0Field = False
	        continue
	    if (line.find("[UA0]") > -1):		
	        UA0Field = True	       
	        continue
	    if (line =="\n" or UA0Field == True):
	        continue
	
	    #For rules field 
	    
	    ActiveRolesTimes = []
	    ActiveEnableRT = []
	    if (line =="\n"):
	        break
    	    tok_lst = line.split()
            asgtimeindex = tok_lst.index(";")
    	    asgtime = tok_lst[asgtimeindex + 1]
	    targetRole = tok_lst[asgtimeindex + 3]
	    strRoleTime = str.strip(tok_lst[asgtimeindex + 3]) + '+' + str.strip(tok_lst[asgtimeindex + 1])

	    #Important Note: Require 1 admin role, if more, must to rewite the code below
	
	    if ((tok_lst[0] == "can_assign" or tok_lst[0] == "can_assign_h" or tok_lst[0] == "can_revoke") and (strRoleTime in CurrentActiveRolesTimes)):
	        isAdded = True
	        if (tok_lst[1] != 'true'):		
	    	    strAdminTime = str.strip(tok_lst[1]) + '+' + str.strip(tok_lst[3])
		    ActiveRolesTimes.append(strAdminTime)
		    ActiveEnableRT.append(strAdminTime)
		    if (not(strAdminTime in AssgnGoalTime) or not(strAdminTime in EnableRoleTime)):
		        isAdded = False

	        j = 5
	        canStartCandidate = True	 #19-8-2013   
	        while (j < asgtimeindex and isAdded == True):
		    #print tok_lst[j]
		
		    if (tok_lst[j] == targetRole): #19-8-2013 to avoid can_assign t1 , 3 4, t3 , 3 ->can not be executed
		        isAdded = False  
		        break	
		    if (tok_lst[j][0] != '-' and tok_lst[j] != 'true'):
		        ActiveRolesTimes.append(str.strip(tok_lst[j]) + "+" + asgtime)
		        if (not((str.strip(tok_lst[j]) + "+" + asgtime) in AssgnGoalTime)) :
		    	    isAdded = False
		    	    break
		
		    j = j + 1
	    
	        if (isAdded) :
	    	    CurrentAction.append(" ".join(tok_lst) + "\n")
		    NextActiveRolesTimes.extend(ActiveRolesTimes)
		    NextActiveEnableRT.extend(ActiveEnableRT)
	    	    
	    elif ((tok_lst[0] == "can_enable" or tok_lst[0] == "can_disable") and (strRoleTime in CurrentActiveEnableRT)):
		isAdded = True
	        if (tok_lst[1] != 'true'):		
	    	    strAdminTime = str.strip(tok_lst[1]) + '+' + str.strip(tok_lst[3])
		    ActiveRolesTimes.append(strAdminTime)
		    ActiveEnableRT.append(strAdminTime)
		    if (not(strAdminTime in AssgnGoalTime) or not(strAdminTime in EnableRoleTime)):
		        isAdded = False

	        j = 5
	        canStartCandidate = True	 #19-8-2013   
	        while (j < asgtimeindex and isAdded == True):
		    #print tok_lst[j]
		
		    if (tok_lst[j] == targetRole): #19-8-2013 to avoid can_assign t1 , 3 4, t3 , 3 ->can not be executed
		        isAdded = False  
		        break	
		    if (tok_lst[j][0] != '-' and tok_lst[j] != 'true'):
		        ActiveEnableRT.append(str.strip(tok_lst[j]) + "+" + asgtime)
		        if (not((str.strip(tok_lst[j]) + "+" + asgtime) in EnableRoleTime)) :
		    	    isAdded = False
		    	    break
		
		    j = j + 1
	    
	        if (isAdded) :
	    	    CurrentAction.append(" ".join(tok_lst) + "\n")
		    NextActiveRolesTimes.extend(ActiveRolesTimes)
		    NextActiveEnableRT.extend(ActiveEnableRT)


	if (len(CurrentAction) <= len(preCurrentAction)):
	    break
	CurrentActiveRolesTimes.extend(NextActiveRolesTimes)
	CurrentActiveEnableRT.extend(NextActiveEnableRT)

   
    while(True):
	AssgnGoalTime = []
	EnableRoleTime = []
    	CurrentActionTemp = []
	i_file.seek(0, 0)
	for line in i_file:

	    if (line.find("[Rules]") > -1):		
	        break
	    if (line.find("[UA0]") > -1):		
	        UA0Field = True	        
	        continue
	    if (line =="\n"):
	        continue

	    if (UA0Field == True):
	        tok_lst = line.split(' ')
	        w = 1 #0 is for user identifier  e.g., u1 3 4 5 > t1 t2
	        
	        while w < tok_lst.index('>') :
		
		    k = tok_lst.index('>') + 1
		    while k < len(tok_lst) :

	                if (line[0] == 'u' and not ((str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k])) in AssgnGoalTime)) :
		    	    AssgnGoalTime.append(str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k]))
		        elif (line[0] == 'r' and not ((str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k])) in EnableRoleTime)) :
		    	    EnableRoleTime.append(str.strip(tok_lst[w]) + '+' + str.strip(tok_lst[k]))
		        k = k + 1

		    w = w + 1


	caI = 0
    	while (caI < len(CurrentAction)):
	    line = CurrentAction[caI]
	    tok_lst = line.split(' ')
	    asgtimeindex = tok_lst.index(";")
	    asgtime = tok_lst[asgtimeindex + 1]
	    if (tok_lst[0] == "can_assign" or tok_lst[0] == "can_assign_h"):    
	    	AssgnGoalTime.append(str.strip(tok_lst[asgtimeindex + 3]) + '+' + str.strip(tok_lst[asgtimeindex + 1]))
	    if (tok_lst[0] == "can_enable"):    
	    	EnableRoleTime.append(str.strip(tok_lst[asgtimeindex + 3]) + '+' + str.strip(tok_lst[asgtimeindex + 1]))

	    caI = caI + 1

       
	caI = 0
	while (caI < len(CurrentAction)):
	    line = CurrentAction[caI]
            if (line =="\n"):
	    	break
    	    tok_lst = line.split()
            asgtimeindex = tok_lst.index(";")
    	    asgtime = tok_lst[asgtimeindex + 1]
	    targetRole = tok_lst[asgtimeindex + 3] 
	    isAdded = True
	    if (tok_lst[1] != 'true'):		
	    	strAdminTime = str.strip(tok_lst[1]) + '+' + str.strip(tok_lst[3])
		if (not(strAdminTime in AssgnGoalTime) or not(strAdminTime in EnableRoleTime)):
		    isAdded = False

	    j = 5 
	    while (j < asgtimeindex and isAdded == True):
		
		if (tok_lst[j] == targetRole): 
		    isAdded = False  
		    break	
		if ((tok_lst[0] == "can_assign" or tok_lst[0] == "can_assign_h") and tok_lst[j][0] != '-' and tok_lst[j] != 'true'  and not((str.strip(tok_lst[j]) + "+" + asgtime) in AssgnGoalTime)) :
		    isAdded = False
		    break
		if (tok_lst[0] == "can_enable" and tok_lst[j][0] != '-' and tok_lst[j] != 'true'  and not((str.strip(tok_lst[j]) + "+" + asgtime) in EnableRoleTime)) :
		    isAdded = False
		    break
		j = j + 1

	  
	    if (isAdded) :
	    	
		CurrentActionTemp.append(" ".join(tok_lst) + "\n")
	    	
	    caI = caI + 1

	if (len(CurrentActionTemp) == len(CurrentAction)):
	    break
	else:
	    CurrentAction = CurrentActionTemp
	
    if (len(CurrentAction) > 0):
        o_file.write("".join(CurrentAction))
    else:
	print "System is SAFE!"
	sys.exit()
    #Write can_assign false ... for unuseful actions
    #i_file.seek(0, 0)
    #for line in i_file:

	#if (line.find("[Rules]") > -1):	
	 #   UA0Field = False
	 #   continue
	#elif (line.find("[UA0]") > -1):		
	 #   UA0Field = True
	 #   continue
	#elif (line =="\n" or UA0Field == True):
	 #   continue
	
	#if ((str.strip(line) + "\n") in CurrentAction):	    
         #   o_file.write(line)
	#else:
	   
	 #   o_file.write("can_assign false , t1 , false ; t1 , 1\n")

    i_file.close()
    o_file.close()
	
    
    #######

    #Choose one of the following (multiple target or single target)
    #16-05-2014: from hierarchies to multiple target roles
    if (mode == "Multi"):
        tq = os.popen('./hiertoMultipleTarget.py system m_system')
        for line in tq.readlines():
            print line
        os.system('./agtrbac2mcmt1.py m_system agtrbac ' + sys.argv[3] + " " + sys.argv[4] + " " + sys.argv[4] + " " + qr + " " + sys.argv[5] + " " + sys.argv[6])

    #16-05-2014: Role hierarchies: For new approach
    elif (mode == "Linear"):
        os.system('./agtrbac2mcmt1.py system agtrbac ' + sys.argv[3] + " " + sys.argv[4] + " " + sys.argv[4] + " " + qr + " " + sys.argv[5] + " " + sys.argv[6])

    #16-05-2014: Role hierarchies: For adaptive approach
    elif(mode =="Adapt"):
        os.system('./agtrbac2mcmt1_foradapt.py system agtrbac ' + sys.argv[3] + " " + sys.argv[4] + " " + sys.argv[4] + " " + qr + " " + sys.argv[5] + " " + sys.argv[6])	

os.system('echo "Running MCMT now..."' )
os.system('echo "==========================================="' )
qp = os.popen('./../mcmt -v0 agtrbac')
for line in qp.readlines():
    print line
