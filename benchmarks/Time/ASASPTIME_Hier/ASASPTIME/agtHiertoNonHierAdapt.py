#!/usr/bin/env python

import sys

fn = sys.argv[1] #input file with temporal hierarchies
#format input file
#[Hierarchies]
#1>2>t1
#3>4>t2
#[UA0]
#u1 2 4 3 > t1
#u2 2 4 3 > t1
#u9 4 2 > t5
#rs 1 > t1     # for initial enabled roles
#rs 2 > t1
#[Rules]
#can_assign
#can_revoke

on = sys.argv[2] #output file with no hierarchies

file = open(fn, 'r')
o_file = open(on, 'w')

#maximum roles for each var is 150
#11-6-2013: note, form A are for role enabling (RS), from a-$ are for TUA, z is for timer
r2a = { 
1 : 'a', 2 : 'b', 3 : 'c', 4 : 'd' , 5 : 'e' , 6 : 'f', 7 : 'g', 
8 : 'h', 9 : 'i' , 10 : 'Z' , 11 : 'k' , 12 : 'l', 13 : 'm', 14 : 'n', 
15 : 'o', 16 : 'p', 17 : 'q', 18 : 'r', 19 : 's', 20 : 't', 21 : 'u', 
22 : 'v', 23 : 'w', 24 : '#', 25 : '$', 26 : 'z', 
27 : 'A', 28 : 'B', 29 : 'C', 30 : 'D' , 31 : 'E' , 32 : 'F', 33 : 'G', 
34 : 'H', 35 : 'I' , 36 : 'J' , 37 : 'K' , 38 : 'L', 39 : 'M', 40 : 'N', 
41 : 'O', 42 : 'P', 43 : 'Q', 44 : 'R', 45 : 'S', 46 : 'T', 47 : 'U', 
48 : 'V', 49 : 'W', 50 : 'X', 51 : 'Y', 52 : '@' 
}

RelRoles = [] #initial role hierarchies
RelRolesTr = [] #transitive closure of hierarchies

for line in open(fn):
    if (line.find("[Hierarchies]") > -1):
			
	relField = True
	ruleField = False
	UA0Field = False
	continue
    elif (line.find("[UA0]") > -1):
	#compute transitive closure of RelRoles (role hierarchies)
	#...
	tempRelRolesTr = RelRolesTr
	firsttime =  True
	while (firsttime or len(tempRelRolesTr) > len(RelRolesTr)):
	    if (firsttime):
		firsttime = False
	    RelRolesTr = tempRelRolesTr
	    
	    i = 0
	    while (i < len(RelRolesTr)):
		hier1 = RelRolesTr[i]
		tok_lstHier1 = hier1.split(">")
		j = 0
		while (j < len(RelRolesTr)):
		    if (i != j):
		        hier2 = RelRolesTr[j]
		        tok_lstHier2 = hier2.split(">")

			if (tok_lstHier1[2] == tok_lstHier2[2] and tok_lstHier1[0] == tok_lstHier2[1]):
			    if (not ((tok_lstHier2[0] + ">" + tok_lstHier1[1] + ">" + tok_lstHier1[2]) in tempRelRolesTr) ):
			        tempRelRolesTr.append(tok_lstHier2[0] + ">" + tok_lstHier1[1] + ">" + tok_lstHier1[2])

			elif (tok_lstHier1[2] == tok_lstHier2[2] and tok_lstHier1[1] == tok_lstHier2[0]):
			    if (not ((tok_lstHier1[0] + ">" + tok_lstHier2[1] + ">" + tok_lstHier1[2]) in tempRelRolesTr) ):
			        tempRelRolesTr.append(tok_lstHier1[0] + ">" + tok_lstHier2[1] + ">" + tok_lstHier1[2])
	    
		    j = j + 1

	        i = i + 1
	print "TransitiveRoleHierarchies:="
	print RelRolesTr
	
	o_file.write(line)
	UA0Field = True
	relField = False
	ruleField = False
	continue
    elif (line.find("[Rules]") > -1):
	
	o_file.write(line)

	relField = False
	UA0Field = False
	ruleField = True
	continue
    elif (line == "\n"):
	continue

    if (relField == True): #1>2>t1
	
	RelRoles.append(str.strip(line))
	RelRolesTr.append(str.strip(line))
    
    elif (UA0Field == True):
	#print "UA0 can be not empty"
	o_file.write(line)


    elif (ruleField == True):   #can_assign admin , ts1 , roles ; ts2 , role
	
        tok_lst = line.split()
	
	strRule= ""
	ts1 = ""
	ts2 = ""
	index = 0
	nextTS = False
	targetRoles = ""
	
	for i,tok in enumerate(tok_lst): 
	    if (tok == "," or tok == ";"):
		index = index + 1
		if (index == 1 or index == 3):
		    nextTS = True
		continue
	    elif (nextTS and index == 1):
		ts1 = tok
		nextTS = False
	    elif (nextTS and index == 3):
		ts2 = tok
		nextTS = False
	    elif (index == 4):
		targetRoles = targetRoles + " " + tok
	targetRoles = str.strip(targetRoles)
	index = 0
	minusPreCond = []
	
    	for i,tok in enumerate(tok_lst): 
	    
	    if (tok == "," or tok == ";"):
		
		if (len(minusPreCond) > 0):
		    if (index == 0):		        

			tempminusPreCond = minusPreCond
			firsttime =  True
			while (firsttime or len(tempminusPreCond) > len(minusPreCond)):
			    
	    		    if (firsttime):
		    	        firsttime = False
	    		    minusPreCond = tempminusPreCond

			    j = 0
		            while (j < len(minusPreCond)):
				minusRole = minusPreCond[j]

			        k = 0
		                while (k < len(RelRolesTr)):
			            if (RelRolesTr[k].find(">" + minusRole + ">" + ts1) > -1):
					relRole_tok_lst = RelRolesTr[k].split(">")
					if (not (relRole_tok_lst[0] in tempminusPreCond)):
					    tempminusPreCond.append(relRole_tok_lst[0])

				    k = k + 1

				j = j + 1
			    
		    elif (index == 2 and (tok_lst[0] == "can_revoke" or tok_lst[0] == "can_assign")):
			tempminusPreCond = minusPreCond
			firsttime =  True
			while (firsttime or len(tempminusPreCond) > len(minusPreCond)):
	    		    if (firsttime):
		    	        firsttime = False
	    		    minusPreCond = tempminusPreCond

			    j = 0
		            while (j < len(minusPreCond)):
				minusRole = minusPreCond[j]

			        k = 0
		                while (k < len(RelRolesTr)):
			            if (RelRolesTr[k].find(">" + minusRole + ">" + ts2) > -1):
					relRole_tok_lst = RelRolesTr[k].split(">")
					if (not (relRole_tok_lst[0] in tempminusPreCond)):
					    tempminusPreCond.append(relRole_tok_lst[0])

				    k = k + 1

				j = j + 1

		
		j = 0
		while (j < len(minusPreCond)):
		    strRule = strRule + "-" + minusPreCond[j] + " "
		    j = j + 1
		minusPreCond = []
		index = index + 1
		strRule = strRule + tok + " "
		
	    elif (tok[0] != "-"):
		strRule = strRule + tok + " "
            else:
	 	if(not (tok[1:] in minusPreCond)):
		    minusPreCond.append(tok[1:])

        #work here for positive roles 	
	tok_lst = strRule.split()
	posRoleSeniorAd = []
	posRoleSeniorCond = []
 	negRoleAd = []
	negRoleCond = []
	posRoleDisEnab = ""  #Only for preCond of a disable, enable actions
	index = 0
	for i,tok in enumerate(tok_lst):
	    if (i < 1):		
		continue

	    if (tok == "," or tok == ";"):
				
		index = index + 1		
		
	    elif (tok[0] != "-"):
		seniorRole = []
		seniorRole.append(tok)

		if (index == 0):		        

		    tempseniorRole = seniorRole
		    firsttime =  True
		    while (firsttime or len(tempseniorRole) > len(seniorRole)):
			    
	    		if (firsttime):
		    	    firsttime = False
	    		seniorRole = tempseniorRole

			j = 0
		        while (j < len(seniorRole)):
			    posRole = seniorRole[j]

			    k = 0
		            while (k < len(RelRolesTr)):
			        if (RelRolesTr[k].find( ">" + posRole + ">" + ts1) > -1):
				    relRole_tok_lst = RelRolesTr[k].split(">")
				    if (not (relRole_tok_lst[0] in tempseniorRole)):
					tempseniorRole.append(relRole_tok_lst[0])

				k = k + 1

			    j = j + 1

		    posRoleSeniorAd.append(seniorRole)
			    
		elif (index == 2 and (tok_lst[0] == "can_revoke" or tok_lst[0] == "can_assign")):
		    tempseniorRole = seniorRole
		    
		    firsttime =  True
		    while (firsttime or len(tempseniorRole) > len(seniorRole)):
			    
	    		if (firsttime):
		    	    firsttime = False
	    		seniorRole = tempseniorRole

			j = 0
		        while (j < len(seniorRole)):
			    posRole = seniorRole[j]

			    k = 0
		            while (k < len(RelRolesTr)):
			        if (RelRolesTr[k].find(">" + posRole + ">" + ts2) > -1):
				    relRole_tok_lst = RelRolesTr[k].split(">")
				    if (not (relRole_tok_lst[0] in tempseniorRole)):
					tempseniorRole.append(relRole_tok_lst[0])

				k = k + 1

			    j = j + 1

		    posRoleSeniorCond.append(seniorRole)

		elif (index == 2 and (tok_lst[0] == "can_enable" or tok_lst[0] == "can_disable")):
		    
		    posRoleDisEnab = posRoleDisEnab + " " + tok


            else:
		if (index == 0):
	 	    if(not (tok[1:] in negRoleAd)):
		        negRoleAd.append(tok[1:])
		elif (index == 2):
	 	    if(not (tok[1:] in negRoleCond)):
		        negRoleCond.append(tok[1:])

	
	#compute cartersian product
	#For Admin
	cartesianAd = []
	i = 0
        while True:
            carte = ""
            j = i
            for l in posRoleSeniorAd:
		
                carte = carte + " " + l[j % len(l)]
                j /= len(l)
	    
	    if (not (str.strip(carte) in cartesianAd)):
		
		cartesianAd.append(str.strip(carte))			
            if j > 0: break
            
            i += 1

	if (tok_lst[0] == "can_enable" or tok_lst[0] == "can_disable"):
	    
 	    i = 0
	    while(i < len(cartesianAd)):
		if (cartesianAd[i] != "true" or cartesianAd[i] != "false"):	
		    carte_lst = cartesianAd[i].split(" ")
		    
		    isRemoved = False
		    for k, tok in enumerate(carte_lst):
			
		        if (tok in negRoleAd):  #Pos and neg have same role -> remove				    
			    isRemoved = True
			    break
		    if (isRemoved): 
			i = i + 1			
			continue

	        strRule = tok_lst[0] + " " + cartesianAd[i]
		for tok in negRoleAd:
		    strRule = strRule + " -" + tok

		strRule = strRule +  " , " + ts1 + " , " + str.strip(posRoleDisEnab)
		for tok in negRoleCond:
		    strRule = strRule + " -" + tok
 		
		strRule = strRule + " ; " + ts2 + " , " + targetRoles
		o_file.write(strRule + "\n")

		i = i + 1

	    continue # not need the following code

	#For condition (can_assign or can_revoke)
	cartesianCond = []
	i = 0
        while True:
            carte = ""
            j = i
            for l in posRoleSeniorCond:
		
                carte = carte + " " + l[j % len(l)]
                j /= len(l)
	    
	    if (not (str.strip(carte) in cartesianCond)):
		
		cartesianCond.append(str.strip(carte))		
            if j > 0: break
            
            i += 1

	#Print to file additional actions
	i = 0
	while(i < len(cartesianAd)):
	    if (cartesianAd[i] != "true" or cartesianAd[i] != "false"):
	        carte_lst = cartesianAd[i].split(" ")
	        isRemoved = False
	        for p,tok in enumerate(carte_lst):
		    if (tok in negRoleAd):  #Pos and neg have same role -> remove	
		        isRemoved = True
		        break
	        if (isRemoved): 
		    i = i + 1			
		    continue

	    j = 0
	    while(j < len(cartesianCond)):
		if (cartesianCond[j] != "true" or cartesianCond[j] != "false"):
		    carte_lst = cartesianCond[j].split(" ")
		    
		    isRemoved = False
		    for t,tok in enumerate(carte_lst):
		        if (tok in negRoleCond):  #Pos and neg have same role -> remove	
			    isRemoved = True
			    break
		    if (isRemoved): 
			j = j + 1			
			continue

		strRule = tok_lst[0] + " " + cartesianAd[i]
		for tok in negRoleAd:
		    strRule = strRule + " -" + tok
	
	        strRule = strRule + " , " + ts1 + " , " + cartesianCond[j] 
		for tok in negRoleCond:
		    strRule = strRule + " -" + tok

		strRule = strRule + " ; " + ts2 + " , " + targetRoles
		o_file.write(strRule + "\n")

		j = j + 1
	    i = i + 1

o_file.close()

	
