#!/usr/bin/env python

import sys

fn = sys.argv[1] #input file with can_assign_h
#format input file
#[UA0]
#u1 2 4 3 > t1
#u2 2 4 3 > t1
#u9 4 2 > t5
#rs 1 > t1     # for initial enabled roles
#rs 2 > t1
#[Rules]
#can_assign
#can_revoke
#can_assign_h

on = sys.argv[2] #output file with multiple target

o_file = open(on, 'w')


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

RelRolesTr = []
for line in open(fn):
    if (line.find("can_assign_h") > -1):
	#format can_assign_h true , t1 , 4 ; t1 , 5
        tok_lst = str.strip(line).split(" ")
	RelRolesTr.append(tok_lst[5] + ">"+ tok_lst[9] + ">" + tok_lst[7])	
    else:
	o_file.write(line)

if (len(RelRolesTr) > 0):
 
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
    print RelRolesTr
    
    processedRoles = [] #format role+timeslot
    i = 0
    while (i < len(RelRolesTr)):
        hier1 = RelRolesTr[i]
	tok_lstHier1 = hier1.split(">")
	if (not((tok_lstHier1[0] + "+" + tok_lstHier1[2]) in processedRoles)):
	    processedRoles.append(tok_lstHier1[0] + "+" + tok_lstHier1[2])
	    juniorRoles = []
	    juniorRoles.append(tok_lstHier1[1])

	    j = 0
	    while (j < len(RelRolesTr)):
		if (i != j):
		    hier2 = RelRolesTr[j]
		    tok_lstHier2 = hier2.split(">")

		    if (tok_lstHier1[2] == tok_lstHier2[2] and tok_lstHier1[0] == tok_lstHier2[0] and not(tok_lstHier2[1] in juniorRoles)):
			juniorRoles.append(tok_lstHier2[1])
		j = j + 1

            k = 0
	    strline = "can_assign_h true , " + tok_lstHier1[2] + " , " + tok_lstHier1[0] + " ; " + tok_lstHier1[2] + " ,"
	    print juniorRoles
	    while (k < len(juniorRoles)):
		strline = strline + " " + juniorRoles[k]
		k = k + 1
	    strline = strline + "\n"
	    o_file.write(strline)

	i = i + 1

o_file.close()

	
