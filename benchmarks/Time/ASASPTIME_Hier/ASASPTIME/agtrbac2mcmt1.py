#!/usr/bin/env python

import sys

fn = sys.argv[1] #file to be tranlated
on = sys.argv[2] #file to be saved
maxrole = sys.argv[3] # max number of roles
maxtime = sys.argv[4] # max number of timeslots for timer
effectivemaxtime = sys.argv[5] #6/6/2013: max number of time slot for transitions (to reduce the vars need to be used)
qr = sys.argv[6]    # for query sign: e.g., ur: is user reach role; up: is user reachs permission
#goal = sys.argv[7]  # there exists a user reach role goal
#time = sys.argv[8]  # there exists a user reach role goal at time 6 

i_file = open(fn, 'r')
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


o_file.write(":smt (define-type uat (tuple ")
j=1
while j<=150 : 
    o_file.write("bool ")
    j=j+1
o_file.write("))\n\n")


o_file.write(":smt (define all_false::uat (mk-tuple ")
j=1
while j<=150 : 
    o_file.write("false ")
    j=j+1
o_file.write("))\n\n")
print

numOfVars = 0 # how many vars we use
numOfVars = int(round((int(maxrole) * int(effectivemaxtime))/150)) + 1


i_file.seek(0, 0)
tr=1
UA0Roles = []
RelRoles1 = [] # before <
RelRoles2 = [] # after < 
UA0User1 = [] #start user in the block
UA0User2 = [] #end user in the block
declareFile = [] #contain smt: define ...
currentBlock = ""
currentEndUser = ""
currentBlockIndex = 0
fblock = True
lstInitRS = []

strDeclare = ""
for line in i_file:
    if (line.find("[UA0]") > -1):
	UA0Field = True
	continue
    elif (line.find("[Rules]") > -1):
        #process initial states
	
	#for rs
	w = 1
	
	while w<=numOfVars :
	    strDeclare = strDeclare + ":smt (define iRS_v" + str(w) + "::uat (mk-tuple"
	    iw = 1
	    while (iw <=150):
		if (("v" + str(w) + "_" +str(iw)) in lstInitRS): 
		    strDeclare = strDeclare + " true"
		else:
		    strDeclare = strDeclare + " false"

		iw = iw + 1
	    strDeclare = strDeclare + " ))\n\n"
            w = w + 1


	#for tua
	if (currentEndUser != ""):
	    UA0User2.append(currentEndUser) # for the last block

	#print define variables
	o_file.write(strDeclare)

	
	### for TUA
	j = 1
	while j<=numOfVars :
    	    o_file.write(":local " + r2a[j] + " uat \n")
    	    j=j+1
	o_file.write("\n")

	#16-05-2014: For implicit TUA
	j = 1
	while j<=numOfVars :
    	    o_file.write(":local " + r2a[j + 17] + " uat \n")
    	    j=j+1
	o_file.write("\n")

	###for RS
	j = 1 #from A j + 34
	while j<=numOfVars :    
    	    o_file.write(":local " + r2a[j + 34] + " uat \n")
    	    j=j+1
	o_file.write("\n")

  
	o_file.write(":global z real \n")  #global clock
	o_file.write("\n")


	#print Initial and Unsafe Field	
	
	o_file.write("\n:initial\n")
	o_file.write(":var x\n")
	#if (len(UA0User1) > 0):
	#    o_file.write(":cnj (or")
	#else:
	o_file.write(":cnj ")	
	
	#for RS
	i = 1
	while i<=numOfVars :
    	    o_file.write(" (= " + r2a[i + 34] + "[x] iRS_v" + str(i) + ")")
	    i = i + 1
	
	#for TUA
	strBlockstr = ""
	tailStr = ""
	wi = 0
	print UA0User1
	print UA0User2
	while (wi < len(UA0User1)):
	    
	    strBlockstr = " (if "
	    tailStr = tailStr + ")"	
	    if (UA0User1[wi] == UA0User2[wi]):
	        strBlockstr = strBlockstr + "(= x " + str(UA0User1[wi]) + ") "
	    else:
		strBlockstr = strBlockstr + "(and (<= " + str(UA0User1[wi])+ " x) (<= x " + str(UA0User2[wi]) + ")) "
	    
	    #if (numOfVars > 1):
	    strBlockstr = strBlockstr + " (and"
	    i = 1
	    while i<=numOfVars :
    	        strBlockstr = strBlockstr + " (= " + r2a[i] + "[x] i" + str(i) + "_" + str(wi+1) + ") (= " + r2a[i+17] + "[x] i" + str(i) + "_" + str(wi+1) + ")"
    	        i=i+1
	    #if (numOfVars > 1):
	    strBlockstr = strBlockstr + ")"
	    o_file.write(strBlockstr)
	    wi = wi + 1
	
	i = 1
	#if (numOfVars > 1):
	o_file.write(" (and")
	while i<=numOfVars :
    	    o_file.write(" (= " + r2a[i] + "[x] all_false) (= " + r2a[i+17] + "[x] all_false)")
    	    i=i+1
	#if (numOfVars > 1):
	o_file.write(")")
	#if (len(UA0User1) > 0):
	o_file.write(tailStr)
		
	o_file.write("\n\n")



	o_file.write(":unsafe\n")
	o_file.write(":var x\n")
	o_file.write(":cnj")

	if (qr == "ur"):
    	    varIndex = int(round((((int(sys.argv[7]) - 1) * int(effectivemaxtime)) + int(sys.argv[8]))/150)) + 1
    	    roleIndex = (((int(sys.argv[7]) - 1) * int(effectivemaxtime)) + int(sys.argv[8]))%150
    	    #notice that index of a tuple starts at 1. Please check it with following code
    	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150

    	    o_file.write(" (= (select " + r2a[varIndex+17] + "[x] %i) true)" % roleIndex)

	    o_file.write("\n\n")


	relField = False
	UA0Field = False
	ruleField = True
	continue
    elif (line == "\n"):
	continue
    if (UA0Field == True):
	#for initial rs
	if (line[0] == 'r'):
	    tok_lst = line.split()

	    w = 1 #0 is for rs  e.g., rs 3 4 > t5 t4	    
	    while w < tok_lst.index('>') :

		k = tok_lst.index('>') + 1
		while k < len(tok_lst) :

		    varIndexb = int(round((((int(tok_lst[w]) - 1) * int(effectivemaxtime)) + int(tok_lst[k][1:]))/150)) + 1
	    
    		    roleIndexb = (((int(tok_lst[w]) - 1) * int(effectivemaxtime)) + int(tok_lst[k][1:]))%150
    		    if (roleIndexb == 0):
       	    		varIndexb = varIndexb - 1
       	    		roleIndexb = 150


		    lstInitRS.append("v" + str(varIndexb) + "_" + str(roleIndexb))

		    k = k + 1
		w = w + 1

	    continue

	#for initial ua
	tok_lst = line.split()
	strRoles = str(tok_lst[1:])
	if (strRoles == currentBlock):
	    currentEndUser = str((tok_lst[0])[1:])
	    continue
	else:
	    if (fblock):
		fblock = False
	    else:
	        UA0User2.append(currentEndUser) #previous end block	
   
	    currentEndUser = str((tok_lst[0])[1:])  #Note: u1 4 3 2 -> identifier not include u:
	    UA0User1.append(currentEndUser) #start new block
	    currentBlock = strRoles
	    currentBlockIndex = currentBlockIndex + 1
	    lstRoles = [] #format v1_3: v1: variable, 3: index	    
	    w = 1 #0 is for user identifier  e.g., u1 3 4 5	    
	    while w < tok_lst.index('>') :

		k = tok_lst.index('>') + 1
		while k < len(tok_lst) :

		    varIndexb = int(round((((int(tok_lst[w]) - 1) * int(effectivemaxtime)) + int(tok_lst[k][1:]))/150)) + 1
	    
    		    roleIndexb = (((int(tok_lst[w]) - 1) * int(effectivemaxtime)) + int(tok_lst[k][1:]))%150
    		    if (roleIndexb == 0):
       	    		varIndexb = varIndexb - 1
       	    		roleIndexb = 150


		    lstRoles.append("v" + str(varIndexb) + "_" + str(roleIndexb))

		    k = k + 1
		w = w + 1


	    w = 1
	    declareBlock = []
	    while w<=numOfVars :
		strDeclare = strDeclare + ":smt (define i" + str(w) + "_" + str(currentBlockIndex) + "::uat (mk-tuple"
		iw = 1
		while (iw <=150):
		    if (("v" + str(w) + "_" +str(iw)) in lstRoles): 
			strDeclare = strDeclare + " true"
		    else:
			strDeclare = strDeclare + " false"

		    iw = iw + 1
		strDeclare = strDeclare + " ))\n\n"

	        w = w + 1


	continue
 
   
    isAsgnorRevk = False   #is this action is can_revoke or assign
    if (line =="\n"):
	break
    tok_lst = line.split()
    o_file.write("\n")
    o_file.write(":comment %i\n" % tr)
    tr=tr+1
    o_file.write(":transition\n")
    o_file.write(":var x\n")
    if ((tok_lst[0] == "can_assign") or (tok_lst[0] == "can_assign_h") or (tok_lst[0] == "can_revoke")):
	isAsgnorRevk = True
	o_file.write(":var y\n")
    else:
	o_file.write(":var y\n")
    o_file.write(":var j\n")

    ###Print guard
    if (tok_lst[1][0] == "t"):
	o_file.write(":guard (= z[y] " + tok_lst[3][1:] + ") ")
    elif (tok_lst[1][0] == "f"):
	o_file.write(":guard (not (= y y)) (= z[y] " + tok_lst[3][1:] + ") ")
    else :
    	varIndexG = int(round((((int(tok_lst[1]) - 1) * int(effectivemaxtime)) + int(tok_lst[3][1:]))/150)) + 1
	    
    	roleIndexG = (((int(tok_lst[1]) - 1) * int(effectivemaxtime)) + int(tok_lst[3][1:]))%150
    	if (roleIndexG == 0):
       	    varIndexG = varIndexG - 1
       	    roleIndexG = 150
    
   	o_file.write(":guard (= z[y] " + tok_lst[3][1:] + ") (= (select " + r2a[varIndexG+17] + "[y] " + str(roleIndexG) + ") true) (= (select " + r2a[varIndexG + 34] + "[y] " + str(roleIndexG) + ") true) ")
    


    #####

    update=0
    
    #13-6-2013: can_assign adminrole , t1 , 1 2 -3 ; t3 , 6 : at this time (13/6/2013) consider t3 contains only 1 time slot and adminrole has only 1 positive role
    #can_revoke adminrole , t1 , true ; t3 , 6 : at this time (13/6/2013) consider t3 contains only 1 time slot
    asgtimeindex = tok_lst.index(";")
    asgtime = tok_lst[asgtimeindex + 1]
    can_assign = -1
    can_enable = -1
    blockIndex = [] #contain the index cariable, For multi-target roles
    blockUpdateReal = [] #update values string, For multi-target roles
    blockUpdateImpl = []
    for i,tok in enumerate(tok_lst): 
		
        if (i==0 and tok=="can_assign") : 
	    can_assign=1
	elif (i==0 and tok=="can_assign_h") : 	    
	    can_assign=2
        elif (i==0 and tok=="can_revoke") : 	    
	    can_assign=0
	elif (i==0 and tok=="can_enable") : 	    
	    can_enable=1
	elif (i==0 and tok=="can_disable") : 	    
	    can_enable=0
	elif (i>0 and tok==";") : 
            update = update + 1
        elif (i>0 and tok==",") : 
            update = update + 1
	    if (update == 4):
	    	o_file.write("\n")
	    	o_file.write(":numcases 3\n")
            	o_file.write(":case (= x j)\n")
        
        elif (i>0 and update==2 and tok[0]=='f') : 
            o_file.write(" (not (= x x)) ")
	elif (i>0 and update==2 and tok[0]=='t') : 
            o_file.write(" (= x x) ")
        elif (i>0 and update==2 and tok[0]=='-') :
	    varIndex = int(round((((int(tok[1:]) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    
    	    roleIndex = (((int(tok[1:]) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
    	    #notice that index of a tuple starts at 1. Please check it with following code
    	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150

	    if (isAsgnorRevk == False): #this is can_enable or disable action
		varIndex = varIndex + 34 #start from A
	    else:
		varIndex = varIndex + 17

 	    o_file.write(" (= (select " + r2a[varIndex] + "[x] %i) false)" % roleIndex)
            
        elif (i>0 and update==2 and tok[0]!='-') : 
	    varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
    	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
    	    #notice that index of a tuple starts at 1. Please check it with following code
    	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150

	    if (isAsgnorRevk == False): #this is can_enable or disable action
		varIndex = varIndex + 34 #start from A
	    else:
		varIndex = varIndex + 17

 	    o_file.write(" (= (select " + r2a[varIndex] + "[x] %i) true)" % roleIndex)

            
        elif (i>0 and update==4 and can_assign==1) : 
	    #can_assign has multiple if needed (only for can_assign, not can_revoke yet)
	    varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
		
	    #For multiple target roles
	    if (str(varIndex) in blockIndex):
		bIndex = blockIndex.index(str(varIndex))
		oldStr = blockUpdateReal[bIndex]
		oldStr = "(update " + oldStr + " " + str(roleIndex) + " true)"
		blockUpdateReal[bIndex] = oldStr

		oldStr = blockUpdateImpl[bIndex]
		oldStr = "(update " + oldStr + " " + str(roleIndex) + " true)"
		blockUpdateImpl[bIndex] = oldStr

	    else: 
		blockIndex.append(str(varIndex))
		blockUpdateReal.append("(update " + r2a[varIndex] + "[j] " + str(roleIndex) + " true)")
		blockUpdateImpl.append("(update " + r2a[varIndex+17] + "[j] " + str(roleIndex) + " true)")

	    ###Previous version: that is for single target role
	    #j = 1
    	    #while j<=numOfVars :
		#if (j == varIndex) :
  	    	#    o_file.write(" :val " + "(update " + r2a[j] + "[j] " + str(roleIndex) + " true)" + " \n")
		#else:
            	#    o_file.write(" :val " + r2a[j] + "[j] \n")
		#j = j + 1
	    #For implicit 16-04-2014
	    #j = 1
    	    #while j<=numOfVars :
		#if (j == varIndex) :
  	    	#    o_file.write(" :val " + "(update " + r2a[j+17] + "[j] " + str(roleIndex) + " true)" + " \n")
		#else:
            	#    o_file.write(" :val " + r2a[j+17] + "[j] \n")
		#j = j + 1

	    ##Nothing for Role enabling RS
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		#j = j + 1

	    #o_file.write(" :val z[j] \n")
	   
	    #o_file.write(":case (= y j)\n")
	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j] + "[j] \n")
		#j=j+1
	    #For implicit
	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j+17] + "[j] \n")
		#j=j+1
	    ##Nothing for Role enabling RS
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		#j = j + 1

	    #o_file.write(" :val z[j] \n")


    	    #o_file.write(":case \n")
    	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j] + "[j] \n")
		#j=j+1
	    #For implicit
	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j+17] + "[j] \n")
		#j=j+1

	    ##Nothing for Role enabling RS
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		#j = j + 1

	    #o_file.write(" :val z[j] \n")

	elif (i>0 and update==4 and can_assign==2) : #16-04-2014 For Implicit, only update 'implicit TUA' 
	    #can_assign has only 1 target role
	    varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
		
	    #For multiple target roles
	    if (str(varIndex) in blockIndex):
		bIndex = blockIndex.index(str(varIndex))
		
		oldStr = blockUpdateImpl[bIndex]
		oldStr = "(update " + oldStr + " " + str(roleIndex) + " true)"
		blockUpdateImpl[bIndex] = oldStr

	    else: 
		blockIndex.append(str(varIndex))
		blockUpdateImpl.append("(update " + r2a[varIndex+17] + "[j] " + str(roleIndex) + " true)")


	    ###Previous version: that is for single target role
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j] + "[j] \n")
		#j = j + 1
	    #For implicit 16-04-2014
	    #j = 1
    	    #while j<=numOfVars :
		#if (j == varIndex) :
  	    	#    o_file.write(" :val " + "(update " + r2a[j+17] + "[j] " + str(roleIndex) + " true)" + " \n")
		#else:
            	#    o_file.write(" :val " + r2a[j+17] + "[j] \n")
		#j = j + 1

	    ##Nothing for Role enabling RS
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		#j = j + 1

	    #o_file.write(" :val z[j] \n")
	   
	    #o_file.write(":case (= y j)\n")
	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j] + "[j] \n")
		#j=j+1
	    #For implicit
	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j+17] + "[j] \n")
		#j=j+1
	    ##Nothing for Role enabling RS
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		#j = j + 1

	    #o_file.write(" :val z[j] \n")


    	    #o_file.write(":case \n")
    	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j] + "[j] \n")
		#j=j+1
	    #For implicit
	    #j = 1
    	    #while j<=numOfVars :
        	#o_file.write(" :val " + r2a[j+17] + "[j] \n")
		#j=j+1

	    ##Nothing for Role enabling RS
	    #j = 1
    	    #while j<=numOfVars :
		#o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		#j = j + 1

	    #o_file.write(" :val z[j] \n")


	elif (i>0 and update==4 and can_assign==0) : #16-04-2014: Assign Implicit TUA to real TUA when revoking some roles
            varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
		
	    j = 1
    	    while j<=numOfVars :
		if (j == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j] + "[j] " + str(roleIndex) + " false)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1

	    #For implicit 16-04-2014, assign to real TUA
	    j = 1
    	    while j<=numOfVars :
		if (j == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j] + "[j] " + str(roleIndex) + " false)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1

	    ##Nothing for Role enabling RS
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1

	    o_file.write(" :val z[j] \n")


	    o_file.write(":case (= y j)\n")
    	    j = 1
    	    while j<=numOfVars :
        	o_file.write(" :val " + r2a[j] + "[j] \n")
		j=j+1

	    #For implicit TUA
	    j = 1
    	    while j<=numOfVars :
        	o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j=j+1

	    ##Nothing for Role enabling RS
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    o_file.write(" :val z[j] \n")



    	    o_file.write(":case \n")
    	    j = 1
    	    while j<=numOfVars :
        	o_file.write(" :val " + r2a[j] + "[j] \n")
		j=j+1
	    #For implicit TUA
	    j = 1
    	    while j<=numOfVars :
        	o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j=j+1
	    ##Nothing for Role enabling RS
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    o_file.write(" :val z[j] \n")
	elif (i>0 and update==4 and can_enable==1) : 
	    #can_enable has only 1 target role
	    varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
	    varIndex = varIndex + 34  #start from A

	    ##Nothing for TUA
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1
	
	    j = 1
    	    while j<=numOfVars :
		if ((j + 34) == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j + 34] + "[j] " + str(roleIndex) + " true)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    
	    o_file.write(" :val z[j] \n")


	    o_file.write(":case (= y j)\n")
	    ##Nothing for TUA
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1
	    #have to update all role enabling
    	    j = 1
    	    while j<=numOfVars :
        	if ((j + 34) == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j + 34] + "[j] " + str(roleIndex) + " true)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    
	    o_file.write(" :val z[j] \n")




    	    o_file.write(":case \n")
	    ##Nothing for TUA
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1
	    #have to update all role enabling
    	    j = 1
    	    while j<=numOfVars :
        	if ((j + 34) == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j + 34] + "[j] " + str(roleIndex) + " true)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    
	    o_file.write(" :val z[j] \n")

	elif (i>0 and update==4 and can_enable==0) : 
            varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150

	    varIndex = varIndex + 34  #start from A
	    ##Nothing for TUA
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1

	    j = 1
    	    while j<=numOfVars :
		if ((j + 34) == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j + 34] + "[j] " + str(roleIndex) + " false)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    
	    o_file.write(" :val z[j] \n")


	    o_file.write(":case (= y j)\n")
	    ##Nothing for TUA
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1

	    #have to update all role enabling
    	    j = 1
    	    while j<=numOfVars :
		if ((j + 34) == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j + 34] + "[j] " + str(roleIndex) + " false)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    
	    o_file.write(" :val z[j] \n")



    	    o_file.write(":case \n")
	    ##Nothing for TUA
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    j = 1
    	    while j<=numOfVars :
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
		j = j + 1
	    #have to update all role enabling
    	    j = 1
    	    while j<=numOfVars :
		if ((j + 34) == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j + 34] + "[j] " + str(roleIndex) + " false)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
		j = j + 1
	    
	    o_file.write(" :val z[j] \n")
    

    #Porcess for multiple-target roles
    if (can_assign == 1 or can_assign == 2):
	j = 1
    	while j<=numOfVars :
	    if (str(j) in blockIndex and can_assign == 1):
	        o_file.write(" :val " + blockUpdateReal[blockIndex.index(str(j))] + " \n")
	    else:
		o_file.write(" :val " + r2a[j] + "[j] \n")
	    j = j + 1

	#For implicit 16-04-2014
	j = 1
    	while j<=numOfVars :
	    if (str(j) in blockIndex):
	        o_file.write(" :val " + blockUpdateImpl[blockIndex.index(str(j))] + " \n")
	    else:
		o_file.write(" :val " + r2a[j+17] + "[j] \n")
	    j = j + 1

	##Nothing for Role enabling RS
	j = 1
    	while j<=numOfVars :
	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
	    j = j + 1

	o_file.write(" :val z[j] \n")
	   
	o_file.write(":case (= y j)\n")
	j = 1
    	while j<=numOfVars :
            o_file.write(" :val " + r2a[j] + "[j] \n")
	    j=j+1
	#For implicit
	j = 1
    	while j<=numOfVars :
            o_file.write(" :val " + r2a[j+17] + "[j] \n")
	    j=j+1
	##Nothing for Role enabling RS
	j = 1
    	while j<=numOfVars :
	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
	    j = j + 1

	o_file.write(" :val z[j] \n")


    	o_file.write(":case \n")
    	j = 1
    	while j<=numOfVars :
            o_file.write(" :val " + r2a[j] + "[j] \n")
	    j=j+1
	#For implicit
	j = 1
    	while j<=numOfVars :
            o_file.write(" :val " + r2a[j+17] + "[j] \n")
	    j=j+1

	##Nothing for Role enabling RS
	j = 1
    	while j<=numOfVars :
	    o_file.write(" :val " + r2a[j + 34] + "[j] \n")
	    j = j + 1

	o_file.write(" :val z[j] \n")

#Time passing
print "Note: Using agtrbac2mcmt1.py - with e.g., (= z[x] 1) then 2 ..."
print

tj=1
while tj <= int(maxtime) :

    o_file.write("\n:comment %i\n" % tr)
    tr=tr+1
    o_file.write(":transition\n")
    o_file.write(":var x\n")
    o_file.write(":var j\n")
    o_file.write(":guard (= z[x] " + str(tj)+ ")")
    o_file.write("\n")
    o_file.write(":numcases 2\n")
    o_file.write(":case (= x j)\n")
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j] + "[j] \n")
    	j=j+1
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j+17] + "[j] \n")
    	j=j+1
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j + 34] + "[j] \n")
    	j=j+1

    if (tj < int(maxtime)):
    	o_file.write(" :val " + str(tj + 1)+ "\n")
    else:
    	o_file.write(" :val 1\n")
    o_file.write(":case\n")
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j] + "[j] \n")
    	j=j+1
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j+17] + "[j] \n")
    	j=j+1
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j + 34] + "[j] \n")
    	j=j+1

    if (tj < int(maxtime)):
    	o_file.write(" :val " + str(tj + 1)+ "\n")
    else:
    	o_file.write(" :val 1\n")
    tj = tj + 1


i_file.close()
o_file.close()

