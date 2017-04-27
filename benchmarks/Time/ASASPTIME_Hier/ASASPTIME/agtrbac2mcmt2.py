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

j = 1
while j<=numOfVars :
    o_file.write(":local " + r2a[j] + " uat \n")
    j=j+1
o_file.write("\n")
  
o_file.write(":global t real \n")  #global clock
o_file.write("\n")


o_file.write(":initial\n")
o_file.write(":var x\n")
o_file.write(":cnj (= t[x] 1) ")

j = 1
while j<=numOfVars :
    o_file.write("(= " + r2a[j] + "[x] all_false) ")
    j=j+1


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

    o_file.write(" (= (select " + r2a[varIndex] + "[x] %i) true)" % roleIndex)

o_file.write("\n")


i_file.seek(0, 0)
tr=1
for line in i_file:
    if (line =="\n"):
	break
    tok_lst = line.split()
    o_file.write("\n")
    o_file.write(":comment %i\n" % tr)
    tr=tr+1
    o_file.write(":transition\n")
    o_file.write(":var x\n")
    o_file.write(":var j\n")
    o_file.write(":guard ")
    
    update=0
    
    #can_assign t1 t2 , 1 2 -3 ; t3 , 6 : at this time (22/5/2013) consider t3 contains only 1 time slot
    #can_revoke t1 t2 , true ; t3 , 6 : at this time (22/5/2013) consider t3 contains only 1 time slot
    asgtimeindex = tok_lst.index(";")
    asgtime = tok_lst[asgtimeindex + 1]
    time_constraint = ''
    numtc = 0  # Number of time_constraints
    for i,tok in enumerate(tok_lst): 
		
        if (i==0 and tok=="can_assign") : 
	    can_assign=1
        elif (i==0 and tok=="can_revoke") : 	    
	    can_assign=0
	elif (i>0 and tok==";") : 
            update = update + 1
        elif (i>0 and tok==",") : 
            update = update + 1
	    if (update == 1):
		
		if (numtc > 1):		    
		    o_file.write("(or " + time_constraint + ") ")
		else:
		    o_file.write(time_constraint)
	    elif (update == 3):
	    	o_file.write("\n")
	    	o_file.write(":numcases 2\n")
            	o_file.write(":case (= x j)\n")
        elif (i>0 and update==0 and tok[0]=='t') : 
	    numtc = numtc + 1
            time_constraint = time_constraint + "(= t[x] " + tok[1:] + ") "
        elif (i>0 and update==1 and tok[0]=='f') : 
            o_file.write(" (not (= x x)) ")
	elif (i>0 and update==1 and tok[0]=='t') : 
            o_file.write(" (= x x) ")
        elif (i>0 and update==1 and tok[0]=='-') :
	    varIndex = int(round((((int(tok[1:]) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
    	    roleIndex = (((int(tok[1:]) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
    	    #notice that index of a tuple starts at 1. Please check it with following code
    	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
 	    o_file.write(" (= (select " + r2a[varIndex] + "[x] %i) false)" % roleIndex)
            
        elif (i>0 and update==1 and tok[0]!='-') : 
	    varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
    	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
    	    #notice that index of a tuple starts at 1. Please check it with following code
    	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
 	    o_file.write(" (= (select " + r2a[varIndex] + "[x] %i) true)" % roleIndex)

            
        elif (i>0 and update==3 and can_assign==1) : 
	    #can_assign has only 1 target role
	    varIndex = int(round((((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))/150)) + 1
	    roleIndex = (((int(tok) - 1) * int(effectivemaxtime)) + int(asgtime[1:]))%150
	    if (roleIndex == 0):
        	varIndex = varIndex - 1
        	roleIndex = 150
		
	    j = 1
    	    while j<=numOfVars :
		if (j == varIndex) :
  	    	    o_file.write(" :val " + "(update " + r2a[j] + "[j] " + str(roleIndex) + " true)" + " \n")
		else:
            	    o_file.write(" :val " + r2a[j] + "[j] \n")
		j = j + 1
	    o_file.write(" :val t[j] \n")
    	    o_file.write(":case \n")
    	    j = 1
    	    while j<=numOfVars :
        	o_file.write(" :val " + r2a[j] + "[j] \n")
		j=j+1
	    o_file.write(" :val t[j] \n")

	elif (i>0 and update==3 and can_assign==0) : 
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
	    o_file.write(" :val t[j] \n")
    	    o_file.write(":case \n")
    	    j = 1
    	    while j<=numOfVars :
        	o_file.write(" :val " + r2a[j] + "[j] \n")
		j=j+1
	    o_file.write(" :val t[j] \n")



#Time passing
print "Note: Using agtrbac2mcmt2.py - with e.g., (< t[x] 3) then 3 ..."
print

tj=2
while tj <= int(maxtime) :
   
    o_file.write("\n:comment %i\n" % tr)
    tr=tr+1
    o_file.write(":transition\n")
    o_file.write(":var x\n")
    o_file.write(":var j\n")
    o_file.write(":guard (< t[x] " + str(tj)+ ")")
    o_file.write("\n")
    o_file.write(":numcases 2\n")
    o_file.write(":case (= x j)\n")
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j] + "[j] \n")
    	j=j+1

    o_file.write(" :val " + str(tj)+ "\n")
    
    o_file.write(":case\n")
    j = 1
    while j<=numOfVars :
    	o_file.write(" :val " + r2a[j] + "[j] \n")
    	j=j+1

    o_file.write(" :val " + str(tj)+ "\n")
   
    tj = tj + 1

o_file.write("\n:comment %i\n" % tr)
tr=tr+1
o_file.write(":transition\n")
o_file.write(":var x\n")
o_file.write(":var j\n")
o_file.write(":guard (= t[x] " + maxtime +")")
o_file.write("\n")
o_file.write(":numcases 2\n")
o_file.write(":case (= x j)\n")
j = 1
while j<=numOfVars :
    o_file.write(" :val " + r2a[j] + "[j] \n")
    j=j+1
o_file.write(" :val 1\n")
o_file.write(":case\n")
j = 1
while j<=numOfVars :
    o_file.write(" :val " + r2a[j] + "[j] \n")
    j=j+1
o_file.write(" :val 1\n")

i_file.close()
o_file.close()

