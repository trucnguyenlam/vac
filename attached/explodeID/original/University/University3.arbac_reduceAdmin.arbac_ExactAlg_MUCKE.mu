/********************************************************/
/******                DECLARATION                *******/
/********************************************************/
class ThreadID {
    bool b1;
    bool b2;
    bool b3;
    bool b4;
    bool b5;
    bool b6;
};

class Roles {
    bool Dean;
    bool DeptChair;
    bool Grad;
    bool President;
    bool Professor;
    bool Provost;
    bool Undergrad;
    bool target;
    bool SUPER_ROLE;
};

/*---------- INIT GLOBAL VARIABLES ---------*/
bool GlobalInit(
   Roles g
)
(true 
& g.Dean=true& g.President=false& g.Provost=true& g.SUPER_ROLE=true);
#size GlobalInit;

/*---------- INIT LOCAL VARIABLES ---------*/
bool LocalInit(
   ThreadID t,
   Roles l
)
  t < l
(false 
| ((/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=true& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=2 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=true& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=3 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=4 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=true)
| ((/* pc=5 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=6 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=true& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=7 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=8 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=9 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=10 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=11 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=12 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=true& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=13 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=14 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=15 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=16 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=17 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=false& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=18 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=true& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=19 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=true& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=20 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=true& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=21 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=true& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=22 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0)& l.Dean=false& l.DeptChair=false& l.Grad=true& l.President=false& l.Professor=false& l.Provost=false& l.Undergrad=false& l.target=false& l.SUPER_ROLE=false)
);
#size LocalInit;

/*---------- CAN ASSIGN SIMULATION ---------*/
bool CanAssign(
   Roles cL,
   Roles cG,
   Roles dL
)
  cL  ~+  cG,
  cG  ~+  dL
(false 
		//------------------ CAN_ASSIGN RULE NUMBER 0 -----------------
		// <SUPER_ROLE,Undergrad&Grad,target>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Undergrad=true & cL.Grad=true & cL.target=false) & /* Applying this rule */
 (dL.target=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 1 -----------------
		// <President,TRUE,Professor>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=false) & /* Applying this rule */
 (dL.Professor=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 2 -----------------
		// <SUPER_ROLE,-Grad,Undergrad>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Grad=false & cL.Undergrad=false) & /* Applying this rule */
 (dL.Undergrad=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 3 -----------------
		// <SUPER_ROLE,-Undergrad,Grad>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Undergrad=false & cL.Grad=false) & /* Applying this rule */
 (dL.Grad=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 4 -----------------
		// <Dean,Professor&-Dean&-President&-Provost,DeptChair>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.Professor=true & cL.Dean=false & cL.President=false & cL.Provost=false & cL.DeptChair=false) & /* Applying this rule */
 (dL.DeptChair=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 5 -----------------
		// <President,Professor&-Dean&-DeptChair&-President,Provost>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.Dean=false & cL.DeptChair=false & cL.President=false & cL.Provost=false) & /* Applying this rule */
 (dL.Provost=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 6 -----------------
		// <Provost,Professor&-DeptChair&-President&-Provost,Dean>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Professor=true & cL.DeptChair=false & cL.President=false & cL.Provost=false & cL.Dean=false) & /* Applying this rule */
 (dL.Dean=true)
/* Copy variables */
& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 7 -----------------
		// <Provost,-Grad,Undergrad>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Grad=false & cL.Undergrad=false) & /* Applying this rule */
 (dL.Undergrad=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 8 -----------------
		// <President,-Grad,Undergrad>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Grad=false & cL.Undergrad=false) & /* Applying this rule */
 (dL.Undergrad=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 9 -----------------
		// <Provost,Professor&-Dean&-President&-Provost,DeptChair>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Professor=true & cL.Dean=false & cL.President=false & cL.Provost=false & cL.DeptChair=false) & /* Applying this rule */
 (dL.DeptChair=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 10 -----------------
		// <President,Professor&-Dean&-President&-Provost,DeptChair>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.Dean=false & cL.President=false & cL.Provost=false & cL.DeptChair=false) & /* Applying this rule */
 (dL.DeptChair=true)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 11 -----------------
		// <President,Professor&-DeptChair&-President&-Provost,Dean>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.DeptChair=false & cL.President=false & cL.Provost=false & cL.Dean=false) & /* Applying this rule */
 (dL.Dean=true)
/* Copy variables */
& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
);
#size CanAssign;

/*---------- CAN REVOKE SIMULATION ---------*/
bool CanRevoke(
   Roles cL,
   Roles cG,
   Roles dL,
   Roles dG
)
  cL  ~+  cG,
  cG  ~+  dL,
  dL  ~+  dG
(false 
		//------------------- CAN_REVOKE RULE NUMBER 0 ---------------------
		// <Dean,Undergrad>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Dean=true & cL.Undergrad=true) & /* apply this rule */
(dL.Undergrad=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 1 ---------------------
		// <Dean,Grad>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Dean=true & cL.Grad=true) & /* apply this rule */
(dL.Grad=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 2 ---------------------
		// <President,Professor>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Professor=true) & /* apply this rule */
(dL.Professor=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 3 ---------------------
		// <President,Provost>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Provost=true) & /* apply this rule */
 (dL.Provost=false & dG.Provost=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 4 ---------------------
		// <Provost,Dean>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.Dean=true) & /* apply this rule */
 (dL.Dean=false & dG.Dean=false)
/* Copy variables */
& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 5 ---------------------
		// <Dean,DeptChair>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Dean=true & cL.DeptChair=true) & /* apply this rule */
(dL.DeptChair=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 6 ---------------------
		// <Provost,Undergrad>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.Undergrad=true) & /* apply this rule */
(dL.Undergrad=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 7 ---------------------
		// <President,Undergrad>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Undergrad=true) & /* apply this rule */
(dL.Undergrad=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 8 ---------------------
		// <Provost,Grad>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.Grad=true) & /* apply this rule */
(dL.Grad=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 9 ---------------------
		// <President,Grad>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Grad=true) & /* apply this rule */
(dL.Grad=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 10 ---------------------
		// <President,Dean>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Dean=true) & /* apply this rule */
 (dL.Dean=false & dG.Dean=false)
/* Copy variables */
& (dL.DeptChair=cL.DeptChair)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 11 ---------------------
		// <Provost,DeptChair>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.DeptChair=true) & /* apply this rule */
(dL.DeptChair=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 12 ---------------------
		// <President,DeptChair>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.DeptChair=true) & /* apply this rule */
(dL.DeptChair=false)
/* Copy variables */
& (dL.Dean=cL.Dean)& (dL.Grad=cL.Grad)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.Undergrad=cL.Undergrad)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.Dean=cG.Dean)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
);
#size CanRevoke;

/*--- ADMIN ROLE CONSISTENCY ----*/
bool UpdateGlobal(
   Roles cL,
   Roles cG,
   Roles dG
)
  cL  ~+  cG,
  cG  ~+  dG
(true 
& (dG.Dean=cG.Dean|cL.Dean)
& (dG.President=cG.President|cL.President)
& (dG.Provost=cG.Provost|cL.Provost)
& (dG.SUPER_ROLE=cG.SUPER_ROLE|cL.SUPER_ROLE)
);
#size UpdateGlobal;

/*--- REACHABILITY CHECK ----*/
bool targetReach(
   ThreadID t,
   Roles L
)
  t  < L
(true 
& (L.target=true)
);
/*--- THREAD FUNCTIONS ----*/
bool IncreaseThreadID(
   ThreadID s,
   ThreadID t
)
  s  ~+  t
(false 
| ((/* pc=0 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=1 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=2 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=2 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=3 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=3 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=4 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=4 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=5 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=5 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=6 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=6 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=7 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0))
| ((/* pc=7 */ s.b1=1 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0) & (/* pc=8 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=8 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=9 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=9 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=10 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=10 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=11 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=11 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=12 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=12 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=13 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=13 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=14 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=14 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=15 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0))
| ((/* pc=15 */ s.b1=1 & s.b2=1 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0) & (/* pc=16 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=16 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=17 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=17 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=18 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=18 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=19 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=19 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=20 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=20 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=21 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=21 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=22 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0))
| ((/* pc=22 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0) & (/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0))
);
/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/
/******                                                                                    *******/
/******                               Reachability Algorithm                               *******/
/******                                                                                    *******/
/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/

mu bool Reach(
 ThreadID   s_ID,      // Thread ID
 Roles      s_CL,     // Local variable
 Roles      s_G       // Global variable
)
  s_ID     <   s_CL,
  s_CL     ~+  s_G
( false

  // early termination
  | ( exists
         ThreadID   t_ID,
         Roles      t_CL,
         Roles      t_G.
        (   Reach( t_ID, t_CL, t_G )
          & (   targetReach( t_ID, t_CL )
            )
        )
     )

  // initial configuration (init)
  |  ( true
         & GlobalInit(s_G)               // INIT runs FIRST
         & LocalInit(s_ID, s_CL)
     )

  // Move to another thread
  | (   true
         & ( exists
                ThreadID t_ID,
                Roles    t_CL,
                Roles    t_G.
              (   true
                  & IncreaseThreadID( t_ID, s_ID ) // when t_ID=max, s_ID=0
                  & Reach( t_ID, t_CL, s_G )
                  & Reach( s_ID, s_CL, t_G )
              )
          )
    )


//*********************************************************************************/
// forward propagation on internal transitions
//*********************************************************************************/

  | ( true
      & (exists                  // There exists an internal state that
           ThreadID  t_ID,
           Roles     t_CL,
           Roles     t_G.
           (    Reach( t_ID, t_CL, t_G )
               & s_ID = t_ID
               & (
                  ( CanAssign(t_CL, t_G, s_CL)
                    & UpdateGlobal(s_CL, t_G, s_G)
                  )
                  | CanRevoke(t_CL, t_G, s_CL, s_G)
                )
           )
        )
    )

);

#size Reach;


/******************************************************************************************************/
//                                       Reachabibility check                                         *
/******************************************************************************************************/


( exists
    ThreadID t_ID,
    Roles    t_CL,
    Roles    t_G.
    (   Reach( t_ID, t_CL, t_G )
      & targetReach( t_ID, t_CL )
    )
);



