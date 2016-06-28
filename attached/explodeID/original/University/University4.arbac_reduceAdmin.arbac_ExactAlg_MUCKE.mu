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
    bool b7;
};

class Roles {
    bool AdmissionsOfficer;
    bool AssistantProf;
    bool AssociateProf;
    bool Dean;
    bool DeanOfAdmissions;
    bool DeptChair;
    bool GradAdmissionsCommittee;
    bool Lecturer;
    bool President;
    bool Professor;
    bool Provost;
    bool target;
    bool SUPER_ROLE;
};

/*---------- INIT GLOBAL VARIABLES ---------*/
bool GlobalInit(
   Roles g
)
(true 
& g.SUPER_ROLE=true& g.DeptChair=true& g.President=false& g.Provost=true& g.Dean=true);
#size GlobalInit;

/*---------- INIT LOCAL VARIABLES ---------*/
bool LocalInit(
   ThreadID t,
   Roles l
)
  t < l
(false 
| ((/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=true& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=2 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=true& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=true)
| ((/* pc=3 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=true& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=4 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=5 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=true& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=6 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=7 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=true& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=8 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=true& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=9 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=true& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=10 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=true& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=11 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=true& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=12 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=true& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=13 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=true& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=14 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=15 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=16 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=17 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=18 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=19 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=true& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=20 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=true& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=21 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=true& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=22 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=true& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=23 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=true& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=24 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=true& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=25 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=true& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=26 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=true& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=27 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=true& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=28 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=true& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=29 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=true& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=30 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=true& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=31 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=true& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=32 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=33 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=34 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=35 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0)& l.AdmissionsOfficer=false& l.AssistantProf=false& l.AssociateProf=false& l.Dean=false& l.DeanOfAdmissions=false& l.DeptChair=false& l.GradAdmissionsCommittee=false& l.Lecturer=false& l.President=false& l.Professor=false& l.Provost=false& l.target=false& l.SUPER_ROLE=false)
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
		// <SUPER_ROLE,GradAdmissionsCommittee&AdmissionsOfficer,target>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.GradAdmissionsCommittee=true & cL.AdmissionsOfficer=true & cL.target=false) & /* Applying this rule */
 (dL.target=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 1 -----------------
		// <President,TRUE,Professor>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=false) & /* Applying this rule */
 (dL.Professor=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 2 -----------------
		// <President,TRUE,DeanOfAdmissions>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.DeanOfAdmissions=false) & /* Applying this rule */
 (dL.DeanOfAdmissions=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 3 -----------------
		// <President,TRUE,Lecturer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Lecturer=false) & /* Applying this rule */
 (dL.Lecturer=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 4 -----------------
		// <President,TRUE,AssistantProf>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.AssistantProf=false) & /* Applying this rule */
 (dL.AssistantProf=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 5 -----------------
		// <President,TRUE,AssociateProf>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.AssociateProf=false) & /* Applying this rule */
 (dL.AssociateProf=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 6 -----------------
		// <Dean,Professor&-Dean&-President&-Provost,DeptChair>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.Professor=true & cL.Dean=false & cL.President=false & cL.Provost=false & cL.DeptChair=false) & /* Applying this rule */
 (dL.DeptChair=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 7 -----------------
		// <SUPER_ROLE,DeanOfAdmissions&-GradAdmissionsCommittee,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.DeanOfAdmissions=true & cL.GradAdmissionsCommittee=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 8 -----------------
		// <SUPER_ROLE,Provost&-GradAdmissionsCommittee,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Provost=true & cL.GradAdmissionsCommittee=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 9 -----------------
		// <SUPER_ROLE,DeanOfAdmissions&-President,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.DeanOfAdmissions=true & cL.President=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 10 -----------------
		// <SUPER_ROLE,Provost&-President,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Provost=true & cL.President=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 11 -----------------
		// <DeptChair,AssistantProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.AssistantProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 12 -----------------
		// <DeptChair,Lecturer&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.Lecturer=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 13 -----------------
		// <DeptChair,AssociateProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.AssociateProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 14 -----------------
		// <DeptChair,Professor&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.Professor=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 15 -----------------
		// <DeptChair,Dean&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.Dean=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 16 -----------------
		// <DeptChair,DeptChair&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.DeptChair=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 17 -----------------
		// <DeptChair,Provost&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.DeptChair=true & cL.Provost=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 18 -----------------
		// <President,Professor&-Dean&-DeptChair&-President,Provost>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.Dean=false & cL.DeptChair=false & cL.President=false & cL.Provost=false) & /* Applying this rule */
 (dL.Provost=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 19 -----------------
		// <Provost,Professor&-DeptChair&-President&-Provost,Dean>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Professor=true & cL.DeptChair=false & cL.President=false & cL.Provost=false & cL.Dean=false) & /* Applying this rule */
 (dL.Dean=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 20 -----------------
		// <Provost,Professor&-Dean&-President&-Provost,DeptChair>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Professor=true & cL.Dean=false & cL.President=false & cL.Provost=false & cL.DeptChair=false) & /* Applying this rule */
 (dL.DeptChair=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 21 -----------------
		// <President,Professor&-Dean&-President&-Provost,DeptChair>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.Dean=false & cL.President=false & cL.Provost=false & cL.DeptChair=false) & /* Applying this rule */
 (dL.DeptChair=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 22 -----------------
		// <Provost,DeanOfAdmissions&-GradAdmissionsCommittee,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.DeanOfAdmissions=true & cL.GradAdmissionsCommittee=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 23 -----------------
		// <President,DeanOfAdmissions&-GradAdmissionsCommittee,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.DeanOfAdmissions=true & cL.GradAdmissionsCommittee=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 24 -----------------
		// <Provost,Provost&-GradAdmissionsCommittee,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Provost=true & cL.GradAdmissionsCommittee=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 25 -----------------
		// <President,Provost&-GradAdmissionsCommittee,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Provost=true & cL.GradAdmissionsCommittee=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 26 -----------------
		// <Provost,DeanOfAdmissions&-President,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.DeanOfAdmissions=true & cL.President=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 27 -----------------
		// <President,DeanOfAdmissions&-President,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.DeanOfAdmissions=true & cL.President=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 28 -----------------
		// <Provost,Provost&-President,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Provost=true & cL.President=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 29 -----------------
		// <President,Provost&-President,AdmissionsOfficer>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Provost=true & cL.President=false & cL.AdmissionsOfficer=false) & /* Applying this rule */
 (dL.AdmissionsOfficer=true)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 30 -----------------
		// <Dean,AssistantProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.AssistantProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 31 -----------------
		// <Provost,AssistantProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.AssistantProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 32 -----------------
		// <President,AssistantProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.AssistantProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 33 -----------------
		// <Dean,Lecturer&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.Lecturer=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 34 -----------------
		// <Provost,Lecturer&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Lecturer=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 35 -----------------
		// <President,Lecturer&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Lecturer=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 36 -----------------
		// <Dean,AssociateProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.AssociateProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 37 -----------------
		// <Provost,AssociateProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.AssociateProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 38 -----------------
		// <President,AssociateProf&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.AssociateProf=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 39 -----------------
		// <Dean,Professor&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.Professor=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 40 -----------------
		// <Provost,Professor&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Professor=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 41 -----------------
		// <President,Professor&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 42 -----------------
		// <Dean,Dean&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.Dean=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 43 -----------------
		// <Provost,Dean&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Dean=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 44 -----------------
		// <President,Dean&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Dean=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 45 -----------------
		// <Dean,DeptChair&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.DeptChair=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 46 -----------------
		// <Provost,DeptChair&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.DeptChair=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 47 -----------------
		// <President,DeptChair&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.DeptChair=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 48 -----------------
		// <Dean,Provost&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Dean=true & cL.Provost=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 49 -----------------
		// <Provost,Provost&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.Provost=true & cL.Provost=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 50 -----------------
		// <President,Provost&-President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Provost=true & cL.President=false & cL.GradAdmissionsCommittee=false) & /* Applying this rule */
 (dL.GradAdmissionsCommittee=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 51 -----------------
		// <President,Professor&-DeptChair&-President&-Provost,Dean>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.President=true & cL.Professor=true & cL.DeptChair=false & cL.President=false & cL.Provost=false & cL.Dean=false) & /* Applying this rule */
 (dL.Dean=true)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
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
		// <SUPER_ROLE,AdmissionsOfficer>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.SUPER_ROLE=true & cL.AdmissionsOfficer=true) & /* apply this rule */
(dL.AdmissionsOfficer=false)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 1 ---------------------
		// <DeptChair,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.DeptChair=true & cL.GradAdmissionsCommittee=true) & /* apply this rule */
(dL.GradAdmissionsCommittee=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 2 ---------------------
		// <President,DeanOfAdmissions>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.DeanOfAdmissions=true) & /* apply this rule */
(dL.DeanOfAdmissions=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 3 ---------------------
		// <President,Lecturer>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Lecturer=true) & /* apply this rule */
(dL.Lecturer=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 4 ---------------------
		// <President,AssistantProf>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.AssistantProf=true) & /* apply this rule */
(dL.AssistantProf=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 5 ---------------------
		// <President,AssociateProf>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.AssociateProf=true) & /* apply this rule */
(dL.AssociateProf=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 6 ---------------------
		// <President,Professor>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Professor=true) & /* apply this rule */
(dL.Professor=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 7 ---------------------
		// <President,Provost>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Provost=true) & /* apply this rule */
 (dL.Provost=false & dG.Provost=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 8 ---------------------
		// <Provost,Dean>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.Dean=true) & /* apply this rule */
 (dL.Dean=false & dG.Dean=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost))
		//------------------- CAN_REVOKE RULE NUMBER 9 ---------------------
		// <Dean,DeptChair>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Dean=true & cL.DeptChair=true) & /* apply this rule */
 (dL.DeptChair=false & dG.DeptChair=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 10 ---------------------
		// <Provost,AdmissionsOfficer>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.AdmissionsOfficer=true) & /* apply this rule */
(dL.AdmissionsOfficer=false)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 11 ---------------------
		// <President,AdmissionsOfficer>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.AdmissionsOfficer=true) & /* apply this rule */
(dL.AdmissionsOfficer=false)
/* Copy variables */
& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 12 ---------------------
		// <Dean,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Dean=true & cL.GradAdmissionsCommittee=true) & /* apply this rule */
(dL.GradAdmissionsCommittee=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 13 ---------------------
		// <Provost,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.GradAdmissionsCommittee=true) & /* apply this rule */
(dL.GradAdmissionsCommittee=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 14 ---------------------
		// <President,GradAdmissionsCommittee>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.GradAdmissionsCommittee=true) & /* apply this rule */
(dL.GradAdmissionsCommittee=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 15 ---------------------
		// <President,Dean>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.Dean=true) & /* apply this rule */
 (dL.Dean=false & dG.Dean=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.DeptChair=cL.DeptChair)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.DeptChair=cG.DeptChair)& (dG.President=cG.President)& (dG.Provost=cG.Provost))
		//------------------- CAN_REVOKE RULE NUMBER 16 ---------------------
		// <Provost,DeptChair>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.Provost=true & cL.DeptChair=true) & /* apply this rule */
 (dL.DeptChair=false & dG.DeptChair=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
		//------------------- CAN_REVOKE RULE NUMBER 17 ---------------------
		// <President,DeptChair>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.President=true & cL.DeptChair=true) & /* apply this rule */
 (dL.DeptChair=false & dG.DeptChair=false)
/* Copy variables */
& (dL.AdmissionsOfficer=cL.AdmissionsOfficer)& (dL.AssistantProf=cL.AssistantProf)& (dL.AssociateProf=cL.AssociateProf)& (dL.Dean=cL.Dean)& (dL.DeanOfAdmissions=cL.DeanOfAdmissions)& (dL.GradAdmissionsCommittee=cL.GradAdmissionsCommittee)& (dL.Lecturer=cL.Lecturer)& (dL.President=cL.President)& (dL.Professor=cL.Professor)& (dL.Provost=cL.Provost)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE)& (dG.President=cG.President)& (dG.Provost=cG.Provost)& (dG.Dean=cG.Dean))
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
& (dG.SUPER_ROLE=cG.SUPER_ROLE|cL.SUPER_ROLE)
& (dG.DeptChair=cG.DeptChair|cL.DeptChair)
& (dG.President=cG.President|cL.President)
& (dG.Provost=cG.Provost|cL.Provost)
& (dG.Dean=cG.Dean|cL.Dean)
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
| ((/* pc=0 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=1 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=2 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=2 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=3 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=3 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=4 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=4 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=5 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=5 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=6 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=6 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=7 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=7 */ s.b1=1 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=8 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=8 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=9 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=9 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=10 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=10 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=11 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=11 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=12 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=12 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=13 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=13 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=14 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=14 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=15 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=0 & t.b6=0 & t.b7=0))
| ((/* pc=15 */ s.b1=1 & s.b2=1 & s.b3=1 & s.b4=1 & s.b5=0 & s.b6=0 & s.b7=0) & (/* pc=16 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=16 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=17 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=17 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=18 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=18 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=19 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=19 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=20 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=20 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=21 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=21 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=22 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=22 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=23 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=0 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=23 */ s.b1=1 & s.b2=1 & s.b3=1 & s.b4=0 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=24 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=24 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=25 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=25 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=26 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=26 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=27 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=27 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=28 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=28 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=29 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=29 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=30 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=30 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=31 */ t.b1=1 & t.b2=1 & t.b3=1 & t.b4=1 & t.b5=1 & t.b6=0 & t.b7=0))
| ((/* pc=31 */ s.b1=1 & s.b2=1 & s.b3=1 & s.b4=1 & s.b5=1 & s.b6=0 & s.b7=0) & (/* pc=32 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0))
| ((/* pc=32 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=1 & s.b7=0) & (/* pc=33 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0))
| ((/* pc=33 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=1 & s.b7=0) & (/* pc=34 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0))
| ((/* pc=34 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=1 & s.b7=0) & (/* pc=35 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=1 & t.b7=0))
| ((/* pc=35 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=0 & s.b5=0 & s.b6=1 & s.b7=0) & (/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0 & t.b5=0 & t.b6=0 & t.b7=0))
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



