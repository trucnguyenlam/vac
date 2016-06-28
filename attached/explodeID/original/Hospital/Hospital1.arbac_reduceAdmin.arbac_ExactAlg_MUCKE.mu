/********************************************************/
/******                DECLARATION                *******/
/********************************************************/
class ThreadID {
    bool b1;
    bool b2;
    bool b3;
    bool b4;
};

class Roles {
    bool Doctor;
    bool Receptionist;
    bool target;
    bool SUPER_ROLE;
};

/*---------- INIT GLOBAL VARIABLES ---------*/
bool GlobalInit(
   Roles g
)
(true 
& g.SUPER_ROLE=true);
#size GlobalInit;

/*---------- INIT LOCAL VARIABLES ---------*/
bool LocalInit(
   ThreadID t,
   Roles l
)
  t < l
(false 
| ((/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0)& l.Doctor=false& l.Receptionist=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0)& l.Doctor=true& l.Receptionist=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=2 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0)& l.Doctor=true& l.Receptionist=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=3 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0)& l.Doctor=false& l.Receptionist=false& l.target=false& l.SUPER_ROLE=true)
| ((/* pc=4 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0)& l.Doctor=false& l.Receptionist=false& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=5 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0)& l.Doctor=false& l.Receptionist=true& l.target=false& l.SUPER_ROLE=false)
| ((/* pc=6 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0)& l.Doctor=false& l.Receptionist=true& l.target=false& l.SUPER_ROLE=false)
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
		// <SUPER_ROLE,Receptionist&Doctor,target>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Receptionist=true & cL.Doctor=true & cL.target=false) & /* Applying this rule */
 (dL.target=true)
/* Copy variables */
& (dL.Doctor=cL.Doctor)& (dL.Receptionist=cL.Receptionist)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 1 -----------------
		// <SUPER_ROLE,-Doctor,Receptionist>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Doctor=false & cL.Receptionist=false) & /* Applying this rule */
 (dL.Receptionist=true)
/* Copy variables */
& (dL.Doctor=cL.Doctor)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
		//------------------ CAN_ASSIGN RULE NUMBER 2 -----------------
		// <SUPER_ROLE,-Receptionist,Doctor>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.Receptionist=false & cL.Doctor=false) & /* Applying this rule */
 (dL.Doctor=true)
/* Copy variables */
& (dL.Receptionist=cL.Receptionist)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE))
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
		// <SUPER_ROLE,Receptionist>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.SUPER_ROLE=true & cL.Receptionist=true) & /* apply this rule */
(dL.Receptionist=false)
/* Copy variables */
& (dL.Doctor=cL.Doctor)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
		//------------------- CAN_REVOKE RULE NUMBER 1 ---------------------
		// <SUPER_ROLE,Doctor>
		//------------------------------------------------------------------
| ( /* condition */
 (cG.SUPER_ROLE=true & cL.Doctor=true) & /* apply this rule */
(dL.Doctor=false)
/* Copy variables */
& (dL.Receptionist=cL.Receptionist)& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dG.SUPER_ROLE=cG.SUPER_ROLE))
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
| ((/* pc=0 */ s.b1=0 & s.b2=0 & s.b3=0 & s.b4=0) & (/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0 & t.b4=0))
| ((/* pc=1 */ s.b1=1 & s.b2=0 & s.b3=0 & s.b4=0) & (/* pc=2 */ t.b1=0 & t.b2=1 & t.b3=0 & t.b4=0))
| ((/* pc=2 */ s.b1=0 & s.b2=1 & s.b3=0 & s.b4=0) & (/* pc=3 */ t.b1=1 & t.b2=1 & t.b3=0 & t.b4=0))
| ((/* pc=3 */ s.b1=1 & s.b2=1 & s.b3=0 & s.b4=0) & (/* pc=4 */ t.b1=0 & t.b2=0 & t.b3=1 & t.b4=0))
| ((/* pc=4 */ s.b1=0 & s.b2=0 & s.b3=1 & s.b4=0) & (/* pc=5 */ t.b1=1 & t.b2=0 & t.b3=1 & t.b4=0))
| ((/* pc=5 */ s.b1=1 & s.b2=0 & s.b3=1 & s.b4=0) & (/* pc=6 */ t.b1=0 & t.b2=1 & t.b3=1 & t.b4=0))
| ((/* pc=6 */ s.b1=0 & s.b2=1 & s.b3=1 & s.b4=0) & (/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0 & t.b4=0))
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



