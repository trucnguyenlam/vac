/********************************************************/
/******                DECLARATION                *******/
/********************************************************/
class ThreadID {
    bool b1;
    bool b2;
    bool b3;
};

class Roles {
    bool target;
    bool anyfour1;
    bool SUPER_ROLE;
    bool ToCheckRole;
    bool TargetPrime;
};

/*---------- INIT GLOBAL VARIABLES ---------*/
bool GlobalInit(
   Roles g
)
(true 
& g.SUPER_ROLE=true& g.ToCheckRole=true);
#size GlobalInit;

/*---------- INIT LOCAL VARIABLES ---------*/
bool LocalInit(
   ThreadID t,
   Roles l
)
  t < l
(false 
| ((/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0)& l.target=false& l.anyfour1=false& l.SUPER_ROLE=true& l.ToCheckRole=true& l.TargetPrime=false)
| ((/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0)& l.target=false& l.anyfour1=false& l.SUPER_ROLE=false& l.ToCheckRole=false& l.TargetPrime=false)
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
		// <SUPER_ROLE,TRUE,anyfour1>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.anyfour1=false) & /* Applying this rule */
 (dL.anyfour1=true)
/* Copy variables */
& (dL.target=cL.target)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dL.ToCheckRole=cL.ToCheckRole)& (dL.TargetPrime=cL.TargetPrime))
		//------------------ CAN_ASSIGN RULE NUMBER 1 -----------------
		// <SUPER_ROLE,anyfour1,target>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.SUPER_ROLE=true & cL.anyfour1=true & cL.target=false) & /* Applying this rule */
 (dL.target=true)
/* Copy variables */
& (dL.anyfour1=cL.anyfour1)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dL.ToCheckRole=cL.ToCheckRole)& (dL.TargetPrime=cL.TargetPrime))
		//------------------ CAN_ASSIGN RULE NUMBER 2 -----------------
		// <ToCheckRole,ToCheckRole&target,TargetPrime>
		//------------------------------------------------------------------
| (/* Precondition */
(cG.ToCheckRole=true & cL.ToCheckRole=true & cL.target=true & cL.TargetPrime=false) & /* Applying this rule */
 (dL.TargetPrime=true)
/* Copy variables */
& (dL.target=cL.target)& (dL.anyfour1=cL.anyfour1)& (dL.SUPER_ROLE=cL.SUPER_ROLE)& (dL.ToCheckRole=cL.ToCheckRole))
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
& (dG.ToCheckRole=cG.ToCheckRole|cL.ToCheckRole)
);
#size UpdateGlobal;

/*--- REACHABILITY CHECK ----*/
bool targetReach(
   ThreadID t,
   Roles L
)
  t  < L
(true 
& (/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0)& (L.TargetPrime=true)
);
/*--- THREAD FUNCTIONS ----*/
bool IncreaseThreadID(
   ThreadID s,
   ThreadID t
)
  s  ~+  t
(false 
| ((/* pc=0 */ s.b1=0 & s.b2=0 & s.b3=0) & (/* pc=1 */ t.b1=1 & t.b2=0 & t.b3=0))
| ((/* pc=1 */ s.b1=1 & s.b2=0 & s.b3=0) & (/* pc=0 */ t.b1=0 & t.b2=0 & t.b3=0))
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



