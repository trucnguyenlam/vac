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



