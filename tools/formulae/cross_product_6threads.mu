/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/
/******                                                                                    *******/
/******                               Reachability Algorithm                               *******/
/******                                                                                    *******/
/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/
#timer go;

// bool Fake_Ordering_All(
//  Counter    t_C,
//  blocktype  t_block,
//  CS         t_r,
//  ThreadID   t_ID,
//  Globals    t_G,
 
//  Counter    s_C,
//  blocktype  s_block,
//  CS         s_r,
//  ThreadID   s_ID,
//  Globals    s_G

// )
//  t_C     <  t_block,
//  t_block <  t_r,
//  t_r     <  t_ID,
//  t_ID    <  t_G,
//  s_C     <  s_block,
//  s_block <  s_r,
//  s_r     <  s_ID,
//  s_ID    <  s_G,
//  t_C      ~+  s_C,
//  t_block  ~+  s_block,
//  t_r      ~+  s_r,
//  t_ID     ~+  s_ID,
//  t_G      ~+  s_G

// ( true
// );

// bool Fake_Ordering_Globals(
//   Globals G,
//   Globals H
// )
// G ~+ H
// ( true
// );

/*
    Fixed point
  s_ : means current state
  t_ : means previous state
 */

mu bool Sequ_Reach(
 bool       s_fr,                  // Frontier bit
 Globals    s_G                    // Global variable & Local variables
)
 s_fr    <  s_G

( false

   | (Sequ_Reach(1, s_G))

   | (INIT(s_G) & s_fr=1)

   | ( true
      & (exists     // There exists an internal state that
           Globals t_G.
           (   Sequ_Reach(1, t_G)
              &  
            (
              ( true
                &  s_G.g1 = t_G.g1
                &  s_G.g2 = t_G.g2
                &  s_G.g3 = t_G.g3
                &  s_G.g4 = t_G.g4
                &  s_G.g5 = t_G.g5
                )
             &  ( CanAssign_t0( t_G, s_G )
                | CanRevoke_t0( t_G, s_G )
                | t_G.g0 = s_G.g0 
               )
              )

           )
        )
    )

   | ( true
      & (exists     // There exists an internal state that
           Globals t_G.
           (   Sequ_Reach(1, t_G)
              &  
            (
              ( true
                &  s_G.g0 = t_G.g0
                &  s_G.g2 = t_G.g2
                &  s_G.g3 = t_G.g3
                &  s_G.g4 = t_G.g4
                &  s_G.g5 = t_G.g5
                )
             &  (  CanAssign_t1( t_G, s_G )
                | CanRevoke_t1( t_G, s_G )
                | t_G.g1 = s_G.g1 
               )
              )

           )
        )
    )


   | ( true
      & (exists     // There exists an internal state that
           Globals t_G.
           (   Sequ_Reach(1, t_G)
              &  
            (
              ( true
                &  s_G.g0 = t_G.g0
                &  s_G.g1 = t_G.g1
                &  s_G.g3 = t_G.g3
                &  s_G.g4 = t_G.g4
                &  s_G.g5 = t_G.g5
                )
             &  (  CanAssign_t2( t_G, s_G )
                | CanRevoke_t2( t_G, s_G )
                | t_G.g2 = s_G.g2 
               )
              )

           )
        )
    )


   | ( true
      & (exists     // There exists an internal state that
           Globals t_G.
           (   Sequ_Reach(1, t_G)
              &  
            (
              ( true
                &  s_G.g0 = t_G.g0
                &  s_G.g1 = t_G.g1
                &  s_G.g2 = t_G.g2
                &  s_G.g4 = t_G.g4
                &  s_G.g5 = t_G.g5
                )
             &  ( CanAssign_t3( t_G, s_G )
                | CanRevoke_t3( t_G, s_G )
                | t_G.g3 = s_G.g3 
               )
              )

           )
        )
    )


   | ( true
      & (exists     // There exists an internal state that
           Globals t_G.
           (   Sequ_Reach(1, t_G)
              &  
            (
              ( true
                &  s_G.g0 = t_G.g0
                &  s_G.g1 = t_G.g1
                &  s_G.g2 = t_G.g2
                &  s_G.g3 = t_G.g3
                &  s_G.g5 = t_G.g5
                )
             &  ( CanAssign_t4( t_G, s_G )
                | CanRevoke_t4( t_G, s_G )
                | t_G.g4 = s_G.g4 
               )
              )

           )
        )
    )


   | ( true
      & (exists     // There exists an internal state that
           Globals t_G.
           (   Sequ_Reach(1, t_G)
              &  
            (
              ( true
                &  s_G.g0 = t_G.g0
                &  s_G.g1 = t_G.g1
                &  s_G.g2 = t_G.g2
                &  s_G.g3 = t_G.g3
                &  s_G.g4 = t_G.g4
                )
             &  ( CanAssign_t5( t_G, s_G )
                | CanRevoke_t5( t_G, s_G )
                | t_G.g5 = s_G.g5 
               )
              )

           )
        )
    )


  // early termination
  | ( exists    /* Sequ_Reach::@Exists0 */               // There exists a state such that
            Globals    t_G.
        (
            Sequ_Reach(1, t_G )    // That state is in fixed point and ...
          & targetReach( t_G )                  // target is reached
        )
     )

)
;

#size Sequ_Reach;
#timer;

/******************************************************************************************************/
//                                       Reachabibility check                                         *
/******************************************************************************************************/

// Uncomment the below line to show witness (if the query is true)
//#wit
( exists
    Globals    t_G.
    (   Sequ_Reach(1, t_G )
      & (
            targetReach( t_G )
        )
    )
);






// #timer stop;