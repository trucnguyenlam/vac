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

bool Fake_Ordering_All(
 blocktype  t_block,
 CS         t_r,
 ThreadID   t_ID,
 Globals    t_G,

 blocktype  s_block,
 CS         s_r,
 ThreadID   s_ID,
 Globals    s_G

)
 t_block <  t_r,
 t_r     <  t_ID,
 t_ID    <  t_G,
 s_block <  s_r,
 s_r     <  s_ID,
 s_ID    <  s_G,
 t_block  ~+  s_block,
 t_r      ~+  s_r,
 t_ID     ~+  s_ID,
 t_G      ~+  s_G

( true
);

bool Fake_Ordering_Globals(
  Globals G,
  Globals H
)
G ~+ H
( true
);

/*
    Fixed point
  s_ : means current state
  t_ : means previous state
 */

mu bool Sequ_Reach(
 bool       s_fr,                  // Frontier bit
 blocktype  s_block,               // Block as appeared in Figure 2 of cav2010
 CS         s_r,                   // Current round
 ThreadID   s_ID,                  // Current thread id
 Globals    s_G                    // Global variable & Local variables
)
 s_fr    <  s_block,
 s_block <  s_r,
 s_r     <  s_ID,
 s_ID    <  s_G
( false

  | (Sequ_Reach(1, s_block, s_r, s_ID, s_G))

  // early termination
  | ( exists    /* Sequ_Reach::@Exists0 */               // There exists a state such that
            CS         t_r,
            ThreadID   t_ID,
            Globals    t_G.
        (
            Sequ_Reach(1, thread, t_r, t_ID, t_G )    // That state is in fixed point and ...
          & Fake_Ordering_All (thread, t_r, t_ID, t_G, s_block, s_r, s_ID, s_G)
          & (   targetReach( t_ID, t_G.L )                  // target is reached
            )
        )
     )

  /*********************************************************************************/
  // First thread (thread0) - TLI   Figure (a)
  |  (  // For the first round
        s_block=thread
        & s_fr=1
        & s_r=0                        // Round 0
        & InitID0(s_ID)                // Thread ID=0
        & GlobalInit(s_G.g0)
        & LocalInit(s_ID, s_G.L)        // init of local variables
        & InitGlobals( s_G )
     )

  | (   // For subsequent round
          s_block=thread       // This block is TLI
        & s_fr=1
        & s_r != 0           // Round > 0
        & InitID0(s_ID)        // Thread ID 0
        & ( exists  /* Sequ_Reach::@Exists1 */
                CS t_r.     // There exists round t_r, which is the previous round
             (    Sequ_Reach(s_fr, thread, t_r, s_ID, s_G ) // There exists thread0 at previous round
                & increaseCS( t_r, s_r )           // previous round
                & ( exists  /* Sequ_Reach::@Exists1::@Exists2 */
                        ThreadID  t_ID,
                        Globals   a_G.
                     (   Sequ_Reach(s_fr, have, t_r, t_ID, a_G ) // There is RLI at previous round
                       & increaseThreadID( s_ID, t_ID )
                       & (
                           //   copy_g_h( a_G, s_G, t_r )    // And input of RLI is the same output TLI
                           // & folding( s_G, a_G, s_r )     // And output of RLI is wrapped at TLI
                           copy_folding_diff_round ( s_G, a_G, s_r )
                         )
                     )
                  )
             )
          )
    )

/*                                  |------||------|
                                    | T0   ||  H1  |
                                    |      ||      |
                                    | s_G  || a_G  |
                                    |      ||      |
                              t_r:  |      ||------|
                                    |      ||
                              s_r:  |------||
*/

  /*********************************************************************************/
  // WRLI block (first thread) Figure 2 (b)
  | ( // WRLI block generates by an TLI (LHS)
         s_block=want       // TLI asks for WRLI block of remaining threads
       & s_r != 0            // Round > 0
       & ( exists     /* Sequ_Reach::@Exists3 */
                CS   t_r.        // And there is already a RLI block in previous round
            (   Sequ_Reach(s_fr, have, t_r, s_ID, s_G ) //HAVE means RLI
              & increaseCS( t_r, s_r )
            )
         )
       & ( exists    /* Sequ_Reach::@Exists4 */
                ThreadID  t_ID,
                Globals   a_G.  // And there exists TLI in which
            ( (   Sequ_Reach(s_fr, threadnoloc, s_r, t_ID, a_G ) //Thread completes simulation in round s_r
                & increaseThreadID( t_ID, s_ID )
                & InitID0( t_ID )
              )
              & (
                  //   copy_g_h( s_G, a_G, s_r )  // Thread1 output matches this block input
                  // & folding( a_G, s_G, s_r )   // And this block output wrap thread1 input
                    copy_folding_same_round( a_G, s_G, s_r)
                )
            )
         )
    )

/*                                                   .............
                                      |------|      '  |-------|  '
                                      | T_0  |      '  | H_1   |  '
                                      |      |      '  |       |  '
                                      | a_G  |      '  |  s_G  |  '
                                      |      |      '  |       |  '
                                t_r:  |      |      '  |-------|  '
                                      |      |      '             '
                                s_r:  |     g| ---> 'h      W_i+1 '
                                      |------|      '.............'
*/

  /*********************************************************************************/
  // WRLI block (forward phase) Figure 2 (d)
  | ( // WRLI block generates by an TLI (LHS)
      true
    & s_block=want       // TLI asks for WRLI block of remaining threads
    & s_r != 0           // Round > 0
    & InitID1( s_ID )    // Not the first thread
    & ( exists     /* Sequ_Reach::@Exists3 */
             CS   t_r.        // And there is already a RLI block in previous round
          ( true
          & Sequ_Reach(s_fr, have, t_r, s_ID, s_G ) //HAVE means RLI
          & increaseCS( t_r, s_r )
          )
      )
    & ( exists
             ThreadID t_ID,
             Globals t_G.
          ( true
            & Sequ_Reach(s_fr, threadnoloc, s_r, t_ID, t_G)  // We have a previous thread
            & increaseThreadID(t_ID, s_ID)
            & copy_g_h(s_G, t_G, s_r)
            & ( exists
                     Globals a_G.
                  ( true
                  & Sequ_Reach(s_fr, want, s_r, t_ID, a_G)
                  & copy_g_g(t_G, a_G, s_r)
                  & copy_h_h(s_G, a_G, s_r)         // maybe too strong since I'm constraining h to s_r, 
                                                    // but since are want blocks can be anything
                  )
              )
          ) 
      )
    )

/*                                  
                              ....................................
                             'W_i             a_G  .............  '
                             '       |------|     '  |-------|  ' '
                             '       | T_i  |     '  | H_i+1 |  ' '
                             '       |      |     '  |       |  ' '
                             '       | t_G  |     '  |  s_G  |  ' '
                             '       |      |     '  |       |  ' '
                             ' t_r:  |------| --->'  |-------|  ' '
                             '       |      |     '             ' '
                             ' s_r:  |     g| --->'  s_G  W_i+1 ' '
                             '       |------|     '.............' '
                             '....................................'
*/
  /*********************************************************************************/
  // TLI inside WRLI block, Figure 2 (c)
  |  (   // round 0 execution of any thread except thread0
         s_block=thread
       & s_fr=1
       & s_r=0
       & InitID1(s_ID)     // thread ID different from thread0
       & LocalInit( s_ID, s_G.L )
       & ( exists         /* Sequ_Reach::@Exists5 */
              ThreadID t_ID,
              Globals  t_G.
            (
              ( Sequ_Reach(s_fr, threadnoloc, 0, t_ID, t_G )    // After a thread finishes its execution
              & Fake_Ordering_Globals( s_G, t_G )
              & increaseThreadID ( t_ID, s_ID )
              )
              & t_G.h0 = s_G.g0             // Map output of thread_i to input of thread_i+1
            )
         )
        & InitGlobals( s_G )
     )

  | ( // increase ROUND for TLI (not thread0, not the last thread)
        s_block=thread
      & s_fr=1
      & s_r != 0               // round > 0
      & nonMaxThreadID( s_ID )  // This TLI must not be the last thread or thread0
      & ( exists        /* Sequ_Reach::@Exists6 */
             CS t_r.
            (   Sequ_Reach(s_fr, thread, t_r, s_ID, s_G )   // TLI
              & increaseCS( t_r, s_r )
            )
        )
      & ( exists      /* Sequ_Reach::@Exists7 */
              Globals b_G.
           (
               Sequ_Reach(s_fr, want, s_r, s_ID, b_G )    // this TLI is in WRLI block
             & ( exists    /*  Sequ_Reach::@Exists7::@Exists8 */
                       CS        t_r,
                       Globals   a_G.
                   (
                     (  ( exists ThreadID  t_ID.
                           (    Sequ_Reach(s_fr, have, t_r, t_ID, a_G )  // There is RLI at previous round with
                              & increaseThreadID( s_ID, t_ID )
                           )
                        )
                        & increaseCS( t_r, s_r )
                     )
                     & (   copy_g_h( a_G, s_G, t_r )            // Output of TLI == input of RLI
                         & copy_h_h( a_G, b_G, t_r )            // Output of RLI == output of WRLI block
                       )
                   )
               )
             & copy_g_g( b_G, s_G, s_r )                   // Input of TLI == input of WRLI block
           )
        )
    )

/*                                   ------------------
                                    |  ------  ------  |
                                    | | T_i  ||H_i+1 | |
                                    | |      ||      | |
                                    | | s_G  || a_G  | |
                                    | |      ||      | |
                                t_r |  ------  ------  |
                                    |        b_G    W_i|
                                s_r  ------------------
*/

  | ( // increase round_number for last thread
        s_block=thread
      & s_fr=1
      & s_r != 0
      & maxThreadID( s_ID )  // last thread
      & ( exists           /* Sequ_Reach::@Exists9 */
              CS      t_r.
            ( (  Sequ_Reach(s_fr, thread, t_r, s_ID, s_G )  // There exists this TLI at previous round
               & increaseCS( t_r, s_r )
              )
              & (exists   /* Sequ_Reach::@Exists9::@Exists10 */
                     Globals a_G.
                   (   Sequ_Reach(s_fr, want, s_r, s_ID, a_G )    // WRLI block
                     & (   copy_h_h( a_G, s_G, t_r )
                         & copy_g_g( a_G, s_G, s_r )
                       )
                   )
                )
            )
        )
    )

/*                                   ............
                                     ' |------| '
                                     ' |  TL  | '
                                     ' |      | '
                                     ' |  s_G | '
                              t_r:   ' |------| '
                                     '  a_G  WL '
                              s_r:   '..........'
*/

  /*********************************************************************************/
  // last thread in WRLI (backward phase)   Figure 2 (e)
  | ( // RLI from the last TLI (stop forward propagation, start backward propagation)
      (  s_block=have
      & maxThreadID( s_ID )
      )
      & Sequ_Reach(s_fr, threadnoloc, s_r, s_ID, s_G )
    )

/*                           |------|              |------|
                             |  TL  |              |  TL  |
                             |      |              |      |
                             | s_G  |    become    | s_G  |
                             |      |     -->      |      |
                             |      |              |      |
                             |------|              |------|
                                WL                    HL
*/

  /*********************************************************************************/
  // Backward creating RLI block (backward phase)   Figure 2 (f)
  | (    // RLI generated from TLI and RLI (inside WRLI)
       (  s_block=have
       & nonMaxThreadID( s_ID )
       )
       & (    s_r=0
           | Sequ_Reach(s_fr, want, s_r, s_ID, s_G )   // There exists WRLI
         )
       & ( exists        /* Sequ_Reach::@Exists11 */
                 Globals b_G.
              (     ( exists           /* Sequ_Reach::@Exists11::@Exists12 */
                          Globals a_G.
                        (    Sequ_Reach(s_fr, threadnoloc, s_r, s_ID, a_G )
                           & (   copy_g_g( s_G, a_G, s_r )
                               & copy_g_h( b_G, a_G, s_r )
                             )
                        )
                    )
                 &  ( exists          /* Sequ_Reach::@Exists11::@Exists13  */
                          ThreadID  t_ID.
                         (   Sequ_Reach(s_fr, have, s_r, t_ID, b_G )
                             & increaseThreadID( s_ID, t_ID )
                         )
                    )
                 &  copy_h_h( s_G, b_G, s_r )
              )
         )
    )

/*                                  |---------------|
                                    | T_i  || H_i+1 |
                                    |      ||       |
                                    | a_G  || b_G   |
                                    |      ||       |
                                    |---------------|
                                          s_G   W_i
*/

  /*********************************************************************************/
   // forgetting local states for  each thread
  | (
    s_block=threadnoloc
    & ( exists                    /* Sequ_Reach::@Exists14 */
          Globals    t_G.
       (    Sequ_Reach(s_fr, thread, s_r, s_ID, t_G )
          & Fake_Ordering_All (thread, s_r, s_ID, t_G, threadnoloc, s_r, s_ID, s_G)
          & (  copy_g_g( t_G, s_G, s_r )
             & copy_h_h( t_G, s_G, s_r )
            )
       )
     )
    )

/*                                  |------------|
                                    |      T     |
                                    |            |
                                    | s_G        |
                                    |            |
                                    | g  ~~-->  h|
                                    |------------|
*/

//*********************************************************************************/
// forward propagation on internal transitions
//*********************************************************************************/

|  (  s_block=thread
   & (exists
         Globals t_G,
         Globals z_G.
      (  Sequ_Reach(s_fr, thread, s_r, s_ID, t_G )
       & Internal_Trans( thread, s_r, s_ID, z_G )
        & (
                copy_g( s_G, t_G )

              & copy_no_h ( s_G, t_G, s_r )

                & t_G.L  =z_G.LP
                & s_G.L  =z_G.L

              & fixed_in_out( s_G, t_G, z_G, s_r )
          )
      )
     )
   )


// |  ( ( s_block=thread
//        & s_r=0
//      )
//    & (exists
//          Globals t_G,
//          Globals z_G.
//       (  Sequ_Reach(s_fr, thread, 0, s_ID, t_G )
//        & Internal_Trans( thread, 0, s_ID, z_G )
//         & (
//                 s_G.g0 =t_G.g0
//                 & s_G.g1 =t_G.g1
//                 & s_G.g2 =t_G.g2
//                 & s_G.g3 =t_G.g3

//                 & s_G.h1 =t_G.h1
//                 & s_G.h2 =t_G.h2
//                 & s_G.h3 =t_G.h3

//                 & t_G.h0 =z_G.g0
//                 & t_G.L  =z_G.LP
//                 & s_G.L  =z_G.L

//                 & z_G.h0 =s_G.h0
//                 & t_G.h0 =t_G.g0
//           )
//       )
//      )
//    )

// |  ( ( s_block=thread
//        & s_r=1
//      )
//    & (exists
//          Globals t_G,
//          Globals z_G.
//       (  Sequ_Reach(s_fr, thread, 1, s_ID, t_G )
//        & Internal_Trans( thread, 1, s_ID, z_G )
//         & (
//                 s_G.g0 =t_G.g0
//                 & s_G.g1 =t_G.g1
//                 & s_G.g2 =t_G.g2
//                 & s_G.g3 =t_G.g3


//                 & s_G.h0 =t_G.h0
//                 & s_G.h2 =t_G.h2
//                 & s_G.h3 =t_G.h3


//                 & t_G.h1 =z_G.g1
//                 & t_G.L  =z_G.LP

//                 & s_G.L  =z_G.L

//                 & z_G.h1 =s_G.h1
//                 & t_G.h1 =t_G.g1
//           )
//       )
//      )
//    )


// |  ( ( s_block=thread
//        & s_r=2
//      )
//    & (exists
//          Globals t_G,
//          Globals z_G.
//       (  Sequ_Reach(s_fr, thread, 2, s_ID, t_G )
//        & Internal_Trans( thread, 2, s_ID, z_G )
//         & (
//                 s_G.g0 =t_G.g0
//                 & s_G.g1 =t_G.g1
//                 & s_G.g2 =t_G.g2
//                 & s_G.g3 =t_G.g3


//                 & s_G.h0 =t_G.h0
//                 & s_G.h1 =t_G.h1
//                 & s_G.h3 =t_G.h3


//                 & t_G.h2 =z_G.g2
//                 & t_G.L  =z_G.LP

//                 & s_G.L  =z_G.L

//                 & z_G.h2 =s_G.h2
//                 & t_G.h2 =t_G.g2
//           )
//       )
//      )
//    )


// |  ( ( s_block=thread
//        & s_r=3
//      )
//    & (exists
//          Globals t_G,
//          Globals z_G.
//       (  Sequ_Reach(s_fr, thread, 3, s_ID, t_G )
//        & Internal_Trans( thread, 3, s_ID, z_G )
//         & (
//                 s_G.g0 =t_G.g0
//                 & s_G.g1 =t_G.g1
//                 & s_G.g2 =t_G.g2
//                 & s_G.g3 =t_G.g3


//                 & s_G.h0 =t_G.h0
//                 & s_G.h1 =t_G.h1
//                 & s_G.h2 =t_G.h2


//                 & t_G.h3 =z_G.g3
//                 & t_G.L  =z_G.LP

//                 & s_G.L  =z_G.L

//                 & z_G.h3 =s_G.h3
//                 & t_G.h3 =t_G.g3
//           )
//       )
//      )
//    )
)
;

#size Sequ_Reach;
#timer;

/******************************************************************************************************/
//                                       Reachabibility check                                         *
/******************************************************************************************************/

// Uncomment the below line to show witness (if the query is true)
// #wit
( exists
    blocktype  t_block,
    CS         t_r,
    ThreadID   t_ID,
    Globals    t_G.
    (   Sequ_Reach(1, t_block, t_r, t_ID, t_G )
      & (
            targetReach( t_ID, t_G.L )
          & t_block=thread
        )
    )
);

// #timer stop;