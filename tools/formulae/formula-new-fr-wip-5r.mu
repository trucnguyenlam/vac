/*************************************************************************************************/
/********************             DESIGN FOR MULTIPLE THREADS         ****************************/
/********************            WITH THE SAME INTERNAL MOVES         ****************************/
/*************************************************************************************************/
#timer go;

enum CS {0..4}; // Round or context switch

// Increase context-switch counter
bool increaseCS(CS s, CS t)
s ~+ t
( false
  | ( s=0 & t=1 )
  | ( s=1 & t=2 )
  | ( s=2 & t=3 )
  | ( s=3 & t=4 )
);

enum blocktype {
                thread,                // TLI
                threadnoloc,           // TLI with no local
                want,                  // WRLI
                have                   // RLI
               };

/*************************************************************************************************/
/*************               Used in internal transition                 *************************/
/*************************************************************************************************/

/*
  Copy global variable at CS 4 (mean round 4)
 */
bool copy_g_and_h_4( Globals s_G, Globals t_G)
 s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 & s_G.h0 =t_G.h0
    & s_G.g1 =t_G.g1 & s_G.h1 =t_G.h1
    & s_G.g2 =t_G.g2 & s_G.h2 =t_G.h2
    & s_G.g3 =t_G.g3 & s_G.h3 =t_G.h3
    & s_G.g4 =t_G.g4
);

/*
  Copy global variable at CS 3 (mean round 3)
 */
bool copy_g_and_h_3( Globals s_G, Globals t_G)
 s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 & s_G.h0 =t_G.h0
    & s_G.g1 =t_G.g1 & s_G.h1 =t_G.h1
    & s_G.g2 =t_G.g2 & s_G.h2 =t_G.h2
    & s_G.g3 =t_G.g3
    & s_G.g4 =t_G.g4 & s_G.h4 =t_G.h4
);

/*
  Copy global variable at CS 2 (mean round 2)
 */
bool copy_g_and_h_2( Globals s_G, Globals t_G)
 s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 & s_G.h0 =t_G.h0
    & s_G.g1 =t_G.g1 & s_G.h1 =t_G.h1
    & s_G.g2 =t_G.g2
    & s_G.g3 =t_G.g3 & s_G.h3 =t_G.h3
    & s_G.g4 =t_G.g4 & s_G.h4 =t_G.h4
);


/*
  Copy global variable at CS 1 (mean round 1)
 */
bool copy_g_and_h_1( Globals s_G, Globals t_G)
 s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 & s_G.h0 =t_G.h0
    & s_G.g1 =t_G.g1
    & s_G.g2 =t_G.g2 & s_G.h2 =t_G.h2
    & s_G.g3 =t_G.g3 & s_G.h3 =t_G.h3
    & s_G.g4 =t_G.g4 & s_G.h4 =t_G.h4
);


/*
  Copy global variable at CS 0 (mean round 0)
 */
bool copy_g_and_h_0( Globals s_G, Globals t_G)
 s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0
    & s_G.g1 =t_G.g1 & s_G.h1 =t_G.h1
    & s_G.g2 =t_G.g2 & s_G.h2 =t_G.h2
    & s_G.g3 =t_G.g3 & s_G.h3 =t_G.h3
    & s_G.g4 =t_G.g4 & s_G.h4 =t_G.h4
);


/******************************************************************************/

bool copy_g_g(Globals s, Globals t, CS r)
 r  < s,
 s  ~+ t
( true
  & ( s.g0=t.g0 | (false  ) )
  & ( s.g1=t.g1 | (false  | r=0  ) )
  & ( s.g2=t.g2 | (false  | r=0  | r=1  ) )
  & ( s.g3=t.g3 | (false  | r=0  | r=1  | r=2  ) )
  & ( s.g4=t.g4 | (false  | r=0  | r=1  | r=2  | r=3) )
);

/******************************************************************************/

bool copy_h_h(Globals s, Globals t, CS r)
 r  < s,
 s  ~+ t
( true
  & ( s.h0=t.h0 | (false ) )
  & ( s.h1=t.h1 | (false | r=0  ) )
  & ( s.h2=t.h2 | (false | r=0  | r=1  ) )
  & ( s.h3=t.h3 | (false | r=0  | r=1  | r=2  ) )
  & ( s.h4=t.h4 | (false | r=0  | r=1  | r=2  | r=3) )
);

/******************************************************************************/

bool copy_g_h(Globals s, Globals t, CS r)
 r  < s,
 s  ~+ t
( true
  & ( s.g0=t.h0 | (false ) )
  & ( s.g1=t.h1 | (false | r=0  ) )
  & ( s.g2=t.h2 | (false | r=0  | r=1  ) )
  & ( s.g3=t.h3 | (false | r=0  | r=1  | r=2  ) )
  & ( s.g4=t.h4 | (false | r=0  | r=1  | r=2  | r=3) )
);

/******************************************************************************/

bool folding( Globals G,  Globals H, CS r )
 r  < G,
 G ~+ H
(
   true
   & (H.h0 = G.g1  | r=0  )
   & (H.h1 = G.g2  | r=0  | r=1  )
   & (H.h2 = G.g3  | r=0  | r=1  | r=2  )
   & (H.h3 = G.g4  | r=0  | r=1  | r=2  | r=3)
);



// copy_g_h( s_G, a_G, s_r )  // Thread1 output matches this block input
// & folding( a_G, s_G, s_r )   // And this block output wrap thread1 input
bool copy_folding_same_round( Globals G, Globals H, CS r )
 r  < G,
 G ~+ H
(   true
  & ( H.g0=G.h0 | (false ) )
  & ( (H.g1=G.h1 & H.h0 = G.g1) | (false | r=0  ) )
  & ( (H.g2=G.h2 & H.h1 = G.g2) | (false | r=0  | r=1  ) )
  & ( (H.g3=G.h3 & H.h2 = G.g3) | (false | r=0  | r=1  | r=2  ) )
  & ( (H.g4=G.h4 & H.h3 = G.g4) | (false | r=0  | r=1  | r=2  | r=3) )
);

// copy_g_h( a_G, s_G, t_r )    // And input of RLI is the same output TLI
// & folding( s_G, a_G, s_r )     // And output of RLI is wrapped at TLI
bool copy_folding_diff_round( Globals G, Globals H, CS r )
 r < G,
 G ~+ H
(  true
  & ( (H.g0=G.h0 & H.h0 = G.g1) | (false | r=0  ) )
  & ( (H.g1=G.h1 & H.h1 = G.g2) | (false | r=0  | r=1  ) )
  & ( (H.g2=G.h2 & H.h2 = G.g3) | (false | r=0  | r=1  | r=2  ) )
  & ( (H.g3=G.h3 & H.h3 = G.g4) | (false | r=0  | r=1  | r=2  | r=3) )
);


/******************************************************************************/

/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/
/******                                                                                    *******/
/******                               Reachability Algorithm                               *******/
/******                                                                                    *******/
/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/

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


mu bool Sequ_Reach(
 blocktype  s_block,
 CS         s_r,
 ThreadID   s_ID,
 Globals    s_G
);



mu bool Internal_Trans(
 blocktype  s_block,
 CS         s_r,
 ThreadID   s_ID,
 Globals    s_G
)
 s_block <  s_r,
 s_r     <  s_ID,
 s_ID    <  s_G
( false

//*************** Round 0
  | ( s_r = 0
    )
    & (exists
          Globals t_G.
        (
            Sequ_Reach( thread, 0, s_ID, t_G )
          & (
                t_G.L = s_G.LP
                & s_G.LP = s_G.L
                & t_G.h0 = s_G.g0
                & s_G.g0 = s_G.h0
            )
        )
    )

  | ( s_r = 1
    )
    & (exists
          Globals t_G.
        (
            Sequ_Reach( thread, 1, s_ID, t_G )
          & (
                t_G.L = s_G.LP
                & s_G.LP = s_G.L
                & t_G.h1 = s_G.g1
                & s_G.g1 = s_G.h1
            )
        )
    )

  | ( s_r = 2
    )
    & (exists
          Globals t_G.
        (
            Sequ_Reach( thread, 2, s_ID, t_G )
          & (
                t_G.L = s_G.LP
                & s_G.LP = s_G.L
                & t_G.h2 = s_G.g2
                & s_G.g2 = s_G.h2
            )
        )
    )

  | ( s_r = 3
    )
    & (exists
          Globals t_G.
        (
            Sequ_Reach( thread, 3, s_ID, t_G )
          & (
                t_G.L = s_G.LP
                & s_G.LP = s_G.L
                & t_G.h3 = s_G.g3
                & s_G.g3 = s_G.h3
            )
        )
    )

  | ( s_r = 4
    )
    & (exists
          Globals t_G.
        (
            Sequ_Reach( thread, 4, s_ID, t_G )
          & (
                t_G.L = s_G.LP
                & s_G.LP = s_G.L
                & t_G.h4 = s_G.g4
                & s_G.g4 = s_G.h4
            )
        )
    )

//*************** Round 0
  | ( true
      & ( s_r=0      // Round 0
        )
      & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
           Globals t_G.
           (  (  Internal_Trans( s_block, 0, s_ID, t_G )
                & s_G.LP = t_G.LP
                & t_G.g0 = s_G.g0
              )
            & (   CanAssign_0( t_G, s_G )
                | CanRevoke_0( t_G, s_G )
                | UpdateGlobal_0( t_G, s_G )
              )
           )
        )
    )

//*************** Round 1
  | ( true
      & (   s_r=1      // Round 1
        )
      & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
           Globals t_G.
           (  (  Internal_Trans( s_block, 1, s_ID, t_G )
                & s_G.LP = t_G.LP
                 & t_G.g1 = s_G.g1
              )
            & (   CanAssign_1( t_G, s_G )
                | CanRevoke_1( t_G, s_G )
                | UpdateGlobal_1( t_G, s_G )
              )
           )
        )
    )


//*************** Round 2
  | ( true
      & (   s_r=2      // Round 2
        )
      & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
           Globals t_G.
           (  (  Internal_Trans( s_block, 2, s_ID, t_G )
                & s_G.LP = t_G.LP
                & t_G.g2 = s_G.g2
              )
            & (   CanAssign_2( t_G, s_G )
                | CanRevoke_2( t_G, s_G )
                | UpdateGlobal_2( t_G, s_G )
              )
           )
        )
    )

//*************** Round 3
  | ( true
      & (   s_r=3      // Round 3
        )
      & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
           Globals t_G.
           (  (  Internal_Trans( s_block, 3, s_ID, t_G )
                & s_G.LP = t_G.LP
                & t_G.g3 = s_G.g3
              )
            & (   CanAssign_3( t_G, s_G )
                | CanRevoke_3( t_G, s_G )
                | UpdateGlobal_3( t_G, s_G )
              )
           )
        )
    )

//*************** Round 4
  | ( true
      & (   s_r=4      // Round 4
        )
      & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
           Globals t_G.
           (  (  Internal_Trans( s_block, 4, s_ID, t_G )
                & s_G.LP = t_G.LP
                & t_G.g4 = s_G.g4
              )
            & (   CanAssign_4( t_G, s_G )
                | CanRevoke_4( t_G, s_G )
                | UpdateGlobal_4( t_G, s_G )
              )
           )
        )
    )

)
;

#size Internal_Trans;

/*
    Fixed point
  s_ : means current state
  t_ : means previous state
 */

mu bool Sequ_Reach(
 blocktype  s_block,               // Block as appeared in Figure 2 of cav2010
 CS         s_r,                   // Current round
 ThreadID   s_ID,                  // Current thread id
 Globals    s_G                    // Global variable & Local variables
)
 s_block <  s_r,
 s_r     <  s_ID,
 s_ID    <  s_G
( false

  // early termination
  | ( exists    /* Sequ_Reach::@Exists0 */               // There exists a state such that
            CS         t_r,
            ThreadID   t_ID,
            Globals    t_G.
        (
            Sequ_Reach( thread, t_r, t_ID, t_G )    // That state is in fixed point and ...
          & Fake_Ordering_All (thread, t_r, t_ID, t_G, s_block, s_r, s_ID, s_G)
          & (   targetReach( t_ID, t_G.L )                  // target is reached
            )
        )
     )

  /*********************************************************************************/
  // First thread (thread0) - TLI   Figure (a)
  |  (  // For the first round
        s_block = thread
        & s_r=0                        // Round 0
        & InitID0(s_ID)                // Thread ID=0
        & GlobalInit(s_G.g0)
        & LocalInit(s_ID, s_G.L)        // init of local variables
        & s_G.h0=s_G.g0                // input = output
        & s_G.h1=s_G.g1                // input = output
        & s_G.h2=s_G.g2                // input = output
        & s_G.h3=s_G.g3                // input = output
        & s_G.h4=s_G.g4                // input = output
     )

  | (   // For subsequent round
          s_block=thread       // This block is TLI
        & s_r != 0           // Round > 0
        & InitID0(s_ID)        // Thread ID 0
        & ( exists  /* Sequ_Reach::@Exists1 */
                CS t_r.     // There exists round t_r, which is the previous round
             (    Sequ_Reach( thread, t_r, s_ID, s_G ) // There exists thread0 at previous round
                & increaseCS( t_r, s_r )           // previous round
                & ( exists  /* Sequ_Reach::@Exists1::@Exists2 */
                        ThreadID  t_ID,
                        Globals   a_G.
                     (   Sequ_Reach( have, t_r, t_ID, a_G ) // There is RLI at previous round
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
  // WRLI block (forward phase) Figure 2 (b+d)
  | ( // WRLI block generates by an TLI (LHS)
         s_block=want       // TLI asks for WRLI block of remaining threads
       & s_r != 0            // Round > 0
       & ( exists     /* Sequ_Reach::@Exists3 */
                CS   t_r.        // And there is already a RLI block in previous round
            (   Sequ_Reach( have, t_r, s_ID, s_G ) //HAVE means RLI
              & increaseCS( t_r, s_r )
            )
         )
       & ( exists    /* Sequ_Reach::@Exists4 */
                ThreadID  t_ID,
                Globals   a_G.  // And there exists TLI in which
            ( (   Sequ_Reach( threadnoloc, s_r, t_ID, a_G ) //Thread completes simulation in round s_r
                & increaseThreadID( t_ID, s_ID )
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
                                      | T_i  |      '  | H_i+1 |  '
                                      |      |      '  |       |  '
                                      | a_G  |      '  |  s_G  |  '
                                      |      |      '  |       |  '
                                t_r:  |      |      '  |-------|  '
                                      |      |      '             '
                                s_r:  |     g| ---> 'h      W_i+1 '
                                      |------|      '.............'
*/
  /*********************************************************************************/
  // TLI inside WRLI block, Figure 2 (c)
  |  (   // round 0 execution of any thread except thread0
         s_block=thread
       & s_r = 0
       & InitID1(s_ID)     // thread ID different from thread0
       & LocalInit( s_ID, s_G.L )
       & ( exists         /* Sequ_Reach::@Exists5 */    // The ordering has some problem (s_G is not mixed with t_G)
              ThreadID t_ID,
              Globals  t_G.
            (
              ( Sequ_Reach( threadnoloc, 0, t_ID, t_G )    // After a thread finishes its execution
              & Fake_Ordering_Globals( s_G, t_G )
              & increaseThreadID ( t_ID, s_ID )
              )
              & t_G.h0 = s_G.g0             // Map output of thread_i to input of thread_i+1
            )
         )
        & ( s_G.h0=s_G.g0                // input = output
        & s_G.h1=s_G.g1                // input = output
        & s_G.h2=s_G.g2                // input = output
        & s_G.h3=s_G.g3                // input = output
        & s_G.h4=s_G.g4                // input = output
        )
     )

  | ( // increase ROUND for TLI (not thread0, not the last thread)
        s_block=thread
      & s_r != 0               // round > 0
      & nonMaxThreadID( s_ID )  // This TLI must not be the last thread or thread0
      & ( exists        /* Sequ_Reach::@Exists6 */
             CS t_r.
            (   Sequ_Reach( thread, t_r, s_ID, s_G )   // TLI
              & increaseCS( t_r, s_r )
            )
        )
      & ( exists      /* Sequ_Reach::@Exists7 */
              Globals b_G.
           (
               Sequ_Reach( want, s_r, s_ID, b_G )    // this TLI is in WRLI block
             & ( exists    /*  Sequ_Reach::@Exists7::@Exists8 */
                       CS        t_r,
                       Globals   a_G.
                   (
                     (  ( exists ThreadID  t_ID.
                           (    Sequ_Reach( have, t_r, t_ID, a_G )  // There is RLI at previous round with
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
      & s_r != 0
      & maxThreadID( s_ID )  // last thread
      & ( exists           /* Sequ_Reach::@Exists9 */
              CS      t_r.
            ( (  Sequ_Reach( thread, t_r, s_ID, s_G )  // There exists this TLI at previous round
               & increaseCS( t_r, s_r )
              )
              & (exists   /* Sequ_Reach::@Exists9::@Exists10 */
                     Globals a_G.
                   (   Sequ_Reach( want, s_r, s_ID, a_G )    // WRLI block
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
      & Sequ_Reach( threadnoloc, s_r, s_ID, s_G )
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
           | Sequ_Reach( want, s_r, s_ID, s_G )   // There exists WRLI
         )
       & ( exists        /* Sequ_Reach::@Exists11 */
                 Globals b_G.
              (     ( exists           /* Sequ_Reach::@Exists11::@Exists12 */
                          Globals a_G.
                        (    Sequ_Reach( threadnoloc, s_r, s_ID, a_G )
                           & (   copy_g_g( s_G, a_G, s_r )
                               & copy_g_h( b_G, a_G, s_r )
                             )
                        )
                    )
                 &  ( exists          /* Sequ_Reach::@Exists11::@Exists13  */
                          ThreadID  t_ID.
                         (   Sequ_Reach( have, s_r, t_ID, b_G )
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
    & ( exists                    /* Sequ_Reach::@Exists14 */   // Wrong ordering
          Globals    t_G.
       (    Sequ_Reach( thread, s_r, s_ID, t_G )
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

// ####### #     # ######  #######    #
//    #     #   #  #     # #          #    #
//    #      # #   #     # #          #    #
//    #       #    ######  #####      #    #
//    #       #    #       #          #######
//    #       #    #       #               #
//    #       #    #       #######         #

|  ( ( s_block=thread
       & s_r=0
     )
   & (exists
         Globals t_G,
         Globals z_G.
      (  Sequ_Reach( thread, 0, s_ID, t_G )
       & Internal_Trans( thread, 0, s_ID, z_G )
        & (
                s_G.g0 =t_G.g0
                & s_G.g1 =t_G.g1
                & s_G.g2 =t_G.g2
                & s_G.g3 =t_G.g3
                & s_G.g4 =t_G.g4

                & s_G.h1 =t_G.h1
                & s_G.h2 =t_G.h2
                & s_G.h3 =t_G.h3
                & s_G.h4 =t_G.h4

                & t_G.h0 =z_G.g0
                & t_G.L  =z_G.LP

                & s_G.L  =z_G.L

                & z_G.h0 =s_G.h0
          )
      )
     )
   )

|  ( ( s_block=thread
       & s_r=1
     )
   & (exists
         Globals t_G,
         Globals z_G.
      (  Sequ_Reach( thread, 1, s_ID, t_G )
       & Internal_Trans( thread, 1, s_ID, z_G )
        & (
                s_G.g0 =t_G.g0
                & s_G.g1 =t_G.g1
                & s_G.g2 =t_G.g2
                & s_G.g3 =t_G.g3
                & s_G.g4 =t_G.g4


                & s_G.h0 =t_G.h0
                & s_G.h2 =t_G.h2
                & s_G.h3 =t_G.h3
                & s_G.h4 =t_G.h4


                & t_G.h1 =z_G.g1
                & t_G.L  =z_G.LP

                & s_G.L  =z_G.L

                & z_G.h1 =s_G.h1
          )
      )
     )
   )

|  ( ( s_block=thread
       & s_r=2
     )
   & (exists
         Globals t_G,
         Globals z_G.
      (  Sequ_Reach( thread, 2, s_ID, t_G )
       & Internal_Trans( thread, 2, s_ID, z_G )
        & (
                s_G.g0 =t_G.g0
                & s_G.g1 =t_G.g1
                & s_G.g2 =t_G.g2
                & s_G.g3 =t_G.g3
                & s_G.g4 =t_G.g4


                & s_G.h0 =t_G.h0
                & s_G.h1 =t_G.h1
                & s_G.h3 =t_G.h3
                & s_G.h4 =t_G.h4


                & t_G.h2 =z_G.g2
                & t_G.L  =z_G.LP

                & s_G.L  =z_G.L

                & z_G.h2 =s_G.h2
          )
      )
     )
   )

|  ( ( s_block=thread
       & s_r=3
     )
   & (exists
         Globals t_G,
         Globals z_G.
      (  Sequ_Reach( thread, 3, s_ID, t_G )
       & Internal_Trans( thread, 3, s_ID, z_G )
        & (
                s_G.g0 =t_G.g0
                & s_G.g1 =t_G.g1
                & s_G.g2 =t_G.g2
                & s_G.g3 =t_G.g3
                & s_G.g4 =t_G.g4


                & s_G.h0 =t_G.h0
                & s_G.h1 =t_G.h1
                & s_G.h2 =t_G.h2
                & s_G.h4 =t_G.h4


                & t_G.h3 =z_G.g3
                & t_G.L  =z_G.LP

                & s_G.L  =z_G.L

                & z_G.h3 =s_G.h3
          )
      )
     )
   )


|  ( ( s_block=thread
       & s_r=4
     )
   & (exists
         Globals t_G,
         Globals z_G.
      (  Sequ_Reach( thread, 4, s_ID, t_G )
       & Internal_Trans( thread, 4, s_ID, z_G )
        & (
                s_G.g0 =t_G.g0
                & s_G.g1 =t_G.g1
                & s_G.g2 =t_G.g2
                & s_G.g3 =t_G.g3
                & s_G.g4 =t_G.g4


                & s_G.h0 =t_G.h0
                & s_G.h1 =t_G.h1
                & s_G.h2 =t_G.h2
                & s_G.h3 =t_G.h3


                & t_G.h4 =z_G.g4
                & t_G.L  =z_G.LP

                & s_G.L  =z_G.L

                & z_G.h4 =s_G.h4
          )
      )
     )
   )


)
// {show s_block, s_r, s_ID, s_G.L, s_G.g0, s_G.h0, s_G.g1, s_G.h1}
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
    (   Sequ_Reach( t_block, t_r, t_ID, t_G )
      & (
            targetReach( t_ID, t_G.L )
          & t_block=thread
        )
    )
);


// #timer stop;