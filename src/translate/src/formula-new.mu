/*************************************************************************************************/
/********************             DESIGN FOR MULTIPLE THREADS         ****************************/
/********************            WITH THE SAME INTERNAL MOVES         ****************************/
/*************************************************************************************************/
#timer go;

enum CS {0..3}; // Round or context switch

// Increase context-switch counter
bool increaseCS(CS s, CS t)
s ~+ t
( false
  | ( s=0 & t=1 )
  | ( s=1 & t=2 )
  | ( s=2 & t=3 )
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
  Copy global variable at CS 3 (mean round 3)
 */
bool copy_g_and_h_3( Globals s_G, Globals t_G)
 s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 & s_G.h0 =t_G.h0
    & s_G.g1 =t_G.g1 & s_G.h1 =t_G.h1
    & s_G.g2 =t_G.g2 & s_G.h2 =t_G.h2
    & s_G.g3 =t_G.g3
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
     )

  | (   // For subsequent round
          s_block=thread       // This block is TLI
        & s_r != 0             // Round > 0
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
                       & (   copy_g_h( a_G, s_G, t_r )    // And input of RLI is the same output TLI
                           & folding( s_G, a_G, s_r )     // And output of RLI is wrapped at TLI
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
            (   Sequ_Reach( threadnoloc, s_r, t_ID, a_G ) //Thread completes simulation in round s_r
              & increaseThreadID( t_ID, s_ID )
              & (   copy_g_h( s_G, a_G, s_r )  // Thread1 output matches this block input
                  & folding( a_G, s_G, s_r )   // And this block output wrap thread1 input
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
              Sequ_Reach( threadnoloc, 0, t_ID, t_G )    // After a thread finishes its execution
              & Fake_Ordering_Globals( s_G, t_G )
              & increaseThreadID ( t_ID, s_ID )
              & t_G.h0 = s_G.g0             // Map output of thread_i to input of thread_i+1
            )
         )
        & s_G.h0=s_G.g0                // input = output
        & s_G.h1=s_G.g1                // input = output
        & s_G.h2=s_G.g2                // input = output
        & s_G.h3=s_G.g3                // input = output
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
           (   Sequ_Reach( want, s_r, s_ID, b_G )    // this TLI is in WRLI block
             & ( exists    /*  Sequ_Reach::@Exists7::@Exists8 */
                       CS        t_r,
                       ThreadID  t_ID,
                       Globals   a_G.
                   (  (    Sequ_Reach( have, t_r, t_ID, a_G )  // There is RLI at previous round with
                         & increaseCS( t_r, s_r )
                         & increaseThreadID( s_ID, t_ID )
                       )
                     & (   copy_g_h( a_G, s_G, t_r )            // Output of TLI == input of RLI
                         & copy_h_h( a_G, b_G, t_r )            // Output of RLI == output of WRLI block
                         & copy_g_g( b_G, s_G, s_r )                   // Input of TLI == input of WRLI block
                       )
                   )
               )
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
            (   Sequ_Reach( thread, t_r, s_ID, s_G )  // There exists this TLI at previous round
              & increaseCS( t_r, s_r )
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
        s_block=have
      & maxThreadID( s_ID )
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
         s_block=have
       & nonMaxThreadID( s_ID )
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
                         (    (   Sequ_Reach( have, s_r, t_ID, b_G )
                                & increaseThreadID( s_ID, t_ID )
                              )
                            & copy_h_h( s_G, b_G, s_r )
                         )
                    )
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
  | ( exists                    /* Sequ_Reach::@Exists14 */   // Wrong ordering
          Globals    t_G.
       (    Sequ_Reach( thread, s_r, s_ID, t_G )
          & Fake_Ordering_All (thread, s_r, s_ID, t_G, s_block, s_r, s_ID, s_G)
          & (s_block=threadnoloc)
          & (  copy_g_g( t_G, s_G, s_r )
             & copy_h_h( t_G, s_G, s_r )
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

//*************** Round 0
  |  (
        (   s_r=0      // Round 0
          & (s_block=thread)
        )
      & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 0, s_ID, t_G )
              ) & (
                    CanAssign_0( t_G, s_G )
                  & copy_g_and_h_0( t_G, s_G )
              )
           )
      )
    )

  |  (
        (   s_r=0      // Round 0
          & (s_block=thread)
        )
      & (exists        /* Sequ_Reach::@Exists16 */              // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 0, s_ID, t_G )
              )
            & (
                CanRevoke_0( t_G, s_G )
              & copy_g_and_h_0( t_G, s_G )
              )
           )
      )
    )

  |  (
        (   s_r=0      // Round 0
          & (s_block=thread)
        )
      & (exists        /* Sequ_Reach::@Exists17 */              // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 0, s_ID, t_G )
              )
            & (
                UpdateGlobal_0( t_G, s_G )
              & copy_g_and_h_0( t_G, s_G )
              )
           )
      )
    )

//*************** Round 1
  |  (
        (   s_r=1      // Round 1
          & (s_block=thread)
        )
      & (exists      /* Sequ_Reach::@Exists18 */              // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 1, s_ID, t_G )
              ) & (
                    CanAssign_1( t_G, s_G )
              & copy_g_and_h_1( t_G, s_G )
              )
           )
      )
    )
 |  (
        (   s_r=1      // Round 1
          & (s_block=thread)
        )
      & (exists      /* Sequ_Reach::@Exists19 */              // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 1, s_ID, t_G )
              )
            & (
                    CanRevoke_1( t_G, s_G )
              & copy_g_and_h_1( t_G, s_G )
              )
           )
      )
    )
 |  (
        (   s_r=1      // Round 1
          & (s_block=thread)
        )
      & (exists      /* Sequ_Reach::@Exists20 */              // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 1, s_ID, t_G )
              )
            & (
                UpdateGlobal_1( t_G, s_G )
              & copy_g_and_h_1( t_G, s_G )
              )
           )
      )
    )

//*************** Round 2
  |  (
        (   s_r=2      // Round 2
          & (s_block=thread)
        )
      & (exists         /* Sequ_Reach::@Exists21 */            // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 2, s_ID, t_G )
              ) & (
                    CanAssign_2( t_G, s_G )
              & copy_g_and_h_2( t_G, s_G )
              )
           )
      )
    )
 |  (
        (   s_r=2      // Round 2
          & (s_block=thread)
        )
      & (exists         /* Sequ_Reach::@Exists22 */            // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 2, s_ID, t_G )
              )
            & (
                CanRevoke_2( t_G, s_G )
              & copy_g_and_h_2( t_G, s_G )
              )
           )
      )
    )
 |  (
        (   s_r=2      // Round 2
          & (s_block=thread)
        )
      & (exists         /* Sequ_Reach::@Exists23 */            // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 2, s_ID, t_G )
              )
            & (
                UpdateGlobal_2( t_G, s_G )
              & copy_g_and_h_2( t_G, s_G )
              )
           )
      )
    )

//*************** Round 3
  |  (
        (   s_r=3     // Round 3
          & (s_block=thread)
        )
      & (exists        /* Sequ_Reach::@Exists24 */            // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 3, s_ID, t_G )
              ) & (
                    CanAssign_3( t_G, s_G )
               & copy_g_and_h_3( t_G, s_G )
              )
           )
      )
    )
  |  (
        (   s_r=3     // Round 3
          & (s_block=thread)
        )
      & (exists        /* Sequ_Reach::@Exists25 */            // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 3, s_ID, t_G )
              )
            & (
                 CanRevoke_3( t_G, s_G )
              & copy_g_and_h_3( t_G, s_G )
              )
           )
      )
    )
  |  (
        (   s_r=3     // Round 3
          & (s_block=thread)
        )
      & (exists        /* Sequ_Reach::@Exists26 */            // There exists an internal state that
           Globals t_G.
           (  (  Sequ_Reach( thread, 3, s_ID, t_G )
              )
            & (
                UpdateGlobal_3( t_G, s_G )
              & copy_g_and_h_3( t_G, s_G )
              )
           )
      )
    )
);

#size Sequ_Reach;
#timer;

/******************************************************************************************************/
//                                       Reachabibility check                                         *
/******************************************************************************************************/

( exists
    blocktype  t_block,
    CS         t_r,
    ThreadID   t_ID,
    Globals    t_G.
    (   Sequ_Reach( t_block, t_r, t_ID, t_G )
      & (
            targetReach( t_ID, t_G.L )
          & ( t_block=thread )
        )
    )
);


#timer stop;
