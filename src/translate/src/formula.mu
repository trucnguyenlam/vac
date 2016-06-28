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
                thread, 
                threadnoloc,
                want,     
                have
               };


/*************************************************************************************************/
/*************               Used in internal transition                 *************************/
/*************************************************************************************************/


class Globals{
 Roles  g0;
 Roles  h0;
 Roles  g1;
 Roles  h1;
 Roles  g2;
 Roles  h2;
 Roles  g3;
 Roles  h3;
}
 g0  ~+ h0,
 h0  ~+  g1,
 g1  ~+ h1,
 h1  ~+  g2,
 g2  ~+ h2,
 h2  ~+  g3,
 g3  ~+ h3;


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


/*
    Fixed point
  s_ : means current state
  t_ : means previous state
 */

mu bool Sequ_Reach(
 blocktype  s_block,               // Block as appeared in Figure 2 of cav2010
 CS         s_r,                   // Current round
 ThreadID   s_ID,                  // Current thread id
 Roles      s_CL,                  // Local variable
 Globals    s_G                    // Global variable
)
 s_block <  s_r,
 s_r     <  s_ID,
 s_ID    <  s_CL,
 s_CL    <  s_G
( false

  // early termination

  | ( exists                   // There exists a state such that
            blocktype  t_block,
            CS         t_r,
            ThreadID   t_ID,
            Roles      t_CL,
            Globals    t_G.
        (   Sequ_Reach( t_block, t_r, t_ID, t_CL, t_G )    // That state is in fixed point and ...
          & (   targetReach( t_ID, t_CL )                  // target is reached
              & ( 
                  t_block=thread                           // And block is TLI (thread linear interface)
                )
            )
        )
     )

  /*********************************************************************************/
  // first thread (thread0) - TLI   Figure (a)
  |  (    // initial configuration for the first thread
         s_block = thread            
         & InitID0(s_ID)                // Thread ID 0
         & GlobalInit(s_G.g0)          
         & s_r=0                        // Round 0
         & s_G.h0=s_G.g0                // At this state, input = output 
         & LocalInit(s_ID, s_CL)
     )
  
  | (   // increase round_number for thread0 
         s_block=thread         // This block is TLI 
         & InitID0(s_ID)        // Thread ID 0        
         & ( exists CS t_r.     // There exists a round t_r is the previous round
              (   true
                  & increaseCS( t_r, s_r )        
                  & Sequ_Reach( thread, t_r, s_ID, s_CL, s_G ) // There exists thread0 at previous round
                  & ( exists 
                            ThreadID  t_ID,
                            Globals   a_G.
                       (     
                             Sequ_Reach( have, t_r, t_ID, s_CL, a_G ) // There is RLI at previous round
                           & increaseThreadID( s_ID, t_ID )
                           & copy_g_h( a_G, s_G, t_r )    // And input of RLI is the same output TLI 
                           & folding( s_G, a_G, s_r )     // And output of RLI is wrapped at TLI 
                       )
                    )
              )
          )
    )

/*
                                    |------||------|
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
  | ( // WRLI block generates by TLI   
         s_block=want       // TLI asks for WRLI block of remaining threads
         & ( s_r!=0 )       // Round > 0
         & ( exists             
                  CS        t_r.        // And there is already a RLI block in previous round
              (   
                  Sequ_Reach( have, t_r, s_ID, s_CL, s_G ) //HAVE=RLI
                & increaseCS( t_r, s_r )
              )
           )
         
         & ( exists 
                  ThreadID  t_ID,
                  Globals   a_G.  // And there exists TLI in which
              (   Sequ_Reach( threadnoloc, s_r, t_ID, s_CL, a_G ) //Thread completes simulation in round s_r
                & (  
                       increaseThreadID( t_ID, s_ID )  
                     & copy_g_h( s_G, a_G, s_r )  // Thread1 output matches this block input
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
  |  (   // round 0 execution of any thread (including the last thread)
         s_block=thread      
         & s_r=0             
         & InitID1(s_ID)     // thread ID different from thread 0
         & ( exists  
                ThreadID t_ID,    
                Globals  t_G.       
              (
                Sequ_Reach( threadnoloc, s_r, t_ID, s_CL, t_G )    // After a thread finishes its execution
                & 
                (  increaseThreadID ( t_ID, s_ID )
                   & t_G.h0 = s_G.g0             // Map output of thread_i to input of thread_i+1
                )
              )
           )
         & s_G.h0=s_G.g0  // At this state, input = output
         & LocalInit( s_ID, s_CL )
     )

  | ( // increase ROUND for TLI (not thread0) 
        s_block=thread        
      & ( s_r!=0 )            // At some round > 0
      & !maxThreadID( s_ID )  // This TLI must not be the last thread
      & ( exists 
             CS t_r.   
            (
                 Sequ_Reach( thread, t_r, s_ID, s_CL, s_G )
               & increaseCS( t_r, s_r )
            )
        )
      & ( exists 
            Globals b_G.         // and there exists a RLI block with global b_G such that
           (   
               ( exists 
                       CS        t_r,
                       ThreadID  t_ID,
                       Globals   a_G.
                   (   Sequ_Reach( have, t_r, t_ID, s_CL, a_G )  // There is RLI at previous round with
                     & (   
                           increaseCS( t_r, s_r )               
                         & increaseThreadID( s_ID, t_ID )             
                         & copy_g_h( a_G, s_G, t_r )            // Output of TLI == input of RLI
                         & copy_h_h( a_G, b_G, t_r )            // Output of RLI == output of WRLI block
                       )
                   )
               )
             & Sequ_Reach( want, s_r, s_ID, s_CL, b_G )    // this TLI is in WRLI block
             & copy_g_g( b_G, s_G, s_r )                   // Input of TLI is the same as input of WRLI block
           )
        )
    )

/*                                   ------------------
                                    |  ------  ------  |
                                    | | T_i  ||H_i+1 | |
                                    | |      ||      | |
                                    | | s_G  || a_G  | |
                                    | |      ||      | |
                                    |  ------  ------  |
                                    |        b_G    W23|
                                     -----------------
*/

  // increase round_number for last thread 
  | (    s_block=thread
         & ( s_r!=0 )
         & maxThreadID( s_ID )  // last thread
         & ( exists 
                    CS t_r,
                    Globals a_G.
               (
                    Sequ_Reach( thread, t_r, s_ID, s_CL, s_G )  // There exists this TLI at previous round
                  & increaseCS( t_r, s_r )

                  & Sequ_Reach( want, s_r, s_ID, s_CL, a_G )    // WRLI block
                  & (   copy_h_h( a_G, s_G, t_r )
                      & copy_g_g( a_G, s_G, s_r )
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
  // last thread in RLI (backward phase)   Figure 2 (e)
  | ( // RLI from the last TLI (stop forward propagation, start backward)   
        s_block=have    
      & (
             maxThreadID(s_ID) 
           & Sequ_Reach( threadnoloc, s_r, s_ID, s_CL, s_G )
        )
    )

/*                                  |------|        |------|
                                    |  TL  |        |  TL  |
                                    |      |        |      |
                                    | s_G  | become | s_G  |
                                    |      |  -->   |      |
                                    |      |        |      |
                                    |------|        |------|
                                       WL              HL
*/

  /*********************************************************************************/
  // Match RLI block (backward phase)   Figure 2 (f)  
  | (    // RLI generated by TLI and RLI    
           s_block=have
         & !maxThreadID( s_ID )  
         & (    s_r=0
              | Sequ_Reach( want, s_r, s_ID, s_CL, s_G )   // There exists WRLI
           )
         & ( exists 
                   Globals b_G.
                  (     ( exists 
                             Globals a_G.
                            (    Sequ_Reach( threadnoloc, s_r, s_ID, s_CL, a_G )
                               & (   copy_g_g( s_G, a_G, s_r )
                                   & copy_g_h( b_G, a_G, s_r )
                                 )
                            )
                        )
                     &  ( exists 
                              ThreadID  t_ID.
                             (
                                  Sequ_Reach( have, s_r, t_ID, s_CL, b_G )
                                & (  copy_h_h( s_G, b_G, s_r )
                                   & increaseThreadID( s_ID, t_ID )
                                  )
                             )
                        )
                  )
           )
    )

/*                                  |--------------|
                                    | T2   ||  H3  |
                                    |      ||      |
                                    | a_G  || b_G  |
                                    |      ||      |
                                    |--------------|
                                          s_G   W23
*/

  /*********************************************************************************/
   // forgetting local states for  each thread
  | ( exists blocktype  t_block,
             CS         t_r,
             ThreadID   t_ID,
             Roles      t_CL,
             Globals    t_G.
             (    Sequ_Reach( t_block, s_r, t_ID, t_CL, t_G )
                & (  
                    (s_block=threadnoloc) & (t_block=thread)
                  )
                & copy_g_g( t_G, s_G, s_r )
                & copy_h_h( t_G, s_G, s_r )
             )
    )


/*                                  |-----------------|
                                    |       T         |
                                    |                 |
                                    | s_G             |
                                    |                 |
                                    | g  ~~~------>  h|
                                    |-----------------|
*/

//*********************************************************************************/
// forward propagation on internal transitions
//*********************************************************************************/

//*************** Round 0
  |  (
        (   s_r=0      // Round 0
          & (s_block=thread)
        )
      & (exists                  // There exists an internal state that
           Roles   t_CL,
           Globals t_G.
           (    (   Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )  
                  & copy_g_and_h_0( s_G, t_G ) 
                )
               &(
                  ( CanAssign( t_CL, t_G.h0, s_CL )  
                    & UpdateGlobal( s_CL, t_G.h0, s_G.h0 )
                  )
                  | CanRevoke( t_CL, t_G.h0, s_CL, s_G.h0 )
                )
           )
      )
    )

//*************** Round 1
  |  (
        (   s_r=1      // Round 1
          & (s_block=thread)
        )
      & (exists                  // There exists an internal state that
           Roles   t_CL,
           Globals t_G.
           (    (   Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )  
                  & copy_g_and_h_1( s_G, t_G ) 
                )
               &(
                  ( CanAssign( t_CL, t_G.h1, s_CL )  
                    & UpdateGlobal( s_CL, t_G.h1, s_G.h1 )
                  )
                  | CanRevoke( t_CL, t_G.h1, s_CL, s_G.h1 )
                )
           )
      )
    )

//*************** Round 2
  |  (
        (   s_r=2      // Round 2
          & (s_block=thread)
        )
      & (exists                  // There exists an internal state that
           Roles   t_CL,
           Globals t_G.
           (    (   Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )  
                  & copy_g_and_h_2( s_G, t_G ) 
                )
               &(
                  ( CanAssign( t_CL, t_G.h2, s_CL )  
                    & UpdateGlobal( s_CL, t_G.h2, s_G.h2 )
                  )
                  | CanRevoke( t_CL, t_G.h2, s_CL, s_G.h2 )
                )
           )
      )
    )

//*************** Round 3
  |  (
        (   s_r=3     // Round 3
          & (s_block=thread)
        )
      & (exists                  // There exists an internal state that
           Roles   t_CL,
           Globals t_G.
           (    (   Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )  
                  & copy_g_and_h_3( s_G, t_G ) 
                )
               &(
                  ( CanAssign( t_CL, t_G.h3, s_CL )  
                    & UpdateGlobal( s_CL, t_G.h3, s_G.h3 )
                  )
                  | CanRevoke( t_CL, t_G.h3, s_CL, s_G.h3 )
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
    Roles      t_CL,
    Globals    t_G.
    (   Sequ_Reach( t_block, t_r, t_ID, t_CL, t_G )
      & (   
            targetReach( t_ID, t_CL )
          & ( t_block=thread )
        )
    )
);

#timer stop;
