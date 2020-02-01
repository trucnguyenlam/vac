bool increment (CS a, CS b)
(
false
|(a=0 & b=1)
|(a=1 & b=2)
|(a=2 & b=3)
|(a=3 & b=4)
|(a=4 & b=5)
);



/***********************************************************************************/




bool copy_g_and_h_1( Globals s_G, Globals t_G) 
s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 & s_G.h0 =t_G.h0 
    & s_G.g1 =t_G.g1 
);



bool copy_g_and_h_0( Globals s_G, Globals t_G) 
s_G ~+ t_G
(   true
    & s_G.g0 =t_G.g0 
    & s_G.g1 =t_G.g1 & s_G.h1 =t_G.h1 
);












mu bool Init_Reach(
 PrCount s_pc,
 Local   s_CL,
 Global  s_G
)
 s_pc    <  s_CL,
 s_CL    <  s_G
(
  false

  // initial conf

  | initPC(s_pc)


  // forward propagation on internal transitions 

  |  ( exists 
           PrCount t_pc,
           Local   t_CL,
           Global  t_G.
           (   Init_Reach( t_pc, t_CL, t_G )
               &(t_G.v1=0 | ( t_G.v1=1 & t_CL.v0=1 ) )
               &( ( programInt1( 2, t_pc, s_pc, t_CL, s_CL, t_G, s_G )
                    & CopyVariables_ProgramInt( 2, t_pc, t_CL, s_CL, t_G, s_G )
                  )
                  | programInt3( 2, t_pc, s_pc, t_CL, s_CL, t_G, s_G )
                )
           )
     )

  | ( exists PrCount t_pc.
           (     Init_Reach( t_pc, s_CL, s_G )
               &(s_G.v1=0 | ( s_G.v1=1 & s_CL.v0=1 ) )
               & programInt2( 2, t_pc, s_pc, s_CL, s_G )
           )
      )

);

#size Init_Reach;





bool GlobalInit(Global CG)
( exists 
         Module  s_mod,
         PrCount s_pc,
         Local   s_CL.
              (   Init_Reach( s_pc, s_CL, CG )
                & Target_Init(s_pc )
              )
);


/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/









/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/
/******                                                                                    *******/
/******                               Reachability Algorithm                               *******/
/******                                                                                    *******/
/*************************************************************************************************/
/*************************************************************************************************/
/*************************************************************************************************/


mu bool Sequ_Reach(
 CS      s_r,
 bool    s_reach,
 Module  s_mod,
 PrCount s_pc,
 Local   s_CL,
 Globals s_G
)
 s_r     <  s_reach,
 s_reach <  s_mod,
 s_mod   <  s_pc,
 s_pc    <  s_CL,
 s_CL    <  s_G
((s_mod=0 | s_mod=1) & (
  false


  // initial conf

  |  (     s_reach=0
         & s_G.h0=s_G.g0
         & s_G.h1=s_G.g1
         & s_r=0
     )

  //set the bit reach to 1

  |  (
         Sequ_Reach( s_r, 0, s_mod, s_pc, s_CL, s_G )
       & target( s_mod, s_pc )
     )


/*
  |  ( exists CS t_r.
           (
               Sequ_Reach( t_r, 1, s_mod, s_pc, s_CL, s_G )
             & increaseCS( t_r, s_r )
             & s_reach
           )
     )
*/

 // increase the round number
 | ( exists CS t_r.
      (    Sequ_Reach( t_r, s_reach, s_mod, s_pc, s_CL, s_G )
         & increaseCS( t_r, s_r )
          
      )
   )


  // forward propagation on internal transitions 

//*************** 0



  |  ( 
        s_r=0
      & (exists
           PrCount t_pc,
           Local   t_CL,
           Globals t_G.
           (    (   Sequ_Reach( 0, s_reach, s_mod, t_pc, t_CL, t_G )
                  & copy_g_and_h_0(s_G,t_G)
                )
               &(t_G.h0.v1=0 | ( t_G.h0.v1=1 & t_CL.v0=1 ) )
               &(
                  ( programInt1(s_mod,t_pc,s_pc,t_CL,s_CL,t_G.h0,s_G.h0)
                    & CopyVariables_ProgramInt(s_mod,t_pc,t_CL,s_CL,t_G.h0,s_G.h0)
                  )
                  | programInt3( s_mod, t_pc, s_pc, t_CL, s_CL, t_G.h0, s_G.h0 )
                )
           )
      )
    )


  | (   
         (s_G.h0.v1=0 | ( s_G.h0.v1=1 & s_CL.v0=1 ) )
       & (exists PrCount t_pc.
             (  
                   Sequ_Reach( 0, s_reach, s_mod, t_pc, s_CL, s_G )
                 & programInt2(s_mod,t_pc,s_pc,s_CL,s_G.h0)
             )
         )
    )




//*************** 1



  |  ( 
         s_r=1
      & (exists
           PrCount t_pc,
           Local   t_CL,
           Globals t_G.
           (    (   Sequ_Reach( 1, s_reach, s_mod, t_pc, t_CL, t_G )
                  & copy_g_and_h_1(s_G,t_G)
                )
               &(t_G.h1.v1=0 | ( t_G.h1.v1=1 & t_CL.v0=1 ) )
               &(
                  ( programInt1(s_mod,t_pc,s_pc,t_CL,s_CL,t_G.h1,s_G.h1)
                    & CopyVariables_ProgramInt(s_mod,t_pc,t_CL,s_CL,t_G.h1,s_G.h1)
                  )
                  | programInt3( s_mod, t_pc, s_pc, t_CL, s_CL, t_G.h1, s_G.h1 )
                )
           )
      )
    )


  | (  
         (s_G.h1.v1=0 | ( s_G.h1.v1=1 & s_CL.v0=1 ) )
       & (exists PrCount t_pc.
             (
                   Sequ_Reach( 1, s_reach, s_mod, t_pc, s_CL, s_G )
                 & programInt2(s_mod,t_pc,s_pc,s_CL,s_G.h1)
             )
         )
    )

));






/******************************************************************************/

bool thread1(
 bool     s_reach,
 Globals  s_G
)
s_reach < s_G
(
   GlobalInit(s_G.g0) &
   ( exists
         CS      s_r,
         PrCount s_pc,
         Local   s_CL.
        (   Sequ_Reach( s_r, s_reach, 1, s_pc, s_CL, s_G )
          & max_round( s_r )
        )
   )
);

/******************************************************************************/

bool thread0(
 bool     s_reach,
 Globals  s_G
)
s_reach < s_G
(  exists
         CS      s_r,
         PrCount s_pc,
         Local   s_CL.
        (   Sequ_Reach( s_r, s_reach, 0, s_pc, s_CL, s_G )
          & max_round( s_r )
        )
);


/******************************************************************************/

mu bool Conc_Reach( 
 bool     s_reach, 
 Globals  s_G 
)
s_reach < s_G
(

 false
  // embibe Sequ_Reachability

 | thread0( s_reach, s_G )
 
 |  (exists bool t_reach, bool v_reach, Globals v_G, CS r.
         (   ( exists  Globals t_G.
                 (   Conc_Reach( t_reach, t_G )
                   & copy_g_g( t_G, s_G, r )
                   & copy_g_h( v_G, t_G, r )
                 )
             ) // T | V
             & Conc_Reach( v_reach, v_G )
             & copy_h_h( v_G, s_G, r )
             & ( !s_reach | t_reach | v_reach ) 
             & max_round( r )
         )
   )

);



/******************************************************************************************************/
//                                       Reachabibility check                                         *
/******************************************************************************************************/

(

   ( exists 
            PrCount t_pc,
            Local   t_CL,
            Global  t_G.
        (   Init_Reach( t_pc, t_CL, t_G )
          & target( 2, t_pc)
        )
     )

|

( exists bool t_reach, bool v_reach,  Globals t_G, Globals v_G, CS r. 
   (   thread1(t_reach, t_G)
     & Conc_Reach( v_reach, v_G )
     & copy_g_h( v_G, t_G, r )
     & ( t_reach | v_reach )
     & folding( t_G, v_G, r )
     & max_round( r )
   )
));










/************************************************************************************************************/



bool  checkGlobal2( 
 CS k, 
 Globals A, 
 Globals B 
) //check A[2][k-1]=B[2][k]
(
  false
  | (k=1 & A.h0 = B.h1 )
  | (k=2 & A.h1 = B.h2 )
  | (k=3 & A.h2 = B.h3 )
  | (k=4 & A.h3 = B.h4 )
  | (k=5 & A.h4 = B.h5 )
  | (k=6 & A.h5 = B.h6 )
);



/**
  move0 is the move for Eve player

*/

bool move0(          
 bool     s_player,     // s_player is Eve 
 bool     t_player,     // t_player is Adam
 bool     s_mode0,      // mode0  is  in
 bool     t_mode0,      
 bool     s_mode1,      // mode1  is  al
 bool     t_mode1, 
 PrCount  s_pc,
 PrCount  t_pc,
 Local    s_CL,
 Local    t_CL,
 Globals  s_GH,
 Globals  t_GH,
 Globals  s_XY,
 Globals  t_XY
)
(

false

|(

/* 
   (0,g,h,x,y) --> (1,g,h',x,y,l') by imbibing a thread linear interface of size k
   s_player=0  & s_mode0=0  & s_mode1=0 correspond to 0
   s_player=1  & s_mode0=0  & s_mode1=0 correspond to 1
   t_pc, t_CL correspond to l'
   S_GH corresponds to (g,h)
   t_GH corresponds to (g,h')
   s_XY corresponds to (x,y)
*/

  s_player=0  & s_mode0=0  &  s_mode1=0  &  
  t_player=1  & t_mode0=0  &  t_mode1=0  &   
  (exists CS k.
       ( true
         & max_round( k )
         & copy_g_g( s_GH, t_GH, k )      // Why not copy_h_h

         & copy_g_g( s_XY, t_XY, k )       // stat of x, y is preserved
         & copy_h_h( s_XY, t_XY, k ) 
       )
  )
  & ( exists CS k.
       (true
         & max_round( k )
         & (  exists 
               Globals  G,
               bool     reach. 
                (true
                 &  copy_g_h( G, s_GH, k )  
                 &  copy_h_h( G, t_GH, k )  
                 &  Sequ_Reach( k, reach, 0, t_pc, t_CL, G )
                )
           )
       )
    )
)

|(
/* 
   (2,g,h) --> (2,g,h') by imbibing a thread linear interface of size k (h,h',*)
   s_player=0  & s_mode0=1  & s_mode1=0 correspond to 2
   S_GH corresponds to (g,h)
   t_GH corresponds to (g,h')
*/
    s_player=0  &  s_mode0=1  & t_mode0=0
  & t_player=1  &  s_mode1=1  & t_mode1=0
  & (exists CS k.
       (true
         & max_round( k )
         & (  exists 
               Globals  G,
               bool     reach. 
                (true
                 &  copy_g_h( G, s_GH, k )  
                 &  copy_h_h( G, t_GH, k )  
                 &  thread0(reach,G)
                )
           )
       )
    )
 )

|(
/*
   START --> (1,g,h,l) which is an initial thread interface: 
     i.e.  (g1 is initial) and (g1,...gk) ---> Thread -->   (h1,...hk) 
          and further thread 1 can use such an interface and end up in local state l

   s_player=0  &  s_mode0=0  &  s_mode1=1  correspond to START
   t_player=1  &  t_mode0=0  &  t_mode1=1  correspond to 1
   t_pc, t_CL correspond to l
   t_GH corresponds to (g,h)

*/

    s_player=0  &  s_mode0=0   & s_mode1=1
  & t_player=1  &  t_mode0=0   & t_mode1=1
  & (exists CS k.
       (true
         & max_round( k )
         & Sequ_Reach( k, reach, 1, t_pc, t_CL, t_GH )
       )
    )
 )

);





bool move1(
 bool     s_player,
 bool     t_player,
 bool     s_mode0,   
 bool     t_mode0,   
 bool     s_mode1,
 bool     t_mode1,
 PrCount  s_pc,
 PrCount  t_pc,
 Local    s_CL,
 Local    t_CL,
 Globals  s_GH,
 Globals  t_GH,
 Globals  s_XY,
 Globals  t_XY
)
(false

|(
/*
  (1,g,h',x,y,l') --> (0,g,h',x,y') by imbibing a thread linear interface of size k-1 that matches l' and y'_k-1=h'_k
  (i.e. there is a thread linear interace (y,y',l') of size k-1 and further y'_k-1 = h'_k)

  s_player=1  & s_mode0=0  &  s_mode1=0   correspond to 1   
  t_player=0 & t_mode0=0 &  t_mode1=0  correspond to 0
  s_pc, s_CL correspond to l'
  S_GH  corresponds to (g,h)
  t_GH corresponds to (g,h')
  S_XY  corresponds to (x,y)
  t_XY corresponds to (x,y')
*/

    s_player=1  & s_mode0=0  &  s_mode1=0   
  & t_player=0  & t_mode0=0  &  t_mode1=0  
  & (exists CS k.
       ( true
         & max_round( k )
         & copy_g_g( s_GH, t_GH, k )  
         & copy_h_h( s_GH, t_GH, k )  
         & checkGlobal2( k, t_XY, t_GH ) //check t_XY[2][k-1]=t_GH[2][k]
       )
    )
  & (exists CS km1, k.
       ( true
         & increment(km1,k)
         & max_round( k )
         & (  exists 
               Globals  G, //(y,y')
               bool     reach. 
                (true
                 &  copy_g_h( G, s_XY,  k )
                 &  copy_h_h( G, t_XY, k )
                 &  Sequ_Reach( km1, reach, 0, s_pc, t_CL, G )
                )
           )
       )
    )
)

|(

/*
  (1,g,h,l) --> (0,g,h,x,y) provided (x,y,l) in a initial thread linear interface of length k-1 where y_k-1=h_k

  s_player=1  & s_mode0=0   &  s_mode1=1   correspond to 1 
  t_player=0  & t_mode0=0   &  t_mode1=0   correspond to 0 

  s_pc, s_CL correspond to l
  S_GH  corresponds to (g,h)
  t_GH corresponds to (g,h')
  t_XY corresponds to (x,y)
*/

    s_player=1  & s_mode0=0   &  s_mode1=1  
  & t_player=0  & t_mode0=0   &  t_mode1=0 
  & (exists CS k.
       ( true
         & max_round( k )
         & copy_g_g( s_GH, t_GH, k )  
         & copy_h_h( s_GH, t_GH, k )  
         & checkGlobal2( k, t_XY, t_GH ) //check t_XY[2][k-1]=t_GH[2][k]
       )
    )
  & (exists CS km1, k.
       ( true
         & ( increment(km1,k) & max_round(k) )
         & ( exists 
               Globals  G, //(y,y')
               bool     reach. 
                (Sequ_Reach( km1, reach, 1, s_pc, s_CL, G )
                )
           )
       )
    )   
 )


|(

/*
  (1,g,h,l) --> (2,g,h)  if there is no inital thread linear interface (x,y,l) of length k-1 where y_k-1=h_k

  s_player=1  & s_mode0=0   &  s_mode1=1   correspond to 1 
  t_player=0 & t_mode0=1  &  t_mode1=0  correspond to 2 

  s_pc, s_CL correspond to l
  S_GH  corresponds to (g,h)
  t_GH corresponds to (g,h)
*/


    s_player=1  & s_mode0=0  & s_mode1=1 
  & t_player=0 & t_mode0=1 & t_mode1=0
  & (exists CS k.
       ( true
         & max_round( k )
         & copy_g_g( s_GH, t_GH, k )  
         & copy_h_h( s_GH, t_GH, k )  
       )
    )
  &  ( forall
             CS       k,
             CS       km1,
             bool     reach,
             Gloabals t_XY.
             (  false
                | (!max_round( k ))
                | (!increase( km1, k ))
                | (!Sequ_Reach( km1, reach, 1, s_pc, s_CL, t_XY )
                | (!checkGlobal2( k, t_XY, t_GH )  )
             )
      )
 )

);



bool win_game(
 bool     s_player,
 bool     s_mode0,   
 bool     s_mode1,   
 PrCount  s_pc,
 Local    s_CL,
 Globals  s_GH,
 Globals  s_XY
)
(false

|(

/*
  (0,g,h,x,y) --> PL0WINS if (g,h) wraps but (x,y) does not wrap

  s_player=0  & s_mode0=0  & s_mode1=0 correspond to 0
  S_GH  corresponds to (g,h)
  S_XY  corresponds to (x,y)

*/
    s_player=0  & s_mode0=0  & s_mode1=0
  & (exists CS km1, CS k.
       ( true
         &  max_round( k )
         &  increase( km1, k )
         &  folding( s_GH, s_GH, k )
         & !folding( s_XY, s_XY, km1 )
       )
    )
 )
 

|(
/*
  (2,g,h) --> PL0wins if (g,h) wraps

  s_player=0  & s_mode0=1  & s_mode1=0 correspond to 2
  S_GH  corresponds to (g,h)

*/
    s_player=0  & s_mode0=1  & s_mode1=0
  & (exists CS km1, CS k.
       ( true
         &  max_round( k )
         &  folding( s_GH, s_GH, k )
       )
    )  
 )

);


bool init_game(
 bool     s_player,
 bool     s_mode0,   
 bool     s_mode1,   
 PrCount  s_pc,
 Local    s_CL,
 Globals  s_GH,
 Globals  s_XY
)
(
   s_player=0  &  s_mode0=0  &  s_mode1=1   // correspond to START
);




mu bool reach_game( 
 bool     s_player,
 bool     s_mode0,   
 bool     s_mode1,   
 PrCount  s_pc,
 Local    s_CL,
 Globals  s_GH,
 Globals  s_XY
)
(
 false


  // imbibe winning
|  win_game(s_player,s_mode0,s_mode1,s_pc,s_CL,s_GH,s_XY)

  // set attractor for player 0
|( exists
       bool     t_player,
       bool     t_mode0,   
       bool     t_mode1,   
       PrCount  t_pc,
       Local    t_CL,
       Globals  t_GH,
       Globals  t_XY.
     (   reach_game( t_player,t_mode0,t_mode1,t_pc,t_CL,t_GH,t_XY)
       & move0(s_player,t_player,s_mode0,t_mode0,s_mode1,t_mode1,s_pc,t_pc,s_CL,t_CL,s_GH,t_GH,s_XY,t_XY)
     )
 )

  // set attractor for player 1
|( forall
       bool     t_player,
       bool     t_mode0,   
       bool     t_mode1,   
       PrCount  t_pc,
       Local    t_CL,
       Globals  t_GH,
       Globals  t_XY.
     (   !reach_game( t_player,t_mode0,t_mode1,t_pc,t_CL,t_GH,t_XY)
       | !move1(s_player,t_player,s_mode0,t_mode0,s_mode1,t_mode1,s_pc,t_pc,s_CL,t_CL,s_GH,t_GH,s_XY,t_XY)
     )
 )


|( exists
       bool     t_player,
       bool     t_mode0,   
       bool     t_mode1,   
       PrCount  t_pc,
       Local    t_CL,
       Globals  t_GH,
       Globals  t_XY.
     (   reach_game( t_player,t_mode0,t_mode1,t_pc,t_CL,t_GH,t_XY )
       & init_game(t_player,t_mode0,t_mode1,t_pc,t_CL,t_GH,t_XY)
     )
 )


);




// query

( exists
       bool     t_player,
       bool     t_mode0,   
       bool     t_mode1,   
       PrCount  t_pc,
       Local    t_CL,
       Globals  t_GH,
       Globals  t_XY.
     (   reach_game( t_player,t_mode0,t_mode1,t_pc,t_CL,t_GH,t_XY )
       & init_game(t_player,t_mode0,t_mode1,t_pc,t_CL,t_GH,t_XY)
     )
 );





