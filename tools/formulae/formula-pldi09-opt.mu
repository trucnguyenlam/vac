// Winning:
//   1 set is frontier
//   0 set is reachable
// Winning will call Reach
// Reach will compute successors of the 1-set of Winning
// Winning will take this, and add the new states discovered as 1-set, and also copy it's old 1-set to 0 set.

mu bool Frontier(
 Module  s_mod,
 PrCount s_pc,
 Local   s_CL,
 Global  s_CG,
 Local   s_ENTRY_CL,
 Global  s_ENTRY_CG
);

mu bool Frontier_modpc(
 Module  s_mod,
 PrCount s_pc
);

mu bool Reachable(
 Module  s_mod,
 PrCount s_pc,
 Local   s_CL,
 Global  s_CG,
 Local   s_ENTRY_CL,
 Global  s_ENTRY_CG
);

mu bool Winning(
 bool    s_fr,
 Module  s_mod,
 PrCount s_pc,
 Local   s_CL,
 Global  s_CG,
 Local   s_ENTRY_CL,
 Global  s_ENTRY_CG
)
s_fr  <  s_mod,
s_mod <  s_pc,
s_pc  <  s_CL,
s_CL  ~+ s_ENTRY_CL,
s_CL  <  s_CG,
s_CG  ~+ s_ENTRY_CG
(
 
  // early termination
  ( exists Module  t_mod, PrCount t_pc, Local t_CL, Global t_CG, Local t_ENTRY_CL, Global  t_ENTRY_CG.
        (Winning(0,t_mod,t_pc,t_CL,t_CG,t_ENTRY_CL,t_ENTRY_CG) & target(t_mod,t_pc) )
  )

  | Winning(1,s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG)

  | ( Reachable(s_mod, s_pc, s_CL, s_CG, s_ENTRY_CL, s_ENTRY_CG) & s_fr=1 )


  // forward propagation on SkipCall (jump from exit to return)
  |( s_fr=1 & enforce(s_mod, s_CL, s_CG) &
    (exists PrCount t_pc, Global t_CG, Module u_mod, PrCount u_pc, Local u_ENTRY_CL.
       ( Frontier_modpc(s_mod,t_pc) | Frontier_modpc(u_mod,u_pc) ) &
       ( exists  Local t_CL.
          (
              (Winning(1,s_mod,t_pc,t_CL,t_CG,s_ENTRY_CL,s_ENTRY_CG)
            & SkipCall(s_mod,t_pc,s_pc))
            & SetReturnTS(s_mod,u_mod,t_pc,u_pc,t_CL,s_CL,t_CG,s_CG)
            & programCall(s_mod,u_mod,t_pc,t_CL,u_ENTRY_CL,t_CG)

       )  )
       &
       ( exists Local u_CL, Global u_CG.
          (   Winning(1,u_mod,u_pc,u_CL,u_CG,u_ENTRY_CL,t_CG)
            & SetReturnUS(s_mod,u_mod,t_pc,u_pc,u_CL,s_CL,u_CG,s_CG)
            & Exit(u_mod,u_pc)
          )
       )
    )
  )

);

mu bool Frontier(
 Module  s_mod,
 PrCount s_pc,
 Local   s_CL,
 Global  s_CG,
 Local   s_ENTRY_CL,
 Global  s_ENTRY_CG
)
s_mod <  s_pc,
s_pc  <  s_CL,
s_CL  ~+ s_ENTRY_CL,
s_CL  <  s_CG,
s_CG  ~+ s_ENTRY_CG 
(
     Winning(1,s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG)        // s is reachable 
  & !Winning(0,s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG)       // s is not in old set
);

mu bool Frontier_modpc(
 Module  s_mod,
 PrCount s_pc
)
s_mod <  s_pc
(exists  Local s_CL, Global s_CG, Local s_ENTRY_CL, Global s_ENTRY_CG.
     Frontier(s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG)        // s is on frontier
);


mu bool Reachable(
 Module  s_mod,
 PrCount s_pc,
 Local   s_CL,
 Global  s_CG,
 Local   s_ENTRY_CL,
 Global  s_ENTRY_CG
)
s_mod <  s_pc,
s_pc  <  s_CL,
s_CL  ~+ s_ENTRY_CL,
s_CL  <  s_CG,
s_CG  ~+ s_ENTRY_CG 
(

  (Winning(1,s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG) & Frontier_modpc(s_mod,s_pc) )

|(enforce(s_mod, s_CL, s_CG) &
( 

  (s_mod=0 & s_pc=0 & !Winning(0,s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG))


  // forward propagation on internal transitions on current set (not just the frontier from prev round)
  | (exists PrCount t_pc, Local t_CL, Global t_CG.
          (  
               Reachable(s_mod,t_pc,t_CL,t_CG,s_ENTRY_CL,s_ENTRY_CG)
               &  (  (programInt1(s_mod,t_pc,s_pc,t_CL,s_CL,t_CG,s_CG)
                      & CopyVariables_ProgramInt(s_mod,t_pc,t_CL,s_CL,t_CG,s_CG)
                     )
                     | programInt3(s_mod,t_pc,s_pc,t_CL,s_CL,t_CG,s_CG)
                  )
     )    )


  // forward propagation on internal transitions on current set (not just the frontier from prev round)
  | (
       (exists PrCount t_pc.
          (  
                  (Reachable(s_mod,t_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG)// & !Calling(s_mod,t_pc)
)
               & programInt2(s_mod,t_pc,s_pc,s_CL,s_CG)
    )  )  )


  // forward propagation on call transitions
  | (      s_pc=0 
           & CopyLocals(s_mod,s_ENTRY_CL,s_CL)
           & (exists Module t_mod, PrCount t_pc, Local t_CL, Global t_CG, Local t_ENTRY_CL, Global t_ENTRY_CG.
                   (   Reachable(t_mod,t_pc,t_CL,t_CG,t_ENTRY_CL,t_ENTRY_CG) 
                       & (programCall(t_mod,s_mod,t_pc,t_CL,s_CL,t_CG)
                       & CopyGlobals(s_mod,t_CG,s_CG) 
                       & CopyGlobals(s_mod,t_CG,s_ENTRY_CG))
   )         )     )


))

);

/******************************************************************************************************/
//                                    Reachability check                                              *
/******************************************************************************************************/

(  exists Module  s_mod, PrCount s_pc, Local s_CL, Global s_CG, Local s_ENTRY_CL, Global  s_ENTRY_CG.
        ( Winning(0,s_mod,s_pc,s_CL,s_CG,s_ENTRY_CL,s_ENTRY_CG) & target(s_mod,s_pc) )
);
