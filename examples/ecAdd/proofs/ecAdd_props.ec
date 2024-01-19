require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.
require import Montgomery_arith.

require import EcAdd_correctness_cases EcAdd_safety_cases EcAdd_spec.

op valid_ecAdd_input (x1 y1 x2 y2) = 
            x1 < P
         /\ y1 < P
         /\ x2 < P
         /\ y2 < P
         /\ (!pIsInfinity (x1, y1) => pointIsInCurve x1 y1)
         /\ (!pIsInfinity (x2, y2) => pointIsInCurve x2 y2).

(* if input is invalid then ecAdd diverges *)
lemma ecAdd_safety &m (x1_in y1_in x2_in y2_in : int) :
         0 <= x1_in  /\ 0 <= y1_in  /\ 0 <= x2_in  /\ 0 <= y2_in =>
    
         !valid_ecAdd_input x1_in y1_in x2_in y2_in =>
         Pr[ AlmostYul.main(x1_in, y1_in, x2_in, y2_in)@&m : true ] = 0%r.
progress.
pose disj1 := !(x1_in < AlmostYUL.N /\
   y1_in < AlmostYUL.N /\ x2_in < AlmostYUL.N /\ y2_in < AlmostYUL.N).
pose disj2 := ((!pIsInfinity (x1_in, y1_in) /\ !pointIsInCurve x1_in y1_in)
         \/ (!pIsInfinity (x2_in, y2_in) /\ !pointIsInCurve x2_in y2_in)).                
have : disj1 \/ disj2. smt().
case (disj1).      progress.     
byphoare (_: arg = (x1_in, y1_in, x2_in, y2_in) ==> _).         
conseq (ecAdd_safety_2 x1_in y1_in x2_in y2_in). progress. smt(). auto.
progress. byphoare (_: arg = (x1_in, y1_in, x2_in, y2_in) ==> _).     
conseq (ecAdd_safety_1 x1_in y1_in x2_in y2_in _). progress;smt(). smt(). auto. auto.
qed.     
     
(* if input is valid then we terminate and result agrees with functional specification   *)
lemma ecAdd_correctness &m (x1_in y1_in x2_in y2_in : int) : 
        0 <= x1_in  /\ 0 <= y1_in  /\ 0 <= x2_in  /\ 0 <= y2_in =>
    
        valid_ecAdd_input x1_in y1_in x2_in y2_in =>
        Pr[ AlmostYul.main(x1_in, y1_in, x2_in, y2_in)@&m : res = ecAdd x1_in y1_in x2_in y2_in ] = 1%r.
proof.
progress.
case (pIsInfinity (x1_in, y1_in)).
case (pIsInfinity (x2_in, y2_in)).
progress.
byphoare (_: arg = (x1_in,y1_in,x2_in,y2_in) ==> _). conseq (ecAdd_correct_1 x1_in y1_in x2_in y2_in).
progress. smt(). smt(). smt(). smt(). smt(). auto. auto.
progress.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_2 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt(). auto. auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
case (pIsInfinity (x2_in, y2_in)).
progress.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_3 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt(). auto. auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
progress.
case (x1_in = x2_in /\ (P - y1_in) %% P = y2_in).
move => ass.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_4 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt(). smt(). auto. auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
progress.
case (x1_in = x2_in /\ y1_in = y2_in).
move => ass2.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_5 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt().  
  progress. smt(). auto.  auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
progress.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_6 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt().  
  progress. smt(). auto.  auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
qed.
