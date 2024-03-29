require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL Parameters.
require import Montgomery_arith.

require import EcAdd_correctness_cases EcAdd_safety_cases EcAdd_spec.


     
(* if input is valid then we terminate and result agrees with functional specification   *)
lemma ecAdd_correctness &m (x1_in y1_in x2_in y2_in : int) : 
        0 <= x1_in  /\ 0 <= y1_in  /\ 0 <= x2_in  /\ 0 <= y2_in =>    
        valid_ecAdd_input x1_in y1_in x2_in y2_in =>
        Pr[ AlmostYul.main(x1_in, y1_in, x2_in, y2_in)@&m : Some res = ecAdd x1_in y1_in x2_in y2_in ] = 1%r.
proof.
progress.
case (pointIsInfinity x1_in y1_in).
case (pointIsInfinity x2_in y2_in).
progress.
byphoare (_: arg = (x1_in,y1_in,x2_in,y2_in) ==> _);auto. conseq (ecAdd_correct_1 x1_in y1_in x2_in y2_in).
progress;smt(). smt().
progress.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   Some res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_2 x1_in y1_in x2_in y2_in). 
 progress;smt(). smt(). smt(). smt(). 
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
case (pointIsInfinity x2_in y2_in).
progress.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   Some res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_3 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt(). auto. auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
progress.
case (x1_in = x2_in /\ (P - y1_in) %% P = y2_in).
move => ass.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   Some res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_4 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt(). smt(). auto. auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
progress.
case (x1_in = x2_in /\ y1_in = y2_in).
move => ass2.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   Some res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_5 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt().  
  progress. smt(). auto.  auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
progress.
 have : Pr[AlmostYul.main(x1_in, y1_in, x2_in, y2_in) @ &m :
   Some res = ecAdd x1_in y1_in x2_in y2_in] >= Pr[ AlmostYul.skipf()@&m : true ].
 byequiv (_: arg{2} = (x1_in,y1_in,x2_in,y2_in) ==> _). symmetry.
 conseq (ecAdd_correct_6 x1_in y1_in x2_in y2_in). 
 progress. smt(). smt(). smt(). smt(). smt(). smt(). progress. smt().  
  progress. smt(). auto.  auto.
 have ->: Pr[AlmostYul.skipf() @ &m : true] = 1%r. byphoare. proc. auto. auto. auto.
 smt(@Distr).
qed.



(* if input is invalid then ecAdd diverges *)
lemma ecAdd_safety &m (x1_in y1_in x2_in y2_in : int) :
         0 <= x1_in  /\ 0 <= y1_in  /\ 0 <= x2_in  /\ 0 <= y2_in =>    
         !valid_ecAdd_input x1_in y1_in x2_in y2_in =>
         Pr[ AlmostYul.main(x1_in, y1_in, x2_in, y2_in)@&m : true ] = 0%r.
progress.
pose disj1 := !(x1_in < P /\
   y1_in < P /\ x2_in < P /\ y2_in < P).
pose disj2 := ((!pointIsInfinity x1_in y1_in /\ !pointIsInCurve x1_in y1_in)
         \/ (!pointIsInfinity x2_in y2_in /\ !pointIsInCurve x2_in y2_in)).                
have : disj1 \/ disj2. smt().
case (disj1).      progress.     
byphoare (_: arg = (x1_in, y1_in, x2_in, y2_in) ==> _).         
conseq (ecAdd_safety_2 x1_in y1_in x2_in y2_in). progress. smt(). auto.
progress. byphoare (_: arg = (x1_in, y1_in, x2_in, y2_in) ==> _).     
conseq (ecAdd_safety_1 x1_in y1_in x2_in y2_in _). progress;smt(). smt(). auto. auto.
qed.     
