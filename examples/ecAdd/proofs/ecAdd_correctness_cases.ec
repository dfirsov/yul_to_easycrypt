require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.
require import Montgomery_arith.
require import EcAdd_spec Parameters.
require import ExtraFacts.


lemma ecAdd_correct_1 x1_in y1_in x2_in y2_in :  
 phoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in)  
         /\ (x1_in = 0 /\ y1_in = 0) 
         /\ (x2_in = 0 /\ y2_in = 0)
                 ==> res = (0,0) ] = 1%r.
proc. 
rcondt 5. inline*. wp. skip. progress. 
rcondf 7. inline*. wp. skip. progress.
inline*. wp. auto. 
qed.


lemma ecAdd_correct_2 x1_in y1_in x2_in y2_in :  
 equiv [ AlmostYul.main ~ AlmostYul.skipf : 
         (arg = (x1_in,y1_in,x2_in,y2_in)  
         /\ 0 <= x2_in < P 
         /\ 0 <= y2_in < P
         /\ pointIsInCurve x2_in y2_in
      
         /\ (x1_in = 0 /\ y1_in = 0) 
         /\ !(x2_in = 0 /\ y2_in = 0)){1}      
                  ==> res{1} = (x2_in,y2_in) ].
proc. 
rcondf {1} 5. progress. inline*. wp. skip. progress. 
rcondt {1} 5. progress. inline*. wp. skip. progress.
rcondf {1} 8. progress. inline*. auto. sp. if. wp. sp.  auto. skip. smt().
rcondt {1} 7. progress. inline*. wp. skip. progress.
rcondf {1} 12. progress. inline*. wp. skip. progress.           smt().
seq  13 0 : (#pre /\ m_x2 = x2_in * R %% P  /\ m_y2 = y2_in * R %% P){1}. auto.
ecall {1} (into_m y2{1}).
ecall {1} (into_m x2{1}).
inline*. wp. skip. progress. 
wp.
rcondf {1} 3. progress. 
inline AlmostYul.iszero. wp.
ecall (pointIsInCurve_m_h x2 y2). skip. progress. rewrite /as_bool. simplify.
rewrite /pointIsInCurve in H4.
 have ->: y2{hr} * y2{hr} * R %% P = y2{hr} * y2{hr} %% P * R %% P.
  smt (@Int @IntDiv).                
  rewrite H3. smt(@IntDiv).
call {1} (_:true ==> true). proc. auto.
call {1} (_:true ==> true). proc. inline*. auto. skip. progress.
qed.           



lemma ecAdd_correct_3 x1_in y1_in x2_in y2_in :  
 equiv[ AlmostYul.main ~ AlmostYul.skipf :
         arg{1} = (x1_in,y1_in,x2_in,y2_in) 
         /\ (0 <= x1_in < P){1}
         /\ (0 <= y1_in < P){1}
         /\ (pointIsInCurve x1_in y1_in){1}

         /\ !(x1_in = 0 /\ y1_in = 0){1}
         /\ (x2_in = 0 /\ y2_in = 0){1}       
               ==> res{1} = (x1_in,y1_in){1} ].
proc. 
rcondf {1} 5. progress. inline*. wp. skip. progress. 
rcondt {1} 5. progress. inline*. wp. skip. progress. 
rcondf {1} 7. progress. inline*. auto.
rcondt {1} 7. progress. inline*. wp. skip. progress.
rcondt {1} 9.  progress. inline*. wp. skip. progress.       
rcondf {1} 22.  progress. wp.  auto.
rcondf {1} 14. progress. inline*. wp. skip. progress.        smt().
seq {1} 15 0 : (#pre /\ m_x1 = x1_in * R %% P  /\ m_y1 = y1_in * R %% P){1}. auto.
ecall {1} (into_m y1{1}).
ecall {1} (into_m x1{1}).
inline*. auto.
wp.
rcondf {1} 3. progress.      
inline AlmostYul.iszero. wp.
ecall (pointIsInCurve_m_h x1 y1). skip. progress. rewrite /as_bool. simplify.
rewrite /pointIsInCurve in H4.
have ->: y1{hr} * y1{hr} * R %% P
  = y1{hr} * y1{hr} %% P * R %% P. smt(@IntDiv).
rewrite H3. smt(@IntDiv).
call {1} (_:true ==> true). proc. auto.
call {1} (_:true ==> true). proc. inline*. auto.
skip. auto.  
qed.       

lemma ecAdd_correct_4 x1_in y1_in x2_in y2_in :  
 equiv [ AlmostYul.main ~ AlmostYul.skipf : 
         (arg = (x1_in,y1_in,x2_in,y2_in) 
         /\ 0 <= x1_in < P 
         /\ 0 <= y1_in < P
         /\ 0 <= x2_in < P 
         /\ 0 <= y2_in < P      
         /\ pointIsInCurve x1_in y1_in
         /\ pointIsInCurve x2_in y2_in

         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ !(x2_in = 0 /\ y2_in = 0)       
         /\ x1_in = x2_in /\ (P - y1_in) %% P = y2){1}
               ==> res{1} = (0,0) ].
proc.             
rcondf {1} 5. progress. inline*. wp. skip. progress.  smt().
rcondt {1} 5. progress. inline*. wp. skip. progress. 
rcondf {1} 7. progress. inline*. auto. smt().
rcondt {1} 7. progress. inline*. wp. skip. progress.
rcondf {1} 9. progress. inline*. wp. skip. progress. smt().
rcondt {1} 9. progress. inline*. auto. 
rcondf {1} 14. progress. inline*. auto. smt().
rcondf {1} 19. progress. inline*. auto. smt().
rcondt {1} 24. progress. inline*. auto. progress. rewrite /as_bool. smt.
rcondf {1} 36. progress. wp. auto.
wp.
seq 27 0 : (#pre /\ m_x1 = x1_in * R %% P  
               /\ m_y1 = y1_in * R %% P 
               /\ m_x2 = x2_in * R %% P  
               /\ m_y2 = y2_in * R %% P){1}. auto.
ecall {1} (into_m y2{1}).
ecall {1} (into_m x2{1}).
ecall {1} (into_m y1{1}).
ecall {1} (into_m x1{1}).
inline*. auto. progress.
rcondf {1} 6. progress.
inline 5. inline 2. inline 5. wp.
ecall (pointIsInCurve_m_h  x2_in y2_in).
wp.
ecall (pointIsInCurve_m_h  x1_in y1_in).
skip. progress. rewrite /as_bool.
have ->: y1{hr} * y1{hr} * R %% P = (x2{hr} * x2{hr} * x2{hr} * R + 3 * R) %% P.
have ->: y1{hr} * y1{hr} * R %% P = y1{hr} * y1{hr} %% P * R %% P.
smt(@Int @IntDiv).             
rewrite  H7.  smt(@Int @IntDiv). simplify.
have ->: (x2{hr} * x2{hr} * x2{hr} * R + 3 * R) %% P
 = (x2{hr} * x2{hr} * x2{hr}  + 3 ) * R %% P.
smt(@Int @IntDiv).
have ->: (x2{hr} * x2{hr} * x2{hr}  + 3 ) * R %% P
 = (x2{hr} * x2{hr} * x2{hr}  + 3) %% P * R %% P.
smt(@Int @IntDiv).
rewrite - H8. smt(@Int @IntDiv).
inline*. auto. 
qed.


lemma ecAdd_correct_5 x1_in y1_in x2_in y2_in :  
 equiv [ AlmostYul.main ~ AlmostYul.skipf  : 
         (arg = (x1_in,y1_in,x2_in,y2_in) 
         /\ 0 <= x1_in < P 
         /\ 0 <= y1_in < P (* to be disjoint from  *)
         /\ 0 <= x2_in < P 
         /\ 0 <= y2_in < P      
         /\ pointIsInCurve x1_in y1_in
         /\ pointIsInCurve x2_in y2_in
         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ !(x2_in = 0 /\ y2_in = 0)       
         /\ (x1_in = x2_in /\ y1_in = y2_in)){1}
         /\ !(x1_in = x2_in /\ (P - y1_in) %% P = y2){1}
               ==> res{1} = ((add_x x1_in y1_in){1} %% P, (add_y x1_in y1_in){1} %% P) ].
proc.             
rcondf {1} 5. progress. inline*. wp. skip. progress. smt().
rcondt  {1} 5. progress. inline*. wp. skip. progress. 
rcondf  {1} 7. progress. inline*. auto. smt().
rcondt {1} 7. progress. inline*. wp. skip. progress.
rcondf {1} 9. progress. inline*. wp. skip. progress. smt().
rcondt {1} 9. progress. inline*. auto. 
rcondf {1} 14. progress. inline*. auto. smt().
rcondf {1} 19. progress. inline*. auto. smt().
rcondf {1} 24. progress. inline*. auto. progress. rewrite /as_bool.
 have f: (P - y2{hr}) %% R = (P - y2{hr}). smt.
 rewrite f f. 
 have ->: (P - y2{hr}) %% P = (P - y2{hr}). smt.
 case (P - y2{hr} <> y2{hr});auto.
  move => j.
  have : !odd P. apply (even_fact P y2{hr}). auto.
  smt.             
rcondt {1} 24. progress. inline*. auto. progress. rewrite /as_bool.
rcondf {1} 33. progress. inline*. auto. 
rcondt {1} 36. progress. inline*. auto. progress. rewrite /as_bool.
rcondf {1} 63. progress. wp. auto.
seq 35 0 : (#pre). inline*. auto.    
seq 2 0 : (#pre /\ x = x1_in * R %% P  /\ y = y1_in * R %% P){1}. auto.
ecall {1} (into_m y1{1}).
ecall {1} (into_m x1{1}). 
skip. progress. 
rcondf {1} 3. progress.  inline 2. wp.             
ecall  (pointIsInCurve_m_h x1_in y1_in).
skip. progress.  rewrite /as_bool. simplify.
have ->: y2{hr} * y2{hr} * R %% P
  = y2{hr} * y2{hr} %% P * R %% P. smt(@IntDiv).
rewrite H8. smt(@Int @IntDiv).
pose x1_squared_raw := x1_in * x1_in.              
seq 3 0 : (#pre /\ x1_squared = x1_squared_raw * R %% P){1}. auto.
ecall {1} (mul_m x1_in x1_in). call {1} (_:true ==> true). proc. auto. call {1} (_:true ==> true). proc. inline*. auto. skip. 
smt.  inline {1} 1. sp.
seq 1 0 : (#pre /\ func372 = (x1_squared + x1_squared) %% P){1}. inline*. wp. skip. progress. smt.
seq 2 0 : (#pre /\ func368 = (x1_squared + (x1_squared + x1_squared)) %% P){1}. inline*. wp. skip. progress.
pose x:= x2{1} * x2{1} * R %% P.
     have ->: (x + (x + x) %% P) %% R = (x + (x + x) %% P). smt.
             smt(@Int @IntDiv).
seq 2 0 : (#pre /\ func382 = (y1_in + y1_in) * R %% P){1}. inline*. wp.  progress. skip. progress.
have ->: (y2{1} * R %% P + y2{1} * R %% P) %% R  = (y2{1} * R %% P + y2{1} * R %% P) . smt.
smt(@Int @IntDiv).    
pose slope_raw := (3 * x1_squared_raw) * (inv  (y1_in + y1_in)).             
seq 1 0 : (#pre /\ slope = slope_raw * R %% P){1}.
ecall {1} (div_m (3 * x1_in * x1_in) (y1_in + y1_in)).
skip. progress.
have ->: (x1_squared_raw * R %% P +
 (x1_squared_raw * R %% P + x1_squared_raw * R %% P)) %% P
  = (x1_squared_raw * R %% P +
 (x1_squared_raw * R %% P + x1_squared_raw * R %% P) %% P) %% P. smt(@Int @IntDiv).
have ->: (x1_squared_raw * R %% P + x1_squared_raw * R %% P) %% P
 = (x1_squared_raw * R + x1_squared_raw * R ) %% P. smt(@Int @IntDiv).
 have ->: (x1_squared_raw * R %% P + (x1_squared_raw * R + x1_squared_raw * R) %% P) %%
P = (x1_squared_raw * R + (x1_squared_raw * R + x1_squared_raw * R)) %%
P. smt(@Int @IntDiv). smt(@Int).
smt. smt.
have ->: (y2{1} + y2{1}) = 2 * y2{1}. smt().
 have : 2 * y2{1} * R %% P <> 0. 
 (* smt(@IntDiv @Int). *)
 rewrite - dvdzE. 
 case (P %| 2 * y2{1} * R). move => q.
  have qq : P %| 2 * y2{1} \/ P %| R.
  apply Euclide. auto. smt.
  elim qq. move => zz.
  have ww : P %| 2 \/ P %| y2{1}.
  apply Euclide. auto. smt.
  elim ww. progress. apply div_fact. smt.
  progress. apply div_fact. smt.
  progress. apply div_fact2. smt. smt. auto.
smt. 
smt.
smt. 
seq 1 0 : (#pre /\ func392 = (slope_raw * slope_raw) * R %% P){1}.
ecall {1} (mul_m slope_raw slope_raw). skip. progress. smt. smt. smt. smt.             
seq 2 0 : (#pre /\ func398 = (x1_in + x1_in) * R %% P){1}. inline*. wp. skip. progress.
have ->: (x2{1} + x2{1}) * R = (x2{1} * R + x2{1} * R). smt. 
have ->: (x2{1} * R %% P + x2{1} * R %% P) %% R 
  = (x2{1} * R %% P + x2{1} * R %% P). smt.
  smt(@Int @IntDiv).
  pose x3_raw := ((slope_raw * slope_raw) - (x1_in + x1_in)).
seq 2 0 : (#pre /\ x3 = x3_raw * R %% P){1}.                 
ecall {1} (submod (slope_raw * slope_raw * R %% P) ((x1_in + x1_in) * R %% P) P). inline*.  wp. skip. progress.
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv). smt. smt(@Int @IntDiv). smt(@Int @IntDiv).  
have ->: (slope_raw * slope_raw - (x2{1} + x2{1})) * R
              = (slope_raw * slope_raw * R - (x2{1} + x2{1}) * R).
                 smt(@Int @IntDiv).
rewrite - qqq.  auto.
seq 2 0 : (#pre /\ func414 = (x1_in - x3_raw) * R %% P){1}.
ecall {1} (submod x{1} x3{1} P). inline*. wp. skip. progress.
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv). smt. smt(@Int @IntDiv). smt(@Int @IntDiv).              
smt(@Int @IntDiv). 
seq 1 0 : (#pre /\ func410 = slope_raw * (x1_in - x3_raw) * R %% P){1}.
ecall {1} (mul_m slope_raw (x1_in - x3_raw)). skip. progress. smt(@Int @IntDiv).
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv).              
seq 2 0 : (#pre /\ y3{1} = (slope_raw * (x1_in - x3_raw) -  (y1_in)) * R %% P).
ecall {1} (submod func410{1} y{1} P). inline*. wp. skip. progress.
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv).
smt. smt(@Int @IntDiv). smt(@Int @IntDiv). 
rewrite - qqq. smt(@Int).
wp.
ecall {1} (outof_m y3{1}).
ecall {1} (outof_m x3{1}).
skip. progress.
smt(@Int @IntDiv).
smt(@Int @IntDiv).                            
smt(@Int @IntDiv).
smt(@Int @IntDiv).
have ->: x3_raw * R %% P * inv R %% P = x3_raw %% P.
  have ->: x3_raw * R %% P * inv R %% P
    = x3_raw * R %% P * (inv R %% P) %% P. smt(@Int @IntDiv).
   have ->: x3_raw * R %% P * (inv R %% P) %% P = (x3_raw * R  * (inv R)) %% P.
   smt(@Int @IntDiv).
   have ->: (x3_raw * R  * (inv R)) = (x3_raw * (R  * (inv R))). smt().
   have ->: x3_raw * (R * inv R) %% P = x3_raw  * ((R * inv R) %% P )  %% P. smt(@Int @IntDiv).
   rewrite inv_ax_opp. smt. auto.
    rewrite /add_x. simplify.
rewrite /x3_raw.
rewrite /slope_raw.
rewrite /x1_squared_raw.
have ->: (x2{1} * x2{1}) = x2{1} ^ 2. smt.
congr. congr. smt.
have ->: (slope_raw * (x2{1} - x3_raw) - y2{1}) * R %% P * inv R %% P
              = (slope_raw * (x2{1} - x3_raw) - y2{1}) %% P.
have ->: (slope_raw * (x2{1} - x3_raw) - y2{1}) * R %% P * inv R %% P
 = ((slope_raw * (x2{1} - x3_raw) - y2{1}) * (inv R * R)) %% P. smt(@Int @IntDiv).
have ->: ((slope_raw * (x2{1} - x3_raw) - y2{1}) * (inv R * R)) %% P
  = ((slope_raw * (x2{1} - x3_raw) - y2{1}) * ((inv R * R) %% P)) %% P. smt(@Int @IntDiv).
rewrite inv_ax.  simplify. smt. simplify. auto.              
congr. congr.
rewrite /add_y /add_x. simplify.
rewrite /slope_raw.
rewrite /x1_squared_raw.
rewrite /x3_raw.
rewrite /slope_raw.
rewrite /x1_squared_raw.
have ->: (x2{1} * x2{1}) = x2{1} ^ 2. smt.
congr.
have ->: (3 * x2{1} ^ 2 * inv (y2{1} + y2{1}) *
  (3 * x2{1} ^ 2 * inv (y2{1} + y2{1})) = (3 * x2{1} ^ 2 * inv (2 * y2{1})) ^ 2). smt.
smt.
qed.


lemma ecAdd_correct_6 x1_in y1_in x2_in y2_in :  
 equiv[ AlmostYul.main ~ AlmostYul.skipf : 
         (arg = (x1_in,y1_in,x2_in,y2_in)
         /\ 0 <= x1_in < P 
         /\ 0 <= y1_in < P 
         /\ 0 <= x2_in < P 
         /\ 0 <= y2_in < P      
         /\ pointIsInCurve x1_in y1_in
         /\ pointIsInCurve x2_in y2_in

         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ !(x2_in = 0 /\ y2_in = 0) 
         /\ !(x1_in = x2_in /\ y1_in = y2_in)
         /\ !(x1_in = x2_in /\ (P - y1_in) %% P = y2)){1}
               ==> (res = (add_x' x1_in x2_in y1_in y2_in %% P, add_y' x1_in x2_in y1_in y2_in %% P)){1} ].
proc.             
rcondf {1} 5. progress. inline*. wp. skip. progress. smt().
rcondt {1} 5. progress. inline*. wp. skip. progress. 
rcondf {1} 7. progress. inline*. auto. smt().
rcondt {1} 7. progress. inline*. wp. skip. progress.
rcondf {1} 9. progress. inline*. wp. skip. progress. smt().
rcondt {1} 9. progress. inline*. auto. 
rcondf {1} 14. progress. inline*. auto. smt().
rcondf {1} 19. progress. inline*. auto. smt().
rcondf {1} 24. progress. inline*. auto. progress. rewrite /as_bool.
 have f: (P - y1{hr}) %% R = (P - y1{hr}). smt.
 rewrite f f. clear f.             
case (x1{hr} = x2{hr}). progress.
smt. auto.
seq 23 0 : (#pre /\ ret_bool = false){1}. inline*. wp. auto.            
rcondt {1} 1. progress. auto.
rcondf {1} 10. progress.
inline 9. inline 8. inline 7. wp. inline 6.
inline 4. inline 1. inline 4. inline 7. sp. wp.
ecall (submod_h 0 y2_in P). skip. progress. smt. smt. smt. smt.
rewrite /as_bool.
have ->: (-y2{hr}) %% P = (P - y2{hr}) %%P. smt(@Int @IntDiv).
case (x1{hr} = x2{hr}). move => x_eq. simplify.
have : y1{hr} %% P = (P - y2{hr}) %% P. 
apply oi. smt. smt. smt(). smt().
have ->: (y1{hr} ^ 2  = y1{hr} *  y1{hr} ). smt.
have ->: (y2{hr} ^ 2  = y2{hr} *  y2{hr} ). smt.
rewrite H7 H8. smt().
smt().             
simplify. auto.                                    
rcondf {1} 13. progress. inline*. auto.  progress. rewrite /as_bool.
seq 12 0 : (#pre){1}. inline*. wp. auto.
rcondt {1} 1. progress. auto.                        
seq 4 0 : ((
   (0 <= x1_in && x1_in < P) /\
   (0 <= y1_in && y1_in < P) /\
   (0 <= x2_in && x2_in < P) /\
   (0 <= y2_in && y2_in < P) /\
   pointIsInCurve x1_in y1_in /\
   pointIsInCurve x2_in y2_in /\
   ! (x1_in = 0 /\ y1_in = 0) /\
   ! (x2_in = 0 /\ y2_in = 0) /\
   ! (x1_in = x2_in /\ y1_in = y2_in) /\ ! (x1_in = x2_in /\ (P - y1_in) %% P = y2_in)) /\
  ret_bool = false /\ x1 = x1_in * R %% P
  /\ y1 = y1_in * R %% P
 /\ x2 = x2_in * R %% P
/\ y2 = y2_in * R %% P){1}.
ecall {1} (into_m y2_in). 
ecall {1} (into_m x2_in).
ecall {1} (into_m y1_in).                          
ecall {1} (into_m x1_in).
skip. progress.
rcondf {1} 6. progress. inline 5. inline 4. inline 2. wp.
ecall (pointIsInCurve_m_h x2_in y2_in).
wp. ecall (pointIsInCurve_m_h x1_in y1_in).
skip. progress. rewrite /as_bool.
have f1: y1_in * y1_in * R %% P = (x1_in * x1_in * x1_in * R + 3 * R) %% P.
  have ->: y1_in * y1_in * R %% P = y1_in * y1_in %%P * R %% P. smt(@Int @IntDiv).
  rewrite H7.  smt(@Int @IntDiv).
have f2 : y2_in * y2_in * R %% P = (x2_in * x2_in * x2_in * R + 3 * R) %% P.
  have ->: y2_in * y2_in * R %% P = y2_in * y2_in %% P * R %% P. smt(@Int @IntDiv).
  rewrite H8. smt(@Int @IntDiv).
smt().
seq 5 0 : (#pre){1}.
call {1} (_:true ==> true). proc. auto.
call {1} (_:true ==> true). proc. auto.
call {1} (_:true ==> true). proc. inline*. auto.
call {1} (_:true ==> true). proc. inline*. auto.
call {1} (_:true ==> true). proc. inline*. auto.
skip. progress.
seq 2 0 : (#pre /\ func492 = (y2_in - y1_in) * R %% P){1}.
ecall {1} (submod y2{1} y1{1} P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite  - qqq. smt (@Int @IntDiv).
seq 2 0 : (#pre /\ func500 = (x2_in - x1_in) * R %% P){1}.
ecall {1} (submod x2{1} x1{1} P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite  - qqq. smt (@Int @IntDiv).
pose slope_raw := (y2_in - y1_in) * (inv (x2_in - x1_in)).
seq 1 0 : (#pre /\ slope = slope_raw * R %% P){1}.
ecall {1} (div_m (y2_in - y1_in) (x2_in - x1_in)). skip. progress. smt. smt.
case (x2_in <> x1_in). progress.
have : (x2_in - x1_in) %% P <> 0. smt.
progress.
have : (x2_in - x1_in) * R %% P <> 0.
 rewrite - dvdzE.
 case (P %| (x2_in - x1_in) * R).
move => q.
  have qq : P %| (x2_in - x1_in) \/ P %| R.
  apply Euclide. auto. smt.
elim qq. smt. apply div_fact2. smt. smt.
smt.
smt.
simplify.
move => eqq.
have : y2_in %%P = (P - y1_in) %%P.
apply (oi y2_in y1_in). smt. smt. smt. smt.
have ->: y2_in ^ 2 = y2_in * y2_in. smt.
have ->: y1_in ^ 2 = y1_in * y1_in. smt.
rewrite H7 H8. smt().
smt().
smt.
seq 1 0 : (#pre /\ func510 = (slope_raw * slope_raw) * R %% P){1}.
ecall {1} (mul_m slope_raw slope_raw). skip. progress. smt. smt. smt. smt.
seq 2 0 : (#pre /\ func516 = (x1_in + x2_in) * R %% P){1}.
ecall {1} (addmod x1{1} x2{1} P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt. smt(@Int @IntDiv).
seq 2 0 : (#pre /\ x3 = (slope_raw * slope_raw - (x1_in + x2_in)) * R %% P){1}.
ecall {1} (submod func510{1} func516{1} P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite - qqq. auto. smt(@Int).
seq 2 0 : (#pre /\ func532 = (x1_in - (slope_raw * slope_raw - (x1_in + x2_in))) * R %% P){1}.
ecall {1} (submod x1{1} x3{1} P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite - qqq. smt(@Int).
pose func532_raw := (x1_in - (slope_raw * slope_raw - (x1_in + x2_in))).
seq 1 0 : (#pre /\ func528 = slope_raw * func532_raw * R %% P){1}.
ecall {1} (mul_m slope_raw{1} func532_raw{1}). skip. progress. smt. smt. smt. smt.
seq 2 0 : (#pre /\ y3 = ((slope_raw * func532_raw) - y1_in) * R %% P){1}.
ecall {1} (submod func528{1} y1{1} P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite - qqq. smt(@Int).
wp.
ecall {1} (outof_m y3{1}).
ecall {1} (outof_m x3{1}).
skip. progress. smt. smt. smt. smt.
have ->: (slope_raw * slope_raw - (x1_in + x2_in)) * R %% P * inv R %% P
 = (slope_raw * slope_raw - (x1_in + x2_in)) %% P.
have ->: (slope_raw * slope_raw - (x1_in + x2_in)) * R %% P * inv R %% P
 = (slope_raw * slope_raw - (x1_in + x2_in)) * R * inv R %% P.
smt(@Int @IntDiv).
have ->:  (slope_raw * slope_raw - (x1_in + x2_in)) * R * inv R %% P
  = (slope_raw * slope_raw - (x1_in + x2_in)) * (R * inv R) %% P. smt().
have ->:   (slope_raw * slope_raw - (x1_in + x2_in)) * (R * inv R) %% P
  = (slope_raw * slope_raw - (x1_in + x2_in)) * ((R * inv R) %% P) %% P.
smt(@Int @IntDiv). rewrite inv_ax_opp.   smt. simplify. auto.
smt.
have ->: (slope_raw * func532_raw - y1_in) * R %% P * inv R %% P
 = (slope_raw * func532_raw - y1_in) * (R * inv R) %% P.
smt(@Int @IntDiv).
have ->: (slope_raw * func532_raw - y1_in) * (R * inv R) %% P =
 (slope_raw * func532_raw - y1_in) * (R * inv R %%P) %% P.
smt(@Int @IntDiv).
rewrite inv_ax_opp. smt. simplify.
 smt.
qed.
