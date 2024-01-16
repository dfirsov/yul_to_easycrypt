require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.
require import Montgomery_arith.


op pointIsInCurve (x y : int) = (y * y) %% P = (x * x * x + 3) %% P.


lemma pointIsInCurve_m_h (x_in y_in : int) :
 hoare [ AlmostYul.pointIsInCurve : arg = (x_in * R %% P, y_in * R %% P) ==>  
       res = (y_in * y_in * R %% P = (x_in * x_in * x_in * R + 3 * R) %% P ) ].
admitted.



lemma ecAdd_correct_1 x1_in y1_in x2_in y2_in :  
 phoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in)  /\
         ((x1_in = 0 /\ y1_in = 0) /\ (x2_in = 0 /\ y2_in = 0))
             ==> res = (0,0) ] = 1%r.
proc. 
rcondt 5. inline*. wp. skip. progress. 
rcondf 7. inline*. wp. skip. progress.
inline*. wp. auto. qed.


lemma ecAdd_correct_2 x1_in y1_in x2_in y2_in :  
 hoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in)  
         /\ (x1_in = 0 /\ y1_in = 0) 
         /\ !(x2_in = 0 /\ y2_in = 0)
         /\ 0 <= x2_in < AlmostYUL.N 
         /\ 0 <= y2_in < AlmostYUL.N
         /\ pointIsInCurve x2_in y2_in  
                  ==> res = (x2_in,y2_in) ].
proc. 
rcondf 5. inline*. wp. skip. progress. 
rcondt 5. inline*. wp. skip. progress.
rcondf 8. inline*. auto. sp. if. wp. sp.  auto. skip. smt().
rcondt 7. inline*. wp. skip. progress.
rcondf 12. inline*. wp. skip. progress.           smt().
seq 13 : (#pre /\ m_x2 = x2_in * R %% P  /\ m_y2 = y2_in * R %% P). auto.
ecall (into_m_h y2).
ecall (into_m_h x2).
inline*. auto.           
wp.
rcondf 3. 
inline AlmostYul.iszero. wp.
ecall (pointIsInCurve_m_h x2 y2). skip. progress. rewrite /as_bool. simplify.
rewrite /pointIsInCurve in H4.
 have ->: y2{hr} * y2{hr} * R %% P = y2{hr} * y2{hr} %% P * R %% P.
  smt (@Int @IntDiv).                
  rewrite H4. smt(@IntDiv).
call (_:true);auto.
call (_:true);auto.             
qed.           


lemma ecAdd_correct_3 x1_in y1_in x2_in y2_in :  
 hoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in) 
         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ (x2_in = 0 /\ y2_in = 0) 
         /\ 0 <= x1_in < AlmostYUL.N 
         /\ 0 <= y1_in < AlmostYUL.N
         /\ pointIsInCurve x1_in y1_in 
               ==> res = (x1_in,y1_in) ].
proc. 
rcondf 5. inline*. wp. skip. progress. 
rcondt 5. inline*. wp. skip. progress. 
rcondf 7. inline*. auto.
rcondt 7. inline*. wp. skip. progress.
rcondt 9. inline*. wp. skip. progress.       
rcondf 22.  wp.  auto.
rcondf 14. inline*. wp. skip. progress.        smt().
seq 15 : (#pre /\ m_x1 = x1_in * R %% P  /\ m_y1 = y1_in * R %% P). auto.
ecall (into_m_h y1).
ecall (into_m_h x1).
inline*. auto.
wp. rcondf 3.       
inline AlmostYul.iszero. wp.
ecall (pointIsInCurve_m_h x1 y1). skip. progress. rewrite /as_bool. simplify.
rewrite /pointIsInCurve in H4.
have ->: y1{hr} * y1{hr} * R %% P
  = y1{hr} * y1{hr} %% P * R %% P. smt(@IntDiv).
rewrite H4. smt(@IntDiv).
call (_:true);auto.
call (_:true);auto.
qed.       

lemma ecAdd_correct_4 x1_in y1_in x2_in y2_in :  
 hoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in) 
         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ !(x2_in = 0 /\ y2_in = 0) 
         /\ 0 <= x1_in < AlmostYUL.N 
         /\ 0 <= y1_in < AlmostYUL.N
         /\ 0 <= x2_in < AlmostYUL.N 
         /\ 0 <= y2_in < AlmostYUL.N      
         /\ pointIsInCurve x1_in y1_in
         /\ pointIsInCurve x2_in y2_in
         /\ x1_in = x2_in
         /\ (P - y1_in) = y2
               ==> res = (0,0) ].
proc.             
rcondf 5. inline*. wp. skip. progress.  smt().
rcondt 5. inline*. wp. skip. progress. 
rcondf 7. inline*. auto. smt().
rcondt 7. inline*. wp. skip. progress.
rcondf 9. inline*. wp. skip. progress. smt().
rcondt 9. inline*. auto. 
rcondf 14. inline*. auto. smt().
rcondf 19. inline*. auto. smt().
rcondt 24. inline*. auto. progress. rewrite /as_bool. smt.
rcondf 36. wp. auto.
wp.
seq 27 : (#pre /\ m_x1 = x1_in * R %% P  
               /\ m_y1 = y1_in * R %% P 
               /\ m_x2 = x2_in * R %% P  
               /\ m_y2 = y2_in * R %% P). auto.
ecall (into_m_h y2).
ecall (into_m_h x2).
ecall (into_m_h y1).
ecall (into_m_h x1).
inline*. auto. progress.  qed.



lemma qqq (a b P : int) : (a - b) %% P = (a %% P - b %% P) %% P.
    smt(@Int @IntDiv). qed.




op add_x (x y : int) =  let slope = 3 * (x ^ 2) * inv P (2 * y) in (slope ^ 2 - (2 * x)).
op add_y (x y : int) =  let slope = 3 * (x ^ 2) * inv P (2 * y) in
                        let x3 = add_x x y in (slope  * (x - x3) - y).



lemma ecAdd_correct_5 x1_in y1_in x2_in y2_in :  
 hoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in) 
         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ !(x2_in = 0 /\ y2_in = 0) 
         /\ 0 <= x1_in < AlmostYUL.N 
         /\ 0 < y1_in < AlmostYUL.N (* to be disjoint from  *)
         /\ 0 <= x2_in < AlmostYUL.N 
         /\ 0 < y2_in < AlmostYUL.N      
         /\ pointIsInCurve x1_in y1_in
         /\ pointIsInCurve x2_in y2_in
         /\ (x1_in = x2_in /\ y1_in = y2_in)
               ==> res = ((add_x x1_in y1_in) %% P, (add_y x1_in y1_in) %% P) ].
proc.             
rcondf 5. inline*. wp. skip. progress. smt().
rcondt 5. inline*. wp. skip. progress. 
rcondf 7. inline*. auto. smt().
rcondt 7. inline*. wp. skip. progress.
rcondf 9. inline*. wp. skip. progress. smt().
rcondt 9. inline*. auto. 
rcondf 14. inline*. auto. smt().
rcondf 19. inline*. auto. smt().
rcondf 24. inline*. auto. progress. rewrite /as_bool.
 have f: (AlmostYUL.N - y2{hr}) %% R = (AlmostYUL.N - y2{hr}). smt.
 rewrite f f. 
 have ->: (AlmostYUL.N - y2{hr}) %% AlmostYUL.N = (AlmostYUL.N - y2{hr}). smt.
 admit.

             
rcondt 24. inline*. auto. progress. rewrite /as_bool.
rcondf 33. inline*. auto. 

rcondt 36. inline*. auto. progress. rewrite /as_bool.
rcondf 63. wp. auto.
seq 35 : (#pre). inline*. auto.
    
seq 2 : (#pre /\ x = x1_in * R %% P  /\ y = y1_in * R %% P). auto.
ecall (into_m_h y1).
ecall (into_m_h x1). 
skip. progress. smt. smt(). smt.
rcondf 3.  inline 2. wp.             
ecall (pointIsInCurve_m_h x1_in y1_in). skip. progress.  rewrite /as_bool. simplify.
have ->: y2{hr} * y2{hr} * R %% P
  = y2{hr} * y2{hr} %% P * R %% P. smt(@IntDiv).
rewrite H9. smt(@Int @IntDiv).
pose x1_squared_raw := x1_in * x1_in.              
seq 3 : (#pre /\ x1_squared = x1_squared_raw * R %% P). auto.
ecall (mul_m_h x1_in x1_in). call (_:true);auto. call (_:true);auto. progress.
smt. smt. smt. smt. inline 1. sp.
seq 1 : (#pre /\ func372 = (x1_squared + x1_squared) %% P). inline*. wp. skip. progress. smt.
seq 2 : (#pre /\ func368 = (x1_squared + (x1_squared + x1_squared)) %% P). inline*. wp. skip. progress.
pose x:= x2{hr} * x2{hr} * R %% P.
     have ->: (x + (x + x) %% P) %% R = (x + (x + x) %% P). smt.
             smt(@Int @IntDiv).
seq 2 : (#pre /\ func382 = (y1_in + y1_in) * R %% P). inline*. wp.  progress. skip. progress. admit.
pose slope_raw := (3 * x1_squared_raw) * (inv P (y1_in + y1_in)).             
seq 1 : (#pre /\ slope = slope_raw * R %% P).
ecall (div_m_h (3 * x1_in * x1_in) (y1_in + y1_in)).
skip. progress.

    admit. smt. smt. admit.  smt. rewrite /slope_raw. rewrite /x1_squared_raw. smt.

seq 1 : (#pre /\ func392 = (slope_raw * slope_raw) * R %% P).
ecall (mul_m_h slope_raw slope_raw). skip. progress. smt. smt. smt. smt.             
seq 2 : (#pre /\ func398 = (x1_in + x1_in) * R %% P). inline*. wp. skip. progress.
have ->: (x2{hr} + x2{hr}) * R = (x2{hr} * R + x2{hr} * R). smt. 
have ->: (x2{hr} * R %% P + x2{hr} * R %% P) %% R 
  = (x2{hr} * R %% P + x2{hr} * R %% P). smt.
  smt(@Int @IntDiv).
  
pose x3_raw := ((slope_raw * slope_raw) - (x1_in + x1_in)).
seq 2 : (#pre /\ x3 = x3_raw * R %% P).
                 
ecall (submod_h (slope_raw * slope_raw * R %% P) ((x1_in + x1_in) * R %% P) P). inline*.  wp. skip. progress.
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv). smt. smt(@Int @IntDiv). smt(@Int @IntDiv).
  
have ->: (slope_raw * slope_raw - (x2{hr} + x2{hr})) * R
              = (slope_raw * slope_raw * R - (x2{hr} + x2{hr}) * R).
                 smt(@Int @IntDiv).
rewrite - qqq.  auto.

seq 2 : (#pre /\ func414 = (x1_in - x3_raw) * R %% P).
ecall (submod_h x x3 P). inline*. wp. skip. progress.
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv). smt. smt(@Int @IntDiv). smt(@Int @IntDiv).              
smt(@Int @IntDiv). 

seq 1 : (#pre /\ func410 = slope_raw * (x1_in - x3_raw) * R %% P).
ecall (mul_m_h slope_raw (x1_in - x3_raw)). skip. progress. smt(@Int @IntDiv).
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv).              

seq 2 : (#pre /\ y3 = (slope_raw * (x1_in - x3_raw) -  (y1_in)) * R %% P).
ecall (submod_h func410 y P). inline*. wp. skip. progress.
smt(@Int @IntDiv). smt(@Int @IntDiv). smt(@Int @IntDiv).
smt. smt(@Int @IntDiv). smt(@Int @IntDiv). 
rewrite - qqq. smt(@Int).
wp.
ecall (outof_m_h y3).
ecall (outof_m_h x3).
skip. progress.
smt(@Int @IntDiv).
smt(@Int @IntDiv).                            
smt(@Int @IntDiv).
smt(@Int @IntDiv).
have ->: x3_raw * R %% P * inv P R %% P = x3_raw %% P. admit.
rewrite /add_x. simplify.
rewrite /x3_raw.
rewrite /slope_raw.
rewrite /x1_squared_raw.
have ->: (x2{hr} * x2{hr}) = x2{hr} ^ 2. smt.
congr. congr. smt.

have ->: (slope_raw * (x2{hr} - x3_raw) - y2{hr}) * R %% P * inv P R %% P
              = (slope_raw * (x2{hr} - x3_raw) - y2{hr}) %% P.
have ->: (slope_raw * (x2{hr} - x3_raw) - y2{hr}) * R %% P * inv P R %% P
 = ((slope_raw * (x2{hr} - x3_raw) - y2{hr}) * (inv P R * R)) %% P. smt(@Int @IntDiv).
have ->: ((slope_raw * (x2{hr} - x3_raw) - y2{hr}) * (inv P R * R)) %% P
  = ((slope_raw * (x2{hr} - x3_raw) - y2{hr}) * ((inv P R * R) %% P)) %% P. smt(@Int @IntDiv).
rewrite inv_ax.  simplify. smt. simplify. auto.
              
congr. congr.
rewrite /add_y /add_x. simplify.
rewrite /slope_raw.
rewrite /x1_squared_raw.
rewrite /x3_raw.
rewrite /slope_raw.
rewrite /x1_squared_raw.
have ->: (x2{hr} * x2{hr}) = x2{hr} ^ 2. smt.
congr.
have ->: (3 * x2{hr} ^ 2 * inv P (y2{hr} + y2{hr}) *
  (3 * x2{hr} ^ 2 * inv P (y2{hr} + y2{hr})) = (3 * x2{hr} ^ 2 * inv P (2 * y2{hr})) ^ 2). smt.
smt.
qed.
