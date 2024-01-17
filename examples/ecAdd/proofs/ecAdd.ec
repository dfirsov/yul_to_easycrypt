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
         arg = (x1_in,y1_in,x2_in,y2_in)  
         /\ (x1_in = 0 /\ y1_in = 0) 
         /\ (x2_in = 0 /\ y2_in = 0)
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
         /\ x1_in = x2_in /\ (P - y1_in) %% P = y2
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


lemma nosmt div_fact (a P : int) : 0 < a < P /\ 0 <= P => !(P %| a).
progress. smt(@Int @IntDiv dvdn_le). qed.



lemma nosmt div_fact2 (a P : int) : 1 < P => coprime P a => !(P %| a).
progress.
have ->: a = a * 1. smt().
case (P %| a * 1);auto.
move => q.
have : P %| 1.
    apply (Gauss P a 1).     auto. auto.
apply div_fact. progress. smt().
qed.    


lemma qqq (a b P : int) : (a - b) %% P = (a %% P - b %% P) %% P.
    smt(@Int @IntDiv). qed.

search (%|).
lemma nosmt oi (y1 y2 : int) : 0 <= y1 < P /\ 0 <= y2 < P => y1 <> y2 => 0 < y1 + y2 => y1^2 %% P = y2^2 %% P => y1 %% P = (P - y2) %% P.
progress.
have fact1 : y1^2 %% P - y2^2 %% P = 0.    smt.
have  :  (y1^2  - y2^2) %% P  = 0. rewrite qqq. rewrite fact1. auto.
have  ->:  (y1^2  - y2^2) = (y1 - y2) * (y1 + y2). smt.
progress.
rewrite - dvdzE in H6.
have fact2 : P %| (y1 + y2). apply (Gauss P _ _ H6).
apply prime_coprime. smt. 
have : `|y1 - y2| < P. smt(@Int).
progress.
case ((y1 - y2) %% P = 0). 
move => oo.
have : `|y1 - y2| %% P = 0. smt (@Int @IntDiv).
progress. apply div_fact2. smt. apply prime_coprime. smt. smt.
auto.
have fact4 : exists k, (y1 + y2) = k * P.
     have d :   P %| (y1 + y2) <=> exists (q : int), y1 + y2 = q * P. apply (dvdzP P (y1 + y2)).
       elim d. progress. apply (H7 fact2).
elim fact4. progress.
have o1 : k = 1. smt.
have : P = y1 + y2. smt.
smt.
qed.



op add_x' (x1 x2 y1 y2 : int) =  let slope = (y2 - y1) * inv P (x2 - x1) in (slope * slope - (x1 + x2)).
op add_y' (x1 x2 y1 y2 : int) =  let slope = (y2 - y1) * inv P (x2 - x1) in
                           (slope * (x1 - (slope * slope - (x1 + x2))) - y1).

lemma ecAdd_correct_6 x1_in y1_in x2_in y2_in :  
 hoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in)
         /\ 0 <= x1_in < AlmostYUL.N 
         /\ 0 <= y1_in < AlmostYUL.N 
         /\ 0 <= x2_in < AlmostYUL.N 
         /\ 0 <= y2_in < AlmostYUL.N      
         /\ pointIsInCurve x1_in y1_in
         /\ pointIsInCurve x2_in y2_in

         /\ !(x1_in = 0 /\ y1_in = 0)
         /\ !(x2_in = 0 /\ y2_in = 0) 
         /\ !(x1_in = x2_in /\ y1_in = y2_in)
         /\ !(x1_in = x2_in /\ (P - y1_in) %% P = y2)
               ==> res = (add_x' x1_in x2_in y1_in y2_in %% P, add_y' x1_in x2_in y1_in y2_in %% P) ].
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
 have f: (AlmostYUL.N - y1{hr}) %% R = (AlmostYUL.N - y1{hr}). smt.
 rewrite f f. clear f.             
case (x1{hr} = x2{hr}). progress.
smt. auto.             
rcondt 24. inline*. auto. progress. rewrite /as_bool.
rcondf 37. inline*. auto.  progress. rewrite /as_bool.
seq 90 : (#pre). wp. skip. auto.
if.  while (true). auto.              auto.
skip. progress.
seq 36 : (#pre /\ ret_bool = false).             
inline *. seq 90 : (#pre /\ ret_bool = false). wp. skip. auto.
wp. if.  while (true). auto.              auto.
skip. auto. progress.
rcondt 1. auto.
seq 4 : ((
   (0 <= x1_in && x1_in < AlmostYUL.N) /\
   (0 <= y1_in && y1_in < AlmostYUL.N) /\
   (0 <= x2_in && x2_in < AlmostYUL.N) /\
   (0 <= y2_in && y2_in < AlmostYUL.N) /\
   pointIsInCurve x1_in y1_in /\
   pointIsInCurve x2_in y2_in /\
   ! (x1_in = 0 /\ y1_in = 0) /\
   ! (x2_in = 0 /\ y2_in = 0) /\
   ! (x1_in = x2_in /\ y1_in = y2_in) /\ ! (x1_in = x2_in /\ (P - y1_in) %% P = y2_in)) /\
  ret_bool = false /\ x1 = x1_in * R %% P
  /\ y1 = y1_in * R %% P
 /\ x2 = x2_in * R %% P
/\ y2 = y2_in * R %% P).
ecall (into_m_h y2_in). 
ecall (into_m_h x2_in).
ecall (into_m_h y1_in).                          
ecall (into_m_h x1_in).
skip. progress. 
seq 6 : (#pre).
seq 5 : (#pre). call (_:true). auto. call (_:true). auto.
call (_:true). auto.  call (_:true). auto. call (_:true). auto. skip. progress.
if. inline*. while (true). auto. auto. auto.
seq 2 : (#pre /\ func492 = (y2_in - y1_in) * R %% P).
ecall (submod_h y2 y1 P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite  - qqq. smt (@Int @IntDiv).
seq 2 : (#pre /\ func500 = (x2_in - x1_in) * R %% P).
ecall (submod_h x2 x1 P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite  - qqq. smt (@Int @IntDiv).
pose slope_raw := (y2_in - y1_in) * (inv P (x2_in - x1_in)).
seq 1 : (#pre /\ slope = slope_raw * R %% P).
ecall (div_m_h (y2_in - y1_in) (x2_in - x1_in)). skip. progress. smt. smt.
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
     (* 

y1^2 %% P = y2^2 %% P



y1^2 %% P - y2^2 %% P = 0
(y1^2 - y2^2) %% P  = 0
y1^2 %% P = -y2^2 %% P
(y1 - y2)(y1 + y2) %% P = 0     

 *)
move => eqq.
have : y2_in %%P = (P - y1_in) %%P.
apply (oi y2_in y1_in). smt. smt. smt.
have ->: y2_in ^ 2 = y2_in * y2_in. smt.
have ->: y1_in ^ 2 = y1_in * y1_in. smt.
rewrite H7 H8. smt().
smt().
smt.
seq 1 : (#pre /\ func510 = (slope_raw * slope_raw) * R %% P).
ecall (mul_m_h slope_raw slope_raw). skip. progress. smt. smt. smt. smt.
seq 2 : (#pre /\ func516 = (x1_in + x2_in) * R %% P).
ecall (addmod_h x1 x2 P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
smt(@Int @IntDiv).
seq 2 : (#pre /\ x3 = (slope_raw * slope_raw - (x1_in + x2_in)) * R %% P).
ecall (submod_h func510 func516 P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite - qqq. auto. smt(@Int).
seq 2 : (#pre /\ func532 = (x1_in - (slope_raw * slope_raw - (x1_in + x2_in))) * R %% P).
ecall (submod_h x1 x3 P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite - qqq. smt(@Int).
pose func532_raw := (x1_in - (slope_raw * slope_raw - (x1_in + x2_in))).
seq 1 : (#pre /\ func528 = slope_raw * func532_raw * R %% P).
ecall (mul_m_h slope_raw func532_raw). skip. progress. smt. smt. smt. smt.
seq 2 : (#pre /\ y3 = ((slope_raw * func532_raw) - y1_in) * R %% P).
ecall (submod_h func528 y1 P). inline*. wp. skip. progress. smt. smt. smt. smt. smt. smt.
rewrite - qqq. smt(@Int).
wp.
ecall (outof_m_h y3).
ecall (outof_m_h x3).
skip. progress. smt. smt. smt. smt.
have ->: (slope_raw * slope_raw - (x1_in + x2_in)) * R %% P * inv P R %% P
 = (slope_raw * slope_raw - (x1_in + x2_in)) %% P. admit. smt.
have ->: (slope_raw * func532_raw - y1_in) * R %% P * inv P R %% P
 = (slope_raw * func532_raw - y1_in) %% P. admit.
 smt.
qed.




op add_x (x y : int) =  let slope = 3 * (x ^ 2) * inv P (2 * y) in (slope ^ 2 - (2 * x)).
op add_y (x y : int) =  let slope = 3 * (x ^ 2) * inv P (2 * y) in
                        let x3 = add_x x y in (slope  * (x - x3) - y).

lemma nosmt even_fact (n a : int) : n - a = a => even n .
progress.
have : n = 2*a.
rewrite - H.    smt.
move => q. rewrite q. smt.
qed.    


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
 case (AlmostYUL.N - y2{hr} <> y2{hr});auto.
  move => j.
  have : even AlmostYUL.N. apply (even_fact AlmostYUL.N y2{hr}). auto.
  smt.             
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
seq 2 : (#pre /\ func382 = (y1_in + y1_in) * R %% P). inline*. wp.  progress. skip. progress.
have ->: (y2{hr} * R %% P + y2{hr} * R %% P) %% R  = (y2{hr} * R %% P + y2{hr} * R %% P) . smt.
smt(@Int @IntDiv).  
  
pose slope_raw := (3 * x1_squared_raw) * (inv P (y1_in + y1_in)).             
seq 1 : (#pre /\ slope = slope_raw * R %% P).
ecall (div_m_h (3 * x1_in * x1_in) (y1_in + y1_in)).
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

have ->: (y2{hr} + y2{hr}) = 2 * y2{hr}. smt().
 have : 2 * y2{hr} * R %% P <> 0. 
 (* smt(@IntDiv @Int). *)
 rewrite - dvdzE. 
 case (P %| 2 * y2{hr} * R). move => q.
 

  have qq : P %| 2 * y2{hr} \/ P %| R.
  apply Euclide. auto. smt.
  elim qq. move => zz.
  have ww : P %| 2 \/ P %| y2{hr}.
  apply Euclide. auto. smt.
  elim ww. progress. apply div_fact. smt.
  progress. apply div_fact. smt.
  progress. apply div_fact2. smt. smt. auto.
smt. 
smt.
smt. 
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
have ->: x3_raw * R %% P * inv P R %% P = x3_raw %% P.
  have ->: x3_raw * R %% P * inv P R %% P
    = x3_raw * R %% P * (inv P R %% P) %% P. smt(@Int @IntDiv).
   have ->: x3_raw * R %% P * (inv P R %% P) %% P = (x3_raw * R  * (inv P R)) %% P.
   smt(@Int @IntDiv).
   have ->: (x3_raw * R  * (inv P R)) = (x3_raw * (R  * (inv P R))). smt().
   have ->: x3_raw * (R * inv P R) %% P = x3_raw  * ((R * inv P R) %% P )  %% P. smt(@Int @IntDiv).
   rewrite inv_ax_opp. smt. auto.
    
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
