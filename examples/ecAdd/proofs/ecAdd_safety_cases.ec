require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.
require import Montgomery_arith.
require import EcAdd_spec.
require import ExtraFacts.
     



lemma nosmt mul_inj (a b r : int) : coprime r P
    => a * r %% P = b * r %% P => a %% P = b %% P.
move => coprime_h eq.
 have : a * r * (inv P r) %% P = b * r * (inv P r) %% P.
  have ->: (a * r) * (inv P r) %% P = (a * r %% P)  * (inv P r) %% P.
  smt(@IntDiv).
  rewrite eq.
  smt(@IntDiv).
  have ->: a * r * inv P r = a * (r * inv P r). smt(@IntDiv).
  have ->: b * r * inv P r = b * (r * inv P r). smt(@IntDiv).
  have ->: a * (r * inv P r) %% P = a * (r * inv P r %% P) %% P.
  smt(@IntDiv).
  have ->: b * (r * inv P r) %% P = b * (r * inv P r %% P) %% P.
  smt(@IntDiv).
  rewrite inv_ax_opp. smt(@IntDiv).
  simplify.
  auto.
qed.

lemma nosmt mul_inj_contra_pos (a b r : int) :  coprime r P =>
  a %% P <> b %% P =>  a * r %% P <> b * r %% P.
proof. smt(mul_inj). qed.




lemma ecAdd_safety_1 x1_in y1_in x2_in y2_in :  0 <= x1_in /\ 0 <= y1_in /\ 0 <= x2_in /\ 0 <= y2_in =>
 phoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in) /\
      (x1_in < AlmostYUL.N
         /\ y1_in < AlmostYUL.N
         /\ x2_in < AlmostYUL.N
         /\ y2_in < AlmostYUL.N) /\
         (((!pIsInfinity (x1_in, y1_in)) /\ (!pointIsInCurve x1_in y1_in)) \/
         ((!pIsInfinity (x2_in, y2_in)) /\ (!pointIsInCurve x2_in y2_in)))      
                 ==> true ] = 0%r.
move => eqs. hoare. simplify.
proc.
seq 5 : (#pre /\ ret_bool = false /\ p1IsInfinity = pIsInfinity (x1_in, y1_in)
 /\  p2IsInfinity = pIsInfinity (x2_in, y2_in)                 ). inline*.
seq 10 : (#pre /\ ret_bool = false  /\ func17 = (pIsInfinity (x1_in, y1_in) /\ pIsInfinity (x2_in, y2_in))
 /\  p1IsInfinity = pIsInfinity (x1_in, y1_in)
 /\  p2IsInfinity = pIsInfinity (x2_in, y2_in)                 
 ). wp. skip. progress.
rcondf 1. skip. progress. smt. skip. smt.
rcondt 1. auto.
seq 2 : (#pre  /\ func43 = (p1IsInfinity /\ !p2IsInfinity)). inline*.  wp. skip. auto.
if.
seq 11 : (false).
rcondf 6. inline*. wp. skip. progress. smt.
seq 7 : (#pre /\ m_x2 = x2 * R %% P /\ m_y2 = y2 * R %% P).
ecall (into_m_h y2_in).
ecall (into_m_h x2_in).  inline*. wp. skip. progress.   smt(). smt(). smt(). smt().
rcondt 3. inline 2. wp.
ecall (pointIsInCurve_m_h x2 y2).  skip. progress.
rewrite /as_bool.
have ->: (x2{hr} * x2{hr} * x2{hr} * R + 3 * R)
 = (x2{hr} * x2{hr} * x2{hr}  + 3 ) * R. smt().
apply mul_inj_contra_pos. smt. 
smt. 
inline 3. while (true). auto. auto. exfalso.
rcondt 1. auto.
seq 2 : (#pre  /\ func109 = (!p1IsInfinity /\ p2IsInfinity)). inline*.  wp. skip. auto.
if.  
rcondf 6. inline*. wp. skip. smt.
seq 7 : (#pre /\ m_x1 = x1 * R %% P /\ m_y1 = y1 * R %% P).
ecall (into_m_h y1_in).
ecall (into_m_h x1_in). inline*. wp. skip. progress;smt().
rcondt 3. inline 2. wp.  
ecall (pointIsInCurve_m_h x1 y1).  skip. progress.
have ->: (x1{hr} * x1{hr} * x1{hr} * R + 3 * R)
 = (x1{hr} * x1{hr} * x1{hr}  + 3 ) * R. smt().
apply mul_inj_contra_pos. smt.
 smt.
seq 3 : (false). inline 3.
 while (true). auto. auto. exfalso.
rcondt 1. auto.
seq 12 : (#pre).
rcondf 6. inline*. wp. progress. skip. progress. smt.
seq 10 : (#pre). inline*. auto.
if. inline*. while(true).  auto. auto. auto.
seq 5 : (#pre /\ func211 = ((x1 = x2) /\ func219)).
inline*. wp. skip. progress.
if.
seq 4 : (#pre /\ m_x1 = x1 * R %% P /\ m_y1 = y1 * R %% P
       /\ m_x2 = x2 * R %% P /\ m_y2 = y2 * R %% P).
ecall (into_m_h y2_in).
ecall (into_m_h x2_in).
ecall (into_m_h y1_in).
ecall (into_m_h x1_in).
skip. progress;smt(). 
rcondt 6.
inline 5. inline 4. wp.
ecall (pointIsInCurve_m_h x2 y2).
inline 2. wp.
ecall (pointIsInCurve_m_h x1 y1).
skip. progress. 
have ->: (x1{hr} * x1{hr} * x1{hr} * R + 3 * R)
  = (x1{hr} * x1{hr} * x1{hr} + 3) * R. smt().
have ->: (x2{hr} * x2{hr} * x2{hr} * R + 3 * R)
  = (x2{hr} * x2{hr} * x2{hr} + 3) * R. smt().
have ok : ! pointIsInCurve x1{hr} y1{hr} \/ ! pointIsInCurve x2{hr} y2{hr} . smt.
have okk : coprime R P. smt.
smt (mul_inj_contra_pos).
seq 6 : (false).
inline 6. while (true). auto. auto. exfalso.
rcondt 1. auto.
seq 10 : (#pre).
seq 9 : (#pre). inline*. auto. if. inline*. while(true). auto. auto.   skip. progress.
seq 3 : (#pre /\ func325 = (x1 = x2 /\ y1 = y2))  . inline*. wp. skip. progress.
if.
seq 2 : (#pre /\ x = x1 * R %% P /\ y = y1 * R %% P).
ecall (into_m_h y1_in).
ecall (into_m_h x1_in). skip. progress;smt().  
seq 3 : (false).
rcondt 3. inline 2. wp.  
ecall (pointIsInCurve_m_h x1 y1). skip. progress. rewrite /as_bool.
have ->: (x1{hr} * x1{hr} * x1{hr} * R + 3 * R) = (x1{hr} * x1{hr} * x1{hr}+ 3) * R. smt().
apply mul_inj_contra_pos. smt. smt.
inline 3. while (true). auto. auto. exfalso.
rcondt 1. auto. simplify.
seq 4 : ((((((((((
           (x1_in < AlmostYUL.N /\
            y1_in < AlmostYUL.N /\ x2_in < AlmostYUL.N /\ y2_in < AlmostYUL.N) /\
           (! pIsInfinity (x1_in, y1_in) /\ ! pointIsInCurve x1_in y1_in \/
            ! pIsInfinity (x2_in, y2_in) /\ ! pointIsInCurve x2_in y2_in)) /\
          ret_bool = false /\
          p1IsInfinity = pIsInfinity (x1_in, y1_in) /\
          p2IsInfinity = pIsInfinity (x2_in, y2_in)) /\
         func43 = (p1IsInfinity /\ !p2IsInfinity)) /\
        ! as_bool func43) /\
       func109 = (!p1IsInfinity /\ p2IsInfinity)) /\
      ! as_bool func109) /\
     func211 = (x1_in = x2_in /\ func219)) /\
    ! as_bool func211) /\
   func325 = (x1_in = x2_in /\ y1_in = y2_in)) /\
  ! as_bool func325 /\ x1 = x1_in * R %% P /\ y1 = y1_in * R %% P /\ x2 = x2_in * R %% P /\ y2 = y2_in * R %% P).  
ecall (into_m_h y2_in).
ecall (into_m_h x2_in).
ecall (into_m_h y1_in).
ecall (into_m_h x1_in). skip.  progress. smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). 
seq 6 : (false).
rcondt 6.
inline 5. inline 4. wp.  
ecall (pointIsInCurve_m_h x2_in y2_in).
inline 2. wp.  
ecall (pointIsInCurve_m_h x1_in y1_in).
skip. progress.
rewrite /as_bool.  
have :  ! pointIsInCurve x1_in y1_in \/ ! pointIsInCurve x2_in y2_in. smt.
elim. progress.
left.
have ->: (x1_in * x1_in * x1_in * R + 3 * R) = (x1_in * x1_in * x1_in + 3 ) * R. smt().
apply mul_inj_contra_pos. smt. smt.
progress.
right.
have ->: (x2_in * x2_in * x2_in * R + 3 * R) = (x2_in * x2_in * x2_in + 3 ) * R. smt().
apply mul_inj_contra_pos. smt.  smt.
inline 6.
while(true). auto. auto. exfalso.
qed.  

 
  

lemma ecAdd_safety_2 x1_in y1_in x2_in y2_in :  
 phoare[ AlmostYul.main : 
         arg = (x1_in,y1_in,x2_in,y2_in)/\
         !(x1_in < AlmostYUL.N
         /\ y1_in < AlmostYUL.N
         /\ x2_in < AlmostYUL.N
         /\ y2_in < AlmostYUL.N)
                 ==> true ] = 0%r.
hoare. simplify.
proc.
rcondt 6.
rcondf 5.
inline*. progress. wp. skip. progress.
smt.               
inline*. progress. auto.
seq 5 : (#pre /\ ret_bool = false /\ p1IsInfinity = pIsInfinity (x1,y1) /\ p2IsInfinity = pIsInfinity (x2,y2) ). inline*. progress. wp. skip. progress. smt.
seq 2 : (#pre /\  func43 = (pIsInfinity (x1_in, y1_in) /\ !pIsInfinity  (x2_in, y2_in))). inline*. wp. skip.
progress.   
if.
  seq 6 : (false).
inline*. sp. rcondt 1. skip. progress. smt.
while (true). auto. skip. auto. exfalso.                              
rcondt 1. auto.               
seq 2 : (#pre /\ func109 = (!pIsInfinity (x1_in, y1_in) /\ pIsInfinity  (x2_in, y2_in)) ). inline*. auto.
if.
  seq 6 : (false).
inline*. sp. rcondt 1. skip. progress. smt.
while (true). auto. skip. auto. exfalso.               
rcondt 1. auto.
  seq 6 : (#pre /\ !(!x1 < P \/  !y1 < P)).               
seq 5 : (#pre /\ func175 = (!x1 < P \/  !y1 < P) ). inline*. auto.  progress.
if. inline*. while (true). auto. auto. skip. progress.  
seq 6 : (false).               
inline*. sp. rcondt 1. skip. progress. smt.
while (true). auto. skip. auto. exfalso.               
qed.
