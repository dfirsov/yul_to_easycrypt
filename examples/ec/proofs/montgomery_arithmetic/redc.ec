require import AllCore Int IntDiv.
require import Gcd Gcd_props.


(* functional specification of REDC algorithm  *)
op m_val (T R N' : int) = ((T %% R) * N') %% R.
op t_val' (T R N' N : int) = (T + (m_val T R N') * N).
op t_val (T R N' N : int) = (t_val' T R N' N) %/ R.

op redc T R N' N = let t = t_val T R N' N in if N <= t then t - N else t.


lemma aux1 (T R N' N : int) : (N' * N %% R) = (-1) %% R =>
    R %| t_val' T R N' N.
move => ass1.    
apply dvdzE.
rewrite /t_val /m_val /t_val' /m_val.
have ->: (T + T %% R * N' %% R * N) %% R
     = (T %% R + T %% R * N' %% R * N %% R) %% R.
smt(@Int @IntDiv).     
have ->: T %% R * N' %% R * N %% R = (T %% R * N' %% R * N %% R) %% R.
smt(@Int @IntDiv).     
have ->: (T %% R * N' %% R * N %% R) %% R = (T %% R * N' %% R * (N %% R) %% R) %% R.
smt(@Int @IntDiv).     
have ->: T %% R * N' %% R = T %% R * (N' %% R) %% R.
smt(@Int @IntDiv).     
have ->: T %% R * (N' %% R) %% R * (N %% R) %% R = T %% R * (N' %% R)  * (N %% R) %% R.
smt(@Int @IntDiv).
have ->: T %% R * (N' %% R)  * (N %% R) %% R = T %% R * ((N' %% R)  * (N %% R)) %% R.
smt(@Int @IntDiv).
have ->: T %% R * ((N' %% R)  * (N %% R)) %% R = T %% R * (((N' %% R)  * (N %% R)) %% R) %% R.
     smt(@Int @IntDiv).
have ->: (((N' %% R)  * (N %% R)) %% R) = (((N' )  * (N )) %% R).
     smt(@Int @IntDiv).
rewrite ass1.
have ->:  T %% R * ((-1) %% R) %% R %% R =  T %% R * ((-1) %% R) %% R.
     smt(@Int @IntDiv).
have ->: T %% R * ((-1) %% R) %% R = T  * ((-1) ) %% R.
     smt(@Int @IntDiv).
have ->: (T %% R + T * (-1) %% R) %% R = (T  + T * -1 ) %% R .
     smt(@Int @IntDiv).
     smt(@Int @IntDiv).     
qed.    

lemma aux2 (T R N' N : int) : (N' * N %% R) = (-1) %% R =>
    exists k, t_val' T R N' N = k * R.
move => ass1.    
apply dvdzP. apply aux1. assumption. qed.


lemma gen a x N : 1 < N  => x <> 0 => coprime N x =>
     x %| a => (a %/ x) %% N = a * (invm x N) %% N.
progress.    
have f: exists (q : int), a = q * x.
smt(dvdzP).    
elim f. progress.    
have ->: q * x %/ x = q. smt(@Int @IntDiv).
have ->: q * x * invm x N = q * (invm x N * x).
smt (@Int @IntDiv).
have ->: q * (invm x N * x) %% N = q * (invm x N * x %% N) %% N.
smt(@Int @IntDiv). 
smt(@Int @IntDiv). 
qed.    

lemma aux3 T R N' N : 1 < N => R <> 0 => coprime N R => (N' * N %% R) = (-1) %% R =>
    (t_val T R N' N) %% N = T * (invm R N) %% N.
proof. progress.
rewrite /t_val gen;auto. apply aux1. assumption.
rewrite /t_val'.
have -> : (T + m_val T R N' * N) * invm R N %% N =
 (T * (invm R N) + (m_val T R N' * N) * invm R N)  %% N. smt.
 have ->: (T * invm R N + m_val T R N' * N * invm R N) %% N =
   (T * invm R N %% N + ((m_val T R N' * N * invm R N) %% N) ) %% N. smt(@Int @IntDiv).
 have ->:    ((m_val T R N' * N * invm R N) %% N) = 0. clear H0 H1. smt(@IntDiv). simplify.
   smt(@Int @IntDiv).
qed.   


lemma aux4 T R N' : 0 < R =>
    0 <= (m_val T R N') < R.
progress.
smt.
rewrite /m_val.  smt(@Int @IntDiv).
qed.


lemma aux5 T R N' N : 0 < R => 0 < N => 0 <= T < R * N =>
    0 <= (t_val' T R N' N) < 2 * R * N.
progress. smt.
rewrite /t_val'.
pose m := m_val T R N'.
have mf : 0 <= m < R. smt(aux4).
have mf2 : 0 <= m * N < R * N.
progress. smt.    
smt.
smt.
qed.    

lemma kk a x y : 0 < x => 0 < y => 0 <= a < x * y => a %/ x < y.
progress. smt.    
qed.    


lemma aux6 T R N' N : 0 < R => 0 < N => 0 <= T < R * N =>
    0 <= (t_val T R N' N) < 2 * N.
progress.
smt.
rewrite /t_val.
pose t := t_val' T R N' N.
have tf : 0 <= t < 2 * R * N. smt(aux5).
apply kk. auto. smt(). smt.
qed.    

lemma redc_fun_correct T R N' N : 1 < N => 0 < R => 0 < N => 0 <= T < R * N =>
   (N' * N %% R) = (-1) %% R => coprime N R =>
    (redc T R N' N) = T * (invm R N) %% N.
progress.
rewrite /redc.
rewrite - (aux3 T R N' N);auto. smt(). 
simplify.    
case (N <= t_val T R N' N). progress.
have f : t_val T R N' N < 2 * N. smt(aux6).    
smt.
progress.    
have f : 0 <= t_val T R N' N < N. progress. smt. smt.
smt.
qed.    


    
    
