
(* 

1/ implement standard REDC
2/ implement ecAdd version of REDC
3/ prove rel. between 1/ and 2/
4/ 

*)

require import Int IntDiv.
require import Gcd Gcd_props.


module REDC = {
  
  proc main(T : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- ((T %% R) * N') %% R;
    t <- (t + m * N) %/ R;
    if (N <= t ){
      r <- t - N;
    }else{
      r <- t;
    }
    return r;
  }
}.



op m_val T R N' = ((T %% R) * N') %% R.
op t_val' T R N' N = (T + (m_val T R N') * N).
op t_val T R N' N = (t_val' T R N' N) %/ R.
op redc T R N' N = let t = t_val T R N' N in if N <= t then t - N else t.


lemma aux1 T R N' N : (N' * N %% R) = -1 =>
    R %| t_val' T R N' N.
move => ass1.    
apply dvdzE.
rewrite /t_val /m_val.
have ->: (T + T %% R * N' %% R * N) %% R = (T + T * N' * N) %% R.
admit.
have ->: (T + T * N' * N) %% R = (T + T * (N' * N %% R)) %% R. admit.
have ->: (N' * N %% R) = -1. assumption.
smt.
qed.    

lemma aux2 T R N' N : (N' * N %% R) = -1 =>
    exists k, t_val' T R N' N = k * R.
move => ass1.    
apply dvdzP. apply aux1. assumption. qed.


lemma gen a x N : x %| a => (a %/ x) %% N = a * (inv N x) %% N.
admitted.
    

lemma aux3 T R N' N : (N' * N %% R) = -1 =>
    (t_val T R N' N) %% N = T * (inv N R) %% N.
proof. move => ass1.
rewrite /t_val gen. apply aux1. assumption.
rewrite /t_val'.
have -> : (T + m_val T R N' * N) * inv N R %% N =
 (T * (inv N R) + (m_val T R N' * N) * inv N R)  %% N. smt.
 have ->: (T * inv N R + m_val T R N' * N * inv N R) %% N =
   (T * inv N R %% N + ((m_val T R N' * N * inv N R) %% N) ) %% N. smt(@Int @IntDiv).
 have ->:    ((m_val T R N' * N * inv N R) %% N) = 0. smt(@Int @IntDiv). simplify.
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

lemma redc_correct T R N' N : 0 < R => 0 < N => 0 <= T < R * N =>
   (N' * N %% R) = -1 =>
    (redc T R N' N) = T * (inv N R) %% N.
progress.
rewrite /redc.
rewrite - (aux3 T R N' N).     auto.
simplify.    
case (N <= t_val T R N' N). progress.
smt.
progress. smt.
qed.    



    
    
