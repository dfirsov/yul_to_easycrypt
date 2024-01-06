require import AllCore Int IntDiv.
require import Gcd Gcd_props.


module REDC = {  
  proc main(T : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- ((T %% R) * N') %% R;
    t <- (T + m * N) %/ R;
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


lemma aux1 (T R N' N : int) : (N' * N %% R) = -1 %% R =>
    R %| t_val' T R N' N.
move => ass1.    
apply dvdzE.
rewrite /t_val /m_val.
have ->: (T + T %% R * N' %% R * N) %% R = (T + T * N' * N) %% R.
 have ->:  (T + T * N' * N) %% R = (T %% R + T * N' * N %% R) %% R.
    smt(@Int @IntDiv).
        smt(@Int @IntDiv).
have ->: (T + T * N' * N) %% R = (T + T * (N' * N %% R)) %% R.
timeout 5.     smt(@Int @IntDiv).    
rewrite ass1.
smt(@Int @IntDiv).    
qed.    

lemma aux2 (T R N' N : int) : (N' * N %% R) = -1 %% R =>
    exists k, t_val' T R N' N = k * R.
move => ass1.    
apply dvdzP. apply aux1. assumption. qed.


lemma gen a x N : x <> 0 => coprime N x =>
     x %| a => (a %/ x) %% N = a * (inv N x) %% N.
progress.    
have f: exists (q : int), a = q * x.
smt(dvdzP).    
elim f. progress.    
have ->: q * x %/ x = q. smt(@Int @IntDiv).
have ->: q * x * inv N x = q * (inv N x * x).
smt (@Int @IntDiv).
have ->: q * (inv N x * x) %% N = q * (inv N x * x %% N) %% N.
smt(@Int @IntDiv).    
rewrite inv_ax.     auto.
simplify.  auto.
qed.    

lemma aux3 T R N' N : R <> 0 => coprime N R => (N' * N %% R) = -1 %% R =>
    (t_val T R N' N) %% N = T * (inv N R) %% N.
proof. progress.
rewrite /t_val gen;auto. apply aux1. assumption.
rewrite /t_val'.
have -> : (T + m_val T R N' * N) * inv N R %% N =
 (T * (inv N R) + (m_val T R N' * N) * inv N R)  %% N. smt.
 have ->: (T * inv N R + m_val T R N' * N * inv N R) %% N =
   (T * inv N R %% N + ((m_val T R N' * N * inv N R) %% N) ) %% N. smt(@Int @IntDiv).
 have ->:    ((m_val T R N' * N * inv N R) %% N) = 0. clear H0 H1. smt(@IntDiv). simplify.
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

lemma redc_fun_correct T R N' N : 0 < R => 0 < N => 0 <= T < R * N =>
   (N' * N %% R) = -1 %% R => coprime N R =>
    (redc T R N' N) = T * (inv N R) %% N.
progress.
rewrite /redc.
rewrite - (aux3 T R N' N).     smt(). auto. auto.
simplify.    
case (N <= t_val T R N' N). progress.
have f : t_val T R N' N < 2 * N. smt(aux6).    
smt.
progress.    
have f : 0 <= t_val T R N' N < N. smt().
smt.
qed.    


lemma REDC_main T R N' N :
  phoare [ REDC.main : arg = (T, R, N, N') ==> res = T * (inv N R) %% N ] = 1%r.    
proc.
wp.  skip. progress.
rewrite -   (redc_fun_correct T{hr} R{hr} N'{hr} N{hr}).    
admit. admit. admit. admit. admit.
rewrite /redc. simplify. rewrite /t_val /t_val' /m_val H.  simplify. auto.
rewrite -   (redc_fun_correct T{hr} R{hr} N'{hr} N{hr}).    
admit. admit. admit. admit. admit.
rewrite /redc. simplify. rewrite /t_val /t_val' /m_val H.  simplify. auto.
qed.


    
    
