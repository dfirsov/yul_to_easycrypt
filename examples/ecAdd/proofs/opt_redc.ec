require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.

module OptREDC = {

  proc _REDC1(Tlo : int, Thi : int, R : int, N : int, N' : int) = {
    var m, hi, lo, s, tmp : int;
    var overflowed : bool;
    m <- (Tlo * N') %% R;
    hi <- (Thi + ((m * N) %/ R)) %% R;
    tmp <- (m * N) %% R;
    (lo, overflowed) <@ AlmostYul.overflowingAdd(Tlo, tmp, R);
    hi <- if overflowed then (hi + 1) %% R else hi;
    s <- if N <= hi then (hi - N) %% R else hi;
    return s;
  }

  proc _REDC2(Tlo : int, Thi : int, R : int, N : int, N' : int) = {
    var m, hi, lo, s, tmp : int;
    m <- (Tlo * N') %% R;     
    hi <- (Thi + ((m * N) %/ R)) %% R;
    tmp <- (m * N) %% R;
    lo <- (Tlo + tmp) %% R;
    hi <- if lo < Tlo then (hi + 1) %% R else hi;
    s <- if N <= hi then (hi - N) %% R else hi;
    return s;
  }


  proc _REDC3(Tlo : int, Thi : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- (Tlo * N') %% R;     
    t <- (Thi + ((m * N) %/ R)) %% R;
    t <- if (Tlo + (m * N) %% R) %% R < Tlo then (t + 1) %% R else t;
    r <- if N <= t then (t - N) %% R else t;
    return r;
  }


  proc _REDC4(T : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- ((T %% R) * N') %% R;
    t <- (T %/ R + (m * N) %/ R) %% R;
    t <- if ((T + ((m * N))) %% R < T %% R) then (t + 1) %% R else t;
    if (N <= t){
      r <- (t - N) %% R;
    }else{
      r <- t;
    }
    return r;
  } 

  proc _REDC5(T : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- ((T %% R) * N') %% R;
    t <- (T %/ R + (m * N) %/ R) %% R;
    t <- if ((T + ((m * N))) %% R < T %% R) then (t + 1) %% R else t;
    r <- if N <= t then  (t - N) %% R else t;
    return r;
  } 

}.


op o_m_val T R N' = ((T %% R) * N') %% R.
op o_t_val' T R N' N = (T %/ R + ((o_m_val T R N') * N) %/ R).
op o_t_val T R N' N = o_t_val' T R N' N + if ((T + (((o_m_val T R N') * N))) %% R < T %% R) then 1 else 0.
op o_redc T R N' N = let t = o_t_val T R N' N in if N <= t then t - N else t.
op o2_t_val' T R N' N = (T %/ R + ((o_m_val T R N') * N) %/ R) %% R.
op o2_t_val T R N' N = (if ((T + (((o_m_val T R N') * N))) %% R < T %% R) then o_t_val' T R N' N + 1 else o_t_val' T R N' N) %% R.
op o2_redc T R N' N = let t = o2_t_val T R N' N in if N <= t then (t - N) %% R else t.


lemma maeq : equiv [ AlmostYul._REDC ~ OptREDC._REDC1 : ={arg} ==> ={res}].
proc. inline*. wp. skip. progress. qed.
lemma maeq2 : equiv [ OptREDC._REDC1 ~ OptREDC._REDC2 : ={arg} ==> ={res}].
proc. inline*. wp. skip. progress. qed.
lemma maeq3 : equiv [ OptREDC._REDC2 ~ OptREDC._REDC3 : ={arg} ==> ={res}].
proc. inline*. wp. skip. progress. qed.
lemma maeq4 : equiv [ OptREDC._REDC3 ~ OptREDC._REDC4 : Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2}
       /\ ={R, N, N'} ==> ={res}].
proc.
seq 1 1 : (#pre /\ ={m}). wp. skip. progress.
seq 1 1 : (#pre /\ ={t}). wp. skip. progress.
seq 1 1 : (#pre /\ ={t}). wp. skip. progress.
have ->:
 (T{2} %% R{2} + m{2} * N{2} %% R{2}) %% R{2}
  = (T{2} + m{2} * N{2} ) %% R{2}. smt(@Int @IntDiv).
auto.  
have ->:
 (T{2} %% R{2} + m{2} * N{2} %% R{2}) %% R{2}
  = (T{2} + m{2} * N{2} ) %% R{2}. smt(@Int @IntDiv).
auto.  
wp. skip. progress.
qed.  


lemma maeq5 : equiv [ OptREDC._REDC4 ~ OptREDC._REDC5 : ={arg} ==> ={res}].
proc. inline*. wp. skip. progress. qed.


lemma maeq6 T R N' N : phoare[ OptREDC._REDC5 : arg = (T,R,N,N') ==> res = o2_redc T R N' N ] = 1%r.
proc.
seq 1 : (#pre /\ m = o_m_val T R N'). wp. skip. auto. wp. skip. smt().
seq 2 : (#pre /\ t = o2_t_val T R N' N). wp. skip. auto. wp. skip.
progress.  rewrite /o2_t_val. rewrite /o_t_val'.
case ((T{hr} + o_m_val T{hr} R{hr} N'{hr} * N{hr}) %% R{hr} < T{hr} %% R{hr}).
progress. smt (@Int @IntDiv). smt (@Int @IntDiv).
wp. skip. progress. hoare. simplify. 
seq 2 : (#pre /\ t = o2_t_val T R N' N). wp. skip. progress.  rewrite /o2_t_val. rewrite /o_t_val'.
case ((T{hr} + o_m_val T{hr} R{hr} N'{hr} * N{hr}) %% R{hr} < T{hr} %% R{hr}).
progress. smt (@Int @IntDiv). smt (@Int @IntDiv). auto. auto.
hoare. wp. skip. progress. auto.
qed.    


    
lemma q (a b d : int) : d <> 0 =>  (a * d + b) %/ d = a + (b %/ d).
 apply divzMDl. 
qed.    


lemma qq (a b d : int) :  0 < d  =>  (a + b) %/ d = (a %/ d + b %/ d) + 
 (if (a %% d + b %% d) %% d < a %% d then 1 else 0).
move => dnn. 
pose a' := a %/ d.
pose r1 := a %% d.
have a_form : a = a' * d + r1. smt (divz_eq).
pose b' := b %/ d.
pose r2 := b %% d.
have b_form : b = b' * d + r2. smt (divz_eq).
have -> : (a + b) %/ d = (a' + b')  + (r1 + r2) %/ d.
rewrite a_form b_form.
  have ->: (a' * d + r1 + (b' * d + r2))  =  
   (a' * d + b' * d  + (r1 + r2)). smt(@Int).
  have ->: a' * d + b' * d = (a' + b') * d. smt(@Int).
  rewrite q.  smt(). auto. 
have ->: (r1 + r2) %/ d
    = if (r1 + r2) %% d < r1 then 1 else 0.
have r1_pos : 0 <= r1 < d. rewrite /r1.
progress. smt(@Int @IntDiv). smt(@IntDiv).
have r2_pos : 0 <= r2 < d. rewrite /r2. smt(@IntDiv).
case ((r1 + r2) < d).
progress.    
have ->: (r1 + r2) %% d = r1 + r2.
    smt(@Int @IntDiv).
have ->: (r1 + r2 < r1 = false).  smt(@IntDiv).
simplify.    
smt.
progress.
have ->: (r1 + r2) %% d = (r1 + r2) - d. smt(@IntDiv).
smt.
    auto.
qed.    


require import Redc.
lemma opt_tval_eq T R N' N : 0 < R =>
 t_val T R N' N = o_t_val T R N' N.
move => Rpos.    
rewrite /t_val /o_t_val /t_val' /o_t_val'.
have ->: o_m_val T R N' = m_val T R N'. auto.
pose m := m_val T R N'.
rewrite qq;auto.
have ->: (T + m * N) %% R =  (T %% R + m * N %% R) %% R. smt(@Int @IntDiv).
    auto. 
qed.    


lemma opt_tval_eq2 T R N' N : 2 * N < R => 0 < N => 0 <= T < R * N =>
 (o_t_val T R N' N) %% R = o_t_val T R N' N.
progress. 
rewrite - opt_tval_eq. smt().
have : 0 <= (t_val T R N' N) < 2 * N.
 apply aux6. smt(). auto.  auto.
smt(@IntDiv).
qed.

lemma opt_tval_eq3 T R N' N : 2 * N < R => 0 < N => 0 <= T < R * N =>
 (o2_t_val T R N' N)  = o_t_val T R N' N.
progress. rewrite - opt_tval_eq2;auto.
smt(@IntDiv).
qed. 


lemma opt_redc_eq3 T R N' N : 2 * N < R => 0 < N => 0 <= T < R * N =>
 (o2_redc T R N' N)  = o_redc T R N' N.
progress.
rewrite /o2_redc /o_redc. 
rewrite opt_tval_eq3;auto.
simplify. rewrite - opt_tval_eq. smt().
case (N <= t_val T R N' N ). progress.
have : 0 <= (t_val T R N' N) < 2 * N.
 apply aux6. smt(). auto. auto. progress.
 smt. auto.
qed. 
 


lemma opt_redc_eq T R N' N : 0 < R =>
    o_redc T R N' N = redc T R N' N .
progress.    
rewrite /o_redc /redc. simplify.
have ->: t_val T R N' N = o_t_val T R N' N.
rewrite opt_tval_eq;auto.    
 auto.
qed.    




lemma almost_yul_redc_full_correctness T_in Tlo Thi R_in N' N :
  2 * N < R_in =>
  0 < N => 
  0 <= T_in < R_in * N =>
  (N' * N %% R_in) = (- 1) %% R_in => 
  coprime N R_in =>
  Tlo = T_in %% R_in =>
  Thi = T_in %/ R_in =>
  
 phoare[ AlmostYul._REDC : arg = (Tlo,Thi,R_in,N,N')
        ==> res = T_in * (inv N R_in) %% N ] = 1%r.
      
proof. progress. bypr. progress.
have <-: Pr[ OptREDC._REDC5(T_in,R_in,N,N') @&m : res = T_in * (inv N R_in) %% N] = 1%r.
have ->: Pr[OptREDC._REDC5(T_in, R_in, N, N') @ &m : res = T_in * inv N R_in %% N]
 = Pr[OptREDC._REDC5(T_in, R_in, N, N') @ &m : res = o2_redc T_in R_in N' N].
rewrite Pr[mu_eq] . progress.
rewrite opt_redc_eq3;auto.
rewrite -  (redc_fun_correct T_in R_in N' N);auto. smt().  
rewrite opt_redc_eq;auto. smt().
rewrite opt_redc_eq3;auto.
rewrite -  (redc_fun_correct T_in R_in N' N);auto. smt(). 
rewrite opt_redc_eq;auto. smt(). auto.
byphoare (_: arg = (T_in,R_in,N,N') ==> _).
apply maeq6. auto. auto.
byequiv. progress.


transitivity OptREDC._REDC1
 (={arg} ==> ={res})
 (Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2} /\ ={R,N,N'} /\ T{2} = T_in /\ R{2} = R_in ==> ={res}).
progress. smt().
smt().  auto.
apply maeq.


transitivity OptREDC._REDC2
 (={arg} ==> ={res})
 (Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2} /\ ={R,N,N'} /\ T{2} = T_in /\ R{2} = R_in ==> ={res}).
smt().  auto.
apply maeq2.


transitivity OptREDC._REDC3
 (={arg} ==> ={res})
 (Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2} /\ ={R,N,N'} /\ T{2} = T_in /\ R{2} = R_in ==> ={res}).
progress. smt().
 
smt().  auto.
apply maeq3.

transitivity OptREDC._REDC4    
 (Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2} /\ ={R, N, N'} /\ T{2} = T_in /\ R{2} = R_in ==> ={res})
 (={arg} ==> ={res}).
  auto. smt().
auto.
 
conseq maeq4. progress. 
conseq maeq5. auto. auto.
qed. 
