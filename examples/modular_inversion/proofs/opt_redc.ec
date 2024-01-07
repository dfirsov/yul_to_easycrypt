require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.


module OptREDC = {

  proc main1(T : int, R : int, N : int, N' : int) = {
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

  proc main2(T : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- ((T %% R) * N') %% R;
    t <- (T %/ R + (m * N) %/ R) %% R;
    t <- if ((T + ((m * N))) %% R < T %% R) then (t + 1) %% R else t;
    r <- if N <= t then  (t - N) %% R else t;
    return r;
  } 


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
lemma maeq4 : equiv [ OptREDC._REDC3 ~ OptREDC.main1 : Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2}
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

lemma maeq5 : equiv [ OptREDC.main1 ~ OptREDC.main2 : ={arg} ==> ={res}].
proc. inline*. wp. skip. progress. qed.



lemma maeq6 T R N' N : phoare[ OptREDC.main2 : arg = (T,R,N,N') ==> res = o2_redc T R N' N ] = 1%r.
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


    
lemma q (a b d : int) :  (a * d + b) %/ d = a + (b %/ d).
 apply divzMDl. admit.
qed.    


lemma qq (a b d : int) :  (a + b) %/ d = (a %/ d + b %/ d) + 
 (if (a %% d + b %% d) %% d < a %% d then 1 else 0).
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
  rewrite q. auto.
have ->: (r1 + r2) %/ d
    = if (r1 + r2) %% d < r1 then 1 else 0.

have r1_pos : 0 <= r1 < d. rewrite /r1. admit.
have r2_pos : 0 <= r2 < d. rewrite /r2. admit.    
case ((r1 + r2) < d).
progress. 
 
    
have ->: (r1 + r2) %% d = r1 + r2.
    smt(@Int @IntDiv).

have ->: (r1 + r2 < r1 = false).  admit.
simplify.    
smt.
progress.
have ->: (r1 + r2) %% d = (r1 + r2) - d. admit.
smt.
    auto.
qed.    


require import Redc.
lemma opt_tval_eq T R N' N :
 t_val T R N' N = o_t_val T R N' N.
rewrite /t_val /o_t_val /t_val' /o_t_val'.
have ->: o_m_val T R N' = m_val T R N'. auto.
pose m := m_val T R N'.
rewrite qq.
have ->: (T + m * N) %% R =  (T %% R + m * N %% R) %% R. smt(@Int @IntDiv).
    auto. 
qed.    


lemma opt_tval_eq2 T R N' N : 2 * N < R =>
 (o_t_val T R N' N) %% R = o_t_val T R N' N.
rewrite - opt_tval_eq. progress.
have : 0 <= (t_val T R N' N) < 2 * N.
 apply aux6. admit. admit. admit.
smt.
qed.

lemma opt_tval_eq3 T R N' N : 2 * N < R =>
 (o2_t_val T R N' N)  = o_t_val T R N' N.
progress. rewrite - opt_tval_eq2. auto.
smt.
qed. 

lemma opt_redc_eq3 T R N' N : 2 * N < R =>
 (o2_redc T R N' N)  = o_redc T R N' N.
progress.
rewrite /o2_redc /o_redc. 
rewrite opt_tval_eq3. auto.
simplify. 
case (N <= o_t_val T R N' N ). progress.
rewrite - opt_tval_eq. progress.
have : 0 <= (t_val T R N' N) < 2 * N.
 apply aux6. admit. admit. admit. progress.
have : 2 * N < R. admit.
smt.
auto.
qed. 
 


lemma opt_redc_eq T R N' N :
    o_redc T R N' N = redc T R N' N .
rewrite /o_redc /redc. simplify.
have ->: t_val T R N' N = o_t_val T R N' N.
rewrite opt_tval_eq. auto.    
 auto.
qed.    




lemma almost_yul_redc_full_correctness  T Tlo Thi R N' N :
 phoare[ AlmostYul._REDC : arg = (Tlo,Thi,R,N,N')
        ==> res = T * (inv N R) %% N ] = 1%r.
proof. bypr. progress.
have <-: Pr[ OptREDC.main2(T,R,N,N') @&m : res = T * (inv N R) %% N] = 1%r.
have ->: Pr[OptREDC.main2(T, R, N, N') @ &m : res = T * inv N R %% N]
 = Pr[OptREDC.main2(T, R, N, N') @ &m : res = o2_redc T R N' N].
rewrite Pr[mu_eq] . progress.
rewrite opt_redc_eq3. admit.
rewrite -  (redc_fun_correct T R N' N).  admit. admit. admit. admit. admit.
rewrite opt_redc_eq. auto. 
rewrite opt_redc_eq3. admit.
rewrite -  (redc_fun_correct T R N' N).  admit. admit. admit. admit. admit.
rewrite opt_redc_eq. auto.  auto.
byphoare (_: arg = (T,R,N,N') ==> _).
apply maeq6. auto. auto.


byequiv. progress.


transitivity OptREDC._REDC1
 (={arg} ==> ={res})
 (={R,N,N'} ==> ={res}).
smt().  auto.
apply maeq.


transitivity OptREDC._REDC2
 (={arg} ==> ={res})
 (={R,N,N'} ==> ={res}).
smt().  auto.
apply maeq2.


transitivity OptREDC._REDC3
 (={arg} ==> ={res})
 (={R,N,N'} ==> ={res}).
smt().  auto.
apply maeq3.

transitivity OptREDC.main1    
 (Tlo{1} = T{2} %% R{2} /\ Thi{1} = T{2} %/ R{2}
       /\ ={R, N, N'} ==> ={res})
 (={arg} ==> ={res}).
  auto.
admit. auto.

conseq maeq4. admit.
conseq maeq5. smt(). auto.
qed. 
