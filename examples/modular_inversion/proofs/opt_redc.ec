require import AllCore Int IntDiv.
require import Gcd Gcd_props.

op mul : int -> int -> int.
op add : int -> int -> int.
op sub : int -> int -> int.
op getHighestHalfOfMultiplication: int -> int -> int.

module OptREDC = {

  proc main1(T : int, R : int, N : int, N' : int) = {
    var m, t, r;
    m <- ((T %% R) * N') %% R;
    t <- (T %/ R + (m * N) %/ R);
    t <- if ((T + ((m * N))) %% R < T %% R) then t + 1 else t;
    if (N <= t){
      r <- t - N;
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
    if (N <= t){
      r <- (t - N) %% R;
    }else{
      r <- t;
    }
    return r;
  } 


  
  (*  proc overflowingAdd(augend : int, addend : int, R : int) : int * bool = {   *)
  (*    var sum <- (augend + addend) %% R; *)
  (*    return (sum, sum < augend); *)
  (*  }   *)


  (* proc main(Tlo : int, Thi : int, R : int, N : int, N' : int) = { *)
  (*   var m, hi, lo, s, tmp : int; *)
  (*   var overflowed : bool; *)

  (*   m <- (Tlo * N') %% R; *)
     
  (*   hi <- (Thi + ((m * N) %/ R)); *)
  (*   tmp <- (m * N) %% R; *)
  (*   (lo, overflowed) <@ overflowingAdd(Tlo, tmp, R); *)
  (*   if (overflowed) { *)
  (*     hi <- (hi + 1) %% R; *)
  (*   } *)

  (*   s <- hi; *)

  (*   if (N < hi){ *)
  (*     s <- hi - N; *)
  (*   } *)
    
  (* }  *)

}.


op o_m_val T R N' = ((T %% R) * N') %% R.
op o_t_val' T R N' N = (T %/ R + ((o_m_val T R N') * N) %/ R).
op o_t_val T R N' N = o_t_val' T R N' N + if ((T + (((o_m_val T R N') * N))) %% R < T %% R) then 1 else 0.
op o_redc T R N' N = let t = o_t_val T R N' N in if N <= t then t - N else t.

op o2_t_val' T R N' N = (T %/ R + ((o_m_val T R N') * N) %/ R) %% R.
op o2_t_val T R N' N = (o_t_val' T R N' N + if ((T + (((o_m_val T R N') * N))) %% R < T %% R) then 1 else 0) %% R.

op o2_redc T R N' N = let t = o2_t_val T R N' N in if N <= t then (t - N) %% R else t.


    
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


