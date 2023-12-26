require import AllCore.

require import IntDiv Int.
require import Gcd_props.

op div_by2s (i : int) : int.
axiom div_by2s1 u : 0 < u = 0 < (div_by2s u).
axiom div_by2s2 u v : odd v => gcd (div_by2s u) v = gcd u v.
axiom div_by2s3 u : odd (div_by2s u).
axiom div_by2s4 u : 0 < u => even u =>  (div_by2s u) < u.
axiom div_by2s5 u : u < 0 => even u =>  u < (div_by2s u).
axiom div_by2s6 u : even u =>  div_by2s (u %/ 2) = div_by2s u.
axiom div_by2s7 u : odd u =>  div_by2s u = u.


module GCDAlgs = {

  proc simplify_t(t:int) = {
      while (even t){
        t <- t %/ 2;
      }
      return t;
  }

  proc main1(u : int, v : int) = {
    var k, t;
    (k,t) <- (0,0);
    k <- 0;
    while (even(u) /\ even(v)) {
       k <- k + 1;
       u <- u %/ 2;
       v <- v %/ 2;
    }
    t <- if (odd u) then (-v) else u;
    t <- div_by2s t; 
    (u,v) <- if 0 < t then (t,v) else (u,-t);
    t <- u - v;
    while (t <> 0){     
      t <- div_by2s t;
      (u,v) <- if 0 < t then (t,v) else (u,-t);
      t <- u - v;
    }
    return u*2^k;
  }


  proc main2(u : int, v : int) = {
    var k, t;
    (k,t) <- (0,0);    
    k <- 0;
    while (even(u) /\ even(v)) {
       k <- k + 1;
       u <- u %/ 2;
       v <- v %/ 2;
    }
    t <- if (odd u) then (-v) else u;
    t <- div_by2s t; 
    (u,v) <- if 0 < t then (t,v) else (u,-t);
    t <- u - v;    
    while (t <> 0){     
      t <- div_by2s t;
      (u,v) <- if v < u then (t,v) else (u,-t);
      t <- u - v;
    }
    return u*2^k;
  }

  proc main3(u : int, v : int) = {
    var t <- 0;
    (u,v) <- (u, div_by2s v);
    t <- u - v;
    while (t <> 0){     
      t <- div_by2s t;
      (u,v) <- if v < u then (t,v) else (u,-t);
      t <- u - v;
    }
    return u;
  }


  proc main4(u : int, v : int) = {
    var t <- 0;
    v <@ simplify_t(v);
    t <- u - v;
    while (t <> 0){     
      t <@ simplify_t(t);
      (u,v) <- if v < u then (t,v) else (u,-t);
      t <- u - v;
    }
    return u;
  }
  
}.


lemma simplify_divby2s t_in :
   phoare [ GCDAlgs.simplify_t : t = t_in /\ t <> 0 ==> res = div_by2s t_in ] = 1%r.
proc.
while (div_by2s t = div_by2s t_in /\ t <> 0) `|t|.
progress.
wp. skip. progress. smt. smt.
 case (t{hr} < 0). progress.
    have ->: `|t{hr} %/ 2| = - (t{hr} %/ 2). smt.
    have ->: `|t{hr}| = - (t{hr}). smt.
    smt.
    progress.
    have ->: `|t{hr} %/ 2| =  (t{hr} %/ 2). smt.
    have ->: `|t{hr}| =  (t{hr}). smt.
    smt.    
skip. progress. smt. smt. 
qed.    


lemma main3_main4 u_in v_in : equiv [ GCDAlgs.main3 ~ GCDAlgs.main4 : arg{1} = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in
 /\ odd u_in /\ ={arg} ==> ={res} ].
proc.
seq 3 3 : (={t,u,v}).
wp.
ecall {2} (simplify_divby2s v{2}). wp.
skip. progress. smt.
while (={t,u,v}). wp.
ecall {2} (simplify_divby2s t{2}). wp.
skip. progress. skip. progress.
qed.    


lemma main3_term : phoare [GCDAlgs.main3 : odd u /\ 0 < u /\ 0 < v ==> true ] = 1%r.
proc. sp.
while (t = u - v /\ even t /\ odd u /\ odd v /\ 0 < u /\ 0 < v) (max u v).
progress.    
wp. skip. progress.
case (v{hr} < u{hr}). progress.
    smt.
    smt.
    smt.
    smt. smt. smt.
pose x := div_by2s (u{hr} - v{hr}).     
case (v{hr} < u{hr}). progress.
have f1 : 0 < x < u{hr} - v{hr}. split. smt.  smt. 
smt.
    move => q.
 case (v{hr} <= x).
   move => mh.
      smt.
progress.
have f1 : 0 < -x < v{hr} - u{hr}. split. smt.    
progress.
     have : u{hr} - v{hr} < x. smt.
    smt.
    smt.    
    skip.
progress.
smt.
    smt. smt. smt.
qed.    


    
    
lemma gcd_alg_eq : equiv [ GCDAlgs.main1 ~ GCDAlgs.main2  : ={arg} 
  ==> ={res} ].
proof. proc.
sp.
while (={u,v,k,t} /\ t{1} = u{1} - v{1}).
wp. skip. progress;smt.
wp. while (={u,v,k,t} ).
wp. skip. progress.
skip. progress.
qed.


lemma gcd_alg u_in v_in : hoare [ GCDAlgs.main1 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in 
  ==> res = gcd u_in v_in ].
proof.
proc.
seq 3 : (gcd u_in v_in = 2^k  * gcd u v /\ (odd u \/ odd v) /\ 0 < u /\ 0 < v /\ 0 <= k).
sp.
while (gcd u_in v_in = 2^k  * gcd u v /\ 0 < u /\ 0 < v /\ 0 <= k).
wp.
skip. progress.
rewrite H.
rewrite gcd1. auto. auto.
have ->: 2 ^ (k{hr} + 1) = 2 ^ k{hr} * 2. smt.
smt(@Int).
smt(@Int). smt(@Int).
smt(). skip. progress. smt(@Int). smt().
seq 1 : (gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ (odd u \/ odd v)
 /\ t = (if odd u then -v else u) /\ 0 < u /\ 0 < v).
wp. skip. progress.
case (odd u{hr}).
have -> : 0 < -v{hr} = false. smt. simplify.
rewrite H.
progress. congr.
smt.                            (* prop of gcd *)
progress. rewrite H. congr. rewrite H1. simplify. auto.
seq 1 : ((if odd u then div_by2s (-v) else div_by2s u) = t /\ gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ (odd u \/ odd v)
 /\  odd t /\ (0 < t = !odd u) /\ 0 < u /\ 0 < v ).
wp. skip. progress.
smt().
rewrite H.
congr.
case (odd u{hr}).
have ->: 0 < -v{hr}  = false. smt(). simplify.
have ->: 0 < div_by2s (-v{hr}) = false. smt(div_by2s1).  simplify.
move => q.
rewrite div_by2s2. auto. 
smt.
progress.
rewrite H1. simplify.
have ->: 0 < div_by2s (u{hr}) = true. smt(div_by2s1). simplify. smt.
apply div_by2s3.
case (odd u{hr}). simplify.
smt.
smt.
seq 1 : (gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ (u = if 0 < t then t else u) /\ (v = if 0 < t then v else -t) /\ 0 < u /\ 0 < v ).
wp.
skip.
progress.
rewrite H.
congr.
smt().
case (0 < t{hr}). smt().
progress.
rewrite  H2.
case (odd u{hr}). simplify. auto.
simplify. smt.
rewrite H2.
case (odd u{hr}). simplify. auto.
smt.  simplify. smt.
smt().
smt().
smt.
smt.
seq 1 : ((gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ even t /\ odd u /\ odd v)  /\  0 < u /\ 0 < v).
wp. skip. progress.
rewrite H. congr.
case (0 < t{hr}).
rewrite H3 H4.
progress. rewrite H7. simplify.
case (0 < t{hr} - v{hr}).
progress. apply gcd6.
progress. smt.
rewrite H4.
progress.
rewrite H7. simplify.
  case (0 < u{hr} + t{hr}).
progress.
smt.
smt.
smt(odd_even).
while (gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ even t /\ odd u /\ odd v /\  0 <= u /\ 0 <= v).
seq 1 : (gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ t <> 0 /\ 0 <= u /\ 0 <= v).
wp. skip. progress. rewrite H. congr.
smt.
smt.
smt.
seq 1 : (gcd u_in v_in = 2^k  * gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ t <> 0 /\ (u = if 0 < t then t else u) /\ (v = if 0 < t then v else -t) /\ 0 <= u /\ 0 <= v) .
wp. skip. progress.
rewrite H. congr.
case (0 < t{hr}). auto.
auto.
smt(). smt.
smt().
smt().
smt.
smt.
wp. skip. progress.
rewrite H. congr.
case (0 < t{hr}). auto.
rewrite H4.
progress. rewrite H8. simplify.
rewrite gcd6. smt.
rewrite H5.
progress. rewrite H8. simplify. smt.
smt.
skip. progress.
smt.
smt.
smt.
qed.



lemma gcd_odd_alg u_in v_in : hoare [ GCDAlgs.main3 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in 
 /\ odd u ==> res = gcd u_in v_in ].
proof.
proc.
seq 2 : (gcd u_in v_in = gcd u v /\ odd u /\ odd v
  /\ 0 < u /\ 0 < v ).
wp. skip. progress.
smt.                            (* prop of gcd *)
smt.
smt.
seq 1 : ((gcd u_in v_in = gcd t (if 0 < t then v else u) /\ even t /\ odd u /\ odd v)  /\  0 < u /\ 0 < v /\ t = u - v).
wp. skip. progress.
rewrite H. 
smt.
smt.
while (gcd u_in v_in =  gcd t (if 0 < t then v else u) /\ even t /\ odd u /\ odd v /\  0 <= u /\ 0 <= v /\ t = u - v).
seq 1 : (gcd u_in v_in =gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ t <> 0 /\ 0 <= u /\ 0 <= v /\ t = div_by2s (u - v)).
wp. skip. progress. rewrite H. 
smt.
smt.
smt.
seq 1 : (gcd u_in v_in = gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ t <> 0 /\ (u = if 0 < t then t else u) /\ (v = if 0 < t then v else -t) /\ 0 <= u /\ 0 <= v ) .
wp. skip. progress.
rewrite H. 
case (0 < t{hr}). auto.
auto. smt. smt. smt. smt. smt. smt. smt. smt.  
wp. skip. progress.
rewrite H. 
case (0 < t{hr}). auto.
rewrite H4.
progress. rewrite H8. simplify.
rewrite gcd6. smt.
rewrite H5.
progress. rewrite H8. simplify. smt.
smt.
skip. progress.
smt.
smt.
smt.
qed.


lemma main3_correct_and_terminating u_in v_in : phoare [ GCDAlgs.main3 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in /\ odd u ==> res = gcd u_in v_in ] = 1%r.
phoare split ! 1%r 0%r. smt().
conseq main3_term. smt().
    hoare. simplify.
apply gcd_odd_alg.
qed.    


lemma main4_correct_and_terminating u_in v_in : phoare [ GCDAlgs.main4 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in /\ odd u ==> res = gcd u_in v_in ] = 1%r.
bypr.
progress.
 have <-: Pr[GCDAlgs.main3(u{m}, v{m}) @ &m : res = gcd u_in v_in] = 1%r.
 byphoare (_: arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in /\ odd u  ==> _).
 apply main3_correct_and_terminating. smt(). auto.
byequiv. symmetry.
conseq (main3_main4 u_in v_in). smt(). smt(). auto. auto.
qed.    

