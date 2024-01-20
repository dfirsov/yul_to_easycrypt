require import AllCore.

require import IntDiv Int.
require import Gcd_props.



module GCDAlgs = {
  proc simplify_t(t:int) = {
      while (!odd t){
        t <- t %/ 2;
      }
      return t;
  }

  proc main3(u : int, v : int) = {
    var t <- 0;
    t <- -v;
    while (t <> 0){     
      t <- div_by2s t;
      (u,v) <- if 0 < t then (t,v) else (u,-t);
      t <- u - v;
    }
    return u;
  }

  proc main4(u : int, v : int) = {
    var t <- 0;
    t <- -v;
    while (t <> 0){     
      t <@ simplify_t(t);
      (u,v) <- if 0 < t then (t,v) else (u,-t);
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



lemma main3_term : phoare [GCDAlgs.main3 : odd u /\ 0 < u /\ 0 < v ==> true ] = 1%r.
proc. unroll 3.
rcondt 3. wp. skip. progress. smt()    .
while (t = u - v /\ !odd t /\ odd u /\ odd v /\ 0 < u /\ 0 < v) (max u v).
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
wp.    skip.
progress.
smt.
    smt. smt. smt. smt. smt.
qed.    



lemma gcd_odd_alg u_in v_in : hoare [ GCDAlgs.main3 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in 
 /\ odd u ==> res = gcd u_in v_in ].
proof.
proc.
unroll 3. rcondt 3. wp. skip. smt.
seq 4 : (gcd u_in v_in = gcd u v /\ odd u /\ odd v
  /\ 0 < u /\ 0 < v ).
wp. skip. progress.
have ->: 0 < div_by2s (-v{hr}) = false. smt(div_by2s1). simplify.
smt.                            
smt.
smt. smt. smt.
seq 1 : ((gcd u_in v_in = gcd t (if 0 < t then v else u) /\ !odd t /\ odd u /\ odd v)  /\  0 < u /\ 0 < v /\ t = u - v).
wp. skip. progress.
rewrite H. 
smt.
smt.
while (gcd u_in v_in =  gcd t (if 0 < t then v else u) /\ !odd t /\ odd u /\ odd v /\  0 <= u /\ 0 <= v /\ t = u - v).
seq 1 : (gcd u_in v_in =gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ t <> 0 /\ 0 <= u /\ 0 <= v /\ t = div_by2s (u - v)).
wp. skip. progress. rewrite H. 
smt.
smt.
smt.
seq 1 : (gcd u_in v_in = gcd t (if 0 < t then v else u) /\ odd t /\ odd u /\ odd v /\ t <> 0
   /\ (u = if 0 < t then t else u) /\ (v = if 0 < t then v else -t) /\ 0 <= u /\ 0 <= v).
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
progress. rewrite H8. simplify. smt. smt.
skip. progress. smt. smt. smt.
qed.


lemma main3_correct_and_terminating u_in v_in : phoare [ GCDAlgs.main3 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in /\ odd u ==> res = gcd u_in v_in ] = 1%r.
phoare split ! 1%r 0%r. smt().
conseq main3_term. smt().
    hoare. simplify.
apply gcd_odd_alg.
qed.    


lemma main3_main4 u_in v_in : equiv [ GCDAlgs.main3 ~ GCDAlgs.main4 : arg{1} = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in
 /\ odd u_in /\ ={arg} ==> ={res} ].
proc.
seq 2 2 : (={t,u,v}).
wp. skip. progress.
(* ecall {2} (simplify_divby2s v{2}). wp. *)
(* skip. progress. smt. *)
while (={t,u,v}). wp.
ecall {2} (simplify_divby2s t{2}). wp.
skip. progress. skip. progress.
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
