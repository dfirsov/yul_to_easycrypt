require import AllCore.

require import IntDiv Int.

require import Gcd_props.

module ExtGCD = {

  proc simplify_ts(t1:int,t2:int,t3: int,u:int,v:int) = {
      while (even(t3)){
        if (even(t1) /\ even(t2)){
          (t1,t2,t3) <- (t1 %/2, t2 %/2, t3 %/2);
        }else{
          (t1,t2,t3) <- ((t1+v) %/2, (t2-u) %/2, t3 %/2);
        }
      }
      return (t1,t2,t3);
  }

  proc opt_simplify_ts(t1:int,t2:int,t3: int,u:int,v:int) = {
      while (even t3){
        if (even t2){
          (t1,t2,t3) <- (t1 %/2, t2 %/2, t3 %/2);
        }else{
          (t1,t2,t3) <- ((t1+v) %/2, (t2-u) %/2, t3 %/2);
        }
      }
      return (t1,t2,t3);
  }
  

  proc main(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;
    var k <- 0;
    (u1,u2,u3,v1,v2,v3,t1,t2,t3) <- (0,0,0,0,0,0,0,0,0);

    (u1,u2,u3) <- (1,0,u);
    (v1,v2,v3) <- (v,1-u,v);
    (t1,t2,t3) <- if (odd u) then  (0,-1,-v) else (1,0,u);

    while (t3 <> 0){
      (t1,t2,t3) <@ simplify_ts(t1, t2, t3, u, v);
      if (0 < t3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
      (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);
      if (t1 < 0){
         (t1, t2) <- (t1+v, t2-u);
       }
     }
      return (u1, u2, u3);
  }


  proc main_unfold1(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;
    var k <- 0;
    (u1,u2,u3,v1,v2,v3,t1,t2,t3) <- (0,0,0,0,0,0,0,0,0);
    (u1,u2,u3) <- (1,0,u);
    (v1,v2,v3) <- (v,1-u,v);
    (t1,t2,t3) <- if (odd u) then  (0,-1,-v) else (1,0,u);
    (t1,t2,t3) <@ simplify_ts(t1, t2, t3, u, v);
    if (0 < t3){
      (u1, u2, u3) <- (t1, t2, t3);
    }else{
      (v1, v2, v3) <- (v-t1, -u-t2, -t3);
    }
    (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);
    if (t1 < 0){
       (t1, t2) <- (t1+v, t2-u);
     }
    while (t3 <> 0){
      (t1,t2,t3) <@ simplify_ts(t1, t2, t3, u, v);
      if (0 < t3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
      (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);
      if (t1 < 0){
         (t1, t2) <- (t1+v, t2-u);
       }
     }
      return (u1, u2, u3);
  }


  (* assumption: u is odd *)
  proc main2(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;
    var k <- 0;
    (u1,u2,u3,v1,v2,v3,t1,t2,t3) <- (0,0,0,0,0,0,0,0,0);
    (u1,u2,u3) <- (1,0, u);
    (v1,v2,v3) <- (v,(1-u), v);
    (t1,t2,t3) <- (0,-1,-v);

    while (t3 <> 0){
      (t1,t2,t3) <@ opt_simplify_ts(t1, t2, t3, u, v);
      if (0 < t3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
      (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);
     }

      return (u1, u2, u3);
  }
  
  
}.


lemma gcd_main_unfold_eq : equiv [ ExtGCD.main ~ ExtGCD.main_unfold1 : ={arg} /\ u{1} <> 0 /\ v{1} <> 0 
  ==> ={res} ].
proof. proc.
unroll {1} 6.
seq 5 5 : (={u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3, k} /\ t3{1} <> 0).
wp. skip. progress. smt.
rcondt {1} 1. progress. sim.
qed.


lemma gcd_t_simp t1_in t2_in t3_in  u1 u2 u3 v1 v2 v3 u_in v_in : 
  hoare [ ExtGCD.simplify_ts : arg = (t1_in,t2_in,t3_in,u_in,v_in) /\ (odd u_in \/ odd v_in) /\ t3 <> 0
 /\ (u_in * t1 + v_in * t2 = t3
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) 
  ==> (u_in * res.`1 + v_in * res.`2 = res.`3) /\ res.`3 <> 0 ].
proc.
simplify.
while((odd u_in \/ odd v_in)
 /\ (u_in * t1 + v_in * t2 = t3
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) /\ u = u_in /\ v = v_in /\ t3 <> 0 ).
case (even t1 /\ even t2).
 rcondt 1.
 skip. progress.
 wp. skip. progress.
 have ->: (u{hr} * t1{hr} + v{hr} * t2{hr}) %/ 2 =
  (u{hr} * t1{hr} %/ 2 + v{hr} * t2{hr} %/ 2).
 smt(@Int).
 timeout 15. smt(@Int). smt.
 rcondf 1. skip. progress.
  wp. skip. progress. 
  have t1v : even (t1{hr} + v{hr}). smt.
  have t2u : even (t2{hr} - u{hr}). smt.
  have ->: u{hr} * ((t1{hr} + v{hr}) %/ 2) = (u{hr} * (t1{hr} + v{hr})) %/ 2.
  timeout 15. smt(@Int).
  have ->: v{hr} * ((t2{hr} - u{hr}) %/ 2) = v{hr} * (t2{hr} - u{hr}) %/ 2.
  timeout 15. smt(@Int).
  timeout 15. smt(@Int).
  smt.
skip. progress.
qed.   


lemma opt_gcd_t_simp t1_in t2_in t3_in  u1 u2 u3 v1 v2 v3 u_in v_in : 
  hoare [ ExtGCD.opt_simplify_ts : arg = (t1_in,t2_in,t3_in,u_in,v_in) /\ odd u /\ t3 <> 0
 /\ (u_in * t1 + v_in * t2 = t3
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) 
  ==> 
   (u_in * res.`1 + v_in * res.`2 = res.`3 /\ res.`3 <> 0  /\ res.`3 < 0 = t3_in < 0) ]. 
proc.
simplify.
while(odd u
 /\ (u_in * t1 + v_in * t2 = t3
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) /\ u = u_in /\ v = v_in /\ t3 <> 0 /\ t3 < 0 = t3_in < 0).
case (even t2).
 rcondt 1.
 skip. progress.
wp.  skip. progress.
have : even(v{hr} * t2{hr}). smt.
progress.
 have : even (u{hr} * t1{hr}). smt.
 progress.
  have : even t1{hr}. smt. progress.
 have ->: (u{hr} * t1{hr} + v{hr} * t2{hr}) %/ 2 =
  (u{hr} * t1{hr} %/ 2 + v{hr} * t2{hr} %/ 2).
 smt(@Int).
 timeout 15. smt(@Int). smt. smt.
 rcondf 1. skip. progress.
  wp. skip. progress.
  have t1v : even (t1{hr} + v{hr}). smt.
  have t2u : even (t2{hr} - u{hr}). smt.
  have ->: u{hr} * ((t1{hr} + v{hr}) %/ 2) = (u{hr} * (t1{hr} + v{hr})) %/ 2.
  timeout 15. smt(@Int).
  have ->: v{hr} * ((t2{hr} - u{hr}) %/ 2) = v{hr} * (t2{hr} - u{hr}) %/ 2.
  timeout 15. smt(@Int).
  timeout 15. smt(@Int).
  smt. smt.
skip. progress.
qed.



lemma gcd_t_simp_eq t1_in t2_in t3_in  u1 u2 u3 v1 v2 v3 u_in v_in : 
  equiv [ ExtGCD.opt_simplify_ts ~ ExtGCD.opt_simplify_ts : ={arg} /\ arg{1} = (t1_in,t2_in,t3_in,u_in,v_in){1} /\ odd u{1} /\ t3{1} <> 0
 /\ (u_in * t1 + v_in * t2 = t3
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3){1} 
  ==> ={res} /\
   (u_in * res.`1 + v_in * res.`2 = res.`3 /\ res.`3 <> 0  /\ res.`3 < 0 = t3_in < 0){1} ].  admitted.


lemma gcd_t_simp_eq2 t3_in  : 
  equiv [ ExtGCD.opt_simplify_ts ~ ExtGCD.opt_simplify_ts : t3_in = t3{1} /\ ={t1,t2,u,v} /\ `|t3{1}| = t3{2}
  ==> res{1}.`1 = res{2}.`1 /\ res{1}.`2 = res{2}.`2 /\ `|res{1}.`3| = res{2}.`3
     /\ 0 < t3_in = 0 < res{1}.`3  ].  admitted.



lemma main2_bezout u_in v_in :
 hoare [ ExtGCD.main2 : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in 
         /\ odd u_in ==> u_in * res.`1 + v_in * res.`2 = res.`3 ].
proof.
proc.
seq 5 : ((u_in * t1 + v_in * t2 = t3)
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3
 /\ u = u_in /\ v = v_in /\ odd u).
wp. skip.  progress.
smt. smt. 
while (((u_in * t1 + v_in * t2 = t3)
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) /\ u = u_in /\ v = v_in /\ odd u).
seq 1 : (#pre).
exists* (t1, t2, t3,  u1, u2, u3, v1, v2, v3).
elim*. progress.
call (opt_gcd_t_simp f.`1 f.`2 f.`3 f.`4 f.`5 f.`6 f.`7 f.`8 f.`9 u_in v_in).
skip. progress.  (* smt. *)
seq 2 : (((u_in * t1 + v_in * t2 = t3)
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) /\ u = u_in /\ v = v_in /\ odd u).
wp. skip. simplify.
move => &hr.
move => q.
case (0 < t3{hr}).
progress.
smt.
smt.
smt.
smt.
smt.
smt. 
smt.
wp. skip. progress. 
skip. progress.
qed.
  


lemma ext_gcd_bezout u_in v_in :
  hoare [ ExtGCD.main : arg = (u_in, v_in) /\ 0 < u_in /\ 0 < v_in /\
     (odd u_in \/ odd v_in)  ==> u_in * res.`1 + v_in * res.`2 = res.`3 ].
proof.
proc.
seq 5 : ((u_in * t1 + v_in * t2 = t3)
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3
 /\ u = u_in /\ v = v_in
 /\ (odd u_in \/ odd v_in)).
wp. skip.  progress.
smt. smt.
while (((u_in * t1 + v_in * t2 = t3)
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) /\ u = u_in /\ v = v_in /\ (odd u_in \/ odd v_in)).
seq 1 : (#pre).
exists* (t1, t2, t3,  u1, u2, u3, v1, v2, v3).
elim*. progress.
call (gcd_t_simp f.`1 f.`2 f.`3 f.`4 f.`5 f.`6 f.`7 f.`8 f.`9 u_in v_in).
skip. progress. 
seq 2 : (((u_in * t1 + v_in * t2 = t3)
 /\ u_in * u1 + v_in * u2 = u3
 /\ u_in * v1 + v_in * v2 = v3) /\ u = u_in /\ v = v_in /\ (odd u_in \/ odd v_in)).
wp. skip. simplify.
move => &hr.
move => q.
case (0 < t3{hr}).
progress.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
wp. skip. progress. smt. 
skip. progress.
qed.

