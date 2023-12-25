require import AllCore IntDiv Int.
require import Ext_gcd Gcd_props.

module OptExtGcd = {

  proc simplify_ts(t2:int,t3: int,u:int,v:int) = {
      while (even t3){
        if (even t2){
          (t2,t3) <- (t2 %/2, t3 %/2);
        }else{
          (t2,t3) <- ((t2-u) %/2, t3 %/2);
        }
      }
      return (t2,t3);
  }

  (* assumption: u odd *)
  proc main1(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;

    (u1,u2,u3) <- (1,0, u);
    (v1,v2,v3) <- (v,(1-u), v);
    (t1,t2,t3) <- (0,-1,-v);

    (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
      if (0 < t3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
    (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);

    while (t3 <> 0){
      (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
      if (0 < t3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
      (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);
     }

      return (u1, u2, u3);
  }


  proc main2(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;

    (u1,u2,u3) <- (1,0, u);
    (v1,v2,v3) <- (v,(1-u), v);
    (t1,t2,t3) <- (0,-1,-v);

    (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
    (v1, v2, v3) <- (v-t1, -u-t2, -t3);

    (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);

    while (t3 <> 0){
      (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
      if (v3 < u3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
      (t1, t2, t3) <- (u1-v1, u2-v2, u3 - v3);

     }
      return (u1, u2, u3);
  }

  proc main3(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;

    (u1,u2,u3) <- (1,0, u);
    (v1,v2,v3) <- (v,(1-u), v);
    (t1,t2,t3) <- (0,-1,v);

    (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
    (v1, v2, v3) <- (v-t1, -u-t2, t3);

    (t1, t2, t3) <- (u1-v1, u2-v2, `|u3-v3|);

    while (t3 <> 0){
      (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
      if (v3 < u3){

        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, t3);
      }

      (t1, t2, t3) <- (u1-v1, u2-v2, `|u3 - v3|);

     }
      return (u1, u2, u3);
  }

    proc main4(u : int, v : int) = {
      var u2,u3,v2,v3,t2,t3;

      (u2,u3) <- (0, u);
      (v2,v3) <- (1-u, v);
      (t2,t3) <- (-1, v);

      (t2,t3) <@ simplify_ts(t2, t3, u, v);
      (v2, v3) <- (-u-t2, t3);

      (t2, t3) <- (u2-v2, `|u3-v3|);

      while (t3 <> 0){
        (t2,t3) <@ simplify_ts(t2, t3, u, v);
        if (v3 < u3){
          (u2, u3) <- (t2, t3);
        }else{
          (v2, v3) <- (-u-t2, t3);
        }

        (t2, t3) <- (u2-v2, `|u3 - v3|);

       }
      return (u2, u3);
  }

    proc main5(u : int, v : int) = {
      var u2,u3,v2,v3,t2,t3;
      (v2,v3) <- ((1-u), v);
      (u2,u3) <- (0, u);
      (t2,t3) <- (-1, v);

      (t2,t3) <@ simplify_ts(t2, t3, u, v);
      (v2, v3) <- (-u-t2, t3);

      (t2, t3) <- (u2-v2, `|u3-v3|);

      while (t3 <> 0){
        (t2,t3) <@ simplify_ts(t2, t3, u, v);
        if (v3 < u3){
          (u2, u3) <- (t2, t3);
          (t2, t3) <- (u2-v2, `|u3 - v3|);          
        }else{
          (v2, v3) <- (-u-t2, t3);
          (t2, t3) <- (u2-v2, `|u3 - v3|);          
        }
       }
      return (u2, u3);
  }
  
}.


lemma opt_4 : equiv[ OptExtGcd.main4 ~ OptExtGcd.main5 : ={arg} /\ 0 < u{1} /\ 0 < v{1}
       ==>  ={res}].
proc.
wp. simplify.
sp.
while (={t2,t3,u2,u3,v2,v3,u,v}). wp.
inline*. sp. wp. 
while (={t20,t30,u0,v0}).
wp. skip. progress. skip. progress. wp.
inline*. sp. wp. 
while (={t20,t30,u0,v0}).
wp. skip. progress. skip. progress.
qed.


lemma opt_3 : equiv[ OptExtGcd.main3 ~ OptExtGcd.main4 : ={arg} /\ 0 < u{1} /\ 0 < v{1}
       ==>  res{1}.`2 = res{2}.`1 /\  res{1}.`3 = res{2}.`2].
proc.
wp. simplify. sp.
while (={t2,t3,u2,u3,v2,v3,u,v}). wp.
inline*. sp. wp. 
while (={t20,t30,u0,v0}).
wp. skip. progress. skip. progress.
wp. inline*. sp. wp. 
while (={t20,t30,u0,v0}).
wp. skip. progress. skip. progress.
qed.


lemma opt_2 : equiv[ OptExtGcd.main2 ~ OptExtGcd.main3 : ={arg} /\ 0 < u{1} /\ 0 < v{1} ==> ={res} ].
proc.
seq 3 3 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0).
wp. simplify.  skip. progress. smt. smt.
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0). admit.
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0).
wp. skip. progress. smt.
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} = u3{1} - v3{1}).
wp. simplify.  progress.  
while (={u,v,u1,u2,u3,v1,v2,v3,t1,t2} /\ t3{1} = u3{1} - v3{1} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1}).
wp.
exists* t3{1}. elim*. progress.
call (gcd_t_simp_eq2 t3_L). simplify.
skip. progress. 
smt. smt. smt.  smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. 
skip. progress. smt. smt.
qed.


lemma opt_1 : equiv[ ExtGCD.main2 ~ OptExtGcd.main1 : ={arg} /\ 0 < u{1} /\ 0 < v{1} ==> ={res} ].
proc. sp. simplify.
unroll {1} 1.
rcondt {1} 1. progress. skip. smt().
sim. 
qed.
