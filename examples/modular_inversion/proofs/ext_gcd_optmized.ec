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

  proc simplify_ts_pos(t2:int,t3: int,u:int,v:int) = {
      while (even t3){
        if (even t2){
          (t2,t3) <- (t2 %/2, t3 %/2);
        }else{
          (t2,t3) <- ((t2+u) %/2, t3 %/2);
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

    (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, v, u, v);
    (v1, v2, v3) <- (v-t1, -u-t2, t3);
    (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);

    while (t3 <> 0){
      (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, t3, u, v);
      if (v3 < u3){
        (u1, u2, u3) <- (t1, t2, t3);
      }else{
        (v1, v2, v3) <- (v-t1, -u-t2, -t3);
      }
      (t1, t2, t3) <- (u1-v1, u2-v2, u3-v3);

     }
      return (u1, u2, u3);
  }

  proc main3(u : int, v : int) = {
    var u1,u2,u3,v1,v2,v3,t1,t2,t3;

    (u1,u2,u3) <- (1,0, u);
    (v1,v2,v3) <- (v,(1-u), v);
    (t1,t2,t3) <- (0,-1,v);

    (t1,t2,t3) <@ ExtGCD.opt_simplify_ts(t1, t2, v, u, v);
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

      (t2,t3) <@ simplify_ts(t2, v, u, v);
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

      (u2,u3) <- (0, u);
      (v2,v3) <- (1-u, v);
      (t2,t3) <- (-1, v);

      (t2,t3) <@ simplify_ts(t2, v, u, v);
      (v2, v3) <- (-u-t2, t3);

      (t2, t3) <- (u2-v2, `|u3-v3|);

      while (t3 <> 0){
        (t2,t3) <@ simplify_ts(t2, t3, u, v);
        if (v3 < u3){
          (u2, u3) <- (t2, t3);
        }else{
          (v2, v3) <- (-u-t2, t3);
        }

        t2 <- u2 - v2;
        if (v3 < u3){
          t3 <- u3 - v3;
        }else{
          t3 <- v3 - u3;
        }

       }
      return (u2, u3);
  }  


    proc main6(u : int, v : int) = {
      var u2,u3,v2,v3,t2,t3;

      (u2,u3) <- (0, u);
      (v2,v3) <- (u-1, v);
      (t2,t3) <- (1, v);

      (t2,t3) <@ simplify_ts_pos(t2, v, u, v);
      (v2, v3) <- (u-t2, t3);

      (t2, t3) <- (-v2, `|u3-v3|);

      while (t3 <> 0){
        (t2,t3) <@ simplify_ts_pos(t2, t3, u, v);
        if (v3 < u3){
          (u2, u3) <- (t2, t3);
        }else{
          (v2, v3) <- (u-t2, t3);
        }

        t2 <- u2 - v2;
        if (v3 < u3){
          t3 <- u3 - v3;
        }else{
          t3 <- v3 - u3;
        }

       }
      return (-u2, u3);
  }


    proc main7(u : int, v : int) = {
      var u2,u3,v2,v3,t2,t3;

      (u2,u3) <- (0, u);
      (v2,v3) <- (u-1, v);
      (t2,t3) <- (1, v);

      (t2,t3) <@ simplify_ts_pos(t2, v, u, v);
      (v2, v3) <- (u-t2, t3);

      (t2, t3) <- (u-v2, `|u3-v3|);

      while (t3 <> 0){
        (t2,t3) <@ simplify_ts_pos(t2, t3, u, v);
        if (v3 < u3){
          (u2, u3) <- (t2, t3);
        }else{
          (v2, v3) <- (u-t2, t3);
        }


        if (u2 < v2){
            t2 <- u + (u2 - v2);
        }else{
            t2 <- u2 - v2;          
        }

        if (v3 < u3){
          t3 <- u3 - v3;
        }else{
          t3 <- v3 - u3;
        }

       }
      return (u-u2, u3);
  }      
}.



lemma opt_6_eq_aux m x' y' :  odd m =>
    2 < m
 =>  (2 * x') %% m = (2 * y') %% m
 => x' %% m = y' %% m. 
proof. progress.
have f1 : 0 <= 2 * (x' %% m) <=  2 * m. smt(@Int @IntDiv).
have f2 : 0 <= 2 * (y' %% m) <= 2 * m. smt(@Int @IntDiv).
have g1: (2 * x') %% m = (2 * (x' %% m)) %% m.
smt (@Int @IntDiv).
have g2: (2 * y') %% m = (2 * (y' %% m)) %% m.
smt (@Int @IntDiv).
have g3 : (2 * (x' %% m)) %% m = (2* (y' %% m)) %% m.
smt (@Int @IntDiv).
case (( 2 * (x' %% m)) < m).
case (( 2* (y' %% m)) < m).
progress.
have g4 : (2 * (x' %% m))  = (2* (y' %% m)) .
smt (@Int @IntDiv).
smt.
progress.
have o : m <= 2 * (y' %% m). smt(). clear H1.
have o2 :  2 * y' %% m =  (2 * (y' %% m) - m) . smt (@Int @IntDiv).
have : odd (2 * (y' %% m) - m). smt.
have : even  (2 * (y' %% m) - m). rewrite - o2 g2 -g3.
 have ->: 2 * (x' %% m) %% m = 2 * (x' %% m). smt.
smt.
progress. smt.
case (( 2* (y' %% m)) < m).
progress.
have o : m <= 2 * (x' %% m). smt(). 
have o2 :  2 * x' %% m =  (2 * (x' %% m) - m) . smt (@Int @IntDiv).
have : odd (2 * (x' %% m) - m). smt.
have : even  (2 * (x' %% m) - m).  rewrite  - o2  g1 g3.
 have ->: 2 * (y' %% m) %% m = 2 * (y' %% m). timeout 10. smt.
smt.
progress. smt.
progress.
have o1 : m <= 2 * (x' %% m). smt(). 
have o2 : m <= 2 * (y' %% m). smt(). 
have o3 :  2 * x' %% m =  (2 * (x' %% m) - m) . smt (@Int @IntDiv).
have o4 :  2 * y' %% m =  (2 * (y' %% m) - m) . smt (@Int @IntDiv).
smt.
qed.


lemma opt_6_eq u_in :
     equiv [ OptExtGcd.simplify_ts_pos ~ OptExtGcd.simplify_ts_pos :  odd u{1} /\ 2 < u{1} /\
      t2{1} %% u{1} = t2{2} %% u{1} /\ ={t3,u,v} /\ u{1} = u_in ==> res{1}.`1 %% u_in = res{2}.`1 %% u_in /\ res{1}.`2 = res{2}.`2 ].
proc. simplify.
while (t2{1} %% u{1} = t2{2} %% u{1} /\ ={t3, u, v} /\ odd u{1} /\ u{1} = u_in /\ 2 < u{1}).
wp. skip. progress.
apply opt_6_eq_aux. auto.  auto.
    have ->: 2 * (t2{1} %/ 2) = t2{1}. smt(@Int @IntDiv).
    have ->: 2 * (t2{2} %/ 2) = t2{2}. smt(@Int @IntDiv).     auto.
apply opt_6_eq_aux. auto. auto.
have ->: 2 * ((t2{1} + u{2}) %/ 2) = ((t2{1} + u{2}) ).
    smt(@Int @IntDiv).
have ->: (t2{1} + u{2}) %% u{2} = t2{1} %% u{2}. smt(@Int @IntDiv).
have ->: 2 * (t2{2} %/ 2) = t2{2}. smt(@Int @IntDiv).    
smt().
apply opt_6_eq_aux. auto. auto.    
have ->: 2 * (t2{1} %/ 2) = t2{1}. smt(@Int @IntDiv).
have ->: 2 * ((t2{2} + u{2}) %/ 2) = (t2{2} + u{2}). smt(@Int @IntDiv).
smt(@Int @IntDiv).    
apply opt_6_eq_aux. auto. auto.    
have ->: 2 * ((t2{2} + u{2}) %/ 2) = (t2{2} + u{2}). smt(@Int @IntDiv).
have ->: 2 * ((t2{1} + u{2}) %/ 2) = ((t2{1} + u{2}) ). smt(@Int @IntDiv).
smt(@Int @IntDiv).    
skip.
progress.
qed.


lemma opt_6 u_in : equiv[ OptExtGcd.main6 ~ OptExtGcd.main7
    : ={arg} /\ u{1} = u_in /\ odd u_in /\ 2 < u_in ==> res{1}.`1 %% u_in = res{2}.`1 %% u_in /\ res{1}.`2 = res{2}.`2 ].
proc.
seq 3 3 : (={u,v,u3,v3,t3} /\ u{1} = u_in
     /\ t2{1} %% u{1} = t2{2} %% u{1} 
     /\ u2{1} %% u{1} = u2{2} %% u{1}
     /\ v2{1} %% u{1} = v2{2} %% u{2}
     /\ odd u_in /\ 2 < u_in).
wp. skip. progress.
seq 1 1 : (={u,v,u3,v3,t3} /\ u{1} = u_in
     /\ t2{1} %% u{1} = t2{2} %% u{1} 
     /\ u2{1} %% u{1} = u2{2} %% u{1}
     /\ v2{1} %% u{1} = v2{2} %% u{2}
     /\ odd u_in /\ 2 < u_in).
ecall (opt_6_eq u{1}). skip. progress. 
seq 2 2 : (={u,v,u3,v3,t3} /\ u{1} = u_in
     /\ t2{1} %% u{1} = t2{2} %% u{1} 
     /\ u2{1} %% u{1} = u2{2} %% u{1}
     /\ v2{1} %% u{1} = v2{2} %% u{2}
     /\ odd u_in /\ 2 < u_in).
wp. skip. progress.  smt(@Int @IntDiv). smt(@Int @IntDiv).
while (={u,v,u3,v3,t3} /\ u{1} = u_in
     /\ t2{1} %% u{1} = t2{2} %% u{1} 
     /\ u2{1} %% u{1} = u2{2} %% u{1}
     /\ v2{1} %% u{1} = v2{2} %% u{2}
     /\ odd u_in /\ 2 < u_in).
seq 1 1 : (={u,v,u3,v3,t3} /\ u{1} = u_in
     /\ t2{1} %% u{1} = t2{2} %% u{1} 
     /\ u2{1} %% u{1} = u2{2} %% u{1}
     /\ v2{1} %% u{1} = v2{2} %% u{2}
     /\ odd u_in /\ 2 < u_in).
ecall (opt_6_eq u{1}). skip. progress. 
wp. skip. progress. timeout 5.
 have ->: ( u{2} + (t2{2} - v2{2})) %% u{2} 
    = (u{2} %% u{2} + (t2{2} - v2{2}) %% u{2} ) %% u{2}. smt(@Int @IntDiv).
    smt(@Int @IntDiv).
 have ->: (u{2} + (t2{2} - v2{2})) %% u{2}
    = (u{2} %% u{2} + (t2{2} - v2{2}) %% u{2} ) %% u{2}. smt(@Int @IntDiv).
    smt(@Int @IntDiv).
smt(@Int @IntDiv).
smt(@Int @IntDiv).
have ->: (u{2} + (u2{2} - (u{2} - t2{2}))) %% u{2} =
    (u{2} %% u{2} + (u2{2} %% u{2} - (u{2} %% u{2} - t2{2} %% u{2}))) %% u{2}.
smt(modzDm @IntDiv).
rewrite - modzDm.
have ->: (- (u{2} - t2{1})) = t2{1} - u{2}.  smt.
have ->: (t2{1} - u{2}) %% u{2} = (t2{1} %% u{2} - u{2} %% u{2}) %% u{2}.
smt(modzDm @IntDiv).    
have ->: u{2} %% u{2} = 0. smt( @IntDiv).  simplify.
rewrite H0.    
smt(@IntDiv).
smt(@Int @IntDiv).
have ->: (u{2} + (u2{2} - (u{2} - t2{2}))) %% u{2} =
    (u{2} %% u{2} + (u2{2} %% u{2} - (u{2} %% u{2} - t2{2} %% u{2}))) %% u{2}.
smt(modzDm @IntDiv).
rewrite - modzDm.
have ->: (- (u{2} - t2{1})) = t2{1} - u{2}.  smt.
have ->: (t2{1} - u{2}) %% u{2} = (t2{1} %% u{2} - u{2} %% u{2}) %% u{2}.
smt(modzDm @IntDiv).    
have ->: u{2} %% u{2} = 0. smt( @IntDiv).  simplify.
rewrite H0.    
smt(@IntDiv).
smt(@Int @IntDiv).
have -> : (u2{1} - (u{2} - t2{1})) %% u{2}
 = (u2{1} %% u{2} - (u{2} %% u{2} - t2{1} %% u{2})) %% u{2}.
rewrite - modzDm.  simplify.
 have ->: - (u{2} - t2{1}) = (t2{1} - u{2}). smt.
have ->: (t2{1} - u{2}) %% u{2} = (t2{1} %% u{2} - u{2} %% u{2}) %% u{2}.
smt(@Int @IntDiv). 
smt(@Int @IntDiv).
have ->: (u2{2} - (u{2} - t2{2})) %% u{2}
  = (u2{2} %% u{2} - (u{2} %% u{2} - t2{2} %% u{2})) %% u{2}.
rewrite - modzDm.  simplify.    
 have ->: - (u{2} - t2{2}) = (t2{2} - u{2}). smt.
have ->: (t2{2} - u{2}) %% u{2} = (t2{2} %% u{2} - u{2} %% u{2}) %% u{2}.    
smt(@Int @IntDiv). 
smt(@Int @IntDiv).
smt(@Int @IntDiv). 
smt(@Int @IntDiv).
have -> : (u2{1} - (u{2} - t2{1})) %% u{2}
 = (u2{1} %% u{2} - (u{2} %% u{2} - t2{1} %% u{2})) %% u{2}.
rewrite - modzDm.  simplify.
 have ->: - (u{2} - t2{1}) = (t2{1} - u{2}). smt.
have ->: (t2{1} - u{2}) %% u{2} = (t2{1} %% u{2} - u{2} %% u{2}) %% u{2}.
smt(@Int @IntDiv). 
smt(@Int @IntDiv).
have ->: (u2{2} - (u{2} - t2{2})) %% u{2}
  = (u2{2} %% u{2} - (u{2} %% u{2} - t2{2} %% u{2})) %% u{2}.
rewrite - modzDm.  simplify.    
 have ->: - (u{2} - t2{2}) = (t2{2} - u{2}). smt.
have ->: (t2{2} - u{2}) %% u{2} = (t2{2} %% u{2} - u{2} %% u{2}) %% u{2}.    
smt(@Int @IntDiv). 
smt(@Int @IntDiv).
smt(@Int @IntDiv). 
smt(@Int @IntDiv).  
skip. progress.
have ->: (u{2} - u2_R) %% u{2} = (u{2} %% u{2}   - u2_R %% u{2}) %% u{2}  .
smt(@Int @IntDiv).
rewrite - H5.
have ->: u{2} %% u{2} = 0. smt(@Int @IntDiv).  simplify.
smt(@Int @IntDiv).  
qed.
 

lemma opt_5_eq :
     equiv [ OptExtGcd.simplify_ts ~ OptExtGcd.simplify_ts_pos :  odd u{1} /\
      t2{1} = -t2{2} /\ ={t3,u,v} ==> res{1}.`1 = -res{2}.`1 /\ res{1}.`2 = res{2}.`2 ].
proc. simplify.
while ( t2{1} = -t2{2} /\ ={t3, u, v} /\ odd u{1}).
wp. skip. progress. smt(@Int). smt(@Int). smt.
have ->: (-t2{2}) - u{2} =  - ((t2{2}) + u{2}). smt(@Int).
pose x := t2{2} + u{2}.
rewrite dvdNdiv. auto.
smt(@Int @IntDiv).
smt.    
skip. progress. qed.
    
   
lemma opt_5 : equiv[ OptExtGcd.main5 ~ OptExtGcd.main6 : ={arg} /\ 0 < u{1} /\ 0 < v{1}
  /\ odd u{1}    ==>  res{1}.`1 = res{2}.`1 /\ res{1}.`2 = res{2}.`2].
proc.
seq 3 3 : (={u,v,u3,v3,t3} /\ t2{1} = -t2{2} /\ u2{1} = -u2{2} /\ v2{1} = -v2{2} /\ 0 < u{1} /\ 0 < v{1} /\ t2{1} = -1 /\ u2{1} = 0 /\ v2{1} = 1 - u{2} /\ 0 <= v2{2} /\ odd u{1} ).
wp. skip. progress. smt. smt.
seq 1 1 : (={u,v,u3,v3,t3} /\ t2{1} = -t2{2} /\ u2{1} = -u2{2} /\ u2{2} = 0 /\ v2{1} = -v2{2} /\ 0 < u{1} /\ 0 < v{1} /\ odd u{1}  ).
call opt_5_eq. simplify. skip. progress. smt(). 
seq 1 1 : (={u,v,u3,v3,t3} /\ t2{1} = -t2{2} /\ u2{1} = -u2{2} /\ v2{1} = -v2{2} /\ u2{2} = 0 /\ 0 < u{1} /\ 0 < v{1}  /\ odd u{1}).
wp. skip. progress.  simplify.  smt. 
seq 1 1 : (={u,v,u3,v3,t3} /\ t2{1} = -t2{2} /\ u2{1} = -u2{2} /\ v2{1} = -v2{2} /\ 0 < u{1} /\ 0 < v{1} /\ odd u{1} /\ u2{2} = 0).      
wp. skip. progress.  simplify. 
while (={u,v,u3,v3,t3} /\ t2{1} = -t2{2} /\ u2{1} = -u2{2} /\ v2{1} = -v2{2} /\ 0 < u{1} /\ 0 < v{1} /\ odd u{1} ).
seq 1 1 : ((={u,v,u3,v3,t3} /\ t2{1} = -t2{2} /\ u2{1} = -u2{2} /\ v2{1} = -v2{2} /\ 0 < u{1} /\ 0 < v{1} /\ odd u{1} )). call opt_5_eq. simplify. skip. progress. 
wp. skip. progress. smt. smt. smt. smt. smt. smt. simplify.
skip. progress.
qed.     
     

lemma opt_0 : equiv[ ExtGCD.main2 ~ OptExtGcd.main1 : ={arg} /\ 0 < u{1} /\ 0 < v{1} ==> ={res} ].
proc. sp. simplify.
unroll {1} 1.
rcondt {1} 1. progress. skip. smt().
sim. 
qed.


lemma opt_1 : equiv[ OptExtGcd.main1 ~ OptExtGcd.main2  : ={arg} /\ 0 < u{1} /\ 0 < v{1} ==> ={res} ].
proc.
seq 3 3 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2,t3} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0 /\ t3{1} = -v{1}).
wp. skip. progress. smt. 
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2}  /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0).    
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0).
ecall (gcd_t_simp_eq2 t3{1}). skip. progress. smt. smt.  
skip. progress.
rcondf {1} 1. progress. skip. smt.
seq 2 2 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2,t3} /\ t3{1} = u3{1} - v3{1}).
wp. skip. progress. smt. smt. 
while (={u,v,u1,u3,v1,v3,t1,u2,v2,t2,t3} /\ t3{1} = u3{1} - v3{1}).
wp. simplify.
ecall (gcd_t_simp_eq3 t3{1}). skip. progress;smt.
skip. progress.
qed.    


lemma opt_2 : equiv[ OptExtGcd.main2 ~ OptExtGcd.main3 : ={arg} /\ 0 < u{1} /\ 0 < v{1} ==> ={res} ].
proc.
seq 3 3 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} < 0).
wp. simplify.  skip. progress. smt. smt.
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ t3{1} = t3{2} /\ 0 < u{1} /\ 0 < v{1} ).
ecall (gcd_t_simp_eq3 v{1}). skip. progress.   
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ t3{1} = t3{2} /\ 0 < u{1} /\ 0 < v{1}).
wp. skip. progress. 
seq 1 1 : (={u,v,u1,u3,v1,v3,t1,u2,v2,t2} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1} /\ t3{1} = u3{1} - v3{1}).
wp. skip. simplify.  progress.  
while (={u,v,u1,u2,u3,v1,v2,v3,t1,t2} /\ t3{1} = u3{1} - v3{1} /\ `|t3{1}| = t3{2} /\ 0 < u{1} /\ 0 < v{1}).
wp.
exists* t3{1}. elim*. progress.
call (gcd_t_simp_eq2 t3_L). simplify.
skip. progress. 
smt. smt. smt.  smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. 
skip. progress. smt. smt.
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


lemma opt_4 : equiv[ OptExtGcd.main4 ~ OptExtGcd.main5 : ={arg} /\ 0 < u{1} /\ 0 < v{1}
       ==>   ={res}].
proc.
wp. simplify. sp.
while (={t2,t3,u2,u3,v2,v3,u,v}). wp.
inline*. sp. wp. 
while (={t20,t30,u0,v0}).
wp. skip. progress. skip. progress;smt.
wp. inline*. sp. wp. 
while (={t20,t30,u0,v0}).
wp. skip. progress. skip. progress.
qed.
