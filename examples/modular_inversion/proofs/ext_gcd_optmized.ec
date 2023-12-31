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


    proc main8(u : int, v : int) = {
      var u2,u3,v2,v3,t2,t3;

      (u2,u3) <- (0, u);
      (v2,v3) <- (u-1, v);
      (t2,t3) <- (1, v);

      (t2,t3) <@ simplify_ts_pos(t2, v, u, v);
      (v2, v3) <- (u-t2, t3);

      if (v3 < u3){
        t3 <- u3 - v3;
      }else{
        t3 <- v3 - u3;
      }
      t2 <- u-v2;

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


    proc main9(u : int, v : int, r : int) = {
      var u2,u3,v2,v3,t2,t3;

      (u2,u3) <- (0, u);
      (v2,v3) <- (u-r, v);
      (t2,t3) <- (r, v);

      (t2,t3) <@ simplify_ts_pos(t2, v, u, v);
      (v2, v3) <- (u-t2, t3);

      if (v3 < u3){
        t3 <- u3 - v3;
      }else{
        t3 <- v3 - u3;
      }
      t2 <- u-v2;

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


lemma nosmt opt_6_eq_aux m x' y' :  odd m =>
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


lemma nosmt opt_8_aux (a b : int) : even b =>
     a * (b %/ 2) = (a * b) %/2.
progress.    
have <-: 2 * (b %/ 2) = b. smt (@Int @IntDiv).
have ->: a * (2 * (b %/ 2)) %/ 2 = 2 * a * (b %/ 2) %/ 2.
    smt (@Int @IntDiv).
have ->: a * ((2 * (b %/ 2)) %/ 2) = 2 * a * ( (b %/ 2)) %/ 2.
smt (@Int @IntDiv).    auto.
qed.    

lemma opt_8_eq u_in r  : 
     equiv [ OptExtGcd.simplify_ts_pos ~ OptExtGcd.simplify_ts_pos :  odd u{1} /\ 2 < u{1} /\
      r * t2{1} %% u{1} = t2{2} %% u{1} /\ ={t3,u,v} /\ u{1} = u_in /\ odd r ==> r * res{1}.`1 %% u_in = res{2}.`1 %% u_in /\ res{1}.`2 = res{2}.`2 ].
proc.  simplify.
while (r * t2{1} %% u{1} = t2{2} %% u{1} /\ ={t3, u, v} /\ odd u{1} /\ u{1} = u_in /\ 2 < u{1} /\ odd r{1}).
wp. skip. progress.
apply opt_6_eq_aux. auto.  auto.
    have ->: 2 * (r * (t2{1} %/ 2)) = r * t2{1}.
       have q : even (r * t2{1} ). smt.
      have -> : (r * (t2{1} %/ 2))  = (r * t2{1}) %/ 2. smt (opt_8_aux).
    smt (opt_8_aux).
   
    have ->: 2 * (t2{2} %/ 2) = t2{2}. smt (opt_8_aux). rewrite - H. auto.
apply opt_6_eq_aux. auto. auto.
have ->: 2 * (r * ((t2{1} + u{2}) %/ 2)) = (r * (t2{1} + u{2}) ).
    rewrite opt_8_aux. smt.
    rewrite opt_8_aux.
    have f : even (t2{1} + u{2}). smt .
    smt.
smt.    
have ->: r * (t2{1} + u{2}) %% u{2} = r * t2{1} %% u{2}.
 have ->: r * (t2{1} + u{2}) = r * t2{1} + r * u{2}. smt.
smt (@Int @IntDiv).       
have ->: 2 * (t2{2} %/ 2) = t2{2}.  smt.
smt().
apply opt_6_eq_aux. auto. auto.    
have ->: 2 * (r * (t2{1} %/ 2)) = r * t2{1}.
    rewrite opt_8_aux. auto.
        rewrite opt_8_aux. auto. smt.
    smt.    
have ->: 2 * ((t2{2} + u{2}) %/ 2) = (t2{2} + u{2}).
rewrite opt_8_aux. auto. smt. smt.
smt(@Int @IntDiv).    
apply opt_6_eq_aux. auto. auto.    
rewrite opt_8_aux. auto. smt.
rewrite opt_8_aux. auto.
  have f : even (t2{1} + u{2}). smt.
    smt.    
    have ->: 2 * ((t2{2} + u{2}) %/ 2) = (t2{2} + u{2}).
      have f : even (t2{2} + u{2}). smt.
    smt.
have ->: 2 * (r * (t2{1} + u{2}) ) %/2 = (r * (t2{1} + u{2}) ). smt(@Int @IntDiv).
have ->: r * (t2{1} + u{2}) = r * t2{1} + r * u{2}. smt.
have ->: (r * t2{1} + r * u{2}) %% u{2} = r * t2{1} %% u{2}.
clear H1 H2 H3 H4 H5 H6.    
smt.
smt.
skip.
progress.
qed.


lemma opt_8 u_in r_in : equiv[ OptExtGcd.main8 ~ OptExtGcd.main9
    : arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 /\  r_in = arg{2}.`3  /\ u{1} = u_in /\ odd u_in /\ odd r_in /\ 2 < u_in ==> (r_in * res{1}.`1 %% u_in =  res{2}.`1 %% u_in) /\ res{1}.`2 = res{2}.`2 ].
proc. 
seq 3 3 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
wp. skip. progress. clear H H0. smt.
seq 1 1 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
call (opt_8_eq u_in r_in).  skip. progress. 
seq 2 2 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
wp. skip. progress.
have ->: r{2} * (u{2} - t2{1}) =
    r{2} * u{2} - r{2} * t2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u{2} - r{2} * t2{1}) %% u{2}
  = (r{2} * u{2} %% u{2} - (r{2} * t2{1} %% u{2})) %% u{2}.
smt (@Int @IntDiv).    
 have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
 rewrite H1.
have ->: (u{2} - t2{2}) %% u{2} = (u{2} %% u{2} - t2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
smt (@Int @IntDiv).      
have ->: r{2} * (u{2} - t2{1}) =
    r{2} * u{2} - r{2} * t2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u{2} - r{2} * t2{1}) %% u{2}
  = (r{2} * u{2} %% u{2} - (r{2} * t2{1} %% u{2})) %% u{2}.
smt (@Int @IntDiv).    
 have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
 rewrite H1.
have ->: (u{2} - t2{2}) %% u{2} = (u{2} %% u{2} - t2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
smt (@Int @IntDiv).      
seq 1 1 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
wp. skip. progress.
have ->: (u{2} - v2{2}) %% u{2}
   = (u{2} %% u{2} - v2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
rewrite - H0.
have ->: u{2} %% u{2} = 0.  smt (@Int @IntDiv). simplify.
have ->: r{2} * (u{2} - v2{1}) =
    r{2} * u{2} - r{2} * v2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u{2} - r{2} * v2{1}) %% u{2}
  = (r{2} * u{2} %% u{2} - (r{2} * v2{1} %% u{2})) %% u{2}.
smt (@Int @IntDiv).    
 have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify. auto.
while  (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}
 /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
seq 1 1 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
call (opt_8_eq u_in r_in).  skip. progress.
seq 1 1 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
wp. skip. progress.  
have ->: r{2} * (u{2} - t2{1}) =
    r{2} * u{2} - r{2} * t2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u{2} - r{2} * t2{1}) %% u{2}
  = (r{2} * u{2} %% u{2} - (r{2} * t2{1} %% u{2})) %% u{2}.
smt (@Int @IntDiv).    
 have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
 rewrite H1.
have ->: (u{2} - t2{2}) %% u{2} = (u{2} %% u{2} - t2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
smt (@Int @IntDiv).      
seq 1 1 : (={u,v,u3,v3,t3} 
 /\ r{2} * u2{1} %% u{1} = u2{2} %% u{2}
 /\ r{2} * v2{1} %% u{1} = v2{2} %% u{2}
 /\ r{2} * t2{1} %% u{1} = t2{2} %% u{2}  /\ u{1} = u_in /\ odd u_in /\ 2 < u_in /\ r{2} = r_in /\ odd r_in).
wp. skip. progress.  
have ->: r{2} * (u{2} + (u2{1} - v2{1})) = (r{2} * u{2} + r{2} * (u2{1} - v2{1})).
smt (@Int @IntDiv).
have ->: (r{2} * u{2} + r{2} * (u2{1} - v2{1})) %% u{2}
   = (r{2} * u{2} %% u{2} + r{2} * (u2{1} - v2{1}) %% u{2}) %% u{2}. 
smt (@Int @IntDiv).
have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
have ->: (u{2} + (u2{2} - v2{2})) %% u{2} =
    (u{2} %% u{2} + (u2{2} - v2{2}) %% u{2}) %% u{2}.
smt (@Int @IntDiv).
    have ->: u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
have ->: (u2{2} - v2{2}) %% u{2}
   = (u2{2} %% u{2} - v2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
rewrite - H0  - H.
have ->: r{2} * (u2{1} - v2{1}) =
    r{2} * u2{1} - r{2} * v2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u2{1} - r{2} * v2{1}) %% u{2}
  = (r{2} * u2{1} %% u{2} - r{2} * v2{1} %% u{2}) %% u{2}.
smt (@Int @IntDiv).    
auto.
have ->: (u{2} + (u2{2} - v2{2})) %% u{2} =
    (u{2} %% u{2} + (u2{2} - v2{2}) %% u{2}) %% u{2}.
smt (@Int @IntDiv).
    have ->: u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
have ->: (u2{2} - v2{2}) %% u{2}
   = (u2{2} %% u{2} - v2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
rewrite - H0  - H.
have ->: r{2} * (u2{1} - v2{1}) =
    r{2} * u2{1} - r{2} * v2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u2{1} - r{2} * v2{1}) %% u{2}
  = (r{2} * u2{1} %% u{2} - r{2} * v2{1} %% u{2}) %% u{2}.
smt (@Int @IntDiv).    
smt (@Int @IntDiv).    
have ->: r{2} * (u{2} + (u2{1} - v2{1})) = (r{2} * u{2} + r{2} * (u2{1} - v2{1})).
smt (@Int @IntDiv).
have ->: (r{2} * u{2} + r{2} * (u2{1} - v2{1})) %% u{2}
   = (r{2} * u{2} %% u{2} + r{2} * (u2{1} - v2{1}) %% u{2}) %% u{2}. 
smt (@Int @IntDiv).
have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv). simplify.
have ->: (u2{2} - v2{2}) %% u{2}
   = (u2{2} %% u{2} - v2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
rewrite - H0  - H.
have ->: r{2} * (u2{1} - v2{1}) =
    r{2} * u2{1} - r{2} * v2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u2{1} - r{2} * v2{1}) %% u{2}
  = (r{2} * u2{1} %% u{2} - r{2} * v2{1} %% u{2}) %% u{2}.
smt (@Int @IntDiv).    
smt (@Int @IntDiv).    
have ->: (u2{2} - v2{2}) %% u{2}
   = (u2{2} %% u{2} - v2{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
rewrite - H0  - H.
have ->: r{2} * (u2{1} - v2{1}) =
    r{2} * u2{1} - r{2} * v2{1}.     smt (@Int @IntDiv).
have ->: (r{2} * u2{1} - r{2} * v2{1}) %% u{2}
  = (r{2} * u2{1} %% u{2} - r{2} * v2{1} %% u{2}) %% u{2}.
smt (@Int @IntDiv).    
smt (@Int @IntDiv).    
wp. skip. progress. 
skip. progress. 
have ->: (u{2} - u2_R) %% u{2}
   = (u{2} %% u{2} - u2_R{2} %% u{2}) %% u{2}.
smt (@Int @IntDiv).
have ->: r{2} * (u{2} - u2_L) =
    r{2} * u{2} - r{2} * u2_L.     smt (@Int @IntDiv).
have ->: (r{2} * u{2} - r{2} * u2_L) %% u{2}
  = (r{2} * u{2} %% u{2} - r{2} * u2_L %% u{2}) %% u{2}.
smt (@Int @IntDiv).    
have ->: r{2} * u{2} %% u{2} = 0. smt (@Int @IntDiv).     simplify.
have ->: u{2} %% u{2} = 0. smt (@Int @IntDiv).     simplify.
smt().
qed.  
  

lemma opt_7 : equiv[ OptExtGcd.main7 ~ OptExtGcd.main8
    : ={arg} ==> ={res} ].
proc. wp. sp. simplify.
while (={u,v,t2,v2,u2,u3,v3,t3}).
wp. simplify. call (_:true). sim. skip. progress.
wp. call (_:true). sim. skip. progress;smt.
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


lemma correctness_transfer u_in r_in : odd u_in => odd r_in => 2 < u_in =>

 equiv[ OptExtGcd.main9 ~ ExtGCD.main2
     : ={u,v}
    /\ u{1} = u_in
    /\ r{1} = r_in
    /\ 0 < u{1}
    /\ 0 < v{1}
    ==> res{1}.`1 %% u_in = r_in * res{2}.`2  %% u_in /\ res{1}.`2 = res{2}.`3 ].
move => oddu oddr uin2. symmetry.

transitivity OptExtGcd.main1
  (={arg} /\ u{1} = u_in  /\ 0 < u{1} /\ 0 < v{1} ==> ={res})
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in  /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`2 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`3 ).
progress. smt().
progress. smt().
conseq opt_0. smt().

  
transitivity OptExtGcd.main2
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> ={res})
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`2 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`3 ).
progress. smt().
progress. 
conseq opt_1. smt().

transitivity OptExtGcd.main3
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> ={res})
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`2 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`3 ).
progress. smt().
progress. 
conseq opt_2. smt().


transitivity OptExtGcd.main4
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> res{1}.`2 = res{2}.`1 /\ res{1}.`3 = res{2}.`2)
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`1 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`2 ).
progress. smt().
progress.  smt(). smt().
conseq opt_3. smt().

  
transitivity OptExtGcd.main5
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> ={res})
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`1 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`2 ).
progress. smt().
progress.  
conseq opt_4. smt().

transitivity OptExtGcd.main6
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> ={res})
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`1 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`2 ).
progress. smt().
progress.  
conseq opt_5. progress. progress. smt().


transitivity OptExtGcd.main7
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> res{1}.`1 %% u_in = res{2}.`1 %% u_in /\ res{1}.`2 = res{2}.`2)
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} ==> r_in * res{1}.`1 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`2 ).
progress. smt().
progress.    rewrite - H1. smt(@Int @IntDiv). smt().  
conseq (opt_6 u_in). progress. 

transitivity OptExtGcd.main8
  (={arg} /\ u{1} = u_in /\ 0 < u{1} /\ 0 < v{1} ==> ={res})
  (={u,v} /\ u{1} = u_in /\ r{2} = r_in /\ 0 < u{1} /\ 0 < v{1} /\ r{2} = r_in ==> r_in * res{1}.`1 %% u_in = res{2}.`1  %% u_in /\ res{2}.`2 = res{1}.`2 ).
progress. exists (u{2}, v{2}). progress. smt(). smt(). smt(). smt().
auto.
  
progress.    
conseq (opt_7). progress.

conseq (opt_8 u_in r_in). progress.  

progress. smt().
qed.  

require import Distr.
  
lemma opt_main9_full_correctness &m u v r: 2 < u => 0 < v => odd u => odd r => 
    1%r = Pr[ OptExtGcd.main9(u,v,r) @&m : v *  (res.`1) %% u =  r * (gcd u v) %% u ].

progress.
have f : 1%r <= Pr[ OptExtGcd.main9(u,v,r) @&m : v *  (res.`1) %% u =  r * (gcd u v) %% u ].
    
rewrite - (main2_full_correctness &m u v).
byequiv.
symmetry.    
conseq (correctness_transfer u r _ _ _).  progress.  smt().
progress.   
have ->: v * result_L.`1 %% u = (v %% u) * (result_L.`1 %% u) %% u.
smt(@Int @IntDiv).    
rewrite H3.
have ->: v %% u * (r * result_R.`2 %% u) %% u = v * (r * result_R.`2) %% u.
smt(@Int @IntDiv).
have ->: v * (r * result_R.`2) %% u = r * v * result_R.`2 %% u. smt(@Int @IntDiv).
have ->: r * v * result_R.`2 %% u = (r %% u) * (v * result_R.`2 %% u) %% u. smt(@Int @IntDiv).
rewrite H5.
have ->: r %% u * (result_R.`3 %% u) %% u = r * result_R.`3 %% u.
smt(@Int @IntDiv).
 rewrite H6. auto.
auto.
auto. smt(). auto. auto.
smt(@Distr).
qed.    

lemma opt_main9_full_correctness2 &m u v r: 2 < u => 0 < v => odd u => odd r =>
    gcd u v = 1 =>
    1%r = Pr[ OptExtGcd.main9(u,v,r) @&m :  (res.`1) %% u =  (inv u v) * r %% u ].
progress.
have f : 1%r <= Pr[ OptExtGcd.main9(u,v,r) @&m :  (res.`1) %% u =  (inv u v) * r %% u ].
rewrite  (opt_main9_full_correctness &m u v r);auto.
rewrite Pr[mu_sub]. progress.
have : (inv u v) %% u * (v * res{hr}.`1 %% u) %% u = (inv u v) * (r * gcd u v) %% u.
    smt (@Int @IntDiv).
rewrite H3.
have ->: (v * res{hr}.`1 %% u) = (v %% u * res{hr}.`1) %% u.
    smt (@Int @IntDiv).
have ->: (inv u v %% u) * (v %% u * res{hr}.`1 %% u) %% u
     = (inv u v) * (v %% u * res{hr}.`1) %% u.
    smt (@Int @IntDiv).
have ->: (inv u v) * (v %% u * res{hr}.`1) %% u
      = ((inv u v) * (v %% u) * res{hr}.`1) %% u.
    smt (@Int @IntDiv).
have ->: inv u v * (v %% u) * res{hr}.`1 %% u
    = (inv u v * (v %% u) %% u) * res{hr}.`1 %% u.
    smt (@Int @IntDiv).
have ->: inv u v * (v %% u) %% u = inv u v * v %% u.
    smt (@Int @IntDiv).
    rewrite inv_ax. smt(). auto.
smt(@Distr).
qed.    
