pragma Goals:printall.
require import AllCore Int IntDiv.
require import Gcd Gcd_props Opt_redc.

require import AlmostYUL.


op P = AlmostYUL.N.
axiom ax1 : 2 * P < R.
axiom ax2 : 0 < P.
axiom ax3 :  N' * P %% R = (-1) %% R.
axiom ax4 :  coprime P R.
axiom R_pos : 0 < R. 
axiom ax5 : 0 <= R2_MOD_P < P.
axiom ax6 : R2_MOD_P = (R * R) %% P.

op comb (l h : int) = h * R + l.

lemma comb_lemma l h : 0 <= l < R => 0 <= h <= P - 1 => comb l h < R * P.
progress.   
rewrite /comb. 
have f : h * R <= (P * R - R). smt.
have q : l < R. smt.
smt.
qed.
    

lemma almost_yul_redc_full_correctness':
  forall (Tlo Thi R_in N' N : int),
    2 * N < R_in =>
    0 < N =>
    N' * N %% R_in = (-1) %% R_in =>
    coprime N R_in =>
    phoare[ AlmostYul._REDC :
                 0 <=(comb Tlo Thi) < R_in * N /\ arg = (Tlo, Thi, R_in, N, N') ==> res = (comb Tlo Thi) * inv N R_in %% N] = 1%r.
admitted.


lemma qq (x a b : int) : 0 < b < a => 0  <= x =>
     x %/ a <= x %/b. smt.
qed.




lemma into_m m_in :
    phoare [ AlmostYul.intoMontgomeryForm : arg = m_in  /\ 0 <= a < P ==> res = (m_in * R) %% P ] = 1%r.
proof. proc.
progress.
seq 1 : (#pre /\ hi = a * R2_MOD_P %/ R ). auto. auto.
seq 1 : (#pre /\ lo = a * R2_MOD_P %% R). auto. auto.
exists* lo, hi. elim*. move => loL hiL.
simplify.
call  (almost_yul_redc_full_correctness' loL hiL  R N' P). smt. smt. smt. smt.
skip. progress.
rewrite /comb. smt.
apply comb_lemma.
split. smt. smt.
split. smt.
progress.
have q1 : a{hr} * R2_MOD_P %/ R <= a{hr} * R2_MOD_P %/ (2 * P). apply qq. smt.
smt.
have q2 : a{hr} * R2_MOD_P %/ (2 * P) <= a{hr}  %/ 2 . smt.
have q3 : a{hr}  %/ 2 <= P - 1 .  smt.
smt.
rewrite /comb.
have ->: (a{hr} * R2_MOD_P %/ R * R + a{hr} * R2_MOD_P %% R)
 = (a{hr} * R2_MOD_P). smt.
rewrite ax6.
have ->: a{hr} * (R * R %% Top.P) * inv Top.P R
 = a{hr} * ((R * R %% Top.P) * inv Top.P R). smt.

have ->: a{hr} * (R * R %% Top.P * inv Top.P R) %% Top.P
 = a{hr} %% Top.P * (R * R %% Top.P * inv Top.P R %% Top.P) %% Top.P. smt(@Int @IntDiv).
admit.

hoare. simplify. auto. auto.
hoare. simplify. auto. auto.
qed. 


lemma outof_m m_in :
    phoare [ AlmostYul.outOfMontgomeryForm : arg = m_in  /\ 0 <= m < P ==> res = m_in * (inv P R) %% P ] = 1%r.
proc.
exists* m. elim*. move => mL.
simplify.
call  (almost_yul_redc_full_correctness' mL 0  R N' P). smt. smt. smt. smt.
skip. progress. smt. smt.
qed.    



lemma add_m a_in b_in :
    phoare [ AlmostYul.montgomeryAdd : arg = (a_in,b_in)  /\ 0 <= a_in < P
      /\  0 <= b_in <= P ==> res = (a_in + b_in) %% P ] = 1%r.
proof. proc.
wp. skip. progress.
case (AlmostYUL.N <= (augend{hr} + addend{hr}) %% R).
have f1 : (augend{hr} + addend{hr}) < 2 * P. smt.
have f2 : (augend{hr} + addend{hr}) %% R = (augend{hr} + addend{hr}) . smt.
rewrite f2.
progress.
have f3 : 0 <= (augend{hr} + addend{hr} - P) < P. split. smt.
progress.   smt. 
have -> : (augend{hr} + addend{hr} - AlmostYUL.N) %% R = (augend{hr} + addend{hr} - AlmostYUL.N). smt.
progress. rewrite /P.
smt (pmod_small @IntDiv).
progress.
have ->: (augend{hr} + addend{hr}) %% R = (augend{hr} + addend{hr}). smt.
smt.
qed.
    


lemma sub_m a_in b_in :
    phoare [ AlmostYul.montgomerySub : arg = (a_in,b_in)  /\ 0 <= a_in < P
      /\  0 <= b_in < P ==> res = (a_in - b_in) %% P ] = 1%r.
proof. proc.
exists* minuend, subtrahend. elim*. move => m1 m2.
call (add_m m1 ((P - m2) %% R)). skip. progress.
smt. smt.
have ->: (P - subtrahend{hr}) %% R = (P - subtrahend{hr}). smt.
smt(@Int @IntDiv).
qed.

lemma mul_m a_in b_in :
       phoare [ AlmostYul.montgomeryMul : arg = (a_in * R %% P,b_in * R %% P)  /\ 0 <= arg.`1 < P
         /\  0 <= arg.`2 < P ==> res = (a_in * b_in) * R %% P ] = 1%r.
proc.
seq 2 : (#pre /\ higherHalfOfProduct = ((a_in * R %% P) * (b_in * R %% P)) %/ R /\ lowestHalfOfProduct = ((a_in * R %% P) * (b_in * R %% P)) %% R).
auto. wp. skip. progress.
exists* lowestHalfOfProduct, higherHalfOfProduct. elim*.
move => lo hi.
call  (almost_yul_redc_full_correctness' lo hi  R N' P). smt. smt. smt. smt.
skip. progress. 
smt.
have ->: comb (a_in * R %% P * (b_in * R %% P) %% R)
  (a_in * R %% P * (b_in * R %% P) %/ R)
   = a_in * R %% P * (b_in * R %% P). smt.
smt.
have ->: comb (a_in * R %% P * (b_in * R %% P) %% R)
  (a_in * R %% P * (b_in * R %% P) %/ R)
   = a_in * R %% P * (b_in * R %% P). smt.
have ->:
   a_in * R %% P * (b_in * R %% P) * inv P R %% P
 =  a_in * R  * ((b_in * R %% P) * inv P R) %% P.
 smt(@Int @IntDiv).
have ->: a_in * R  * ((b_in * R %% P) * inv P R) %% P
  = a_in * R  * ((b_in * R %% P) * inv P R %% P) %% P.
 smt(@Int @IntDiv).  
have ->: ((b_in * R %% P) * inv P R %% P)
  = (b_in * R) * inv P R %% P . 
 smt(@Int @IntDiv).  
have ->: (b_in * R) * inv P R %% P
 = b_in * (R * inv P R) %% P.
smt.
have ->: b_in * (R * inv P R) %% P 
 = b_in * (R * inv P R %% P) %% P.
 smt(@Int @IntDiv).
have ->: (R * inv P R %% P) = 1.
   smt.
have ->: b_in * 1 = b_in. smt().
have ->: a_in * R * (b_in %% P) %% P
  = a_in * R * (b_in ) %% P.
 smt(@Int @IntDiv).
smt().
hoare. simplify. wp. skip. progress. auto.
qed.  
