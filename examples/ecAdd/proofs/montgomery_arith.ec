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
axiom ax7 : 2 < P.
axiom ax9 : odd P.
axiom ax10 : odd R2_MOD_P.
axiom P_prime : prime P.

axiom ax11 (a b : int) : coprime P (a * b) => inv P (a * b) %% P  = inv P a * inv P b %% P.
axiom ax12 a : coprime P a => inv P (a %% P) = inv P a.
lemma ax13 a : coprime P a = coprime P (a %% P). rewrite /coprime. rewrite gcd4. rewrite - gcd_modl.
rewrite gcd4. auto. qed.



lemma addmod a_in b_in m_in :
    phoare [ AlmostYul.addmod : arg = (a_in,b_in,m_in)  /\ 0 <= a_in < m_in /\ 0 <= 2 * m_in < R
      /\  0 <= b_in <= m_in ==> res = (a_in + b_in) %% m_in ] = 1%r.
proof. proc.
wp. skip. progress. smt.
qed.


lemma submod a_in b_in m_in :
    phoare [ AlmostYul.submod : arg = (a_in,b_in,m_in)  /\ 0 <= a_in < m_in /\ 0 <= 2 * m_in < R
      /\  0 <= b_in <= m_in ==> res = (a_in - b_in) %% m_in ] = 1%r.
proof. proc.
call (addmod a_in ((m_in - b_in) %% R) m_in). skip. progress.
smt. smt. smt.
qed.


op comb (l h : int) = h * R + l.

lemma comb_lemma l h : 0 <= l < R => 0 <= h <= P - 1 => comb l h < R * P.
progress.   
rewrite /comb. 
have f : h * R <= (P * R - R). smt.
have q : l < R. smt.
smt.
qed.
    

lemma almost_yul_redc_full_correctness':
  forall (Tlo Thi  N' N : int),
    2 * N < AlmostYUL.R =>
    0 < N =>
    N' * N %% AlmostYUL.R = (-1) %% AlmostYUL.R =>
    coprime N AlmostYUL.R =>
    phoare[ AlmostYul._REDC :
                 0 <=(comb Tlo Thi) < R * N /\ arg = (Tlo, Thi, AlmostYUL.R, N, N') /\ 0 <= Thi < R /\
    0 <= Tlo < R ==> res = (comb Tlo Thi) * inv N AlmostYUL.R %% N] = 1%r.
progress.
conseq (almost_yul_redc_full_correctness  (comb Tlo Thi) Tlo Thi AlmostYUL.R N' N _ _ _ _  );auto.
progress. rewrite /comb. smt. smt. smt.
qed.    


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
call  (almost_yul_redc_full_correctness' loL hiL  N' P). smt. smt. smt. smt.
skip. progress.
rewrite /comb. smt.
apply comb_lemma.
split. smt. smt.
split. smt. smt. smt. smt. smt. smt. 
rewrite /comb.
have ->: (a{hr} * R2_MOD_P %/ R * R + a{hr} * R2_MOD_P %% R)
 = (a{hr} * R2_MOD_P). smt.
rewrite ax6.
have ->: a{hr} * (R * R %% Top.P) * inv Top.P R
 = a{hr} * ((R * R %% Top.P) * inv Top.P R). smt.
have ->: a{hr} * (R * R %% Top.P * inv Top.P R) %% Top.P
 = a{hr} %% Top.P * (R * R %% Top.P * inv Top.P R %% Top.P) %% Top.P. smt(@Int @IntDiv).
have ->: (R * R %% P * inv P R %% P) = (R * R * inv P R %% P). smt(@Int @IntDiv).
have ->: (R * R * inv P R %% P) = (R * (R * inv P R) %% P). smt(@Int @IntDiv).
have ->: (R * (R * inv P R) %% P) = (R * ((inv P R * R ) %% P) %% P). smt(@Int @IntDiv). rewrite inv_ax. smt.
 smt(@Int @IntDiv).
hoare. simplify. auto. auto.
hoare. simplify. auto. auto.
qed. 





lemma outof_m m_in :
    phoare [ AlmostYul.outOfMontgomeryForm : arg = m_in  /\ 0 <= m < P ==> res = m_in * (inv P R) %% P ] = 1%r.
proc.
exists* m. elim*. move => mL.
simplify.
call  (almost_yul_redc_full_correctness' mL 0   N' P);auto. smt. smt. smt. smt.
progress. smt. smt. smt. smt.
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
call  (almost_yul_redc_full_correctness' lo hi  N' P). smt. smt. smt. smt.
skip. progress. 
smt.
have ->: comb (a_in * R %% P * (b_in * R %% P) %% R)
  (a_in * R %% P * (b_in * R %% P) %/ R)
   = a_in * R %% P * (b_in * R %% P). smt.
smt. smt. smt. smt. smt.
have ->: comb (a_in * R %% P * (b_in * R %% P) %% R)
  (a_in * R %% P * (b_in * R %% P) %/ R)
   = a_in * R %% P * (b_in * R %% P). timeout 10. smt.
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


require import Ext_gcd_optmized.

lemma inv_eq u_in :
     equiv [ AlmostYul.simplify_ts_pos ~ OptExtGcd.simplify_ts_pos : ={t2,t3,u} /\ u{1} = u_in
       /\ 0 <= t2{1} <= u{1}  /\ 0 <= t3{1} <= u{1} /\ 2 * u{1} < R /\ 0 <= u{1} ==> ={res} /\ 0 <= res{1}.`1 <= u_in /\ 0 <= res{1}.`2 <= u_in ].
proc. simplify.
while (#pre). wp. skip. progress.
smt. smt. smt. smt. smt. smt. smt. smt. smt.
skip. progress.
qed.    
    

lemma simp_eq :
     equiv [ AlmostYul.binaryExtendedEuclideanAlgorithm ~ OptExtGcd.main10 : ={arg} /\ 0 < u{1} /\ 0 <= r{1} <= u{2} /\ 0 < v{2} < u{2} /\ 2 * u{1} < R ==> res{1} = res{2}.`1   ].
proc. simplify.
while (={u2,v2,t2,u3,v3,t3,u,v,r} 
  /\ 0 <= u2{1} <= u{1}
  /\ 0 <= v2{1} <= u{1}
  /\ 0 <= t2{1} <= u{1}
  /\ 0 <= u3{1} <= u{1}
  /\ 0 <= v3{1} <= u{1}
  /\ 0 <= t3{1} <= u{1}       
  /\ 2 * u{1}   < R
  /\ 0 < v{1} < u{1}
  /\ 0 < u{1} 
).
seq 1 1 : (={u2,v2,t2,u3,v3,t3,u,v,r} 
  /\ 0 <= u2{1} <= u{1}
  /\ 0 <= v2{1} <= u{1}
  /\ 0 <= t2{1} <= u{1}
  /\ 0 <= u3{1} <= u{1}
  /\ 0 <= v3{1} <= u{1}
  /\ 0 <= t3{1} <= u{1}       
  /\ 2 * u{1}   < R
  /\ 0 < v{1} < u{1}
  /\ 0 < u{1} ).
ecall (inv_eq  u{1}). simplify. skip. progress.
smt.
wp. skip. progress;smt.
seq 3 3 : (={u2,v2,t2,u3,v3,t3,u,v,r} 
  /\ 0 <= u2{1} <= u{1}
  /\ 0 <= v2{1} <= u{1}
  /\ 0 <= t2{1} <= u{1}
  /\ 0 <= u3{1} <= u{1}
  /\ 0 <= v3{1} <= u{1}
  /\ 0 <= t3{1} <= u{1}       
  /\ 2 * u{1}   < R
  /\ 0 < v{1} < u{1}
  /\ 0 < u{1} ).
wp. skip. progress;smt().
seq 1 1 : (={u2,v2,t2,u3,v3,t3,u,v,r} 
  /\ 0 <= u2{1} <= u{1}
  /\ 0 <= v2{1} <= u{1}
  /\ 0 <= t2{1} <= u{1}
  /\ 0 <= u3{1} <= u{1}
  /\ 0 <= v3{1} <= u{1}
  /\ 0 <= t3{1} <= u{1}       
  /\ 2 * u{1}   < R
  /\ 0 < v{1} < u{1}
  /\ 0 < u{1} ).
ecall (inv_eq  u{1}). simplify. wp. skip. progress;smt.
wp. skip. progress;smt.
qed.





lemma inv_m a_in :
       phoare [ AlmostYul.montgomeryModularInverse : arg = (a_in * R %% P)  /\ 0 < arg < P
         ==> res = (inv P a_in) * R %% P ] = 1%r.
bypr. progress. rewrite H. rewrite H in H0. rewrite H in H1. clear H.
 have ->: Pr[AlmostYul.montgomeryModularInverse(a_in * R %% P) @ &m : res = inv P a_in * R %% P]
        = Pr[AlmostYul.binaryExtendedEuclideanAlgorithm(P, a_in * R %% P, R2_MOD_P) @ &m : res = inv P a_in * R %% P].
  byequiv. proc*. inline AlmostYul.montgomeryModularInverse. wp. sp. simplify.
   call (_:true). sim. skip. progress. auto. auto.
        
 have ->: Pr[AlmostYul.binaryExtendedEuclideanAlgorithm(P, a_in * R %% P, R2_MOD_P) @ &m : res = inv P a_in * R %% P]
        = Pr[OptExtGcd.main10(P, a_in * R %% P, R2_MOD_P) @ &m :
   res.`1 = inv P a_in * R %% P].
byequiv. conseq  simp_eq. progress. smt. smt. smt. smt. auto. auto. auto.

byphoare (_: arg = (P, a_in * R %% P, R2_MOD_P) ==> _).
conseq (modular_inversion_correctness P (a_in * R %% P) R2_MOD_P _ _ _ _ _ _).
have QQ : inv P a_in * R %% P = inv P (a_in * R %% P) * R2_MOD_P %% P.

  have ->: inv P (a_in * R %% P) * R2_MOD_P %% P = inv P (a_in * R %% P) %% P * R2_MOD_P %% P.
  smt(@Int @IntDiv). rewrite ax12. rewrite ax13. apply prime_coprime. smt. smt.
          rewrite ax11.  rewrite ax13. apply prime_coprime. smt. smt.
have ->: inv P a_in * inv P R %% P = (inv P a_in %% P) * (inv P R %% P) %% P.   smt(@Int @IntDiv).
have ->: inv P a_in %% P * (inv P R %% P) %% P * R2_MOD_P %% P
        = inv P a_in %% P * (inv P R %% P) * R2_MOD_P %% P. smt(@Int @IntDiv).


rewrite  ax6.
have ->: inv P a_in %% P * (inv P R %% P) * (R * R %% P) %% P
     = inv P a_in %% P * ((inv P R %% P) * (R * R %% P)) %% P. smt().
have ->: inv P a_in %% P * ((inv P R %% P) * (R * R %% P)) %% P
   = inv P a_in %% P * ((inv P R %% P) * (R * R %% P) %% P) %% P. smt(@Int @IntDiv).
have ->:  R * R %% P  =  R %% P * R %% P. smt(@Int @IntDiv).
have ->: (inv P R %% P * (R %% P * R %% P) %% P) =
   (inv P R %% P * (R %% P * R) %% P). smt(@Int @IntDiv).
have ->: inv P R %% P * (R %% P * R) = (inv P R %% P * (R %% P)) * R.   smt().
have ->: (inv P R %% P * (R %% P) * R %% P) = (inv P R %% P * (R %% P) %% P * R %% P).   smt(@Int @IntDiv).
have ->: inv P R %% P * (R %% P) %% P = inv P R  * R %% P. smt(@Int @IntDiv).
rewrite inv_ax. smt.  simplify.   
smt(@Int @IntDiv). 
progress.
rewrite H. apply QQ. rewrite H. rewrite  QQ. auto.
rewrite /P.   smt. smt. smt.  smt.
apply prime_coprime. smt. smt. smt. auto. auto. qed.

lemma div_m a_in b_in :
       phoare [ AlmostYul.montgomeryDiv : arg = (a_in * R %% P, b_in * R %% P)  /\ 0 <= arg.`1 < P
           /\  0 < arg.`2 < P
         ==> res =  a_in * (inv P b_in) * R %% P ] = 1%r.
proc. simplify.
seq 1 : (#pre /\ inverse = (inv P b_in) * R %% P ) 1%r 1%r 0%r 0%r.  auto.
exists* divisor. elim*. move => div_v.
call (inv_m b_in).               skip. progress.
call (mul_m a_in (inv P b_in)). skip. progress.
smt. smt. 
phoare split ! 1%r 1%r.
auto.        
call (inv_m b_in).               skip. progress.
call (inv_m b_in).               skip. progress.           
auto.
qed.       



lemma into_m_h m_in :
 hoare [ AlmostYul.intoMontgomeryForm : arg = m_in  /\ 0 <= a < P ==> res = (m_in * R) %% P ].
hoare.
phoare split ! 1%r 1%r. auto. proc. inline*. auto.
apply into_m. qed.


lemma mul_m_h a_in b_in :
       hoare [ AlmostYul.montgomeryMul : arg = (a_in * R %% P,b_in * R %% P)  /\ 0 <= arg.`1 < P
         /\  0 <= arg.`2 < P ==> res = (a_in * b_in) * R %% P ].
hoare.
phoare split ! 1%r 1%r. auto. proc. inline*. auto.
apply mul_m. qed.

lemma div_m_h a_in b_in :
       hoare [ AlmostYul.montgomeryDiv : arg = (a_in * R %% P, b_in * R %% P)  /\ 0 <= arg.`1 < P
           /\  0 < arg.`2 < P
         ==> res =  a_in * (inv P b_in) * R %% P ].
hoare.
phoare split ! 1%r 1%r. auto. proc*.  call (div_m a_in b_in). progress.
apply div_m. qed.

lemma submod_h a_in b_in m_in :
    hoare [ AlmostYul.submod : arg = (a_in,b_in,m_in)  /\ 0 <= a_in < m_in /\ 0 <= 2 * m_in < R
      /\  0 <= b_in <= m_in ==> res = (a_in - b_in) %% m_in ]. admitted.


lemma outof_m_h m_in :
    hoare [ AlmostYul.outOfMontgomeryForm : arg = m_in  /\ 0 <= m < P ==> res = m_in * (inv P R) %% P ].
admitted.


lemma addmod_h a_in b_in m_in :
    hoare [ AlmostYul.addmod : arg = (a_in,b_in,m_in)  /\ 0 <= a_in < m_in /\ 0 <= 2 * m_in < R
      /\  0 <= b_in <= m_in ==> res = (a_in + b_in) %% m_in ]. admitted.


op pointIsInCurve (x y : int) = (y * y) %% P = (x * x * x + 3) %% P.


lemma pointIsInCurve_m_h (x_in y_in : int) :
 hoare [ AlmostYul.pointIsInCurve : arg = (x_in * R %% P, y_in * R %% P) ==>  
       res = (y_in * y_in * R %% P = (x_in * x_in * x_in * R + 3 * R) %% P ) ].
admitted.

    
lemma pointIsInCurve_m (x_in y_in : int) :
 phoare [ AlmostYul.pointIsInCurve : arg = (x_in * R %% P, y_in * R %% P) ==>  
       res = (y_in * y_in * R %% P = (x_in * x_in * x_in * R + 3 * R) %% P ) ] = 1%r.
admitted.
    
