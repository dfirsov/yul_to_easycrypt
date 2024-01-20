require import Int IntDiv.



lemma odd_even u v : odd u => odd v => !odd (u - v).
proof. smt(@IntDiv). qed.

axiom gcd1 u v : !odd u => !odd v =>  gcd u v = 2 * gcd (u %/ 2) (v %/ 2).
axiom gcd2 u v : !odd u => odd v => gcd u v = gcd (u %/ 2) v.   
lemma gcd3 u v : gcd u v = gcd (u - v) v. smt. qed.
lemma gcd4 u v : gcd u v = gcd v u. smt. qed.
lemma gcd5 u v : gcd u v = gcd (-u) v. smt. qed.
lemma gcd6 t v : gcd t v = gcd (t - v) v. smt. qed.


op div_by2s (i : int) : int.
axiom div_by2s1 u : 0 < u = 0 < (div_by2s u).
axiom div_by2s2 u v : odd v => gcd (div_by2s u) v = gcd u v.
axiom div_by2s3 u : odd (div_by2s u).
axiom div_by2s4 u : 0 < u => !odd u =>  (div_by2s u) < u.
axiom div_by2s5 u : u < 0 => !odd u =>  u < (div_by2s u).
axiom div_by2s6 u : !odd u =>  div_by2s (u %/ 2) = div_by2s u.
axiom div_by2s7 u : odd u =>  div_by2s u = u.
