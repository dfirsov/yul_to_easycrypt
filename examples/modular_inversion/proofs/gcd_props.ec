require import Int IntDiv.

op even x = ! (odd x).

lemma odd_even u v : odd u => odd v => even (u - v).
proof. smt(@IntDiv). qed.

axiom gcd1 u v : even u => even v =>  gcd u v = 2 * gcd (u %/ 2) (v %/ 2).
axiom gcd2 u v : even u => odd v => gcd u v = gcd (u %/ 2) v.   
lemma gcd3 u v : gcd u v = gcd (u - v) v. smt. qed.
lemma gcd4 u v : gcd u v = gcd v u. smt. qed.
lemma gcd5 u v : gcd u v = gcd (-u) v. smt. qed.
lemma gcd6 t v : gcd t v = gcd (t - v) v. smt. qed.
