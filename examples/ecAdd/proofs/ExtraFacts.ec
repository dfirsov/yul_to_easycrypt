require import Int IntDiv AllCore.

lemma nosmt even_fact (n a : int) : n - a = a => !odd n .
progress.
have : n = 2*a.
rewrite - H.    smt.
move => q. rewrite q. smt.
qed.    


lemma nosmt div_fact (a P : int) : 0 < a < P /\ 0 <= P => !(P %| a).
progress. smt(@Int @IntDiv dvdn_le). qed.



lemma nosmt div_fact2 (a P : int) : 1 < P => coprime P a => !(P %| a).
progress.
have ->: a = a * 1. smt().
case (P %| a * 1);auto.
move => q.
have : P %| 1.
    apply (Gauss P a 1).     auto. auto.
apply div_fact. progress. smt().
qed.    


lemma nosmt qqq (a b P : int) : (a - b) %% P = (a %% P - b %% P) %% P.
    smt(@Int @IntDiv). qed.



lemma nosmt oi (y1 y2 P : int) : prime P => 0 <= y1 < P /\ 0 <= y2 < P
  => y1 <> y2
  => 0 < y1 + y2
  => y1^2 %% P = y2^2 %% P
  => y1 %% P = (P - y2) %% P.
move => primeP. progress.
have fact1 : y1^2 %% P - y2^2 %% P = 0.    smt.
have  :  (y1^2  - y2^2) %% P  = 0. rewrite qqq. rewrite fact1. auto.
have  ->:  (y1^2  - y2^2) = (y1 - y2) * (y1 + y2). smt.
progress.
rewrite - dvdzE in H6.
have fact2 : P %| (y1 + y2). apply (Gauss P _ _ H6).
apply prime_coprime. smt. 
have : `|y1 - y2| < P. smt(@Int).
progress.
case ((y1 - y2) %% P = 0). 
move => oo.
have : `|y1 - y2| %% P = 0. smt (@Int @IntDiv).
progress. apply div_fact2. smt. apply prime_coprime. smt. smt.
auto.
have fact4 : exists k, (y1 + y2) = k * P.
     have d :   P %| (y1 + y2) <=> exists (q : int), y1 + y2 = q * P. apply (dvdzP P (y1 + y2)).
       elim d. progress. apply (H7 fact2).
elim fact4. progress.
have o1 : k = 1. smt.
have : P = y1 + y2. smt.
smt.
qed.



(* lemma nosmt mul_inj (a b r P : int) : coprime r P => 1 < P  *)
(*     => a * r %% P = b * r %% P => a %% P = b %% P. *)
(* move => coprime_h posP eq. *)
(*  have : a * r * (invm r P) %% P = b * r * (invm r P) %% P. *)
(*   have ->: (a * r) * (invm r P) %% P = (a * r %% P)  * (invm r P) %% P. *)
(*   smt(@IntDiv). *)
(*   rewrite eq. *)
(*   smt(@IntDiv). *)
(*   have ->: a * r * invm r P = a * (r * invm r P). smt(@IntDiv). *)
(*   have ->: b * r * invm r P = b * (r * invm r P). smt(@IntDiv). *)
(*   have ->: a * (r * invm r P) %% P = a * (r * invm r P %% P) %% P. *)
(*   smt(@IntDiv). *)
(*   have ->: b * (r * invm r P) %% P = b * (r * invm r P %% P) %% P. *)
(*   smt(@IntDiv). *)
(*   rewrite invmP. auto. auto. rewrite /coprime. smt(@IntDiv).  *)
(*   simplify. *)
(*   auto. *)
(* qed. *)

(* lemma nosmt mul_inj_contra_pos (a b r P : int) : coprime r P => 1 < P  *)
(*   => a %% P <> b %% P =>  a * r %% P <> b * r %% P. *)
(* proof. smt(mul_inj). qed. *)


