pragma Goals:printall.
require import AllCore Int IntDiv.

op R2_MOD_P : int.
op R, P, N' : int.


axiom ax1 : 2 * P < R.
axiom ax2 : 0 < P.
axiom ax3 :  N' * P %% R = (-1) %% R.
axiom ax4 :  coprime P R.
axiom ax4_1 :  coprime R P.
axiom R_pos : 0 < R. 
axiom ax5 : 0 <= R2_MOD_P < P.
axiom ax6 : R2_MOD_P = (R * R) %% P.
axiom ax7 : 2 < P.
axiom ax9 : odd P.
axiom ax10 : odd R2_MOD_P.
axiom P_prime : prime P.


op inv (x : int) : int = invm x P.
axiom inv_ax u v : gcd u v = 1 => (inv v) * v %% u = 1.
axiom nosmt inv_ax_opp u v : gcd u v = 1 => v * (inv v) %% u = 1. 
