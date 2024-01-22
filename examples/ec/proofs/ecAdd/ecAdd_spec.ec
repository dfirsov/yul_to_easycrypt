require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.
require import Montgomery_arith.
require import Parameters.


op pointIsInfinity (x y : int) = x = 0 /\ y = 0.
op pointIsInCurve  (x y : int) = (y * y) %% P = (x * x * x + 3) %% P.


(* definition of valid input  *)
op valid_ecAdd_input (x1 y1 x2 y2) = 
            x1 < P
         /\ y1 < P
         /\ x2 < P
         /\ y2 < P
         /\ (!pointIsInfinity x1 y1 => pointIsInCurve x1 y1)
         /\ (!pointIsInfinity x2 y2 => pointIsInCurve x2 y2).


op add_eq_x (x1 x2 y1 y2 : int) =  let slope = (y2 - y1) * inv (x2 - x1) in (slope * slope - (x1 + x2)).
op add_eq_y (x1 x2 y1 y2 : int) =  let slope = (y2 - y1) * inv (x2 - x1) in
                           (slope * (x1 - (slope * slope - (x1 + x2))) - y1).



op add_diff_x (x y : int) =  let slope = 3 * (x ^ 2) * inv (2 * y) in (slope ^ 2 - (2 * x)).
op add_diff_y (x y : int) =  let slope = 3 * (x ^ 2) * inv (2 * y) in
                        let x3 = add_diff_x x y in (slope  * (x - x3) - y).


op ecAdd (x1 y1 x2 y2 : int) : ((int * int) option) =
  let p1Infinity = (x1 = 0 /\ y1 = 0) in
  let p2Infinity = (x2 = 0 /\ y2 = 0) in
  let p1IsOnCurve = pointIsInCurve x1 y1 in
  let p2IsOnCurve = pointIsInCurve x2 y2 in 
 
  if p1Infinity /\ p2Infinity then Some (0,0)
  else if !p1Infinity /\ p2Infinity /\ p1IsOnCurve then Some (x1,y1)
      else if p1Infinity /\ !p2Infinity /\ p2IsOnCurve then Some (x2,y2)
      else if x1 = x2 /\ y2 = (P - y1) %% P /\ p1IsOnCurve /\ p2IsOnCurve then Some (0,0)
      else if x1 = x2 /\ y2 = y1 /\ p1IsOnCurve then Some (add_diff_x x1 y1 %% P,add_diff_y x1 y1 %% P)
      else if p1IsOnCurve /\ p2IsOnCurve then Some (add_eq_x x1 x2 y1 y2 %% P, add_eq_y x1 x2 y1 y2 %% P)
      else None.


