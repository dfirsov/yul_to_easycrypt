require import AllCore Int IntDiv.
require import Gcd Gcd_props.

require import AlmostYUL.
require import Montgomery_arith.



op add_x' (x1 x2 y1 y2 : int) =  let slope = (y2 - y1) * inv P (x2 - x1) in (slope * slope - (x1 + x2)).
op add_y' (x1 x2 y1 y2 : int) =  let slope = (y2 - y1) * inv P (x2 - x1) in
                           (slope * (x1 - (slope * slope - (x1 + x2))) - y1).



op add_x (x y : int) =  let slope = 3 * (x ^ 2) * inv P (2 * y) in (slope ^ 2 - (2 * x)).
op add_y (x y : int) =  let slope = 3 * (x ^ 2) * inv P (2 * y) in
                        let x3 = add_x x y in (slope  * (x - x3) - y).



op pIsInfinity (xy : int * int) = xy.`1 = 0 /\ xy.`2 = 0.

op ecAdd (x1 y1 x2 y2 : int) : (int * int) =
  let p1Infinity = (x1 = 0 /\ y1 = 0) in
  let p2Infinity = (x2 = 0 /\ y2 = 0) in
  let p1IsOnCurve = pointIsInCurve x1 y1 in
  let p2IsOnCurve = pointIsInCurve x2 y2 in 
 
  if p1Infinity /\ p2Infinity then (0,0)
  else if !p1Infinity /\ p2Infinity /\ p1IsOnCurve then (x1,y1)
      else if p1Infinity /\ !p2Infinity /\ p2IsOnCurve then (x2,y2)
      else if x1 = x2 /\ y2 = (P - y1) %% P /\ p1IsOnCurve /\ p2IsOnCurve then (0,0)
      else if x1 = x2 /\ y2 = y1 /\ p1IsOnCurve then (add_x x1 y1 %% P,add_y x1 y1 %% P)
      else if p1IsOnCurve /\ p2IsOnCurve then (add_x' x1 x2 y1 y2 %% P, add_y' x1 x2 y1 y2 %% P)
      else (witness, witness).


   
 
