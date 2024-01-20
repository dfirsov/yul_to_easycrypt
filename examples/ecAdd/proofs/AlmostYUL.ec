require import AllCore Int IntDiv.

require import Parameters.


op getHighestHalfOfMultiplication (a b : int) : int = (a * b) %/ R.
op as_bool (b : bool) = b.


module AlmostYul = {

  proc skipf() : unit = {}

  proc addmod(a : int, b : int, modulus : int) : int = {
    var sum <- (a + b) %% R  %% modulus;
    return sum;
  }

  proc submod(minuend : int, subtrahend : int, modulus : int) : int = {
    var difference;
    difference <@ addmod(minuend, (modulus - subtrahend) %% R, modulus);
    return difference;
  }

  proc getHighestHalfOfMultiplication(a : int, b : int) : int = {
   return getHighestHalfOfMultiplication a b; 
  }

  proc overflowingAdd(augend : int, addend : int, R : int) : int * bool = {
    var sum <- (augend + addend) %% R;
    return (sum, sum < augend);
  }


   proc isInfinity(x : int, y : int) : bool = {
       return x = 0 /\ y = 0;
   }

  proc isOnFieldOrder(coordinate : int) : bool = {
      return coordinate < P;
  }




  proc _REDC(Tlo : int, Thi : int, R : int, N : int, N' : int) = {
    var m, hi, lo, s, tmp, overflowed;
    m <- (Tlo * N') %% R;
    hi <- (Thi + ((m * N) %/ R)) %% R;
    tmp <- (m * N) %% R;
    (lo, overflowed) <@ overflowingAdd(Tlo, tmp, R);
    if (overflowed) {
      hi <- (hi + 1) %% R;
    }
    s <- hi;
    if (N <= hi){
      s <- (hi - N) %% R;
    }
    return s;
  } 


  proc outOfMontgomeryForm(m : int) : int = {
      var ret;
      ret <@ _REDC(m, 0, R, P, N');
      return ret;
  } 

  proc intoMontgomeryForm(a : int) : int = {
      var ret, hi, lo;
      hi <- getHighestHalfOfMultiplication a R2_MOD_P;
      lo <- (a * R2_MOD_P) %% R;
      ret <@ _REDC(lo, hi, R, P, N');    
      return ret;
  }

  proc montgomeryAdd(augend : int, addend : int) : int = {
    var ret;
    ret <- (augend + addend) %% R;
    ret <- if P <= ret then (ret - P) %% R else ret;
    return ret;
  }


  proc montgomerySub(minuend : int, subtrahend : int) : int = {
      var ret;
      ret <@ montgomeryAdd(minuend, (P - subtrahend) %% R);
      return ret;
  }

  proc montgomeryMul(multiplicand : int, multiplier : int) : int = {
    var higherHalfOfProduct, lowestHalfOfProduct, ret;
    
    higherHalfOfProduct <- getHighestHalfOfMultiplication multiplicand multiplier;
    lowestHalfOfProduct <- (multiplicand * multiplier) %% R;
    ret <@ _REDC(lowestHalfOfProduct, higherHalfOfProduct, R, P, N');
    return ret;
  }



  proc simplify_ts_pos(t2:int,t3: int,u:int) = {
      while (!odd t3){
        if (!odd t2){
          (t2,t3) <- (t2 %/2, t3 %/2);
        }else{
          (t2,t3) <- ((t2+u) %% R %/2, t3 %/2);
        }
      }
      return (t2,t3);
  }


  proc binaryExtendedEuclideanAlgorithm(u : int, v : int, r : int) = {
    var u2,u3,v2,v3,t2,t3;

    (u2,u3) <- (0, u);
    (v2,v3) <- (r, v);
    (t2,t3) <- (r, v);

    (t2,t3) <@ simplify_ts_pos(t2, v, u);
    (v2, v3) <- (t2, t3);

    if (v3 < u3){
      t3 <- (u3 - v3) %% R;
    }else{
      t3 <- (v3 - u3) %% R;
    }
    t2 <- v2;

    while (t3 <> 0){
      (t2,t3) <@ simplify_ts_pos(t2, t3, u);

      if (v3 < u3){
        (u2, u3) <- (t2, t3);
      }else{
        (v2, v3) <- (t2, t3);
      }

      t2 <- u2 + v2;
      if (u <= t2){
          t2 <- (t2 - u) %% R;
      }else{
          t2 <- (u2 + v2) %% R;
      }

      if (v3 < u3){
        t3 <- (u3 - v3) %% R;
      }else{
        t3 <- (v3 - u3) %% R;
      }

     }
    return (u-u2) %% R;
  }


  proc montgomeryModularInverse(a : int) : int = {
    var invmod;
    invmod <@ binaryExtendedEuclideanAlgorithm(P,a,R2_MOD_P);
    return invmod;
  } 

 proc montgomeryDiv(dividend : int, divisor: int) : int = {
   var quotient, inverse;
   inverse  <@ montgomeryModularInverse(divisor);
   quotient <@ montgomeryMul(dividend, inverse);
   return quotient;
 }


 proc pointIsInCurve(x: int, y: int) : bool = {
  var ySquared, xSquared, xQubed, xQubedPlusThree;
  ySquared <@ montgomeryMul(y, y);
  xSquared <@ montgomeryMul(x, x);
  xQubed <@ montgomeryMul(xSquared, x);
  xQubedPlusThree <@ montgomeryAdd(xQubed, (3 * R) %% P);
  return (ySquared = xQubedPlusThree);    
 }

proc and(b1:bool, b2:bool) : bool = {
   return b1 /\ b2;
}


proc or(b1:bool, b2:bool) : bool = {
   return b1 \/ b2;
}

proc eq(b1:int, b2:int) : bool = {
   return b1 = b2;
}


proc iszero(b) : bool = {
   return !b;
}

proc burnGas() = {
  while(true){}
}

proc _P() : int = {
 return P;
}    


proc main(x1: int, y1: int, x2: int, y2: int) : int * int = { 
        var ret, p1IsInfinity, p2IsInfinity, func17, func43, func47, func53, func55, func57, func61, func63, m_x2, m_y2, func79, func81, func109, func111, func119, func121, func123, func127, func129, m_x1, m_y1, func145, func147, func175, func177, func179, func183, func185, func193, func195, func197, func201, func203, func211, func213, func219, func221, func227, func249, func251, func253, func259, func261, func289, func291, func297, func299, func301, func307, func309, func313, func319, func325, func327, func333, x, y, func349, func351, x1_squared, slope, func368, func372, func378, func380, func382, func388, x3, func392, func398, func404, func406, y3, func410, func414, func420, func424, func469, func471, func473, func479, func481, func492, func498, func500, func506, func510, func516, func522, func524, func528, func532, func538, func542, ret_bool;
        ret_bool <- false;

        p1IsInfinity <@ isInfinity(x1,y1);
        p2IsInfinity <@ isInfinity(x2,y2);
        func17 <@ and(p1IsInfinity,p2IsInfinity);
        if(as_bool func17){
            ret <- (0,0);
            ret_bool <- true;

        }

        if (!ret_bool){

        func47 <@ iszero(p2IsInfinity);
        func43 <@ and(p1IsInfinity,func47);
        if(as_bool func43){
            func57 <@ isOnFieldOrder(x2);
            func55 <@ iszero(func57);
            func63 <@ isOnFieldOrder(y2);
            func61 <@ iszero(func63);
            func53 <@ or(func55,func61);
            if(as_bool func53){
                burnGas();

            }
            m_x2 <@ intoMontgomeryForm(x2);
            m_y2 <@ intoMontgomeryForm(y2);
            func81 <@ pointIsInCurve(m_x2,m_y2);
            func79 <@ iszero(func81);
            if(as_bool func79){
                burnGas();

            }
            ret <- (x2,y2);
            ret_bool <- true;

        }

        if (!ret_bool) {

        func111 <@ iszero(p1IsInfinity);
        func109 <@ and(func111,p2IsInfinity);
        if(as_bool func109){
            func123 <@ isOnFieldOrder(x1);
            func121 <@ iszero(func123);
            func129 <@ isOnFieldOrder(y1);
            func127 <@ iszero(func129);
            func119 <@ or(func121,func127);
            if(as_bool func119){
                burnGas();

            }
            m_x1 <@ intoMontgomeryForm(x1);
            m_y1 <@ intoMontgomeryForm(y1);
            func147 <@ pointIsInCurve(m_x1,m_y1);
            func145 <@ iszero(func147);
            if(as_bool func145){
                burnGas();

            }
            ret <- (x1,y1);
            ret_bool <- true;

        }

        if (!ret_bool) {

        func179 <@ isOnFieldOrder(x1);
        func177 <@ iszero(func179);
        func185 <@ isOnFieldOrder(y1);
        func183 <@ iszero(func185);
        func175 <@ or(func177,func183);
        if(as_bool func175){
            burnGas();

        }
        func197 <@ isOnFieldOrder(x2);
        func195 <@ iszero(func197);
        func203 <@ isOnFieldOrder(y2);
        func201 <@ iszero(func203);
        func193 <@ or(func195,func201);
        if(as_bool func193){
            burnGas();

        }
        func213 <@ eq(x1,x2);
        func227 <@ _P();
        func221 <@ submod(0,y1,func227);
        func219 <@ eq(func221,y2);
        func211 <@ and(func213,func219);
        if(as_bool func211){
            m_x1 <@ intoMontgomeryForm(x1);
            m_y1 <@ intoMontgomeryForm(y1);
            m_x2 <@ intoMontgomeryForm(x2);
            m_y2 <@ intoMontgomeryForm(y2);
            func253 <@ pointIsInCurve(m_x1,m_y1);
            func251 <@ iszero(func253);
            func261 <@ pointIsInCurve(m_x2,m_y2);
            func259 <@ iszero(func261);
            func249 <@ or(func251,func259);
            if(as_bool func249){
                burnGas();

            }
            ret <- (0,0);
            ret_bool <- true;            
        }

        if (!ret_bool){

        func291 <@ eq(x1,x2);
        func301 <@ eq(y1,y2);
        func299 <@ iszero(func301);
        func319 <@ _P();
        func313 <@ submod(0,y2,func319);
        func309 <@ eq(y1,func313);
        func307 <@ iszero(func309);
        func297 <@ and(func299,func307);
        func289 <@ and(func291,func297);
        if(as_bool func289){
            burnGas();

        }
        func327 <@ eq(x1,x2);
        func333 <@ eq(y1,y2);
        func325 <@ and(func327,func333);
        if(as_bool func325){
            x <@ intoMontgomeryForm(x1);
            y <@ intoMontgomeryForm(y1);
            func351 <@ pointIsInCurve(x,y);
            func349 <@ iszero(func351);
            if(as_bool func349){
                burnGas();

            }
            x1_squared <@ montgomeryMul(x,x);
            func378 <@ _P();
            func372 <@ addmod(x1_squared,x1_squared,func378);
            func380 <@ _P();
            func368 <@ addmod(x1_squared,func372,func380);
            func388 <@ _P();
            func382 <@ addmod(y,y,func388);
            slope <@ montgomeryDiv(func368,func382);
            func392 <@ montgomeryMul(slope,slope);
            func404 <@ _P();
            func398 <@ addmod(x,x,func404);
            func406 <@ _P();
            x3 <@ submod(func392,func398,func406);
            func420 <@ _P();
            func414 <@ submod(x,x3,func420);
            func410 <@ montgomeryMul(slope,func414);
            func424 <@ _P();
            y3 <@ submod(func410,y,func424);
            x3 <@ outOfMontgomeryForm(x3);
            y3 <@ outOfMontgomeryForm(y3);

            ret <- (x3,y3);
            ret_bool <- true;
        }

        if (!ret_bool) {

        x1 <@ intoMontgomeryForm(x1);
        y1 <@ intoMontgomeryForm(y1);
        x2 <@ intoMontgomeryForm(x2);
        y2 <@ intoMontgomeryForm(y2);
        func473 <@ pointIsInCurve(x1,y1);
        func471 <@ iszero(func473);
        func481 <@ pointIsInCurve(x2,y2);
        func479 <@ iszero(func481);
        func469 <@ or(func471,func479);
        if(as_bool func469){
            burnGas();

        }
        func498 <@ _P();
        func492 <@ submod(y2,y1,func498);
        func506 <@ _P();
        func500 <@ submod(x2,x1,func506);
        slope <@ montgomeryDiv(func492,func500);
        func510 <@ montgomeryMul(slope,slope);
        func522 <@ _P();
        func516 <@ addmod(x1,x2,func522);
        func524 <@ _P();
        x3 <@ submod(func510,func516,func524);
        func538 <@ _P();
        func532 <@ submod(x1,x3,func538);
        func528 <@ montgomeryMul(slope,func532);
        func542 <@ _P();
        y3 <@ submod(func528,y1,func542);
        x3 <@ outOfMontgomeryForm(x3);
        y3 <@ outOfMontgomeryForm(y3);

        ret <- (x3,y3);

        }
        }
        }
        }
        }

        return ret;
    }

}.
