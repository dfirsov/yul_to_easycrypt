require import AllCore Int IntDiv.

op R2_MOD_P : int.
op R, N, N' : int.

op getHighestHalfOfMultiplication (a b : int) : int = (a * b) %/ R.


module AlmostYul = {


  proc overflowingAdd(augend : int, addend : int, R : int) : int * bool = {
    var sum <- (augend + addend) %% R;
    return (sum, sum < augend);
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
      ret <@ _REDC(m, 0, R, N, N');
      return ret;
  } 

  proc intoMontgomeryForm(a : int) : int = {
      var ret, hi, lo;

      hi <- getHighestHalfOfMultiplication a R2_MOD_P;
      lo <- (a * R2_MOD_P) %% R;
      ret <@ _REDC(lo, hi, R, N, N');
    
      return ret;
  }

  proc montgomeryAdd(augend : int, addend : int) : int = {
    var ret;
    ret <- (augend + addend) %% R;
    ret <- if N <= ret then (ret - N) %% R else ret;
    return ret;
  }


  proc montgomerySub(minuend : int, subtrahend : int) : int = {
      var ret;
      ret <@ montgomeryAdd(minuend, (N - subtrahend) %% R);
      return ret;
  }

  proc montgomeryMul(multiplicand : int, multiplier : int) : int = {
    var higherHalfOfProduct, lowestHalfOfProduct, ret;
    
    higherHalfOfProduct <- getHighestHalfOfMultiplication multiplicand multiplier;
    lowestHalfOfProduct <- (multiplicand * multiplier) %% R;
    ret <@ _REDC(lowestHalfOfProduct, higherHalfOfProduct, R, N, N');
    return ret;
  }

}.
