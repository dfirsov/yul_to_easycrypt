require import AllCore Int IntDiv.


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



}.
