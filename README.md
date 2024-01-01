# Yul to EasyCrypt transpiler

Work in progress: We implement a converter for a subset of Yul language to EasyCrypt module system.

# Setup

```
python3 -m venv yul2ec-env
source yul2ec-env/bin/activate
pip3 install antlr4-python3-runtime
pip3 install bigtree
```

# Running

`python3 yul2ec.py source.yul target.ec`


# Example: Modular inversion 

* `examples/modular_inversion/proofs/gcd.ec` EasyCrypt implementation and proofs of correctness for binary Euclidean algorithm.
* `examples/modular_inversion/proofs/ext_gcd.ec` modular inversion by extended binary Euclidean algorithm (Bézout's identity and GCD) in EasyCrypt.
* `examples/modular_inversion/proofs/ext_gcd_optmized.ec` gradual optimizations of extended binary Euclidean algorithm.
* `examples/modular_inversion/sources/` YUL and Python implementation of modular inversion.

# Example: Montgomery addition


```
 object "EcAdd_deployed" {
     code {

            function P() -> ret {
                ret := 21888242871839275222246405745257275088696311157297823662689037894645226208583
            }

            function montgomeryAdd(augend, addend) -> ret {
                ret := add(augend, addend)
                if iszero(lt(ret, P())) {
                    ret := sub(ret, P())
                }
            }

     }
 }
```

The above function gets transpiled into the following EasyCrypt module:

```
require import AllCore.
require import YulEasyCryptModel.



module YulExtract = {
    var m : memory
 
    proc lt(v1: uint256, v2 : uint256) : uint256 = {
      return lt(v1,v2);  
    }

    proc sub(v1: uint256, v2 : uint256) : uint256 = {
      return lt(v1,v2);  
    }

   proc add(v1: uint256, v2 : uint256) : uint256 = {
      return lt(v1,v2);  
    }


    proc iszero(v1: uint256) : uint256 = {
      return iszero(v1);  
    }


    proc _P() : (uint256) = { 
        var ret;
        ret <- !21888242871839275222246405745257275088696311157297823662689037894645226208583;
        return ret;
    }
    proc montgomeryAdd(augend: uint256, addend: uint256) : (uint256) = { 
        var ret, func15, func17, func21, func28;
        ret <@ add(augend,addend);
        func21 <@ _P();
        func17 <@ lt(ret,func21);
        func15 <@ iszero(func17);
        if(as_bool func15){
            func28 <@ _P();
            ret <@ sub(ret,func28);
        }
        return ret;
    }
}.
```
