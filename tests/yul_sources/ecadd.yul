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
