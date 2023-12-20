 object "EcAdd_deployed" {
     code {

            function MONTGOMERY_THREE() -> m_three {
                m_three := 19052624634359457937016868847204597229365286637454337178037183604060995791063
            }

            /// @notice Constant function for the alt_bn128 field order.
            /// @dev See https://eips.ethereum.org/EIPS/eip-196 for further details.
            /// @return ret The alt_bn128 field order.
            function P() -> ret {
                ret := 21888242871839275222246405745257275088696311157297823662689037894645226208583
            }


            function R2_MOD_P() -> ret {
                ret := 3096616502983703923843567936837374451735540968419076528771170197431451843209
            }


            function N_PRIME() -> ret {
                ret := 111032442853175714102588374283752698368366046808579839647964533820976443843465
            }


            function binaryExtendedEuclideanAlgorithm(base) -> inv {
                let modulus := P()
                let u := base
                let v := modulus
                // Avoids unnecessary reduction step.
                let b := R2_MOD_P()
                let c := 0

                for {} and(iszero(eq(u, 1)), iszero(eq(v, 1))) {} {
                    for {} iszero(and(u, 1)) {} {
                        u := shr(1, u)
                        let current := b
                        switch and(current, 1)
                        case 0 {
                            b := shr(1, b)
                        }
                        case 1 {
                            b := shr(1, add(b, modulus))
                        }
                    }

                    for {} iszero(and(v, 1)) {} {
                        v := shr(1, v)
                        let current := c
                        switch and(current, 1)
                        case 0 {
                            c := shr(1, c)
                        }
                        case 1 {
                            c := shr(1, add(c, modulus))
                        }
                    }

                    switch gt(v, u)
                    case 0 {
                        u := sub(u, v)
                        if lt(b, c) {
                            b := add(b, modulus)
                        }
                        b := sub(b, c)
                    }
                    case 1 {
                        v := sub(v, u)
                        if lt(c, b) {
                            c := add(c, modulus)
                        }
                        c := sub(c, b)
                    }
                }

                switch eq(u, 1)
                case 0 {
                    inv := c
                }
                case 1 {
                    inv := b
                }
            }


 }
}
