// SPDX-License-Identifier: GPL-3.0

pragma solidity >=0.8.2 <0.9.0;

/**
 * @title Storage
 * @dev Store & retrieve value in a variable
 * @custom:dev-run-script ./scripts/deploy_with_ethers.ts
 */
contract Tester {

    function test1() public pure  returns (uint256){
        assembly {


            function P() -> ret {
                ret := 21888242871839275222246405745257275088696311157297823662689037894645226208583
            }

	    function binaryExtendedEuclideanAlgorithm_version2(u, v) -> inv {
		let u2 := 0
		let u3 := u
		let t2 := 1
		let t3 := v

		for {} iszero (and (t3, 1)) {} {
		    switch iszero(and (t2, 1))
		    case 1{

			t2 := shr(1,t2)
			t3 := shr(1,t3)
		}default{
			t2 := shr(1,add(t2,u))
			t3 := shr(1,t3)
		}
		}

		let v2 := t2
		let v3 := t3
		t2 := v2
		t3 := sub(u3,v3)


		for {} iszero(eq(u3,v3)) {} {
		    for {} iszero (and (t3, 1)){} {
			switch iszero(and(t2,1))
			case 1{
			    t2 := shr(1,t2)
			    t3 := shr(1,t3)
			}default{
			    t2 := shr(1,add(t2,u))
			    t3 := shr(1,t3)
		       }
		     }

		    switch lt(v3, u3) 
		    case 1 {
		       u2 := t2
		       u3 := t3
		    }default {   
			v2 := t2
			v3 := t3         
		    }

		    t2 := add(u2,v2)
		    if gt(t2,u) {
			t2 := sub(t2, u)
		     }

		    switch gt(u3,v3)
		    case 1{
			t3 := sub(u3, v3)
		    }default {
			t3 := sub(v3, u3)
		    }
		}          

		inv := sub(u, u2)
	    }


	    let x := binaryExtendedEuclideanAlgorithm_version2(P(),1234)
	    mstore(0,x)
	    return(0,32)       
    }



}

    function test2() public pure  returns (uint256){
	    assembly {


	 function P() -> ret {
	     ret := 21888242871839275222246405745257275088696311157297823662689037894645226208583
	 }

	 function binaryExtendedEuclideanAlgorithm(modulus,base) -> inv {
		    let u := base
		    let v := modulus
		    // Avoids unnecessary reduction step.
		    let b := 1
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

	       let x := binaryExtendedEuclideanAlgorithm(P(),1234)
	       mstore(0,x)
	       return(0,32)




	 }
    }
}
