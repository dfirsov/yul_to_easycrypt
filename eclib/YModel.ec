(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap Ring List StdOrder Bool.
(*---*) import CoreMap Map Ring.IntID IntOrder.
require export YUtils YArray YWord YMemory.

(* op (\comp) ['a 'b 'c] : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c = fun f g a => g (f a). *)

op MLOAD  : global_mem_t -> address -> W256.t = loadW256.
op MSTORE : global_mem_t -> address -> W256.t -> global_mem_t = storeW256.
op ADD : W256.t -> W256.t -> W256.t = W256.(+).
op MUL : W256.t -> W256.t -> W256.t = W256.( * ).
op DIV : W256.t -> W256.t -> W256.t = W256.\udiv.
op MOD : W256.t -> W256.t -> W256.t = W256.\umod.
op OR : W256.t -> W256.t -> W256.t = W256.(`|`).
op AND : W256.t -> W256.t -> W256.t = W256.(`&`).
op LT : W256.t -> W256.t -> bool = W256.\ult.
op LE : W256.t -> W256.t -> bool = W256.\ule.
op GT : W256.t -> W256.t -> bool = fun w1 w2 => ! (LE w1 w2).
op EQ : W256.t -> W256.t -> bool = (=).
op SHL : int -> W256.t -> W256.t = fun i w => W256.(`<<<`) w i.
op SHR : int -> W256.t -> W256.t = fun i w => W256.(`>>>`) w i.










lemma q a b : ADD a b = ADD b a.
smt. qed.

lemma w a b : to_uint (ADD a b) = (to_uint a + to_uint b) %% W256.modulus.
rewrite /ADD. rewrite /(+). rewrite /ulift2. smt. qed.
    

op KECCAK256 : global_mem_t -> address -> address -> W256.t.


{-


op iszero :  uint256 -> uint256.
op addmod : uint256 * uint256 * uint256 -> uint256.


op gas : uint256.

op sub : uint256 * uint256 -> uint256.
-}
