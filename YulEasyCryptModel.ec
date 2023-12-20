type memory, uint256.

op mload : memory * uint256 -> uint256.
op mstore : memory * uint256 * uint256 -> memory.
op keccak256 : memory * uint256 * uint256 -> uint256.

op add : uint256 * uint256 -> uint256.
op mul : uint256 * uint256 -> uint256.
op div : uint256 * uint256 -> uint256.
op mod : uint256 * uint256 -> uint256.
op or : uint256 * uint256 -> uint256.
op lt : uint256 * uint256 -> uint256.
op gt : uint256 * uint256 -> uint256.
op eq : uint256 * uint256 -> uint256.
op and : uint256 * uint256 -> uint256.
op shl : uint256 * uint256 -> uint256.
op shr : uint256 * uint256 -> uint256.

op iszero :  uint256 -> uint256.
op addmod : uint256 * uint256 * uint256 -> uint256.


op gas : uint256.

op sub : uint256 * uint256 -> uint256.


op [!] : int -> uint256.
op as_bool : uint256 -> bool.
