// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.0;









/// @notice The manager contract to control fees.
/// Management functions are omitted.
interface IFeeManager {
    function getSwapFee(
        address pool,
        address sender,
        address tokenIn,
        address tokenOut,
        bytes calldata data) external view returns (uint24);
    function getProtocolFee(address pool) external view returns (uint24);
    function getFeeRecipient() external view returns (address);
}




interface IForwarderRegistry {
    function isForwarder(address forwarder) external view returns (bool);
}

/// @dev The master contract to create pools and manage whitelisted factories.
/// Inheriting the fee manager interface to support fee queries.
interface IPoolMaster is IFeeManager, IForwarderRegistry {
    event SetFactoryWhitelisted(address indexed factory, bool whitelisted);

    event RegisterPool(
        address indexed factory,
        address indexed pool,
        uint16 indexed poolType,
        bytes data
    );

    event UpdateForwarderRegistry(address indexed newForwarderRegistry);

    event UpdateFeeManager(address indexed newFeeManager);

    function vault() external view returns (address);

    function feeManager() external view returns (address);

    function pools(uint) external view returns (address);

    function poolsLength() external view returns (uint);

    // Forwarder Registry
    function setForwarderRegistry(address) external;

    // Fees
    function setFeeManager(address) external;

    // Factories
    function isFactoryWhitelisted(address) external view returns (bool);

    function setFactoryWhitelisted(address factory, bool whitelisted) external;

    // Pools
    function isPool(address) external view returns (bool);

    function getPool(bytes32) external view returns (address);

    function createPool(address factory, bytes calldata data) external returns (address pool);

    function registerPool(address pool, uint16 poolType, bytes calldata data) external;
}








interface IERC20Base {
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint amount) external returns (bool);
    function transfer(address to, uint amount) external returns (bool);
    function transferFrom(address from, address to, uint amount) external returns (bool);

    event Approval(address indexed owner, address indexed spender, uint amount);
    event Transfer(address indexed from, address indexed to, uint amount);
}

interface IERC20 is IERC20Base {
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
}













interface IPoolFactory {
    function master() external view returns (address);

    function getDeployData() external view returns (bytes memory);

    function createPool(bytes calldata data) external returns (address pool);
}

interface IBasePoolFactory is IPoolFactory {
    event PoolCreated(
        address indexed token0,
        address indexed token1,
        address pool
    );

    function getPool(address tokenA, address tokenB) external view returns (address pool);

    function getSwapFee(
        address pool,
        address sender,
        address tokenIn,
        address tokenOut,
        bytes calldata data
    ) external view returns (uint24 swapFee);
}


error InvalidTokens();

abstract contract BasePoolFactory is IBasePoolFactory {
    /// @dev The pool master that control fees and registry.
    address public immutable master;

    /// @dev Pools by its two pool tokens.
    mapping(address => mapping(address => address)) public override getPool;

    bytes internal cachedDeployData;

    constructor(address _master) {
        master = _master;
    }

    function getDeployData() external view override returns (bytes memory deployData) {
        deployData = cachedDeployData;
    }

    function getSwapFee(
        address pool,
        address sender,
        address tokenIn,
        address tokenOut,
        bytes calldata data
    ) external view override returns (uint24 swapFee) {
        swapFee = IPoolMaster(master).getSwapFee(pool, sender, tokenIn, tokenOut, data);
    }

    function createPool(bytes calldata data) external override returns (address pool) {
        (address tokenA, address tokenB) = abi.decode(data, (address, address));

        // Perform safety checks.
        if (tokenA == tokenB) {
            revert InvalidTokens();
        }

        // Sort tokens.
        if (tokenB < tokenA) {
            (tokenA, tokenB) = (tokenB, tokenA);
        }
        if (tokenA == address(0)) {
            revert InvalidTokens();
        }

        // Underlying implementation to deploy the pools and register them.
        pool = _createPool(tokenA, tokenB);

        // Populate mapping in both directions.
        // Not necessary as existence of the master, but keep them for better compatibility.
        getPool[tokenA][tokenB] = pool;
        getPool[tokenB][tokenA] = pool;

        emit PoolCreated(tokenA, tokenB, pool);
    }

    function _createPool(address tokenA, address tokenB) internal virtual returns (address) {
    }
}









/// @dev Math functions.
/// @dev Modified from Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/utils/FixedPointMathLib.sol)
library Math {

    /// @notice Compares a and b and returns 'true' if the difference between a and b
    /// is less than 1 or equal to each other.
    /// @param a uint256 to compare with.
    /// @param b uint256 to compare with.
    function within1(uint256 a, uint256 b) internal pure returns (bool) {
        unchecked {
            if (a > b) {
                return a - b <= 1;
            }
            return b - a <= 1;
        }
    }

    /// @dev Returns the square root of `x`.
    function sqrt(uint256 x) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // `floor(sqrt(2**15)) = 181`. `sqrt(2**15) - 181 = 2.84`.
            z := 181 // The "correct" value is 1, but this saves a multiplication later.

            // This segment is to get a reasonable initial estimate for the Babylonian method. With a bad
            // start, the correct # of bits increases ~linearly each iteration instead of ~quadratically.

            // Let `y = x / 2**r`.
            // We check `y >= 2**(k + 8)` but shift right by `k` bits
            // each branch to ensure that if `x >= 256`, then `y >= 256`.
            let r := shl(7, lt(0xffffffffffffffffffffffffffffffffff, x))
            r := or(r, shl(6, lt(0xffffffffffffffffff, shr(r, x))))
            r := or(r, shl(5, lt(0xffffffffff, shr(r, x))))
            r := or(r, shl(4, lt(0xffffff, shr(r, x))))
            z := shl(shr(1, r), z)

            // Goal was to get `z*z*y` within a small factor of `x`. More iterations could
            // get y in a tighter range. Currently, we will have y in `[256, 256*(2**16))`.
            // We ensured `y >= 256` so that the relative difference between `y` and `y+1` is small.
            // That's not possible if `x < 256` but we can just verify those cases exhaustively.

            // Now, `z*z*y <= x < z*z*(y+1)`, and `y <= 2**(16+8)`, and either `y >= 256`, or `x < 256`.
            // Correctness can be checked exhaustively for `x < 256`, so we assume `y >= 256`.
            // Then `z*sqrt(y)` is within `sqrt(257)/sqrt(256)` of `sqrt(x)`, or about 20bps.

            // For `s` in the range `[1/256, 256]`, the estimate `f(s) = (181/1024) * (s+1)`
            // is in the range `(1/2.84 * sqrt(s), 2.84 * sqrt(s))`,
            // with largest error when `s = 1` and when `s = 256` or `1/256`.

            // Since `y` is in `[256, 256*(2**16))`, let `a = y/65536`, so that `a` is in `[1/256, 256)`.
            // Then we can estimate `sqrt(y)` using
            // `sqrt(65536) * 181/1024 * (a + 1) = 181/4 * (y + 65536)/65536 = 181 * (y + 65536)/2**18`.

            // There is no overflow risk here since `y < 2**136` after the first branch above.
            z := shr(18, mul(z, add(shr(r, x), 65536))) // A `mul()` is saved from starting `z` at 181.

            // Given the worst case multiplicative error of 2.84 above, 7 iterations should be enough.
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))

            // If `x+1` is a perfect square, the Babylonian method cycles between
            // `floor(sqrt(x))` and `ceil(sqrt(x))`. This statement ensures we return floor.
            // See: https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division
            // Since the ceil is rare, we save gas on the assignment and repeat division in the rare case.
            // If you don't care whether the floor or ceil square root is returned, you can remove this statement.
            z := sub(z, lt(div(x, z), z))
        }
    }

    // Mul Div

    /// @dev Rounded down.
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require(denominator != 0 && (x == 0 || (x * y) / x == y))
            if iszero(and(iszero(iszero(denominator)), or(iszero(x), eq(div(z, x), y)))) {
                revert(0, 0)
            }

            // Divide z by the denominator.
            z := div(z, denominator)
        }
    }

    /// @dev Rounded down.
    /// This function assumes that `x` is not zero, and must be checked externally.
    function mulDivUnsafeFirst(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require(denominator != 0 && (x * y) / x == y)
            if iszero(and(iszero(iszero(denominator)), eq(div(z, x), y))) {
                revert(0, 0)
            }

            // Divide z by the denominator.
            z := div(z, denominator)
        }
    }

    /// @dev Rounded down.
    /// This function assumes that `denominator` is not zero, and must be checked externally.
    function mulDivUnsafeLast(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require(x == 0 || (x * y) / x == y)
            if iszero(or(iszero(x), eq(div(z, x), y))) {
                revert(0, 0)
            }

            // Divide z by the denominator.
            z := div(z, denominator)
        }
    }

    /// @dev Rounded down.
    /// This function assumes that both `x` and `denominator` are not zero, and must be checked externally.
    function mulDivUnsafeFirstLast(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require((x * y) / x == y)
            if iszero(eq(div(z, x), y)) {
                revert(0, 0)
            }

            // Divide z by the denominator.
            z := div(z, denominator)
        }
    }

    // Mul

    /// @dev Optimized safe multiplication operation for minimal gas cost.
    /// Equivalent to *
    function mul(
        uint256 x,
        uint256 y
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require(x == 0 || (x * y) / x == y)
            if iszero(or(iszero(x), eq(div(z, x), y))) {
                revert(0, 0)
            }
        }
    }

    /// @dev Optimized unsafe multiplication operation for minimal gas cost.
    /// This function assumes that `x` is not zero, and must be checked externally.
    function mulUnsafeFirst(
        uint256 x,
        uint256 y
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require((x * y) / x == y)
            if iszero(eq(div(z, x), y)) {
                revert(0, 0)
            }
        }
    }

    // Div

    /// @dev Optimized safe division operation for minimal gas cost.
    /// Equivalent to /
    function div(
        uint256 x,
        uint256 y
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := div(x, y)

            // Equivalent to require(y != 0)
            if iszero(y) {
                revert(0, 0)
            }
        }
    }

    /// @dev Optimized unsafe division operation for minimal gas cost.
    /// Division by 0 will not reverts and returns 0, and must be checked externally.
    function divUnsafeLast(
        uint256 x,
        uint256 y
    ) internal pure returns (uint256 z) {
        assembly {
            z := div(x, y)
        }
    }
}








interface IERC165 {
    /// @notice Query if a contract implements an interface
    /// @param interfaceID The interface identifier, as specified in ERC-165
    /// @dev Interface identification is specified in ERC-165. This function
    ///  uses less than 30,000 gas.
    /// @return `true` if the contract implements `interfaceID` and
    ///  `interfaceID` is not 0xffffffff, `false` otherwise
    function supportsInterface(bytes4 interfaceID) external view returns (bool);
}










interface IERC20Permit is IERC20 {
    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;
    function nonces(address owner) external view returns (uint);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

interface IERC20Permit2 is IERC20Permit {
    function permit2(address owner, address spender, uint amount, uint deadline, bytes calldata signature) external;
}









/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 *
 * Based on OpenZeppelin's ECDSA library.
 * https://github.com/OpenZeppelin/openzeppelin-contracts/blob/561d1061fc568f04c7a65853538e834a889751e8/contracts/utils/cryptography/ECDSA.sol
 */
library ECDSA {

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature` or error string. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        // Check the signature length
        if (signature.length != 65) {
            return address(0);
        }

        // Divide the signature in r, s and v variables
        bytes32 r;
        bytes32 s;
        uint8 v;

        // ecrecover takes the signature parameters, and the only way to get them
        // currently is to use assembly.
        /// @solidity memory-safe-assembly
        // solhint-disable-next-line no-inline-assembly
        assembly {
            r := mload(add(signature, 0x20))
            s := mload(add(signature, 0x40))
            v := byte(0, mload(add(signature, 0x60)))
        }

        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return address(0);
        }

        return ecrecover(hash, v, r, s);
    }
}

/**
 * @dev Signature verification helper that can be used instead of `ECDSA.recover` to seamlessly support both ECDSA
 * signatures from externally owned accounts (EOAs) as well as ERC1271 signatures from smart contract wallets like
 * Argent and Gnosis Safe.
 *
 * Based on OpenZeppelin's SignatureChecker library.
 * https://github.com/OpenZeppelin/openzeppelin-contracts/blob/561d1061fc568f04c7a65853538e834a889751e8/contracts/utils/cryptography/SignatureChecker.sol
 */
library SignatureChecker {

    bytes4 constant internal MAGICVALUE = 0x1626ba7e; // bytes4(keccak256("isValidSignature(bytes32,bytes)")

    /**
     * @dev Checks if a signature is valid for a given signer and data hash. If the signer is a smart contract, the
     * signature is validated against that smart contract using ERC1271, otherwise it's validated using `ECDSA.recover`.
     *
     * NOTE: Unlike ECDSA signatures, contract signatures are revocable, and the outcome of this function can thus
     * change through time. It could return true at block N and false at block N+1 (or the opposite).
     */
    function isValidSignatureNow(
        address signer,
        bytes32 hash,
        bytes memory signature
    ) internal view returns (bool) {
        (address recovered) = ECDSA.recover(hash, signature);
        if (recovered == signer) {
            if (recovered != address(0)) {
                return true;
            }
        }

        (bool success, bytes memory result) = signer.staticcall(
            abi.encodeWithSelector(MAGICVALUE, hash, signature)
        );
        return (
            success &&
            result.length == 32 &&
            abi.decode(result, (bytes32)) == bytes32(MAGICVALUE)
        );
    }
}

error Expired();
error InvalidSignature();

/**
 * @dev A simple ERC20 implementation for pool's liquidity token, supports permit by both ECDSA signatures from
 * externally owned accounts (EOAs) as well as ERC1271 signatures from smart contract wallets like Argent.
 *
 * Based on Solmate's ERC20.
 * https://github.com/transmissions11/solmate/blob/bff24e835192470ed38bf15dbed6084c2d723ace/src/tokens/ERC20.sol
 */
contract ERC20Permit2 is IERC165, IERC20Permit2 {
    uint8 public immutable override decimals = 18;

    uint public override totalSupply;
    mapping(address => uint) public override balanceOf;
    mapping(address => mapping(address => uint)) public override allowance;

    bytes32 private constant PERMIT_TYPEHASH = 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9; // keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")
    mapping(address => uint) public override nonces;

    // These members are actually immutable as
    // `_initialize` will only indent to be called once.
    string public override name;
    string public override symbol;
    uint private INITIAL_CHAIN_ID;
    bytes32 private INITIAL_DOMAIN_SEPARATOR;

    function _initialize(string memory _name, string memory _symbol) internal {
        name = _name;
        symbol = _symbol;

        INITIAL_CHAIN_ID = block.chainid;
        INITIAL_DOMAIN_SEPARATOR = _computeDomainSeparator();
    }

    function supportsInterface(bytes4 interfaceID) external pure override returns (bool) {
        return
            interfaceID == this.supportsInterface.selector || // ERC-165
            interfaceID == this.permit.selector || // ERC-2612
            interfaceID == this.permit2.selector; // Permit2
    }

    function DOMAIN_SEPARATOR() public view override returns (bytes32) {
        return block.chainid == INITIAL_CHAIN_ID ? INITIAL_DOMAIN_SEPARATOR : _computeDomainSeparator();
    }

    function _computeDomainSeparator() private view returns (bytes32) {
        return keccak256(
            abi.encode(
                // keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
                0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f,
                keccak256(bytes(name)),
                // keccak256(bytes("1"))
                0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6,
                block.chainid,
                address(this)
            )
        );
    }

    function _approve(address _owner, address _spender, uint _amount) private {
        allowance[_owner][_spender] = _amount;
        emit Approval(_owner, _spender, _amount);
    }

    function approve(address _spender, uint _amount) public override returns (bool) {
        _approve(msg.sender, _spender, _amount);
        return true;
    }

    function transfer(address _to, uint _amount) public override returns (bool) {
        balanceOf[msg.sender] -= _amount;

        // Cannot overflow because the sum of all user balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[_to] += _amount;
        }

        emit Transfer(msg.sender, _to, _amount);
        return true;
    }

    function transferFrom(address _from, address _to, uint _amount) public override returns (bool) {
        uint256 _allowed = allowance[_from][msg.sender]; // Saves gas for limited approvals.
        if (_allowed != type(uint).max) {
            allowance[_from][msg.sender] = _allowed - _amount;
        }

        balanceOf[_from] -= _amount;
        // Cannot overflow because the sum of all user balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[_to] += _amount;
        }

        emit Transfer(_from, _to, _amount);
        return true;
    }

    function _mint(address _to, uint _amount) internal {
        totalSupply += _amount;

        // Cannot overflow because the sum of all user balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[_to] += _amount;
        }

        emit Transfer(address(0), _to, _amount);
    }

    function _burn(address _from, uint _amount) internal {
        balanceOf[_from] -= _amount;

        // Cannot underflow because a user's balance will never be larger than the total supply.
        unchecked {
            totalSupply -= _amount;
        }

        emit Transfer(_from, address(0), _amount);
    }

    modifier ensures(uint _deadline) {
        // solhint-disable-next-line not-rely-on-time
        if (block.timestamp > _deadline) {
            revert Expired();
        }
        _;
    }

    function _permitHash(
        address _owner,
        address _spender,
        uint _amount,
        uint _deadline
    ) private returns (bytes32) {
        return keccak256(
            abi.encodePacked(
                "\x19\x01",
                DOMAIN_SEPARATOR(),
                keccak256(abi.encode(PERMIT_TYPEHASH, _owner, _spender, _amount, nonces[_owner]++, _deadline))
            )
        );
    }

    function permit(
        address _owner,
        address _spender,
        uint _amount,
        uint _deadline,
        uint8 _v,
        bytes32 _r,
        bytes32 _s
    ) public override ensures(_deadline) {
        bytes32 _hash = _permitHash(_owner, _spender, _amount, _deadline);
        address _recoveredAddress = ecrecover(_hash, _v, _r, _s);

        if (_recoveredAddress != _owner) {
            revert InvalidSignature();
        }
        if (_recoveredAddress == address(0)) {
            revert InvalidSignature();
        }

        _approve(_owner, _spender, _amount);
    }

    function permit2(
        address _owner,
        address _spender,
        uint _amount,
        uint _deadline,
        bytes calldata _signature
    ) public override ensures(_deadline) {
        bytes32 _hash = _permitHash(_owner, _spender, _amount, _deadline);

        if (!SignatureChecker.isValidSignatureNow(_owner, _hash, _signature)) {
            revert InvalidSignature();
        }

        _approve(_owner, _spender, _amount);
    }
}




library MetadataHelper {
    /**
     * @dev Returns symbol of the token.
     *
     * @param token The address of a ERC20 token.
     *
     * Return boolean indicating the status and the symbol as string;
     *
     * NOTE: Symbol is not the standard interface and some tokens may not support it.
     * Calling against these tokens will not success, with an empty result.
     */
    function getSymbol(address token) internal view returns (bool, string memory) {
        // bytes4(keccak256(bytes("symbol()")))
        (bool success, bytes memory returndata) = token.staticcall(abi.encodeWithSelector(0x95d89b41));
        if (success) {
            return (true, abi.decode(returndata, (string)));
        } else {
            return (false, "");
        }
    }
}

// OpenZeppelin Contracts (last updated v4.8.0) (security/ReentrancyGuard.sol)



/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}





/// @dev The callback interface for SyncSwap base pool operations.
/// Note additional checks will be required for some callbacks, see below for more information.
/// Visit the documentation https://syncswap.gitbook.io/api-documentation/ for more details.
interface ICallback {

    struct BaseMintCallbackParams {
        address sender;
        address to;
        uint reserve0;
        uint reserve1;
        uint balance0;
        uint balance1;
        uint amount0;
        uint amount1;
        uint fee0;
        uint fee1;
        uint newInvariant;
        uint oldInvariant;
        uint totalSupply;
        uint liquidity;
        uint24 swapFee;
        bytes callbackData;
    }
    function syncSwapBaseMintCallback(BaseMintCallbackParams calldata params) external;

    struct BaseBurnCallbackParams {
        address sender;
        address to;
        uint balance0;
        uint balance1;
        uint liquidity;
        uint totalSupply;
        uint amount0;
        uint amount1;
        uint8 withdrawMode;
        bytes callbackData;
    }
    function syncSwapBaseBurnCallback(BaseBurnCallbackParams calldata params) external;

    struct BaseBurnSingleCallbackParams {
        address sender;
        address to;
        address tokenIn;
        address tokenOut;
        uint balance0;
        uint balance1;
        uint liquidity;
        uint totalSupply;
        uint amount0;
        uint amount1;
        uint amountOut;
        uint amountSwapped;
        uint feeIn;
        uint24 swapFee;
        uint8 withdrawMode;
        bytes callbackData;
    }
    /// @dev Note the `tokenOut` parameter can be decided by the caller, and the correctness is not guaranteed.
    /// Additional checks MUST be performed in callback to ensure the `tokenOut` is one of the pools tokens if the sender
    /// is not a trusted source to avoid potential issues.
    function syncSwapBaseBurnSingleCallback(BaseBurnSingleCallbackParams calldata params) external;

    struct BaseSwapCallbackParams {
        address sender;
        address to;
        address tokenIn;
        address tokenOut;
        uint reserve0;
        uint reserve1;
        uint balance0;
        uint balance1;
        uint amountIn;
        uint amountOut;
        uint feeIn;
        uint24 swapFee;
        uint8 withdrawMode;
        bytes callbackData;
    }
    /// @dev Note the `tokenIn` parameter can be decided by the caller, and the correctness is not guaranteed.
    /// Additional checks MUST be performed in callback to ensure the `tokenIn` is one of the pools tokens if the sender
    /// is not a trusted source to avoid potential issues.
    function syncSwapBaseSwapCallback(BaseSwapCallbackParams calldata params) external;
}












// Inspired by Aave Protocol's IFlashLoanReceiver.

interface IFlashLoanRecipient {
    /**
     * @dev When `flashLoan` is called on the Vault, it invokes the `receiveFlashLoan` hook on the recipient.
     *
     * At the time of the call, the Vault will have transferred `amounts` for `tokens` to the recipient. Before this
     * call returns, the recipient must have transferred `amounts` plus `feeAmounts` for each token back to the
     * Vault, or else the entire flash loan will revert.
     *
     * `userData` is the same value passed in the `IVault.flashLoan` call.
     */
    function receiveFlashLoan(
        address[] memory tokens,
        uint[] memory amounts,
        uint[] memory feeAmounts,
        bytes memory userData
    ) external;
}








interface IERC3156FlashBorrower {
    /**
     * @dev Receive a flash loan.
     * @param initiator The initiator of the loan.
     * @param token The loan currency.
     * @param amount The amount of tokens lent.
     * @param fee The additional amount of tokens to repay.
     * @param data Arbitrary data structure, intended to contain user-defined parameters.
     * @return The keccak256 hash of "ERC3156FlashBorrower.onFlashLoan"
     */
    function onFlashLoan(
        address initiator,
        address token,
        uint256 amount,
        uint256 fee,
        bytes calldata data
    ) external returns (bytes32);
}

interface IERC3156FlashLender {
    /**
     * @dev The amount of currency available to be lent.
     * @param token The loan currency.
     * @return The amount of `token` that can be borrowed.
     */
    function maxFlashLoan(
        address token
    ) external view returns (uint256);

    /**
     * @dev The fee to be charged for a given loan.
     * @param token The loan currency.
     * @param amount The amount of tokens lent.
     * @return The amount of `token` to be charged for the loan, on top of the returned principal.
     */
    function flashFee(
        address token,
        uint256 amount
    ) external view returns (uint256);

    /**
     * @dev Initiate a flash loan.
     * @param receiver The receiver of the tokens in the loan, and the receiver of the callback.
     * @param token The loan currency.
     * @param amount The amount of tokens lent.
     * @param data Arbitrary data structure, intended to contain user-defined parameters.
     */
    function flashLoan(
        IERC3156FlashBorrower receiver,
        address token,
        uint256 amount,
        bytes calldata data
    ) external returns (bool);
}

interface IFlashLoan is IERC3156FlashLender {
    function flashLoanFeePercentage() external view returns (uint);

    /**
     * @dev Performs a 'flash loan', sending tokens to `recipient`, executing the `receiveFlashLoan` hook on it,
     * and then reverting unless the tokens plus a proportional protocol fee have been returned.
     *
     * The `tokens` and `amounts` arrays must have the same length, and each entry in these indicates the loan amount
     * for each token contract. `tokens` must be sorted in ascending order.
     *
     * The 'userData' field is ignored by the Vault, and forwarded as-is to `recipient` as part of the
     * `receiveFlashLoan` call.
     *
     * Emits `FlashLoan` events.
     */
    function flashLoanMultiple(
        IFlashLoanRecipient recipient,
        address[] memory tokens,
        uint[] memory amounts,
        bytes memory userData
    ) external;

    /**
     * @dev Emitted for each individual flash loan performed by `flashLoan`.
     */
    event FlashLoan(address indexed recipient, address indexed token, uint amount, uint feeAmount);
}

interface IVault is IFlashLoan {
    function wETH() external view returns (address);

    function reserves(address token) external view returns (uint reserve);

    function balanceOf(address token, address owner) external view returns (uint balance);

    function deposit(address token, address to) external payable returns (uint amount);

    function depositETH(address to) external payable returns (uint amount);

    function transferAndDeposit(address token, address to, uint amount) external payable returns (uint);

    function transfer(address token, address to, uint amount) external;

    function withdraw(address token, address to, uint amount) external;

    function withdrawAlternative(address token, address to, uint amount, uint8 mode) external;

    function withdrawETH(address to, uint amount) external;
}












interface IPool {
    struct TokenAmount {
        address token;
        uint amount;
    }

    /// @dev Returns the address of pool master.
    function master() external view returns (address);

    /// @dev Returns the vault.
    function vault() external view returns (address);

    /// @dev Returns the pool type.
    function poolType() external view returns (uint16);

    /// @dev Returns the assets of the pool.
    function getAssets() external view returns (address[] memory assets);

    /// @dev Returns the swap fee of the pool.
    function getSwapFee(address sender, address tokenIn, address tokenOut, bytes calldata data) external view returns (uint24 swapFee);

    /// @dev Returns the protocol fee of the pool.
    function getProtocolFee() external view returns (uint24 protocolFee);

    /// @dev Mints liquidity.
    function mint(
        bytes calldata data,
        address sender,
        address callback,
        bytes calldata callbackData
    ) external returns (uint liquidity);

    /// @dev Burns liquidity.
    function burn(
        bytes calldata data,
        address sender,
        address callback,
        bytes calldata callbackData
    ) external returns (TokenAmount[] memory tokenAmounts);

    /// @dev Burns liquidity with single output token.
    function burnSingle(
        bytes calldata data,
        address sender,
        address callback,
        bytes calldata callbackData
    ) external returns (TokenAmount memory tokenAmount);

    /// @dev Swaps between tokens.
    function swap(
        bytes calldata data,
        address sender,
        address callback,
        bytes calldata callbackData
    ) external returns (TokenAmount memory tokenAmount);
}


interface IBasePool is IPool, IERC20Permit2 {
    function token0() external view returns (address);
    function token1() external view returns (address);

    function reserve0() external view returns (uint);
    function reserve1() external view returns (uint);
    function invariantLast() external view returns (uint);

    function getReserves() external view returns (uint, uint);
    function getAmountOut(address tokenIn, uint amountIn, address sender) external view returns (uint amountOut);
    function getAmountIn(address tokenOut, uint amountOut, address sender) external view returns (uint amountIn);

    event Mint(
        address indexed sender,
        uint amount0,
        uint amount1,
        uint liquidity,
        address indexed to
    );

    event Burn(
        address indexed sender,
        uint amount0,
        uint amount1,
        uint liquidity,
        address indexed to
    );

    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );

    event Sync(
        uint reserve0,
        uint reserve1
    );
}

interface IClassicPool is IBasePool {
}





interface IFeeRecipient {
    /// @dev Notifies the fee recipient after sent fees.
    function notifyFees(
        uint16 feeType,
        address token,
        uint amount,
        uint feeRate,
        bytes calldata data
    ) external;
}


error Overflow();
error InsufficientLiquidityMinted();

contract SyncSwapClassicPool is IClassicPool, ERC20Permit2, ReentrancyGuard {
    using Math for uint;

    uint private constant MINIMUM_LIQUIDITY = 1000;
    uint private constant MAX_FEE = 1e5; /// @dev 100%.

    /// @dev Pool type `1` for classic pools.
    uint16 public constant override poolType = 1;

    address public immutable override master;
    address public immutable override vault;

    address public immutable override token0;
    address public immutable override token1;

    /// @dev Pool reserve of each pool token as of immediately after the most recent balance event.
    /// The value is used to measure growth in invariant on mints and input tokens on swaps.
    uint public override reserve0;
    uint public override reserve1;

    /// @dev Invariant of the pool as of immediately after the most recent liquidity event.
    /// The value is used to measure growth in invariant when protocol fee is enabled,
    /// and will be reset to zero if protocol fee is disabled.
    uint public override invariantLast;

    /// @dev Factory must ensures that the parameters are valid.
    constructor() {
        (bytes memory _deployData) = IPoolFactory(msg.sender).getDeployData();
        (address _token0, address _token1) = abi.decode(_deployData, (address, address));
        address _master = IPoolFactory(msg.sender).master();

        master = _master;
        vault = IPoolMaster(_master).vault();
        (token0, token1) = (_token0, _token1);

        // try to set symbols for the LP token
        (bool _success0, string memory _symbol0) = MetadataHelper.getSymbol(_token0);
        (bool _success1, string memory _symbol1) = MetadataHelper.getSymbol(_token1);
        if (_success0 && _success1) {
            _initialize(
                string(abi.encodePacked("SyncSwap ", _symbol0, "/", _symbol1, " Classic LP")),
                string(abi.encodePacked(_symbol0, "/", _symbol1, " cSLP"))
            );
        } else {
            _initialize(
                "SyncSwap Classic LP",
                "cSLP"
            );
        }
    }

    function getAssets() external view override returns (address[] memory assets) {
        assets = new address[](2);
        assets[0] = token0;
        assets[1] = token1;
    }

    /// @dev Returns the verified sender address otherwise `address(0)`.
    function _getVerifiedSender(address _sender) private view returns (address) {
        if (_sender != address(0)) {
            if (_sender != msg.sender) {
                if (!IPoolMaster(master).isForwarder(msg.sender)) {
                    // The sender from non-forwarder is invalid.
                    return address(0);
                }
            }
        }
        return _sender;
    }

    /// @dev Mints LP tokens - should be called via the router after transferring pool tokens.
    /// The router should ensure that sufficient LP tokens are minted.
    function mint(
        bytes calldata _data,
        address _sender,
        address _callback,
        bytes calldata _callbackData
    ) external override nonReentrant returns (uint) {
        ICallback.BaseMintCallbackParams memory params;

        params.to = abi.decode(_data, (address));
        (params.reserve0, params.reserve1) = (reserve0, reserve1);
        (params.balance0, params.balance1) = _balances();

        params.newInvariant = _computeInvariant(params.balance0, params.balance1);
        params.amount0 = params.balance0 - params.reserve0;
        params.amount1 = params.balance1 - params.reserve1;
        //require(_amount0 != 0 && _amount1 != 0);

        // Gets swap fee for the sender.
        _sender = _getVerifiedSender(_sender);
        uint _amount1Optimal = params.reserve0 == 0 ? 0 : (params.amount0 * params.reserve1) / params.reserve0;
        bool _swap0For1 = params.amount1 < _amount1Optimal;
        if (_swap0For1) {
            params.swapFee = _getSwapFee(_sender, token0, token1);
        } else {
            params.swapFee = _getSwapFee(_sender, token1, token0);
        }

        // Adds mint fee to reserves (applies to invariant increase) if unbalanced.
        (params.fee0, params.fee1) = _unbalancedMintFee(params.swapFee, params.amount0, params.amount1, _amount1Optimal, params.reserve0, params.reserve1);
        params.reserve0 += params.fee0;
        params.reserve1 += params.fee1;

        // Calculates old invariant (where unbalanced fee added to) and, mint protocol fee if any.
        params.oldInvariant = _computeInvariant(params.reserve0, params.reserve1);
        bool _feeOn;
        (_feeOn, params.totalSupply) = _mintProtocolFee(0, 0, params.oldInvariant);

        if (params.totalSupply == 0) {
            params.liquidity = params.newInvariant - MINIMUM_LIQUIDITY;
            _mint(address(0), MINIMUM_LIQUIDITY); // permanently lock on first mint.
        } else {
            // Calculates liquidity proportional to invariant growth.
            params.liquidity = ((params.newInvariant - params.oldInvariant) * params.totalSupply) / params.oldInvariant;
        }

        // Mints liquidity for recipient.
        if (params.liquidity == 0) {
            revert InsufficientLiquidityMinted();
        }
        _mint(params.to, params.liquidity);

        // Calls callback with data.
        if (_callback != address(0)) {
            // Fills additional values for callback params.
            params.sender = _sender;
            params.callbackData = _callbackData;

            ICallback(_callback).syncSwapBaseMintCallback(params);
        }

        // Updates reserves and last invariant with new balances.
        _updateReserves(params.balance0, params.balance1);
        if (_feeOn) {
            invariantLast = params.newInvariant;
        }

        emit Mint(msg.sender, params.amount0, params.amount1, params.liquidity, params.to);

        return params.liquidity;
    }

    /// @dev Burns LP tokens sent to this contract.
    /// The router should ensure that sufficient pool tokens are received.
    function burn(
        bytes calldata _data,
        address _sender,
        address _callback,
        bytes calldata _callbackData
    ) external override nonReentrant returns (TokenAmount[] memory _amounts) {
        ICallback.BaseBurnCallbackParams memory params;

        (params.to, params.withdrawMode) = abi.decode(_data, (address, uint8));
        (params.balance0, params.balance1) = _balances();
        params.liquidity = balanceOf[address(this)];

        // Mints protocol fee if any.
        // Note `_mintProtocolFee` here will checks overflow.
        bool _feeOn;
        (_feeOn, params.totalSupply) = _mintProtocolFee(params.balance0, params.balance1, 0);

        // Calculates amounts of pool tokens proportional to balances.
        params.amount0 = params.liquidity * params.balance0 / params.totalSupply;
        params.amount1 = params.liquidity * params.balance1 / params.totalSupply;
        //require(_amount0 != 0 || _amount1 != 0);

        // Burns liquidity and transfers pool tokens.
        _burn(address(this), params.liquidity);
        _transferTokens(token0, params.to, params.amount0, params.withdrawMode);
        _transferTokens(token1, params.to, params.amount1, params.withdrawMode);

        // Updates balances.
        /// @dev Cannot underflow because amounts are lesser figures derived from balances.
        unchecked {
            params.balance0 -= params.amount0;
            params.balance1 -= params.amount1;
        }

        // Calls callback with data.
        // Note reserves are not updated at this point to allow read the old values.
        if (_callback != address(0)) {
            // Fills additional values for callback params.
            params.sender = _getVerifiedSender(_sender);
            params.callbackData = _callbackData;

            ICallback(_callback).syncSwapBaseBurnCallback(params);
        }

        // Updates reserves and last invariant with up-to-date balances (after transfers).
        _updateReserves(params.balance0, params.balance1);
        if (_feeOn) {
            invariantLast = _computeInvariant(params.balance0, params.balance1);
        }

        _amounts = new TokenAmount[](2);
        _amounts[0] = TokenAmount(token0, params.amount0);
        _amounts[1] = TokenAmount(token1, params.amount1);

        emit Burn(msg.sender, params.amount0, params.amount1, params.liquidity, params.to);
    }

    /// @dev Burns LP tokens sent to this contract and swaps one of the output tokens for another
    /// - i.e., the user gets a single token out by burning LP tokens.
    /// The router should ensure that sufficient pool tokens are received.
    function burnSingle(
        bytes calldata _data,
        address _sender,
        address _callback,
        bytes calldata _callbackData
    ) external override nonReentrant returns (TokenAmount memory _tokenAmount) {
        ICallback.BaseBurnSingleCallbackParams memory params;

        (params.tokenOut, params.to, params.withdrawMode) = abi.decode(_data, (address, address, uint8));
        (params.balance0, params.balance1) = _balances();
        params.liquidity = balanceOf[address(this)];

        // Mints protocol fee if any.
        // Note `_mintProtocolFee` here will checks overflow.
        bool _feeOn;
        (_feeOn, params.totalSupply) = _mintProtocolFee(params.balance0, params.balance1, 0);

        // Calculates amounts of pool tokens proportional to balances.
        params.amount0 = params.liquidity * params.balance0 / params.totalSupply;
        params.amount1 = params.liquidity * params.balance1 / params.totalSupply;

        // Burns liquidity.
        _burn(address(this), params.liquidity);

        // Gets swap fee for the sender.
        _sender = _getVerifiedSender(_sender);

        // Swaps one token for another, transfers desired tokens, and update context values.
        /// @dev Calculate `amountOut` as if the user first withdrew balanced liquidity and then swapped from one token for another.
        if (params.tokenOut == token1) {
            // Swaps `token0` for `token1`.
            params.swapFee = _getSwapFee(_sender, token0, token1);

            params.tokenIn = token0;
            (params.amountSwapped, params.feeIn) = _getAmountOut(
                params.swapFee, params.amount0, params.balance0 - params.amount0, params.balance1 - params.amount1, true
            );
            params.amount1 += params.amountSwapped;

            _transferTokens(token1, params.to, params.amount1, params.withdrawMode);
            params.amountOut = params.amount1;
            params.amount0 = 0;
            params.balance1 -= params.amount1;
        } else {
            // Swaps `token1` for `token0`.
            //require(_tokenOut == token0);
            params.swapFee = _getSwapFee(_sender, token1, token0);

            params.tokenIn = token1;
            (params.amountSwapped, params.feeIn) = _getAmountOut(
                params.swapFee, params.amount1, params.balance0 - params.amount0, params.balance1 - params.amount1, false
            );
            params.amount0 += params.amountSwapped;

            _transferTokens(token0, params.to, params.amount0, params.withdrawMode);
            params.amountOut = params.amount0;
            params.amount1 = 0;
            params.balance0 -= params.amount0;
        }

        // Calls callback with data.
        // Note reserves are not updated at this point to allow read the old values.
        if (_callback != address(0)) {
            // Fills additional values for callback params.
            params.sender = _sender;
            params.callbackData = _callbackData;

            /// @dev Note the `tokenOut` parameter can be decided by the caller, and the correctness is not guaranteed.
            /// Additional checks MUST be performed in callback to ensure the `tokenOut` is one of the pools tokens if the sender
            /// is not a trusted source to avoid potential issues.
            ICallback(_callback).syncSwapBaseBurnSingleCallback(params);
        }

        // Update reserves and last invariant with up-to-date balances (updated above).
        _updateReserves(params.balance0, params.balance1);
        if (_feeOn) {
            invariantLast = _computeInvariant(params.balance0, params.balance1);
        }

        _tokenAmount = TokenAmount(params.tokenOut, params.amountOut);

        emit Burn(msg.sender, params.amount0, params.amount1, params.liquidity, params.to);
    }

    /// @dev Swaps one token for another - should be called via the router after transferring input tokens.
    /// The router should ensure that sufficient output tokens are received.
    function swap(
        bytes calldata _data,
        address _sender,
        address _callback,
        bytes calldata _callbackData
    ) external override nonReentrant returns (TokenAmount memory _tokenAmount) {
        ICallback.BaseSwapCallbackParams memory params;

        (params.tokenIn, params.to, params.withdrawMode) = abi.decode(_data, (address, address, uint8));
        (params.reserve0, params.reserve1) = (reserve0, reserve1);
        (params.balance0, params.balance1) = _balances();

        // Gets swap fee for the sender.
        _sender = _getVerifiedSender(_sender);

        // Calculates output amount, update context values and emit event.
        if (params.tokenIn == token0) {
            params.swapFee = _getSwapFee(_sender, token0, token1);

            params.tokenOut = token1;
            params.amountIn = params.balance0 - params.reserve0;

            (params.amountOut, params.feeIn) = _getAmountOut(params.swapFee, params.amountIn, params.reserve0, params.reserve1, true);
            params.balance1 -= params.amountOut;

            emit Swap(msg.sender, params.amountIn, 0, 0, params.amountOut, params.to);
        } else {
            //require(params.tokenIn == token1);
            params.swapFee = _getSwapFee(_sender, token1, token0);

            params.tokenOut = token0;
            params.amountIn = params.balance1 - params.reserve1;

            (params.amountOut, params.feeIn) = _getAmountOut(params.swapFee, params.amountIn, params.reserve0, params.reserve1, false);
            params.balance0 -= params.amountOut;

            emit Swap(msg.sender, 0, params.amountIn, params.amountOut, 0, params.to);
        }

        // Checks overflow.
        if (params.balance0 > type(uint128).max) {
            revert Overflow();
        }
        if (params.balance1 > type(uint128).max) {
            revert Overflow();
        }

        // Transfers output tokens.
        _transferTokens(params.tokenOut, params.to, params.amountOut, params.withdrawMode);

        // Calls callback with data.
        if (_callback != address(0)) {
            // Fills additional values for callback params.
            params.sender = _sender;
            params.callbackData = _callbackData;

            /// @dev Note the `tokenIn` parameter can be decided by the caller, and the correctness is not guaranteed.
            /// Additional checks MUST be performed in callback to ensure the `tokenIn` is one of the pools tokens if the sender
            /// is not a trusted source to avoid potential issues.
            ICallback(_callback).syncSwapBaseSwapCallback(params);
        }

        // Updates reserves with up-to-date balances (updated above).
        _updateReserves(params.balance0, params.balance1);

        _tokenAmount.token = params.tokenOut;
        _tokenAmount.amount = params.amountOut;
    }

    function _getSwapFee(address _sender, address _tokenIn, address _tokenOut) private view returns (uint24 _swapFee) {
        _swapFee = getSwapFee(_sender, _tokenIn, _tokenOut, "");
    }

    /// @dev This function doesn't check the forwarder.
    function getSwapFee(address _sender, address _tokenIn, address _tokenOut, bytes memory data) public view override returns (uint24 _swapFee) {
        _swapFee = IPoolMaster(master).getSwapFee(address(this), _sender, _tokenIn, _tokenOut, data);
    }

    function getProtocolFee() public view override returns (uint24 _protocolFee) {
        _protocolFee = IPoolMaster(master).getProtocolFee(address(this));
    }

    function _updateReserves(uint _balance0, uint _balance1) private {
        (reserve0, reserve1) = (_balance0, _balance1);
        emit Sync(_balance0, _balance1);
    }

    function _transferTokens(address token, address to, uint amount, uint8 withdrawMode) private {
        if (withdrawMode == 0) {
            IVault(vault).transfer(token, to, amount);
        } else {
            IVault(vault).withdrawAlternative(token, to, amount, withdrawMode);
        }
    }

    function _balances() private view returns (uint balance0, uint balance1) {
        balance0 = IVault(vault).balanceOf(token0, address(this));
        balance1 = IVault(vault).balanceOf(token1, address(this));
    }

    /// @dev This fee is charged to cover for the swap fee when users adding unbalanced liquidity.
    function _unbalancedMintFee(
        uint _swapFee,
        uint _amount0,
        uint _amount1,
        uint _amount1Optimal,
        uint _reserve0,
        uint _reserve1
    ) private pure returns (uint _token0Fee, uint _token1Fee) {
        if (_reserve0 == 0) {
            return (0, 0);
        }
        if (_amount1 >= _amount1Optimal) {
            _token1Fee = (_swapFee * (_amount1 - _amount1Optimal)) / (2 * MAX_FEE);
        } else {
            uint _amount0Optimal = (_amount1 * _reserve0) / _reserve1;
            _token0Fee = (_swapFee * (_amount0 - _amount0Optimal)) / (2 * MAX_FEE);
        }
    }

    function _mintProtocolFee(uint _reserve0, uint _reserve1, uint _invariant) private returns (bool _feeOn, uint _totalSupply) {
        _totalSupply = totalSupply;

        address _feeRecipient = IPoolMaster(master).getFeeRecipient();
        _feeOn = (_feeRecipient != address(0));

        uint _invariantLast = invariantLast;
        if (_invariantLast != 0) {
            if (_feeOn) {
                if (_invariant == 0) {
                    _invariant = _computeInvariant(_reserve0, _reserve1);
                }

                if (_invariant > _invariantLast) {
                    /// @dev Mints `protocolFee` % of growth in liquidity (invariant).
                    uint _protocolFee = getProtocolFee();
                    uint _numerator = _totalSupply * (_invariant - _invariantLast) * _protocolFee;
                    uint _denominator = (MAX_FEE - _protocolFee) * _invariant + _protocolFee * _invariantLast;
                    uint _liquidity = _numerator / _denominator;

                    if (_liquidity != 0) {
                        _mint(_feeRecipient, _liquidity);

                        // Notifies the fee recipient.
                        IFeeRecipient(_feeRecipient).notifyFees(1, address(this), _liquidity, _protocolFee, "");

                        _totalSupply += _liquidity; // update cached value.
                    }
                }
            } else {
                /// @dev Resets last invariant to clear measured growth if protocol fee is not enabled.
                invariantLast = 0;
            }
        }
    }

    function getReserves() external view override returns (uint _reserve0, uint _reserve1) {
        (_reserve0, _reserve1) = (reserve0, reserve1);
    }

    function getAmountOut(address _tokenIn, uint _amountIn, address _sender) external view override returns (uint _amountOut) {
        (uint _reserve0, uint _reserve1) = (reserve0, reserve1);
        bool _swap0For1 = _tokenIn == token0;
        address _tokenOut = _swap0For1 ? token1 : token0;
        (_amountOut,) = _getAmountOut(_getSwapFee(_sender, _tokenIn, _tokenOut), _amountIn, _reserve0, _reserve1, _swap0For1);
    }

    function getAmountIn(address _tokenOut, uint _amountOut, address _sender) external view override returns (uint _amountIn) {
        (uint _reserve0, uint _reserve1) = (reserve0, reserve1);
        bool _swap1For0 = _tokenOut == token0;
        address _tokenIn = _swap1For0 ? token1 : token0;
        _amountIn = _getAmountIn(_getSwapFee(_sender, _tokenIn, _tokenOut), _amountOut, _reserve0, _reserve1, _swap1For0);
    }

    function _getAmountOut(
        uint _swapFee,
        uint _amountIn,
        uint _reserve0,
        uint _reserve1,
        bool _token0In
    ) private pure returns (uint _dy, uint _feeIn) {
        if (_amountIn == 0) {
            _dy = 0;
        } else {
            uint _amountInWithFee = _amountIn * (MAX_FEE - _swapFee);
            _feeIn = _amountIn * _swapFee / MAX_FEE;

            if (_token0In) {
                _dy = (_amountInWithFee * _reserve1) / (_reserve0 * MAX_FEE + _amountInWithFee);
            } else {
                _dy = (_amountInWithFee * _reserve0) / (_reserve1 * MAX_FEE + _amountInWithFee);
            }
        }
    }

    function _getAmountIn(
        uint _swapFee,
        uint _amountOut,
        uint _reserve0,
        uint _reserve1,
        bool _token0Out
    ) private pure returns (uint _dx) {
        if (_amountOut == 0) {
            _dx = 0;
        } else {
            if (_token0Out) {
                _dx = (_reserve1 * _amountOut * MAX_FEE) / ((_reserve0 - _amountOut) * (MAX_FEE - _swapFee)) + 1;
            } else {
                _dx = (_reserve0 * _amountOut * MAX_FEE) / ((_reserve1 - _amountOut) * (MAX_FEE - _swapFee)) + 1;
            }
        }
    }

    function _computeInvariant(uint _reserve0, uint _reserve1) private pure returns (uint _invariant) {
        if (_reserve0 > type(uint128).max) {
            revert Overflow();
        }
        if (_reserve1 > type(uint128).max) {
            revert Overflow();
        }
        _invariant = (_reserve0 * _reserve1).sqrt();
    }
}

contract SyncSwapClassicPoolFactory is BasePoolFactory {
    constructor(address _master) BasePoolFactory(_master) {
    }

    function _createPool(address token0, address token1) internal override returns (address pool) {
        // Perform sanity checks.
        IERC20(token0).balanceOf(address(this));
        IERC20(token1).balanceOf(address(this));

        bytes memory deployData = abi.encode(token0, token1);
        cachedDeployData = deployData;

        // The salt is same with deployment data.
        bytes32 salt = keccak256(deployData);
        pool = address(new SyncSwapClassicPool{salt: salt}()); // this will prevent duplicated pools.

        // Register the pool. The config is same with deployment data.
        IPoolMaster(master).registerPool(pool, 1, deployData);
    }
}

