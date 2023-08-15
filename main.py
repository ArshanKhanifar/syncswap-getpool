import json

from eth_utils import to_checksum_address
from web3 import Web3, HTTPProvider


def main():
    web3 = Web3(HTTPProvider('https://mainnet.era.zksync.io'))
    b = web3.eth.get_block_number()
    addr = to_checksum_address('0xf2DAd89f2788a8CD54625C60b55cD3d2D0ACa7Cb')
    with open("compiled/syncswap_sol_SyncSwapClassicPoolFactory.abi", 'r') as f:
        pool_abi = json.load(f)
    c = web3.eth.contract(address=addr, abi=pool_abi)
    pool_a = to_checksum_address('0x3355df6D4c9C3035724Fd0e3914dE96A5a83aaf4')
    pool_b = to_checksum_address('0x5aea5775959fbc2557cc8789bc1bf90a239d9a91')
    pool = c.caller().getPool(pool_a, pool_b)
    print(f"pool: {pool}")


if __name__ == '__main__':
    main()
