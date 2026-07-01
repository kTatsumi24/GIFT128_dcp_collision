#GIFT128_ref.pyから関数を呼び出す
from GIFT128_ref import encrypt


pt  = 0xe39c141fa57dba43f08a85b6a91f86c1
key = 0xd0f5c59a7700d3e799028fa9f90ad837
round_num = 40
print('gift128の暗号化：',encrypt(pt, key, round_num))


#MMOモードのハッシュ関数
def gift128_mmo_hash(chain_value, message, round_num):
    #F(H,M) = E(M,H) XOR M | E(M,H) : GIFT128の暗号化関数、鍵HでメッセージMを暗号化
    crypto = int(encrypt(message, chain_value, round_num), 16)
    mmo_hash = crypto ^ message
    return format(mmo_hash, '032x')

print('gift128-mmoのハッシュ値：',gift128_mmo_hash(pt, key, round_num))