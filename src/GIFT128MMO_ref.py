#GIFT128_ref.pyから関数を呼び出す
from GIFT128_ref import encrypt


pt  = 0xe39c141fa57dba43f08a85b6a91f86c1
key = 0xd0f5c59a7700d3e799028fa9f90ad837
round_num = 40
print('gift128の暗号化：',encrypt(pt, key, round_num))


#MMOモードのハッシュ関数
def gift128_mmo_hash(chain_value, message, round_num):
    # 1. 暗号化を実行 (余計な int() 変換はここではしない)
    crypto = encrypt(message, chain_value, round_num)
    
    # 2. crypto の型をチェックして、確実に整数(int)にする
    if isinstance(crypto, str):
        crypto_int = int(crypto, 16)  # 文字列なら16進数として変換
    else:
        crypto_int = int(crypto)      # すでに整数ならそのまま
        
    # 3. message の型をチェックして、確実に整数(int)にする
    if isinstance(message, str):
        msg_int = int(message, 16)    # 文字列なら16進数として変換
    else:
        msg_int = int(message)        # すでに整数ならそのまま
        
    # 4. 整数同士で安全に XOR 計算
    mmo_hash = crypto_int ^ msg_int
    
    # 5. ゼロ埋めされた32文字の16進数文字列として返す
    return format(mmo_hash, '032x')

print('gift128-mmoのハッシュ値：',gift128_mmo_hash(pt, key, round_num))