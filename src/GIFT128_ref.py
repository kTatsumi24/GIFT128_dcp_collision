#GIFT-128のリファレンス実装
#xx_128bits: 要素数128のビットを格納した一次元配列
#xx_hex: 16進数表記の文字列(32桁)
#nibble_list: 4ビットごとに分割した一次元配列(要素数32)

#Subcells s-boxの適用
def sbox(nibble_list, SBOX):
    state_subcells = [SBOX[nibble] for nibble in nibble_list]
    return state_subcells


def hex_2_128bits(state_hex):
    #1*128の配列に変換
    state_128bits = [0] * 128
    for i in range(32):
        nibble = state_hex[i]
        state_128bits[4*i + 0] = (nibble >> 0) & 1
        state_128bits[4*i + 1] = (nibble >> 1) & 1
        state_128bits[4*i + 2] = (nibble >> 2) & 1
        state_128bits[4*i + 3] = (nibble >> 3) & 1
    return state_128bits

#PermBits
def perm_bits(state_128bits, GIFT_P):
    state_permbits = [0] * 128
    for i in range(128):
        #元の状態のi番目を、置換表に従って新しい状態のGIFT_P[i]番目に置き換え
        state_permbits[GIFT_P[i]] = state_128bits[i]
    return state_permbits

#AddRoundKey: ラウンド鍵加算、ラウンド定数加算
def add_round_key(state_128bits, rk, rc):
    #ラウンド鍵の加算
    for i in range(32):
        # stateの (4*i + 1) ビット目に、鍵の i ビット目をXOR
        state_128bits[4 * i + 1] ^= rk[i]
        
        # stateの (4*i + 2) ビット目に、鍵の (i + 64) ビット目をXOR
        state_128bits[4 * i + 2] ^= rk[i + 64]

    #ラウンド定数の加算
    # rcの各ビット(0〜5ビット目)を、状態の特定の場所(4*i + 3)にXOR
    state_128bits[3]  ^= (rc >> 0) & 1
    state_128bits[7]  ^= (rc >> 1) & 1
    state_128bits[11] ^= (rc >> 2) & 1
    state_128bits[15] ^= (rc >> 3) & 1
    state_128bits[19] ^= (rc >> 4) & 1
    state_128bits[23] ^= (rc >> 5) & 1

    #ビット加算
    state_128bits[127] ^= 1
    return state_128bits


#鍵更新
def key_schedule(key_128bits):
    #鍵更新のため、4bit * 32の配列を用意
    key_nibbles = [0] * 32
    for i in range(32):
        key_nibbles[i] = (
            (key_128bits[4*i + 3] << 3) |
            (key_128bits[4*i + 2] << 2) |
            (key_128bits[4*i + 1] << 1) |
            key_128bits[4*i + 0]
        )
    
    #鍵更新の操作
    #全体を8セル分右に巡回シフト
    temp = [key_nibbles[(i + 8) % 32] for i in range(32)]  

    out_nibbles = [0] * 32
    
    # セル0〜23はそのまま配置
    for i in range(24):
        out_nibbles[i] = temp[i]
        
    # セル24〜27はセル単位での入れ替え
    out_nibbles[24] = temp[27]
    out_nibbles[25] = temp[24]
    out_nibbles[26] = temp[25]
    out_nibbles[27] = temp[26]
    
    # セル28〜31は内部のビットを分割して入れ替え
    # (上位2ビットを右シフトし、隣のセルの下位2ビットを左シフトして結合する)
    out_nibbles[28] = ((temp[28] & 0xC) >> 2) ^ ((temp[29] & 0x3) << 2) #0xC: 1100, 0x3: 0011
    out_nibbles[29] = ((temp[29] & 0xC) >> 2) ^ ((temp[30] & 0x3) << 2)
    out_nibbles[30] = ((temp[30] & 0xC) >> 2) ^ ((temp[31] & 0x3) << 2)
    out_nibbles[31] = ((temp[31] & 0xC) >> 2) ^ ((temp[28] & 0x3) << 2)

    #返すため、nibbleの配列を再び128ビットの整数に変換
    key_out = [0] * 128
    for i in range(32):
        key_out[4*i + 0] = (out_nibbles[i] >> 0) & 1
        key_out[4*i + 1] = (out_nibbles[i] >> 1) & 1
        key_out[4*i + 2] = (out_nibbles[i] >> 2) & 1
        key_out[4*i + 3] = (out_nibbles[i] >> 3) & 1

    return key_out


def roundfunction_gift128(pt_128bits, key_128bits, r, SBOX, GIFT_P, GIFT_RC):
    state = pt_128bits #要素数128の内容

    #4bitずつ配列に格納
    nibble_list = [0] * 32
    for i in range(32):
        nibble_list[i] = (
            (state[4*i + 3] << 3) |
            (state[4*i + 2] << 2) |
            (state[4*i + 1] << 1) |
            state[4*i + 0]
        )
    print(f"round: {r} \npt: {nibble_list}")
    print("key: ",key_128bits)

    #subcells
    state = sbox(nibble_list, SBOX)
    
    #nibbleを128bitの配列に変換
    list_128bits = hex_2_128bits(state)

    #PermBits
    state = perm_bits(list_128bits, GIFT_P)

    #AddRoundKey
    state = add_round_key(state, key_128bits, GIFT_RC[r])

    #KeySchedule
    key_next = key_schedule(key_128bits)
    
    return state, key_next


def encrypt(pt, key, round_num):    
    #ラウンド関数を繰り返して暗号化
    #Subcellsで使うsbox
    SBOX = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]

    #PremBitsで使うビット置換表 
    GIFT_P = [
        0, 33, 66, 99, 96, 1, 34, 67, 64, 97, 2, 35, 32, 65, 98, 3,
        4, 37, 70, 103, 100, 5, 38, 71, 68, 101, 6, 39, 36, 69, 102, 7,
        8, 41, 74, 107, 104, 9, 42, 75, 72, 105, 10, 43, 40, 73, 106, 11,
        12, 45, 78, 111, 108, 13, 46, 79, 76, 109, 14, 47, 44, 77, 110, 15,
        16, 49, 82, 115, 112, 17, 50, 83, 80, 113, 18, 51, 48, 81, 114, 19,
        20, 53, 86, 119, 116, 21, 54, 87, 84, 117, 22, 55, 52, 85, 118, 23,
        24, 57, 90, 123, 120, 25, 58, 91, 88, 121, 26, 59, 56, 89, 122, 27,
        28, 61, 94, 127, 124, 29, 62, 95, 92, 125, 30, 63, 60, 93, 126, 31
        ]

    #AddRoundKey処理で使うラウンド定数
    GIFT_RC = [
        0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
        0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
        0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
        0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
        0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
        0x26, 0x0C, 0x19, 0x32, 0x25, 0x0A, 0x15, 0x2A, 0x14, 0x28,
        0x10, 0x20
    ]

    #pt = 0xfedcba9876543210fedcba9876543210
    #key = 0xfedcba9876543210fedcba9876543210
    #round_num = 40

    #暗号化

    #フォーマットされていない（＝int型）なら平文、鍵をフォーマット
    if type(pt) == str:
        pt = int(pt, 16)
    if type(key) == str:
        key = int(key, 16)
    #平文、鍵を要素数128の配列に格納
    pt_128bits = [int(b) for b in reversed(format(pt, '0128b'))]
    key_128bits = [int(b) for b in reversed(format(key, '0128b'))]

    for i in range(round_num):
        pt_128bits, key_128bits = roundfunction_gift128(pt_128bits, key_128bits, i, SBOX, GIFT_P, GIFT_RC)

    enc = pt_128bits

    #16進数の整数に変換
    enc_hex = 0
    for i in range(128):
        enc_hex |= (enc[i] << i)
    #16進数にフォーマット
    enc_hex = format(enc_hex, '032x')

    return enc_hex