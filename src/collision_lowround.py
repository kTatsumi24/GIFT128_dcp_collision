#少数ラウンドで衝突ができるか検証する
#参照実装： GIFT128-MMO_ref.py
'''
制約実装の流れ
1. DDTからS-boxの禁止パターンを作成、値制約として実装
2. S-box差分値制約：dy=S(x) XOR S(x XOR dx)の制約を作成
3. Bit置換の制約：入れ替える
4. ラウンド鍵加算：値制約は鍵、ラウンド定数 ／ 差分値制約は鍵差分のみ
5. 鍵更新：同じ更新をする
6. MMO条件：dC = dM | d(E_h(M) XOR M) = 0

SATに解かせる
→ H, M, dH, dMからH', M'を求め、ref実装で確認する
'''
import json
from pathlib import Path

from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195
import json
from pyganak import Counter

from ddt_ref import DDT

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

#制約の変数IDを生成
def get_value_var(var_pool, value, round_num):
    state = []
    for c in range(32):
        for b in range(4):
            var_id = var_pool.id(f'{value}:r{round_num}:c{c}:b{b}') #x:r4:c5:b2
            state.append(var_id)
    return state

#禁止パターンの変数の組をcnfに追加する関数
def pattern2cnf(cnf, vars_id, pattern):
    clause = []
    for i, var in enumerate(vars_id):
        if pattern[i] == 1:
            clause.append(-var)
        else:
            clause.append(var)
    cnf.append(clause)

#整数を下位ビットからリストに格納する
def int2bits(val, length):
    return [(val >> i) & 1 for i in range(length)]

#subcellsのためのニブル作成
def bit2nibble(state_128bits):
    return [state_128bits[4*i : 4*i+4] for i in range(32)]

#subcellsの後のニブルを128bitの配列に変換
def nibble2bit(nibble_list):
    return [bit for nibble in nibble_list for bit in nibble]

#制約
#S-box値制約
def sbox_value_const(cnf, x_vars, y_vars):
    #値がy = S(x)である制約を作成　→　y = S(x)でない場合を禁止
    vars_list = x_vars + y_vars
    for x in range(16):
        y_true = SBOX[x]
        #y_true以外の値を禁止する制約を追加
        for y in range(16):
            if y != y_true:
                pattern = int2bits(x, 4) + int2bits(y, 4)
                pattern2cnf(cnf, vars_list, pattern)

#S-box差分値制約
def sbox_diff_const(cnf, dx_vars, dy_vars, x_vars):
    #差分値がdy = S(x XOR dx) XOR S(x)となる制約を作成
    vars_list = x_vars + dx_vars + dy_vars #12bit分結合
    for x in range(16):
        for dx in range(16):
            dy_true = SBOX[x ^ dx] ^ SBOX[x]
            #dy_true以外の値を禁止する制約を追加
            for dy in range(16):
                if dy != dy_true:
                    pattern = int2bits(x, 4) + int2bits(dx, 4) + int2bits(dy, 4)
                    pattern2cnf(cnf, vars_list, pattern)

#ビット置換の制約：値と差分値で共通
def perm_bits(state_128bits):
    next_state = [state_128bits[GIFT_P[i]] for i in range(128)]
    return next_state

#ラウンド鍵加算用：等価
def add_eq_const(cnf, a, b):
    cnf.append([-a, b])
    cnf.append([a, -b])

#ラウンド鍵加算用：反転
def add_not_const(cnf, a, b):
    cnf.append([a, b])
    cnf.append([-a, -b])

#XORの制約
def xor3_const(cnf, a, b, c):
    #どれか一つに差分がある場合を禁止
    cnf.append([a, b, -c])
    cnf.append([a, -b, c])
    cnf.append([-a, b, c])
    #すべてに差分がある場合を禁止
    cnf.append([-a, -b, -c])

#ラウンド鍵・定数加算で加算されるか、ビット毎に判定
def add_round_key_flag(i, rc):
    k_idx = None
    # 鍵のインデックス判定
    if i % 4 == 1:
        k_idx = i // 4
    elif i % 4 == 2:
        k_idx = 64 + i // 4
        
    c_bit = 0
    # 定数の判定
    if i % 4 == 3:
        idx = i // 4
        if idx < 6:
            c_bit = (rc >> idx) & 1
        elif idx == 31:
            c_bit = 1
            
    return k_idx, c_bit


#ラウンド鍵加算：値制約
def add_round_key_value_const(cnf, vpool, x_vars, y_vars, key_val, rc):
    #ラウンド鍵の加算
    for i in range(128):
        kval = None
        
        # 鍵のインデックス判定
        if i % 4 == 1:
            kval = key_val[i // 4]
        elif i % 4 == 2:
            kval = key_val[64 + i // 4]
        
        # 定数の判定
        const = 0
        if i in [3, 7, 11, 15, 19, 23]:
            const = (rc >> ((i - 3) // 4)) & 1
        if i == 127:
            const ^= 1
        
        current_val = x_vars[i]
        
        # 鍵がある場合はXOR
        if kval is not None:
            temp = vpool.id()
            xor3_const(cnf, current_val, kval, temp)
            current_val = temp
        
        # 定数がある場合は反転、なければそのまま
        if const:
            add_not_const(cnf, current_val, y_vars[i])
        else:
            add_eq_const(cnf, current_val, y_vars[i])

#ラウンド鍵加算：差分値制約
def add_round_key_diff_const(cnf, vpool, dx_vars, dy_vars, key_diff):
    for i in range(128):
        kval = None
        
        # 鍵差分のインデックス判定
        if i % 4 == 1:
            kval = key_diff[i // 4]
        elif i % 4 == 2:
            kval = key_diff[64 + i // 4]
        
        current_val = dx_vars[i]
        
        # 鍵差分がある場合はXOR、ない場合はそのまま
        if kval is not None:
            xor3_const(cnf, current_val, kval, dy_vars[i])
        else:
            add_eq_const(cnf, current_val, dy_vars[i])

#鍵更新
def key_update_const(key_vars):
    # 参照実装の key_update_bits と同じ処理
    # key_vars は 128 個のビット変数のリスト
    def cell(kbits, c):
        return kbits[4 * c : 4 * c + 4]

    # temp = key[(i + 8) % 32] で8セル右ローテーション
    temp = [cell(key_vars, (i + 8) % 32) for i in range(32)]
    out = [None] * 32
    
    # cells 0-23 はそのまま
    for i in range(24):
        out[i] = temp[i]
    
    # cells 24-27 のローテーション
    out[24], out[25], out[26], out[27] = temp[27], temp[24], temp[25], temp[26]
    
    # cells 28-31 のビットシャッフル
    out[28] = [temp[28][2], temp[28][3], temp[29][0], temp[29][1]]
    out[29] = [temp[29][2], temp[29][3], temp[30][0], temp[30][1]]
    out[30] = [temp[30][2], temp[30][3], temp[31][0], temp[31][1]]
    out[31] = [temp[31][2], temp[31][3], temp[28][0], temp[28][1]]
    
    # フラット化
    return [b for c in out for b in c]


#MMO条件の制約
#暗号化の出力差分をdC、メッセージ差分をdMとすると、dC = dM | d(E_h(M) XOR M) = 0となる
def mmo_condition_const(cnf, dC_vars, dM_vars):
    for i in range(128):
        cnf.append([-dC_vars[i], dM_vars[i]])
        cnf.append([dC_vars[i], -dM_vars[i]]) 

#dMは、どれか1bitでも1でなければならない
def dM_const(cnf, dM_vars):
    cnf.append(dM_vars)  # dMのどれか1bitが1であることを強制


#復元用
#16進数の文字列をニブルのリスト（リトルエンディアン）に変換
def hex_to_nibbles_le(h):
    return [int(c, 16) for c in h.strip().lower()[::-1]]

#ニブルのリスト（リトルエンディアン）を16進数文字列に変換
def nibbles_le_to_hex(n):
    return "".join("0123456789abcdef"[x] for x in n[::-1])

#16進数の文字列をビットのリスト（リトルエンディアン）に変換
def hex_to_bits_le(h):
    n = hex_to_nibbles_le(h)
    return [(n[i] >> j) & 1 for i in range(32) for j in range(4)]

#ビットのリスト（リトルエンディアン）を16進数文字列に変換
def bits_le_to_hex(bits):
    n = []
    for i in range(32):
        v = 0
        for j in range(4):
            v |= (bits[4 * i + j] & 1) << j
        n.append(v)
    return nibbles_le_to_hex(n)

#16進数の文字列同士のXORを計算する関数
def xor_hex(a, b):
    return f"{int(a, 16) ^ int(b, 16):032x}"

#解の復元
def get_hex_from_model(model, var_ids):
    vals = {abs(v): (1 if v > 0 else 0) for v in model}
    bits = [vals[v] for v in var_ids]
    
    nibbles = []
    for i in range(32):
        val = 0
        for j in range(4):
            val |= (bits[4 * i + j] << j)
        nibbles.append(val)
        
    return "".join(f"{x:x}" for x in nibbles[::-1])

def solve_for_collision(rounds, condition):
    cnf = CNF()
    vpool = IDPool(start_from=1)

    # h, dh, m, dmの変数IDを生成
    h = [vpool.id() for _ in range(128)]
    dh = [vpool.id() for _ in range(128)]
    m = [vpool.id() for _ in range(128)]
    dm = [vpool.id() for _ in range(128)]

    # 衝突条件 (COL, SFS, FS) の適用
    if condition == "COL":
        # COL: h を ZERO に固定、dh を 0 に強制、dm を非ゼロに強制
        for i in range(128):
            cnf.append([-h[i]])   # h を 0 に固定
            cnf.append([-dh[i]])  # dh を 0 に固定
        cnf.append(dm)            # dm のどれか1bit以上が1
        
    elif condition == "SFS":
        # SFS: m を固定値に固定、dm を 0 に強制、dh を非ゼロに強制
        m_fixed = "0123456789abcdeffedcba9876543210"
        m_bits = hex_to_bits_le(m_fixed)
        for i, bit in enumerate(m_bits):
            if bit:
                cnf.append([m[i]])
            else:
                cnf.append([-m[i]])
        for i in range(128):
            cnf.append([-dm[i]])  # dm を 0 に固定
        cnf.append(dh)            # dh のどれか1bit以上が1
        
    elif condition == "FS":
        # FS衝突: dh と dm のどれか1bit以上が非ゼロ
        cnf.append(dh + dm)

    # 状態変数の初期化
    state_val = m
    state_diff = dm
    key_val = h
    key_diff = dh

    # ラウンド関数のループ
    for r in range(rounds):
        # S-box通過後の中間変数を生成
        sb_val = [vpool.id() for _ in range(128)]
        sb_diff = [vpool.id() for _ in range(128)]
        
        # ラウンド終了時の次の状態変数を生成
        next_val = [vpool.id() for _ in range(128)]
        next_diff = [vpool.id() for _ in range(128)]

        # ラウンド定数を取得
        rc = GIFT_RC[r]

        # S-box制約
        for c in range(32):
            sbox_value_const(cnf, state_val[4*c:4*c+4], sb_val[4*c:4*c+4])
            sbox_diff_const(cnf, state_diff[4*c:4*c+4], sb_diff[4*c:4*c+4], state_val[4*c:4*c+4])

        # PermBits制約
        perm_val = [0] * 128
        perm_diff = [0] * 128
        for i in range(128):
            perm_val[GIFT_P[i]] = sb_val[i]
            perm_diff[GIFT_P[i]] = sb_diff[i]

        # AddRoundKey制約（値制約と差分値制約を別々に呼び出し）
        add_round_key_value_const(cnf, vpool, perm_val, next_val, key_val, rc)
        add_round_key_diff_const(cnf, vpool, perm_diff, next_diff, key_diff)

        # 鍵更新制約
        key_val = key_update_const(key_val)
        key_diff = key_update_const(key_diff)

        # 更新
        state_val = next_val
        state_diff = next_diff

    # MMO条件 (dC == dM)
    # 参照実装では: for a, b in zip(dc, dm): add_eq(cnf, a, b)
    for i in range(128):
        add_eq_const(cnf, state_diff[i], dm[i])

    # SATソルバーで解く
    num_clauses = len(cnf.clauses)
    num_vars = vpool.top
    
    with Cadical195(bootstrap_with=cnf.clauses) as solver:
        if solver.solve():
            model = solver.get_model()
            vals = {abs(v): (v > 0) for v in model}
            
            # 結果を抽出
            h0_hex = bits_le_to_hex([1 if vals.get(v, False) else 0 for v in h])
            dh_hex = bits_le_to_hex([1 if vals.get(v, False) else 0 for v in dh])
            m0_hex = bits_le_to_hex([1 if vals.get(v, False) else 0 for v in m])
            dm_hex = bits_le_to_hex([1 if vals.get(v, False) else 0 for v in dm])
            
            h1_hex = xor_hex(h0_hex, dh_hex)
            m1_hex = xor_hex(m0_hex, dm_hex)
            
            return model, h, dh, m, dm, num_vars, num_clauses, h0_hex, dh_hex, m0_hex, dm_hex
        else:
            return None, None, None, None, None, num_vars, num_clauses, None, None, None, None


def main():
    # 複数ラウンドの結果をまとめるためのリスト
    all_results = []
    conditions = ["COL", "SFS", "FS"]  # 衝突条件のリスト
    
    for target_rounds in [1, 2]:
        for condition in conditions:
            print(f"\n=== {target_rounds}ラウンドの衝突探索 (条件: {condition}) ===")
            # solve_for_collisionを呼び出し
            model, h_vars, dh_vars, m_vars, dm_vars, num_vars, num_clauses, h0_hex, dh_hex, m0_hex, dm_hex = solve_for_collision(target_rounds, condition)
            
            # 出力用の辞書（枠組み）を作成
            result = {
                "condition": condition,
                "rounds": target_rounds,
                "sat_status": "UNSAT",
                "model": "difference_value",
                "num_vars": num_vars,
                "num_clauses": num_clauses,
                "h0": None,
                "dh": None,
                "m0": None,
                "dm": None,
                "h1": None,
                "m1": None,
                "out0": None, 
                "out1": None, 
                "direct_pass": None, 
                "sat_and_direct_agree": None 
            }
            
            if model:
                result["sat_status"] = "SAT"
                
                # 値を辞書に格納
                result["h0"] = h0_hex
                result["dh"] = dh_hex
                result["m0"] = m0_hex
                result["dm"] = dm_hex
                
                # XORを計算して h1, m1 を求める
                h1_hex = xor_hex(h0_hex, dh_hex)
                m1_hex = xor_hex(m0_hex, dm_hex)
                result["h1"] = h1_hex
                result["m1"] = m1_hex
                
                print(" -> SAT")
                print(f"  H  (チェイン値): {h0_hex}")
                print(f"  M  (メッセージ): {m0_hex}")

                # MMOモード検証：GIFT128MMO_ref.py から関数をimport
                try:
                    from GIFT128MMO_ref import gift128_mmo_hash
                    
                    # MMOハッシュで検証（参照実装：gift128_mmo_hash）
                    out0_hex = gift128_mmo_hash(h0_hex, m0_hex, target_rounds)
                    out1_hex = gift128_mmo_hash(h1_hex, m1_hex, target_rounds)
                    
                    result["out0"] = out0_hex
                    result["out1"] = out1_hex
                    
                    # MMO衝突の判定: 2つのハッシュ値が一致かつ入力が異なることを確認
                    result["direct_pass"] = (out0_hex == out1_hex) and ((h0_hex, m0_hex) != (h1_hex, m1_hex))
                    result["sat_and_direct_agree"] = result["direct_pass"]
                    print(f"  -> MMO検証完了: 衝突 {'成功！' if result['direct_pass'] else '失敗...'}")
                    
                except ImportError as ie:
                    print(f"  -> [エラー] GIFT128MMO_ref.py から gift128_mmo_hash をインポートできませんでした: {ie}")
                except Exception as e:
                    print(f"  -> [エラー] MMO検証中にエラーが発生しました: {e}")
                    
            else:
                print(" -> UNSAT")
            
            all_results.append(result)

    # 出力先となる results フォルダを作成 (存在しない場合のみ)
    output_dir = Path("results")
    output_dir.mkdir(exist_ok=True)
    
    # 出力ファイルのパスを指定
    output_file = output_dir / "gift128_lowround_diffvalue_checks_mmo.json"
    
    # JSONとして書き込み (整形して出力)
    output_file.write_text(
        json.dumps(all_results, indent=6, ensure_ascii=False), 
        encoding="utf-8"
    )
    print(f"\n結果をファイルに保存しました: {output_file.absolute()}")


if __name__ == "__main__":
    main()