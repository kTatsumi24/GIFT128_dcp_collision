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

#変数IDの生成：値系列X, 差分系列dXのみ
var_pool = IDPool(start_from=1)
cnf = CNF()

#制約の変数IDを生成
def get_value_var(value, round_num):
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

#XORの制約
#演算子３つの場合
def xor3_const(cnf, a, b, c):
    #どれか一つに差分がある場合を禁止
    cnf.append([a, b, -c])
    cnf.append([a, -b, c])
    cnf.append([-a, b, c])
    #すべてに差分がある場合を禁止
    cnf.append([-a, -b, -c])

#演算子４つの場合
def xor4_const(cnf, a, b, c, d):
    #1の数が奇数の場合を禁止
    #1つ
    cnf.append([a, b, c, -d])
    cnf.append([a, b, -c, d])
    cnf.append([a, -b, c, d])
    cnf.append([-a, b, c, d])
    #3つ
    cnf.append([-a, -b, -c, d])
    cnf.append([-a, -b, c, -d])
    cnf.append([-a, b, -c, -d])
    cnf.append([a, -b, -c, -d])

#ラウンド鍵加算：値制約
def add_round_key_value_const(cnf, x_vars, y_vars, rk_vars, rc):
    #ラウンド鍵の加算
    vars_list = x_vars + y_vars + rk_vars
    for i in range(128):
        xor4_const(cnf, state_val[i], key_val[i], rc_vars[i], next_val[i])

#ラウンド鍵加算：差分値制約
def add_round_key_diff_const(cnf, dx_vars, dy_vars, drk_vars):
    #ラウンド鍵の加算
    for i in range(128):
        xor3_const(cnf, dx_vars[i], drk_vars[i], dy_vars[i])

#鍵更新
def key_update_const(key_vars):
    #128ビットを16ビット毎8つのブロックに分ける
    blocks = [key_vars[i:i + 16] for i in range(0, 128, 16)]
    #block[6]を右に2ビットローテーション
    blocks[6] = blocks[6][-2:] + blocks[6][:-2]
    #block[7]を右に12ビットローテーション
    blocks[7] = blocks[7][-12:] + blocks[7][:-12]
    #全体をシフトして結合し、次のラウンドの鍵を作成
    next_key_vars = blocks[1] + blocks[2] + blocks[3] + blocks[4] + blocks[5] + blocks[6] + blocks[7] + blocks[0]

    return next_key_vars


#MMO条件の制約
#暗号化の出力差分をdC、メッセージ差分をdMとすると、dC = dM | d(E_h(M) XOR M) = 0となる
def mmo_condition_const(cnf, dC_vars, dM_vars):
    for i in range(128):
        cnf.append([-dC_vars[i], dM_vars[i]])
        cnf.append([dC_vars[i], -dM_vars[i]]) 

#dMは、どれか1bitでも1でなければならない
def dM_const(cnf, dM_vars):
    cnf.append(dM_vars)  # dMのどれか1bitが1であることを強制




def solve_for_collision(rounds):
    cnf = CNF()
    vpool = IDPool(start_from=1)

    #定数変数
    ZERO = vpool.id('ZERO')
    ONE = vpool.id('ONE')
    cnf.append([-ZERO])  # ZEROは0に固定
    cnf.append([ONE])    # ONEは1に固定

    # h, dh, m, dmの変数IDを生成
    #hはgift128の鍵、mはメッセージ
    h = get_value_var('h', rounds) # hの変数ID: 1~128
    dh = get_value_var('dh', rounds) # dhの変数ID: 129~256
    m = get_value_var('m', rounds) # mの変数ID: 257~384
    dm = get_value_var('dm', rounds) # dmの変数ID: 385~512

    
    