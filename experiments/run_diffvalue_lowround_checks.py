from __future__ import annotations
from pathlib import Path
import json
from typing import Dict, List
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195
from pyganak import Counter

try:
    import pyganak

    PYGANAK_VERSION = getattr(pyganak, "__version__", "unknown")
except Exception:
    PYGANAK_VERSION = "unknown"

GIFT_S = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14] #S-box
GIFT_P = [ 
    0,
    33,
    66,
    99,
    96,
    1,
    34,
    67,
    64,
    97,
    2,
    35,
    32,
    65,
    98,
    3,
    4,
    37,
    70,
    103,
    100,
    5,
    38,
    71,
    68,
    101,
    6,
    39,
    36,
    69,
    102,
    7,
    8,
    41,
    74,
    107,
    104,
    9,
    42,
    75,
    72,
    105,
    10,
    43,
    40,
    73,
    106,
    11,
    12,
    45,
    78,
    111,
    108,
    13,
    46,
    79,
    76,
    109,
    14,
    47,
    44,
    77,
    110,
    15,
    16,
    49,
    82,
    115,
    112,
    17,
    50,
    83,
    80,
    113,
    18,
    51,
    48,
    81,
    114,
    19,
    20,
    53,
    86,
    119,
    116,
    21,
    54,
    87,
    84,
    117,
    22,
    55,
    52,
    85,
    118,
    23,
    24,
    57,
    90,
    123,
    120,
    25,
    58,
    91,
    88,
    121,
    26,
    59,
    56,
    89,
    122,
    27,
    28,
    61,
    94,
    127,
    124,
    29,
    62,
    95,
    92,
    125,
    30,
    63,
    60,
    93,
    126,
    31,
]
GIFT_RC = [
    0x01,
    0x03,
    0x07,
    0x0F,
    0x1F,
    0x3E,
    0x3D,
    0x3B,
    0x37,
    0x2F,
    0x1E,
    0x3C,
    0x39,
    0x33,
    0x27,
    0x0E,
    0x1D,
    0x3A,
    0x35,
    0x2B,
    0x16,
    0x2C,
    0x18,
    0x30,
    0x21,
    0x02,
    0x05,
    0x0B,
    0x17,
    0x2E,
    0x1C,
    0x38,
    0x31,
    0x23,
    0x06,
    0x0D,
    0x1B,
    0x36,
    0x2D,
    0x1A,
    0x34,
    0x29,
    0x12,
    0x24,
    0x08,
    0x11,
    0x22,
    0x04,
    0x09,
    0x13,
    0x26,
    0x0C,
    0x19,
    0x32,
    0x25,
    0x0A,
    0x15,
    0x2A,
    0x14,
    0x28,
    0x10,
    0x20,
]
TEST_VECTORS = [
    (
        "00000000000000000000000000000000",
        "00000000000000000000000000000000",
        "cd0bd738388ad3f668b15a36ceb6ff92",
    ),
    (
        "fedcba9876543210fedcba9876543210",
        "fedcba9876543210fedcba9876543210",
        "8422241a6dbf5a9346af468409ee0152",
    ),
    (
        "e39c141fa57dba43f08a85b6a91f86c1",
        "d0f5c59a7700d3e799028fa9f90ad837",
        "13ede67cbdcc3dbf400a62d6977265ea",
    ),
]
ZERO = "0" * 32
FIXED_M = "0123456789abcdeffedcba9876543210"


def hex_to_nibbles_le(h: str) -> List[int]:
    return [int(c, 16) for c in h.strip().lower()[::-1]]


def nibbles_le_to_hex(n: List[int]) -> str:
    return "".join("0123456789abcdef"[x] for x in n[::-1])


def hex_to_bits_le(h: str) -> List[int]:
    n = hex_to_nibbles_le(h)
    return [(n[i] >> j) & 1 for i in range(32) for j in range(4)]


def bits_le_to_hex(bits: List[int]) -> str:
    n = []
    for i in range(32):
        v = 0
        for j in range(4):
            v |= (bits[4 * i + j] & 1) << j
        n.append(v)
    return nibbles_le_to_hex(n)


def xor_hex(a: str, b: str) -> str:
    return f"{int(a,16)^int(b,16):032x}"


def gift128_permute(state: List[int]) -> List[int]:
    bits = [0] * 128
    perm_bits = [0] * 128
    for i in range(32):
        for j in range(4):
            bits[4 * i + j] = (state[i] >> j) & 1
    for i in range(128):
        perm_bits[GIFT_P[i]] = bits[i]
    out = [0] * 32
    for i in range(32):
        for j in range(4):
            out[i] ^= perm_bits[4 * i + j] << j
    return out


def gift128_add_round_key_const(state: List[int], key: List[int], r: int) -> List[int]:
    bits = [0] * 128
    key_bits = [0] * 128
    for i in range(32):
        for j in range(4):
            bits[4 * i + j] = (state[i] >> j) & 1
            key_bits[4 * i + j] = (key[i] >> j) & 1
    for i in range(32):
        bits[4 * i + 1] ^= key_bits[i]
        bits[4 * i + 2] ^= key_bits[i + 64]
    for bitpos, shift in [(3, 0), (7, 1), (11, 2), (15, 3), (19, 4), (23, 5)]:
        bits[bitpos] ^= (GIFT_RC[r] >> shift) & 1
    bits[127] ^= 1
    out = [0] * 32
    for i in range(32):
        for j in range(4):
            out[i] ^= bits[4 * i + j] << j
    return out


def gift128_key_update(key: List[int]) -> List[int]:
    temp = [key[(i + 8) % 32] for i in range(32)]
    out = [0] * 32
    for i in range(24):
        out[i] = temp[i]
    out[24], out[25], out[26], out[27] = temp[27], temp[24], temp[25], temp[26]
    out[28] = ((temp[28] & 0xC) >> 2) ^ ((temp[29] & 0x3) << 2)
    out[29] = ((temp[29] & 0xC) >> 2) ^ ((temp[30] & 0x3) << 2)
    out[30] = ((temp[30] & 0xC) >> 2) ^ ((temp[31] & 0x3) << 2)
    out[31] = ((temp[31] & 0xC) >> 2) ^ ((temp[28] & 0x3) << 2)
    return out


def gift128_encrypt_rounds(plaintext_hex: str, key_hex: str, rounds: int) -> str:
    state = hex_to_nibbles_le(plaintext_hex)
    key = hex_to_nibbles_le(key_hex)
    for r in range(rounds):
        state = [GIFT_S[x] for x in state]
        state = gift128_permute(state)
        state = gift128_add_round_key_const(state, key, r)
        key = gift128_key_update(key)
    return nibbles_le_to_hex(state)


def mmo_compress_gift128_rounds(h: str, m: str, rounds: int) -> str:
    return xor_hex(gift128_encrypt_rounds(m, h, rounds), m) #圧縮関数


def verify_collision_rounds(h0: str, m0: str, h1: str, m1: str, rounds: int) -> bool:
    return (h0, m0) != (h1, m1) and mmo_compress_gift128_rounds(
        h0, m0, rounds
    ) == mmo_compress_gift128_rounds(h1, m1, rounds)


def make_ddt() -> List[List[int]]:
    ddt = [[0] * 16 for _ in range(16)]
    for dx in range(16):
        for x in range(16):
            ddt[dx][GIFT_S[x] ^ GIFT_S[x ^ dx]] += 1
    return ddt


def add_eq(cnf: CNF, a: int, b: int) -> None:
    cnf.append([-a, b])
    cnf.append([a, -b])


def add_not(cnf: CNF, a: int, b: int) -> None:
    cnf.append([a, b])
    cnf.append([-a, -b])


def add_const(cnf: CNF, v: int, bit: int) -> None:
    cnf.append([v if bit else -v])


def add_xor2(cnf: CNF, x: int, y: int, z: int) -> None:
    cnf.append([-x, -y, -z])
    cnf.append([-x, y, z])
    cnf.append([x, -y, z])
    cnf.append([x, y, -z])


def forbid_pattern(cnf: CNF, vars_: List[int], pat: List[int]) -> None:
    cnf.append([-v if b else v for v, b in zip(vars_, pat)])


def bits_le(x: int, n: int) -> List[int]:
    return [(x >> i) & 1 for i in range(n)]


def add_sbox_value(cnf: CNF, xbits: List[int], ybits: List[int]) -> None:
    vars_ = xbits + ybits
    for x in range(16):
        y_ok = GIFT_S[x]
        for y in range(16):
            if y != y_ok:
                forbid_pattern(cnf, vars_, bits_le(x, 4) + bits_le(y, 4))


def add_sbox_diff_value(
    cnf: CNF, xbits: List[int], dxbits: List[int], dybits: List[int]
) -> None:
    vars_ = xbits + dxbits + dybits
    for x in range(16):
        for dx in range(16):
            dy_ok = GIFT_S[x] ^ GIFT_S[x ^ dx]
            for dy in range(16):
                if dy != dy_ok:
                    forbid_pattern(
                        cnf, vars_, bits_le(x, 4) + bits_le(dx, 4) + bits_le(dy, 4)
                    )


def key_update_bits(kbits: List[int]) -> List[int]:
    def cell(c: int) -> List[int]:
        return kbits[4 * c : 4 * c + 4]

    temp = [cell((i + 8) % 32) for i in range(32)]
    out = [None] * 32
    for i in range(24):
        out[i] = temp[i]
    out[24], out[25], out[26], out[27] = temp[27], temp[24], temp[25], temp[26]
    out[28] = [temp[28][2], temp[28][3], temp[29][0], temp[29][1]]
    out[29] = [temp[29][2], temp[29][3], temp[30][0], temp[30][1]]
    out[30] = [temp[30][2], temp[30][3], temp[31][0], temp[31][1]]
    out[31] = [temp[31][2], temp[31][3], temp[28][0], temp[28][1]]
    return [b for c in out for b in c]


def xor_key_and_const(
    cnf: CNF, pool: IDPool, data: int, key: int | None, const: int
) -> int:
    cur = data
    if key is not None:
        t = pool.id()
        add_xor2(cnf, cur, key, t)
        cur = t
    out = pool.id()
    if const:
        add_not(cnf, cur, out)
    else:
        add_eq(cnf, cur, out)
    return out


def xor_key_only(cnf: CNF, pool: IDPool, data: int, key: int | None) -> int:
    if key is None:
        out = pool.id()
        add_eq(cnf, data, out)
        return out
    out = pool.id()
    add_xor2(cnf, data, key, out)
    return out


def encrypt_diff_value_cnf(
    cnf: CNF,
    pool: IDPool,
    state: List[int],
    dstate: List[int],
    key: List[int],
    dkey: List[int],
    rounds: int,
) -> tuple[List[int], List[int]]:
    s = state[:]
    ds = dstate[:]
    k = key[:]
    dk = dkey[:]
    for r in range(rounds):
        y = [pool.id() for _ in range(128)]
        dy = [pool.id() for _ in range(128)]
        for c in range(32):
            add_sbox_value(cnf, s[4 * c : 4 * c + 4], y[4 * c : 4 * c + 4])
            add_sbox_diff_value(
                cnf, s[4 * c : 4 * c + 4], ds[4 * c : 4 * c + 4], dy[4 * c : 4 * c + 4]
            )
        py = [0] * 128
        pdy = [0] * 128
        for i in range(128):
            py[GIFT_P[i]] = y[i]
            pdy[GIFT_P[i]] = dy[i]
        ns = [0] * 128
        nds = [0] * 128
        for i in range(128):
            kval = None
            dkval = None
            if i % 4 == 1:
                kval = k[i // 4]
                dkval = dk[i // 4]
            elif i % 4 == 2:
                kval = k[64 + i // 4]
                dkval = dk[64 + i // 4]
            const = 0
            if i in [3, 7, 11, 15, 19, 23]:
                const = (GIFT_RC[r] >> ((i - 3) // 4)) & 1
            if i == 127:
                const ^= 1
            ns[i] = xor_key_and_const(cnf, pool, py[i], kval, const)
            nds[i] = xor_key_only(cnf, pool, pdy[i], dkval)
        s, ds = ns, nds
        k = key_update_bits(k)
        dk = key_update_bits(dk)
    return s, ds


def fixed_bits(cnf: CNF, bits: List[int], hx: str) -> None:
    for v, b in zip(bits, hex_to_bits_le(hx)):
        add_const(cnf, v, b)


def force_zero(cnf: CNF, bits: List[int]) -> None:
    for v in bits:
        add_const(cnf, v, 0)


def force_nonzero(cnf: CNF, bits: List[int]) -> None:
    cnf.append(bits[:])


def read_bits(vals: Dict[int, bool], bits: List[int]) -> str:
    return bits_le_to_hex([1 if vals[v] else 0 for v in bits])


def sat_find_collision_diff_value(condition: str, rounds: int) -> Dict[str, object]: #衝突探索
    cnf = CNF()
    pool = IDPool()
    h = [pool.id() for _ in range(128)]
    dh = [pool.id() for _ in range(128)]
    m = [pool.id() for _ in range(128)]
    dm = [pool.id() for _ in range(128)]
    if condition == "COL":
        fixed_bits(cnf, h, ZERO)
        force_zero(cnf, dh)
        force_nonzero(cnf, dm)
    elif condition == "SFS":
        fixed_bits(cnf, m, FIXED_M)
        force_zero(cnf, dm)
        force_nonzero(cnf, dh)
    elif condition == "FS":
        force_nonzero(cnf, dh + dm)
    else:
        raise ValueError(condition)
    c, dc = encrypt_diff_value_cnf(cnf, pool, m, dm, h, dh, rounds)
    for a, b in zip(dc, dm):
        add_eq(cnf, a, b)  # Delta(E_H(M) xor M) = dc xor dm = 0
    with Cadical195(bootstrap_with=cnf.clauses) as solver:
        sat = solver.solve()
        if not sat:
            return {
                "condition": condition,
                "rounds": rounds,
                "sat_status": "UNSAT",
                "num_vars": pool.top,
                "num_clauses": len(cnf.clauses),
            }
        model = solver.get_model()
    vals = {abs(l): (l > 0) for l in model}
    h0 = read_bits(vals, h)
    dhx = read_bits(vals, dh)
    m0 = read_bits(vals, m)
    dmx = read_bits(vals, dm)
    h1 = xor_hex(h0, dhx)
    m1 = xor_hex(m0, dmx)
    out0 = mmo_compress_gift128_rounds(h0, m0, rounds)
    out1 = mmo_compress_gift128_rounds(h1, m1, rounds)
    return {
        "condition": condition,
        "rounds": rounds,
        "sat_status": "SAT",
        "model": "difference_value",
        "num_vars": pool.top,
        "num_clauses": len(cnf.clauses),
        "h0": h0,
        "dh": dhx,
        "m0": m0,
        "dm": dmx,
        "h1": h1,
        "m1": m1,
        "out0": out0,
        "out1": out1,
        "direct_pass": verify_collision_rounds(h0, m0, h1, m1, rounds),
        "sat_and_direct_agree": out0 == out1,
    }


def toy_cipher_mmo(h: int, m: int) -> int:
    return GIFT_S[m ^ h] ^ m #圧縮関数


def projected_count_toy_bruteforce() -> int:
    seen = set()
    for x1 in [0, 1]:
        for x2 in [0, 1]:
            for z in [0, 1]:
                if (x1 or z) and (x2 or (not z)):
                    seen.add((x1, x2))
    return len(seen)


def projected_count_toy_cadical() -> int:
    solver = Cadical195()
    for c in [[1, 3], [2, -3]]:
        solver.add_clause(c)
    count = 0
    while solver.solve():
        vals = {abs(l): (l > 0) for l in solver.get_model()}
        solver.add_clause([(-v if vals[v] else v) for v in [1, 2]])
        count += 1
    solver.delete()
    return count


def projected_count_toy_pyganak() -> int:
    counter = Counter()
    counter.add_clauses([[1, 3], [2, -3]])
    counter.set_sampling_set([1, 2])
    return int(counter.count())


def main() -> None:
    ddt = make_ddt()
    tv = [
        {
            "pt": pt,
            "key": key,
            "expected": ct,
            "got": gift128_encrypt_rounds(pt, key, 40),
            "ok": gift128_encrypt_rounds(pt, key, 40) == ct,
        }
        for pt, key, ct in TEST_VECTORS
    ]
    sat_checks = [
        sat_find_collision_diff_value(cond, r)
        for r in [1, 2]
        for cond in ["COL", "SFS", "FS"]
    ]
    toy_classes = {}
    for h in range(16):
        for m in range(16):
            toy_classes.setdefault(toy_cipher_mmo(h, m), []).append((h, m))
    summary = {
        "gift128_test_vectors": tv,
        "gift128_one_round_zero": gift128_encrypt_rounds(ZERO, ZERO, 1),
        "gift128_two_round_zero": gift128_encrypt_rounds(ZERO, ZERO, 2),
        "ddt_row_sums_ok": all(sum(row) == 16 for row in ddt),
        "ddt_nonzero_values_for_nonzero_dx": sorted(
            {v for dx in range(1, 16) for v in ddt[dx] if v}
        ),
        "sat_low_round_collision_checks": sat_checks,
        "all_sat_direct_agree": all(
            x.get("sat_and_direct_agree", False) for x in sat_checks
        ),
        "toy_cipher_outputs_with_collision_class": len(
            [k for k, v in toy_classes.items() if len(v) >= 2]
        ),
        "projected_count_toy": {
            "bruteforce": projected_count_toy_bruteforce(),
            "cadical195_incremental": projected_count_toy_cadical(),
            "pyganak": projected_count_toy_pyganak(),
            "pyganak_version": PYGANAK_VERSION,
        },
    }
    Path("results").mkdir(exist_ok=True)
    Path("results/gift128_lowround_diffvalue_checks_mmo.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
