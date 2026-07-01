#DDT表の生成

DDT = [[0 for col in range(16)] for row in range(16)]

# GIFT-128のS-box
GIFT_S = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]

#S-boxの差分遷移表を作成
for dx in range(16):
    for x in range(16):
        y1 = GIFT_S[x]
        y2 = GIFT_S[x ^ dx]
        dy = y1 ^ y2
        DDT[dx][dy] += 1

print("DDT:")
for dx in range(16):
    print(f"dx={dx:2x}: ", end="")
    for dy in range(16):
        print(f"{DDT[dx][dy]:2d} ", end="")
    print()