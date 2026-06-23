from src.GIFT128_ref import encrypt

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

def test_reference():
    # 1つ目のテスト
    assert encrypt(TEST_VECTORS[0][0], TEST_VECTORS[0][1], 40) == TEST_VECTORS[0][2]
    
    # 2つ目のテスト
    assert encrypt(TEST_VECTORS[1][0], TEST_VECTORS[1][1], 40) == TEST_VECTORS[1][2]
    
    # 3つ目のテスト
    assert encrypt(TEST_VECTORS[2][0], TEST_VECTORS[2][1], 40) == TEST_VECTORS[2][2]