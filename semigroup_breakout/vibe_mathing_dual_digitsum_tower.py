"""
Semigroup Breakout — The Dual Base-2 / Base-3 Digit-Sum Tower:
Testing the newly discovered exact conservation laws connecting Base-2 Hamming weight s_2
and Base-3 digit sum s_3 across the odd-block recurrence 2^{s_{r+1}} u_{r+1} = 3^{s_r} u_r + 1:
  1. s_2(P_r) = s_2(2^{s_r} u_r) = s_2(u_r)           (Base-2 division invariance)
  2. s_3(b_{r+1}) = s_3(3^{s_r - 1} u_r) = s_3(u_r)   (Base-3 multiplication invariance)
  3. s_3(P_r) = s_3(3 b_r + 1) = s_3(b_r) + 1         (Base-3 unit-step increment)
  4. s_3(P_{r+1}) = s_3(2^{s_{r+1}} u_{r+1}) = s_3(u_r) + 1
  5. Exact Telescoping Conservation Law across N blocks:
       s_3(u_N) + sum_{r=0}^N (s_3(2^{s_r} u_r) - s_3(u_r)) == s_3(b_0) + N + 1!
"""

from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks


def s2(n: int) -> int:
    return n.bit_count()


def s3(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total


def test_dual_digitsum_conservation():
    print("=== THE DUAL BASE-2 / BASE-3 DIGIT-SUM CONSERVATION TOWER ===")
    blocks, _ = compute_kneading_blocks(20)
    b0, T_15, _ = minimal_odd_seed_for_blocks(blocks[:15])
    print(f"Testing on 15-block kneading seed b_0 = {b0} (s_2(b_0)={s2(b0)}, s_3(b_0)={s3(b0)})")
    print(f"{'r':>2} | {'s_r':>3} | {'s_2(P_r)==s_2(u_r)':>18} | {'s_3(b_r)':>8} | {'s_3(P_r)':>8} | {'s_3(u_r)':>8} | {'Delta_3 = s_3(2^s u)-s_3(u)':>27}")
    print("-" * 92)

    b = b0
    cum_delta3 = 0
    u_prev = None
    for r in range(15):
        P_r = 3 * b + 1
        s_r = blocks[r]
        u_r = P_r >> s_r
        assert P_r == (1 << s_r) * u_r
        # Check Law 1: s_2(P_r) == s_2(u_r)
        assert s2(P_r) == s2(u_r)
        # Check Law 2: for r >= 1, s_3(b_r) == s_3(u_{r-1})
        if r >= 1:
            assert s3(b) == s3(u_prev)
        # Check Law 3: s_3(P_r) == s_3(b_r) + 1
        assert s3(P_r) == s3(b) + 1
        # Check Law 4: for r >= 1, s_3(P_r) == s_3(u_{r-1}) + 1
        if r >= 1:
            assert s3(P_r) == s3(u_prev) + 1

        delta3 = s3(P_r) - s3(u_r)
        cum_delta3 += delta3
        # Check Law 5 (Telescoping Conservation): s_3(u_r) + sum_{k=0}^r delta3_k == s_3(b_0) + r + 1
        assert s3(u_r) + cum_delta3 == s3(b0) + r + 1

        print(f"{r:>2} | {s_r:>3} | {s2(P_r):>8} == {s2(u_r):<8} | {s3(b):>8} | {s3(P_r):>8} | {s3(u_r):>8} | {delta3:>+27}")
        u_prev = u_r
        b = (3 ** (s_r - 1)) * u_r

    print(f"\nVerified all 5 Dual Base-2/Base-3 Conservation Laws across all 15 blocks!")
    print(f"At r=14: s_3(u_14) = {s3(u_prev)}, sum_{'{r=0}'}^{'{14}'} Delta_3(r) = {cum_delta3}, "
          f"s_3(u_14) + sum = {s3(u_prev) + cum_delta3} == s_3(b_0) + 15 = {s3(b0) + 15}!")


if __name__ == "__main__":
    test_dual_digitsum_conservation()
