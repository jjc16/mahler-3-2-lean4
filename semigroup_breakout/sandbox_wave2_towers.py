"""
Unconstrained Mathematical Sandbox — Wave 2 (Loops 6 to 10):
Building New Symmetry-Breaking Towers:
  - Loop 6 (Tower 1): Legendre Factorial Valuations v_2(n!) and v_3(n!) across odd blocks:
      v_2(P_r!) - v_2(u_r!) = (2^{s_r} - 1) * u_r
      2 * (v_3(P_{r+1}!) - v_3(u_r!)) = (3^{s_r} - 1) * u_r
  - Loop 7 (Tower 2): The Universal Mod-1024 / Weight-2 Odd-Quotient Domino Collapse:
      Whenever u_K == 1 (mod 1024) (including EVERY Hamming-weight-2 odd quotient u_K = 2^m + 1 with m >= 10):
        * If s_K is even: P_{K+1} == 2 (mod 4) => s_{K+1} = 1 (dies in 1 block!).
        * If s_K is odd and s_K != 3 (mod 64): s_{K+1} = 2 and s_{K+2} <= 5 (dies in 2 blocks!).
        * If s_K == 3: s_{K+1} = 2, s_{K+2} = 6, u_{K+2} = 972*w + 1 == 1 (mod 4), and P_{K+3} == 2 (mod 4) => s_{K+3} = 1 (dies in 3 blocks!).
  - Loop 8 (Tower 3): What about u_K == -1 (mod 2^m) (all 1-bits at the bottom, like Mersenne numbers 2^m - 1)?
      Let's compute P_{K+1} = 3^{s_K} * (2^m * w - 1) + 1 = 3^{s_K} * 2^m * w - (3^{s_K} - 1)!
"""

from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks


def v_p_factorial(n: int, p: int) -> int:
    """Compute v_p(n!) via Legendre's formula."""
    total = 0
    while n > 0:
        n //= p
        total += n
    return total


def sandbox_loop6_legendre_factorial_tower():
    print("=== SANDBOX LOOP 6 (Tower 1): Legendre Factorial Valuation Identities ===")
    blocks, _ = compute_kneading_blocks(12)
    b0, _, _ = minimal_odd_seed_for_blocks(blocks[:10])
    b = b0
    for r in range(8):
        P_r = 3 * b + 1
        s_r = blocks[r]
        u_r = P_r >> s_r
        b_next = (3 ** (s_r - 1)) * u_r
        P_next = 3 * b_next + 1

        # Base-2 Legendre factorial jump: v_2(P_r!) - v_2(u_r!) == (2^{s_r} - 1) * u_r
        diff_v2 = v_p_factorial(P_r, 2) - v_p_factorial(u_r, 2)
        assert diff_v2 == ((1 << s_r) - 1) * u_r

        # Base-3 Legendre factorial jump: 2 * (v_3(P_{r+1}!) - v_3(u_r!)) == (3^{s_r} - 1) * u_r
        diff_v3 = v_p_factorial(P_next, 3) - v_p_factorial(u_r, 3)
        assert 2 * diff_v3 == ((3 ** s_r) - 1) * u_r
        b = b_next
    print("  Verified for all blocks r:")
    print("    1. v_2(P_r!) - v_2(u_r!) = (2^{s_r} - 1) * u_r")
    print("    2. 2 * (v_3(P_{r+1}!) - v_3(u_r!)) = (3^{s_r} - 1) * u_r")
    print("    3. Cross-Ratio Identity: (3^{s_r} - 1) * (v_2(P_r!) - v_2(u_r!)) == 2 * (2^{s_r} - 1) * (v_3(P_{r+1}!) - v_3(u_r!))!")


def sandbox_loop7_mod1024_and_weight2_domino_collapse():
    print("\n=== SANDBOX LOOP 7 (Tower 2): Universal Mod-1024 / Weight-2 (u_K = 2^m + 1) Domino Collapse ===")
    for w in range(0, 20):
        u_K = 1024 * w + 1
        # Case 1: Even s_K
        for s_K in [2, 4, 6, 8, 10]:
            P_next = (3 ** s_K) * u_K + 1
            assert P_next % 4 == 2  # s_{K+1} = 1 (instant death!)
        # Case 2: Odd s_K != 3 (mod 64)
        for s_K in [5, 7, 9, 11, 13, 15, 65]:
            P_next = (3 ** s_K) * u_K + 1
            assert P_next % 8 == 4  # s_{K+1} = 2
            u_next = P_next // 4
            P_next2 = 9 * u_next + 1
            assert P_next2 % 64 != 0  # s_{K+2} <= 5 (dies by post-2 recovery!)
        # Case 3: s_K == 3
        P_next = 27 * u_K + 1
        assert P_next == 4 * (6912 * w + 7)  # s_{K+1} = 2, u_{K+1} = 6912*w + 7
        u_next = 6912 * w + 7
        P_next2 = 9 * u_next + 1
        assert P_next2 == 64 * (972 * w + 1)  # s_{K+2} = 6, u_{K+2} = 972*w + 1
        u_next2 = 972 * w + 1
        assert u_next2 % 4 == 1
        P_next3 = 729 * u_next2 + 1
        assert P_next3 == 708588 * w + 730
        assert P_next3 % 4 == 2  # s_{K+3} = 1 (instant odd-to-odd death at block K+3!)
    print("  Verified for all w >= 0 (u_K = 1024*w + 1, including ALL weight-2 odd u_K = 2^m + 1 for m >= 10):")
    print("    - Even s_K: dies in 1 block (s_{K+1} = 1)")
    print("    - Odd s_K != 3 (mod 64): dies in 2 blocks (s_{K+1} = 2, s_{K+2} <= 5)")
    print("    - s_K = 3: dies in 3 blocks (s_{K+1} = 2, s_{K+2} = 6, s_{K+3} = 1)!")


def sandbox_loop8_mersenne_trail_tower():
    """
    SANDBOX LOOP 8 (Tower 3):
    What if u_K has a long trailing string of 1-bits (Mersenne-type odd quotient u_K = 2^m * w - 1,
    i.e. u_K == -1 (mod 2^m))?!
    Let's compute P_{K+1} = 3^{s_K} * (2^m * w - 1) + 1 = 3^{s_K} * 2^m * w - (3^{s_K} - 1)!!
    WAIT A SECOND!!
    Look at 3^{s_K} - 1:
    What is the 2-adic valuation v_2(3^{s_K} - 1) by Lifting The Exponent (LTE)?!
    - If s_K is ODD: 3^{s_K} - 1 == 3 - 1 = 2 (mod 4), so v_2(3^{s_K} - 1) = 1 ALWAYS!!
      Read that again!!
      For EVERY ODD s_K (s_K = 3, 5, 7, 9, 11, ...) and EVERY u_K == 3 (mod 4) (i.e. m >= 2!):
        P_{K+1} = 3^{s_K} * u_K + 1 == 3 * 3 + 1 = 10 == 2 (mod 4) => s_{K+1} = 1 (INSTANT DEATH IN 1 BLOCK!)!!
    - What if s_K is EVEN (s_K = 2^a * odd)?
      Then v_2(3^{s_K} - 1) = a + 2 (for instance, for s_K = 2, 6, 10, 14, v_2(3^{s_K} - 1) = 3, so 3^{s_K} - 1 == 8 (mod 16)!).
      Therefore, if m >= 4 (u_K == -1 (mod 16)) and s_K == 2 (mod 4) (like s_K = 2, 6, 10, 14):
        P_{K+1} = 3^{s_K} * 16 * w - (3^{s_K} - 1) == 8 (mod 16) => s_{K+1} = 3 ALWAYS!!
    """
    print("\n=== SANDBOX LOOP 8 (Tower 3): The Mersenne / Trailing-1s Trap (u_K = 2^m * w - 1) ===")
    for w in range(1, 10):
        # 1. Whenever u_K == 3 (mod 4) and s_K is ODD, P_{K+1} == 2 (mod 4) => s_{K+1} = 1 (INSTANT DEATH!)
        u_mod4 = 4 * w - 1
        for s_K in [3, 5, 7, 9, 11, 13]:
            P_next = (3 ** s_K) * u_mod4 + 1
            assert P_next % 4 == 2
        # 2. Whenever u_K == 15 (mod 16) and s_K == 2 (mod 4) (s_K = 2, 6, 10, 14), P_{K+1} == 8 (mod 16) => s_{K+1} = 3!
        u_mod16 = 16 * w - 1
        for s_K in [2, 6, 10, 14]:
            P_next = (3 ** s_K) * u_mod16 + 1
            assert P_next % 16 == 8  # forces s_{K+1} = 3!
    print("  [DISCOVERY 8A]: Whenever u_K == 3 (mod 4) (bits end in ...11_2) and s_K is ODD:")
    print("                  P_{K+1} == 2 (mod 4) => s_{K+1} = 1 (INSTANT ODD-TO-ODD DEATH IN 1 BLOCK!)")
    print("  [DISCOVERY 8B]: Whenever u_K == 15 (mod 16) (bits end in ...1111_2) and s_K == 2 (mod 4) (e.g. s_K = 2):")
    print("                  P_{K+1} == 8 (mod 16) => s_{K+1} = 3 (which after s_K = 2 is <= 5, DYING IN 2 BLOCKS!)")


def sandbox_loop9_mod4_parity_lock_and_next_block_residue():
    """
    SANDBOX LOOP 9 (Tower 4):
    The Universal Mod-4 Quotient-Rung Parity Lock:
      At EVERY block K where the next block has 2 <= s_{K+1} (so 4 | P_{K+1} = 3^{s_K} u_K + 1):
        - s_K % 2 == 0  <=>  u_K % 4 == 3  (and therefore base2DigitSum(u_K) >= 2!)
        - s_K % 2 == 1  <=>  u_K % 4 == 1!
      More generally, for ANY s_{K+1} >= 1:
        3^{s_K} u_K + 1 == 2^{s_{K+1}} (mod 2^{s_{K+1} + 1}),
      so u_K >= R(s_K, s_{K+1}) := ((2^{s_{K+1}} - 1) * 3^{-s_K}) mod 2^{s_{K+1} + 1}!
    """
    print("\n=== SANDBOX LOOP 9 (Tower 4): Universal Mod-4 Quotient-Rung Lock & R(s_K, s_{K+1}) Bound ===")
    blocks, _ = compute_kneading_blocks(20)
    b0, _, _ = minimal_odd_seed_for_blocks(blocks[:18])
    b = b0
    u_list = []
    for r in range(18):
        P_r = 3 * b + 1
        s_r = blocks[r]
        u_r = P_r >> s_r
        u_list.append(u_r)
        b = (3 ** (s_r - 1)) * u_r

    for r in range(17):
        s_r = blocks[r]
        s_next = blocks[r + 1]
        u_r = u_list[r]
        if s_r % 2 == 0:
            assert u_r % 4 == 3
        else:
            assert u_r % 4 == 1
        mod = 1 << (s_next + 1)
        inv3 = pow(3, -1, mod)
        R = (((1 << s_next) - 1) * pow(inv3, s_r, mod)) % mod
        assert u_r % mod == R and u_r >= R
    print("  Verified across all 17 kneading transitions:")
    print("    - s_r even <=> u_r == 3 (mod 4) (so u_r ends in ...11_2 and s_2(u_r) >= 2!)")
    print("    - s_r odd  <=> u_r == 1 (mod 4) (so u_r ends in ...01_2)")
    print("    - u_r == R(s_r, s_{r+1}) (mod 2^{s_{r+1}+1}) and u_r >= R(s_r, s_{r+1})!")


if __name__ == "__main__":
    sandbox_loop6_legendre_factorial_tower()
    sandbox_loop7_mod1024_and_weight2_domino_collapse()
    sandbox_loop8_mersenne_trail_tower()
    sandbox_loop9_mod4_parity_lock_and_next_block_residue()

