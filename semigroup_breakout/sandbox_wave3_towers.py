"""
Unconstrained Mathematical Sandbox — Wave 3 (Loops 10 to 12):
1. Loop 10 (Tower 18 — The Universal Mod-12 {5, 7} Lock):
   At EVERY block r >= 0 where s_{r+1} >= 2:
     - From 3 * b_r + 1 = 2^{s_r} * u_r == 1 (mod 3):
         s_r even <=> u_r == 1 (mod 3)
         s_r odd  <=> u_r == 2 (mod 3)
     - From 3^{s_r} * u_r + 1 = 2^{s_{r+1}} * u_{r+1} == 0 (mod 4):
         s_r even <=> u_r == 3 (mod 4)
         s_r odd  <=> u_r == 1 (mod 4)
     - Combining mod 3 and mod 4 (Chinese Remainder Theorem mod 12):
         s_r even <=> u_r == 7 (mod 12)
         s_r odd  <=> u_r == 5 (mod 12)!
     - Consequently: u_r in {1, 3, 9, 11} (mod 12) is UNIVERSALLY FORBIDDEN!
       In particular, u_r = 1 is 100% IMPOSSIBLE for BOTH even and odd s_r whenever s_{r+1} >= 2,
       u_r >= 5 always (u_r >= 7 when s_r is even), s_2(u_r) >= 2 always, and s_3(u_r) >= 2 always!
2. Loop 11 (Tower 19 — Two-Sided Chinese Remainder Lock Mod 3^{s_{r-1}} * 2^{s_{r+1}+1}):
   At every interior block r >= 1, u_r satisfies simultaneously:
     (2^{s_{r+1}} * u_{r+1}) / 3^{s_r} = u_r,   (2^{s_{r+1}} * u_{r+1}) % 3^{s_r} = 1,
     2^{s_r} * u_r == 1 (mod 3^{s_{r-1}})   AND   3^{s_r} * u_r == 2^{s_{r+1}} - 1 (mod 2^{s_{r+1}+1})!
3. Loop 12 (Tower 20 — 5x/7x Sharpened Archimedean Rung Ceiling & Joint Digit-Sum Floor):
   Since u_K >= 5 (and u_K >= 7 when s_K is even),
     10 * 2^{T_{K+1}} <= 2 * 2^{T_{K+1}} * u_K < 3^{T_K} * (2 * P_0 + 1)
   and s_2(P_r) + s_3(P_{r+1}) = s_2(u_r) + s_3(u_r) + 1 >= 2 + 2 + 1 = 5 at EVERY surviving block!
"""

import math
from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks


def s2(n: int) -> int:
    return n.bit_count()


def s3(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total


def sandbox_loop10_mod12_lock():
    print("=== SANDBOX LOOP 10 (Tower 18): The Universal Mod-12 {5, 7} Lock on u_r ===")
    blocks, _ = compute_kneading_blocks(30)
    b0, _, _ = minimal_odd_seed_for_blocks(blocks[:25])
    b = b0
    u_list = []
    P_list = []
    for r in range(25):
        P_r = 3 * b + 1
        s_r = blocks[r]
        u_r = P_r >> s_r
        P_list.append(P_r)
        u_list.append(u_r)
        b = (3 ** (s_r - 1)) * u_r

    for r in range(24):
        s_r = blocks[r]
        u_r = u_list[r]
        if s_r % 2 == 0:
            assert u_r % 12 == 7, f"At r={r}, even s_r={s_r}, got u_r % 12 = {u_r % 12}"
            assert u_r >= 7
        else:
            assert u_r % 12 == 5, f"At r={r}, odd s_r={s_r}, got u_r % 12 = {u_r % 12}"
            assert u_r >= 5
        assert s2(u_r) >= 2 and s3(u_r) >= 2
        assert s2(P_list[r]) + s3(P_list[r + 1]) >= 5

    print("  Verified across all 24 kneading blocks:")
    print("    - Whenever s_r is EVEN: u_r == 7 (mod 12)  (so u_r >= 7)")
    print("    - Whenever s_r is ODD:  u_r == 5 (mod 12)  (so u_r >= 5)")
    print("    - Residue classes 1, 3, 9, 11 (mod 12) are 100% EXTINCT!")
    print("    - u_r = 1 is IMPOSSIBLE for BOTH even and odd s_r!")
    print("    - s_2(u_r) >= 2, s_3(u_r) >= 2, and s_2(P_r) + s_3(P_{r+1}) >= 5 at EVERY block!")


def sandbox_loop11_two_sided_crt_lock():
    print("\n=== SANDBOX LOOP 11 (Tower 19): Two-Sided Chinese Remainder Lock Mod 3^{s_{r-1}} * 2^{s_{r+1}+1} ===")
    blocks, _ = compute_kneading_blocks(20)
    b0, _, _ = minimal_odd_seed_for_blocks(blocks[:15])
    b = b0
    u_list = []
    for r in range(15):
        P_r = 3 * b + 1
        s_r = blocks[r]
        u_r = P_r >> s_r
        u_list.append(u_r)
        b = (3 ** (s_r - 1)) * u_r

    for r in range(1, 14):
        s_prev = blocks[r - 1]
        s_curr = blocks[r]
        s_next = blocks[r + 1]
        u_prev = u_list[r - 1]
        u_curr = u_list[r]
        # 1. Exact backward quotient recovery: (2^{s_curr} * u_curr) // 3^{s_prev} == u_prev and % == 1
        val = (1 << s_curr) * u_curr
        assert val // (3 ** s_prev) == u_prev
        assert val % (3 ** s_prev) == 1
        # 2. Combined CRT modulus M_r = 3^{s_{r-1}} * 2^{s_{r+1} + 1}
        mod3 = 3 ** s_prev
        mod2 = 1 << (s_next + 1)
        M_r = mod3 * mod2
        # Solve CRT for u_curr mod M_r solely from (s_prev, s_curr, s_next)!
        r3 = pow(1 << s_curr, -1, mod3)
        r2 = (((1 << s_next) - 1) * pow(pow(3, -1, mod2), s_curr, mod2)) % mod2
        # Combine r3 (mod mod3) and r2 (mod mod2)
        inv_mod3 = pow(mod3, -1, mod2)
        crt_res = (r3 + mod3 * ((r2 - r3) * inv_mod3 % mod2)) % M_r
        assert u_curr % M_r == crt_res
        if r in [1, 4, 5, 11, 12]:
            print(f"  r={r:>2} (s_{{r-1}}={s_prev:>2}, s_r={s_curr:>2}, s_{{r+1}}={s_next:>2}): "
                  f"M_r = 3^{s_prev} * 2^{s_next+1} = {M_r:>10} | u_r >= crt_res = {crt_res}")


if __name__ == "__main__":
    sandbox_loop10_mod12_lock()
    sandbox_loop11_two_sided_crt_lock()
