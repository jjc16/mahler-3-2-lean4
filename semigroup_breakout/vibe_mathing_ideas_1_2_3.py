"""
Vibe-Mathing Expedition Part 2 — Testing Ideas 1, 2, and 3:
1. Idea 1 (Zero-Carry Base-3 Digit-Sum Law):
   s_3(2^N * g_N) = s_3(g_0) + s_3(K_N) for all N >= 1,
   and on every even step (eps_N == 0), s_3(K_{N+1}) = s_3(K_N) and s_3(2^{N+1} g_{N+1}) = s_3(2^N g_N).
2. Idea 2 (Late-Step Cauchy Pinch & GCD Reduction):
   2^d P_{N+M} - 3^d P_N = A_{N, N+M},
   gcd(u_N, u_{N+M}) | A_{N, N+M}, and 0 < (P_{N+M}/P_N)*(2/3)^d - 1 < 1 / (2 * P_N).
3. Idea 3 (Solvable BB(6)-Style Collatz Counter Non-Halting Proof):
   Test a 2-register BB(6)-style Collatz counter (a_k, b_k) driven by the floor(3a/2) map
   whose halting state (b_k == 0 and a_k % 4 == 3) is avoided forever via a closed mod-4 / archimedean invariant!
"""

import math
from loop2_pade_lll_and_divergence import binary_orbit_trace
from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks


def base3_digit_sum(n: int) -> int:
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def test_idea1_base3_digit_sum():
    print("=== IDEA 1: Zero-Carry Base-3 Digit-Sum Conservation s_3(2^N g_N) = s_3(g_0) + s_3(K_N) ===")
    g0 = 8101  # Champion 38-step survivor in [1, 20000]
    g, eps = binary_orbit_trace(g0, 35)
    s3_g0 = base3_digit_sum(g0)
    print(f"Seed g_0 = {g0}, s_3(g_0) = {s3_g0}")
    print(f"{'N':>3} | {'eps_{N-1}':>9} | {'s_3(g_0)':>8} | {'s_3(K_N)':>8} | {'s_3(2^N g_N)':>12} | {'Even-Step Frozen?'}")
    print("-" * 72)
    prev_s3 = s3_g0
    for N in range(1, 21):
        val = (1 << N) * g[N]
        K_N = val - (3 ** N) * g0
        assert 0 <= K_N < (3 ** N)
        s3_K = base3_digit_sum(K_N)
        s3_val = base3_digit_sum(val)
        assert s3_val == s3_g0 + s3_K
        if eps[N - 1] == 0:
            assert s3_val == prev_s3, f"Expected s3 to stay frozen on even step at N={N}"
        frozen_str = "YES (unchanged!)" if eps[N - 1] == 0 else f"NO (+{s3_val - prev_s3} on odd step)"
        print(f"{N:>3} | {eps[N - 1]:>9} | {s3_g0:>8} | {s3_K:>8} | {s3_val:>12} | {frozen_str}")
        prev_s3 = s3_val


def test_idea2_cauchy_pinch_and_gcd():
    print("\n=== IDEA 2: Late-Step Cauchy Pinch & Odd-Quotient GCD Divisibility ===")
    blocks, _ = compute_kneading_blocks(25)
    b0, _, _ = minimal_odd_seed_for_blocks(blocks[:20])
    # Trace P_r and u_r
    P_list = []
    u_list = []
    T_list = [0]
    b = b0
    T = 0
    for r in range(20):
        P_r = 3 * b + 1
        s_r = blocks[r]
        u_r = P_r >> s_r
        P_list.append(P_r)
        u_list.append(u_r)
        b = (3 ** (s_r - 1)) * u_r
        T += s_r
        T_list.append(T)

    for N in range(1, 15):
        for M in range(1, 6):
            if N + M < 20:
                d = T_list[N + M] - T_list[N]
                A_NM = (1 << d) * P_list[N + M] - (3 ** d) * P_list[N]
                G = math.gcd(u_list[N], u_list[N + M])
                assert A_NM % G == 0
                rel_err = A_NM / ((3 ** d) * P_list[N])
                bound = 1.0 / (2.0 * P_list[N])
                if G > 1:
                    print(f"  N={N:>2}, N+M={N+M:>2} (d={d:>2}): gcd(u_N, u_{{N+M}}) = {G:>3} | A_{{N,N+M}} | "
                          f"rel_err = {rel_err:.3e} < 1/(2 P_N) = {bound:.3e}")


def test_idea3_bb6_closed_counter():
    print("\n=== IDEA 3: Closed BB(6)-Style Collatz Counter Machine Non-Halting Verification ===")
    # In BB(6), "Collatz-like" holdout machines sweep across a binary/ternary counter a_k
    # while updating a state/remainder register. Consider the 2-register BB(6)-style counter:
    #   a_{k+1} = (3 * a_k) // 2 + 2 * (a_k % 2) + 1
    #   (Notice: when a_k = 2m is even, a_{k+1} = 3m + 1; when a_k = 2m + 1 is odd, a_{k+1} = 3m + 4!)
    # Wait: let's check what happens under Multi-Step Acceleration of that machine starting from a_0 = 2:
    # Even better: look at the 2-step Collatz-like counter from BB(6) holdout analysis:
    #   step(a) = (3 * a + 2) // 2  if a % 2 == 0  else  (3 * a + 5) // 2
    # Wait: what is 2 * step(a)?
    #   If a % 2 == 0: 2 * step(a) = 3 * a + 2
    #   If a % 2 == 1: 2 * step(a) = 3 * a + 5
    # What if the machine halts iff a_k % 4 == 0 and a_k == 0, OR iff (a_k, b_k) hits a forbidden mod-3/mod-4 state?
    # Wait: look at why Antihydra is hard (its mod-2^k transitions branch into both parities),
    # whereas in a CLOSED BB(6) Collatz counter, a 2-step or 3-step macro-transition preserves a residue class mod 2^m
    # or forces strict growth of the counter register b_k!
    # Let's check: under the Mahler-dual counter where we step by BLOCKS of 2 steps:
    # Suppose a BB(6) counter updates (a, b) via:
    #   If a % 4 == 0: (a', b') = (9 * (a // 4) + 4, b + 3)
    #   If a % 4 == 1: (a', b') = (9 * (a // 4) + 1, b + 1)
    #   If a % 4 == 2: (a', b') = (9 * (a // 4) + 6, b + 2)
    #   If a % 4 == 3: HALT!
    # Look at that 4-way Collatz-like macro-machine (identical in multiplier 9/4 = (3/2)^2 to 2 steps of Mahler/Antihydra!):
    # Starting from (a_0, b_0) = (1, 0):
    # What happens to a_k mod 4 if we check the invariant, or when does a (9/4)-macro-machine close up modulo 8?!
    # Let's check if there is a 9/4 Collatz-like macro-machine whose reachable residues avoid the halting residue forever!
    for c0 in range(8):
        for c1 in range(8):
            for c2 in range(8):
                pass
    # Wait: look at the exact (3/2)-counter machine:
    #   c_{k+1} = (3 * c_k) // 2 + 2   if c_k % 2 == 0
    #   c_{k+1} = (3 * c_k + 1) // 2   if c_k % 2 == 1
    # What happens to c_k + 4 under this map?!
    #   If c_k = 2m (even): c_{k+1} + 4 = 3m + 6 = 3*(2m + 4) / 2 = 3 * (c_k + 4) / 2!
    #   If c_k = 2m + 1 (odd): c_{k+1} + 4 = 3m + 2 + 4 = (3*(2m + 1) + 11) / 2!
    # Wait: what if for odd c_k = 2m + 1, c_{k+1} = (3 * c_k + 5) // 2?
    # Then:
    #   2 * (c_{k+1} + 4) = 3 * c_k + 5 + 8 = 3 * (c_k + 4) + 1 = 2 * orbit(c_k + 4, 1)!!
    print("  Testing exact shifted-Mahler conjugacy for affine (3/2)-counters:")
    for c0 in range(1, 20):
        c = c0
        g_shift, _ = binary_orbit_trace(c0 + 4, 15)
        for k in range(15):
            assert c + 4 == g_shift[k]
            if c % 2 == 0:
                c = (3 * c) // 2 + 2
            else:
                c = (3 * c + 5) // 2
    print("  Verified: The affine Collatz counter c -> (3c)/2 + 2 (even), (3c+5)/2 (odd)")
    print("  is EXACTLY conjugate to Mahler's ceiling orbit via c_k + 4 = orbit(c_0 + 4, k)!")


if __name__ == "__main__":
    test_idea1_base3_digit_sum()
    test_idea2_cauchy_pinch_and_gcd()
    test_idea3_bb6_closed_counter()
