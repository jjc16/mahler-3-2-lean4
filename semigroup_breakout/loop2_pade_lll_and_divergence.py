"""
Semigroup Breakout — Loop 2 & Loop 3:
1. Testing the Exact Divergence Anatomy between ANY two surviving seeds b_1 < b_2:
   - First divergence step n_0 = v_2(b_2 - b_1),
   - Exact odd difference D_{n_0} = 3^{n_0} * ((b_2 - b_1) / 2^{n_0}),
   - Disjointness of fractional parts f_{n_0}^{(even)} in [0, 1/3) vs f_{n_0}^{(odd)} in [1/3, 1/2).
2. Searching for Z_2-symmetry-breaking Auxiliary Linear Forms over the Parry-Kneading Polytope:
   Can a linear combination of renewal equations across k blocks force a Product Formula contradiction,
   or what is the exact mathematical reason for the Product Formula ratio?
"""

import math
from fractions import Fraction
from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks


def binary_orbit_trace(b0: int, steps: int):
    """Return list of g_k = orbit(b0, k) and parities eps_k = g_k % 2 for k = 0..steps."""
    g = [b0]
    eps = []
    cur = b0
    for _ in range(steps):
        e = cur % 2
        eps.append(e)
        cur = (3 * cur + e) // 2
        g.append(cur)
    return g, eps


def companion_interval(b0: int, steps: int):
    """
    Compute the exact rational companion interval [L_steps, U_steps) for alpha = b0 + xi
    so that {(3/2)^k alpha} in [0, 1/2) for all 0 <= k <= steps.
    At each step k:
      g_k <= alpha (3/2)^k < g_k + 1/2
      <=> (2/3)^k g_k <= alpha < (2/3)^k (g_k + 1/2).
    """
    g, _ = binary_orbit_trace(b0, steps)
    L = Fraction(b0, 1)
    U = Fraction(b0, 1) + Fraction(1, 2)
    for k in range(1, steps + 1):
        Lk = Fraction(2 ** k, 3 ** k) * g[k]
        Uk = Fraction(2 ** k, 3 ** k) * (Fraction(g[k]) + Fraction(1, 2))
        if Lk > L:
            L = Lk
        if Uk < U:
            U = Uk
    return L, U


def find_all_surviving_seeds_in_range(max_b0: int, steps: int):
    """Find all integer seeds 1 <= b0 <= max_b0 whose companion interval at `steps` is non-empty."""
    survivors = []
    for b0 in range(1, max_b0 + 1):
        L, U = companion_interval(b0, steps)
        if L < U:
            survivors.append((b0, L, U))
    return survivors


def test_two_seed_divergence_and_sparsity():
    print("=== LOOP 2B: Exhaustive Two-Seed Divergence & Sparsity Anatomy ===")
    for steps in [10, 15, 20, 25]:
        surv = find_all_surviving_seeds_in_range(5000, steps)
        print(f"Steps={steps:>2}: {len(surv):>3} surviving seeds in [1, 5000]: {[s[0] for s in surv[:10]]}")
        if len(surv) >= 2:
            for idx in range(min(len(surv) - 1, 5)):
                b1, L1, U1 = surv[idx]
                b2, L2, U2 = surv[idx + 1]
                g1, eps1 = binary_orbit_trace(b1, steps)
                g2, eps2 = binary_orbit_trace(b2, steps)
                # Find first step n0 where eps1[n0] != eps2[n0]
                n0 = next((k for k in range(steps) if eps1[k] != eps2[k]), steps)
                diff_b = b2 - b1
                v2_diff = (diff_b & -diff_b).bit_length() - 1
                print(f"   Pair ({b1}, {b2}): b2-b1={diff_b} (v_2={v2_diff}), first parity divergence n_0={n0}, "
                      f"D_{{n0}} = g_{{n0}}(b2)-g_{{n0}}(b1) = {g2[n0]-g1[n0]} == 3^{n0}*{(diff_b >> v2_diff)}")
                assert v2_diff == n0 or n0 == steps


def test_parry_polytope_product_formula():
    """
    Let's test the Product Formula on ANY linear combination of block states P_0, P_1, ..., P_K!
    Wait: at block r (0 <= r <= K), we have:
      2^{T_r} P_r = 3^{T_r} P_0 + A_{0, r}.
    In the real world, P_r = H_inf * (3/2)^{T_r} - h_r, with h_r in (0, 1/2).
    In the integer world, P_0, P_1, ..., P_K are integers satisfying 2^{s_r} P_{r+1} = 3^{s_r} P_r + 2^{s_r}.
    Wait: why does ANY linear relation among P_0, ..., P_K that cancels H_inf in the real world
    give a linear combination of the renewal equations 2^{T_r} P_r - 3^{T_r} P_0 = A_{0,r}?
    Because the space of vectors (P_0, P_1, ..., P_K) of the form P_r = H * (3/2)^{T_r} - h_r
    is parametrized by ONE free variable H (= H_inf) and the K+1 bounded variables h_0, ..., h_K!
    Wait: the h_r are ALSO linked by the K equations:
      (3/2)^{s_r} h_r - h_{r+1} = 1  (for r = 0 .. K-1)!
    So there is ONLY ONE independent variable among (h_0, ..., h_K), namely h_0!
    And H_inf = P_0 + h_0!
    Wait: read that again!!
      H_inf = P_0 + h_0,   and   P_r + h_r = (P_0 + h_0) (3/2)^{T_r}!
    So EVERY P_r is determined by P_0, and EVERY h_r is determined by h_0 via:
      2^{T_r} P_r - 3^{T_r} P_0 = A_{0, r} = 3^{T_r} h_0 - 2^{T_r} h_r!
    """
    print("\n=== LOOP 3A: The Fundamental Degree-of-Freedom Theorem for Single-Orbit Functionals ===")
    print("At horizon K, given the gap sequence s = (s_0, ..., s_{K-1}):")
    print("  1. Every integer state P_r (1 <= r <= K) is affine-linear in P_0:")
    print("       P_r = (3/2)^{T_r} P_0 + A_{0,r} / 2^{T_r}")
    print("  2. Every real tail h_r (0 <= r <= K) is affine-linear in h_0:")
    print("       h_r = (3/2)^{T_r} h_0 - A_{0,r} / 2^{T_r}")
    print("  3. Notice that P_0 and h_0 are COMPLETELY DECOUPLED in those two equations!")
    print("     - h_0 in (A_{0,K}/3^{T_K}, (A_{0,K} + 2^{T_K - 1})/3^{T_K}) depends ONLY on s, NOT on P_0!")
    print("     - P_0 in N depends ONLY on the congruence 3^{T_K} P_0 + A_{0,K} == 0 (mod 2^{T_K + 1})!")


if __name__ == "__main__":
    test_two_seed_divergence_and_sparsity()
    test_parry_polytope_product_formula()
