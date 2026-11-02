"""
Semigroup Breakout — Loop 3B:
Testing the Z_2-Symmetry-Breaking Generators:
1. The Archimedean Rung Ceiling: 2^{T_K + s_K} * u_K = 3^{T_K} P_0 + A_{0,K} < 3^{T_K} (P_0 + 1/2).
2. What happens if u_K = 1 (so b_{K+1} = 3^{s_K - 1}, a pure power of 3) or u_K is small?
3. Exhaustive survival census of [1, 50000] at steps 25..40: how many seeds survive?
"""

from loop2_pade_lll_and_divergence import companion_interval, binary_orbit_trace
from loop1_product_formula_and_pade import trace_post_horizon_survival


def test_pure_power_of_three_seeds():
    print("=== LOOP 3B.1: Fate of Pure Power-of-3 Odd States b = 3^m (which occur whenever u_K = 1) ===")
    for m in range(1, 25):
        b = 3 ** m
        die_blk, die_step, reason, blocks = trace_post_horizon_survival(b, max_blocks=20)
        print(f"  m={m:>2} (b = 3^{m:<2}): blocks={blocks[:5]}, dies at block {die_blk} (step {die_step}): {reason}")


def test_survivor_census():
    print("\n=== LOOP 3B.2: Survivor Census in [1, 20000] across Steps 20..40 ===")
    # Filter survivors progressively from step 1 to 40
    candidates = list(range(1, 20001))
    for step in range(1, 41):
        next_cand = []
        for b0 in candidates:
            L, U = companion_interval(b0, step)
            if L < U:
                next_cand.append(b0)
        candidates = next_cand
        if step in [10, 15, 20, 25, 28, 30, 32, 34, 35, 36, 37, 38, 39, 40] or len(candidates) <= 10:
            odd_cands = [c for c in candidates if c % 2 == 1]
            print(f"  Step {step:>2}: {len(candidates):>4} total ({len(odd_cands):>3} odd) | odd seeds: {odd_cands[:10]}")
            if not candidates:
                print(f"  --> ALL SEEDS IN [1, 20000] EXTINCT BY STEP {step}!")
                break


if __name__ == "__main__":
    test_pure_power_of_three_seeds()
    test_survivor_census()
