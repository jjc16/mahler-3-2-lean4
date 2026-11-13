"""
Wave 27 Capstone Sandbox: Verifying Exact (N + 1) Width-Class Rank Compression of
parryCylTree, Upward Hensel Phase Dichotomy, At-Most-One-Rogue-d-Per-q Uniqueness
(Barrier #7), and Dyadic Non-Zero Frequency Factorization (SB.149-SB.152).
"""

from sandbox_wave23_fourier_frontier_and_parseval_barrier import build_parry_tree_levels
from sandbox_wave26_twisted_operator_and_laplace_partition import kneading_spine_and_splits


def test_sb149_exact_width_class_compression():
    print("=== Test 1 (SB.149): Exact (N + 1) Width-Class Rank Compression of parryCylTree ===")
    failures = 0
    MAX_N = 18
    levels = build_parry_tree_levels(MAX_N)
    B_spine, _, _ = kneading_spine_and_splits(MAX_N)

    for N in range(0, MAX_N + 1):
        actual_widths = {B for B, _ in levels[N]}
        spine_image = {(1 << (N - r)) * B_spine[r] for r in range(N + 1)}
        if actual_widths != spine_image:
            print(f"Mismatch at N={N}: actual={actual_widths} vs image={spine_image}")
            failures += 1
        if len(actual_widths) > N + 1:
            failures += 1
    print(f"SB.149 verified across N=0..{MAX_N} (exact equality actual_widths == spine_image): failures = {failures}")
    assert failures == 0


def test_sb150_upward_hensel_dichotomy_and_rogue_uniqueness():
    print("=== Test 2 (SB.150): Upward Hensel Dichotomy & At-Most-One-Rogue-d-Per-q ===")
    failures = 0
    for k in range(3, 14):
        mod_k = 1 << k
        mod_k1 = 1 << (k + 1)
        for yk in range(1, mod_k, 2):
            dk = min(yk, mod_k - yk)
            base = (3 * yk) & (mod_k1 - 1)
            for yk1 in (base, (base + mod_k) & (mod_k1 - 1)):
                if yk1 % mod_k != (3 * yk) % mod_k:
                    failures += 1
                dk1 = min(yk1, mod_k1 - yk1)
                if not (8 * dk >= mod_k or 8 * dk1 >= mod_k1 or dk1 == 3 * dk):
                    failures += 1

    # Check at-most-one-rogue-d-per-q whenever 2 * R <= 3^A:
    for K in range(6, 13):
        modK = 1 << K
        for A in range(3, 8):
            pow3A = 3 ** A
            R = pow3A // 2  # satisfies 2 * R <= 3^A
            for q in range(1, 10):
                sols = [d for d in range(1, modK) if abs(pow3A * d - q * modK) < R]
                if len(sols) > 1:
                    failures += 1
    print(f"SB.150 verified: failures = {failures}")
    assert failures == 0


def test_sb151_dyadic_frequency_factorization():
    print("=== Test 3 (SB.151): Dyadic Non-Zero Frequency Factorization & High-Power Vanishing ===")
    failures = 0
    for N in range(2, 12):
        modN = 1 << N
        for W in range(1, N + 1):
            M = N - W
            modM = 1 << M
            for h in range(1, modN):
                if h % modM == 0:
                    if (h * (1 << W)) % modN != 0 or h % modN == 0:
                        failures += 1
                else:
                    v = (h & -h).bit_length() - 1
                    h_odd = h >> v
                    if not (v < M and h_odd % 2 == 1 and h_odd < (1 << (N - v)) and h == (1 << v) * h_odd):
                        failures += 1
    print(f"SB.151 verified: failures = {failures}")
    assert failures == 0


if __name__ == "__main__":
    test_sb149_exact_width_class_compression()
    test_sb150_upward_hensel_dichotomy_and_rogue_uniqueness()
    test_sb151_dyadic_frequency_factorization()
    print("ALL WAVE 27 CAPSTONE SANDBOX CHECKS PASSED (0 FAILURES)!")
