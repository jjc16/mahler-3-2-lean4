"""
Wave 26 Discovery Sandbox: Executing Move 1 (Exact Parry Kneading Renewal Operator,
Multi-Scale Phase Non-Concentration, & Sub-FLP Reduction) and Move 2 (Rational
Laplace-Poisson Origin Partition Function Z_N^rat(W), Euler Inequalities (1+1/n)^n < 3
and 2*(m-1)^m <= m^m, Discrete Poisson Positivity, & Exact Z = empty Equivalence)
(SB.141-SB.148).
"""

import cmath
import math
from fractions import Fraction
from sandbox_wave23_fourier_frontier_and_parseval_barrier import (
    build_parry_tree_levels,
    fft_radix2,
)


def kneading_spine_and_splits(max_n: int):
    B = 1
    psi = 0
    B_list = [1]
    splits = []
    psi_spine = [0]
    for k in range(max_n):
        thresh = 1 << (k + 1)
        if 3 * B <= thresh:
            B = 3 * B
            psi = 3 * psi
        else:
            splits.append((k + 1, 3 * psi))
            B = 3 * B - thresh
            psi = 3 * psi + (1 << k)
        B_list.append(B)
        psi_spine.append(psi)
    return B_list, splits, psi_spine


def test_move1_kneading_renewal_and_phase_debt():
    print("=== Move 1 (SB.141-SB.144): Kneading Renewal, Phase Syzygy, & 3-Adic Debt Law ===")
    failures = 0
    MAX_N = 18
    levels = build_parry_tree_levels(MAX_N)
    B_list, splits, psi_spine = kneading_spine_and_splits(MAX_N)

    # 1. SB.141: Exact Kneading Renewal Decomposition of |C_N|:
    for N in range(0, MAX_N + 1):
        c_N = len(levels[N])
        rhs = 1 + sum(len(levels[N - m]) for m, _ in splits if m <= N)
        if c_N != rhs:
            failures += 1

    # 2. SB.142: Coalesced (000 + 100) & (m2=3, m3=9) 9*b_pref3 === 13*b_pref2 (mod 2^N) syzygy:
    # Check psi_pref(3) == 9 and psi_pref(9) == 9477 == 13 * 3^6:
    split_dict = dict(splits)
    if split_dict[1] != 0 or split_dict[3] != 9 or split_dict[9] != 9477:
        failures += 1
    for N in range(3, 20):
        mod = 1 << N
        b_pref2 = ((-9) * pow(3, -3, mod)) % mod
        b_pref3 = ((-9477) * pow(3, -9, mod)) % mod
        if (3 * b_pref2 + 1) % mod != 0:
            failures += 1
        if (27 * b_pref3 + 13) % mod != 0:
            failures += 1
        if (9 * b_pref3) % mod != (13 * b_pref2) % mod:
            failures += 1

    # 3. SB.143: Multi-Scale Phase Non-Concentration & No-Wraparound 3-Adic Debt Law:
    for K in range(6, 15):
        mod_K = 1 << K
        for s in [1, 2, 3]:
            mod_sub = 1 << (K - s)
            inv3s = pow(3, -s, mod_sub)
            for yK in range(1, mod_K, 2):
                y_sub = (yK * inv3s) % mod_sub
                dK = min(yK, mod_K - yK)
                d_sub = min(y_sub, mod_sub - y_sub)
                if dK + (3 ** s) * d_sub < mod_sub:
                    if dK != (3 ** s) * d_sub:
                        failures += 1

    # 4. SB.144: Sub-FLP 8:7 Reduction at Spectral Rate Lambda = 7/5 = 1.40 < 3/2:
    # Verify 6561 < 13 * 512, 5764801 < 15 * 390625, and 15^k < 17^k <= |C_{7*k}|:
    if not (3 ** 8 < 13 * (2 ** 9) and (7 ** 8) < 15 * (5 ** 8)):
        failures += 1
    for k in range(1, 3):
        c_7k = len(levels[7 * k]) if 7 * k <= MAX_N else None
        if c_7k is not None and not (15 ** k < 17 ** k <= c_7k):
            failures += 1

    print(f"Move 1 (SB.141-SB.144) verified: failures = {failures}")
    assert failures == 0


def test_move2_rational_laplace_poisson_partition():
    print("\n=== Move 2 (SB.145-SB.148): Rational Laplace-Poisson Origin Partition Z_N^rat(W) ===")
    failures = 0
    levels = build_parry_tree_levels(16)

    # 1. SB.145: Pure-Nat Euler Sandwich for ALL m >= 2:
    #    - 2 * (m - 1)^m <= m^m  (i.e. ((m-1)/m)^m <= 1/2, damping by <= 1/2 per 2^W block!)
    #    - m^(m - 1) < 3 * (m - 1)^(m - 1)  (i.e. ((m-1)/m)^(m-1) > 1/3, survivor weight > 1/3!)
    for m in range(2, 120):
        if not (2 * ((m - 1) ** m) <= (m ** m)):
            print(f"Upper Euler failed at m={m}")
            failures += 1
        if not ((m ** (m - 1)) < 3 * ((m - 1) ** (m - 1))):
            print(f"Lower Euler failed at m={m}")
            failures += 1

    # 2. SB.146-SB.147: Exact Rational Partition Function Z_N^rat(W) = sum_{w in C_N} ((2^W - 1)/2^W)^{b0(w)}:
    #    - Whenever ANY positive survivor b0 in [1, 2^W) exists in B_N, Z_N^rat(W) > 4/3!
    #    - Whenever NO survivor exists in [1, k * 2^W), Z_N^rat(W) <= 1 + |C_N| / 2^k!
    #    - Also compare L1 Poisson bound vs Signed Poisson sum!
    W = 4
    L = 1 << W  # 16
    r = (L - 1) / L  # 15/16 = 0.9375
    print(f"{'N':>2s} | {'PosSurv <16':>11s} | {'MinPos b0':>9s} | {'Z_N^rat(4)':>11s} | {'4/3 Thresh':>10s} | {'Poisson Main':>12s} | {'Poisson L1 Err':>14s}")
    print("-" * 92)
    for N in range(4, 17):
        mod = 1 << N
        inv3 = pow(3, -N, mod)
        b_list = sorted(((-psi) * inv3) % mod for _, psi in levels[N])
        pos_in_box = [b for b in b_list if 1 <= b < L]
        min_pos = b_list[1] if len(b_list) > 1 else None
        z_rat = sum((r ** b) for b in b_list)

        if len(pos_in_box) >= 1 and not (z_rat > 4.0 / 3.0):
            failures += 1
        if min_pos is not None:
            k_empty = min_pos // L
            tail_upper = 1.0 + (len(b_list) - 1) * (0.5 ** k_empty)
            if not (z_rat <= tail_upper + 1e-12):
                failures += 1

        # Exact Discrete Poisson DFT Check:
        ind = [0] * mod
        for b in b_list:
            ind[b] = 1
        spec = fft_radix2(ind)
        # Z_N^rat = ((1 - r^mod) / mod) * sum_{h=0}^{mod-1} S(h; N) / (1 - r * exp(-2*pi*i*h/mod))
        pref = (1.0 - (r ** mod)) / mod
        p_main = pref * len(b_list) / (1.0 - r)
        p_signed = 0.0 + 0.0j
        p_l1 = 0.0
        for h in range(1, mod):
            denom = 1.0 - r * cmath.exp(-2j * math.pi * h / mod)
            # Check strict Poisson real-part positivity Re(1 / denom) > 0.5:
            if (1.0 / denom).real <= 0.5 - 1e-12:
                failures += 1
            term = pref * spec[h] / denom
            p_signed += term
            p_l1 += abs(term)
        if abs((p_main + p_signed.real) - z_rat) > 1e-7:
            failures += 1
        if N in [4, 6, 8, 10, 12, 14, 16]:
            print(f"{N:2d} | {len(pos_in_box):11d} | {str(min_pos):>9s} | {z_rat:11.6f} | {4/3:10.6f} | {p_main:12.6f} | {p_l1:14.2f}")

    print(f"Move 2 (SB.145-SB.148) verified: failures = {failures}")
    assert failures == 0


def dp_all_for_single_h(h_odd: int, target_n: int, splits: list[bool], spine_psi: list[int], inv3: list[int]) -> complex:
    """Exact O(N^2) memoized evaluation of S(h_odd; target_n) along the 3^(-1)-orbit of h_odd."""
    memo: dict[tuple[int, int], complex] = {(0, 0): 1.0 + 0.0j}

    def solve(h: int, n: int) -> complex:
        if n == 0:
            return 1.0 + 0.0j
        h &= (1 << n) - 1
        key = (h, n)
        if key in memo:
            return memo[key]
        mod = 1 << n
        b_leaf = ((-spine_psi[n]) * inv3[n]) % mod
        total = cmath.exp(2j * math.pi * ((h * b_leaf) % mod) / mod)
        for j in range(n):
            if splits[j]:
                m = n - 1 - j
                shift_b = ((-pow(3, m + 1, mod) * spine_psi[j]) * inv3[n]) % mod
                phase = cmath.exp(2j * math.pi * ((h * shift_b) % mod) / mod)
                if m == 0:
                    total += phase
                else:
                    mod_m = 1 << m
                    h_child = (h * pow(3, -(j + 1), mod_m)) % mod_m
                    total += phase * solve(h_child, m)
        memo[key] = total
        return total

    return solve(h_odd, target_n)


def test_move1_quadratic_dp_and_hensel_300() -> None:
    print("\n=== Reproducible O(N^2) Kneading-Renewal Fourier DP Out to N = 300 ===")
    max_n = 300
    spine_b = [1]
    spine_psi = [0]
    splits: list[bool] = []
    cyl_counts = [1]
    for n in range(1, max_n + 1):
        j = n - 1
        b = spine_b[-1]
        psi = spine_psi[-1]
        if 3 * b <= (1 << (j + 1)):
            splits.append(False)
            spine_b.append(3 * b)
            spine_psi.append(3 * psi)
        else:
            splits.append(True)
            spine_b.append(3 * b - (1 << (j + 1)))
            spine_psi.append(3 * psi + (1 << j))
        c_n = 1 + sum(cyl_counts[n - 1 - k] for k in range(n) if splits[k])
        cyl_counts.append(c_n)

    inv3 = [1] * (max_n + 1)
    for n in range(1, max_n + 1):
        inv3[n] = pow(3, -n, 1 << n)

    # 1. Exact cross-check against full FFT at N = 12 across ALL odd h < 4096:
    levels12 = build_parry_tree_levels(12)
    mod12 = 1 << 12
    inv3_12 = inv3[12]
    ind12 = [0] * mod12
    for _, psi in levels12[12]:
        ind12[((-psi) * inv3_12) % mod12] = 1
    spec12 = fft_radix2(ind12)
    failures = 0
    for h in range(1, mod12, 2):
        val_dp = dp_all_for_single_h(h, 12, splits, spine_psi, inv3)
        if abs(val_dp - spec12[h]) > 1e-7:
            failures += 1
    assert failures == 0, f"DP vs FFT mismatch count: {failures}"

    # 2. Upward Hensel beam search (beam width = 16) + structured families out to N = 300:
    beam = [1, 3, 5, 7]
    hensel_best: dict[int, float] = {}
    for n in range(3, max_n + 1):
        cands = set()
        half = 1 << (n - 1)
        for h_prev in beam:
            # Upward Hensel step: y_{n} = 3 * y_{n-1} mod 2^(n-1) lifts to two odd h in mod 2^n
            h_base = (3 * h_prev) & (half - 1)
            cands.add(h_base)
            cands.add(h_base + half)
        cands.update([1, 3, pow(3, n // 2, 1 << n)])
        scored = [(abs(dp_all_for_single_h(h, n, splits, spine_psi, inv3)), h) for h in cands]
        scored.sort(reverse=True)
        beam = [h for _, h in scored[:16]]
        hensel_best[n] = scored[0][0]

    print(f"{'N':>3s} | {'rho(h=1)':>9s} | {'rho(3^(N/2))':>12s} | {'rho(Hensel beam)':>16s} | {'Lambda_Hensel':>13s}")
    print("-" * 66)
    for n in [50, 100, 150, 200, 250, 300]:
        c_n = cyl_counts[n]
        r1 = (abs(dp_all_for_single_h(1, n, splits, spine_psi, inv3)) / c_n) ** (1.0 / n)
        r3 = (abs(dp_all_for_single_h(pow(3, n // 2, 1 << n), n, splits, spine_psi, inv3)) / c_n) ** (1.0 / n)
        rh = (hensel_best[n] / c_n) ** (1.0 / n)
        lam = (hensel_best[n]) ** (1.0 / n)
        print(f"{n:3d} | {r1:9.5f} | {r3:12.5f} | {rh:16.5f} | {lam:13.5f}")
    print("O(N^2) DP verified exact against full 4096-point FFT at N=12 (0 failures)!")


if __name__ == "__main__":
    test_move1_kneading_renewal_and_phase_debt()
    test_move2_rational_laplace_poisson_partition()
    test_move1_quadratic_dp_and_hensel_300()
    print("\nALL WAVE 26 MOVE 1, MOVE 2 & N=300 DP CHECKS PASSED (0 FAILURES)!")
