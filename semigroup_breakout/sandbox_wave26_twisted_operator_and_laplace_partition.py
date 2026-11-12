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
    print("\nALL WAVE 26 MOVE 1 & MOVE 2 SANDBOX CHECKS PASSED (0 FAILURES)!")


if __name__ == "__main__":
    test_move1_kneading_renewal_and_phase_debt()
    test_move2_rational_laplace_poisson_partition()
