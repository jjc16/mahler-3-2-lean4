"""
Semigroup Breakout — Loop 4:
1. Exact Two-Orbit Archimedean Repulsion & Wronskian Elimination:
   Given two surviving companions alpha_1 < alpha_2, let beta = alpha_2 - alpha_1 > 0.
   At every step k:
     beta * (3/2)^k = D_k + delta_k,   where D_k = g_k(b_2) - g_k(b_1) in N, |delta_k| < 1/2.
   Wait: with our Round 3 / Campaign 2 pinching bound (0 <= f_k < 9/19 on s_r >= 3 segments,
   or at the divergence step n_0 where one is in [0, 1/3) and the other is in [1/3, 1/2)):
   What is the EXACT interval for delta_{n_0} = f_{n_0}(alpha_2) - f_{n_0}(alpha_1) at the divergence step n_0,
   and how does that constrain beta = alpha_2 - alpha_1?
2. Testing Multi-Step Padé / Wronskian Elimination on Single and Double Orbits.
"""

from fractions import Fraction
from loop2_pade_lll_and_divergence import find_all_surviving_seeds_in_range, binary_orbit_trace


def analyze_divergence_pinch():
    print("=== LOOP 4A: Exact Divergence-Step Fractional-Part Split [0, 1/3) vs [1/3, 1/2) ===")
    surv = find_all_surviving_seeds_in_range(20000, 28)
    print(f"Surviving seeds in [1, 20000] at step 28: {[s[0] for s in surv]}")
    for i in range(len(surv)):
        for j in range(i + 1, len(surv)):
            b1, L1, U1 = surv[i]
            b2, L2, U2 = surv[j]
            g1, eps1 = binary_orbit_trace(b1, 28)
            g2, eps2 = binary_orbit_trace(b2, 28)
            n0 = next((k for k in range(28) if eps1[k] != eps2[k]), 28)
            diff_b = b2 - b1
            v2 = (diff_b & -diff_b).bit_length() - 1
            q = diff_b >> v2
            D_n0 = g2[n0] - g1[n0]
            assert v2 == n0 and D_n0 == (3 ** n0) * q
            # Check the companion interval for f_{n0} = alpha (3/2)^{n0} - g_{n0}
            f1_lo = L1 * Fraction(3 ** n0, 2 ** n0) - g1[n0]
            f1_hi = U1 * Fraction(3 ** n0, 2 ** n0) - g1[n0]
            f2_lo = L2 * Fraction(3 ** n0, 2 ** n0) - g2[n0]
            f2_hi = U2 * Fraction(3 ** n0, 2 ** n0) - g2[n0]
            if i == 0 and j <= 4:
                print(f"  ({b1:>4}, {b2:>5}): n0={n0:>2}, q={q:>4}, D_n0={D_n0:>6} | "
                      f"eps_n0=({eps1[n0]},{eps2[n0]}) | "
                      f"f1 in [{float(f1_lo):.4f}, {float(f1_hi):.4f}), "
                      f"f2 in [{float(f2_lo):.4f}, {float(f2_hi):.4f})")


def analyze_power_of_three_mod_64_trap():
    print("\n=== LOOP 4B: Verifying the Exact 3^{m+3} + 13 = 243*(3^{m-2} - 1) + 256 Identity ===")
    for m in range(2, 200, 2):
        lhs = (3 ** (m + 3)) + 13
        rhs = 243 * ((3 ** (m - 2)) - 1) + 256
        assert lhs == rhs
        div256 = (lhs % 256 == 0)
        mod64 = ((m - 2) % 64 == 0)
        assert div256 == mod64
    print("  Verified for all even m in [2, 200): 256 | (3^{m+3} + 13) <=> 64 | (m - 2)!")
    for k in range(0, 6):
        m = 64 * k + 2
        P1 = ((3 ** (m + 3)) + 13) // 4
        s1 = (P1 & -P1).bit_length() - 1
        u1 = P1 >> s1
        b2 = (3 ** (s1 - 1)) * u1
        P2 = 3 * b2 + 1
        s2 = (P2 & -P2).bit_length() - 1
        print(f"  k={k} (m={m:>3}): s_0=2, s_1={s1:>2}, u_1_mod_8={u1 % 8}, s_2={s2}")


if __name__ == "__main__":
    analyze_divergence_pinch()
    analyze_power_of_three_mod_64_trap()
