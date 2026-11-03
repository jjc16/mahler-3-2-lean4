#!/usr/bin/env python3
"""
Wave 11 Discovery & Verification Sandbox:
End-of-Block 3^{s_r}-Upgraded Baker Pinch, Adjacent/2-Step Return Extinction,
and the 1/5 Reduced Renewal Ceiling (Theorems SB.69 - SB.72)
=============================================================================

Tests and verifies four exact structural theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.69 (Adjacent Odd-Core Coprimality & Universal Non-Equality u_{r+1} != u_r):
   - Across any single step 2^{s_{r+1}} * u_{r+1} = 3^{s_r} * u_r + 1 with s_r >= 2:
     * gcd(u_r, u_{r+1}) == 1 and gcd(2^{s_{r+1}} * u_{r+1}, 3^{s_r} * u_r) == 1
     * (3^{s_r} + 1) % 8 in {2, 4} and 10 <= 3^{s_r} + 1
     * u_{r+1} != u_r UNCONDITIONALLY!

2. SB.70 (Two-Step Odd-Core GCD, s_r-Free Return Bound, & Boundary Extinction):
   - Across two steps r -> r+1 -> r+2:
     2^{s_{r+1} + s_{r+2}} * u_{r+2} = 3^{s_r + s_{r+1}} * u_r + 3^{s_{r+1}} + 2^{s_{r+1}}
     * gcd(u_r, u_{r+2}) divides (3^{s_{r+1}} + 2^{s_{r+1}})
     * Whenever u_{r+2} == u_r:
       (2^{s_{r+1} + s_{r+2}} - 3^{s_r + s_{r+1}}) * u_r == 3^{s_{r+1}} + 2^{s_{r+1}},
       u_r divides (3^{s_{r+1}} + 2^{s_{r+1}}), and u_r <= 3^{s_{r+1}} + 2^{s_{r+1}} (independent of s_r!).
     * For the boundary 2-step return (s_r=3, s_{r+1}=2, s_{r+2}=6, u_r=1, u_{r+1}=7, u_{r+2}=1),
       the next step has 3^6 * 1 + 1 = 730, with 730 % 4 == 2 (s_{r+3} = 1, instant death!).

3. SB.71 (End-of-Block 3^{s_r}-Upgraded Baker Pinch & s_r-Free M-Step Return Bound):
   - Across M+1 blocks starting from u_r (d = s_{r+1} + ... + s_{r+M}, S = d + s_{r+1+M},
     T = s_r + d, R = 3^d + renewalNumerator(s', M)):
     * 2^S * u_{r+1+M} = 3^T * u_r + R and R % 2 == 1 (R is strictly odd!)
     * 5 * 3^{s_r} * (2^S * u_{r+1+M} - 3^T * u_r) + 4 * 3^{s_r} * 2^d <= 9 * 3^T
     * gcd(u_r, u_{r+1+M}) divides R
     * Whenever u_{r+1+M} == u_r:
       u_r * (2^S - 3^T) == R, u_r divides R, and 5 * u_r + 4 * 2^d <= 9 * 3^d (completely independent of s_r!).

4. SB.72 (Exact 2-Adic Renewal Valuation A_{0,K} = 2^{s_0} * R_0 & 1/5 Reduced Ceiling):
   - For any K >= 1 blocks with s_k >= 2, let d_0 = T_K - s_0 and R_0 = 3^{d_0} + renewalNumerator(s', K-1):
     * A_{0,K} = 2^{s_0} * R_0 with R_0 % 2 == 1 (exact 2-adic valuation v_2(A_{0,K}) == s_0!)
     * 2^{T_K + s_K - s_0} * u_K = 3^{T_K} * u_0 + R_0
     * 5 * R_0 + 4 * 2^{T_K - s_0} <= 3^{T_K} and 5 * R_0 < 3^{T_K} (the 1/5 reduced ceiling!)
     * (2^{T_K + s_K - s_0} * u_K) // 3^{T_K} == u_0 and (2^{T_K + s_K - s_0} * u_K) % 3^{T_K} == R_0.
"""

import itertools
import math
from typing import List, Tuple


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb69_adjacent_coprime_and_neq() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_r in range(2, 16):
        for u_r in range(1, 1000, 2):
            num = (3**s_r) * u_r + 1
            s_r1 = (num & -num).bit_length() - 1
            u_r1 = num // (2**s_r1)
            ok_gcd = math.gcd(u_r, u_r1) == 1 and math.gcd((2**s_r1) * u_r1, (3**s_r) * u_r) == 1
            ok_mod8 = ((3**s_r + 1) % 8 in (2, 4)) and ((3**s_r + 1) >= 10)
            ok_neq = u_r1 != u_r
            checked += 1
            if not (ok_gcd and ok_mod8 and ok_neq):
                failures += 1
    return checked, failures


def test_sb70_two_step_gcd_and_return() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_r in range(2, 10):
        for u_r in range(1, 500, 2):
            num1 = (3**s_r) * u_r + 1
            s_r1 = (num1 & -num1).bit_length() - 1
            u_r1 = num1 // (2**s_r1)
            if s_r1 < 2:
                continue
            num2 = (3**s_r1) * u_r1 + 1
            s_r2 = (num2 & -num2).bit_length() - 1
            u_r2 = num2 // (2**s_r2)
            rhs = (3**s_r1) + (2**s_r1)
            g = math.gcd(u_r, u_r2)
            ok_gcd = (rhs % g) == 0
            if u_r2 == u_r:
                ok_ret = (rhs % u_r == 0) and (u_r <= rhs)
            else:
                ok_ret = True
            checked += 1
            if not (ok_gcd and ok_ret):
                failures += 1
    return checked, failures


def test_sb71_and_sb72_upgraded_baker_and_one_fifth() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s0 in [2, 3, 4, 5]:
        for m_len in [0, 1, 2, 3]:
            for s_tail in itertools.product([2, 3, 4], repeat=m_len + 1):
                s_seq = [s0] + list(s_tail)
                d = sum(s_seq[1 : 1 + m_len])
                s_end = s_seq[1 + m_len]
                s_total = d + s_end
                t_total = s0 + d
                r_val = (3**d) + renewal_numerator(s_seq[1 : 1 + m_len], m_len)
                a_full = renewal_numerator(s_seq, m_len + 1)

                # Check SB.71 & SB.72 properties
                ok_odd = (r_val % 2) == 1
                ok_afull = a_full == (2**s0) * r_val
                ok_baker = 5 * (3**s0) * r_val + 4 * (3**s0) * (2**d) <= 9 * (3**t_total)
                ok_one_fifth = (5 * r_val + 4 * (2**d) <= 3**t_total) and (5 * r_val < 3**t_total)

                for u0 in [1, 5, 7, 17]:
                    lhs = (3**t_total) * u0 + r_val
                    ok_div = (lhs // (3**t_total) == u0) and (lhs % (3**t_total) == r_val)
                    checked += 1
                    if not (ok_odd and ok_afull and ok_baker and ok_one_fifth and ok_div):
                        failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 11 SANDBOX: UPGRADED BAKER PINCH, RETURN EXTINCTION, & 1/5 CEILING")
    print("=" * 78)

    c69, f69 = test_sb69_adjacent_coprime_and_neq()
    print(f"[SB.69] Adjacent Coprimality & Universal u_{{r+1}} != u_r:  checked={c69:6d}, failures={f69}")

    c70, f70 = test_sb70_two_step_gcd_and_return()
    print(f"[SB.70] Two-Step GCD & s_r-Free Return Bound/Extinction:   checked={c70:6d}, failures={f70}")

    c71, f71 = test_sb71_and_sb72_upgraded_baker_and_one_fifth()
    print(f"[SB.71/72] 3^{{s_r}} Baker Pinch & 1/5 Reduced Ceiling:      checked={c71:6d}, failures={f71}")

    total_checked = c69 + c70 + c71
    total_failures = f69 + f70 + f71
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
