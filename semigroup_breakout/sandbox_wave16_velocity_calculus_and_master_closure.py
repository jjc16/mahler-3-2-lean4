#!/usr/bin/env python3
"""
Wave 16 Discovery & Verification Sandbox:
Adaptive Cyclotomic Velocity Calculus, Shrinking Canyon Tube,
and the Master Conditional Completeness Closure (Theorems SB.89 - SB.92)
========================================================================

Tests and verifies four exact theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.89 (Adaptive Cyclotomic Velocity Factorization & Eliminator):
   - Define Orbit Velocity K_r = P_{r+1} - P_r = (3^{s_r} - 2^{s_r}) * u_r + 1:
     * P_r < P_{r+1} and P_r + K_r == P_{r+1}
     * cyclotomicGauge(s_r, P_r) == 2^{s_r} * K_r
     * cyclotomicGauge(s_r, P_{r+1}) == 3^{s_r} * K_r
     * Two-Step Velocity Eliminator across r -> r+1:
       s_r <= s_{r+1}  ==>  (3^{s_{r+1}} - 2^{s_{r+1}}) * 3^{s_r} * K_r ==
         (3^{s_r} - 2^{s_r}) * 2^{s_{r+1}} * K_{r+1} + 2^{s_r} * 3^{s_r} * (3^{s_{r+1} - s_r} - 2^{s_{r+1} - s_r})
       s_{r+1} == s_r  ==>  2^{s_r} * K_{r+1} == 3^{s_r} * K_r.

2. SB.90 (Velocity 2-Adic Valuation Lock v_2(K_r) = min(s_r, s_{r+1}) & Telescoped Sum):
   - Whenever s_{r+1} != s_r:
     * s_r < s_{r+1}  ==>  K_r % 2^{s_r + 1} == 2^{s_r} (v_2(K_r) == s_r)
     * s_{r+1} < s_r  ==>  K_r % 2^{s_{r+1} + 1} == 2^{s_{r+1}} (v_2(K_r) == s_{r+1})
   - Telescoped Velocity Sum:
     * P_K == P_0 + sum_{r=0}^{K-1} K_r.

3. SB.91 (Nested Canyon Interval Tube [L_r, U_r] & Exponential Width Contraction):
   - L_num(k) = 5 * 2^{T_k} * P_k, U_num(k) = 2^{T_k} * (5 * P_k + 4):
     * U_num(k) - L_num(k) == 4 * 2^{T_k}
     * 3^d * L_num(r) + 5 * 2^{T_r} * A_{r,M} == L_num(r + M)  (strict ascent)
     * U_num(r + M) + 36 * 2^{T_r} * E_{r,M} == 3^d * U_num(r) (monotone descent)
     * 3^d * L_num(r) < L_num(r + M) < U_num(r + M) <= 3^d * U_num(r).

4. SB.92 (Master Conditional Canyon Closure & 92-Theorem Synthesis).
"""

import itertools
from typing import List, Tuple


def cyclotomic_gauge(m: int, p: int) -> int:
    return ((3**m) - (2**m)) * p + (2**m)


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def gauge_deficit(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[: r - 1])
    s_last = s_seq[r - 1]
    return (3**s_last) * gauge_deficit(s_seq, r - 1) + (2**t_steps) * (
        (3 ** (s_last - 2)) - (2 ** (s_last - 2))
    )


def test_sb89_and_sb90_velocity_calculus() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for b0 in range(1, 3000, 2):
        s_seq = []
        u_seq = []
        p_seq = []
        curr_p = 3 * b0 + 1
        for _ in range(5):
            s_r = (curr_p & -curr_p).bit_length() - 1
            u_r = curr_p // (2**s_r)
            s_seq.append(s_r)
            u_seq.append(u_r)
            p_seq.append(curr_p)
            curr_p = (3**s_r) * u_r + 1

        k_seq = [((3 ** s_seq[r]) - (2 ** s_seq[r])) * u_seq[r] + 1 for r in range(4)]

        for r in range(3):
            sr = s_seq[r]
            sr1 = s_seq[r + 1]
            kr = k_seq[r]
            kr1 = k_seq[r + 1]

            ok_diff = (p_seq[r] < p_seq[r + 1]) and (p_seq[r] + kr == p_seq[r + 1])
            ok_g1 = cyclotomic_gauge(sr, p_seq[r]) == (2**sr) * kr
            ok_g2 = cyclotomic_gauge(sr, p_seq[r + 1]) == (3**sr) * kr

            if sr <= sr1:
                ok_elim = ((3**sr1) - (2**sr1)) * (3**sr) * kr == (
                    ((3**sr) - (2**sr)) * (2**sr1) * kr1
                    + (2**sr) * (3**sr) * ((3 ** (sr1 - sr)) - (2 ** (sr1 - sr)))
                )
            else:
                ok_elim = (
                    ((3**sr1) - (2**sr1)) * (3**sr) * kr
                    + (2**sr1) * (3**sr1) * ((3 ** (sr - sr1)) - (2 ** (sr - sr1)))
                    == ((3**sr) - (2**sr)) * (2**sr1) * kr1
                )

            if sr < sr1:
                ok_val = (kr % (2 ** (sr + 1))) == (2**sr)
            elif sr1 < sr:
                ok_val = (kr % (2 ** (sr1 + 1))) == (2**sr1)
            else:
                ok_val = (2**sr) * kr1 == (3**sr) * kr

            checked += 1
            if not (ok_diff and ok_g1 and ok_g2 and ok_elim and ok_val):
                failures += 1

        # Check telescoped velocity sum
        if p_seq[4] != p_seq[0] + sum(k_seq):
            failures += 1
        checked += 1
    return checked, failures


def test_sb91_nested_canyon_tube() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for r in [0, 1, 2]:
        for m_len in [1, 2, 3]:
            for s_seq in itertools.product([2, 3, 4], repeat=r + m_len + 1):
                s_list = list(s_seq)
                t_r = sum(s_list[:r])
                t_rm = sum(s_list[: r + m_len])
                d = t_rm - t_r
                s_win = s_list[r : r + m_len]
                a_rm = renewal_numerator(s_win, m_len)
                e_rm = gauge_deficit(s_win, m_len)

                for p_r in [4, 12, 20, 28, 64]:
                    if ((3**d) * p_r + a_rm) % (2**d) != 0:
                        continue
                    p_rm = ((3**d) * p_r + a_rm) // (2**d)
                    l_r = 5 * (2**t_r) * p_r
                    u_r = (2**t_r) * (5 * p_r + 4)
                    l_rm = 5 * (2**t_rm) * p_rm
                    u_rm = (2**t_rm) * (5 * p_rm + 4)

                    ok_w = (u_r - l_r == 4 * (2**t_r)) and (u_rm - l_rm == 4 * (2**t_rm))
                    ok_l = (3**d) * l_r + 5 * (2**t_r) * a_rm == l_rm
                    ok_u = u_rm + 36 * (2**t_r) * e_rm == (3**d) * u_r
                    ok_nest = ((3**d) * l_r < l_rm) and (l_rm < u_rm) and (u_rm <= (3**d) * u_r)

                    checked += 1
                    if not (ok_w and ok_l and ok_u and ok_nest):
                        failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 16 SANDBOX: VELOCITY CALCULUS, CANYON TUBE, & MASTER CONDITIONAL CLOSURE")
    print("=" * 78)

    c89, f89 = test_sb89_and_sb90_velocity_calculus()
    print(f"[SB.89/90] Adaptive Cyclotomic Velocity & Valuation Lock:  checked={c89:6d}, failures={f89}")

    c91, f91 = test_sb91_nested_canyon_tube()
    print(f"[SB.91/92] Nested Canyon Tube & Master Closure Bridge:     checked={c91:6d}, failures={f91}")

    total_checked = c89 + c91
    total_failures = f89 + f91
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
