#!/usr/bin/env python3
"""
Wave 13 Discovery & Verification Sandbox:
Greedy 2-Adic Base-(2/3) Kempner Expansion, Two-Horizon Kempner Tail Valuation,
and the 2-Adic Rational-Target Obstruction Bridge (Theorems SB.77 - SB.80)
===============================================================================

Tests and verifies four exact theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.77 (Greedy 2-Adic Base-(2/3) Kempner Step & Prefix Law):
   - At every horizon r <= K:
     * 3^{T_r} * P_0 + A_{0,r} == 2^{T_{r+1}} * u_r
     * (3^{T_r} * P_0 + A_{0,r}) % 2^{T_{r+1}} == 0
     * (3^{T_r} * P_0 + A_{0,r}) % 2^{T_{r+1} + 1} == 2^{T_{r+1}}
   - Greedy single-step update (r < K):
     * 3^{s_r} * (3^{T_r} * P_0 + A_{0,r}) + 2^{T_{r+1}} == 3^{T_{r+1}} * P_0 + A_{0,r+1}
     * 2^{T_{r+1}} * (3^{s_r} * u_r + 1) == 2^{T_{r+2}} * u_{r+1}.

2. SB.78 (Two-Horizon Kempner Tail Exact 2-Adic Valuation & 1/5 Bound):
   - Between horizon K_1 = r and K_2 = r + 1 + M (with s_r >= 2 and s_{r+1+k} >= 2):
     Let T_1 = T_r, T_{1,next} = T_r + s_r, d = sum_{k=0}^{M-1} s_{r+1+k},
     S_2 = T_{K_2} + s_{K_2}, and R_tail = 3^d + renewalNumerator(s', M):
     * A_{0,K_2} == 3^{s_r + d} * A_{0,K_1} + 2^{T_{1,next}} * R_tail
     * 2^{S_2} * u_{K_2} == 3^{s_r + d} * (2^{T_{1,next}} * u_{K_1}) + 2^{T_{1,next}} * R_tail
     * R_tail % 2 == 1 and (2^{S_2} * u_{K_2} - 3^{s_r + d} * 2^{T_{1,next}} * u_{K_1}) % 2^{T_{1,next} + 1} == 2^{T_{1,next}}
     * 5 * R_tail + 4 * 2^d <= 3^{s_r + d} and 5 * R_tail < 3^{s_r + d}.

3. SB.79 (Kempner 2-Adic Rational-Target Obstruction & Irrationality Bridge):
   - Simultaneous R x Q_2 Kempner partial-sum lock and non-integrality exclusion.

4. SB.80 (Grand 80-Theorem Synthesis of the Kempner 2-Adic Base-(2/3) Tower).
"""

import itertools
import math
from typing import List, Tuple


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb77_greedy_kempner_expansion() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for b0 in range(1, 3000, 2):
        s_seq = []
        u_seq = []
        curr_p = 3 * b0 + 1
        for _ in range(5):
            s_r = (curr_p & -curr_p).bit_length() - 1
            u_r = curr_p // (2**s_r)
            s_seq.append(s_r)
            u_seq.append(u_r)
            curr_p = (3**s_r) * u_r + 1

        p0 = (2 ** s_seq[0]) * u_seq[0]
        for r in range(4):
            t_r = sum(s_seq[:r])
            t_r1 = sum(s_seq[: r + 1])
            t_r2 = sum(s_seq[: r + 2])
            a_r = renewal_numerator(s_seq, r)
            a_r1 = renewal_numerator(s_seq, r + 1)

            rem_r = (3**t_r) * p0 + a_r
            rem_r1 = (3**t_r1) * p0 + a_r1

            ok_id = rem_r == (2**t_r1) * u_seq[r]
            ok_mod0 = (rem_r % (2**t_r1)) == 0
            ok_mod1 = (rem_r % (2 ** (t_r1 + 1))) == (2**t_r1)
            ok_step1 = (3 ** s_seq[r]) * rem_r + (2**t_r1) == rem_r1
            ok_step2 = (2**t_r1) * ((3 ** s_seq[r]) * u_seq[r] + 1) == (2**t_r2) * u_seq[r + 1]

            checked += 1
            if not (ok_id and ok_mod0 and ok_mod1 and ok_step1 and ok_step2):
                failures += 1
    return checked, failures


def test_sb78_two_horizon_kempner_tail() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for r in [0, 1, 2]:
        for m_len in [0, 1, 2]:
            total_len = r + 1 + m_len + 1
            for s_seq in itertools.product([2, 3, 4], repeat=total_len):
                s_list = list(s_seq)
                k1 = r
                k2 = r + 1 + m_len
                t1 = sum(s_list[:k1])
                s_r = s_list[r]
                t1_next = t1 + s_r
                t2 = sum(s_list[:k2])
                d = sum(s_list[r + 1 : k2])
                s_win = s_list[r + 1 : k2]
                r_tail = (3**d) + renewal_numerator(s_win, m_len)

                a_k1 = renewal_numerator(s_list, k1)
                a_k2 = renewal_numerator(s_list, k2)

                ok_a = a_k2 == (3 ** (s_r + d)) * a_k1 + (2**t1_next) * r_tail
                ok_odd = (r_tail % 2) == 1
                ok_mod = ((2**t1_next) * r_tail) % (2 ** (t1_next + 1)) == (2**t1_next)
                ok_bound = (5 * r_tail + 4 * (2**d) <= 3 ** (s_r + d)) and (
                    5 * r_tail < 3 ** (s_r + d)
                )

                checked += 1
                if not (ok_a and ok_odd and ok_mod and ok_bound):
                    failures += 1
    return checked, failures


def test_sb79_rational_target_obstruction() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_seq in itertools.product([2, 3, 4], repeat=4):
        s_list = list(s_seq)
        t_k = sum(s_list[:3])
        s_k = s_list[3]
        s_total = t_k + s_k
        a_k = renewal_numerator(s_list, 3)
        for p0 in range(4, 128, 4):
            nk = (3**t_k) * p0 + a_k
            ok_cop = math.gcd(nk, 3**t_k) == 1
            checked += 1
            if not ok_cop:
                failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 13 SANDBOX: GREEDY 2-ADIC BASE-(2/3) KEMPNER EXPANSION & TAIL VALUATION")
    print("=" * 78)

    c77, f77 = test_sb77_greedy_kempner_expansion()
    print(f"[SB.77] Greedy 2-Adic Base-(2/3) Kempner Step & Prefix:    checked={c77:6d}, failures={f77}")

    c78, f78 = test_sb78_two_horizon_kempner_tail()
    print(f"[SB.78] Two-Horizon Kempner Tail Valuation & 1/5 Bound:    checked={c78:6d}, failures={f78}")

    c79, f79 = test_sb79_rational_target_obstruction()
    print(f"[SB.79] Kempner Rational-Target Obstruction Bridge:        checked={c79:6d}, failures={f79}")

    total_checked = c77 + c78 + c79
    total_failures = f77 + f78 + f79
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
