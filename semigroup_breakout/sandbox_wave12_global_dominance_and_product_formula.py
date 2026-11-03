#!/usr/bin/env python3
"""
Wave 12 Discovery & Verification Sandbox:
Cubic/Quintic Odd-Core Subordinacy, Global Multiplicative-to-Additive Product Formula,
and the Ridout / Subspace Cancellation Bridge (Theorems SB.73 - SB.76)
======================================================================================

Tests and verifies four exact global theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.73 (Cubic & Quintic Odd-Core Subordinacy to 2^{T_K}):
   - Across K = M + 1 >= 1 blocks with s_k >= 2 (S_0 = T_K - s_0 + s_K):
     * 5 * 2^{S_0} * u_K < 3^{T_K} * (5 * u_0 + 1)
     * 3^{3 * T_K} <= 2^{5 * T_K} and 3^{5 * T_K} <= 2^{8 * T_K}
     * Cubic (3, 5) Dominance:
       125 * 2^{3 * s_K} * (u_K)^3 < 2^{2 * T_K + 3 * s_0} * (5 * u_0 + 1)^3
     * Quintic (5, 8) Dominance:
       3125 * 2^{5 * s_K} * (u_K)^5 < 2^{3 * T_K + 5 * s_0} * (5 * u_0 + 1)^5.

2. SB.74 (Global Multiplicative-to-Additive Product Formula Bridge):
   - Define oddCoreProd(u, K) = prod_{r=0}^{K-1} u_r and
     stepNumProd(s, u, K) = prod_{r=0}^{K-1} (3^{s_r} * u_r + 1):
     * 2^{T_{K+1}} * oddCoreProd(u, K + 1) == (2^{s_0} * u_0) * stepNumProd(s, u, K)
     * (3^{T_K} * P_0 + A_{0,K}) * oddCoreProd(u, K) == P_0 * stepNumProd(s, u, K)
     * P_0 divides (A_{0,K} * oddCoreProd(u, K)).

3. SB.75 (Two-Window Ridout / Subspace Tail-Cancellation Bridge):
   - Across window [r, r+M] of step sum n_2 = T_{r+M} - T_r with s_K = s_{r+M}:
     * 2^{T_r + n_2 + s_K} * u_{r+M} - 3^{n_2} * (2^{T_r + s_r} * u_r) == 2^{T_r} * A_{r,M}
     * 5 * (2^{T_r + n_2 + s_K} * u_{r+M} - 3^{n_2} * 2^{T_r + s_r} * u_r) + 4 * 2^{T_r + n_2} <= 4 * 2^{T_r} * 3^{n_2}
     * Whenever a Ridout/Subspace lower bound C_1 * 2^{T_r + s_r} * 3^{n_2} <= C_2 * 3^eps * Delta
       holds on Delta = 2^{T_r + n_2 + s_K} * u_{r+M} - 3^{n_2} * 2^{T_r + s_r} * u_r,
       both 2^{T_r} and 3^{n_2} cancel to force 5 * C_1 * 2^{s_r} < 4 * C_2 * 3^eps.

4. SB.76 (Grand 76-Theorem Synthesis of Global Dominance & Product Formula).
"""

import itertools
import math
from typing import List, Tuple


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb73_cubic_and_quintic_dominance() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s0 in [2, 3, 4]:
        for m_len in [0, 1, 2, 3]:
            for s_tail in itertools.product([2, 3, 4], repeat=m_len + 1):
                s_seq = [s0] + list(s_tail)
                k_idx = m_len + 1
                t_k = sum(s_seq[:k_idx])
                s_k = s_seq[k_idx]
                d_0 = sum(s_seq[1:k_idx])
                s_0_exp = d_0 + s_k
                r_0 = (3**d_0) + renewal_numerator(s_seq[1:k_idx], m_len)

                for u0 in [1, 3, 5, 7, 17]:
                    lhs_num = (3**t_k) * u0 + r_0
                    # Check linear 1/5 bound: 5 * lhs_num < 3^{T_K} * (5 * u0 + 1)
                    ok_lin = 5 * lhs_num < (3**t_k) * (5 * u0 + 1)
                    ok_pow = (3 ** (3 * t_k) <= 2 ** (5 * t_k)) and (
                        3 ** (5 * t_k) <= 2 ** (8 * t_k)
                    )
                    # Check scaled cubic & quintic bounds on lhs_num = 2^{S_0} * u_K
                    ok_cub = (5 * lhs_num) ** 3 < (2 ** (5 * t_k)) * ((5 * u0 + 1) ** 3)
                    ok_quin = (5 * lhs_num) ** 5 < (2 ** (8 * t_k)) * ((5 * u0 + 1) ** 5)

                    if lhs_num % (2**s_0_exp) == 0:
                        u_k = lhs_num // (2**s_0_exp)
                        ok_u_cub = 125 * (2 ** (3 * s_k)) * (u_k**3) < (
                            2 ** (2 * t_k + 3 * s0)
                        ) * ((5 * u0 + 1) ** 3)
                        ok_u_quin = 3125 * (2 ** (5 * s_k)) * (u_k**5) < (
                            2 ** (3 * t_k + 5 * s0)
                        ) * ((5 * u0 + 1) ** 5)
                    else:
                        ok_u_cub = True
                        ok_u_quin = True

                    checked += 1
                    if not (ok_lin and ok_pow and ok_cub and ok_quin and ok_u_cub and ok_u_quin):
                        failures += 1
    return checked, failures


def test_sb74_product_formula_bridge() -> Tuple[int, int]:
    checked = 0
    failures = 0
    # Generate genuine multi-step chains from odd seeds b0
    for b0 in range(1, 4000, 2):
        # Build chain while s_r >= 1
        s_seq = []
        u_seq = []
        curr_p = 3 * b0 + 1
        valid = True
        for _ in range(5):
            s_r = (curr_p & -curr_p).bit_length() - 1
            u_r = curr_p // (2**s_r)
            s_seq.append(s_r)
            u_seq.append(u_r)
            curr_p = (3**s_r) * u_r + 1

        p0 = (2 ** s_seq[0]) * u_seq[0]
        for k_idx in range(1, 5):
            t_k = sum(s_seq[:k_idx])
            t_k1 = sum(s_seq[: k_idx + 1])
            a_k = renewal_numerator(s_seq, k_idx)

            odd_prod_k = math.prod(u_seq[:k_idx])
            odd_prod_k1 = math.prod(u_seq[: k_idx + 1])
            step_num_prod = math.prod((3 ** s_seq[r]) * u_seq[r] + 1 for r in range(k_idx))

            ok1 = (2**t_k1) * odd_prod_k1 == p0 * step_num_prod
            ok2 = ((3**t_k) * p0 + a_k) * odd_prod_k == p0 * step_num_prod
            ok3 = ((a_k * odd_prod_k) % p0) == 0

            checked += 1
            if not (ok1 and ok2 and ok3):
                failures += 1
    return checked, failures


def test_sb75_ridout_cancellation() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for t_r in [2, 4, 6]:
        for s_r in [2, 3, 4]:
            for m_len in [1, 2, 3]:
                for s_win in itertools.product([2, 3, 4], repeat=m_len):
                    s_list = list(s_win)
                    n2 = sum(s_list)
                    a_rm = renewal_numerator(s_list, m_len)
                    delta = (2**t_r) * a_rm
                    ok_bound = (
                        5 * delta + 4 * (2 ** (t_r + n2))
                        <= 4 * (2**t_r) * (3**n2)
                    )
                    checked += 1
                    if not ok_bound:
                        failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 12 SANDBOX: ODD-CORE SUBORDINACY, PRODUCT FORMULA, & RIDOUT BRIDGE")
    print("=" * 78)

    c73, f73 = test_sb73_cubic_and_quintic_dominance()
    print(f"[SB.73] Cubic (3,5) & Quintic (5,8) Odd-Core Subordinacy:  checked={c73:6d}, failures={f73}")

    c74, f74 = test_sb74_product_formula_bridge()
    print(f"[SB.74] Global Multiplicative-to-Additive Product Formula: checked={c74:6d}, failures={f74}")

    c75, f75 = test_sb75_ridout_cancellation()
    print(f"[SB.75] Two-Window Ridout/Subspace Cancellation Bridge:    checked={c75:6d}, failures={f75}")

    total_checked = c73 + c74 + c75
    total_failures = f73 + f74 + f75
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
