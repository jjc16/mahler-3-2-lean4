#!/usr/bin/env python3
"""
Wave 17 Discovery & Verification Sandbox:
Path A (Binary Carry-Split, Quotient Decomposition of u_K, & Weight Excess Law)
and Path B (Reduced Odd-Seed Product Formula & Symmetric Excess) (SB.93 - SB.96)
=================================================================================

Tests and verifies four exact theorems along Path A and Path B before
formalization in SemigroupBreakoutTheorems.lean:

1. SB.93 (Path A Binary Carry-Split & Quotient Decomposition of u_K):
   - In 2^{S_0} * u_K = 3^{T_K} * u_0 + R_0 (with R_0 odd and S_0 = T_K - s_0 + s_K):
     * 1 <= (3^{T_K} * u_0) % 2^{S_0} and 1 <= R_0 % 2^{S_0}
     * (3^{T_K} * u_0) % 2^{S_0} + (R_0 % 2^{S_0}) == 2^{S_0}
     * u_K == (3^{T_K} * u_0) // 2^{S_0} + (R_0 // 2^{S_0}) + 1
     * s_2((3^{T_K} * u_0) % 2^{S_0}) + s_2(R_0 % 2^{S_0}) == S_0 + 1.

2. SB.94 (Path A Zero-Carry Binary Block Split & Weight Excess Law):
   - Splitting 3^{T_K} * u_0 and R_0 in Base 2 at 2^{S_0}:
     * s_2(3^{T_K} * u_0) == s_2((3^{T_K} * u_0) // 2^{S_0}) + s_2((3^{T_K} * u_0) % 2^{S_0})
     * s_2(R_0) == s_2(R_0 // 2^{S_0}) + s_2(R_0 % 2^{S_0})
     * s_2(3^{T_K} * u_0) + s_2(R_0) ==
         S_0 + 1 + s_2((3^{T_K} * u_0) // 2^{S_0}) + s_2(R_0 // 2^{S_0})
     * Whenever u_K >= 2, S_0 + 2 <= s_2(3^{T_K} * u_0) + s_2(R_0).

3. SB.95 (Path B Reduced Odd-Seed Product Formula & Symmetric Excess):
   - After canceling P_0 = 2^{s_0} * u_0 from the global product formula:
     Let tailOddProd = prod_{r=1}^{K-1} u_r:
     * oddCoreProd(u, K) == u_0 * tailOddProd
     * (3^{T_K} * u_0 + R_0) * tailOddProd == stepNumProd(s, u, K)
     * 3^{T_K} * oddCoreProd(u, K) + R_0 * tailOddProd == stepNumProd(s, u, K)
     * R_0 * tailOddProd == stepNumProd(s, u, K) - 3^{T_K} * oddCoreProd(u, K)
     * stepNumProd(s, u, K) % u_0 == (R_0 * tailOddProd) % u_0.

4. SB.96 (Grand 96-Theorem Synthesis of Path A & Path B).
"""

import math
from typing import List, Tuple


def base2_digit_sum(n: int) -> int:
    return bin(n).count("1")


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb93_sb94_sb95_paths_a_and_b() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for b0 in range(1, 5000, 2):
        s_seq = []
        u_seq = []
        curr_p = 3 * b0 + 1
        for _ in range(5):
            s_r = (curr_p & -curr_p).bit_length() - 1
            u_r = curr_p // (2**s_r)
            s_seq.append(s_r)
            u_seq.append(u_r)
            curr_p = (3**s_r) * u_r + 1

        if s_seq[0] < 2:
            continue

        for m_len in [0, 1, 2, 3]:
            if any(s_seq[1 + k] < 2 for k in range(m_len)):
                continue
            k_idx = 1 + m_len
            t_k = sum(s_seq[:k_idx])
            s_k = s_seq[k_idx]
            d_0 = sum(s_seq[1:k_idx])
            s_0_exp = d_0 + s_k
            r_0 = (3**d_0) + renewal_numerator(s_seq[1:k_idx], m_len)
            u_0 = u_seq[0]
            u_k = u_seq[k_idx]

            term1 = (3**t_k) * u_0
            mod1 = term1 % (2**s_0_exp)
            mod2 = r_0 % (2**s_0_exp)
            div1 = term1 // (2**s_0_exp)
            div2 = r_0 // (2**s_0_exp)

            # Check SB.93 (Path A Carry-Split & Quotient Decomposition)
            ok_93 = (
                (mod1 >= 1)
                and (mod2 >= 1)
                and (mod1 + mod2 == 2**s_0_exp)
                and (u_k == div1 + div2 + 1)
                and (base2_digit_sum(mod1) + base2_digit_sum(mod2) == s_0_exp + 1)
            )

            # Check SB.94 (Path A Zero-Carry Binary Block Split & Excess)
            ok_94 = (
                (base2_digit_sum(term1) == base2_digit_sum(div1) + base2_digit_sum(mod1))
                and (base2_digit_sum(r_0) == base2_digit_sum(div2) + base2_digit_sum(mod2))
                and (
                    base2_digit_sum(term1) + base2_digit_sum(r_0)
                    == s_0_exp + 1 + base2_digit_sum(div1) + base2_digit_sum(div2)
                )
                and ((u_k < 2) or (base2_digit_sum(term1) + base2_digit_sum(r_0) >= s_0_exp + 2))
            )

            # Check SB.95 (Path B Reduced Odd-Seed Product Formula)
            tail_prod = math.prod(u_seq[1:k_idx])
            full_prod = math.prod(u_seq[:k_idx])
            step_prod = math.prod((3 ** s_seq[r]) * u_seq[r] + 1 for r in range(k_idx))

            ok_95 = (
                (full_prod == u_0 * tail_prod)
                and ((term1 + r_0) * tail_prod == step_prod)
                and ((2**s_0_exp) * u_k * tail_prod == step_prod)
                and ((3**t_k) * full_prod + r_0 * tail_prod == step_prod)
                and (r_0 * tail_prod == step_prod - (3**t_k) * full_prod)
                and ((step_prod % u_0) == ((r_0 * tail_prod) % u_0))
            )

            checked += 1
            if not (ok_93 and ok_94 and ok_95):
                failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 17 SANDBOX: PATH A (CARRY-MIXING SPLIT) & PATH B (REDUCED PRODUCT)")
    print("=" * 78)

    c_all, f_all = test_sb93_sb94_sb95_paths_a_and_b()
    print(f"[SB.93-95] Path A Carry-Split & Path B Reduced Product:    checked={c_all:6d}, failures={f_all}")
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {c_all} | TOTAL FAILURES: {f_all}")
    assert f_all == 0, f"Found {f_all} failures!"


if __name__ == "__main__":
    main()
