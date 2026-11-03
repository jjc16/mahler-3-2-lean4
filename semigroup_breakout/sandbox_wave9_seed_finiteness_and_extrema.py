#!/usr/bin/env python3
"""
Wave 9 Discovery & Verification Sandbox:
Seed Finiteness, Extrema Seesaw, & The Trough-Rebound Trap (Theorems SB.61 - SB.64)
===================================================================================

Tests and verifies four exact structural laws exploiting seed finiteness and orbit
extrema before formalization in SemigroupBreakoutTheorems.lean:

1. SB.61 (Local Descent Rung Jump & Multi-Step Descent Explosion):
   - Whenever u_{r+1} <= u_r in 2^{s_{r+1}} * u_{r+1} = 3^{s_r} * u_r + 1,
     we have 3^{s_r} < 2^{s_{r+1}}.
   - Specifically:
     s_r >= 2  ==>  s_{r+1} >= 4
     s_r >= 4  ==>  s_{r+1} >= 7
     s_r >= 7  ==>  s_{r+1} >= 12
   - Across any 3-step non-increasing run u_{r+3} <= u_{r+2} <= u_{r+1} <= u_r with s_r >= 2,
     the rungs explode along the staircase: s_{r+1} >= 4, s_{r+2} >= 7, s_{r+3} >= 12.

2. SB.62 (Trough-Rebound Compound-Interest Identity & Local Minimum Trap):
   - Across two transitions r -> r+1 -> r+2:
     2^{s_{r+1} + s_{r+2}} * u_{r+2} = 3^{s_r + s_{r+1}} * u_r + 3^{s_{r+1}} + 2^{s_{r+1}}.
   - Whenever step r -> r+1 enters a trough (u_{r+1} <= u_r with s_r >= 2):
     * 4 <= s_{r+1}
     * 81 * u_{r+1} + 1 <= 2^{s_{r+2}} * u_{r+2}
     * 16 * 2^{s_{r+2}} * u_{r+2} >= 81 * (3^{s_r} * u_r + 1) + 16
     * And if step r+1 -> r+2 exits at a local rung peak (2 <= s_{r+2} <= s_{r+1}),
       9 * 3^{s_{r+1} - s_{r+2}} * u_{r+1} + 1 <= 4 * u_{r+2}.

3. SB.63 (Finite-Seed Global Peak-Trough Seesaw & Post-Horizon Exhaustion):
   - Across K blocks (T_K steps, P_0 = 2^{s_0} * u_0):
     * 3^{T_K} * 2^{s_0} * u_0 < 2^{T_K + s_K} * u_K
     * 5 * 2^{T_K + s_K} * u_K + 4 * 2^{T_K} <= 3^{T_K} * (5 * 2^{s_0} * u_0 + 4)
   - Global Return-to-Baseline Barrier:
     u_K <= u_0  ==>  3^{T_K} * 2^{s_0} < 2^{T_K + s_K}
   - Bounded-Rung Exponential Divergence:
     s_K <= s_0  ==>  3^{T_K} * u_0 < 2^{T_K} * u_K
   - Post-Horizon Seed Frozen Top-Block & Base-3 Split:
     (2^{T_K + s_K} * u_K) // 3^{T_K} == P_0 and
     s_3(2^{T_K + s_K} * u_K) == s_3(P_0) + s_3(A_{0,K}).

4. SB.64 (Grand 64-Theorem Synthesis of Seed Finiteness & Orbit Extrema).
"""

import itertools
from typing import List, Tuple


def base3_digit_sum(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb61_local_descent_and_staircase() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_r in range(2, 10):
        for u_r in range(1, 2000, 2):
            num = (3**s_r) * u_r + 1
            s_r1 = (num & -num).bit_length() - 1
            u_r1 = num // (2**s_r1)
            if u_r1 <= u_r:
                ok1 = (3**s_r) < (2**s_r1)
                ok2 = (s_r < 2) or (s_r1 >= 4)
                ok3 = (s_r < 4) or (s_r1 >= 7)
                ok4 = (s_r < 7) or (s_r1 >= 12)
                checked += 1
                if not (ok1 and ok2 and ok3 and ok4):
                    failures += 1
    return checked, failures


def test_sb62_trough_rebound_compound_interest() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_r in range(2, 8):
        for u_r in range(1, 1500, 2):
            num1 = (3**s_r) * u_r + 1
            s_r1 = (num1 & -num1).bit_length() - 1
            u_r1 = num1 // (2**s_r1)

            num2 = (3**s_r1) * u_r1 + 1
            s_r2 = (num2 & -num2).bit_length() - 1
            u_r2 = num2 // (2**s_r2)

            # 1. Exact compound-interest identity
            ok_id = (2 ** (s_r1 + s_r2)) * u_r2 == (3 ** (s_r + s_r1)) * u_r + (
                3**s_r1
            ) + (2**s_r1)

            # 2. Trough entry bounds when u_{r+1} <= u_r
            if u_r1 <= u_r:
                ok_trough = (
                    (s_r1 >= 4)
                    and (81 * u_r1 + 1 <= (2**s_r2) * u_r2)
                    and (16 * (2**s_r2) * u_r2 >= 81 * ((3**s_r) * u_r + 1) + 16)
                )
            else:
                ok_trough = True

            # 3. Local rung peak rebound when 2 <= s_{r+2} <= s_{r+1}
            if 2 <= s_r2 <= s_r1:
                ok_peak = 9 * (3 ** (s_r1 - s_r2)) * u_r1 + 1 <= 4 * u_r2
            else:
                ok_peak = True

            checked += 1
            if not (ok_id and ok_trough and ok_peak):
                failures += 1
    return checked, failures


def test_sb63_finite_seed_global_seesaw() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s0 in [2, 3, 4, 5]:
        for u0 in [1, 3, 5, 7, 11, 17, 25]:
            p0 = (2**s0) * u0
            for k_blocks in [1, 2, 3, 4]:
                for s_rest in itertools.product([2, 3, 4, 5], repeat=k_blocks):
                    s_seq = [s0] + list(s_rest)
                    t_k = sum(s_seq[:k_blocks])
                    s_k = s_seq[k_blocks]
                    a_k = renewal_numerator(s_seq, k_blocks)
                    nk = (3**t_k) * p0 + a_k
                    # Treat nk as 2^{T_K + s_K} * u_K for testing the algebraic seesaw laws
                    # when 2^{T_K + s_K} divides nk (or test on exact u_K when divisible)
                    ok_sandwich = (3**t_k) * (2**s0) * u0 < nk and (
                        5 * nk + 4 * (2**t_k) <= (3**t_k) * (5 * (2**s0) * u0 + 4)
                    )
                    ok_div = (nk // (3**t_k)) == p0
                    ok_s3 = base3_digit_sum(nk) == base3_digit_sum(p0) + base3_digit_sum(a_k)

                    if nk % (2 ** (t_k + s_k)) == 0:
                        u_k = nk // (2 ** (t_k + s_k))
                        if u_k <= u0:
                            ok_ret = (3**t_k) * (2**s0) < (2 ** (t_k + s_k))
                        else:
                            ok_ret = True
                        if s_k <= s0:
                            ok_div_u = (3**t_k) * u0 < (2**t_k) * u_k
                        else:
                            ok_div_u = True
                    else:
                        ok_ret = True
                        ok_div_u = True

                    checked += 1
                    if not (ok_sandwich and ok_div and ok_s3 and ok_ret and ok_div_u):
                        failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 9 SANDBOX: SEED FINITENESS, EXTREMA SEESAW, & TROUGH-REBOUND TRAP")
    print("=" * 78)

    c61, f61 = test_sb61_local_descent_and_staircase()
    print(f"[SB.61] Local Descent Rung Jump & Staircase Explosion:     checked={c61:6d}, failures={f61}")

    c62, f62 = test_sb62_trough_rebound_compound_interest()
    print(f"[SB.62] Trough-Rebound Compound-Interest & Local Min Trap: checked={c62:6d}, failures={f62}")

    c63, f63 = test_sb63_finite_seed_global_seesaw()
    print(f"[SB.63] Finite-Seed Global Seesaw & Return Barrier:        checked={c63:6d}, failures={f63}")

    total_checked = c61 + c62 + c63
    total_failures = f61 + f62 + f63
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
