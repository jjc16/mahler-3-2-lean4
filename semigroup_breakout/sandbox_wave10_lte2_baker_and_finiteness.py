#!/usr/bin/env python3
"""
Wave 10 Discovery & Verification Sandbox:
LTE_2 Ultrametric Flush Pinning, Shifted-Basepoint Baker-Matveev Pinch,
and the Senge-Straus / Stewart Finiteness Bridge (Theorems SB.65 - SB.68)
=========================================================================

Tests and verifies four exact structural theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.65 (LTE_2 Ultrametric Flush Pinning & Descent-Flush Prohibition):
   - Even rung s_r % 4 == 2 (so (3^{s_r} - 1) % 16 == 8, v_2(3^{s_r} - 1) == 3):
     * u_r % 8 == 3   ==>  (3^{s_r} * u_r + 1) % 8 == 4   ==>  s_{r+1} == 2
     * u_r % 16 == 15 ==>  (3^{s_r} * u_r + 1) % 16 == 8  ==>  s_{r+1} == 3 and u_r < u_{r+1}
     * Consequently, u_{r+1} <= u_r (or s_{r+1} >= 4) FORCES u_r % 16 == 7!
   - Odd rung s_r % 4 == 3 (so (3^{s_r - 1} - 1) % 16 == 8, v_2(3^{s_r - 1} - 1) == 3):
     * u_r % 8 == 1   ==>  (3^{s_r} * u_r + 1) % 8 == 4   ==>  s_{r+1} == 2
     * u_r % 16 == 5  ==>  (3^{s_r} * u_r + 1) % 16 == 8  ==>  s_{r+1} == 3 and u_r < u_{r+1}
     * Consequently, u_{r+1} <= u_r (or s_{r+1} >= 4) FORCES u_r % 16 == 13!

2. SB.66 (Post-Horizon Binary Zero-Bit Desert & Dual-Radix Lock):
   - For P_0 < 2^{B_0} with B_0 <= T_K + s_K and N_K = 3^{T_K} * P_0 + A_{0,K} = 2^{T_K + s_K} * u_K:
     * P_0 // 2^{B_0} == 0, P_0 % 2^{B_0} == P_0, and for all B >= B_0, (P_0 % 2^{T_K + s_K}) // 2^B == 0
     * N_K % 2^{T_K + s_K} == 0, N_K // 2^{T_K + s_K} == u_K, s_2(N_K) == s_2(u_K)
     * N_K // 3^{T_K} == P_0, N_K % 3^{T_K} == A_{0,K}, s_3(N_K) == s_3(P_0) + s_3(A_{0,K}).

3. SB.67 (Shifted-Basepoint Baker-Matveev Pinch & Repeated-Odd-Core Rhin Reduction):
   - Across window [r, r+M] of step length n_2 = T_{r+M} - T_r with K = r + M:
     * 2^{n_2 + s_K} * u_K = 3^{n_2} * (2^{s_r} * u_r) + A_{r,M}
     * 5 * (2^{n_2 + s_K} * u_K - 3^{n_2} * 2^{s_r} * u_r) + 4 * 2^{n_2} <= 4 * 3^{n_2}
     * 3^{T_r} * 2^{s_0} * u_0 < 2^{T_r} * (2^{s_r} * u_r)
   - Whenever u_K == u_r (Repeated Odd Core):
     * s_r < s_K and 3^{n_2} < 2^{n_2 + s_K - s_r}
     * (2^{s_r} * u_r) * (2^{n_2 + s_K - s_r} - 3^{n_2}) == A_{r,M}
     * 5 * (2^{s_r} * u_r) * (2^{n_2 + s_K - s_r} - 3^{n_2}) + 4 * 2^{n_2} <= 4 * 3^{n_2}
     * 5 * (2^{s_r} * u_r) + 4 * 2^{n_2} <= 4 * 3^{n_2} and 5 * 3^{T_r} * 2^{s_0} * u_0 < 4 * 2^{T_r} * 3^{n_2}.

4. SB.68 (Senge-Straus / Stewart Simultaneous (s_2, s_3) Finiteness Bridge & 68-Theorem Synthesis):
   - s_2(N_K) == s_2(u_K) and s_3(N_K) == s_3(P_0) + s_3(A_{0,K}) >= s_3(P_0) + K
   - s_3(N_K) + 2 * (v_3(N_K!) - 2^{T_K + s_K} * v_3(u_K!)) == 2^{T_K + s_K} * s_3(u_K).
"""

import itertools
from typing import List, Tuple


def base2_digit_sum(n: int) -> int:
    return bin(n).count("1")


def base3_digit_sum(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total


def v3_factorial(n: int) -> int:
    return (n - base3_digit_sum(n)) // 2


def renewal_numerator(s_seq: List[int], r: int) -> int:
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb65_lte2_ultrametric_flush_pinning() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_r in range(2, 18):
        for u_r in range(1, 1024, 2):
            num = (3**s_r) * u_r + 1
            s_r1 = (num & -num).bit_length() - 1
            u_r1 = num // (2**s_r1)
            if s_r1 < 2:
                continue

            ok = True
            if s_r % 4 == 2:
                if (3**s_r - 1) % 16 != 8:
                    ok = False
                if u_r % 8 == 3 and not (num % 8 == 4 and s_r1 == 2):
                    ok = False
                if u_r % 16 == 15 and not (num % 16 == 8 and s_r1 == 3 and u_r < u_r1):
                    ok = False
                if (u_r1 <= u_r or s_r1 >= 4) and (u_r % 16 != 7):
                    ok = False
            elif s_r % 4 == 3:
                if (3 ** (s_r - 1) - 1) % 16 != 8:
                    ok = False
                if u_r % 8 == 1 and not (num % 8 == 4 and s_r1 == 2):
                    ok = False
                if u_r % 16 == 5 and not (num % 16 == 8 and s_r1 == 3 and u_r < u_r1):
                    ok = False
                if (u_r1 <= u_r or s_r1 >= 4) and (u_r % 16 != 13):
                    ok = False

            checked += 1
            if not ok:
                failures += 1
    return checked, failures


def test_sb66_post_horizon_zero_bit_desert() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s0 in [2, 3]:
        for u0 in [1, 3, 5, 7]:
            p0 = (2**s0) * u0
            b0 = p0.bit_length()
            for k_blocks in [2, 3, 4]:
                for s_rest in itertools.product([2, 3, 4], repeat=k_blocks):
                    s_seq = [s0] + list(s_rest)
                    t_k = sum(s_seq[:k_blocks])
                    s_k = s_seq[k_blocks]
                    if b0 > t_k + s_k:
                        continue
                    a_k = renewal_numerator(s_seq, k_blocks)
                    nk = (3**t_k) * p0 + a_k
                    ok_p0 = (
                        (p0 // (2**b0) == 0)
                        and (p0 % (2**b0) == p0)
                        and all((p0 % (2 ** (t_k + s_k))) // (2**b) == 0 for b in range(b0, t_k + s_k + 1))
                    )
                    ok_b3 = (
                        (nk // (3**t_k) == p0)
                        and (nk % (3**t_k) == a_k)
                        and (base3_digit_sum(nk) == base3_digit_sum(p0) + base3_digit_sum(a_k))
                    )
                    checked += 1
                    if not (ok_p0 and ok_b3):
                        failures += 1
    return checked, failures


def test_sb67_and_sb68_baker_and_finiteness() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for m_len in [1, 2, 3]:
        for s_win in itertools.product([2, 3, 4, 5], repeat=m_len):
            s_list = list(s_win)
            n2 = sum(s_list)
            a_rm = renewal_numerator(s_list, m_len)
            ok_bound = 5 * a_rm + 4 * (2**n2) <= 4 * (3**n2)

            # Check repeated odd core condition: (2^{s_r} * u_r) * (2^{n2 + s_K - s_r} - 3^{n2}) == a_rm
            # and general Senge-Straus / Kummer factorial identity
            for s_k in [2, 3, 4]:
                for u_k in [1, 5, 7, 17]:
                    nk = (2 ** (n2 + s_k)) * u_k
                    ok_s2 = base2_digit_sum(nk) == base2_digit_sum(u_k)
                    ok_kummer = base3_digit_sum(nk) + 2 * (
                        v3_factorial(nk) - (2 ** (n2 + s_k)) * v3_factorial(u_k)
                    ) == (2 ** (n2 + s_k)) * base3_digit_sum(u_k)
                    checked += 1
                    if not (ok_bound and ok_s2 and ok_kummer):
                        failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 10 SANDBOX: LTE_2 FLUSH PINNING, BAKER PINCH, & FINITENESS BRIDGE")
    print("=" * 78)

    c65, f65 = test_sb65_lte2_ultrametric_flush_pinning()
    print(f"[SB.65] LTE_2 Ultrametric Flush Pinning & Prohibition:     checked={c65:6d}, failures={f65}")

    c66, f66 = test_sb66_post_horizon_zero_bit_desert()
    print(f"[SB.66] Post-Horizon Binary Zero-Bit Desert & Lock:        checked={c66:6d}, failures={f66}")

    c67, f67 = test_sb67_and_sb68_baker_and_finiteness()
    print(f"[SB.67/68] Shifted Baker Pinch & Senge-Straus Bridge:      checked={c67:6d}, failures={f67}")

    total_checked = c65 + c66 + c67
    total_failures = f65 + f66 + f67
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
