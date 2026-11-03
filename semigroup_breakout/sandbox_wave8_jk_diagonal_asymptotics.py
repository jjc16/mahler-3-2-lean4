#!/usr/bin/env python3
"""
Wave 8 Discovery & Verification Sandbox:
The (j+n, k+n) Diagonal Limit & The j >= k / j >> k Regime (Theorems SB.57 - SB.60)
===================================================================================

Tests and verifies four exact structural laws along the user's (j+n, k+n) diagonal
and j >= k / j >> k axis before formalization in SemigroupBreakoutTheorems.lean:

1. SB.57 (Two-Window Cauchy Tail-Freeze & Drift-Arrest Law):
   Starting at block r with j = s_r, advancing across M1 blocks (n1 steps) and then
   M2 more blocks (n2 steps, total n = n1 + n2):
   - R_{12} = 3^{n2} * R_1 + 2^{n1} * A^{(2)}
   - 5 * (R_{12} - 3^{n2} * R_1) + 4 * 2^{n1 + n2} <= 4 * 2^{n1} * 3^{n2}
   - Both horizons recover the exact same integer quotient u_r:
     (2^{n1 + k1} * u_{r+1+M1}) // 3^{j + n1} == u_r == (2^{n1 + n2 + k2} * u_{r+1+M1+M2}) // 3^{j + n1 + n2}
   - Relative tail drift (R_{12} - 3^{n2} R_1) / (3^{j+n1+n2} u_r) <= (4 / (5 * 3^j * u_r)) * (2/3)^{n1}.

2. SB.58 (j >= k Peak-to-Trough Explosion, Binary Weight Swelling, & Halving-Debt Law):
   At any block transition 2^k * u_{r+1} = 3^j * u_r + 1 with j = s_r >= k = s_{r+1} >= 2
   and excess Delta = j - k >= 0:
   - 2^k * u_{r+1} = 3^Delta * 3^k * u_r + 1
   - 4 * u_{r+1} >= 9 * 3^Delta * u_r + 1 and u_{r+1} > 2 * 3^Delta * u_r
   - Binary 1-bit budget: s_2(u_{r+1}) + k = s_2(3^j * u_r) + 1
   - Two-step halving-debt crisis: across block r (j, k) and block r+1 (k, k' = s_{r+2}),
     2^{k + k'} * u_{r+2} = 3^{j + k} * u_r + 3^k + 2^k, so u_{r+2} <= u_r IMPLIES
     2^{k + k'} > 3^{j + k} = 3^{2k + Delta} and 2^{k'} > 3^j = 3^{k + Delta}.

3. SB.59 (3-Adic Valuation Shift P_0 = 3^{j0} * m, (j0+n, k+n) Diagonal & j0-Trit Dead Zone):
   Whenever P_0 = 3^{j0} * m (or u_r = 3^{j0} * m) with j0 >= 1:
   - After K blocks (n = T_K steps, k = s_K), N_K = 2^{n+k} * u_K = 3^{j0 + n} * m + A_{0,K}
   - Top quotient above 3^{j0+n} is m: N_K // 3^{j0+n} == m
   - Middle j0-trit dead zone [3^n, 3^{j0+n}) is identically zero:
     (N_K // 3^n) % 3^{j0} == 0 and (N_K % 3^{j0+n}) // 3^n == 0
   - Base-3 digit sum is completely invariant in j0:
     s_3(2^{n+k} * u_K) == s_3(m) + s_3(A_{0,K}).

4. SB.60 (Grand 60-Theorem Synthesis of the (j+n, k+n) Diagonal & j >> k Regime).
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


def renewal_numerator(s_seq: List[int], r: int) -> int:
    """Computes renewalNumerator s r matching Lean definition."""
    if r == 0:
        return 0
    t_steps = sum(s_seq[:r])
    return 3 ** s_seq[r - 1] * renewal_numerator(s_seq, r - 1) + 2 ** t_steps


def test_sb57_two_window_cauchy_tail_freeze() -> Tuple[int, int]:
    """Tests SB.57 across multi-block two-window splits (M1, M2)."""
    checked = 0
    failures = 0
    for j in [2, 3, 4, 5, 7]:
        for m1 in [1, 2, 3]:
            for m2 in [1, 2, 3]:
                for s_tail in itertools.product([2, 3, 4], repeat=m1 + m2 + 1):
                    s_seq = [j] + list(s_tail)
                    n1 = sum(s_seq[1 : 1 + m1])
                    k1 = s_seq[1 + m1]
                    n2 = sum(s_seq[1 + m1 : 1 + m1 + m2])
                    k2 = s_seq[1 + m1 + m2]

                    s_win1 = s_seq[1 : 1 + m1]
                    s_win2 = s_seq[1 + m1 : 1 + m1 + m2]
                    s_win12 = s_seq[1 : 1 + m1 + m2]

                    r1 = 3**n1 + renewal_numerator(s_win1, m1)
                    a2 = renewal_numerator(s_win2, m2)
                    r12 = 3 ** (n1 + n2) + renewal_numerator(s_win12, m1 + m2)

                    for u_r in [1, 5, 7, 17, 79]:
                        lhs1 = 3 ** (j + n1) * u_r + r1
                        lhs12 = 3 ** (j + n1 + n2) * u_r + r12

                        # Check exact two-window recurrence
                        ok_rec = (r12 == 3**n2 * r1 + (2**n1) * a2) and (
                            lhs12 == 3**n2 * lhs1 + (2**n1) * a2
                        )
                        # Check 4/5 Cauchy tail-freeze inequality
                        ok_ineq = (
                            5 * (r12 - 3**n2 * r1) + 4 * 2 ** (n1 + n2)
                            <= 4 * (2**n1) * (3**n2)
                        )
                        # Check quotient invariance at both horizons
                        ok_q1 = (lhs1 // (3 ** (j + n1))) == u_r
                        ok_q12 = (lhs12 // (3 ** (j + n1 + n2))) == u_r
                        # Check Base-3 digit sum invariance of top block
                        ok_s3_1 = base3_digit_sum(lhs1) == base3_digit_sum(u_r) + base3_digit_sum(r1)
                        ok_s3_12 = base3_digit_sum(lhs12) == base3_digit_sum(u_r) + base3_digit_sum(r12)

                        checked += 1
                        if not (ok_rec and ok_ineq and ok_q1 and ok_q12 and ok_s3_1 and ok_s3_12):
                            failures += 1
    return checked, failures


def test_sb58_j_ge_k_explosion_and_halving_debt() -> Tuple[int, int]:
    """Tests SB.58 across j >= k transitions and two-step halving-debt recovery."""
    checked = 0
    failures = 0
    for k in range(2, 8):
        for delta in range(0, 8):
            j = k + delta
            for u_r in range(1, 500, 2):
                num1 = (3**j) * u_r + 1
                if num1 % (2**k) != 0:
                    continue
                u_r1 = num1 // (2**k)
                if u_r1 % 2 == 0:
                    continue
                # 1. Excess-exponent decomposition & 9/4 * 3^Delta jump
                ok_decomp = (2**k) * u_r1 == (3**delta) * (3**k) * u_r + 1
                ok_jump = 4 * u_r1 >= 9 * (3**delta) * u_r + 1 and u_r1 > 2 * (3**delta) * u_r
                # 2. Binary 1-bit depletion law
                ok_b2 = base2_digit_sum(u_r1) + k == base2_digit_sum((3**j) * u_r) + 1

                # 3. Two-step halving-debt crisis
                num2 = (3**k) * u_r1 + 1
                # Write num2 = 2^{k'} * u_{r+2}
                k_prime = (num2 & -num2).bit_length() - 1
                u_r2 = num2 // (2**k_prime)
                ok_2step = (2 ** (k + k_prime)) * u_r2 == (3 ** (j + k)) * u_r + (3**k) + (2**k)
                if u_r2 <= u_r:
                    ok_debt = (2 ** (k + k_prime) > 3 ** (j + k)) and (2**k_prime > 3**j)
                else:
                    ok_debt = True

                checked += 1
                if not (ok_decomp and ok_jump and ok_b2 and ok_2step and ok_debt):
                    failures += 1
    return checked, failures


def test_sb59_three_adic_diagonal_dead_zone() -> Tuple[int, int]:
    """Tests SB.59 for P_0 = 3^{j0} * m across j0 >= 1 and multi-block windows."""
    checked = 0
    failures = 0
    for j0 in range(1, 7):
        for m in [1, 2, 4, 5, 7, 8, 10, 11, 13, 17, 25]:
            p0 = (3**j0) * m
            for num_blocks in [1, 2, 3, 4]:
                for s_seq in itertools.product([2, 3, 4], repeat=num_blocks):
                    s_list = list(s_seq)
                    n = sum(s_list)
                    a0k = renewal_numerator(s_list, num_blocks)
                    nk = (3**n) * p0 + a0k

                    # Check diagonal equation N_K = 3^{j0 + n} * m + A_{0,K}
                    ok_diag = nk == (3 ** (j0 + n)) * m + a0k
                    # Check top quotient recovery above 3^{j0 + n}
                    ok_top_q = (nk // (3 ** (j0 + n))) == m
                    # Check remainder below 3^{j0 + n}
                    ok_top_r = (nk % (3 ** (j0 + n))) == a0k
                    # Check exact j0-trit dead zone in [3^n, 3^{j0+n})
                    ok_dead1 = ((nk // (3**n)) % (3**j0)) == 0
                    ok_dead2 = ((nk % (3 ** (j0 + n))) // (3**n)) == 0
                    # Check Base-3 digit sum invariance in j0
                    ok_s3 = base3_digit_sum(nk) == base3_digit_sum(m) + base3_digit_sum(a0k)

                    checked += 1
                    if not (ok_diag and ok_top_q and ok_top_r and ok_dead1 and ok_dead2 and ok_s3):
                        failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 8 SANDBOX: (j+n, k+n) DIAGONAL LIMIT & j >= k / j >> k REGIME")
    print("=" * 78)

    c57, f57 = test_sb57_two_window_cauchy_tail_freeze()
    print(f"[SB.57] Two-Window Cauchy Tail-Freeze & Drift-Arrest Law:  checked={c57:6d}, failures={f57}")

    c58, f58 = test_sb58_j_ge_k_explosion_and_halving_debt()
    print(f"[SB.58] j >= k Peak-to-Trough Explosion & Halving Debt:    checked={c58:6d}, failures={f58}")

    c59, f59 = test_sb59_three_adic_diagonal_dead_zone()
    print(f"[SB.59] 3^j0 Diagonal Shift & j0-Trit Dead-Zone Law:       checked={c59:6d}, failures={f59}")

    total_checked = c57 + c58 + c59
    total_failures = f57 + f58 + f59
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
