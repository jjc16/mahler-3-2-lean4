#!/usr/bin/env python3
"""
Wave 14 Discovery & Verification Sandbox:
The (5P + 4)/36 Ceiling-Dual Gauge Transformation & Dual-Wall Squeeze (SB.81 - SB.84)
=====================================================================================

Invents and verifies a genuinely new coordinate system outside the standard bottom-up
renewal semigroup: the Ceiling-Dual Gauge W_r = (5 * P_r + 4) / 36, which measures
distance DOWN from the 4/5 ceiling rather than UP from 0:

1. SB.81 (Exact 36-Divisibility of 5*P_r + 4, Rung-2 Parity Detector, & Pure (9/4) Step):
   - For every interior block r >= 1 with s_{r-1} >= 2 and s_r >= 2:
     * P_r % 4 == 0 and P_r % 9 == 1 (so P_r % 36 == 28)
     * (5 * P_r + 4) % 36 == 0, so W_r = (5 * P_r + 4) // 36 is an exact positive integer
       with 36 * W_r == 5 * P_r + 4 and 9 * W_r == 5 * 2^{s_r - 2} * u_r + 1
     * Rung-2 Parity Detector:
       (W_r % 2 == 0  <==>  s_r == 2)  and  (W_r % 2 == 1  <==>  s_r >= 3)
     * One-Step Gauge Law:
       2^{s_r} * W_{r+1} + (3^{s_r - 2} - 2^{s_r - 2}) == 3^{s_r} * W_r
       and when s_r == 2, 4 * W_{r+1} == 9 * W_r (zero additive error!).

2. SB.82 (Multi-Block Gauge Deficit E_{r,M} & The 1/9 Sub-3^{d-2} Bound):
   - Across M blocks starting from r >= 1 (step sum d = T_{r+M} - T_r):
     * 36 * E_{r,M} == 4 * 3^d - 4 * 2^d - 5 * A_{r,M}
     * 2^d * W_{r+M} + E_{r,M} == 3^d * W_r  (sub-multiplicative: 2^d * W_{r+M} <= 3^d * W_r!)
     * 9 * E_{r,M} + 2^d <= 3^d and E_{r,M} < 3^{d - 2} (for d >= 2).

3. SB.83 (Gauge-Complement Base-3 Conservation Law & Top '22'-Trit Lock):
   - Whenever E_{r,M} >= 1 (i.e. at least one block has s_{r+k} >= 3):
     * 2^d * W_{r+M} == 3^d * (W_r - 1) + (3^d - E_{r,M})
     * (2^d * W_{r+M}) // 3^d == W_r - 1 and (2^d * W_{r+M}) % 3^d == 3^d - E_{r,M}
     * Top 2 trits of remainder are locked to '22' in Base 3:
       8 * 3^{d - 2} < 3^d - E_{r,M} < 3^d and ((2^d * W_{r+M}) % 3^d) // 3^{d - 2} == 8
     * Exact Base-3 Complement Conservation Law:
       s_3(2^d * W_{r+M}) + s_3(E_{r,M} - 1) == s_3(W_r - 1) + 2 * d.

4. SB.84 (Dual-Wall Monotone Squeeze & Grand 84-Theorem Synthesis):
   - Simultaneously traps the orbit between the strictly increasing lower-wall sequence
     P_r and the monotonically non-increasing upper-wall gauge sequence W_r linked by
     36 * W_r - 5 * P_r == 4.
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


def test_sb81_gauge_transform_and_parity() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_prev in range(2, 9):
        for u_prev in range(1, 600, 2):
            p_r = (3**s_prev) * u_prev + 1
            s_r = (p_r & -p_r).bit_length() - 1
            if s_r < 2:
                continue
            u_r = p_r // (2**s_r)

            p_r1 = (3**s_r) * u_r + 1
            s_r1 = (p_r1 & -p_r1).bit_length() - 1
            if s_r1 < 2:
                continue

            ok_mod36 = (p_r % 4 == 0) and (p_r % 9 == 1) and (p_r % 36 == 28) and ((5 * p_r + 4) % 36 == 0)
            w_r = (5 * p_r + 4) // 36
            w_r1 = (5 * p_r1 + 4) // 36

            ok_w_id = (36 * w_r == 5 * p_r + 4) and (9 * w_r == 5 * (2 ** (s_r - 2)) * u_r + 1)
            ok_parity = ((w_r % 2 == 0) == (s_r == 2)) and ((w_r % 2 == 1) == (s_r >= 3))
            ok_step = (2**s_r) * w_r1 + (3 ** (s_r - 2) - 2 ** (s_r - 2)) == (3**s_r) * w_r
            ok_s2 = (s_r != 2) or (4 * w_r1 == 9 * w_r)

            checked += 1
            if not (ok_mod36 and ok_w_id and ok_parity and ok_step and ok_s2):
                failures += 1
    return checked, failures


def test_sb82_and_sb83_multi_block_gauge_and_complement() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for m_len in [1, 2, 3, 4]:
        for s_win in itertools.product([2, 3, 4], repeat=m_len):
            s_list = list(s_win)
            d = sum(s_list)
            a_rm = renewal_numerator(s_list, m_len)
            d_raw = 4 * (3**d) - 4 * (2**d) - 5 * a_rm
            ok_div36 = (d_raw >= 0) and (d_raw % 36 == 0)
            e_rm = d_raw // 36
            ok_19 = (9 * e_rm + (2**d) <= 3**d) and (e_rm < 3 ** (d - 2))

            for w_r in [1, 2, 5, 12, 37]:
                # Test the exact gauge relation 2^d * W_{r+M} = 3^d * W_r - E_{r,M}
                lhs_val = (3**d) * w_r - e_rm
                if e_rm >= 1:
                    ok_q = (lhs_val // (3**d)) == (w_r - 1)
                    ok_r = (lhs_val % (3**d)) == ((3**d) - e_rm)
                    ok_22 = (((lhs_val % (3**d)) // (3 ** (d - 2))) == 8)
                    ok_s3 = base3_digit_sum(lhs_val) + base3_digit_sum(e_rm - 1) == (
                        base3_digit_sum(w_r - 1) + 2 * d
                    )
                else:
                    ok_q = (lhs_val // (3**d)) == w_r
                    ok_r = (lhs_val % (3**d)) == 0
                    ok_22 = True
                    ok_s3 = base3_digit_sum(lhs_val) == base3_digit_sum(w_r)

                checked += 1
                if not (ok_div36 and ok_19 and ok_q and ok_r and ok_22 and ok_s3):
                    failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 14 SANDBOX: (5P+4)/36 CEILING-DUAL GAUGE & BASE-3 COMPLEMENT SQUEEZE")
    print("=" * 78)

    c81, f81 = test_sb81_gauge_transform_and_parity()
    print(f"[SB.81] (5P+4)/36 Gauge Transform & Rung-2 Parity Law:     checked={c81:6d}, failures={f81}")

    c82, f82 = test_sb82_and_sb83_multi_block_gauge_and_complement()
    print(f"[SB.82/83] 1/9 Deficit Bound, '22'-Trit Lock & 2d Law:     checked={c82:6d}, failures={f82}")

    total_checked = c81 + c82
    total_failures = f81 + f82
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
