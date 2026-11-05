#!/usr/bin/env python3
"""
Wave 15 Discovery & Verification Sandbox:
Second-Order Super-Block Renormalization, Mod-8 Future-Rung Predictor,
and the Infinite Cyclotomic Gauge Spectrum (Theorems SB.85 - SB.88)
======================================================================

Tests and verifies four exact theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.85 (Odd-Valuation Death Trap W_{r+1} % 4 != 2 & s = 2 Run Evolution):
   - In any surviving chain with s_r, s_{r+1}, s_{r+2} >= 2:
     * W_{r+1} % 4 != 2
     * (W_{r+1} % 2 == 0  <==>  W_{r+1} % 4 == 0)  and  (s_{r+1} == 2  <==>  W_{r+1} % 4 == 0)
   - Across any run of m consecutive s = 2 blocks:
     * 4^m * W_{r+1+m} == 9^m * W_{r+1}
     * W_{r+1} can NEVER equal 2 * 4^m * V with V odd if the chain survives to r+1+m+2!

2. SB.86 (Mod-8 Odd-Gauge Future-Rung Predictor, V % 8 != 7 Extinction, & Super-Block Jump):
   - Suppose W_{r+1} = 4^m * V executes m steps of s = 2 followed by s^* = s_{r+1+m} >= 3:
     * W_{r+1+m} == 9^m * V, V % 2 == 1, and W_{r+1+m} % 8 == V % 8
     * V % 8 != 7 (Delayed-Action Death Trap #2!)
     * Exact Future-Rung Predictor m blocks in advance:
       (V % 8 == 3  <==>  s^* == 3)
       (V % 8 == 5  <==>  s^* == 4)
       (V % 8 == 1  <==>  s^* >= 5)
     * Super-Block Jump Identity:
       2^{s^*} * W_{r+1+m+1} + (3^{s^* - 2} - 2^{s^* - 2}) == 3^{2*m + s^*} * V.

3. SB.87 (Universal Cyclotomic Gauge Spectrum G_r^{(m)} = (3^m - 2^m)*P_r + 2^m):
   - For all m >= 1 and any block transition 2^{s_r} * P_{r+1} = 3^{s_r} * P_r + 2^{s_r}:
     * s_r == m  ==>  2^m * G_{r+1}^{(m)} == 3^m * G_r^{(m)}
     * m <= s_r  ==>  2^{s_r} * G_{r+1}^{(m)} + 6^m * (3^{s_r - m} - 2^{s_r - m}) == 3^{s_r} * G_r^{(m)}
     * s_r <= m  ==>  2^{s_r} * G_{r+1}^{(m)} == 3^{s_r} * G_r^{(m)} + 6^{s_r} * (3^{m - s_r} - 2^{m - s_r})
   - Dual-Gauge Syzygy (m = 2 vs m = 3):
     * 19 * G_r^{(2)} == 5 * G_r^{(3)} + 36.

4. SB.88 (Grand 88-Theorem Synthesis of Super-Block Renormalization & Multi-Gauge Spectrum).
"""

from typing import Tuple


def cyclotomic_gauge(m: int, p: int) -> int:
    return ((3**m) - (2**m)) * p + (2**m)


def test_sb85_and_sb86_superblock_and_predictor() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_prev in range(2, 7):
        for u_prev in range(1, 4000, 2):
            p1 = (3**s_prev) * u_prev + 1
            s1 = (p1 & -p1).bit_length() - 1
            if s1 < 2:
                continue
            u1 = p1 // (2**s1)
            w1 = (5 * p1 + 4) // 36

            p2 = (3**s1) * u1 + 1
            s2 = (p2 & -p2).bit_length() - 1
            if s2 < 2:
                continue

            # Check SB.85: W_1 % 4 != 2 and (s_1 == 2 <==> W_1 % 4 == 0)
            ok_85 = (w1 % 4 != 2) and ((w1 % 2 == 0) == (w1 % 4 == 0)) and ((s1 == 2) == (w1 % 4 == 0))
            if not ok_85:
                failures += 1
            checked += 1

            # Follow the s = 2 run starting at p1
            curr_p = p1
            curr_s = s1
            curr_u = u1
            m_run = 0
            alive = True
            while curr_s == 2:
                m_run += 1
                curr_p = (3**curr_s) * curr_u + 1
                curr_s = (curr_p & -curr_p).bit_length() - 1
                if curr_s < 2:
                    alive = False
                    break
                curr_u = curr_p // (2**curr_s)

            if not alive:
                continue

            # Now curr_s >= 3 is the end of the s = 2 run!
            # Check if the step after curr_s also survives (s >= 2)
            next_p = (3**curr_s) * curr_u + 1
            next_s = (next_p & -next_p).bit_length() - 1
            if next_s < 2:
                continue

            w_end = (5 * curr_p + 4) // 36
            w_next = (5 * next_p + 4) // 36

            ok_div4m = (w1 % (4**m_run)) == 0
            v_odd = w1 // (4**m_run)
            ok_v = (
                (v_odd % 2 == 1)
                and (w_end == (9**m_run) * v_odd)
                and (w_end % 8 == v_odd % 8)
                and (v_odd % 8 != 7)
            )
            ok_pred = (
                ((v_odd % 8 == 3) == (curr_s == 3))
                and ((v_odd % 8 == 5) == (curr_s == 4))
                and ((v_odd % 8 == 1) == (curr_s >= 5))
            )
            ok_jump = (2**curr_s) * w_next + (
                (3 ** (curr_s - 2)) - (2 ** (curr_s - 2))
            ) == (3 ** (2 * m_run + curr_s)) * v_odd

            checked += 1
            if not (ok_div4m and ok_v and ok_pred and ok_jump):
                failures += 1
    return checked, failures


def test_sb87_cyclotomic_gauge_spectrum() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for m in range(1, 7):
        for s_r in range(1, 7):
            for u_r in range(1, 200, 2):
                p_r = (2**s_r) * u_r
                p_r1 = (3**s_r) * u_r + 1
                g_r = cyclotomic_gauge(m, p_r)
                g_r1 = cyclotomic_gauge(m, p_r1)

                ok = True
                if s_r == m:
                    ok = (2**m) * g_r1 == (3**m) * g_r
                if m <= s_r:
                    ok = ok and (
                        (2**s_r) * g_r1
                        + (2**m) * (3**m) * ((3 ** (s_r - m)) - (2 ** (s_r - m)))
                        == (3**s_r) * g_r
                    )
                if s_r <= m:
                    ok = ok and (
                        (2**s_r) * g_r1
                        == (3**s_r) * g_r
                        + (2**s_r) * (3**s_r) * ((3 ** (m - s_r)) - (2 ** (m - s_r)))
                    )

                g2 = cyclotomic_gauge(2, p_r)
                g3 = cyclotomic_gauge(3, p_r)
                ok_syz = 19 * g2 == 5 * g3 + 36

                checked += 1
                if not (ok and ok_syz):
                    failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 15 SANDBOX: SUPER-BLOCK RENORMALIZATION, MOD-8 PREDICTOR, & MULTI-GAUGE")
    print("=" * 78)

    c85, f85 = test_sb85_and_sb86_superblock_and_predictor()
    print(f"[SB.85/86] Super-Block Renormalization & Mod-8 Predictor:  checked={c85:6d}, failures={f85}")

    c87, f87 = test_sb87_cyclotomic_gauge_spectrum()
    print(f"[SB.87] Universal Cyclotomic Gauge Spectrum & Syzygy:      checked={c87:6d}, failures={f87}")

    total_checked = c85 + c87
    total_failures = f85 + f87
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
