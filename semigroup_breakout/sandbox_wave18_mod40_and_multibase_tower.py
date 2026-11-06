#!/usr/bin/env python3
"""
Wave 18 Discovery & Verification Sandbox:
Universal Mod-5/Mod-10 Gauge Lock, Mod-40 Six-Residue Super-Block Bijection,
and the Cyclotomic Base-D_m / Base-4 / Base-9 Tower (Theorems SB.97 - SB.100)
=============================================================================

Tests and verifies four exact theorems before formalization in
SemigroupBreakoutTheorems.lean:

1. SB.97 (Universal Mod-5/Mod-10 Gauge Lock & Run-Length Parity Detector):
   - At every interior block r + 1 (s_r, s_{r+1}, s_{r+2} >= 2):
     * W_{r+1} % 5 == 4
     * (W_{r+1} % 10 == 4  <==>  s_{r+1} == 2)
     * (W_{r+1} % 10 == 9  <==>  s_{r+1} >= 3)
   - For W_{r+1} = 4^m * V followed by s^* = s_{r+1+m} >= 3:
     * (m % 2 == 0  <==>  V % 5 == 4)  and  (m % 2 == 1  <==>  V % 5 == 1)
     * (m % 2 == 0  <==>  V % 10 == 9) and  (m % 2 == 1  <==>  V % 10 == 1)
     * V % 5 not in {0, 2, 3}.

2. SB.98 (Mod-40 Six-Residue Super-Block Bijection & 34-Class Extinction):
   - Across any Super-Block W_{r+1} = 4^m * V ending at s^* = s_{r+1+m} >= 3:
     * (V % 40 == 19  <==>  m % 2 == 0 and s^* == 3)
     * (V % 40 == 11  <==>  m % 2 == 1 and s^* == 3)
     * (V % 40 == 29  <==>  m % 2 == 0 and s^* == 4)
     * (V % 40 == 21  <==>  m % 2 == 1 and s^* == 4)
     * (V % 40 == 9   <==>  m % 2 == 0 and s^* >= 5)
     * (V % 40 == 1   <==>  m % 2 == 1 and s^* >= 5)
     * V % 40 in {1, 9, 11, 19, 21, 29} (34 of 40 residue classes are extinct!).

3. SB.99 (Cyclotomic Base-D_m Modular Invariance & Base-4/Base-9 Shift Laws):
   - For D_m = 3^m - 2^m and G^{(m)}(P) = D_m * P + 2^m:
     * G^{(m)}(P) % D_m == (2^m) % D_m
     * G^{(2)}(P) % 5 == 4, G^{(3)}(P) % 19 == 8, G^{(4)}(P) % 65 == 16,
       G^{(4)}(P) % 13 == 3, G^{(5)}(P) % 211 == 32
   - For W_start = 4^m * V and W_end = 9^m * V:
     * W_start // 4^m == V, W_start % 4^m == 0
     * W_end // 9^m == V, W_end % 9^m == 0, and s_3(W_end) == s_3(V).

4. SB.100 (Centennial 100-Theorem Grand Synthesis of Semigroup Breakout).
"""

from typing import Tuple


def base3_digit_sum(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total


def cyclotomic_gauge(m: int, p: int) -> int:
    return ((3**m) - (2**m)) * p + (2**m)


def test_sb97_and_sb98_mod5_mod10_mod40() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for s_prev in range(2, 7):
        for u_prev in range(1, 5000, 2):
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

            # Check SB.97 Part 1
            ok_97_1 = (
                (w1 % 5 == 4)
                and ((w1 % 10 == 4) == (s1 == 2))
                and ((w1 % 10 == 9) == (s1 >= 3))
            )
            if not ok_97_1:
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

            next_p = (3**curr_s) * curr_u + 1
            next_s = (next_p & -next_p).bit_length() - 1
            if next_s < 2:
                continue

            v_odd = w1 // (4**m_run)
            s_star = curr_s

            # Check SB.97 Part 2
            ok_97_2 = (
                ((m_run % 2 == 0) == (v_odd % 5 == 4))
                and ((m_run % 2 == 1) == (v_odd % 5 == 1))
                and ((m_run % 2 == 0) == (v_odd % 10 == 9))
                and ((m_run % 2 == 1) == (v_odd % 10 == 1))
                and (v_odd % 5 not in (0, 2, 3))
            )

            # Check SB.98 Mod-40 Six-Residue Bijection
            ok_98 = (
                ((v_odd % 40 == 19) == (m_run % 2 == 0 and s_star == 3))
                and ((v_odd % 40 == 11) == (m_run % 2 == 1 and s_star == 3))
                and ((v_odd % 40 == 29) == (m_run % 2 == 0 and s_star == 4))
                and ((v_odd % 40 == 21) == (m_run % 2 == 1 and s_star == 4))
                and ((v_odd % 40 == 9) == (m_run % 2 == 0 and s_star >= 5))
                and ((v_odd % 40 == 1) == (m_run % 2 == 1 and s_star >= 5))
                and (v_odd % 40 in (1, 9, 11, 19, 21, 29))
            )

            checked += 1
            if not (ok_97_2 and ok_98):
                failures += 1
    return checked, failures


def test_sb99_cyclotomic_and_base4_base9() -> Tuple[int, int]:
    checked = 0
    failures = 0
    for p in range(1, 2000):
        ok_dm = True
        for m in range(1, 7):
            dm = (3**m) - (2**m)
            if cyclotomic_gauge(m, p) % dm != (2**m) % dm:
                ok_dm = False
        ok_explicit = (
            (cyclotomic_gauge(2, p) % 5 == 4)
            and (cyclotomic_gauge(3, p) % 19 == 8)
            and (cyclotomic_gauge(4, p) % 65 == 16)
            and (cyclotomic_gauge(4, p) % 13 == 3)
            and (cyclotomic_gauge(5, p) % 211 == 32)
        )
        checked += 1
        if not (ok_dm and ok_explicit):
            failures += 1

    for m in range(0, 6):
        for v in range(1, 300, 2):
            w_start = (4**m) * v
            w_end = (9**m) * v
            ok_b49 = (
                (w_start // (4**m) == v)
                and (w_start % (4**m) == 0)
                and (w_end // (9**m) == v)
                and (w_end % (9**m) == 0)
                and (base3_digit_sum(w_end) == base3_digit_sum(v))
            )
            checked += 1
            if not ok_b49:
                failures += 1
    return checked, failures


def main() -> None:
    print("=" * 78)
    print("WAVE 18 SANDBOX: MOD-5/MOD-10/MOD-40 BIJECTION & MULTI-BASE TOWER (SB.97-100)")
    print("=" * 78)

    c97, f97 = test_sb97_and_sb98_mod5_mod10_mod40()
    print(f"[SB.97/98] Mod-5/Mod-10 Lock & Mod-40 6-Residue Bijection: checked={c97:6d}, failures={f97}")

    c99, f99 = test_sb99_cyclotomic_and_base4_base9()
    print(f"[SB.99] Cyclotomic Base-D_m & Base-4/Base-9 Shift Laws:    checked={c99:6d}, failures={f99}")

    total_checked = c97 + c99
    total_failures = f97 + f99
    print("-" * 78)
    print(f"TOTAL VERIFIED CONFIGURATIONS: {total_checked} | TOTAL FAILURES: {total_failures}")
    assert total_failures == 0, f"Found {total_failures} failures!"


if __name__ == "__main__":
    main()
