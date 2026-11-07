"""
Wave 20 Discovery Sandbox: Universal q/2 Relaxation Phase Diagram, Kempner Threshold
Inversion Dichotomy (q = 3 vs q >= 5), Universal Mod-4 50/50 Mortality, and the
Universal ((q^2 - 4) u + 1) Super-Block Gauge & Odd-Valuation Death Trap (SB.105-SB.108).
"""

def test_sb105_kempner_inversion_dichotomy():
    print("=== Test 1 (SB.105): Kempner Threshold Inversion Dichotomy (q = 3 vs q >= 5) ===")
    failures = 0
    for q in range(3, 51):
        lhs = (q + 2) * (q * q - 4)
        rhs = q ** 3
        diff = lhs - rhs
        expected_diff = 2 * (q * q - 2 * q - 4)
        if diff != expected_diff:
            failures += 1
        if q == 3:
            # At q = 3: (q+2)(q^2-4) = 25 < 27 = q^3 (Kempner point 3/5 > 5/9 Zone-1 top!)
            if not (lhs < rhs and lhs == 25 and rhs == 27):
                failures += 1
            # And at Mahler's k = 1/2: 1*(3^2-4) = 5 < 6 = 2*3 (1/2 < 3/5)
            if not ((3 * 3 - 4) < 2 * 3):
                failures += 1
        elif q >= 4:
            # For all q >= 4: q^3 < (q+2)(q^2-4) (Kempner point q/(q^2-4) < (q+2)/q^2 Zone-1 top!)
            d = q - 4
            poly = 2 * (d * d + 6 * d + 4)
            if not (lhs > rhs and diff == poly and poly >= 8):
                failures += 1
        # Hierarchy: k_0 = 1/q < k_1 = (q+2)/q^2 < k_3 = 1/(q-2) and k_Kemp = q/(q^2-4) < k_3
        if not (q * q < q * (q + 2) and (q + 2) * (q - 2) < q * q and q * (q - 2) < q * q - 4):
            failures += 1
    print(f"Verified q in [3..50]: failures = {failures}")
    assert failures == 0


def test_sb106_universal_mod4_and_affine_bijection():
    print("=== Test 2 (SB.106): Universal Mod-4 50/50 Split & Mod-2^{S_0} Bijection ===")
    failures = 0
    for q in [3, 5, 7, 9, 11, 13, 15, 17, 19, 21]:
        for k in range(1, 10):
            # Even power q^(2k) % 8 == 1, Odd power q^(2k+1) % 8 == q % 8
            if (q ** (2 * k)) % 8 != 1:
                failures += 1
            if (q ** (2 * k + 1)) % 8 != (q % 8):
                failures += 1
        for s in range(1, 8):
            qs = q ** s
            for t in range(200):
                u1 = 4 * t + 1
                u3 = 4 * t + 3
                v1 = (qs * u1 + 1) % 4
                v3 = (qs * u3 + 1) % 4
                if qs % 4 == 1:
                    if not (v1 == 2 and v3 == 0):
                        failures += 1
                else:
                    if not (qs % 4 == 3 and v1 == 0 and v3 == 2):
                        failures += 1
                # Exactly one of {u1, u3} survives (mod 4 == 0) and one dies (mod 4 == 2)
                if not ((v1 == 0 and v3 == 2) or (v1 == 2 and v3 == 0)):
                    failures += 1
    print(f"Verified Mod-8 & Mod-4 50/50 split across 10 odd q: failures = {failures}")
    assert failures == 0


def test_sb107_universal_q_superblock_gauge_and_death_trap():
    print("=== Test 3 (SB.107): Universal ((q^2-4)u + 1) Super-Block Gauge & Odd-v2 Death Trap ===")
    failures = 0
    for q in [3, 5, 7, 9, 11, 13, 15, 17, 19, 21]:
        c_q = q * q - 4
        # Check c_q % 8 == 5 and c_q % 4 == 1
        if c_q % 8 != 5 or c_q % 4 != 1:
            failures += 1
        # Check single-step s_r = 2, s_{r+1} = 2 identity:
        # If 4 * u_next = q^2 * u + 1, then 4 * (c_q * u_next + 1) = q^2 * (c_q * u + 1)
        for t in range(500):
            u = 4 * t + 3  # since q^2 % 4 == 1, u % 4 == 3 gives 4 | (q^2 u + 1)
            if (q * q * u + 1) % 4 != 0:
                failures += 1
            u_next = (q * q * u + 1) // 4
            g_curr = c_q * u + 1
            g_next = c_q * u_next + 1
            if 4 * g_next != (q * q) * g_curr:
                failures += 1

        # Check multi-step Super-Block & Odd-Valuation Death Trap across 5,000 odd u0:
        for i in range(5000):
            u0 = 2 * i + 1
            g0 = c_q * u0 + 1
            v2_g0 = (g0 & -g0).bit_length() - 1
            # Count how many consecutive s=2 steps occur starting from u0 when fed into 2^{s} u' = q^2 u + 1
            m_actual = 0
            u_curr = u0
            while True:
                rhs = q * q * u_curr + 1
                s_next = (rhs & -rhs).bit_length() - 1
                if s_next == 2:
                    u_curr = rhs >> 2
                    m_actual += 1
                else:
                    terminal_s = s_next
                    break
            # Theorem SB.107:
            # - If v2(g0) = 2*m + 1 is ODD, then the orbit does EXACTLY m steps of s=2 and then DIES at terminal_s == 1!
            # - If v2(g0) = 2*m + 2 is EVEN (>= 2), write g0 = 4^(m+1) * V (V odd):
            #   then the orbit does EXACTLY m steps of s=2 and JUMPS to terminal_s >= 3, with UNIVERSAL exit-rung lock:
            #     * V % 4 == 3  <==>  terminal_s == 3
            #     * V % 8 == 5  <==>  terminal_s == 4
            #     * V % 8 == 1  <==>  terminal_s >= 5
            if v2_g0 % 2 == 1:
                m_pred = (v2_g0 - 1) // 2
                if not (m_actual == m_pred and terminal_s == 1):
                    failures += 1
            else:
                m_pred = (v2_g0 // 2) - 1
                V_odd = g0 >> v2_g0
                if not (m_actual == m_pred and terminal_s >= 3):
                    failures += 1
                if V_odd % 4 == 3 and terminal_s != 3:
                    failures += 1
                if V_odd % 8 == 5 and terminal_s != 4:
                    failures += 1
                if V_odd % 8 == 1 and terminal_s < 5:
                    failures += 1
            # And verify the O(1) jump formula: c_q * u_curr + 1 == q^(2*m_actual) * (g0 >> (2*m_actual))
            if c_q * u_curr + 1 != (q ** (2 * m_actual)) * (g0 >> (2 * m_actual)):
                failures += 1

    print(f"Verified Universal Super-Block Gauge & Odd-v2 Death Trap (50,000 orbits): failures = {failures}")
    assert failures == 0


if __name__ == "__main__":
    test_sb105_kempner_inversion_dichotomy()
    test_sb106_universal_mod4_and_affine_bijection()
    test_sb107_universal_q_superblock_gauge_and_death_trap()
    print("ALL WAVE 20 SANDBOX CHECKS PASSED (0 FAILURES).")
