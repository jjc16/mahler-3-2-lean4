"""
Wave 25 Discovery Sandbox: Quantitative Barriers of Methods 1-3 + Four Fusion Ideas
for #2 (Prime-Supply >= 5, Multiplicative-to-Additive Dual Product, Laplace-Poisson
Origin Damping Z_N(W), and the Real-Coupled Mod-64 / Mod-320 Ceiling-Dual Gauge Pinch)
(SB.133-SB.140).
"""

import math
from fractions import Fraction
from sandbox_wave23_fourier_frontier_and_parseval_barrier import build_parry_tree_levels


def trace_true_half_interval_blocks(b0: int):
    """
    Trace block chain of odd b0 enforcing BOTH 2-adic survival (s_r >= 2) AND
    true [0, 1/2) real companion feasibility (minSlack > 0, i.e., mu > 0)!
    Recall normalized slack recurrence (CoupledFractionalPartDynamics.lean):
      mu_0 = 1,  mu_{r+1} = min(1, (3/2)^{s_r} * mu_r - 2),
      surviving step T_{r+1} iff mu_{r+1} > 0!
    Wait: let's verify against exact rational interval intersection [lo, hi) subset [0, 1/2)!
    """
    g = b0
    lo = Fraction(0, 1)
    hi = Fraction(1, 2)
    step_idx = 0
    blocks = []
    # Require b0 odd so step 0 is odd:
    assert b0 % 2 == 1
    while True:
        # Check current odd step feasibility [1/3, 1/2) for r_{step_idx}:
        # Since x_n = (b0 + r0) * (3/2)^n = g_n + r_n, r_n = (3/2)^n * r0 + ((3/2)^n * b0 - g_n) — wait:
        # Simpler: track interval [r_lo, r_hi) of r_n at step n directly under F!
        if step_idx == 0:
            r_lo, r_hi = Fraction(0, 1), Fraction(1, 2)
        # At an odd step g, we MUST have r_n in [1/3, 1/2):
        r_lo = max(r_lo, Fraction(1, 3))
        if r_lo >= r_hi:
            break
        # Determine 2-adic rung s = v2(3*g + 1):
        P = 3 * g + 1
        s = (P & -P).bit_length() - 1
        u = P >> s
        # Apply 1 odd step F_odd(r) = (3*r - 1)/2:
        r_lo = (3 * r_lo - 1) / 2
        r_hi = (3 * r_hi - 1) / 2
        g = (3 * g + 1) // 2
        step_idx += 1
        if s < 2:
            blocks.append((P, s, u, False))
            break
        # Apply (s - 1) even steps F_even(r) = (3/2)*r, requiring r < 1/3 at each even step:
        died_real = False
        for _ in range(s - 1):
            r_hi = min(r_hi, Fraction(1, 3))
            if r_lo >= r_hi:
                died_real = True
                break
            r_lo = Fraction(3, 2) * r_lo
            r_hi = Fraction(3, 2) * r_hi
            g = (3 * g) // 2
            step_idx += 1
        if died_real:
            blocks.append((P, s, u, False))
            break
        blocks.append((P, s, u, True))
    return blocks


def test_sb133_135_three_method_barriers():
    print("=== Test 1 (SB.133-SB.135): Quantitative Barriers of Standalone Methods 1, 2, 3 ===")
    failures = 0
    levels = build_parry_tree_levels(15)

    # SB.133: Method 1 Pigeonhole cylinder excess: at L = 7*k vs M = 12*k:
    # 2^(7*k) * |C_{7*k}| >= 3^(7*k) = 2187^k, and 17 * 128 = 2176 < 2187, so |C_{7*k}| >= 17^k > 12*k + 1!
    for k in range(1, 15):
        if not ((17 ** k) * (128 ** k) < (2187 ** k)):
            failures += 1
        if not ((12 * k + 1) < (17 ** k)):
            failures += 1

    # SB.134: Method 2 unconditional R_0 >= 3^(T_K - s_0) & u_K * R_0 radical excess:
    for i in range(1, 5000):
        b0 = 2 * i + 1
        blocks = trace_true_half_interval_blocks(b0)
        valid = [b for b in blocks if b[3]]
        if len(valid) >= 2:
            s_list = [b[1] for b in valid]
            u0 = valid[0][2]
            s0 = s_list[0]
            # Compute A_{0,K} and R_0 = A_{0,K} // 2^s0 for K = len(valid) - 1:
            K = len(valid) - 1
            T_K = sum(s_list[:K])
            A_K = 0
            t_acc = 0
            for idx in range(K):
                t_acc += s_list[idx]
                A_K = (3 ** s_list[idx]) * A_K + (2 ** t_acc)
            R0 = A_K >> s0
            uK = valid[K][2]
            sK = valid[K][1]
            S0 = T_K - s0 + sK
            if (2 ** S0) * uK != (3 ** T_K) * u0 + R0:
                failures += 1
            if R0 < 3 ** (T_K - s0):
                failures += 1
            if (2 ** S0) * (uK * R0) <= (3 ** (2 * T_K - s0)) * u0:
                failures += 1

    # SB.135: Method 3 exact shift-sum identity & Laplace-Poisson origin damping Z_N(W):
    W = 4
    print(f"Laplace-Poisson Origin Partition Function Z_N(W={W}) = sum_{{w in C_N}} exp(-b0(w)/16):")
    for N in [4, 6, 8, 10, 12, 14]:
        mod = 2 ** N
        inv3 = pow(3, -N, mod)
        b_list = [((-psi) * inv3) % mod for _, psi in levels[N]]
        ind = [0] * mod
        for b in b_list:
            ind[b] = 1
        # Exact shift-sum identity: sum_{a=0}^{M-1} sum_{j=0}^{L-1} ind[(a+j)%M] == L * |C_N|
        L = 2 ** W
        if N <= 10:
            shift_sum = sum(sum(ind[(a + j) % mod] for j in range(L)) for a in range(mod))
            if shift_sum != L * len(b_list):
                failures += 1
        z_val = sum(math.exp(-b / L) for b in b_list)
        surv_pos = sum(1 for b in b_list if 0 < b < L)
        print(f"  N={N:2d}: Z_N(4) = {z_val:.6f} (positive survivors in [1,16): {surv_pos})")

    print(f"SB.133-SB.135 verified: failures = {failures}")
    assert failures == 0


def test_sb136_139_method2_fusion_and_mod320_pinch():
    print("\n=== Test 2 (SB.136-SB.139): Prime>=5 Supply, Dual Product, & Mod-320 Even-Gauge Pinch ===")
    failures = 0
    even_W_checked = 0
    even_W_residues_mod64 = set()
    even_W_residues_mod320 = set()

    # 1. Verify exact (2, 2), (2, 3), (2, 4), (2, 5) thresholds > 1/2 vs (2, 6) < 1/2:
    # After s_r = 2 and s_{r+1} = c, followed by odd step (r_end >= 1/3):
    # Let's compute exact rational threshold r_min(c) such that F_even^(c-1)(F_odd(F_even(F_odd(r0)))) >= 1/3!
    expected_thresholds = {
        2: Fraction(133, 243),
        3: Fraction(383, 729),
        4: Fraction(1117, 2187),
        5: Fraction(3287, 6561),
        6: Fraction(9733, 19683),
    }
    for c, thresh in expected_thresholds.items():
        # Evaluate forward from r0 = thresh:
        r = thresh
        r = (3 * r - 1) / 2  # odd
        r = (3 * r) / 2      # even (completes s = 2)
        r = (3 * r - 1) / 2  # odd
        for _ in range(c - 1):
            r = (3 * r) / 2  # (c - 1) evens
        if r != Fraction(1, 3):
            failures += 1
        if c <= 5 and not (thresh > Fraction(1, 2)):
            failures += 1
        if c == 6 and not (thresh < Fraction(1, 2)):
            failures += 1

    # 2. Scan 200,000 odd seeds under TRUE [0, 1/2) survival!
    for i in range(1, 200001):
        b0 = 2 * i + 1
        blocks = trace_true_half_interval_blocks(b0)
        valid = [b for b in blocks if b[3]]

        # Check SB.136: for all r >= 1 in valid, gcd(u_r, 6) == 1 (so if u_r > 1, all prime factors >= 5):
        for r in range(1, len(valid)):
            ur = valid[r][2]
            if math.gcd(ur, 6) != 1 or (ur > 1 and ur < 5):
                failures += 1

        # Check SB.138 & SB.139 on every interior block k >= 1 where k + 2 < len(valid)
        # (so block k, block k+1, AND the odd entry of block k+2 all survive in [0, 1/2)!):
        for k in range(1, len(valid) - 2):
            Pk, sk, uk, _ = valid[k]
            Pk1, sk1, uk1, _ = valid[k + 1]
            assert (5 * Pk + 4) % 36 == 0
            Wk = (5 * Pk + 4) // 36
            if Wk % 2 == 0:
                # Then sk MUST be 2! And by SB.138, sk1 MUST be >= 6!!
                even_W_checked += 1
                if sk != 2 or sk1 < 6:
                    print(f"FAILURE at b0={b0}, k={k}: sk={sk}, sk1={sk1}, Wk={Wk}")
                    failures += 1
                even_W_residues_mod64.add(Wk % 64)
                even_W_residues_mod320.add(Wk % 320)

    print(f"Checked {even_W_checked} interior even-W blocks surviving 2 more blocks in [0, 1/2):")
    print(f"  Observed W_{'{r+1}'} mod 64  residues (out of 32 even classes): {sorted(even_W_residues_mod64)}")
    print(f"  Observed W_{'{r+1}'} mod 320 residues (out of 160 even classes): {sorted(even_W_residues_mod320)}")
    assert failures == 0
    print("ALL WAVE 25 SANDBOX CHECKS PASSED (0 FAILURES)!")


if __name__ == "__main__":
    test_sb133_135_three_method_barriers()
    test_sb136_139_method2_fusion_and_mod320_pinch()
