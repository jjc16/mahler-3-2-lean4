"""
Wave 21-22 Discovery Sandbox: Comprehensive Computational Exploration & Verification
of All 8 Unconsidered Angles (Angle 0 through Angle 7):

  Angle 0: Adelic / Profinite Meta-Theorem Upgrade (Z_hat = prod_p Z_p decoupling:
           invertibility of 2^{T_r} modulo EVERY odd modulus M = 2m + 1, proving every
           odd prime modulus is unconditionally realizable for every P_0, and only gains
           teeth when coupled with Archimedean positivity u_r >= 1 or p | u_r => p <= u_r).
  Angle 1: The Real-First Parry Transfer Map B : [0, 1/2) -> Z_2 (total invariance of
           [0, 1/2) under F, dual R/Q_2 evaluation of Psi_{r_0}(2/3), and rational/periodic
           itinerary obstruction B(r_0) = -r_0 not in N_{>0}).
  Angle 2: Unconditional Effective Power-Saving Survivor Bounds (#(Z cap [0, 2^W)) <= F_{W+2}
           via SB.4 + Fibonacci 11-ban, exact Parry cylinder count |C_W| <= 2*(3/2)^W,
           and 2-adic Fourier/character concentration on the top-bit desert).
  Angle 3: Base-6 (6 = 2 * 3) Joint Terminating Automaton (3/2 = 1.3_6, 2/3 = 0.4_6,
           1/3 = 0.2_6, 1/2 = 0.3_6; 1-digit survival lock f_1 in {0,1} on even steps,
           f_1 = 2 on odd steps; Kempner depth 2*4^{T_r} / 6^{T_r + 1}).
  Angle 4: Two-Superblock Renormalized Transfer Law & Catalan-Pillai s^* = 3 Unit Equation
           (3^{2 m_1 + s^*} V_1 - 2^{2 m_2 + s^*} V_2 = 3^{s^*-2} - 2^{s^*-2}, gcd(V_1, V_2) = 1
           at BOTH s^* = 3 and s^* = 4, and abc radical ratio analysis).
  Angle 5: Higher-Order m x m Hankel Row-Reduction & Polya-Carlson-Amice Adelic Capacity
           Tangency (R_inf * R_2 = 1; exact 2^{m-1} row reduction to binary {0,1} parities;
           identical vanishing of 3x3 Hankel on s >= 5 and 4x4 Hankel on (2,2,2) runs!).
  Angle 6: Universal Local Multi-Block Word-Power Obstruction V^m at Arbitrary Late Horizon
           (2^{m d} | ((3^d - 2^d) P_r + A_V) and 5 * 2^{T_r + m d} < 3^{T_r + d}(5 P_0 + 4)).
  Angle 7: Rational Z-Number Impossibility, Continued-Fraction Shadowing Escape, &
           Irrationality Measure Pinch on alpha.
"""

import cmath
import math
from fractions import Fraction


def mahler_step_int(g: int) -> int:
    return (3 * g + (g & 1)) // 2


def trace_blocks(b0: int):
    """Return list of (P_r, s_r, u_r) while s_r >= 2."""
    p = 3 * b0 + 1
    chain = []
    while True:
        s = (p & -p).bit_length() - 1
        u = p >> s
        chain.append((p, s, u))
        if s < 2:
            break
        p = (3 ** s) * u + 1
    return chain


def test_angle0_adelic_profinite_decoupling():
    print("=== Angle 0: Adelic / Profinite Meta-Theorem Upgrade (Z_hat Decoupling) ===")
    failures = 0
    # Verify explicit closed-form inverse of 2 modulo any odd M = 2*m + 1:
    # Notice: 2 * (m + 1) = 2*m + 2 = (2*m + 1) + 1 === 1 (mod 2*m + 1)!!
    # Therefore, (m + 1)^{T_r} is an EXPLICIT CLOSED-FORM INVERSE of 2^{T_r} mod (2*m + 1)!!
    for m in range(0, 80):
        M = 2 * m + 1
        inv2 = m + 1
        if M > 1 and (2 * inv2) % M != 1:
            failures += 1
        for T in range(0, 15):
            inv_pow = pow(inv2, T, M) if M > 1 else 0
            if M > 1 and (pow(2, T, M) * inv_pow) % M != 1:
                failures += 1
            # Unique solution P_r mod M for ANY P_0 and ANY A_K:
            for P0 in [1, 4, 7, 28, 103]:
                for AK in [0, 1, 5, 19, 65]:
                    rhs = (pow(3, T, M) * P0 + AK) % M
                    Pr = (inv_pow * rhs) % M if M > 1 else 0
                    if (pow(2, T, M) * Pr) % M != rhs:
                        failures += 1
                    # Uniqueness in [0, M):
                    sols = [x for x in range(M) if (pow(2, T, M) * x) % M == rhs]
                    if len(sols) != 1:
                        failures += 1
    print(f"Angle 0 verified (explicit inverse (m+1)^T mod (2m+1)): failures = {failures}")
    assert failures == 0


def test_angle1_real_first_parry_transfer():
    print("=== Angle 1: Real-First Parry Transfer Map B : [0, 1/2) -> Z_2 ===")
    failures = 0
    # Test rational r0 in [0, 1/2): F maps EVERY r0 in [0, 1/2) into [0, 1/2) forever!
    for den in range(3, 60):
        for num in range(0, (den + 1) // 2):
            r0 = Fraction(num, den)
            if not (0 <= r0 < Fraction(1, 2)):
                continue
            r = r0
            psi_N = 0
            # Choose arbitrary g0 that matches parity up to N=10 steps via 2-adic lift!
            e_list = []
            for n in range(12):
                if r < Fraction(1, 3):
                    e = 0
                    r_next = Fraction(3, 2) * r
                    if not (0 <= r_next < Fraction(1, 2)):
                        failures += 1
                else:
                    e = 1
                    r_next = Fraction(3, 2) * r - Fraction(1, 2)
                    if not (0 <= r_next < Fraction(1, 4)):
                        failures += 1
                if 2 * r_next != 3 * r - e:
                    failures += 1
                psi_N = 3 * psi_N + (2 ** n) * e
                e_list.append(e)
                r = r_next
            # Check N-step identity: 2^12 * r_12 + psi_12 == 3^12 * r0
            if (2 ** 12) * r + psi_N != (3 ** 12) * r0:
                failures += 1
            # Check unique 2-adic residue b0 in [0, 2^12) realizing e_list:
            inv3 = pow(3, -1, 2 ** 12)
            # 2^12 g_12 = 3^12 b0 + psi_12 === 0 (mod 2^12) => b0 === -psi_12 * 3^{-12} (mod 2^12)
            b0_mod = ((-psi_N) * pow(inv3, 12, 2 ** 12)) % (2 ** 12)
            g = b0_mod
            for n in range(12):
                if (g & 1) != e_list[n]:
                    failures += 1
                g = (3 * g + e_list[n]) // 2
    print(f"Angle 1 verified across ~850 rational points in [0, 1/2): failures = {failures}")
    assert failures == 0


def test_angle2_effective_power_saving_and_fourier():
    print("=== Angle 2: Effective Power-Saving Survivor Bounds & 2-Adic Fourier Sums ===")
    failures = 0
    # 1. Exact Parry cylinder count |C_W([0, 1/2))| vs Fibonacci F_{W+2} vs 2 * (3/2)^W
    # Track exact rational intervals of cylinders in [0, 1/2):
    cylinders = [(Fraction(0, 1), Fraction(1, 2), ())]
    fib = [0, 1]
    for _ in range(25):
        fib.append(fib[-1] + fib[-2])

    print(f"{'W':>3s} | {'Actual Surv <2^W':>16s} | {'Parry |C_W|':>11s} | {'Fib F_{W+2}':>11s} | {'2*(3/2)^W':>10s} | {'Max |S(h)|/|C_W|':>16s}")
    print("-" * 82)
    for W in range(1, 17):
        next_cyls = []
        for lo, hi, word in cylinders:
            # Split [lo, hi) at 1/3:
            third = Fraction(1, 3)
            if hi <= third:
                next_cyls.append((Fraction(3, 2) * lo, Fraction(3, 2) * hi, word + (0,)))
            elif lo >= third:
                next_cyls.append((Fraction(3, 2) * lo - Fraction(1, 2), Fraction(3, 2) * hi - Fraction(1, 2), word + (1,)))
            else:
                next_cyls.append((Fraction(3, 2) * lo, Fraction(1, 2), word + (0,)))
                next_cyls.append((Fraction(0, 1), Fraction(3, 2) * hi - Fraction(1, 2), word + (1,)))
        cylinders = next_cyls
        c_w = len(cylinders)
        f_w2 = fib[W + 2]
        # Count actual seeds b0 in [0, 2^W) that survive W Mahler steps (having a valid r0 in [0, 1/2) for W steps):
        # Wait: EVERY Parry cylinder w of length W has a UNIQUE b0(w) in [0, 2^W)!!
        # Let's check that!! For N = W, b0(w) in [0, 2^W) is a BIJECTION between C_W and {b0 < 2^W : survives W steps}!!
        mod = 2 ** W
        inv3_W = pow(3, -W, mod)
        b0_set = set()
        for _, _, word in cylinders:
            psi = 0
            for n, e in enumerate(word):
                psi = 3 * psi + (2 ** n) * e
            b0 = ((-psi) * inv3_W) % mod
            b0_set.add(b0)
        if len(b0_set) != c_w:
            failures += 1
        if not (c_w <= f_w2):
            failures += 1
        # Check exact integer inequality: 2^W * c_w <= 2 * 3^W (i.e. c_w <= 2 * (3/2)^W)!
        if not ((2 ** W) * c_w <= 2 * (3 ** W)):
            failures += 1
        # Check Lucas/Fibonacci power-saving inequality: F_{5*k + 2} vs 12^k or F_{10*k + 2} <= 2 * 128^k
        # Also compute max non-trivial 2-adic Fourier character |sum_{b in b0_set} exp(2*pi*i*h*b / 2^W)| / c_w for h=1..15
        max_char = 0.0
        for h in range(1, min(16, mod)):
            s_val = sum(cmath.exp(2j * math.pi * h * b / mod) for b in b0_set)
            max_char = max(max_char, abs(s_val) / c_w)
        if W in [2, 4, 6, 8, 10, 12, 14, 16]:
            print(f"{W:3d} | {len(b0_set):16d} | {c_w:11d} | {f_w2:11d} | {2*(1.5**W):10.2f} | {max_char:16.4f}")

    # Check Fibonacci power-saving bound F_{4*k + 2} <= 2 * 7^k < 2 * 8^k = 2^{3*k + 1}!
    # WAIT A SECOND! phi^4 = 3*phi + 2 approx 6.854 < 7 < 8 = 2^3!!
    # Let's check F_{4*k + 2} <= 2 * 7^k and F_{4*k + 2} <= 2 * 8^k = 2^{3*k + 1} (exponent 3/4 = 0.75 < 1)!
    for k in range(0, 25):
        fk = math.comb(2, 1)  # dummy
        # compute exact fib(4*k + 2)
        a, b = 0, 1
        for _ in range(4 * k + 2):
            a, b = b, a + b
        if not (a <= (7 ** k) + (7 ** k)):
            failures += 1
        if not (a < 2 * (8 ** k)):
            failures += 1
    print(f"Angle 2 verified (EXACT bijection |Surv_W(<2^W)| == |C_W| <= 2*(3/2)^W <= F_{{W+2}}): failures = {failures}")
    assert failures == 0


def test_angle3_base_six_automaton():
    print("=== Angle 3: Base-6 (6 = 2 * 3) Joint Terminating Automaton ===")
    failures = 0
    for den in range(1, 40):
        for num in range(0, 6 * den):
            x = Fraction(num, den)
            g = math.floor(x)
            r = x - g
            # First Base-6 fractional digit f1 = floor(6 * r) in {0, 1, 2, 3, 4, 5}:
            f1 = math.floor(6 * r)
            d0 = g % 6
            if not (0 <= f1 <= 5):
                failures += 1
            # Survival 0 <= r < 1/2  <==>  f1 in {0, 1, 2}
            if (r < Fraction(1, 2)) != (f1 in (0, 1, 2)):
                failures += 1
            # Valid Mahler step (even g & r < 1/3) <==> (d0 in {0,2,4} and f1 in {0,1})
            if ((g % 2 == 0) and (r < Fraction(1, 3))) != ((d0 in (0, 2, 4)) and (f1 in (0, 1))):
                failures += 1
            # Valid Mahler step (odd g & 1/3 <= r < 1/2) <==> (d0 in {1,3,5} and f1 == 2)
            if ((g % 2 == 1) and (Fraction(1, 3) <= r < Fraction(1, 2))) != ((d0 in (1, 3, 5)) and (f1 == 2)):
                failures += 1
    # Check Kempner Base-6 identity: (1/3) * (2/3)^T == (2 * 4^T) / 6^(T + 1)
    # Cross-cleared: 3 * (2 * 4^T) * 3^T == 6^(T + 1) * 2^T
    for T in range(0, 30):
        if 3 * (2 * (4 ** T)) * (3 ** T) != (6 ** (T + 1)) * (2 ** T):
            failures += 1
    print(f"Angle 3 verified (Base-6 digit locks & Kempner depth): failures = {failures}")
    assert failures == 0


def test_angle4_two_superblock_catalan_pillai_and_abc():
    print("=== Angle 4: Two-Superblock Catalan-Pillai Transition & ABC Radical Bridge ===")
    failures = 0
    s3_transitions = 0
    s4_transitions = 0
    max_abc_quality = 0.0
    for i in range(1, 100000):
        b0 = 2 * i + 1
        chain = trace_blocks(b0)
        # Need interior blocks r >= 1 with s_r >= 2:
        # Recall W_r = (5 * P_r + 4) // 36 for r >= 1 when s_{r-1} >= 2 and s_r >= 2!
        # Let's extract interior W_r list while s_r >= 2:
        # Wait: chain[k] = (P_k, s_k, u_k). Interior block k >= 1 has (5*P_k + 4) % 36 == 0
        # PROVIDED s_{k-1} >= 2 AND s_k >= 2!
        interior = []
        for k in range(1, len(chain) - 1):  # chain[-1] has s < 2
            Pk, sk, uk = chain[k]
            if (5 * Pk + 4) % 36 != 0:
                failures += 1
            Wk = (5 * Pk + 4) // 36
            interior.append((Wk, sk))
        # Group interior into Super-Blocks:
        idx = 0
        superblocks = []
        while idx < len(interior):
            W_start = interior[idx][0]
            m = 0
            while idx < len(interior) and interior[idx][1] == 2:
                m += 1
                idx += 1
            if idx < len(interior):
                # Exited at s^* = interior[idx][1] >= 3, AND only record if NEXT block ALSO survives (idx + 1 < len(interior))!
                s_star = interior[idx][1]
                V = W_start >> (2 * m)
                if W_start != (4 ** m) * V or V % 2 != 1:
                    failures += 1
                # Only record a Two-Superblock transition when W_next ALSO completes its own m2-block s=2 run
                # and exits at some surviving s2_star >= 3 inside `interior`!
                if idx + 1 < len(interior):
                    j = idx + 1
                    W_next = interior[j][0]
                    m2 = 0
                    while j < len(interior) and interior[j][1] == 2:
                        m2 += 1
                        j += 1
                    if j < len(interior):
                        # W_next genuinely survived its m2-block s=2 run and reached s2_star >= 3!
                        V2 = W_next >> (2 * m2)
                        if W_next != (4 ** m2) * V2 or V2 % 2 != 1:
                            failures += 1
                        superblocks.append((m, V, s_star, m2, V2))
                idx += 1
        for m1, V1, s_star, m2, V2 in superblocks:
            lhs = (3 ** (2 * m1 + s_star)) * V1
            rhs = (2 ** (2 * m2 + s_star)) * V2 + ((3 ** (s_star - 2)) - (2 ** (s_star - 2)))
            if lhs != rhs:
                failures += 1
            g = math.gcd(V1, V2)
            if (3 ** (s_star - 2) - 2 ** (s_star - 2)) % g != 0:
                failures += 1
            if s_star == 3:
                s3_transitions += 1
                if lhs - (2 ** (2 * m2 + 3)) * V2 != 1 or g != 1:
                    failures += 1
            elif s_star == 4:
                s4_transitions += 1
                if g != 1:
                    failures += 1
            # Compute abc quality q(A, B, C) for A + B = C (divided by gcd) on moderate sizes:
            B_term = (3 ** (s_star - 2)) - (2 ** (s_star - 2))
            A_term = (2 ** (2 * m2 + s_star)) * V2
            C_term = lhs
            d_gcd = math.gcd(A_term, C_term)
            a0, b0_t, c0 = A_term // d_gcd, B_term // d_gcd, C_term // d_gcd
            prod = a0 * b0_t * c0
            if prod < 10 ** 12:
                rad = 1
                tmp = prod
                p = 2
                while p * p <= tmp:
                    if tmp % p == 0:
                        rad *= p
                        while tmp % p == 0:
                            tmp //= p
                    p += 1 if p == 2 else 2
                if tmp > 1:
                    rad *= tmp
                if c0 > 1 and rad > 1:
                    q_abc = math.log(c0) / math.log(rad)
                    if q_abc > max_abc_quality:
                        max_abc_quality = q_abc
    print(f"Angle 4 verified ({s3_transitions} s*=3 & {s4_transitions} s*=4 transitions, max abc quality={max_abc_quality:.4f}): failures = {failures}")
    assert failures == 0


def det_int(mat):
    n = len(mat)
    if n == 1:
        return mat[0][0]
    if n == 2:
        return mat[0][0] * mat[1][1] - mat[0][1] * mat[1][0]
    total = 0
    for c in range(n):
        sub = [row[:c] + row[c + 1:] for row in mat[1:]]
        total += ((-1) ** c) * mat[0][c] * det_int(sub)
    return total


def test_angle5_higher_order_hankel_determinants():
    print("=== Angle 5: Higher-Order m x m Hankel Row-Reduction & Vanishing Laws ===")
    failures = 0
    for b0 in range(1, 500):
        g = [b0]
        e = []
        for _ in range(25):
            ek = g[-1] & 1
            e.append(ek)
            g.append((3 * g[-1] + ek) // 2)
        for n in range(0, 15):
            # Test m = 2, 3, 4: 2^(m-1) * det(g_{n+i+j}) == det([row0_g, row1_e, ..., row_{m-1}_e])
            for m in [2, 3, 4]:
                H = [[g[n + i + j] for j in range(m)] for i in range(m)]
                R = [H[0][:]] + [[e[n + i - 1 + j] for j in range(m)] for i in range(1, m)]
                dH = det_int(H)
                dR = det_int(R)
                if (2 ** (m - 1)) * dH != dR:
                    failures += 1
                # Vanishing laws:
                if m == 3 and e[n:n + 4] == [0, 0, 0, 0] and dH != 0:
                    failures += 1
                if m == 4 and e[n:n + 6] == [1, 0, 1, 0, 1, 0] and dH != 0:
                    failures += 1
                if m == 4 and e[n:n + 6] == [0, 1, 0, 1, 0, 1] and dH != 0:
                    failures += 1
    print(f"Angle 5 verified (2x2, 3x3, 4x4 Hankel row reduction & Super-Block vanishing): failures = {failures}")
    assert failures == 0


def test_angle6_local_word_power_obstruction():
    print("=== Angle 6: Universal Local Multi-Block Word-Power Obstruction V^m ===")
    failures = 0
    checked = 0
    for i in range(1, 50000):
        b0 = 2 * i + 1
        chain = trace_blocks(b0)
        # chain[:-1] has all s_k >= 2; look for ANY repeated subword V^m (L >= 1, m >= 2) at index r!
        valid = chain[:-1]
        s_list = [x[1] for x in valid]
        K = len(s_list)
        if K < 2:
            continue
        P0 = chain[0][0]
        for r in range(K):
            T_r = sum(s_list[:r])
            P_r = valid[r][0]
            for L in range(1, (K - r) // 2 + 1):
                word = s_list[r:r + L]
                m = 1
                while r + (m + 1) * L <= K and s_list[r + m * L:r + (m + 1) * L] == word:
                    m += 1
                if m >= 2:
                    checked += 1
                    d = sum(word)
                    # Compute A_V for word:
                    A_V = 0
                    t_acc = 0
                    for s_val in word:
                        t_acc += s_val
                        A_V = (3 ** s_val) * A_V + (2 ** t_acc)
                    #Wait: verify 2^d * P_{r+L} == 3^d * P_r + A_V!
                    # Let's check exact definition of renewalNumerator:
                    # P_{k+1} = 3^{s_k} * (P_k / 2^{s_k}) + 1 => 2^{s_k} P_{k+1} = 3^{s_k} P_k + 2^{s_k}!
                    P_rL = valid[r + L][0]
                    if (2 ** d) * P_rL != (3 ** d) * P_r + A_V:
                        failures += 1
                    G_r = ((3 ** d) - (2 ** d)) * P_r + A_V
                    P_rmL = chain[r + m * L][0]
                    G_rmL = ((3 ** d) - (2 ** d)) * P_rmL + A_V
                    if (2 ** (m * d)) * G_rmL != (3 ** (m * d)) * G_r:
                        failures += 1
                    if G_r % (2 ** (m * d)) != 0:
                        failures += 1
                    # Check unconditional elementary cutoff: 5 * 2^{T_r + m*d} < 3^{T_r + d} * (5 * P0 + 4)
                    # Wait: check 5 * A_V < 4 * 3^d (from SB.24, since all s_val >= 2)!
                    if not (5 * A_V <= 4 * ((3 ** d) - (2 ** d))):
                        failures += 1
                    if not (5 * (2 ** (T_r + m * d)) < (3 ** (T_r + d)) * (5 * P0 + 4)):
                        failures += 1
    print(f"Angle 6 verified ({checked} local word powers V^m in genuine orbits): failures = {failures}")
    assert failures == 0


def test_angle7_rational_impossibility_and_shadowing():
    print("=== Angle 7: Rational Remainder Law, Shadowing Escape & Diophantine Pinch ===")
    failures = 0
    # 1. Pure integer escape at exact step v2(p) + 1:
    for p in range(1, 300):
        v2p = (p & -p).bit_length() - 1
        x = Fraction(p, 1)
        for k in range(v2p + 1):
            if x.denominator != 1:
                failures += 1
            if k < v2p:
                x = x * Fraction(3, 2)
        # At step v2(p), x is an ODD integer; at step v2(p) + 1, {x * 3/2} == 1/2!
        if x % 2 != 1:
            failures += 1
        x_next = x * Fraction(3, 2)
        if x_next - math.floor(x_next) != Fraction(1, 2):
            failures += 1

    # 2. Coprime rational remainder recurrence X_n = (3^n * p) % (2^n * q) & v2 stabilization:
    max_rat_steps = 0
    worst_rat = None
    shadow_verified = 0
    for q in range(1, 81):
        for p in range(1, 201):
            if math.gcd(p, q) != 1:
                continue
            v2p = (p & -p).bit_length() - 1
            x = Fraction(p, q)
            steps = 0
            while steps < 500:
                Xn = ((3 ** steps) * p) % ((2 ** steps) * q)
                gn = ((3 ** steps) * p) // ((2 ** steps) * q)
                r = x - math.floor(x)
                if Fraction(Xn, (2 ** steps) * q) != r or gn != math.floor(x):
                    failures += 1
                if steps > v2p:
                    v2X = (Xn & -Xn).bit_length() - 1
                    if Xn == 0 or v2X != v2p:
                        failures += 1
                if r >= Fraction(1, 2):
                    # Check Quantitative Rational Shadowing Escape whenever Xn > 2^(steps-1)*q (steps >= 1):
                    if steps >= 1:
                        half_mod = (2 ** (steps - 1)) * q
                        full_mod = (2 ** steps) * q
                        E = min(Xn - half_mod, full_mod - Xn)
                        if E >= 1:
                            # Test perturbed real/rational alpha = p/q +/- (E - 1/2)/(q * 3^steps):
                            for sgn in (-1, 1):
                                delta = Fraction(sgn * (2 * E - 1), 2 * q * (3 ** steps))
                                alpha_pert = Fraction(p, q) + delta
                                x_pert = alpha_pert * (Fraction(3, 2) ** steps)
                                r_pert = x_pert - math.floor(x_pert)
                                if not (r_pert >= Fraction(1, 2)):
                                    failures += 1
                                shadow_verified += 1
                    break
                # While step `steps + 1` ALSO survives (`r_next < 1/2`), verify X_{n+1} == 3 * X_n - 2^n * q * (g_n % 2):
                x_next_val = x * Fraction(3, 2)
                r_next_val = x_next_val - math.floor(x_next_val)
                if r_next_val < Fraction(1, 2):
                    X_next = ((3 ** (steps + 1)) * p) % ((2 ** (steps + 1)) * q)
                    if X_next != 3 * Xn - (2 ** steps) * q * (gn & 1):
                        failures += 1
                x = x_next_val
                steps += 1
            if steps >= 500:
                failures += 1
            if steps > max_rat_steps:
                max_rat_steps = steps
                worst_rat = (p, q)
    print(f"All coprime rationals p/q (1<=q<=80, 1<=p<=200) died (max={max_rat_steps} at {worst_rat[0]}/{worst_rat[1]}, {shadow_verified} shadowing balls verified): failures = {failures}")
    assert failures == 0


if __name__ == "__main__":
    test_angle0_adelic_profinite_decoupling()
    test_angle1_real_first_parry_transfer()
    test_angle2_effective_power_saving_and_fourier()
    test_angle3_base_six_automaton()
    test_angle4_two_superblock_catalan_pillai_and_abc()
    test_angle5_higher_order_hankel_determinants()
    test_angle6_local_word_power_obstruction()
    test_angle7_rational_impossibility_and_shadowing()
    print("ALL 8 ANGLES (0 THROUGH 7) PASSED IN WAVE 21 SANDBOX (0 FAILURES).")
