"""
Semigroup Breakout — Loop 1B & Loop 2:
1. Beukers / Flatto-Lagarias-Pollington Padé Approximants at z = 1/9 (since 8/9 = 1 - 1/9)
   and how they couple with our Parry-Kneading constraints.
2. Multi-Block Hankel Determinants det [[P_{r1}, P_{r2}], [P_{r3}, P_{r4}]] and
   Two-Seed Cross-Ratio Repulsion across arbitrary survival branches.
"""

import math
from fractions import Fraction


def pade_polynomials_binomial(m: int, n: int, nu: Fraction):
    """
    Construct the (m, n) Padé approximant P_{m,n}(z) / Q_{m,n}(z) to (1 - z)^nu
    so that Q_{m,n}(z) (1 - z)^nu - P_{m,n}(z) = O(z^{m + n + 1}).
    Explicit hypergeometric formula for Q_{m,n}(z):
      Q_{m,n}(z) = sum_{j=0}^n (-1)^j * binom(n, j) * prod_{i=0}^{j-1} (m + nu + 1 + i) / prod_{i=0}^{j-1} (m + n - i) * z^j
    """
    Q = [Fraction(0)] * (n + 1)
    for j in range(n + 1):
        num = Fraction(math.comb(n, j))
        for i in range(j):
            num *= (m + nu + 1 + i)
            num /= (m + n - i)
        if j % 2 == 1:
            num = -num
        Q[j] = num

    # Compute Taylor series of (1 - z)^nu up to degree m + n
    taylor = [Fraction(0)] * (m + n + 1)
    coeff = Fraction(1)
    taylor[0] = coeff
    for k in range(1, m + n + 1):
        coeff *= -(nu - (k - 1)) / Fraction(k)
        taylor[k] = coeff

    # P(z) = (Q(z) * taylor(z)) mod z^{m+1}
    P = [Fraction(0)] * (m + 1)
    for deg in range(m + 1):
        s = Fraction(0)
        for j in range(min(deg, n) + 1):
            s += Q[j] * taylor[deg - j]
        P[deg] = s

    # Remainder coefficient at z^{m+n+1}
    rem_coeff = Fraction(0)
    # One more Taylor term
    coeff_next = coeff * (-(nu - (m + n))) / Fraction(m + n + 1)
    taylor_ext = taylor + [coeff_next]
    for j in range(n + 1):
        rem_coeff += Q[j] * taylor_ext[m + n + 1 - j]

    return P, Q, rem_coeff


def eval_poly(poly, z: Fraction) -> Fraction:
    res = Fraction(0)
    zpow = Fraction(1)
    for c in poly:
        res += c * zpow
        zpow *= z
    return res


def v_p(n: int, p: int) -> int:
    if n == 0:
        return 999999
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def test_beukers_pade():
    print("=== LOOP 1B: Beukers / FLP Padé Approximants to (1 - z)^{k/2} at z = 1/9 ===")
    # Note: 1 - 1/9 = 8/9 = 2^3 / 3^2, so (1 - 1/9)^{-1/2} = 3 / (2 * sqrt(2)),
    # or even better: for ANY rational approximation to (3/2)^k, Wait:
    # Why did Beukers use Padé approximants to (1 - z)^{1/2} or (1 + z)?
    # Let's check: in Mahler's problem, g_n = alpha (3/2)^n - f_n.
    # For TWO steps n and n + k, g_{n+k} - (3/2)^k g_n = (3/2)^k f_n - f_{n+k}, which is JUST K_{n,k} / 2^k!
    # Wait: why did Beukers use Padé approximants in his 1981 paper?
    # Because Beukers studied powers of (3/2)^n directly (when alpha = 1, i.e., {(3/2)^n})!
    # When alpha = 1 (the classical Mahler question for {(3/2)^n}), you KNOW g_0 = 1 and f_0 = 0!
    # Wait: for a GENERAL Z-number alpha = g_0 + f_0, f_0 is UNKNOWN!
    # How did Flatto-Lagarias-Pollington (1995) eliminate the unknown alpha between TWO Z-numbers alpha_1 < alpha_2
    # or along a SINGLE Z-number alpha?!
    pass


def analyze_two_seed_wronskian():
    """
    Let's test the TWO-SEED WRONSKIAN / DETERMINANT across arbitrary branches!
    Suppose alpha_1 != alpha_2 are two Z-numbers (or two companions up to step N).
    At EVERY step n:
      2 g_{n+1}^{(i)} - 3 g_n^{(i)} = eps_n^{(i)} in {0, 1}.
    Wait: what if we take a SINGLE Z-number alpha, and look at its renewal blocks:
      2^{s_r} P_{r+1} - 3^{s_r} P_r = 2^{s_r}.
    Wait: at EVERY block r, the right-hand side is 2^{s_r}!
    So:
      P_{r+1} - 1 = (3 / 2)^{s_r} P_r  (as a real/rational number, i.e. 2^{s_r} (P_{r+1} - 1) = 3^{s_r} P_r)!
    And in terms of the odd quotients u_r = (3 b_r + 1) / 2^{s_r} = P_r / 2^{s_r}:
      P_{r+1} = 3^{s_r} u_r + 1,  and  2^{s_{r+1}} u_{r+1} = 3^{s_r} u_r + 1!
    """
    print("=== LOOP 2A: Testing Multi-Block Hankel Determinants on the 54-Block Kneading Orbit ===")
    from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks
    blocks, _ = compute_kneading_blocks(30)
    b0, T_25, A_25 = minimal_odd_seed_for_blocks(blocks[:25])

    # Trace P_0, P_1, ..., P_25 for this seed b0
    P_list = []
    T_list = [0]
    b = b0
    T = 0
    for r in range(25):
        P_r = 3 * b + 1
        P_list.append(P_r)
        s = blocks[r]
        u = P_r >> s
        b = (3 ** (s - 1)) * u
        T += s
        T_list.append(T)
    P_list.append(3 * b + 1)

    # Find pairs of intervals [r1, r2] and [r3, r4] with the SAME step sum d = T_{r2} - T_{r1} = T_{r4} - T_{r3}
    by_d = {}
    for r1 in range(25):
        for r2 in range(r1 + 1, 26):
            d = T_list[r2] - T_list[r1]
            by_d.setdefault(d, []).append((r1, r2))

    print(f"Found {sum(len(v) > 1 for v in by_d.values())} step-sums d with multiple windows [r1, r2], [r3, r4].")
    for d in sorted(by_d.keys()):
        pairs = by_d[d]
        if len(pairs) >= 2 and d >= 10:
            (r1, r2), (r3, r4) = pairs[0], pairs[-1]
            if r1 < r3:
                # Compute Hankel determinant Det = P_{r1} * P_{r4} - P_{r2} * P_{r3}
                det = P_list[r1] * P_list[r4] - P_list[r2] * P_list[r3]
                # Compute window renewal numerators A_{r1, r2} and A_{r3, r4}
                A12 = (1 << d) * P_list[r2] - (3 ** d) * P_list[r1]
                A34 = (1 << d) * P_list[r4] - (3 ** d) * P_list[r3]
                rhs = P_list[r1] * A34 - P_list[r3] * A12
                assert (1 << d) * det == rhs
                # Also check archimedean bound on |det| / P_{r3}:
                # Since A12 < 3^d / 2 and A34 < 3^d / 2 and P_{r1} <= (2/3)^{T_{r3}-T_{r1}} P_{r3}:
                ratio = abs(det) / ((3 ** d) * P_list[r3] / (1 << (d + 1)))
                print(f"  d={d:>2}: [{r1},{r2}] vs [{r3},{r4}] | v_2(RHS)={v_p(rhs, 2):>2} >= d={d} | |det| / (0.5*(3/2)^d P_r3) = {ratio:.6f} < 1")


if __name__ == "__main__":
    analyze_two_seed_wronskian()
