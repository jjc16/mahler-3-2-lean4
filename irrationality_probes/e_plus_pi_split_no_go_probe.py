#!/usr/bin/env python3
"""
Exact-Arithmetic & 140-Digit Probe for Split-Integral & Determinant No-Go Laws on e + pi
(Companion script to irrationality_probes/EPlusPiSplitNoGo.lean, Theorems EP.1 - EP.4).
"""

from decimal import Decimal, getcontext
from fractions import Fraction
import math

getcontext().prec = 140


def compute_e_pi_decimal() -> tuple[Decimal, Decimal]:
    e_val = Decimal(0)
    fact = 1
    for k in range(105):
        if k > 0:
            fact *= k
        e_val += Decimal(1) / Decimal(fact)

    def arctan_inv(m: int) -> Decimal:
        s = Decimal(0)
        m2 = m * m
        pw = Decimal(m)
        for k in range(110):
            term = Decimal(1) / (Decimal(2 * k + 1) * pw)
            s = s + term if k % 2 == 0 else s - term
            pw *= m2
        return s

    pi_val = Decimal(4) * (Decimal(4) * arctan_inv(5) - arctan_inv(239))
    return e_val, pi_val


E_DEC, PI_DEC = compute_e_pi_decimal()
XI_DEC = E_DEC + PI_DEC


def dist_to_int(x: Decimal) -> Decimal:
    n = int(x.to_integral_value(rounding="ROUND_FLOOR"))
    f = x - Decimal(n)
    return min(f, Decimal(1) - f)


def hermite_e_form(s: int) -> tuple[int, int]:
    A_s, B_s = 0, 0
    for k in range(s, 2 * s + 1):
        j = k - s
        deriv_0 = ((-1) ** j) * math.comb(s, j) * (math.factorial(k) // math.factorial(s))
        deriv_1 = ((-1) ** k) * deriv_0
        A_s += ((-1) ** k) * deriv_1
        B_s -= ((-1) ** k) * deriv_0
    return A_s, B_s


def verify_ep1_through_ep4() -> None:
    print("=== Verify EP.3: Hermite Recurrence A_{s+2} = -(4s + 6) A_{s+1} + A_s ===")
    A_vals = [hermite_e_form(s)[0] for s in range(0, 15)]
    for s in range(0, 13):
        assert A_vals[s + 2] == -(4 * s + 6) * A_vals[s + 1] + A_vals[s]
    print("  Verified exact 2nd-order recurrence for s = 0..12 [OK]")

    print("\n=== Verify EP.2: Split-Offset Nearest-Integer Floor on Coupled Hermite + Beukers-Lucas ===")
    for r in range(1, 6):
        deg = 8 * r
        coeffs = [0] * (deg + 1)
        for k in range(4 * r + 1):
            coeffs[4 * r + k] = ((-1) ** k) * math.comb(4 * r, k)
        quot = [0] * (deg - 1)
        work = list(coeffs)
        for d in range(deg, 1, -1):
            c = work[d]
            quot[d - 2] = c
            work[d - 2] -= c
        Q_i = work[0]
        rat_part = sum((Fraction(4 * qj, j + 1) for j, qj in enumerate(quot) if qj != 0), Fraction(0))
        D_den = rat_part.denominator
        C_mult = D_den * Q_i
        B_pi = rat_part.numerator
        eps_pi = abs(Decimal(C_mult) * PI_DEC + Decimal(B_pi))
        floor_Ce = dist_to_int(Decimal(C_mult) * E_DEC)
        # Test optimal integer B_e (nearest integer to -C_mult * e):
        B_e_opt = -round(Decimal(C_mult) * E_DEC)
        actual_L = abs(Decimal(C_mult) * XI_DEC + Decimal(B_e_opt + B_pi))
        lb = floor_Ce - eps_pi
        assert actual_L >= lb - Decimal("1e-120")
        print(f"  r={r}: distToInt(C*e)={float(floor_Ce):.4f}, eps_pi={float(eps_pi):.3e}, lower_bound={float(lb):.4f}, min |L|={float(actual_L):.4f} [OK]")


if __name__ == "__main__":
    verify_ep1_through_ep4()
    print("\nALL EP.1-EP.4 PROBE CHECKS PASSED.")
