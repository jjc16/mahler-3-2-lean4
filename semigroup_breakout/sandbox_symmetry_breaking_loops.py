"""
Unconstrained Mathematical Sandbox (Loops 1 to 5 — NO Bottom-Up Lean Filter):
Exploring deep combinations of the Z_2-symmetry-breaking functionals:
  - s_2(n): binary Hamming weight (number of 1-bits in base 2)
  - s_3(n): ternary digit sum (sum of trits in base 3)
  - C_2(a, b): number of binary carries when adding a + b
  - C_3(a, b): number of ternary carries when adding a + b
  - v_2(n!), v_3(n!): Legendre p-adic factorial valuations

Goal: Find exact multi-step relationships and top-down conditional bridges that
connect s_2(u_r) and s_3(u_r) to the Mahler survival inequalities!
"""

from loop1_product_formula_and_pade import compute_kneading_blocks, minimal_odd_seed_for_blocks
from loop2_pade_lll_and_divergence import binary_orbit_trace


def s2(n: int) -> int:
    return n.bit_count()


def s3(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total


def base3_digits_lsb(n: int):
    """Return base-3 digits from LSB (position 0) to MSB."""
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits


def count_carries(a: int, b: int, base: int) -> int:
    """Count the exact number of carries when adding a + b in `base`."""
    carries = 0
    c = 0
    while a > 0 or b > 0 or c > 0:
        da = a % base
        db = b % base
        c = (da + db + c) // base
        carries += c
        a //= base
        b //= base
    return carries


def sandbox_loop1_legendre_carry_duality():
    """
    SANDBOX LOOP 1:
    In any base p, Kummer's / Legendre's theorem states:
      s_p(a + b) = s_p(a) + s_p(b) - (p - 1) * C_p(a, b).
    Let's apply this to BOTH halves of the Mahler step!
    1. In Base 2 (p = 2, p - 1 = 1):
       At an odd step, P_r = 3 b_r + 1 = (2 b_r + 1) + b_r = 2^{s_r} u_r.
       Notice that 2 b_r + 1 in binary is just b_r shifted left by 1 with a '1' appended at bit 0!
       So s_2(2 b_r + 1) = s_2(b_r) + 1!
       Therefore, adding (2 b_r + 1) + b_r gives:
         s_2(u_r) = s_2(P_r) = s_2(2 b_r + 1) + s_2(b_r) - C_2(2 b_r + 1, b_r)
                  = 2 * s_2(b_r) + 1 - C_2(2 b_r + 1, b_r)!!
    2. Even better: what about the RAW binary step 2 g_{k+1} = 3 g_k + eps_k = (2 g_k + eps_k) + g_k?!
       Since s_2(2 g_{k+1}) = s_2(g_{k+1}) and s_2(2 g_k + eps_k) = s_2(g_k) + eps_k:
         s_2(g_{k+1}) = 2 * s_2(g_k) + eps_k - C_2(2 g_k + eps_k, g_k)!!
    3. Now look at Base 3 (p = 3, p - 1 = 2) on the RAW binary step:
       We know 2 g_{k+1} = g_{k+1} + g_{k+1} = 3 g_k + eps_k!
       In Base 3, what is s_3(3 g_k + eps_k)?
       Since eps_k in {0, 1} < 3, s_3(3 g_k + eps_k) = s_3(g_k) + eps_k (ZERO base-3 carries on the RHS!)!
       And what is s_3(2 g_{k+1}) = s_3(g_{k+1} + g_{k+1}) in Base 3 by Kummer's theorem?!
         s_3(2 g_{k+1}) = 2 * s_3(g_{k+1}) - 2 * C_3(g_{k+1}, g_{k+1})!!
       EQUATE THE TWO SIDES OF 2 g_{k+1} = 3 g_k + eps_k IN BASE 3:
         2 * s_3(g_{k+1}) - 2 * C_3(g_{k+1}, g_{k+1}) = s_3(g_k) + eps_k!!
    """
    print("=== SANDBOX LOOP 1: Kummer-Legendre Carry Laws in Base 2 AND Base 3 ===")
    g0 = 8101
    g, eps = binary_orbit_trace(g0, 30)
    for k in range(30):
        # Base 2 exact step law:
        c2 = count_carries(2 * g[k] + eps[k], g[k], 2)
        assert s2(g[k + 1]) == 2 * s2(g[k]) + eps[k] - c2

        # Base 3 exact step law on 2 * g_{k+1} = 3 * g_k + eps_k:
        c3 = count_carries(g[k + 1], g[k + 1], 3)
        assert 2 * s3(g[k + 1]) - 2 * c3 == s3(g[k]) + eps[k]

    print("  [DISCOVERY 1A — Base-2 Step Law]:")
    print("    s_2(g_{k+1}) = 2 * s_2(g_k) + eps_k - C_2(2 g_k + eps_k, g_k)")
    print("  [DISCOVERY 1B — Base-3 Step Law]:")
    print("    2 * s_3(g_{k+1}) - s_3(g_k) = eps_k + 2 * C_3(g_{k+1}, g_{k+1})")
    print("  Notice what Discovery 1B says modulo 2:")
    print("    s_3(g_k) == eps_k (mod 2)  (since 2*s_3(g_{k+1}) - 2*C_3 is even!)")


def sandbox_loop2_base3_doubling_anatomy():
    """
    SANDBOX LOOP 2:
    Look closely at Discovery 1B:
      2 * s_3(g_{k+1}) - s_3(g_k) = eps_k + 2 * C_3(g_{k+1}, g_{k+1})
    Wait: what if we apply Kummer's theorem in Base 3 to:
      2^N * g_N = 3^N * g_0 + K_N?!
    We ALREADY proved in Theorem SB.9 that on the RHS:
      s_3(3^N * g_0 + K_N) = s_3(g_0) + s_3(K_N)!
    Now what is the LHS s_3(2^N * g_N) when we double g_N N times:
      x_0 = g_N,  x_1 = 2 g_N,  x_2 = 4 g_N, ...,  x_N = 2^N g_N?!
    At each doubling x_{j+1} = 2 x_j = x_j + x_j:
      s_3(2 x_j) = 2 * s_3(x_j) - 2 * C_3(x_j, x_j)!
    Wait: what if instead we telescope Discovery 1B:
      2 * s_3(g_{k+1}) - s_3(g_k) = eps_k + 2 * C_3(g_{k+1}, g_{k+1})
    across k = 0, 1, ..., N - 1 with weights 2^k?!
    HOLD EVERYTHING!!
    Multiply 2 * s_3(g_{k+1}) - s_3(g_k) = eps_k + 2 * C_3(g_{k+1}, g_{k+1}) by 2^k and sum from k=0 to N-1!
    The LHS telescopes IDENTICALLY:
      sum_{k=0}^{N-1} 2^k (2 * s_3(g_{k+1}) - s_3(g_k)) = 2^N * s_3(g_N) - s_3(g_0)!!
    And what is the RHS?!
      sum_{k=0}^{N-1} 2^k * eps_k + 2 * sum_{k=0}^{N-1} 2^k * C_3(g_{k+1}, g_{k+1})!!
    """
    print("\n=== SANDBOX LOOP 2: The Exact 2^k-Weighted Base-3 Telescoping Identity! ===")
    g0 = 8101
    g, eps = binary_orbit_trace(g0, 25)
    for N in [1, 5, 10, 15, 20, 25]:
        lhs = (1 << N) * s3(g[N]) - s3(g0)
        eps_binary_int = sum((1 << k) * eps[k] for k in range(N))
        carry_sum = sum((1 << (k + 1)) * count_carries(g[k + 1], g[k + 1], 3) for k in range(N))
        assert lhs == eps_binary_int + carry_sum
        print(f"  N={N:>2}: 2^N*s_3(g_N) - s_3(g_0) = {lhs:>10} == "
              f"eps_int ({eps_binary_int:>8}) + 2*sum 2^k C_3 ({carry_sum:>10})")


def sandbox_loop3_compare_two_s3_identities():
    """
    SANDBOX LOOP 3:
    WAIT A SECOND!! Look at what we now have at step N:
    Identity A (from 2^N g_N = 3^N g_0 + K_N in Theorem SB.9):
      s_3(2^N * g_N) = s_3(g_0) + s_3(K_N)
    Identity B (from telescoping 2 g_{k+1} = 3 g_k + eps_k in Sandbox Loop 2):
      2^N * s_3(g_N) = s_3(g_0) + sum_{k=0}^{N-1} 2^k eps_k + 2 * sum_{k=0}^{N-1} 2^k C_3(g_{k+1}, g_{k+1})
    Identity C (also in Base 2, telescoping s_2(g_{k+1}) = 2 s_2(g_k) + eps_k - C_2):
      Multiply s_2(g_k) by 2^{N-1-k}:
      2^N * s_2(g_0) - s_2(g_N) = sum_{k=0}^{N-1} 2^{N-1-k} (C_2(2 g_k + eps_k, g_k) - eps_k)!
    Let's verify Identity C as well!
    """
    print("\n=== SANDBOX LOOP 3: Dual Exponential Telescoping of s_2(g_k) and s_3(g_k) ===")
    g0 = 8101
    g, eps = binary_orbit_trace(g0, 25)
    for N in [5, 10, 15, 20, 25]:
        lhs_s2 = s2(g[N]) - (1 << N) * s2(g0)
        rhs_s2 = sum((1 << (N - 1 - k)) * (eps[k] - count_carries(2 * g[k] + eps[k], g[k], 2)) for k in range(N))
        assert lhs_s2 == rhs_s2
        print(f"  N={N:>2}: s_2(g_N) = {s2(g[N]):>2}, s_3(g_N) = {s3(g[N]):>2}, s_3(K_N) = {s3((1<<N)*g[N] - (3**N)*g0):>2}")


def sandbox_loop4_lower_bound_on_s3_K_N():
    """
    SANDBOX LOOP 4:
    Look at s_3(K_N) where K_N = sum_{k=0}^{N-1} 3^{N-1-k} 2^k eps_k.
    At step N, let's see how s_3(K_N) grows along ANY surviving orbit!
    Wait: can K_N EVER be 0 for N >= 1 if g_0 is a surviving seed?
    Only if eps_0 = eps_1 = ... = eps_{N-1} = 0, which means 2^N | g_0 (so N <= log_2 g_0)!
    Once N > log_2 g_0 (post-bit-length!), there MUST be at least one odd step eps_k = 1, so K_N >= 1
    and s_3(K_N) >= 1!
    Even better: at EVERY block r (where eps_{T_r} = 1), what happens to K_{T_{r+1}}?
    Remember:
      K_{T_r + 1} = 3 * K_{T_r} + 2^{T_r},
      and for the s_r - 1 even steps inside block r:
      K_{T_{r+1}} = 3^{s_r - 1} * (3 * K_{T_r} + 2^{T_r})!
    So across the ENTIRE block r, s_3(K_n) changes ONLY ONCE (at the odd step T_r, where we add 2^{T_r} to 3 * K_{T_r})!
    Let's check:
      s_3(K_{T_{r+1}}) = s_3(3 * K_{T_r} + 2^{T_r})
                       = s_3(K_{T_r}) + s_3(2^{T_r}) - 2 * C_3(3 * K_{T_r}, 2^{T_r})!!
    """
    print("\n=== SANDBOX LOOP 4: Block-Level Base-3 Carry Formula for s_3(K_{T_r}) ===")
    g0 = 8101
    g, eps = binary_orbit_trace(g0, 35)
    K = 0
    for n in range(30):
        K_next = 3 * K + (1 << n) * eps[n]
        if eps[n] == 0:
            assert s3(K_next) == s3(K)
        else:
            c3 = count_carries(3 * K, 1 << n, 3)
            assert s3(K_next) == s3(K) + s3(1 << n) - 2 * c3
            print(f"  Odd step n={n:>2}: s_3(K_{{n+1}}) = {s3(K_next):>2} == s_3(K_n) ({s3(K):>2}) + s_3(2^n) ({s3(1<<n):>2}) - 2*C_3 ({2*c3:>2})")
        K = K_next


def sandbox_loop5_bridge_to_stewart_senge_straus():
    """
    SANDBOX LOOP 5 (Top-Down Blueprint Synthesis):
    Look at what we can prove as a TOP-DOWN CONDITIONAL / BLUEPRINT THEOREM:
    In analytic number theory, Senge-Straus (1973) and Stewart (1980) proved that for any fixed integer g_0 >= 1:
      lim_{N -> infty} (s_2(x_N) + s_3(x_N)) = infty.
    More specifically, in our Zero-Carry Base-3 Identity (Theorem SB.9):
      s_3(2^N * g_N) = s_3(g_0) + s_3(K_N).
    Therefore:
      s_3(K_N) <= M (bounded base-3 digit sum of the kernel K_N)
      <=> s_3(2^N * g_N) <= s_3(g_0) + M (bounded base-3 digit sum of 2^N * g_N)!
    AND what if s_3(2^N * g_N) is bounded (or what if s_3(u_r) is bounded)?
    Remember in Theorem SB.12:
      s_3(b_{r+1}) = s_3(u_r)  and  s_3(P_{r+1}) = s_3(2^{s_{r+1}} u_{r+1}) = s_3(u_r) + 1!
    Wait: look at s_2(P_r) = s_2(u_r) and s_3(P_{r+1}) = s_3(u_r) + 1:
      At EVERY block r:
        s_2(P_r) + s_3(P_{r+1}) = s_2(u_r) + s_3(u_r) + 1!!
    HOLD ON!! Read that identity again:
      s_2(P_r) + s_3(P_{r+1}) = s_2(u_r) + s_3(u_r) + 1!!
    Because P_r = 2^{s_r} u_r (pure power of 2 times u_r) and P_{r+1} - 1 = 3^{s_r} u_r (pure power of 3 times u_r),
    the SINGLE odd integer u_r simultaneously controls the Base-2 weight of P_r AND the Base-3 weight of P_{r+1}:
      s_2(u_r) = s_2(P_r),   and   s_3(u_r) = s_3(b_{r+1}) = s_3(P_{r+1}) - 1!!
    """
    print("\n=== SANDBOX LOOP 5: The Joint (s_2, s_3) Senge-Straus / Stewart Bridge ===")
    print("  For EVERY block r >= 0:")
    print("    s_2(u_r) = s_2(P_r)")
    print("    s_3(u_r) = s_3(b_{r+1}) = s_3(P_{r+1}) - 1")
    print("    s_2(P_r) + s_3(P_{r+1}) = s_2(u_r) + s_3(u_r) + 1!")


if __name__ == "__main__":
    sandbox_loop1_legendre_carry_duality()
    sandbox_loop2_base3_doubling_anatomy()
    sandbox_loop3_compare_two_s3_identities()
    sandbox_loop4_lower_bound_on_s3_K_N()
    sandbox_loop5_bridge_to_stewart_senge_straus()
