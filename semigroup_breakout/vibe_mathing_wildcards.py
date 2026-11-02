"""
Vibe-Mathing Expedition — Testing All Three Wildcards:
1. Wildcard 1 (Exponential Density-Zero):
   Verify that out of the 4^m seeds in [0, 4^m), at most 3^m avoid double-odd steps (1, 1) at even positions,
   and compare with the Fibonacci bound F_{T+2} and actual Parry-Mahler survivor counts.
2. Wildcard 2 (Base-3 Frozen Top Digits):
   Verify that for every surviving seed g_0 and every step N:
     floor(2^N * g_N / 3^N) == g_0,
     (2^N * g_N) mod 3^N == K_N < 3^N / 2,
     and the (N-1)-st base-3 digit of 2^N * g_N is in {0, 1} (NEVER 2!).
3. Wildcard 3 (The Mahler-Antihydra BB(6) Exact Complement Duality & Closed Modular Counter):
   Verify that for Antihydra's map a_{k+1} = floor(3 * a_k / 2) starting at a_0 = 8
   and Mahler's map g_{k+1} = ceil(3 * g_k / 2) starting at b_0 = 2^N - 8:
     g_k(2^N - a_0) + a_k(a_0) == 3^k * 2^{N - k}  for all 0 <= k <= N,
     and g_k(2^N - a_0) % 2 == a_k(a_0) % 2        for all 0 <= k < N!
"""

from loop2_pade_lll_and_divergence import companion_interval, binary_orbit_trace


def antihydra_orbit_trace(a0: int, steps: int):
    """Trace Antihydra's floor map a_{k+1} = (3 * a_k) // 2 and parities a_k % 2."""
    a = [a0]
    eps = []
    cur = a0
    for _ in range(steps):
        eps.append(cur % 2)
        cur = (3 * cur) // 2
        a.append(cur)
    return a, eps


def to_base3_digits(n: int):
    """Return base-3 digits of n from most significant to least significant."""
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return list(reversed(digits))


def test_wildcard1_density_zero():
    print("=== WILDCARD 1: Exponential Density-Zero in Dyadic Boxes [0, 4^m) ===")
    print(f"{'m':>2} | {'2m':>3} | {'Box 4^m':>8} | {'No-(1,1) 3^m':>12} | {'Fibonacci F_{2m+2}':>18} | {'Actual Survivors':>16} | {'Actual / 4^m':>12}")
    print("-" * 92)
    fib = [0, 1]
    for _ in range(30):
        fib.append(fib[-1] + fib[-2])
    for m in range(1, 8):
        T = 2 * m
        box = 4 ** m
        three_m = 3 ** m
        fib_bound = fib[T + 2]
        surv = 0
        no_pair_11 = 0
        for b0 in range(box):
            _, eps = binary_orbit_trace(b0, T)
            if all(not (eps[2 * j] == 1 and eps[2 * j + 1] == 1) for j in range(m)):
                no_pair_11 += 1
            L, U = companion_interval(b0, T)
            if L < U:
                surv += 1
        assert no_pair_11 == three_m, f"Expected {three_m}, got {no_pair_11}"
        assert surv <= fib_bound <= three_m
        print(f"{m:>2} | {T:>3} | {box:>8} | {three_m:>12} | {fib_bound:>18} | {surv:>16} | {surv / box:>12.6f}")


def test_wildcard2_base3_frozen_prefix():
    print("\n=== WILDCARD 2: Base-3 'Frozen Top Digits' of 2^N * g_N ===")
    # Take champion seed b0 = 8101 (which survives 38 steps)
    b0 = 8101
    b0_b3 = "".join(str(d) for d in to_base3_digits(b0))
    print(f"Seed g_0 = {b0} has base-3 expansion: {b0_b3}_3 (length {len(b0_b3)} trits)")
    g, eps = binary_orbit_trace(b0, 30)
    for N in [1, 5, 10, 15, 20, 25, 30]:
        val = (2 ** N) * g[N]
        quot = val // (3 ** N)
        rem = val % (3 ** N)
        lead_trit = rem // (3 ** (N - 1))
        b3_str = "".join(str(d) for d in to_base3_digits(val))
        prefix_str = b3_str[:-N]
        tail_str = b3_str[-N:]
        assert quot == b0 and 2 * rem < (3 ** N) and lead_trit in (0, 1)
        print(f"  N={N:>2}: 2^N*g_N in base 3 = [{prefix_str}] . [{tail_str[0]}]{tail_str[1:]}_3 "
              f"(top prefix == {quot} == g_0, next trit = {lead_trit} in {{0,1}})")


def test_wildcard3_mahler_antihydra_duality():
    print("\n=== WILDCARD 3: Exact Mahler-Antihydra BB(6) Complement Duality ===")
    a0 = 8  # Antihydra starting value
    N = 20
    b0 = (1 << N) - a0
    g_mahler, eps_mahler = binary_orbit_trace(b0, N)
    a_anti, eps_anti = antihydra_orbit_trace(a0, N)
    print(f"Antihydra seed a_0 = {a0}, Horizon N = {N}, Dual Mahler seed b_0 = 2^{N} - {a0} = {b0}")
    for k in range(N + 1):
        assert g_mahler[k] + a_anti[k] == (3 ** k) * (1 << (N - k))
        if k < N:
            assert eps_mahler[k] == eps_anti[k]
    print(f"  Verified for ALL 0 <= k <= {N}:")
    print(f"    mahlerOrbit(2^N - a_0, k) + antihydraOrbit(a_0, k) == 3^k * 2^(N - k)")
    print(f"    mahlerOrbit(2^N - a_0, k) % 2 == antihydraOrbit(a_0, k) % 2  for all k < {N}!")
    print(f"  First 15 Antihydra states (a_0=8): {a_anti[:15]}")
    print(f"  First 15 shared parities:          {eps_anti[:15]}")


if __name__ == "__main__":
    test_wildcard1_density_zero()
    test_wildcard2_base3_frozen_prefix()
    test_wildcard3_mahler_antihydra_duality()
