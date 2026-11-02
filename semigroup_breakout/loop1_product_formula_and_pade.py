"""
Semigroup Breakout — Loop 1:
Testing the Exact Atomic Skeleton of Mahler's 3/2 Problem,
Post-Horizon Survival of Minimal 2-Adic Seeds, and Beukers/FLP Padé Approximants.
"""

import math
from fractions import Fraction


def compute_kneading_blocks(num_blocks: int = 54):
    """Compute the unique sub-ceiling kneading sequence kappa_0 .. kappa_{num_blocks-1}."""
    T = 2
    S = 1  # after s_0 = 2
    blocks = [2]
    states = [(2, 1, -3)]  # (T_1, S_1, C_1)
    for k in range(1, num_blocks):
        s = 2
        while True:
            nextS = (3 ** s) * S - 2 * (2 ** (T + s))
            nextC = (3 ** s) * S - 3 * (2 ** (T + s))
            if nextS > 0 and nextC < 0:
                T += s
                S = nextS
                blocks.append(s)
                states.append((T, S, nextC))
                break
            s += 1
    return blocks, states


def renewal_numerator(blocks):
    """Compute A_{0, N} and T_N for a list of block lengths."""
    T = 0
    A = 0
    for s in blocks:
        T += s
        A = (3 ** s) * A + (2 ** T)
    return T, A


def minimal_odd_seed_for_blocks(blocks):
    """
    Find the unique smallest positive odd integer b_0 in (0, 2^{T_N + 1})
    realizing the block sequence `blocks`, i.e.,
      2^{T_N} | (3^{T_N} P_0 + A_{0,N}) and 2^{T_N + 1} | (3^{T_N} P_0 + A_{0,N})
    with P_0 = 3 b_0 + 1 == 4 (mod 6).
    Wait: at step N, for b_0 to realize s_0, ..., s_{N-1}, we need:
      For each k < N, v_2(P_k) = s_k, which is equivalent to
      3^{T_N} P_0 + A_{0,N} == 2^{T_N} (mod 2^{T_N + 1})!
      Wait: in ExtraBitBackwardPropagationAndKneading15.lean, we proved that if
      2^{T_N + 1} | (3^{T_N} P_0 + A_{0,N}), then for ALL k < N, v_2(P_k) = s_k,
      AND at step N itself, 2 | P_N (so s_N >= 1)!
      Even better: if we want P_{N-1} to have exact valuation s_{N-1} (so P_N is odd),
      then 3^{T_N} P_0 + A_{0,N} = 2^{T_N} P_N with P_N odd, which means:
      3^{T_N} P_0 + A_{0,N} == 2^{T_N} (mod 2^{T_N + 1})!
    """
    T_N, A_N = renewal_numerator(blocks)
    mod = 1 << (T_N + 1)
    # Since b_N is odd, P_N = 3 b_N + 1 is even, so 2^{T_N + 1} | (3^{T_N} P_0 + A_N).
    # Choose the smallest odd seed b_0 in (0, 2^{T_N + 1}) satisfying
    # 3^{T_N} (3 b_0 + 1) + A_N == 2^{T_N + 1} (mod 2^{T_N + 2}) so P_N is odd*2 or any valid lift:
    # Actually, any solution to 3^{T_N} (3 b_0 + 1) + A_N == 0 (mod 2^{T_N + 1})
    # automatically realizes s_0 .. s_{N-1} by `extra_bit_congruence_propagates_to_all_prefixes`!
    rhs = (-A_N - (3 ** T_N)) % mod
    inv3 = pow(3, -1, mod)
    inv_pow3 = pow(inv3, T_N + 1, mod)
    b0 = (rhs * inv_pow3) % mod
    if b0 == 0:
        b0 += mod
    return b0, T_N, A_N


def trace_post_horizon_survival(b0: int, max_blocks: int = 200):
    """
    Given an odd seed b0, trace its actual Mahler odd-block sequence:
      3 * b_k + 1 = 2^{s_k} * u_k  (u_k odd)
      b_{k+1} = 3^{s_k - 1} * u_k
    and find the exact block k and binary step T_k where either:
      1. s_k == 1 (odd-to-odd step, immediate death), or
      2. renewalIntSlack <= 0 (archimedean companion interval becomes empty).
    """
    b = b0
    T = 0
    S = 1  # renewalIntSlack_0 = 1
    blocks = []
    for k in range(max_blocks):
        val = 3 * b + 1
        s = (val & -val).bit_length() - 1
        u = val >> s
        blocks.append(s)
        nextS = (3 ** s) * S - 2 * (1 << (T + s))
        T += s
        S = nextS
        b = (3 ** (s - 1)) * u
        if s == 1:
            return k + 1, T, "s_k = 1 (odd-to-odd death)", blocks
        if S <= 0:
            return k + 1, T, f"Slack S_{k+1} <= 0 (Parry-Mahler pinch death at s_{k}={s})", blocks
    return max_blocks, T, "survived max_blocks", blocks


def main():
    kneading_blocks, _ = compute_kneading_blocks(30)
    print("=== LOOP 1A: Post-Horizon Free-Fall of Minimal Engineered Seeds ===")
    print(f"{'N':>3} | {'T_N':>4} | {'bitlen(b0)':>10} | {'DieBlk':>6} | {'DieStep':>7} | {'ExtraSteps':>10} | {'Death Reason'}")
    print("-" * 88)
    extra_steps_list = []
    for N in range(1, 26):
        prefix = kneading_blocks[:N]
        b0, T_N, _ = minimal_odd_seed_for_blocks(prefix)
        die_blk, die_step, reason, actual_blocks = trace_post_horizon_survival(b0)
        assert actual_blocks[:N] == prefix, f"Mismatch at N={N}: {actual_blocks[:N]} != {prefix}"
        extra = die_step - T_N
        extra_steps_list.append(extra)
        print(f"{N:>3} | {T_N:>4} | {b0.bit_length():>10} | {die_blk:>6} | {die_step:>7} | {extra:>10} | {reason}")
    print(f"\nAverage extra binary steps past engineered horizon T_N: {sum(extra_steps_list)/len(extra_steps_list):.2f}")
    print(f"Max extra binary steps past engineered horizon T_N: {max(extra_steps_list)}")


if __name__ == "__main__":
    main()
