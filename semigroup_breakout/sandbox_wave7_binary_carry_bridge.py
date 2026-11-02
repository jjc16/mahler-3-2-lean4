"""
Wave 7 Sandbox (Bridge C): The Binary Carry-Depletion & Halving-Budget Bridge
=============================================================================
Looking one more time at the middle of the canyon revealed the missing BASE-2 counterpart
to our Base-3 Zero-Carry Firewall (SB.24-SB.30):

1. Tower 31 (SB.31): One-Step Binary Trailing-Ones Depletion Law:
   At every block r, since 3^{s_r} * u_r + 1 = 2^{s_{r+1}} * u_{r+1} and u_{r+1} is odd:
     3^{s_r} * u_r = 2^{s_{r+1}} * (u_{r+1} - 1) + (2^{s_{r+1}} - 1).
   In Base 2, the bottom s_{r+1} bits of 3^{s_r} * u_r are ALL ONES (2^{s_{r+1}} - 1, digit sum s_{r+1}),
   and the bits above 2^{s_{r+1}} are u_{r+1} - 1 (digit sum s_2(u_{r+1}) - 1, since u_{r+1} is odd).
   Therefore, with ZERO Base-2 overlap:
     - (3^{s_r} * u_r) // 2^{s_{r+1}} == u_{r+1} - 1
     - (3^{s_r} * u_r) %  2^{s_{r+1}} == 2^{s_{r+1}} - 1
     - s_2(3^{s_r} * u_r) + 1 == s_2(u_{r+1}) + s_{r+1}!

2. Tower 32 (SB.32): Multi-Step Dual Base-2 / Base-3 Zero-Carry Split of N_K = 3^{T_K} P_0 + A_{0, K}:
   For N_K = 3^{T_K} * P_0 + A_{0, K} = 2^{T_{K+1}} * u_K:
   - In Base 3 (SB.24):
       N_K = 3^{T_K} * P_0 + A_{0, K}  -->  s_3(N_K) = s_3(P_0) + s_3(A_{0, K}).
   - In Base 2 (Bridge C):
       N_K - 1 = 2^{T_{K+1}} * (u_K - 1) + (2^{T_{K+1}} - 1)
       (N_K - 1) // 2^{T_{K+1}} == u_K - 1
       (N_K - 1) %  2^{T_{K+1}} == 2^{T_{K+1}} - 1
       s_2(N_K - 1) + 1 == T_{K+1} + s_2(u_K)
     And when blocks K+1 survives (s_{K+1} >= 2, so s_2(u_K) >= 2 by SB.18):
       s_2(N_K - 1) >= T_{K+1} + 1!

3. Tower 33 (SB.33): The Telescoped Binary Halving-Budget Law:
   Across any K blocks, every halving step s_{r+1} is paid for out of the binary 1-bits
   manufactured by multiplying u_r by 3^{s_r}:
     (T_{K+1} - s_0) + s_2(u_K) == s_2(u_0) + K + sum_{r=0}^{K-1} (s_2(3^{s_r} * u_r) - s_2(u_r))!
"""

def v2(n: int) -> int:
    c = 0
    while n > 0 and n % 2 == 0:
        n //= 2
        c += 1
    return c

def s2(n: int) -> int:
    return bin(n).count("1")

def s3(n: int) -> int:
    total = 0
    while n > 0:
        total += n % 3
        n //= 3
    return total

def extract_blocks(b0: int):
    blocks = []
    b = b0
    while True:
        P = 3 * b + 1
        s = v2(P)
        u = P >> s
        blocks.append((b, P, s, u))
        if s == 1:
            break
        b = (3 ** (s - 1)) * u
    return blocks

def renewal_num(s_list):
    r = len(s_list)
    total = 0
    for j in range(r):
        t_j = sum(s_list[:j+1])
        t_rem = sum(s_list[j+1:])
        total += (3 ** t_rem) * (1 << t_j)
    return total

def run_wave7_tests():
    verified_one_step = 0
    verified_multi_step = 0
    verified_budget = 0

    for b0 in range(1, 200001, 2):
        blocks = extract_blocks(b0)
        L = len(blocks)
        if L < 2:
            continue
        K_max = L - 1
        s_all = [blk[2] for blk in blocks]
        P_all = [blk[1] for blk in blocks]
        u_all = [blk[3] for blk in blocks]
        P0 = P_all[0]

        # 1. One-step binary trailing-ones depletion law (SB.31)
        for r in range(K_max):
            s_r = s_all[r]
            u_r = u_all[r]
            s_next = s_all[r + 1]
            u_next = u_all[r + 1]
            val = (3 ** s_r) * u_r
            assert val == (1 << s_next) * (u_next - 1) + ((1 << s_next) - 1)
            assert val // (1 << s_next) == u_next - 1
            assert val % (1 << s_next) == (1 << s_next) - 1
            assert s2(val) + 1 == s2(u_next) + s_next
            verified_one_step += 1

        # 2. Multi-step Dual Base-2 / Base-3 Zero-Carry Split of N_K (SB.32)
        for K in range(K_max + 1):
            T_K = sum(s_all[:K])
            T_K1 = sum(s_all[:K+1])
            A_0K = renewal_num(s_all[:K])
            u_K = u_all[K]
            N_K = (3 ** T_K) * P0 + A_0K
            assert N_K == (1 << T_K1) * u_K
            # Base-3 split of N_K
            assert s3(N_K) == s3(P0) + s3(A_0K)
            # Base-2 split of N_K - 1
            assert N_K - 1 == (1 << T_K1) * (u_K - 1) + ((1 << T_K1) - 1)
            assert (N_K - 1) // (1 << T_K1) == u_K - 1
            assert (N_K - 1) % (1 << T_K1) == (1 << T_K1) - 1
            assert s2(N_K - 1) + 1 == T_K1 + s2(u_K)
            if K < K_max and s_all[K + 1] >= 2:
                assert s2(N_K - 1) >= T_K1 + 1
            verified_multi_step += 1

        # 3. Telescoped Binary Halving-Budget Law (SB.33)
        for K in range(1, K_max + 1):
            T_K1 = sum(s_all[:K+1])
            s0 = s_all[0]
            u0 = u_all[0]
            uK = u_all[K]
            lhs = (T_K1 - s0) + s2(uK)
            rhs = s2(u0) + K + sum(s2((3 ** s_all[r]) * u_all[r]) - s2(u_all[r]) for r in range(K))
            assert lhs == rhs
            verified_budget += 1

    print(f"[Bridge C - SB.31] Verified One-Step Binary Trailing-Ones Depletion Law across {verified_one_step} blocks: 0 exceptions.")
    print(f"[Bridge C - SB.32] Verified Multi-Step Dual Base-2/Base-3 Zero-Carry Split of N_K across {verified_multi_step} horizons: 0 exceptions.")
    print(f"[Bridge C - SB.33] Verified Telescoped Binary Halving-Budget Law across {verified_budget} chains: 0 exceptions.")

if __name__ == "__main__":
    run_wave7_tests()
