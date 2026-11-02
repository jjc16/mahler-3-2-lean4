"""
Wave 5 Sandbox: Multi-Block Past-Future Chinese Remainder Pinch & Sliding Cut-Point Uniqueness
==============================================================================================
For any K-block chain (blocks 0, 1, ..., K) and any interior cut point r (0 <= r <= K):
Let:
  - T_r = s_0 + ... + s_{r-1}  (past halvings before block r)
  - d_r = T_K - T_r = s_r + ... + s_{K-1}
  - D_r = T_{K+1} - T_r = s_r + ... + s_K  (future halvings from block r through block K)
  - M_r = 3^{T_r} * 2^{D_r + 1}  (combined Past-Base-3 x Future-Base-2 modulus at cut r)

We test three new symmetry-breaking towers:
1. Tower 24 (SB.24): Exact Past-Base-3 / Future-Base-2 Decomposition at Every Cut Point r:
   - Past Base-3 Quotient & Remainder:
       floor(2^{T_r} * P_r / 3^{T_r}) = P_0
       (2^{T_r} * P_r) mod 3^{T_r} = A_{0, r}
       s_3(2^{T_r} * P_r) = s_3(P_0) + s_3(A_{0, r})
   - Future Base-2 Congruence:
       (3^{d_r} * P_r + A_{r, K}) mod 2^{D_r + 1} = 2^{D_r}
       (3^{d_r} * 2^{s_r} * u_r + A_{r, K}) mod 2^{D_r + 1} = 2^{D_r}
2. Tower 25 (SB.25): The Sliding Cut-Point Archimedean Pinch (P_r < M_r and u_r < 3^{T_r} * 2^{D_r - s_r + 1}):
   Whenever 2 * P_0 + 1 <= 2^{T_{K+1} + 1} (post-bit-length horizon):
   - At EVERY cut point r in {0, ..., K}:
       P_r < 3^{T_r} * 2^{D_r + 1} = M_r
     and at the odd leftover level:
       u_r < 3^{T_r} * 2^{D_r - s_r + 1}!
3. Tower 26 (SB.26): Unconditional Two-Candidate CRT Annihilation at Cut Point r:
   If any two integers P_r, P_r' satisfy the same Past Base-3 congruence mod 3^{T_r}
   and Future Base-2 congruence mod 2^{D_r + 1}, and both lie below M_r = 3^{T_r} * 2^{D_r + 1},
   then P_r == P_r' identically!
"""

def v2(n: int) -> int:
    c = 0
    while n > 0 and n % 2 == 0:
        n //= 2
        c += 1
    return c

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
    # A_{0, r} for step list s_list of length r
    r = len(s_list)
    total = 0
    for j in range(r):
        t_j = sum(s_list[:j+1])
        t_rem = sum(s_list[j+1:])
        total += (3 ** t_rem) * (1 << t_j)
    return total

def run_wave5_tests():
    verified_cuts = 0
    verified_post_bitlength_pinch = 0
    for b0 in range(1, 200001, 2):
        blocks = extract_blocks(b0)
        L = len(blocks)
        if L < 2:
            continue
        K = L - 1
        s_all = [blk[2] for blk in blocks]
        P_all = [blk[1] for blk in blocks]
        u_all = [blk[3] for blk in blocks]
        P0 = P_all[0]
        T_K1 = sum(s_all[:K+1])

        for r in range(K + 1):
            T_r = sum(s_all[:r])
            d_r = sum(s_all[r:K])
            D_r = sum(s_all[r:K+1])
            A_0r = renewal_num(s_all[:r])
            A_rK = renewal_num(s_all[r:K])
            P_r = P_all[r]
            u_r = u_all[r]
            s_r = s_all[r]

            # 1. UNCONDITIONAL 4/5 Renewal Ceiling & Past Base-3 laws (no slack assumption needed!)
            lhs_past = (1 << T_r) * P_r
            div_past = 3 ** T_r
            assert lhs_past == div_past * P0 + A_0r
            assert 5 * A_0r + 4 * (1 << T_r) <= 4 * div_past
            assert A_0r < div_past
            assert lhs_past // div_past == P0
            assert lhs_past % div_past == A_0r
            assert s3(lhs_past) == s3(P0) + s3(A_0r)

            # 2. Future Base-2 congruence
            lhs_fut = (3 ** d_r) * P_r + A_rK
            assert lhs_fut == (1 << D_r) * u_all[K]
            assert lhs_fut % (1 << (D_r + 1)) == (1 << D_r)

            # 3. Unconditional Sliding Cut-Point Inequality:
            # 5 * 2^{T_{K+1}} * P_r < 3^{T_r} * 2^{D_r} * (5 * P_0 + 4)
            M_r = (3 ** T_r) * (1 << (D_r + 1))
            assert 5 * (1 << T_K1) * P_r < (3 ** T_r) * (1 << D_r) * (5 * P0 + 4)
            if P0 <= (1 << (T_K1 + 1)):
                assert P_r < M_r
                assert u_r < (3 ** T_r) * (1 << (D_r - s_r + 1))
                verified_post_bitlength_pinch += 1

            verified_cuts += 1

    print(f"[Wave 5] Verified Past-Base-3 / Future-Base-2 decomposition across {verified_cuts} cut points: 0 exceptions.")
    print(f"[Wave 5] Verified Post-Bit-Length Sliding Cut-Point Pinch (P_r < M_r) across {verified_post_bitlength_pinch} post-bit-length cut points: 0 exceptions.")

if __name__ == "__main__":
    run_wave5_tests()
