"""
Wave 6 Sandbox: Exploring Bridge A (One Power Series, Two Universes R x Q_2)
and Bridge B (The Zero-Carry Base-2 / Base-3 Horner Transducer & Carry-Isolation Law)
====================================================================================

Bridge A (Dual-Universe Series F(2/3) = sum (2/3)^{T_j} in R x Q_2):
1. Lowest-Terms & Exact Weil Height Law (SB.28):
   At every surviving block K >= 0, consider the rational number
     Q_K = P_0 + sum_{j=1}^K (2/3)^{T_j} = (3^{T_K} * P_0 + A_{0, K}) / 3^{T_K} = (2^{T_{K+1}} * u_K) / 3^{T_K}.
   - Exact Coprimality (Lowest Terms):
       gcd(2^{T_{K+1}} * u_K, 3^{T_K}) == 1  and  gcd(3^{T_K} * P_0 + A_{0, K}, 3^{T_K}) == 1
     (because 3 * b_K + 1 = 2^{s_K} * u_K === 1 (mod 3), so 3 never divides u_K!).
   - Dual-Universe Uniqueness of P_0 in the Post-Bit-Length Regime (P_0 < 2^{T_{K+1}}):
     In R (Archimedean): P_0 = floor((2^{T_{K+1}} * u_K) / 3^{T_K}).
     In Q_2 (2-adic):    3^{T_K} * P_0 + A_{0, K} === 0 (mod 2^{T_{K+1}}), and for ANY
                         candidate P_0' < 2^{T_{K+1}} satisfying 3^{T_K} * P_0' + A_{0, K} === 0 (mod 2^{T_{K+1}}),
                         we have P_0' == P_0 identically!
   - Exact 2-adic Distance to -P_0:
     (3^{T_K} * P_0 + A_{0, K}) mod 2^{T_{K+1} + 1} == 2^{T_{K+1}} (v_2(3^{T_K} P_0 + A_{0, K}) == T_{K+1}).

Bridge B (Zero-Carry Base-2 / Base-3 Horner Transducer & Seed-Independent Step-Difference Law):
2. Seed-Independent Step-to-Step Base-3 Evolution Law (SB.29):
   For ANY seed b_0 and ANY block r >= 0 along a surviving chain (s_k >= 2):
     s_3(2^{T_{r+1}} * u_r) = s_3(P_0) + s_3(A_{0, r})
   and therefore across ANY two blocks r_1, r_2 >= 0:
     s_3(2^{T_{r_2+1}} * u_{r_2}) + s_3(A_{0, r_1}) == s_3(2^{T_{r_1+1}} * u_{r_1}) + s_3(A_{0, r_2})!
   In particular, the step-to-step Base-3 digit-sum change
     s_3(2^{T_{r+2}} * u_{r+1}) - s_3(2^{T_{r+1}} * u_r) == s_3(A_{0, r+1}) - s_3(A_{0, r})
   is 100% INDEPENDENT of the seed b_0 (and P_0) and depends ONLY on the step sizes (s_0, ..., s_r)!

3. Additive Carry-Isolation Law Across the Multi-Step Boundary (SB.30):
   For X = 2^{d + s_{r+1+M}} * u_{r+1+M} = 3^{s_r + d} * u_r + R (where R = 3^d + A'):
   Because 2^{s_r} * R = A_{r, r+1+M} < 3^{s_r + d} (by the 4/5 law SB.24!), EVEN AFTER multiplying
   both sides by 2^{s_r}, the remainder 2^{s_r} * R STILL never carries into 3^{s_r + d} * (2^{s_r} * u_r)!
   Therefore:
     s_3(2^{s_r} * X) + s_3(u_r) + s_3(R) == s_3(X) + s_3(2^{s_r} * u_r) + s_3(2^{s_r} * R)
   i.e., the Base-3 carry defect of multiplying X by 2^{s_r} splits with ZERO cross-talk into
   the carry defect on u_r plus the carry defect on R!
"""

import math

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
    r = len(s_list)
    total = 0
    for j in range(r):
        t_j = sum(s_list[:j+1])
        t_rem = sum(s_list[j+1:])
        total += (3 ** t_rem) * (1 << t_j)
    return total

def run_wave6_tests():
    verified_bridge_a = 0
    verified_bridge_b_diff = 0
    verified_bridge_b_isolation = 0

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

        # Test Bridge A & Bridge B (SB.28 & SB.29)
        prev_s3_val = None
        prev_s3_A = None
        for r in range(K_max + 1):
            T_r = sum(s_all[:r])
            T_r1 = sum(s_all[:r+1])
            A_0r = renewal_num(s_all[:r])
            u_r = u_all[r]
            num_r = (1 << T_r1) * u_r
            den_r = 3 ** T_r

            # Bridge A: Lowest terms & dual-universe recovery
            assert num_r == den_r * P0 + A_0r
            assert math.gcd(num_r, den_r) == 1
            assert num_r // den_r == P0
            assert (den_r * P0 + A_0r) % (1 << (T_r1 + 1)) == (1 << T_r1)
            verified_bridge_a += 1

            # Bridge B1: Seed-independent step-to-step Base-3 evolution
            cur_s3_val = s3(num_r)
            cur_s3_A = s3(A_0r)
            assert cur_s3_val == s3(P0) + cur_s3_A
            if prev_s3_val is not None:
                assert cur_s3_val - prev_s3_val == cur_s3_A - prev_s3_A
                verified_bridge_b_diff += 1
            prev_s3_val = cur_s3_val
            prev_s3_A = cur_s3_A

        # Test Bridge B2: Additive Carry-Isolation Law (SB.30)
        for r in range(K_max):
            s_r = s_all[r]
            u_r = u_all[r]
            for M in range(K_max - r):
                d = sum(s_all[r+1:r+1+M])
                S = d + s_all[r+1+M]
                u_end = u_all[r+1+M]
                A_inner = renewal_num(s_all[r+1:r+1+M])
                R = (3 ** d) + A_inner
                X = (1 << S) * u_end
                assert X == (3 ** (s_r + d)) * u_r + R
                # Multiply X by 2^{s_r}: since 2^{s_r} * R = A_{r, r+1+M} < 3^{s_r + d},
                # 2^{s_r} * R STILL never carries into 3^{s_r + d} * (2^{s_r} * u_r)!
                assert (1 << s_r) * R < 3 ** (s_r + d)
                assert s3((1 << s_r) * X) == s3((1 << s_r) * u_r) + s3((1 << s_r) * R)
                # Therefore, the carry defect of multiplying X by 2^{s_r} splits additively:
                assert (s3((1 << s_r) * X) - s3(X)) == (s3((1 << s_r) * u_r) - s3(u_r)) + (s3((1 << s_r) * R) - s3(R))
                verified_bridge_b_isolation += 1

    print(f"[Bridge A - SB.28] Verified Lowest-Terms & Dual R x Q_2 Uniqueness across {verified_bridge_a} blocks: 0 exceptions.")
    print(f"[Bridge B - SB.29] Verified Seed-Independent Base-3 Step-Difference Law across {verified_bridge_b_diff} transitions: 0 exceptions.")
    print(f"[Bridge B - SB.30] Verified Additive Carry-Isolation Law across {verified_bridge_b_isolation} windows: 0 exceptions.")

if __name__ == "__main__":
    run_wave6_tests()
