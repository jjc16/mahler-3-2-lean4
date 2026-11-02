"""
Wave 4 Canyon-View Sandbox:
Testing what is visible from the top of Towers 18-20:
1. Two-Step Disjoint Base-3 Digit-Block Law:
     2^{s_{r+1} + s_{r+2}} * u_{r+2} = 3^{s_r + s_{r+1}} * u_r + 3^{s_{r+1}} + 2^{s_{r+1}}
   Because 2^{s_{r+1}} < 3^{s_{r+1}} and s_r >= 1, the three terms occupy
   COMPLETELY DISJOINT Base-3 digit ranges:
     - [0, s_{r+1}-1]: Base-3 digits of 2^{s_{r+1}}
     - [s_{r+1}]: single trit '1' from 3^{s_{r+1}}
     - [s_{r+1}+1, s_r+s_{r+1}-1]: all '0' trits!
     - [s_r+s_{r+1}, infinity): Base-3 digits of u_r
   Therefore, with ZERO Base-3 carries:
     s_3(2^{s_{r+1} + s_{r+2}} * u_{r+2}) = s_3(u_r) + 1 + s_3(2^{s_{r+1}}).
2. Two-Step Backward Exact Quotient & Remainder:
     floor(2^{s_{r+1} + s_{r+2}} * u_{r+2} / 3^{s_r + s_{r+1}}) = u_r
     (2^{s_{r+1} + s_{r+2}} * u_{r+2}) mod 3^{s_r + s_{r+1}} = 3^{s_{r+1}} + 2^{s_{r+1}}
   whenever s_r >= 2.
3. Two-Sided Past-Future CRT Lock on u_r:
   At every interior surviving block r >= 1 (with s_{r-1} >= 2, s_r >= 2, s_{r+1} >= 2):
     - Past lock (mod 3^{s_{r-1}}): 2^{s_r} * u_r === 1 (mod 3^{s_{r-1}})
     - Future lock (mod 2^{s_{r+1}+1}): 3^{s_r} * u_r === 2^{s_{r+1}} - 1 (mod 2^{s_{r+1}+1})
   Since gcd(3^{s_{r-1}}, 2^{s_{r+1}+1}) = 1, u_r is locked into a UNIQUE residue
   class modulo M_r = 3^{s_{r-1}} * 2^{s_{r+1}+1} >= 72.
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

def s2(n: int) -> int:
    return bin(n).count("1")

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

def test_two_step_disjoint_base3_digits():
    verified_2step = 0
    for b0 in range(1, 200001, 2):
        blocks = extract_blocks(b0)
        if len(blocks) >= 3:
            for r in range(len(blocks) - 2):
                _, _, s_r, u_r = blocks[r]
                _, _, s_r1, u_r1 = blocks[r + 1]
                _, _, s_r2, u_r2 = blocks[r + 2]
                if s_r >= 2 and s_r1 >= 2:
                    lhs_val = (1 << (s_r1 + s_r2)) * u_r2
                    rhs_val = (3 ** (s_r + s_r1)) * u_r + (3 ** s_r1) + (1 << s_r1)
                    assert lhs_val == rhs_val
                    # Exact two-step quotient and remainder
                    div = 3 ** (s_r + s_r1)
                    rem = (3 ** s_r1) + (1 << s_r1)
                    assert rem < div
                    assert lhs_val // div == u_r
                    assert lhs_val % div == rem
                    # Exact zero-carry Base-3 digit sum law
                    assert s3(lhs_val) == s3(u_r) + 1 + s3(1 << s_r1)
                    verified_2step += 1
    print(f"[Loop 1] Verified 2-step disjoint Base-3 digit-block law across {verified_2step} triples: 0 exceptions.")

def test_all_k_step_disjoint_top_digits():
    verified_kstep = 0
    for b0 in range(1, 200001, 2):
        blocks = extract_blocks(b0)
        L = len(blocks)
        for r in range(L):
            _, _, s_r, u_r = blocks[r]
            if s_r < 2:
                continue
            pow2_sum = 0
            pow3_sum = s_r
            rem = 0
            for k in range(1, L - r):
                _, _, s_rk, u_rk = blocks[r + k]
                if k == 1:
                    rem = 1
                else:
                    _, _, s_prev, _ = blocks[r + k - 1]
                    rem = (3 ** s_prev) * rem + (1 << pow2_sum)
                    pow3_sum += s_prev
                pow2_sum += s_rk
                lhs = (1 << pow2_sum) * u_rk
                div = 3 ** pow3_sum
                assert lhs == div * u_r + rem
                assert 5 * rem < 9 * (3 ** (pow3_sum - s_r))
                assert rem < 2 * (3 ** (pow3_sum - s_r))
                assert rem < div
                assert lhs // div == u_r
                assert lhs % div == rem
                # NEVER carries into u_r for ANY K >= 1!
                assert s3(lhs) == s3(u_r) + s3(rem)
                verified_kstep += 1
    print(f"[Loop 2] Verified ALL-K-step zero-carry top-block law s_3(2^S u_{{r+K}}) = s_3(u_r) + s_3(R_{{r,K}}) across {verified_kstep} pairs: 0 exceptions.")

def test_two_sided_past_future_crt_pinch():
    verified_crt = 0
    for b0 in range(1, 200001, 2):
        blocks = extract_blocks(b0)
        L = len(blocks)
        for r in range(1, L - 1):
            _, _, s_prev, u_prev = blocks[r - 1]
            _, _, s_r, u_r = blocks[r]
            _, _, s_next, u_next = blocks[r + 1]
            if s_prev >= 2 and s_r >= 2 and s_next >= 2:
                # Past lock: 2^{s_r} * u_r === 1 (mod 3^{s_{r-1}})
                assert ((1 << s_r) * u_r) % (3 ** s_prev) == 1
                # Future lock: 3^{s_r} * u_r + 1 === 2^{s_{r+1}} (mod 2^{s_{r+1}+1})
                assert ((3 ** s_r) * u_r + 1) % (1 << (s_next + 1)) == (1 << s_next)
                # Combined coprime modulus M_r = 3^{s_{r-1}} * 2^{s_{r+1}+1} >= 72
                M_r = (3 ** s_prev) * (1 << (s_next + 1))
                assert M_r >= 72
                verified_crt += 1
    print(f"[Loop 3] Verified Two-Sided Past-Future CRT Lock (modulus >= 72) across {verified_crt} interior blocks: 0 exceptions.")

if __name__ == "__main__":
    test_two_step_disjoint_base3_digits()
    test_all_k_step_disjoint_top_digits()
    test_two_sided_past_future_crt_pinch()
