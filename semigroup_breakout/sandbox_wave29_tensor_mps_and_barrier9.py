#!/usr/bin/env python3
"""
Wave 29 Computational Discovery & Verification Suite (SB.159 - SB.160):
=======================================================================
Bit-Cut Matrix Product State (MPS) Rank Profiles, Continuation Phase Bijection,
and Barrier #9 (Additive-Carry Hankel Flattening Rank vs. Carry-Free Kronecker Rank).

Verifies:
  1. SB.159 (Bit-Cut Affine Carry Transport, Continuation Phase Bijection, & MPS Arch Bounds):
     - Prefix parity invariance & step-k affine transport:
         orbit_parity_word(r + 2^k * m, k) == orbit_parity_word(r, k)
         orbit(r + 2^k * m, k) == orbit(r, k) + 3^k * m
     - Bijection of m |-> (orbit(r, k) + 3^k * m) mod 2^d on [0, 2^d)
     - Active-row/column MPS arch support bounds:
         rank(M^(no-11)_{k, W-k}) <= min(F_{k+2}, 2^{W-k})
         rank(M^(Mahler)_{k, W-k}) <= min(|C_k|, 2^{W-k})
       plus exact Q-rank and GF(2)-rank saturation across k = 1..7 at W = 15, N = 18
       (ranks 2,3,5,8,13,21,34 = F_{k+2} for no-11 and 2,3,5,8,12,18,27 = |C_k| for Mahler
       [0, 1/2), and 39/40 at k = 8, W = 15 rising to full 40/40 at W = 16).
  2. SB.160 (Barrier #9 - Additive-Carry Hankel Flattening Rank vs. Carry-Free Kronecker Rank):
     - For ANY nonempty positive survivor set S subseteq N_{>0} with minimum z_min = min(S) >= 1
       (even a singleton S = {z_min}), the reversed-column (z_min + 1) x (z_min + 1) submatrix
         A_{i, j} = 1_S(i + (z_min - j))   (0 <= i, j <= z_min)
       is unit lower-triangular (A_{i, i} = 1, A_{i, j} = 0 for i < j), forcing det(A) = 1 and
       linear independence of all z_min + 1 rows over EVERY field F (including Q, R, and GF(2)),
       and inheriting flattening rank >= z_min + 1 for r-copy tensors T(x_1,...,x_r) = 1_S(sum x_i)
       whenever each leg domain contains {0, ..., z_min}.
     - Contrasts with carry-free Kronecker singleton tensors delta_{x=w*} * delta_{y=w*},
       which have rank 1 on any singleton {w*}.
  3. Section 34.3 Parity-Word Coordinate Comparison:
     - Compares binary-coordinate vs. parity-word-coordinate bit-cut peak ranks at W = N = 15
       (64 & 58 over Q -> 2 & 9) and post-bit-length W = 15, N = 18 (rebounding to 33 & 27 over Q).
"""


def orbit_step(b: int) -> int:
    return (3 * b + (b & 1)) >> 1


def orbit_val_and_word(b0: int, steps: int) -> tuple[int, tuple[int, ...]]:
    b = b0
    bits = []
    for _ in range(steps):
        e = b & 1
        bits.append(e)
        b = (3 * b + e) >> 1
    return b, tuple(bits)


def survives_no11(b0: int, N: int) -> int:
    b = b0
    prev = 0
    for _ in range(N):
        e = b & 1
        if prev == 1 and e == 1:
            return 0
        prev = e
        b = (3 * b + e) >> 1
    return 1


def build_parry_words(N: int) -> set[tuple[int, ...]]:
    cur: list[tuple[int, tuple[int, ...]]] = [(1, ())]
    for step in range(N):
        nxt: list[tuple[int, tuple[int, ...]]] = []
        lim = 1 << (step + 1)
        for B, w in cur:
            if 3 * B <= lim:
                nxt.append((3 * B, w + (0,)))
            else:
                nxt.append((lim, w + (0,)))
                nxt.append((3 * B - lim, w + (1,)))
        cur = nxt
    return {w for _, w in cur}


def gf2_rank_rows(rows: list[list[int]]) -> int:
    """Exact GF(2) rank via arbitrary-precision Python integer bitmask elimination."""
    basis: dict[int, int] = {}
    for row in rows:
        mask = 0
        for idx, val in enumerate(row):
            if val & 1:
                mask |= 1 << idx
        while mask:
            msb = mask.bit_length() - 1
            if msb in basis:
                mask ^= basis[msb]
            else:
                basis[msb] = mask
                break
    return len(basis)


def exact_q_rank(rows: list[list[int]]) -> int:
    """Exact rank over Q via fraction-free Bareiss integer Gaussian elimination."""
    # Deduplicate / drop all-zero rows first to keep elimination compact on wide bit-cut matrices
    uniq = []
    seen = set()
    for row in rows:
        t = tuple(row)
        if any(t) and t not in seen:
            seen.add(t)
            uniq.append(list(t))
    if not uniq:
        return 0
    # Transpose if wider than tall so elimination runs on min(R, C) dimension
    m, n = len(uniq), len(uniq[0])
    if n > m:
        A = [[uniq[i][j] for i in range(m)] for j in range(n)]
        m, n = n, m
    else:
        A = uniq
    rank = 0
    prev_piv = 1
    for col in range(n):
        piv_row = None
        for r in range(rank, m):
            if A[r][col] != 0:
                piv_row = r
                break
        if piv_row is None:
            continue
        if piv_row != rank:
            A[rank], A[piv_row] = A[piv_row], A[rank]
        piv = A[rank][col]
        for r in range(rank + 1, m):
            for c in range(col + 1, n):
                A[r][c] = (A[r][c] * piv - A[r][col] * A[rank][c]) // prev_piv
            A[r][col] = 0
        prev_piv = piv
        rank += 1
    return rank


def reshape_bit_cut(vec: list[int], W: int, k: int) -> list[list[int]]:
    n_rows = 1 << k
    n_cols = 1 << (W - k)
    return [[vec[r + (m << k)] for m in range(n_cols)] for r in range(n_rows)]


def test_sb159_bit_cut_transport_and_mps_arch() -> None:
    print("=== Test 1 (SB.159): Bit-Cut Affine Carry Transport & MPS Entanglement Arch ===")
    # 1A: Exact affine transport & mod-2^d bijection (including k=0, d=0 edge cases)
    for k in range(0, 7):
        for r in range(1 << k):
            orb_r, word_r = orbit_val_and_word(r, k)
            for m in range(25):
                orb_rm, word_rm = orbit_val_and_word(r + (1 << k) * m, k)
                assert word_rm == word_r
                assert orb_rm == orb_r + (3 ** k) * m
            for d in range(0, 6):
                mod_vals = {(orb_r + (3 ** k) * m) % (1 << d) for m in range(1 << d)}
                assert len(mod_vals) == (1 << d)
    print("  Verified exact prefix word invariance, orbit(r + 2^k m, k) = orbit(r, k) + 3^k m, and mod-2^d bijection [OK]")

    # 1B: Exact MPS bond-rank arch at W = N = 12 and exact Q / GF(2) saturation at W = 15..16, N = 18
    fib = [0, 1]
    for _ in range(20):
        fib.append(fib[-2] + fib[-1])

    W_arch, N_arch = 12, 12
    vec12 = [survives_no11(b0, N_arch) for b0 in range(1 << W_arch)]
    ranks_12_Q = []
    ranks_12_F2 = []
    caps_12 = []
    for k in range(1, W_arch):
        M = reshape_bit_cut(vec12, W_arch, k)
        rk_Q = exact_q_rank(M)
        rk_2 = gf2_rank_rows(M)
        cap = min(fib[k + 2], 1 << (W_arch - k))
        assert rk_Q <= cap and rk_2 <= cap
        ranks_12_Q.append(rk_Q)
        ranks_12_F2.append(rk_2)
        caps_12.append(cap)
    print(f"  W=N=12 exact MPS ranks k=1..11 (Q={ranks_12_Q}, GF2={ranks_12_F2}) <= arch caps {caps_12} [OK]")

    W_sat, N_sat = 15, 18
    adm18 = build_parry_words(N_sat)
    vec_no11 = [survives_no11(b0, N_sat) for b0 in range(1 << W_sat)]
    vec_mah = [1 if orbit_val_and_word(b0, N_sat)[1] in adm18 else 0 for b0 in range(1 << W_sat)]
    for k in range(1, 8):
        M_n = reshape_bit_cut(vec_no11, W_sat, k)
        M_m = reshape_bit_cut(vec_mah, W_sat, k)
        rk_n_Q, rk_n_2 = exact_q_rank(M_n), gf2_rank_rows(M_n)
        rk_m_Q, rk_m_2 = exact_q_rank(M_m), gf2_rank_rows(M_m)
        parry_k = len(build_parry_words(k))
        assert rk_n_Q == fib[k + 2] and rk_n_2 == fib[k + 2]
        assert rk_m_Q == parry_k and rk_m_2 == parry_k
    # Also check k = 8 starvation at W = 15 (39/40) vs full saturation at W = 16 (40/40)
    M_m8_w15 = reshape_bit_cut(vec_mah, 15, 8)
    assert exact_q_rank(M_m8_w15) == 39 and gf2_rank_rows(M_m8_w15) == 39 and len(build_parry_words(8)) == 40
    vec_mah16 = [1 if orbit_val_and_word(b0, N_sat)[1] in adm18 else 0 for b0 in range(1 << 16)]
    M_m8_w16 = reshape_bit_cut(vec_mah16, 16, 8)
    assert exact_q_rank(M_m8_w16) == 40 and gf2_rank_rows(M_m8_w16) == 40
    print(
        "  Verified exact Q & GF(2) rank saturation F_{k+2}=(2,3,5,8,13,21,34) & |C_k|=(2,3,5,8,12,18,27) "
        "for k=1..7 at W=15, N=18 (and k=8: 39/40 at W=15 -> 40/40 at W=16) [OK]"
    )


def test_sb160_barrier9_antidiagonal_singleton_rank_explosion() -> None:
    print("\n=== Test 2 (SB.160 - Barrier #9): Unit-Triangular Additive-Carry Hankel Minor ===")
    M = 64
    test_sets = [
        {1},
        {7},
        {29},
        {63},
        {5, 12, 19, 44, 61},
        {z for z in range(1, 2 * M) if survives_no11(z, 24) == 1},
    ]
    for S in test_sets:
        assert len(S) >= 1
        z_min = min(S)
        assert z_min < M
        H = [[1 if (x + y) in S else 0 for y in range(M)] for x in range(M)]
        A = [[H[i][z_min - j] for j in range(z_min + 1)] for i in range(z_min + 1)]
        for i in range(z_min + 1):
            assert A[i][i] == 1
            for j in range(i + 1, z_min + 1):
                assert A[i][j] == 0
        rk_Q = exact_q_rank(H)
        rk_2 = gf2_rank_rows(H)
        assert rk_Q >= z_min + 1
        assert rk_2 >= z_min + 1
        K_diag = [[1 if (x == z_min and y == z_min) else 0 for y in range(M)] for x in range(M)]
        assert exact_q_rank(K_diag) == 1 and gf2_rank_rows(K_diag) == 1
        print(
            f"  |S|={len(S):2d}, z_min={z_min:2d}: unit-triangular minor size={z_min+1:2d}, "
            f"rank_Q(H)={rk_Q:2d}, rank_GF2(H)={rk_2:2d} >= {z_min+1:2d} (vs Kronecker singleton rank=1) [OK]"
        )


def test_section34_3_parity_word_coordinate_comparison() -> None:
    print("\n=== Test 3 (Section 34.3): Binary vs. Parity-Word Coordinate Bit-Cut Ranks ===")
    W = 15
    adm15 = build_parry_words(15)
    adm18 = build_parry_words(18)

    def word_to_int(bits: tuple[int, ...]) -> int:
        v = 0
        for i, bit in enumerate(bits):
            v |= (bit & 1) << i
        return v

    bin_no11_15 = [0] * (1 << W)
    bin_mah_15 = [0] * (1 << W)
    par_no11_15 = [0] * (1 << W)
    par_mah_15 = [0] * (1 << W)
    par_no11_18 = [0] * (1 << W)
    par_mah_18 = [0] * (1 << W)

    for b0 in range(1 << W):
        _, w18 = orbit_val_and_word(b0, 18)
        w15 = w18[:15]
        idx_p = word_to_int(w15)
        s_n15 = survives_no11(b0, 15)
        s_m15 = 1 if w15 in adm15 else 0
        s_n18 = survives_no11(b0, 18)
        s_m18 = 1 if w18 in adm18 else 0
        bin_no11_15[b0] = s_n15
        bin_mah_15[b0] = s_m15
        par_no11_15[idx_p] = s_n15
        par_mah_15[idx_p] = s_m15
        par_no11_18[idx_p] = s_n18
        par_mah_18[idx_p] = s_m18

    peak_bin_n15_Q = max(exact_q_rank(reshape_bit_cut(bin_no11_15, W, k)) for k in range(1, W))
    peak_bin_m15_Q = max(exact_q_rank(reshape_bit_cut(bin_mah_15, W, k)) for k in range(1, W))
    peak_bin_m15_F2 = max(gf2_rank_rows(reshape_bit_cut(bin_mah_15, W, k)) for k in range(1, W))
    peak_par_n15_Q = max(exact_q_rank(reshape_bit_cut(par_no11_15, W, k)) for k in range(1, W))
    peak_par_m15_Q = max(exact_q_rank(reshape_bit_cut(par_mah_15, W, k)) for k in range(1, W))
    peak_par_n18_Q = max(exact_q_rank(reshape_bit_cut(par_no11_18, W, k)) for k in range(1, W))
    peak_par_n18_F2 = max(gf2_rank_rows(reshape_bit_cut(par_no11_18, W, k)) for k in range(1, W))
    peak_par_m18_Q = max(exact_q_rank(reshape_bit_cut(par_mah_18, W, k)) for k in range(1, W))
    peak_par_m18_F2 = max(gf2_rank_rows(reshape_bit_cut(par_mah_18, W, k)) for k in range(1, W))

    assert (peak_bin_n15_Q, peak_bin_m15_Q, peak_bin_m15_F2) == (64, 58, 57)
    assert (peak_par_n15_Q, peak_par_m15_Q) == (2, 9)
    assert (peak_par_n18_Q, peak_par_n18_F2, peak_par_m18_Q, peak_par_m18_F2) == (33, 33, 27, 27)
    print(
        f"  W=N=15 peak Q-ranks: binary=({peak_bin_n15_Q}, {peak_bin_m15_Q}) [GF2 Mahler={peak_bin_m15_F2}] "
        f"-> parity=({peak_par_n15_Q}, {peak_par_m15_Q}); W=15, N=18 parity Q/GF2-ranks=({peak_par_n18_Q}, {peak_par_m18_Q}) [OK]"
    )


if __name__ == "__main__":
    test_sb159_bit_cut_transport_and_mps_arch()
    test_sb160_barrier9_antidiagonal_singleton_rank_explosion()
    test_section34_3_parity_word_coordinate_comparison()
    print("\nALL WAVE 29 VERIFICATION CHECKS PASSED (0 FAILURES).")
