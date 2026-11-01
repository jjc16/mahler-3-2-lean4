import CanonicalOddBlockChainAndGrandSynthesis

/-!
# All-Block Constant of Motion $\lfloor 2^{T_N} P_N / 3^{T_N} \rfloor = P_0$, Markovian Mod-$3^{T_N}$ Escape, Backward State Recovery & Floor-Fractional Identification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 1 / 20 (Part XVI, Sections C2.O1.1–C2.O1.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O1.1 (Inner Loop 1 / 5) — Unconditional $A_{0,N} < 3^{T_N}$ and All-Block Constant of Motion
   (`renewalNumerator_lt_three_pow_of_two_le`,
   `allBlock_constant_of_motion_and_mod_three_pow`)**:
   - Whenever $\forall k < N,\, 2 \le s_k$, the $L = 2$ Bellman upper sandwich gives
     `5 * renewalNumerator s N ≤ 4 * (3 ^ T_N - 2 ^ T_N) < 4 * 3 ^ T_N`, so `renewalNumerator s N < 3 ^ T_N`
     holds **unconditionally** (including all $s = 2$ recovery blocks!).
   - Consequently, along any valid `N`-block chain (`ValidBlockChain b_0 s u N`) with $\forall k < N,\, 2 \le s_k$:
     `(2 ^ T_N * oddReturnP (orbit b_0 T_N)) / 3 ^ T_N = oddReturnP b_0` and
     `(2 ^ T_N * oddReturnP (orbit b_0 T_N)) % 3 ^ T_N = renewalNumerator s N`.

2. **Section C2.O1.2 (Inner Loop 2 / 5) — Markovian Mod-$3^{T_N}$ Escape & Slack Representation
   (`allBlock_markovian_mod_three_pow_escape_and_slack`)**:
   - Under $\forall k < N,\, 2 \le s_k$, the finite escape certificate and integer renewal slack are
     determined purely by the terminal state $P_N$ and step sum $T_N$:
     `2 * renewalNumerator s N ≥ 3 ^ T_N ↔ 2 * ((2 ^ T_N * P_N) % 3 ^ T_N) ≥ 3 ^ T_N` and
     `renewalIntSlack s N = (3 : ℤ) ^ T_N - 2 * (((2 ^ T_N * P_N) % 3 ^ T_N : ℕ) : ℤ)`.

3. **Section C2.O1.3 (Inner Loop 3 / 5) — Dual Base-2 Frozen-Seed Stabilization
   (`allBlock_frozen_seed_stabilization`)**:
   - Whenever `oddReturnP b_0 < 2 ^ T_N` and $\forall k < N,\, 2 \le s_k$,
     `oddReturnP b_0 / 2 ^ T_N = 0`, `oddReturnP b_0 % 2 ^ T_N = oddReturnP b_0`, and
     `oddReturnP (orbit b_0 T_N) < 3 ^ T_N` (`oddReturnP (orbit b_0 T_N) / 3 ^ T_N = 0`).

4. **Section C2.O1.4 (Inner Loop 4 / 5) — Exact Backward State Recovery from Any Future State
   (`allBlock_backward_state_recovery_from_future`)**:
   - For any $K \le M$ along a valid chain with $\forall k < M,\, 2 \le s_k$, setting $d = T_M - T_K$:
     `(2 ^ d * P_M) / 3 ^ d = P_K` and `(2 ^ d * P_M) % 3 ^ d = renewalNumerator (fun t => s (K + t)) (M - K)`,
     recovering every past state $P_K$ and segment numerator $A_{K,M}$ from $(P_M, d)$!

5. **Section C2.O1.5 (Inner Loop 5 / 5) — Exact Floor and Fractional-Part Identification of $\mathcal{H}_\infty (3/2)^{T_r}$
   (`supRenewalTail_le_four_fifths_and_floor_fract_identity`)**:
   - Whenever $\forall k,\, 2 \le s_k$ along an infinite valid block chain,
     `0 < supRenewalTail b_0 s r ≤ 4 / 5 < 1`, so for every $r \in \mathbb{N}$:
     `⌊supRenewalScale b_0 s * (3 / 2 : ℝ) ^ T_r⌋ = (oddReturnP (orbit b_0 T_r) : ℤ)` and
     `Int.fract (supRenewalScale b_0 s * (3 / 2 : ℝ) ^ T_r) = supRenewalTail b_0 s r`.
-/

namespace Mahler.AllBlockConstantOfMotion

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.SparseDefectCocycle
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection
open Mahler.BetaShiftDictionary
open Mahler.GeneralizedDefectAllRung
open Mahler.BoundedOddPartAndSieve
open Mahler.AllRungConstantOfMotion
open Mahler.ArchimedeanPinningAndRenewal
open Mahler.ConsecutiveGCDAndPillai
open Mahler.OctadicDeathAnatomy
open Mahler.RenewalCocycleAndSandwich
open Mahler.AllBlockRepeatedWindow
open Mahler.SignedCocycleRenewalBridge
open Mahler.MultiStepQuotientAndFermatGCD
open Mahler.RecoveryCascadeClosedForms
open Mahler.TwoAdicRecoveryPruningTree
open Mahler.SixBlockKneadingAndFiftyMillion
open Mahler.StrictEndpointAndSlackGrowth
open Mahler.InfiniteRenewalEquivalence
open Mahler.CanonicalOddBlockSynthesis

/-! ## 1. Section C2.O1.1: Unconditional $A_{0,N} < 3^{T_N}$ & All-Block Constant of Motion -/

/-- **Unconditional Upper Bound $5 A_{0,N} \le 4(3^{T_N} - 2^{T_N})$ and $A_{0,N} < 3^{T_N}$ for $s_k \ge 2$
(`renewalNumerator_lt_three_pow_of_two_le`, Section C2.O1.1)**:
Whenever `∀ k < N, 2 ≤ s k`:
1. `5 * renewalNumerator s N ≤ 4 * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N))`, and
2. `renewalNumerator s N < 3 ^ (blockSteps s N)`. -/
theorem renewalNumerator_lt_three_pow_of_two_le {s : ℕ → ℕ} {N : ℕ}
    (hs2 : ∀ k < N, 2 ≤ s k) :
    5 * renewalNumerator s N ≤ 4 * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) ∧
      renewalNumerator s N < 3 ^ (blockSteps s N) := by
  have hsand := renewalNumerator_bellman_upper_sandwich (L := 2) hs2
  set T_N := blockSteps s N
  change (3 ^ 2 - 2 ^ 2) * renewalNumerator s N ≤ 2 ^ 2 * (3 ^ T_N - 2 ^ T_N) at hsand
  have h2_pos : 0 < 2 ^ T_N := Nat.pow_pos (by decide)
  have hle_T : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  exact ⟨by omega, by omega⟩

/-- **All-Block Constant of Motion & Mod-$3^{T_N}$ Remainder Law
(`allBlock_constant_of_motion_and_mod_three_pow`, Section C2.O1.1)**:
Along any valid `N`-block chain (`ValidBlockChain b_0 s u N`) with `∀ k < N, 2 ≤ s k`, setting
`T_N = blockSteps s N` and `P_N = oddReturnP (orbit b_0 T_N)`:
1. `(2 ^ T_N * P_N) / 3 ^ T_N = oddReturnP b_0`, and
2. `(2 ^ T_N * P_N) % 3 ^ T_N = renewalNumerator s N`. -/
theorem allBlock_constant_of_motion_and_mod_three_pow
    {b_0 N : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u N)
    (hs2 : ∀ k < N, 2 ≤ s k) :
    let T_N := blockSteps s N
    let P_N := oddReturnP (orbit b_0 T_N)
    (2 ^ T_N * P_N) / 3 ^ T_N = oddReturnP b_0 ∧
      (2 ^ T_N * P_N) % 3 ^ T_N = renewalNumerator s N := by
  intro T_N P_N
  have hm := renewal_prefix_master_identity hchain
  change 2 ^ T_N * P_N = 3 ^ T_N * oddReturnP b_0 + renewalNumerator s N at hm
  have hlt := (renewalNumerator_lt_three_pow_of_two_le hs2).2
  change renewalNumerator s N < 3 ^ T_N at hlt
  have h3_pos : 0 < 3 ^ T_N := Nat.pow_pos (by decide)
  have hcomm : 3 ^ T_N * oddReturnP b_0 + renewalNumerator s N =
      renewalNumerator s N + 3 ^ T_N * oddReturnP b_0 := Nat.add_comm _ _
  rw [hm, hcomm]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ h3_pos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## 2. Section C2.O1.2: Markovian Mod-$3^{T_N}$ Escape & Slack Representation -/

/-- **Markovian Mod-$3^{T_N}$ Escape & Slack Representation
(`allBlock_markovian_mod_three_pow_escape_and_slack`, Section C2.O1.2)**:
Along any valid `N`-block chain (`ValidBlockChain b_0 s u N`) with `∀ k < N, 2 ≤ s k`, setting
`T_N = blockSteps s N` and `P_N = oddReturnP (orbit b_0 T_N)`:
1. `2 * renewalNumerator s N ≥ 3 ^ T_N ↔ 2 * ((2 ^ T_N * P_N) % 3 ^ T_N) ≥ 3 ^ T_N`, and
2. `renewalIntSlack s N = (3 : ℤ) ^ T_N - 2 * (((2 ^ T_N * P_N) % 3 ^ T_N : ℕ) : ℤ)`. -/
theorem allBlock_markovian_mod_three_pow_escape_and_slack
    {b_0 N : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u N)
    (hs2 : ∀ k < N, 2 ≤ s k) :
    let T_N := blockSteps s N
    let P_N := oddReturnP (orbit b_0 T_N)
    (2 * renewalNumerator s N ≥ 3 ^ T_N ↔
      2 * ((2 ^ T_N * P_N) % 3 ^ T_N) ≥ 3 ^ T_N) ∧
      renewalIntSlack s N =
        (3 : ℤ) ^ T_N - 2 * (((2 ^ T_N * P_N) % 3 ^ T_N : ℕ) : ℤ) := by
  intro T_N P_N
  have hmod := (allBlock_constant_of_motion_and_mod_three_pow hchain hs2).2
  change (2 ^ T_N * P_N) % 3 ^ T_N = renewalNumerator s N at hmod
  rw [hmod]
  exact ⟨Iff.rfl, rfl⟩

/-! ## 3. Section C2.O1.3: Dual Base-2 Frozen-Seed Stabilization -/

/-- **Dual Base-2 Frozen-Seed Stabilization (`allBlock_frozen_seed_stabilization`, Section C2.O1.3)**:
Whenever `ValidBlockChain b_0 s u N`, `∀ k < N, 2 ≤ s k`, and `oddReturnP b_0 < 2 ^ (blockSteps s N)`:
1. `oddReturnP b_0 / 2 ^ (blockSteps s N) = 0` and `oddReturnP b_0 % 2 ^ (blockSteps s N) = oddReturnP b_0`,
2. `oddReturnP (orbit b_0 (blockSteps s N)) < 3 ^ (blockSteps s N)`, and
3. `oddReturnP (orbit b_0 (blockSteps s N)) / 3 ^ (blockSteps s N) = 0`. -/
theorem allBlock_frozen_seed_stabilization
    {b_0 N : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u N)
    (hs2 : ∀ k < N, 2 ≤ s k)
    (hP0_lt : oddReturnP b_0 < 2 ^ (blockSteps s N)) :
    let T_N := blockSteps s N
    let P_N := oddReturnP (orbit b_0 T_N)
    oddReturnP b_0 / 2 ^ T_N = 0 ∧
      oddReturnP b_0 % 2 ^ T_N = oddReturnP b_0 ∧
      P_N < 3 ^ T_N ∧
      P_N / 3 ^ T_N = 0 := by
  intro T_N P_N
  have hm := renewal_prefix_master_identity hchain
  change 2 ^ T_N * P_N = 3 ^ T_N * oddReturnP b_0 + renewalNumerator s N at hm
  have hA_lt := (renewalNumerator_lt_three_pow_of_two_le hs2).2
  change renewalNumerator s N < 3 ^ T_N at hA_lt
  have hP0_le : oddReturnP b_0 + 1 ≤ 2 ^ T_N := hP0_lt
  have hmul_lt : 2 ^ T_N * P_N < 2 ^ T_N * 3 ^ T_N := by
    calc
      2 ^ T_N * P_N = 3 ^ T_N * oddReturnP b_0 + renewalNumerator s N := hm
      _ < 3 ^ T_N * oddReturnP b_0 + 3 ^ T_N := by omega
      _ = 3 ^ T_N * (oddReturnP b_0 + 1) := by ring
      _ ≤ 3 ^ T_N * 2 ^ T_N := Nat.mul_le_mul_left (3 ^ T_N) hP0_le
      _ = 2 ^ T_N * 3 ^ T_N := Nat.mul_comm _ _
  have hPN_lt : P_N < 3 ^ T_N :=
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide))).mp hmul_lt
  exact ⟨Nat.div_eq_of_lt hP0_lt, Nat.mod_eq_of_lt hP0_lt, hPN_lt, Nat.div_eq_of_lt hPN_lt⟩

/-! ## 4. Section C2.O1.4: Exact Backward State Recovery from Any Future State -/

/-- **Exact Backward State Recovery from Any Future State
(`allBlock_backward_state_recovery_from_future`, Section C2.O1.4)**:
Along any valid `M`-block chain (`ValidBlockChain b_0 s u M`) with `∀ k < M, 2 ≤ s k`, for every
`K ≤ M`, setting `d = blockSteps s M - blockSteps s K`, `P_K = oddReturnP (orbit b_0 (blockSteps s K))`,
and `P_M = oddReturnP (orbit b_0 (blockSteps s M))`:
1. `(2 ^ d * P_M) / 3 ^ d = P_K`, and
2. `(2 ^ d * P_M) % 3 ^ d = renewalNumerator (fun t => s (K + t)) (M - K)`. -/
theorem allBlock_backward_state_recovery_from_future
    {b_0 K M : ℕ} {s u : ℕ → ℕ}
    (hKM : K ≤ M) (hchain : ValidBlockChain b_0 s u M)
    (hs2 : ∀ k < M, 2 ≤ s k) :
    let d := blockSteps s M - blockSteps s K
    let P_K := oddReturnP (orbit b_0 (blockSteps s K))
    let P_M := oddReturnP (orbit b_0 (blockSteps s M))
    (2 ^ d * P_M) / 3 ^ d = P_K ∧
      (2 ^ d * P_M) % 3 ^ d = renewalNumerator (fun t => s (K + t)) (M - K) := by
  intro d P_K P_M
  have hM_eq : K + (M - K) = M := by omega
  have hch_shift := validBlockChain_shift (r := K) (L := M - K) (by omega) hchain
  have hs2_shift : ∀ t < M - K, 2 ≤ s (K + t) := fun t ht => hs2 (K + t) (by omega)
  have hcom := allBlock_constant_of_motion_and_mod_three_pow hch_shift hs2_shift
  dsimp only at hcom
  have hshift := blockSteps_add_shift s K (M - K)
  rw [hM_eq] at hshift
  have hd_eq : blockSteps (fun t => s (K + t)) (M - K) = d := by
    dsimp [d]
    omega
  rw [← orbit_add, ← hshift, hd_eq] at hcom
  exact hcom

/-! ## 5. Section C2.O1.5: Floor and Fractional-Part Identification of $\mathcal{H}_\infty (3/2)^{T_r}$ -/

/-- **Upper Bound $h_r^\infty \le 4/5 < 1$ and Exact Floor / Fractional-Part Identification
(`supRenewalTail_le_four_fifths_and_floor_fract_identity`, Section C2.O1.5)**:
Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`) with `∀ k, 2 ≤ s k`,
for every `r : ℕ`, setting `T_r = blockSteps s r` and `P_r = oddReturnP (orbit b_0 T_r)`:
1. `0 < supRenewalTail b_0 s r` and `supRenewalTail b_0 s r ≤ 4 / 5`,
2. `⌊supRenewalScale b_0 s * (3 / 2 : ℝ) ^ T_r⌋ = (P_r : ℤ)`, and
3. `Int.fract (supRenewalScale b_0 s * (3 / 2 : ℝ) ^ T_r) = supRenewalTail b_0 s r`. -/
theorem supRenewalTail_le_four_fifths_and_floor_fract_identity
    {b_0 : ℕ} {s u : ℕ → ℕ}
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N)
    (hs2 : ∀ k : ℕ, 2 ≤ s k) (r : ℕ) :
    let T_r := blockSteps s r
    let P_r := oddReturnP (orbit b_0 T_r)
    let x_r := supRenewalScale b_0 s * (3 / 2 : ℝ) ^ T_r
    (0 < supRenewalTail b_0 s r ∧ supRenewalTail b_0 s r ≤ 4 / 5) ∧
      ⌊x_r⌋ = (P_r : ℤ) ∧
      Int.fract x_r = supRenewalTail b_0 s r := by
  intro T_r P_r x_r
  have hs1 : ∀ k : ℕ, 1 ≤ s k := fun k => by have := hs2 k; omega
  have hmain := supRenewalTail_bounds_and_recurrence hchain
  have hpos : 0 < supRenewalTail b_0 s r := (hmain.2.1 r).1
  have hLUB := hmain.1
  set H := supRenewalScale b_0 s
  set LSeq := renewalPartialSeq b_0 s
  have hmono := (renewalPartialSeq_strictMono_and_two_index_bound b_0 hs1).2.1
  have htwo_45 :
      ∀ M : ℕ, r < M →
        LSeq M - LSeq r ≤ (4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r := by
    intro M hrM
    have hM_eq : r + (M - r) = M := by omega
    set s' := fun t => s (r + t)
    set d := blockSteps s' (M - r)
    set TM := blockSteps s M
    have hshift := blockSteps_add_shift s r (M - r)
    rw [hM_eq] at hshift
    change TM = T_r + d at hshift
    have hcomp := renewalNumerator_cocycle_composition s r (M - r)
    rw [hM_eq] at hcomp
    change renewalNumerator s M = 3 ^ d * renewalNumerator s r + 2 ^ T_r * renewalNumerator s' (M - r) at hcomp
    have h3r_ne : (3 : ℝ) ^ T_r ≠ 0 := pow_ne_zero T_r (by norm_num)
    have h3d_pos : (0 : ℝ) < (3 : ℝ) ^ d := pow_pos (by norm_num) d
    have h3d_ne : (3 : ℝ) ^ d ≠ 0 := ne_of_gt h3d_pos
    have hdiff_eq :
        LSeq M - LSeq r = (2 / 3 : ℝ) ^ T_r * ((renewalNumerator s' (M - r) : ℝ) / (3 : ℝ) ^ d) := by
      unfold LSeq renewalPartialSeq
      dsimp only [T_r, TM] at hshift hcomp h3r_ne ⊢
      rw [hshift, hcomp, pow_add, div_pow]
      push_cast
      field_simp [h3r_ne, h3d_ne]
      ring
    rw [hdiff_eq]
    have h54 := (renewalNumerator_lt_three_pow_of_two_le (s := s') (N := M - r)
      (fun k _ => hs2 (r + k))).1
    change 5 * renewalNumerator s' (M - r) ≤ 4 * (3 ^ d - 2 ^ d) at h54
    have h2d_pos : 0 < 2 ^ d := Nat.pow_pos (by decide)
    have hd_le : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
    have hle_3d : 5 * renewalNumerator s' (M - r) ≤ 4 * 3 ^ d := by omega
    have hle_r : 5 * (renewalNumerator s' (M - r) : ℝ) ≤ 4 * (3 : ℝ) ^ d := by
      exact_mod_cast hle_3d
    have hdiv_le : (renewalNumerator s' (M - r) : ℝ) / (3 : ℝ) ^ d ≤ 4 / 5 := by
      rw [div_le_iff₀ h3d_pos]
      linarith
    have hqr_nonneg : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ T_r := pow_nonneg (by norm_num) T_r
    calc
      (2 / 3 : ℝ) ^ T_r * ((renewalNumerator s' (M - r) : ℝ) / (3 : ℝ) ^ d) ≤
          (2 / 3 : ℝ) ^ T_r * (4 / 5) :=
        mul_le_mul_of_nonneg_left hdiv_le hqr_nonneg
      _ = (4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r := by ring
  have hH_le : H ≤ LSeq r + (4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r := by
    refine hLUB.2 ?_
    rintro _ ⟨M, rfl⟩
    rcases lt_trichotomy M r with hMr | rfl | hrM
    · have hlt : LSeq M < LSeq r := hmono hMr
      have hq_nonneg : (0 : ℝ) ≤ (4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r := by positivity
      linarith
    · have hq_nonneg : (0 : ℝ) ≤ (4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r := by positivity
      linarith
    · have h := htwo_45 M hrM
      linarith
  have hxr_eq : x_r = (P_r : ℝ) + supRenewalTail b_0 s r := by
    dsimp [x_r, P_r, T_r]
    unfold supRenewalTail renewalTail fracPart oddReturnP
    push_cast
    ring
  have htail_eq : supRenewalTail b_0 s r = (3 / 2 : ℝ) ^ T_r * (H - LSeq r) := by
    have hnorm := renewal_normalized_prefix_identity (hchain r)
    dsimp only at hnorm
    have hL_def : LSeq r = (oddReturnP b_0 : ℝ) + (renewalNumerator s r : ℝ) / (3 : ℝ) ^ T_r := rfl
    rw [← hL_def] at hnorm
    have hcancel : (3 / 2 : ℝ) ^ T_r * (2 / 3 : ℝ) ^ T_r = 1 := by
      rw [← mul_pow]; norm_num
    have hPr_eq : (P_r : ℝ) = (3 / 2 : ℝ) ^ T_r * LSeq r := by
      dsimp [P_r]
      calc
        (oddReturnP (orbit b_0 T_r) : ℝ) =
            ((3 / 2 : ℝ) ^ T_r * (2 / 3 : ℝ) ^ T_r) * (oddReturnP (orbit b_0 T_r) : ℝ) := by
          rw [hcancel, one_mul]
        _ = (3 / 2 : ℝ) ^ T_r * ((2 / 3 : ℝ) ^ T_r * (oddReturnP (orbit b_0 T_r) : ℝ)) := by ring
        _ = (3 / 2 : ℝ) ^ T_r * LSeq r := by rw [hnorm]
    have hx_def : x_r = H * (3 / 2 : ℝ) ^ T_r := rfl
    linarith [hxr_eq, hPr_eq, hx_def]
  have hle_45 : supRenewalTail b_0 s r ≤ 4 / 5 := by
    rw [htail_eq]
    have h32_nonneg : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ T_r := pow_nonneg (by norm_num) T_r
    have hdiff_le : H - LSeq r ≤ (4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r := by linarith [hH_le]
    have hcancel : (3 / 2 : ℝ) ^ T_r * ((4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r) = 4 / 5 := by
      have hc : (3 / 2 : ℝ) ^ T_r * (2 / 3 : ℝ) ^ T_r = 1 := by
        rw [← mul_pow]; norm_num
      calc
        (3 / 2 : ℝ) ^ T_r * ((4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r) =
            (4 / 5 : ℝ) * ((3 / 2 : ℝ) ^ T_r * (2 / 3 : ℝ) ^ T_r) := by ring
        _ = 4 / 5 := by rw [hc, mul_one]
    calc
      (3 / 2 : ℝ) ^ T_r * (H - LSeq r) ≤ (3 / 2 : ℝ) ^ T_r * ((4 / 5 : ℝ) * (2 / 3 : ℝ) ^ T_r) :=
        mul_le_mul_of_nonneg_left hdiff_le h32_nonneg
      _ = 4 / 5 := hcancel
  have hfl : ⌊x_r⌋ = (P_r : ℤ) := by
    rw [Int.floor_eq_iff, hxr_eq]
    push_cast
    constructor <;> linarith
  have hfr : Int.fract x_r = supRenewalTail b_0 s r := by
    rw [Int.fract, hfl, hxr_eq]
    push_cast
    ring
  exact ⟨⟨hpos, hle_45⟩, hfl, hfr⟩

end Mahler.AllBlockConstantOfMotion
