import InfiniteZNumberBridgeAndRationalBase
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Weighted Repetition Cutoffs & Exclusion of Sturmian / Balanced Aperiodic Block Classes

This module implements Path 2 of the research plan (Centerpiece 1: rigorous
exclusion of a substantial aperiodic class):

1. **The $5:3$ ($3^5 = 243 < 2^8 = 256$) and $17:10$ ($3^{17} < 2^{27}$) Weighted
   Repetition Cutoffs (`weighted_five_three_repeated_subword_cutoff`,
   `weighted_seventeen_ten_repeated_subword_cutoff`,
   `weighted_five_three_block_count_cutoff`,
   `weighted_seventeen_ten_block_count_cutoff`)**:
   Starting from the exact exponential inequality
   `2^(T(r2) + S + 2) < 3^(T(r2) + 1) * (2 * a_0 + 1)` of
   `sharpened_repeated_subword_linear_cutoff` (where `S = blockSteps (shiftSeq s r1) L`),
   raising both sides to the 5th and 17th powers eliminates `Real.log` and proves:
   - `5 * blockSteps (shiftSeq s r1) L ≤ 3 * blockSteps s r2 + 5 * W + 2`,
   - `17 * blockSteps (shiftSeq s r1) L ≤ 10 * blockSteps s r2 + 17 * W + 9`,
   - `15 * L ≤ 3 * blockSteps s r2 + 5 * W + 7` (`5 * L ≤ blockSteps s r2 + 2 * W + 2`),
   - `51 * L ≤ 10 * blockSteps s r2 + 17 * W + 26`.

2. **Finite Pigeonhole Principle on Subword Complexity
   (`exists_repeated_subword_of_pattern_classifier`,
   `exists_repeated_subword_of_sturmian_complexity`)**:
   For any block sequence `s : ℕ → ℕ`, window length `1 ≤ L`, and complexity bound
   `1 ≤ C`, if a pattern classifier `pat : ℕ → Fin C` distinguishes distinct
   length-`L` windows among `0 ≤ r ≤ C`, then by the Finite Pigeonhole Principle
   there exist `r1 < r2 ≤ C` whose length-`L` subwords match (`∀ i < L, s (r1 + i) = s (r2 + i)`).

3. **Unconditional Exclusion of Ceiling-Saturated Sturmian & Sub-Critical Balanced
   Aperiodic Classes (`aperiodic_sturmian_three_four_exclusion`,
   `aperiodic_sturmian_three_five_exclusion`,
   `balanced_subcritical_complexity_exclusion`)**:
   - Even when `3 ≤ s k ≤ 4` for all `k` (so `minSlack s m = 2^T(m) > 0` holds
     forever and **no archimedean or deficiency test can ever fail**), any sequence
     of complexity `C ≤ L + C_0` at window length `L` satisfies
     `3 * L ≤ 12 * C_0 + 5 * W + 2` (and for `3 ≤ s k ≤ 5`, `L ≤ 50 * C_0 + 17 * W + 9`).
   - More generally, for **any** average block length `λ` (arbitrarily large), any
     surviving block chain satisfying the Sub-Critical Balanced Complexity Condition
     `10 * blockSteps s r2 ≤ (17 - δ) * blockSteps (shiftSeq s r1) L + D_0` (`1 ≤ δ`,
     corresponding to complexity factor `κ ≤ (17 - δ)/10 < 1.7095`) is bounded by
     `3 * δ * L ≤ D_0 + 17 * W + 9 + δ`.
-/

namespace Mahler.SturmianComplexityExclusion

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB
open Mahler.JumpValuation
open Mahler.EscapeBranchCap
open Mahler.PhaseLock
open Mahler.MasterReduction
open Mahler.ModEightClassifier
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.KernelDuality
open Mahler.Coasting
open Mahler.TwoSidedSqueeze
open Mahler.SharpenedSqueezes
open Mahler.AperiodicCocycle
open Mahler.MinSlackSystem
open Mahler.GlobalStepRate
open Mahler.BaseTwoLock
open Mahler.CeilingSynthesis
open Mahler.TelescopingDuality
open Mahler.ConverseReconstruction
open Mahler.ExplicitCutoffs
open Mahler.DeficitAmplification
open Mahler.TwoVisitSeparation
open Mahler.MonotonicSeparation
open Mahler.CeilingModTraps
open Mahler.TwoAdicLTE
open Mahler.FullStepValuation
open Mahler.RemainderAdditionLaw
open Mahler.TwoAdicCauchy
open Mahler.AllHistoryRecovery
open Mahler.ParametricCorridor
open Mahler.AperiodicBoundedSqueeze
open Mahler.TimeIndependentSqueeze
open Mahler.SlackDeadEnds
open Mahler.GrandSynthesis
open Mahler.Mod256Sieve
open Mahler.UnitRigidity
open Mahler.DeterminantCollapse
open Mahler.BakerMatveev
open Mahler.RidoutSubspace
open Mahler.MultiOriginSyzygy
open Mahler.SubwordComplexity
open Mahler.SimultaneousBaseDigits
open Mahler.MultiStepGCD
open Mahler.SeriesHankel
open Mahler.ThreeAdicSeedLocks
open Mahler.CoupledFractionalDynamics
open Mahler.Mod2304Sieve
open Mahler.TwoSidedCRTObstructions
open Mahler.ThreeAdicConservation
open Mahler.Mod216QuotientFloor
open Mahler.InfiniteZNumberBridge

/-! ## 1. Exponential Rational Approximations to $\log_2(3/2)$ (`3^5 < 2^8` & `3^17 < 2^27`) -/

/-- For every `T : ℕ`, `(3^(T + 1))^5 < 2^(8 * T + 8)` (`243^(T+1) < 256^(T+1)`). -/
theorem three_pow_succ_pow_five_lt_two_pow (T : ℕ) :
    (3 ^ (T + 1)) ^ 5 < 2 ^ (8 * T + 8) := by
  rw [← Nat.pow_mul]
  induction T with
  | zero => decide
  | succ T ih =>
      have h3 : 3 ^ ((T + 1 + 1) * 5) = 3 ^ ((T + 1) * 5) * 243 := by
        rw [show (T + 1 + 1) * 5 = (T + 1) * 5 + 5 by omega, Nat.pow_add]
      have h2 : 2 ^ (8 * (T + 1) + 8) = 2 ^ (8 * T + 8) * 256 := by
        rw [show 8 * (T + 1) + 8 = (8 * T + 8) + 8 by omega, Nat.pow_add]
      rw [h3, h2]
      omega

/-- For every `T : ℕ`, `(3^(T + 1))^17 < 2^(27 * T + 27)` (`3^17 = 129140163 < 134217728 = 2^27`). -/
theorem three_pow_succ_pow_seventeen_lt_two_pow (T : ℕ) :
    (3 ^ (T + 1)) ^ 17 < 2 ^ (27 * T + 27) := by
  rw [← Nat.pow_mul]
  induction T with
  | zero => decide
  | succ T ih =>
      have h3 : 3 ^ ((T + 1 + 1) * 17) = 3 ^ ((T + 1) * 17) * 129140163 := by
        rw [show (T + 1 + 1) * 17 = (T + 1) * 17 + 17 by omega, Nat.pow_add]
      have h2 : 2 ^ (27 * (T + 1) + 27) = 2 ^ (27 * T + 27) * 134217728 := by
        rw [show 27 * (T + 1) + 27 = (27 * T + 27) + 27 by omega, Nat.pow_add]
      rw [h3, h2]
      omega

private theorem pow_strict_mono_left {a b n : ℕ} (hn : 1 ≤ n) (hlt : a < b) :
    a ^ n < b ^ n := by
  have hb_pos : 0 < b := by omega
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · rw [Nat.zero_pow (by omega : 0 < n)]
    exact Nat.pow_pos hb_pos
  · induction n with
    | zero => omega
    | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simpa using hlt
        · have ihn := ih hpos
          rw [Nat.pow_succ, Nat.pow_succ]
          have h1 : a ^ n * a < b ^ n * a := Nat.mul_lt_mul_of_pos_right ihn ha_pos
          have h2 : b ^ n * a ≤ b ^ n * b := Nat.mul_le_mul_left (b ^ n) (by omega)
          exact lt_of_lt_of_le h1 h2

private theorem pow_le_pow_left_nat {a b n : ℕ} (hle : a ≤ b) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih hle

private theorem exp_lt_of_two_pow_lt {A B : ℕ} (h : 2 ^ A < 2 ^ B) : A < B := by
  by_contra hge
  have hle : 2 ^ B ≤ 2 ^ A := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private theorem five_three_cutoff_of_exp_bound {T S a_0 W : ℕ}
    (ha0 : a_0 < 2 ^ W)
    (hsharp : 2 ^ (T + S + 2) < 3 ^ (T + 1) * (2 * a_0 + 1)) :
    5 * S ≤ 3 * T + 5 * W + 2 := by
  have hpow5 := pow_strict_mono_left (by decide : 1 ≤ 5) hsharp
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have h2a0_5 : (2 * a_0 + 1) ^ 5 ≤ (2 ^ (W + 1)) ^ 5 :=
    pow_le_pow_left_nat h2a0
  have h3_5 := three_pow_succ_pow_five_lt_two_pow T
  have hlhs : (2 ^ (T + S + 2)) ^ 5 = 2 ^ (5 * T + 5 * S + 10) := by
    rw [← Nat.pow_mul]
    congr 1
    omega
  have hrhs_le :
      (3 ^ (T + 1) * (2 * a_0 + 1)) ^ 5 < 2 ^ (8 * T + 5 * W + 13) := by
    rw [Nat.mul_pow]
    have hpos : 0 < (2 * a_0 + 1) ^ 5 := Nat.pow_pos (by omega)
    have h1 :
        (3 ^ (T + 1)) ^ 5 * (2 * a_0 + 1) ^ 5 <
          2 ^ (8 * T + 8) * (2 * a_0 + 1) ^ 5 :=
      Nat.mul_lt_mul_of_pos_right h3_5 hpos
    have h2 :
        2 ^ (8 * T + 8) * (2 * a_0 + 1) ^ 5 ≤
          2 ^ (8 * T + 8) * (2 ^ (W + 1)) ^ 5 :=
      Nat.mul_le_mul_left _ h2a0_5
    have h3 :
        2 ^ (8 * T + 8) * (2 ^ (W + 1)) ^ 5 = 2 ^ (8 * T + 5 * W + 13) := by
      rw [← Nat.pow_mul, ← Nat.pow_add]
      congr 1
      omega
    rw [h3] at h2
    exact lt_of_lt_of_le h1 h2
  rw [hlhs] at hpow5
  have hexp := exp_lt_of_two_pow_lt (lt_trans hpow5 hrhs_le)
  omega

private theorem seventeen_ten_cutoff_of_exp_bound {T S a_0 W : ℕ}
    (ha0 : a_0 < 2 ^ W)
    (hsharp : 2 ^ (T + S + 2) < 3 ^ (T + 1) * (2 * a_0 + 1)) :
    17 * S ≤ 10 * T + 17 * W + 9 := by
  have hpow17 := pow_strict_mono_left (by decide : 1 ≤ 17) hsharp
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have h2a0_17 : (2 * a_0 + 1) ^ 17 ≤ (2 ^ (W + 1)) ^ 17 :=
    pow_le_pow_left_nat h2a0
  have h3_17 := three_pow_succ_pow_seventeen_lt_two_pow T
  have hlhs : (2 ^ (T + S + 2)) ^ 17 = 2 ^ (17 * T + 17 * S + 34) := by
    rw [← Nat.pow_mul]
    congr 1
    omega
  have hrhs_le :
      (3 ^ (T + 1) * (2 * a_0 + 1)) ^ 17 < 2 ^ (27 * T + 17 * W + 44) := by
    rw [Nat.mul_pow]
    have hpos : 0 < (2 * a_0 + 1) ^ 17 := Nat.pow_pos (by omega)
    have h1 :
        (3 ^ (T + 1)) ^ 17 * (2 * a_0 + 1) ^ 17 <
          2 ^ (27 * T + 27) * (2 * a_0 + 1) ^ 17 :=
      Nat.mul_lt_mul_of_pos_right h3_17 hpos
    have h2 :
        2 ^ (27 * T + 27) * (2 * a_0 + 1) ^ 17 ≤
          2 ^ (27 * T + 27) * (2 ^ (W + 1)) ^ 17 :=
      Nat.mul_le_mul_left _ h2a0_17
    have h3 :
        2 ^ (27 * T + 27) * (2 ^ (W + 1)) ^ 17 = 2 ^ (27 * T + 17 * W + 44) := by
      rw [← Nat.pow_mul, ← Nat.pow_add]
      congr 1
      omega
    rw [h3] at h2
    exact lt_of_lt_of_le h1 h2
  rw [hlhs] at hpow17
  have hexp := exp_lt_of_two_pow_lt (lt_trans hpow17 hrhs_le)
  omega

/-- **The $5:3$ Weighted Repeated-Subword Step Cutoff (`weighted_five_three_repeated_subword_cutoff`)**:
Along any `ValidBlockChain a_0 s u K` with `a_0 < 2^W` and `0 < integerSlack s r2`,
any `1 ≤ L`-block subword repeating at `r1 < r2` (`r2 + (L - 1) < K`) satisfies:
`5 * blockSteps (shiftSeq s r1) L ≤ 3 * blockSteps s r2 + 5 * W + 2`. -/
theorem weighted_five_three_repeated_subword_cutoff
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    5 * blockSteps (shiftSeq s r1) L ≤ 3 * blockSteps s r2 + 5 * W + 2 :=
  five_three_cutoff_of_exp_bound ha0
    (sharpened_repeated_subword_linear_cutoff hL hr12 hr2L ha0 hchain hslack hmatch).1

/-- **The $17:10$ Weighted Repeated-Subword Step Cutoff (`weighted_seventeen_ten_repeated_subword_cutoff`)**:
Along any `ValidBlockChain a_0 s u K` with `a_0 < 2^W` and `0 < integerSlack s r2`,
any `1 ≤ L`-block subword repeating at `r1 < r2` (`r2 + (L - 1) < K`) satisfies:
`17 * blockSteps (shiftSeq s r1) L ≤ 10 * blockSteps s r2 + 17 * W + 9`. -/
theorem weighted_seventeen_ten_repeated_subword_cutoff
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    17 * blockSteps (shiftSeq s r1) L ≤ 10 * blockSteps s r2 + 17 * W + 9 :=
  seventeen_ten_cutoff_of_exp_bound ha0
    (sharpened_repeated_subword_linear_cutoff hL hr12 hr2L ha0 hchain hslack hmatch).1

/-- **Weighted $5:3$ Block-Count Cutoff (`weighted_five_three_block_count_cutoff`)**:
Under the surviving step-rate conditions (`∀ k < L, 2 ≤ s (r1 + k)` and
`s (r1 + k) = 2 → 6 ≤ s (r1 + k + 1)`), any repeated `L`-block subword satisfies:
`15 * L ≤ 3 * blockSteps s r2 + 5 * W + 7` and `5 * L ≤ blockSteps s r2 + 2 * W + 2`. -/
theorem weighted_five_three_block_count_cutoff
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hge2 : ∀ k < L, 2 ≤ s (r1 + k))
    (h2to6 : ∀ k < L, s (r1 + k) = 2 → 6 ≤ s (r1 + k + 1))
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    15 * L ≤ 3 * blockSteps s r2 + 5 * W + 7 ∧
      5 * L ≤ blockSteps s r2 + 2 * W + 2 := by
  have hw :=
    weighted_five_three_repeated_subword_cutoff hL hr12 hr2L ha0 hchain hslack hmatch
  have hrate :=
    (three_mul_le_blockSteps_add_one (shiftSeq s r1) L
      (fun k hk => by simpa [shiftSeq] using hge2 k hk)
      (fun k hk hsk => by
        have h := h2to6 k hk (by simpa [shiftSeq] using hsk)
        simpa [shiftSeq, Nat.add_assoc] using h)).1
  omega

/-- **Weighted $17:10$ Block-Count Cutoff (`weighted_seventeen_ten_block_count_cutoff`)**:
Under the surviving step-rate conditions, any repeated `L`-block subword satisfies:
`51 * L ≤ 10 * blockSteps s r2 + 17 * W + 26`. -/
theorem weighted_seventeen_ten_block_count_cutoff
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hge2 : ∀ k < L, 2 ≤ s (r1 + k))
    (h2to6 : ∀ k < L, s (r1 + k) = 2 → 6 ≤ s (r1 + k + 1))
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    51 * L ≤ 10 * blockSteps s r2 + 17 * W + 26 := by
  have hw :=
    weighted_seventeen_ten_repeated_subword_cutoff hL hr12 hr2L ha0 hchain hslack hmatch
  have hrate :=
    (three_mul_le_blockSteps_add_one (shiftSeq s r1) L
      (fun k hk => by simpa [shiftSeq] using hge2 k hk)
      (fun k hk hsk => by
        have h := h2to6 k hk (by simpa [shiftSeq] using hsk)
        simpa [shiftSeq, Nat.add_assoc] using h)).1
  omega

/-! ## 2. Finite Pigeonhole Principle on Subword Complexity -/

/-- **Finite Pigeonhole Principle for Subword Complexity (`exists_repeated_subword_of_pattern_classifier`)**:
If a sequence `s : ℕ → ℕ` has at most `C` distinct length-`L` subwords among the
first `C + 1` origins `0, 1, ..., C` (witnessed by a pattern classifier
`pat : ℕ → Fin C` such that `pat r1 = pat r2` implies the length-`L` windows at
`r1` and `r2` agree), then there exist `r1 < r2 ≤ C` with
`∀ i < L, s (r1 + i) = s (r2 + i)`. -/
theorem exists_repeated_subword_of_pattern_classifier
    (s : ℕ → ℕ) (L C : ℕ) (pat : ℕ → Fin C)
    (hpat : ∀ r1 ≤ C, ∀ r2 ≤ C, pat r1 = pat r2 → ∀ i < L, s (r1 + i) = s (r2 + i)) :
    ∃ r1 r2 : ℕ, r1 < r2 ∧ r2 ≤ C ∧ ∀ i < L, s (r1 + i) = s (r2 + i) := by
  have hcard : Fintype.card (Fin C) < Fintype.card (Fin (C + 1)) := by
    simp
  obtain ⟨a, b, hab, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun x : Fin (C + 1) => pat x.val) hcard
  have hval_ne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · refine ⟨a.val, b.val, hlt, Nat.le_of_lt_succ b.isLt, ?_⟩
    exact hpat a.val (Nat.le_of_lt_succ a.isLt) b.val (Nat.le_of_lt_succ b.isLt) heq
  · refine ⟨b.val, a.val, hgt, Nat.le_of_lt_succ a.isLt, ?_⟩
    exact hpat b.val (Nat.le_of_lt_succ b.isLt) a.val (Nat.le_of_lt_succ a.isLt) heq.symm

/-- **Sturmian Complexity Specialization (`exists_repeated_subword_of_sturmian_complexity`)**:
For any Sturmian-complexity sequence (`C = L + 1` patterns of length `L`), there
exist `r1 < r2 ≤ L + 1` whose length-`L` subwords coincide. -/
theorem exists_repeated_subword_of_sturmian_complexity
    (s : ℕ → ℕ) (L : ℕ) (pat : ℕ → Fin (L + 1))
    (hpat : ∀ r1 ≤ L + 1, ∀ r2 ≤ L + 1, pat r1 = pat r2 → ∀ i < L, s (r1 + i) = s (r2 + i)) :
    ∃ r1 r2 : ℕ, r1 < r2 ∧ r2 ≤ L + 1 ∧ ∀ i < L, s (r1 + i) = s (r2 + i) :=
  exists_repeated_subword_of_pattern_classifier s L (L + 1) pat hpat

/-! ## 3. Unconditional Exclusion of Ceiling-Saturated Sturmian & Balanced Aperiodic Classes -/

private theorem blockSteps_ge_mul_of_lower_bound (s : ℕ → ℕ) (m b : ℕ)
    (hlo : ∀ k < m, b ≤ s k) :
    b * m ≤ blockSteps s m := by
  induction m with
  | zero => simp [blockSteps]
  | succ m ih =>
      have ihm := ih (fun k hk => hlo k (by omega))
      have hsm := hlo m (Nat.lt_succ_self m)
      simp only [blockSteps]
      calc
        b * (m + 1) = b * m + b := by ring
        _ ≤ blockSteps s m + s m := Nat.add_le_add ihm hsm

private theorem blockSteps_le_mul_of_upper_bound (s : ℕ → ℕ) (m B : ℕ)
    (hhi : ∀ k < m, s k ≤ B) :
    blockSteps s m ≤ B * m := by
  induction m with
  | zero => simp [blockSteps]
  | succ m ih =>
      have ihm := ih (fun k hk => hhi k (by omega))
      have hsm := hhi m (Nat.lt_succ_self m)
      simp only [blockSteps]
      calc
        blockSteps s m + s m ≤ B * m + B := Nat.add_le_add ihm hsm
        _ = B * (m + 1) := by ring

/-- **Exclusion of Aperiodic Ceiling-Saturated `{3, 4}` Sequences of Complexity `L + C_0`
(`aperiodic_sturmian_three_four_exclusion`)**:
Suppose `s : ℕ → ℕ` satisfies `3 ≤ s k ≤ 4` for all `k` (so `minSlack s m = 2^T(m) > 0`
forever, and archimedean companion bounds never fail) and has subword complexity
at most `L + C_0` at window length `1 ≤ L`. Then along any `ValidBlockChain a_0 s u K`
with `a_0 < 2^W` and `2 * L + C_0 ≤ K`, the window length `L` is unconditionally
bounded by:
`3 * L ≤ 12 * C_0 + 5 * W + 2`
(and for Sturmian complexity `C_0 = 1`, `3 * L ≤ 5 * W + 14`). -/
theorem aperiodic_sturmian_three_four_exclusion
    {a_0 W L C_0 K : ℕ} {s u : ℕ → ℕ}
    (hL : 1 ≤ L) (hK : 2 * L + C_0 ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_bounds : ∀ k < K, 3 ≤ s k ∧ s k ≤ 4)
    (pat : ℕ → Fin (L + C_0))
    (hpat : ∀ r1 ≤ L + C_0, ∀ r2 ≤ L + C_0,
      pat r1 = pat r2 → ∀ i < L, s (r1 + i) = s (r2 + i)) :
    3 * L ≤ 12 * C_0 + 5 * W + 2 := by
  obtain ⟨r1, r2, hr12, hr2C, hmatch⟩ :=
    exists_repeated_subword_of_pattern_classifier s L (L + C_0) pat hpat
  have hr2L : r2 + (L - 1) < K := by omega
  have hslack_r2 : 0 < integerSlack s r2 := by
    have h3 : ∀ k < r2, 3 ≤ s k := fun k hk => (hs_bounds k (by omega)).1
    have h := (all_shifted_slacks_pos_of_three_le s r2 h3).2 0 (Nat.zero_le r2)
    have hshift0 : shiftSeq s 0 = s := by funext k; simp [shiftSeq]
    rwa [hshift0, Nat.sub_zero] at h
  have hw :=
    weighted_five_three_repeated_subword_cutoff hL hr12 hr2L ha0 hchain hslack_r2 hmatch
  have hS_ge : 3 * L ≤ blockSteps (shiftSeq s r1) L := by
    apply blockSteps_ge_mul_of_lower_bound (shiftSeq s r1) L 3
    intro k hk
    simpa [shiftSeq] using (hs_bounds (r1 + k) (by omega)).1
  have hT_le : blockSteps s r2 ≤ 4 * (L + C_0) := by
    have h1 : blockSteps s r2 ≤ 4 * r2 := by
      apply blockSteps_le_mul_of_upper_bound s r2 4
      intro k hk
      exact (hs_bounds k (by omega)).2
    omega
  omega

/-- **Exclusion of Aperiodic Ceiling-Saturated `[3, 5]` Sequences of Complexity `L + C_0`
(`aperiodic_sturmian_three_five_exclusion`)**:
Suppose `s : ℕ → ℕ` satisfies `3 ≤ s k ≤ 5` for all `k` (ceiling-saturated) and
has subword complexity at most `L + C_0` at window length `1 ≤ L`. Then along any
`ValidBlockChain a_0 s u K` with `a_0 < 2^W` and `2 * L + C_0 ≤ K`, the window
length `L` is unconditionally bounded by:
`L ≤ 50 * C_0 + 17 * W + 9`. -/
theorem aperiodic_sturmian_three_five_exclusion
    {a_0 W L C_0 K : ℕ} {s u : ℕ → ℕ}
    (hL : 1 ≤ L) (hK : 2 * L + C_0 ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_bounds : ∀ k < K, 3 ≤ s k ∧ s k ≤ 5)
    (pat : ℕ → Fin (L + C_0))
    (hpat : ∀ r1 ≤ L + C_0, ∀ r2 ≤ L + C_0,
      pat r1 = pat r2 → ∀ i < L, s (r1 + i) = s (r2 + i)) :
    L ≤ 50 * C_0 + 17 * W + 9 := by
  obtain ⟨r1, r2, hr12, hr2C, hmatch⟩ :=
    exists_repeated_subword_of_pattern_classifier s L (L + C_0) pat hpat
  have hr2L : r2 + (L - 1) < K := by omega
  have hslack_r2 : 0 < integerSlack s r2 := by
    have h3 : ∀ k < r2, 3 ≤ s k := fun k hk => (hs_bounds k (by omega)).1
    have h := (all_shifted_slacks_pos_of_three_le s r2 h3).2 0 (Nat.zero_le r2)
    have hshift0 : shiftSeq s 0 = s := by funext k; simp [shiftSeq]
    rwa [hshift0, Nat.sub_zero] at h
  have hw :=
    weighted_seventeen_ten_repeated_subword_cutoff hL hr12 hr2L ha0 hchain hslack_r2 hmatch
  have hS_ge : 3 * L ≤ blockSteps (shiftSeq s r1) L := by
    apply blockSteps_ge_mul_of_lower_bound (shiftSeq s r1) L 3
    intro k hk
    simpa [shiftSeq] using (hs_bounds (r1 + k) (by omega)).1
  have hT_le : blockSteps s r2 ≤ 5 * (L + C_0) := by
    have h1 : blockSteps s r2 ≤ 5 * r2 := by
      apply blockSteps_le_mul_of_upper_bound s r2 5
      intro k hk
      exact (hs_bounds k (by omega)).2
    omega
  omega

/-- Downward persistence of `minSlack` positivity: if `0 < minSlack s m` and
`r ≤ m`, then `0 < minSlack s r` and `0 < integerSlack s r`. -/
theorem minSlack_pos_of_le (s : ℕ → ℕ) {r m : ℕ} (hrm : r ≤ m)
    (hpos : 0 < minSlack s m) :
    0 < minSlack s r ∧ 0 < integerSlack s r := by
  have hmin_r : 0 < minSlack s r := by
    induction m with
    | zero =>
        have hr0 : r = 0 := by omega
        subst hr0
        exact hpos
    | succ m ih =>
        rcases Nat.eq_or_lt_of_le hrm with rfl | hlt
        · exact hpos
        · apply ih (by omega)
          have hstep := minSlack_succ_le_step s m
          have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by positivity
          have h3pos : (0 : ℤ) < (3 : ℤ) ^ (s m) := by positivity
          have hmul_pos : (0 : ℤ) < (3 : ℤ) ^ (s m) * minSlack s m := by linarith
          exact pos_of_mul_pos_right hmul_pos (le_of_lt h3pos)
  have hall := (minSlack_pos_iff_all_shifted_pos s r).mp hmin_r 0 (Nat.zero_le r)
  have hshift0 : shiftSeq s 0 = s := by
    funext k
    simp [shiftSeq]
  rw [hshift0, Nat.sub_zero] at hall
  exact ⟨hmin_r, hall⟩

/-- **General Sub-Critical Balanced Complexity Exclusion (`balanced_subcritical_complexity_exclusion`)**:
For **any** average block length (arbitrarily large), suppose a surviving block
chain `ValidBlockChain a_0 s u K` (`a_0 < 2^W`, `0 < minSlack s C`, `C + L ≤ K`)
has subword complexity `C` at window length `1 ≤ L` and satisfies the Sub-Critical
Balanced Complexity Condition with margin `1 ≤ δ ≤ 17` and discrepancy `D_0`:
`∀ r1 < r2 ≤ C, 10 * blockSteps s r2 ≤ (17 - δ) * blockSteps (shiftSeq s r1) L + D_0`
(which holds whenever cumulative steps are balanced `T(n) = λ n + O(1)` and
`p(L) ≤ κ L + O(1)` with `κ ≤ (17 - δ) / 10 < 1.7`).
Then:
`3 * δ * L ≤ D_0 + 17 * W + 9 + δ`. -/
theorem balanced_subcritical_complexity_exclusion
    {a_0 W L C K δ D_0 : ℕ} {s u : ℕ → ℕ}
    (hL : 1 ≤ L) (hδ1 : 1 ≤ δ) (hδ17 : δ ≤ 17) (hK : C + L ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hminSlack : 0 < minSlack s C)
    (hge2 : ∀ k < K, 2 ≤ s k)
    (h2to6 : ∀ k, k + 1 < K → s k = 2 → 6 ≤ s (k + 1))
    (pat : ℕ → Fin C)
    (hpat : ∀ r1 ≤ C, ∀ r2 ≤ C, pat r1 = pat r2 → ∀ i < L, s (r1 + i) = s (r2 + i))
    (hbal : ∀ r1 r2 : ℕ, r1 < r2 → r2 ≤ C →
      10 * blockSteps s r2 ≤ (17 - δ) * blockSteps (shiftSeq s r1) L + D_0) :
    3 * δ * L ≤ D_0 + 17 * W + 9 + δ := by
  obtain ⟨r1, r2, hr12, hr2C, hmatch⟩ :=
    exists_repeated_subword_of_pattern_classifier s L C pat hpat
  have hr2L : r2 + (L - 1) < K := by omega
  have hslack_r2 : 0 < integerSlack s r2 :=
    (minSlack_pos_of_le s hr2C hminSlack).2
  have hw :=
    weighted_seventeen_ten_repeated_subword_cutoff hL hr12 hr2L ha0 hchain hslack_r2 hmatch
  have hbal_r := hbal r1 r2 hr12 hr2C
  have hrate : 3 * L ≤ blockSteps (shiftSeq s r1) L + 1 :=
    (three_mul_le_blockSteps_add_one (shiftSeq s r1) L
      (fun k hk => by simpa [shiftSeq] using hge2 (r1 + k) (by omega))
      (fun k hk hsk => by
        have h := h2to6 (r1 + k) (by omega) (by simpa [shiftSeq] using hsk)
        simpa [shiftSeq, Nat.add_assoc] using h)).1
  generalize blockSteps (shiftSeq s r1) L = S at hw hbal_r hrate
  generalize blockSteps s r2 = T at hw hbal_r
  have hS_split : 17 * S = (17 - δ) * S + δ * S := by
    have h17 : 17 = (17 - δ) + δ := by omega
    conv_lhs => rw [h17, Nat.add_mul]
  have hδS : δ * S ≤ D_0 + 17 * W + 9 := by omega
  have hmul_rate : δ * (3 * L) ≤ δ * (S + 1) := Nat.mul_le_mul_left δ hrate
  have hring : δ * (3 * L) = 3 * δ * L ∧ δ * (S + 1) = δ * S + δ :=
    ⟨by ring, by ring⟩
  omega

end Mahler.SturmianComplexityExclusion
