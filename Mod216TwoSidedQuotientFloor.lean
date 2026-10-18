import ThreeAdicValuationConservation

/-!
# The Modulo-54 & Modulo-216 Two-Sided CRT Sieves (`65 ≤ u k` & `125 ≤ u k`)

This module formalizes Paths 12 & 13 (Modules 113–114): combining the backward
Mod-27 lock (`3 ≤ s (k - 1)`) with forward 2-adic valuation locks (`mod 2`,
`mod 4`, `mod 8`, `mod 64`) and 2-step predecessor obstructions:

1. **Path 12 — Exact Modulo-54 (`27 × 2`) Quotient Locks for `s k ∈ {3, 4, 5, 6}`
   (`mod_54_quotient_locks_of_three_le_prev`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ k < K`) with `3 ≤ s (k - 1)`,
   combining `(2^(s k) * u k) % 27 = 1` with `u k % 2 = 1` locks `u k % 54`:
   - `s k = 3 → u k % 54 = 17`,
   - `s k = 4 → u k % 54 = 49`,
   - `s k = 5 → u k % 54 = 11`,
   - `s k = 6 → u k % 54 = 19`.
2. **Path 12 — Elimination of Minimal Modulo-54 Representatives & the `65 ≤ u k` Floor
   (`mod_54_minimal_representatives_eliminated`, `sixty_five_le_u_on_bounded_blocks`)**:
   Along a surviving trajectory (`2 ≤ k`, `k + 2 < K`, `2 ≤ s (k - 2)`, `3 ≤ s (k - 1)`,
   `2 ≤ s (k + 1)`, and `s (k + 1) = 2 → 6 ≤ s (k + 2)`):
   - `s k = 3 → u k ≠ 17 ∧ 71 ≤ u k` (since `u k = 17` forces `s (k + 1) = 2, u (k + 1) = 115`,
     which fails `64 ∣ (9 * 115 + 1 = 1036)`),
   - `s k = 4 → u k ≠ 49 ∧ 103 ≤ u k` (since `81 * 49 + 1 = 3970` fails `4 ∣ 3970`),
   - `s k = 5 → u k ≠ 11 ∧ 65 ≤ u k` (since `243 * 11 + 1 = 2674` fails `4 ∣ 2674`),
   - `s k = 6 → u k ≠ 19 ∧ 73 ≤ u k` (since `3^(s (k - 1)) * u (k - 1) = 64 * 19 - 1 = 1215 = 3^5 * 5`
     forces `s (k - 1) = 5` and `u (k - 1) = 5`, violating `s (k - 1) % 6 = 1`).
   - Consequently, across all `2 ≤ s k ≤ 6` (combining `1735 ≤ u k` at `s k = 2`),
     we have **`65 ≤ u k`**.
3. **Path 13 — The Modulo-216 (`27 × 8`) Ceiling-Saturated Classifier & `103×` Coasting Bound
   (`mod_216_ceiling_saturated_quotient_locks`,
   `coasting_103_mul_single_block_bound`)**:
   Whenever `1 ≤ k`, `k + 1 < K`, `3 ≤ s (k - 1)`, and `3 ≤ s (k + 1)`:
   - `s k = 3 → u k % 216 = 125 ∧ 125 ≤ u k`,
   - `s k = 4 → u k % 216 = 103 ∧ 103 ≤ u k`,
   - `s k = 5 → u k % 216 = 173 ∧ 173 ≤ u k`,
   - `s k = 6 → u k % 216 = 127 ∧ 127 ≤ u k`,
   - Across all `3 ≤ s k ≤ 6`: **`103 ≤ u k`** and
     `103 * 2^(blockSteps s (k + 1) + 1) < 3^(blockSteps s k + 1) * (2 * a_0 + 1)`.
-/

namespace Mahler.Mod216QuotientFloor

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

/-! ## 1. Path 12: Exact Modulo-54 (`27 × 2`) Quotient Locks -/

private theorem mod_54_of_mul_mod_27_and_odd {u : ℕ}
    (hodd : u % 2 = 1) :
    ((8 * u) % 27 = 1 → u % 54 = 17) ∧
      ((16 * u) % 27 = 1 → u % 54 = 49) ∧
      ((32 * u) % 27 = 1 → u % 54 = 11) ∧
      ((64 * u) % 27 = 1 → u % 54 = 19) := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exact Modulo-54 Quotient Locks (`mod_54_quotient_locks_of_three_le_prev`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ k < K`) with `3 ≤ s (k - 1)`:
- `s k = 3 → u k % 54 = 17`,
- `s k = 4 → u k % 54 = 49`,
- `s k = 5 → u k % 54 = 11`,
- `s k = 6 → u k % 54 = 19`. -/
theorem mod_54_quotient_locks_of_three_le_prev
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hkK : k < K) (hchain : ValidBlockChain a_0 s u K)
    (hs_prev : 3 ≤ s (k - 1)) :
    (s k = 3 → u k % 54 = 17) ∧
      (s k = 4 → u k % 54 = 49) ∧
      (s k = 5 → u k % 54 = 11) ∧
      (s k = 6 → u k % 54 = 19) := by
  have hrec := coprime_quotient_recurrence (k := k - 1) (by omega) hchain
  have hk_idx : k - 1 + 1 = k := by omega
  rw [hk_idx] at hrec
  have h27_dvd : 27 ∣ 3 ^ (s (k - 1)) * u (k - 1) := by
    have hpow : 3 ^ 3 ∣ 3 ^ (s (k - 1)) := Nat.pow_dvd_pow 3 hs_prev
    exact dvd_mul_of_dvd_left (by simpa using hpow) (u (k - 1))
  rcases h27_dvd with ⟨q27, hq27⟩
  have hmod27 : (2 ^ (s k) * u k) % 27 = 1 := by
    rw [hrec, hq27]
    omega
  have hodd : u k % 2 = 1 := (hchain k hkK).2.1
  have hcrt := mod_54_of_mul_mod_27_and_odd hodd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs3; rw [hs3] at hmod27; exact hcrt.1 hmod27
  · intro hs4; rw [hs4] at hmod27; exact hcrt.2.1 hmod27
  · intro hs5; rw [hs5] at hmod27; exact hcrt.2.2.1 hmod27
  · intro hs6; rw [hs6] at hmod27; exact hcrt.2.2.2 hmod27

/-! ## 2. Elimination of Minimal Modulo-54 Representatives & the `65 ≤ u k` Floor -/

/-- **Elimination of Minimal Modulo-54 Representatives (`mod_54_minimal_representatives_eliminated`)**:
Along any `ValidBlockChain a_0 s u K` with `2 ≤ k`, `k + 2 < K`, `2 ≤ s (k - 2)`,
`3 ≤ s (k - 1)`, `2 ≤ s (k + 1)`, and `(s (k + 1) = 2 → 6 ≤ s (k + 2))`:
1. `s k = 3 → u k ≠ 17 ∧ 71 ≤ u k`,
2. `s k = 4 → u k ≠ 49 ∧ 103 ≤ u k`,
3. `s k = 5 → u k ≠ 11 ∧ 65 ≤ u k`,
4. `s k = 6 → u k ≠ 19 ∧ 73 ≤ u k`. -/
theorem mod_54_minimal_representatives_eliminated
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2_lo : 2 ≤ k) (hk2_hi : k + 2 < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_prev2 : 2 ≤ s (k - 2)) (hs_prev1 : 3 ≤ s (k - 1))
    (hs_next1 : 2 ≤ s (k + 1)) (hs_next2 : s (k + 1) = 2 → 6 ≤ s (k + 2)) :
    (s k = 3 → u k ≠ 17 ∧ 71 ≤ u k) ∧
      (s k = 4 → u k ≠ 49 ∧ 103 ≤ u k) ∧
      (s k = 5 → u k ≠ 11 ∧ 65 ≤ u k) ∧
      (s k = 6 → u k ≠ 19 ∧ 73 ≤ u k) := by
  rcases mod_54_quotient_locks_of_three_le_prev (by omega) (by omega) hchain hs_prev1 with
    ⟨hm3, hm4, hm5, hm6⟩
  have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hrec2 : 2 ^ (s (k + 2)) * u (k + 2) = 3 ^ (s (k + 1)) * u (k + 1) + 1 :=
    coprime_quotient_recurrence (by omega : (k + 1) + 1 < K) hchain
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs3
    have hmod54 := hm3 hs3
    have hne17 : u k ≠ 17 := by
      intro hu17
      rw [hs3, hu17] at hrec1
      have huk1_odd : u (k + 1) % 2 = 1 := (hchain (k + 1) (by omega)).2.1
      have hs1_eq2 : s (k + 1) = 2 := by
        by_contra hne2
        have hge3 : 3 ≤ s (k + 1) := by omega
        have hdvd8 : 8 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
          dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge3) (u (k + 1))
        rcases hdvd8 with ⟨q8, hq8⟩
        omega
      rw [hs1_eq2] at hrec1 hrec2
      have huk1_eq : u (k + 1) = 115 := by omega
      have hs2_ge6 : 6 ≤ s (k + 2) := hs_next2 hs1_eq2
      have hdvd64 : 64 ∣ 2 ^ (s (k + 2)) * u (k + 2) :=
        dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hs2_ge6) (u (k + 2))
      rcases hdvd64 with ⟨q64, hq64⟩
      rw [huk1_eq, hq64] at hrec2
      omega
    exact ⟨hne17, by omega⟩
  · intro hs4
    have hmod54 := hm4 hs4
    have hne49 : u k ≠ 49 := by
      intro hu49
      rw [hs4, hu49] at hrec1
      have hdvd4 : 4 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
        dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hs_next1) (u (k + 1))
      rcases hdvd4 with ⟨q4, hq4⟩
      omega
    exact ⟨hne49, by omega⟩
  · intro hs5
    have hmod54 := hm5 hs5
    have hne11 : u k ≠ 11 := by
      intro hu11
      rw [hs5, hu11] at hrec1
      have hdvd4 : 4 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
        dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hs_next1) (u (k + 1))
      rcases hdvd4 with ⟨q4, hq4⟩
      omega
    exact ⟨hne11, by omega⟩
  · intro hs6
    have hmod54 := hm6 hs6
    have hne19 : u k ≠ 19 := by
      intro hu19
      have hrec0 := coprime_quotient_recurrence (k := k - 1) (by omega) hchain
      have hk_idx : k - 1 + 1 = k := by omega
      rw [hk_idx, hs6, hu19] at hrec0
      have hprod_eq : 3 ^ (s (k - 1)) * u (k - 1) = 1215 := by omega
      have hu_cop6 := u_coprime_six_of_validBlockChain (by omega : k - 1 < K) hchain
      have hu_mod3 : u (k - 1) % 3 ≠ 0 := hu_cop6.2.1
      have hs_prev_le5 : s (k - 1) ≤ 5 := by
        by_contra hgt5
        rcases Nat.eq_or_lt_of_le (show 6 ≤ s (k - 1) by omega) with h6 | hge7
        · rw [← h6] at hprod_eq
          omega
        · have hge2187 : 2187 ≤ 3 ^ (s (k - 1)) := by
            have h := Nat.pow_le_pow_right (by decide : 0 < 3) (show 7 ≤ s (k - 1) by omega)
            simpa using h
          have hu_odd : u (k - 1) % 2 = 1 := hu_cop6.1
          have hu_pos : 1 ≤ u (k - 1) := by omega
          nlinarith
      have hs_cases : s (k - 1) = 3 ∨ s (k - 1) = 4 ∨ s (k - 1) = 5 := by omega
      rcases hs_cases with h3 | h4 | h5
      · rw [h3] at hprod_eq
        have : u (k - 1) = 45 := by omega
        omega
      · rw [h4] at hprod_eq
        have : u (k - 1) = 15 := by omega
        omega
      · rw [h5] at hprod_eq
        have hu5 : u (k - 1) = 5 := by omega
        have hlock5 :=
          (u_eq_five_or_seven_mod_six_locks (k := k - 1) (by omega) (by omega)
            hchain (by simpa [show k - 1 - 1 = k - 2 by omega] using hs_prev2)).1 hu5
        omega
    exact ⟨hne19, by omega⟩

/-- **The `65 ≤ u k` Bounded-Block Floor (`sixty_five_le_u_on_bounded_blocks`)**:
Under the hypotheses of `mod_54_minimal_representatives_eliminated`, for every
block length `2 ≤ s k ≤ 6`, we have `65 ≤ u k`. -/
theorem sixty_five_le_u_on_bounded_blocks
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2_lo : 2 ≤ k) (hk2_hi : k + 2 < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_prev2 : 2 ≤ s (k - 2)) (hs_prev1 : 3 ≤ s (k - 1))
    (hs_next1 : 2 ≤ s (k + 1)) (hs_next2 : s (k + 1) = 2 → 6 ≤ s (k + 2))
    (hsk_lo : 2 ≤ s k) (hsk_hi : s k ≤ 6) :
    65 ≤ u k := by
  have helim :=
    mod_54_minimal_representatives_eliminated hk2_lo hk2_hi hchain hs_prev2 hs_prev1 hs_next1 hs_next2
  have hcases : s k = 2 ∨ s k = 3 ∨ s k = 4 ∨ s k = 5 ∨ s k = 6 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6
  · have hrec0 := coprime_quotient_recurrence (k := k - 1) (by omega) hchain
    have hk_idx : k - 1 + 1 = k := by omega
    rw [hk_idx, h2] at hrec0
    have h27_dvd : 27 ∣ 3 ^ (s (k - 1)) * u (k - 1) := by
      have hpow : 3 ^ 3 ∣ 3 ^ (s (k - 1)) := Nat.pow_dvd_pow 3 hs_prev1
      exact dvd_mul_of_dvd_left (by simpa using hpow) (u (k - 1))
    rcases h27_dvd with ⟨q27, hq27⟩
    rw [hq27] at hrec0
    have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
    rw [h2] at hrec1
    have hdvd4 : 4 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hs_next1) (u (k + 1))
    rcases hdvd4 with ⟨q4, hq4⟩
    rw [hq4] at hrec1
    have hne7 : u k ≠ 7 := by
      have h :=
        post_two_u_ne_seven_of_pos_index (k := k - 1) (by omega) (by omega)
          hchain hs_prev1 (by simpa [hk_idx] using h2)
      simpa [hk_idx] using h
    omega
  · have h := (helim.1 h3).2; omega
  · have h := (helim.2.1 h4).2; omega
  · exact (helim.2.2.1 h5).2
  · have h := (helim.2.2.2 h6).2; omega

/-! ## 3. Path 13: The Modulo-216 (`27 × 8`) Ceiling-Saturated Classifier & `103×` Coasting Bound -/

private theorem crt_27_and_8 {u : ℕ} :
    (u % 27 = 17 → u % 8 = 5 → u % 216 = 125) ∧
      (u % 27 = 22 → u % 8 = 7 → u % 216 = 103) ∧
      (u % 27 = 11 → u % 8 = 5 → u % 216 = 173) ∧
      (u % 27 = 19 → u % 8 = 7 → u % 216 = 127) := by
  refine ⟨by omega, by omega, by omega, by omega⟩

private theorem mod_27_and_8_from_products {u : ℕ} :
    ((8 * u) % 27 = 1 → u % 27 = 17) ∧
      ((16 * u) % 27 = 1 → u % 27 = 22) ∧
      ((32 * u) % 27 = 1 → u % 27 = 11) ∧
      ((64 * u) % 27 = 1 → u % 27 = 19) ∧
      ((27 * u + 1) % 8 = 0 → u % 8 = 5) ∧
      ((81 * u + 1) % 8 = 0 → u % 8 = 7) ∧
      ((243 * u + 1) % 8 = 0 → u % 8 = 5) ∧
      ((729 * u + 1) % 8 = 0 → u % 8 = 7) := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem le_of_mod_216_eq {u r : ℕ} (hm : u % 216 = r) : r ≤ u := by
  omega

/-- **Modulo-216 (`27 × 8`) Ceiling-Saturated Quotient Classifier
(`mod_216_ceiling_saturated_quotient_locks`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ k`, `k + 1 < K`) with `3 ≤ s (k - 1)`
and `3 ≤ s (k + 1)`:
- `s k = 3 → u k % 216 = 125 ∧ 125 ≤ u k`,
- `s k = 4 → u k % 216 = 103 ∧ 103 ≤ u k`,
- `s k = 5 → u k % 216 = 173 ∧ 173 ≤ u k`,
- `s k = 6 → u k % 216 = 127 ∧ 127 ≤ u k`, and
- `(3 ≤ s k ∧ s k ≤ 6) → 103 ≤ u k`. -/
theorem mod_216_ceiling_saturated_quotient_locks
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk1 : k + 1 < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_prev : 3 ≤ s (k - 1)) (hs_next : 3 ≤ s (k + 1)) :
    (s k = 3 → u k % 216 = 125 ∧ 125 ≤ u k) ∧
      (s k = 4 → u k % 216 = 103 ∧ 103 ≤ u k) ∧
      (s k = 5 → u k % 216 = 173 ∧ 173 ≤ u k) ∧
      (s k = 6 → u k % 216 = 127 ∧ 127 ≤ u k) ∧
      (3 ≤ s k ∧ s k ≤ 6 → 103 ≤ u k) := by
  have hrec0 := coprime_quotient_recurrence (k := k - 1) (by omega) hchain
  have hk_idx : k - 1 + 1 = k := by omega
  rw [hk_idx] at hrec0
  have h27_dvd : 27 ∣ 3 ^ (s (k - 1)) * u (k - 1) := by
    have hpow : 3 ^ 3 ∣ 3 ^ (s (k - 1)) := Nat.pow_dvd_pow 3 hs_prev
    exact dvd_mul_of_dvd_left (by simpa using hpow) (u (k - 1))
  rcases h27_dvd with ⟨q27, hq27⟩
  have hmod27 : (2 ^ (s k) * u k) % 27 = 1 := by
    rw [hrec0, hq27]
    omega
  have hrec1 := coprime_quotient_recurrence hk1 hchain
  have h8_dvd : 8 ∣ 2 ^ (s (k + 1)) * u (k + 1) := by
    have hpow : 2 ^ 3 ∣ 2 ^ (s (k + 1)) := Nat.pow_dvd_pow 2 hs_next
    exact dvd_mul_of_dvd_left (by simpa using hpow) (u (k + 1))
  rcases h8_dvd with ⟨q8, hq8⟩
  have hmod8 : (3 ^ (s k) * u k + 1) % 8 = 0 := by
    rw [← hrec1, hq8]
    omega
  have hcrt := crt_27_and_8 (u := u k)
  have hprods := mod_27_and_8_from_products (u := u k)
  have hp3 : s k = 3 → u k % 216 = 125 ∧ 125 ≤ u k := by
    intro hs3
    rw [hs3] at hmod27 hmod8
    have hm := hcrt.1 (hprods.1 hmod27) (hprods.2.2.2.2.1 hmod8)
    exact ⟨hm, le_of_mod_216_eq hm⟩
  have hp4 : s k = 4 → u k % 216 = 103 ∧ 103 ≤ u k := by
    intro hs4
    rw [hs4] at hmod27 hmod8
    have hm := hcrt.2.1 (hprods.2.1 hmod27) (hprods.2.2.2.2.2.1 hmod8)
    exact ⟨hm, le_of_mod_216_eq hm⟩
  have hp5 : s k = 5 → u k % 216 = 173 ∧ 173 ≤ u k := by
    intro hs5
    rw [hs5] at hmod27 hmod8
    have hm := hcrt.2.2.1 (hprods.2.2.1 hmod27) (hprods.2.2.2.2.2.2.1 hmod8)
    exact ⟨hm, le_of_mod_216_eq hm⟩
  have hp6 : s k = 6 → u k % 216 = 127 ∧ 127 ≤ u k := by
    intro hs6
    rw [hs6] at hmod27 hmod8
    have hm := hcrt.2.2.2 (hprods.2.2.2.1 hmod27) (hprods.2.2.2.2.2.2.2 hmod8)
    exact ⟨hm, le_of_mod_216_eq hm⟩
  refine ⟨hp3, hp4, hp5, hp6, ?_⟩
  rintro ⟨hlo, hhi⟩
  have hcases : s k = 3 ∨ s k = 4 ∨ s k = 5 ∨ s k = 6 := by omega
  rcases hcases with h3 | h4 | h5 | h6
  · exact Nat.le_trans (by decide : 103 ≤ 125) (hp3 h3).2
  · exact (hp4 h4).2
  · exact Nat.le_trans (by decide : 103 ≤ 173) (hp5 h5).2
  · exact Nat.le_trans (by decide : 103 ≤ 127) (hp6 h6).2

/-- **The `103×` Single-Block Coasting Bound (`coasting_103_mul_single_block_bound`)**:
Under the hypotheses of `mod_216_ceiling_saturated_quotient_locks`, if
`3 ≤ s k ≤ 6` and `0 < integerSlack s k`, then:
`103 * 2^(blockSteps s (k + 1) + 1) < 3^(blockSteps s k + 1) * (2 * a_0 + 1)`. -/
theorem coasting_103_mul_single_block_bound
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk1 : k + 1 < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_prev : 3 ≤ s (k - 1)) (hs_next : 3 ≤ s (k + 1))
    (hsk_lo : 3 ≤ s k) (hsk_hi : s k ≤ 6)
    (hpos : 0 < integerSlack s k) :
    103 * 2 ^ (blockSteps s (k + 1) + 1) <
      3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) := by
  have hu103 :=
    (mod_216_ceiling_saturated_quotient_locks hk_pos hk1 hchain hs_prev hs_next).2.2.2.2
      ⟨hsk_lo, hsk_hi⟩
  have horbit := integerSlack_eq_orbit_slack (by omega : k < K) hchain
  have horbit' :
      integerSlack s k =
        ((3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (k + 1) + 1) * u k : ℕ) : ℤ) := by
    rw [horbit]
    push_cast
    rfl
  have hlt :
      2 ^ (blockSteps s (k + 1) + 1) * u k <
        3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) := by
    omega
  have hle :
      103 * 2 ^ (blockSteps s (k + 1) + 1) ≤
        2 ^ (blockSteps s (k + 1) + 1) * u k := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hu103
  exact lt_of_le_of_lt hle hlt

end Mahler.Mod216QuotientFloor
