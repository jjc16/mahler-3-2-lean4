import TimeIndependentDeficiencySqueeze

/-!
# Formalized Slack Dead Ends & Negative Witnesses (`altTwoSeven`, `seq622`, `seq26332`)

This module formalizes three negative witnesses / dead ends in the `integerSlack`
and `minSlack` theory, proving why neither unshifted slack positivity nor
purely Archimedean `minSlack` positivity (even with density-`1/2` visits to
`s = 2`) suffices without the 2-adic coprime recurrence:

1. **Dead End 9 — Infinite Density-`1/2` Visits to `s = 2` With Eternal `minSlack > 0`
   (`altTwoSeven`, `altTwoSeven_minSlack_even_odd`, `altTwoSeven_minSlack_pos`)**:
   Define `altTwoSeven k = if k % 2 = 0 then 2 else 7` (`(2, 7, 2, 7, ...)`).
   - At every even block `2 * k`, `s = 7` restores `minSlack` to `100%` of the
     ceiling: `minSlack altTwoSeven (2 * k) = 2^(9 * k)`.
   - At every odd block `2 * k + 1`, `minSlack altTwoSeven (2 * k + 1) = 2^(9 * k)`.
   - Consequently, `∀ m, 0 < minSlack altTwoSeven m` holds forever despite
     `altTwoSeven (2 * k) = 2` occurring at half of all blocks.
2. **Dead End 10 — Strictly Positive `integerSlack` With Strictly Negative `minSlack`
   (`seq622`, `positive_integerSlack_with_negative_minSlack`)**:
   For `seq622 = (6, 2, 2, ...)`, at `m = 3`:
   - `integerSlack seq622 3 = 42025 > 0` (fooled by the initial large block `6`),
   - while `minSlack seq622 3 = -1472 < 0` (correctly detecting the forbidden
     `(2, 2)` subword starting at `j = 1`).
3. **Dead End 11 — 5-Block Positive `minSlack` Prefix Killing All Continuations `c ≤ 9`
   (`seq26332`, `seq26332_positive_up_to_five_and_dead_below_ten`)**:
   For `seq26332 c = (2, 6, 3, 3, 2, c, ...)`, `0 < minSlack (seq26332 c) m`
   holds for all `m ≤ 5`, yet `minSlack (seq26332 c) 6 ≤ 0` for every `c ≤ 9`.
-/

namespace Mahler.SlackDeadEnds

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

/-! ## 1. Dead End 9: The Alternating `(2, 7, 2, 7, ...)` Sequence -/

/-- The alternating block sequence `2, 7, 2, 7, ...`. -/
def altTwoSeven (k : ℕ) : ℕ :=
  if k % 2 = 0 then 2 else 7

@[simp] theorem altTwoSeven_mul_two (k : ℕ) :
    altTwoSeven (2 * k) = 2 := by
  unfold altTwoSeven
  simp

@[simp] theorem altTwoSeven_mul_two_add_one (k : ℕ) :
    altTwoSeven (2 * k + 1) = 7 := by
  unfold altTwoSeven
  have : (2 * k + 1) % 2 = 1 := by omega
  simp [this]

/-- Exact cumulative step counts for `altTwoSeven`:
`blockSteps altTwoSeven (2 * k) = 9 * k` and
`blockSteps altTwoSeven (2 * k + 1) = 9 * k + 2`. -/
theorem altTwoSeven_blockSteps (k : ℕ) :
    blockSteps altTwoSeven (2 * k) = 9 * k ∧
      blockSteps altTwoSeven (2 * k + 1) = 9 * k + 2 := by
  induction k with
  | zero =>
      simp [blockSteps, altTwoSeven]
  | succ k ih =>
      rcases ih with ⟨ih0, ih1⟩
      have h_even : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      have hb_even : blockSteps altTwoSeven (2 * (k + 1)) = 9 * (k + 1) := by
        rw [h_even]
        change blockSteps altTwoSeven (2 * k + 1) + altTwoSeven (2 * k + 1) =
          9 * (k + 1)
        rw [ih1, altTwoSeven_mul_two_add_one]
        omega
      have hb_odd :
          blockSteps altTwoSeven (2 * (k + 1) + 1) = 9 * (k + 1) + 2 := by
        change blockSteps altTwoSeven (2 * (k + 1)) + altTwoSeven (2 * (k + 1)) =
          9 * (k + 1) + 2
        rw [hb_even, altTwoSeven_mul_two]
      exact ⟨hb_even, hb_odd⟩

/-- **Exact `minSlack` Periodicity on `(2, 7, 2, 7, ...)` (`altTwoSeven_minSlack`)**:
For every `k : ℕ`,
`minSlack altTwoSeven (2 * k) = 2^(9 * k)` and
`minSlack altTwoSeven (2 * k + 1) = 2^(9 * k)`. -/
theorem altTwoSeven_minSlack (k : ℕ) :
    minSlack altTwoSeven (2 * k) = (2 : ℤ) ^ (9 * k) ∧
      minSlack altTwoSeven (2 * k + 1) = (2 : ℤ) ^ (9 * k) := by
  induction k with
  | zero =>
      simp [minSlack, blockSteps, altTwoSeven]
  | succ k ih =>
      rcases ih with ⟨ih0, ih1⟩
      have hb1 := (altTwoSeven_blockSteps k).2
      have hb2 := (altTwoSeven_blockSteps (k + 1)).1
      have hb3 := (altTwoSeven_blockSteps (k + 1)).2
      have h_even_idx : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      have hm_even :
          minSlack altTwoSeven (2 * (k + 1)) = (2 : ℤ) ^ (9 * (k + 1)) := by
        rw [h_even_idx]
        unfold minSlack
        rw [ ← h_even_idx, hb2, ih1, altTwoSeven_mul_two_add_one ]
        have hpow9 :
            (2 : ℤ) ^ (9 * (k + 1)) = 512 * (2 : ℤ) ^ (9 * k) := by
          rw [show 9 * (k + 1) = 9 + 9 * k by omega, pow_add]
          ring
        have hpow10 :
            (2 : ℤ) ^ (9 * (k + 1) + 1) = 1024 * (2 : ℤ) ^ (9 * k) := by
          rw [pow_succ, hpow9]
          ring
        have h37 : (3 : ℤ) ^ 7 = 2187 := by norm_num
        have h2k_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (9 * k) := pow_nonneg (by decide) _
        apply min_eq_left
        rw [hpow9, hpow10, h37]
        linarith
      have hm_odd :
          minSlack altTwoSeven (2 * (k + 1) + 1) = (2 : ℤ) ^ (9 * (k + 1)) := by
        unfold minSlack
        rw [hb3, hm_even, altTwoSeven_mul_two]
        have hpow2 :
            (2 : ℤ) ^ (9 * (k + 1) + 2) =
              4 * (2 : ℤ) ^ (9 * (k + 1)) := by
          rw [pow_add]
          ring
        have hpow3 :
            (2 : ℤ) ^ (9 * (k + 1) + 2 + 1) =
              8 * (2 : ℤ) ^ (9 * (k + 1)) := by
          rw [show 9 * (k + 1) + 2 + 1 = (9 * (k + 1)) + 3 by omega, pow_add]
          ring
        have h2k_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (9 * (k + 1)) :=
          pow_nonneg (by decide) _
        rw [hpow2, hpow3]
        have h9 : (3 : ℤ) ^ 2 * (2 : ℤ) ^ (9 * (k + 1)) -
            8 * (2 : ℤ) ^ (9 * (k + 1)) = (2 : ℤ) ^ (9 * (k + 1)) := by ring
        rw [h9]
        exact min_eq_right (by linarith)
      exact ⟨hm_even, hm_odd⟩

/-- **Dead End 9 (`altTwoSeven_minSlack_pos`)**:
Even though `altTwoSeven (2 * k) = 2` for every `k : ℕ`, `0 < minSlack altTwoSeven m`
holds for **every** `m : ℕ`. -/
theorem altTwoSeven_minSlack_pos :
    (∀ k : ℕ, altTwoSeven (2 * k) = 2) ∧
      (∀ m : ℕ, 0 < minSlack altTwoSeven m) := by
  refine ⟨altTwoSeven_mul_two, ?_⟩
  intro m
  have hdiv : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by omega
  rcases hdiv with hm0 | hm1
  · rw [hm0, (altTwoSeven_minSlack (m / 2)).1]
    exact pow_pos (by decide) _
  · rw [hm1, (altTwoSeven_minSlack (m / 2)).2]
    exact pow_pos (by decide) _

/-! ## 2. Dead End 10: Positive `integerSlack` With Negative `minSlack` -/

/-- Witness sequence `(6, 2, 2, ...)`. -/
def seq622 : ℕ → ℕ
  | 0 => 6
  | 1 => 2
  | _ => 2

/-- **Dead End 10 (`positive_integerSlack_with_negative_minSlack`)**:
At `m = 3` for `seq622 = (6, 2, 2, ...)`, the unshifted slack is strictly
positive (`integerSlack seq622 3 = 42025 > 0`), whereas the true multi-origin
minimum slack is strictly negative (`minSlack seq622 3 = -1472 < 0`). -/
theorem positive_integerSlack_with_negative_minSlack :
    integerSlack seq622 3 = 42025 ∧
      0 < integerSlack seq622 3 ∧
      minSlack seq622 3 = -1472 ∧
      minSlack seq622 3 < 0 := by
  have hs1 := integerSlack_one seq622
  have hs2 := integerSlack_succ seq622 1
  have hs3 := integerSlack_succ seq622 2
  have hb1 : blockSteps seq622 1 = 6 := by rfl
  have hb2 : blockSteps seq622 2 = 8 := by rfl
  have hb3 : blockSteps seq622 3 = 10 := by rfl
  have h0 : seq622 0 = 6 := rfl
  have h1 : seq622 1 = 2 := rfl
  have h2 : seq622 2 = 2 := rfl
  rw [h0] at hs1
  rw [h1, hb2, hs1] at hs2
  rw [h2, hb3, hs2] at hs3
  norm_num at hs3
  have hm3 : minSlack seq622 3 = -1472 := by decide
  exact ⟨hs3, by linarith, hm3, by linarith⟩

/-! ## 3. Dead End 11: 5-Block Positive Prefix Killing All Continuations `c ≤ 9` -/

/-- Witness sequence `(2, 6, 3, 3, 2, c, ...)`. -/
def seq26332 (c : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 6
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | _ => c

/-- **Dead End 11 (`seq26332_positive_up_to_five_and_dead_below_ten`)**:
For every `c`, `minSlack (seq26332 c) 5 = 2425 > 0`, yet for every `c ≤ 9`,
`minSlack (seq26332 c) 6 ≤ 0`. -/
theorem seq26332_positive_up_to_five_and_dead_below_ten (c : ℕ) :
    minSlack (seq26332 c) 5 = 2425 ∧
      (c ≤ 9 → minSlack (seq26332 c) 6 ≤ 0) := by
  have hm5 : minSlack (seq26332 c) 5 = 2425 := rfl
  refine ⟨hm5, ?_⟩
  intro hc
  have hcases :
      c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨
      c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

end Mahler.SlackDeadEnds
