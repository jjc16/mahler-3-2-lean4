import CeilingDeficitAmplification

/-!
# The Universal Two-Visit-to-`2` Separation Criterion & Parametric Subword Exclusions

This module derives the closed-form formula for the ceiling deficit at any
offset `r` after `s j = 2` and the universal inequality governing any two
occurrences of `2` separated by `r` blocks:

1. **Exact Post-`s j = 2` Shifted Slack & Universal Ceiling Deficit Lower Bound
   (`integerSlack_shift_one_add_of_two`,
   `universal_post_two_ceilingDeficit_lower_bound`)**:
   Whenever `s j = 2`, for every lookahead `r : ℕ` (with
   `S_r = blockSteps (shiftSeq s (j + 1)) r` and
   `R_r = coprimeRemainder (shiftSeq s (j + 1)) r`):
   - `integerSlack (shiftSeq s j) (1 + r) = 3^S_r - 2^(s (j + 1) + 3) * R_r`.
   - `2^T(j) * (2^(s (j + 1) + 3) * R_r + 4 * 2^S_r - 3^S_r) ≤ ceilingDeficit s (j + (1 + r))`.
2. **Universal Two-Visit-to-`2` Slack Cap & Survival Inequality
   (`universal_two_visit_minSlack_cap`,
   `universal_two_visit_survival_inequality`)**:
   If `s j = 2` and `s (j + (1 + r)) = 2`, then
   `minSlack s (j + (1 + r) + 1) ≤ 2^T(j) * (9 * 3^S_r - 32 * 2^S_r - 9 * 2^(s (j + 1) + 3) * R_r)`.
   Consequently, whenever `0 < minSlack s (j + (1 + r) + 1)`,
   `9 * 2^(s (j + 1) + 3) * R_r + 32 * 2^S_r < 9 * 3^S_r`.
3. **Unified Parametric Subword Exclusions (`seven_le_between_two_and_two`,
   `four_le_after_two_six_before_two`)**:
   - At `r = 1` (`(s j, s (j + 1), s (j + 2)) = (2, c, 2)`), `0 < minSlack s (j + 3)`
     forces `104 * 2^c < 9 * 3^c`, hence **`7 ≤ s (j + 1)`** (excluding `(2, c, 2)`
     for all `c ≤ 6`).
   - At `r = 2` with `s (j + 1) = 6` (`(s j, s (j + 1), s (j + 2), s (j + 3)) = (2, 6, c, 2)`),
     `0 < minSlack s (j + 4)` forces `6656 * 2^c < 1953 * 3^c`, hence **`4 ≤ s (j + 2)`**
     (excluding `(2, 6, c, 2)` for all `c ≤ 3`).
-/

namespace Mahler.TwoVisitSeparation

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

/-! ## 1. Exact Post-`s j = 2` Shifted Slack & Universal Ceiling Deficit Lower Bound -/

/-- Whenever `s j = 2`, for every `r : ℕ`,
`integerSlack (shiftSeq s j) (1 + r) =
  3^(blockSteps (shiftSeq s (j + 1)) r) -
    2^(s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) r`. -/
theorem integerSlack_shift_one_add_of_two (s : ℕ → ℕ) {j : ℕ}
    (hsj : s j = 2) (r : ℕ) :
    integerSlack (shiftSeq s j) (1 + r) =
      (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
        (2 : ℤ) ^ (s (j + 1) + 3) *
          (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ) := by
  have hid := post_two_slack_identity s hsj r
  have hlhs :
      integerSlack (shiftSeq s (j + 1)) r =
        (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
          (2 : ℤ) ^ (s (j + 1) + 1) *
            (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ) := rfl
  rw [hlhs] at hid
  have hpow3 :
      (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r + 1) =
        3 * (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) := by
    rw [pow_succ]
    ring
  have hpow2 :
      4 * ((2 : ℤ) ^ (s (j + 1) + 1) *
          (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ)) =
        (2 : ℤ) ^ (s (j + 1) + 3) *
          (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ) := by
    rw [show s (j + 1) + 3 = (s (j + 1) + 1) + 2 by omega, pow_add]
    ring
  linarith

/-- Helper decomposition: when `s j = 2`,
`blockSteps s (j + (1 + r)) = blockSteps s j + 2 + blockSteps (shiftSeq s (j + 1)) r`. -/
theorem blockSteps_add_one_add_of_two (s : ℕ → ℕ) {j : ℕ}
    (hsj : s j = 2) (r : ℕ) :
    blockSteps s (j + (1 + r)) =
      blockSteps s j + 2 + blockSteps (shiftSeq s (j + 1)) r := by
  have h1 : j + (1 + r) = (j + 1) + r := by omega
  rw [h1, blockSteps_add]
  simp [blockSteps, hsj]

/-- **Universal Post-`s j = 2` Ceiling Deficit Lower Bound
(`universal_post_two_ceilingDeficit_lower_bound`)**:
Whenever `s j = 2`, for every lookahead `r : ℕ`,
`2^(blockSteps s j) * (2^(s (j + 1) + 3) * R_r + 4 * 2^S_r - 3^S_r) ≤
  ceilingDeficit s (j + (1 + r))`. -/
theorem universal_post_two_ceilingDeficit_lower_bound (s : ℕ → ℕ) {j : ℕ}
    (hsj : s j = 2) (r : ℕ) :
    (2 : ℤ) ^ (blockSteps s j) *
        ((2 : ℤ) ^ (s (j + 1) + 3) *
            (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ) +
          4 * (2 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
          (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r)) ≤
      ceilingDeficit s (j + (1 + r)) := by
  unfold ceilingDeficit
  have hmin :=
    minSlack_le_scaled_shifted_slack s (by omega : j ≤ j + (1 + r))
  have hsub : j + (1 + r) - j = 1 + r := by omega
  rw [hsub, integerSlack_shift_one_add_of_two s hsj r] at hmin
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s (j + (1 + r))) =
        (2 : ℤ) ^ (blockSteps s j) *
          (4 * (2 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r)) := by
    rw [blockSteps_add_one_add_of_two s hsj r, pow_add, pow_add]
    ring
  rw [hpow2]
  linarith

/-! ## 2. Universal Two-Visit-to-`2` Slack Cap & Survival Inequality -/

/-- **Universal Two-Visit-to-`2` Slack Cap (`universal_two_visit_minSlack_cap`)**:
If `s j = 2` and `s (j + (1 + r)) = 2`, then
`minSlack s (j + (1 + r) + 1) ≤
  2^(blockSteps s j) * (9 * 3^S_r - 32 * 2^S_r - 9 * 2^(s (j + 1) + 3) * R_r)`. -/
theorem universal_two_visit_minSlack_cap (s : ℕ → ℕ) {j r : ℕ}
    (hsj : s j = 2) (hs_second : s (j + (1 + r)) = 2) :
    minSlack s (j + (1 + r) + 1) ≤
      (2 : ℤ) ^ (blockSteps s j) *
        (9 * (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
          32 * (2 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
          9 * (2 : ℤ) ^ (s (j + 1) + 3) *
            (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ)) := by
  have hamp := post_two_quarter_deficit_amplification s hs_second
  have hdef := universal_post_two_ceilingDeficit_lower_bound s hsj r
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s (j + (1 + r))) =
        (2 : ℤ) ^ (blockSteps s j) *
          (4 * (2 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r)) := by
    rw [blockSteps_add_one_add_of_two s hsj r, pow_add, pow_add]
    ring
  rw [hpow2] at hamp
  linarith

/-- **Universal Two-Visit-to-`2` Survival Inequality
(`universal_two_visit_survival_inequality`)**:
If `s j = 2`, `s (j + (1 + r)) = 2`, and `0 < minSlack s (j + (1 + r) + 1)`, then
`9 * 2^(s (j + 1) + 3) * R_r + 32 * 2^S_r < 9 * 3^S_r`. -/
theorem universal_two_visit_survival_inequality (s : ℕ → ℕ) {j r : ℕ}
    (hsj : s j = 2) (hs_second : s (j + (1 + r)) = 2)
    (hpos : 0 < minSlack s (j + (1 + r) + 1)) :
    9 * 2 ^ (s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) r +
        32 * 2 ^ (blockSteps (shiftSeq s (j + 1)) r) <
      9 * 3 ^ (blockSteps (shiftSeq s (j + 1)) r) := by
  have hcap := universal_two_visit_minSlack_cap s hsj hs_second
  have hprod_pos :
      0 < (2 : ℤ) ^ (blockSteps s j) *
        (9 * (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
          32 * (2 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
          9 * (2 : ℤ) ^ (s (j + 1) + 3) *
            (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ)) :=
    lt_of_lt_of_le hpos hcap
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s j) := pow_pos (by decide) _
  have hfactor_pos :
      0 < 9 * (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
        32 * (2 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) r) -
        9 * (2 : ℤ) ^ (s (j + 1) + 3) *
          (coprimeRemainder (shiftSeq s (j + 1)) r : ℤ) :=
    pos_of_mul_pos_right hprod_pos (le_of_lt h2pos)
  have hlt_int :
      ((9 * 2 ^ (s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) r +
          32 * 2 ^ (blockSteps (shiftSeq s (j + 1)) r) : ℕ) : ℤ) <
        ((9 * 3 ^ (blockSteps (shiftSeq s (j + 1)) r) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hlt_int

/-! ## 3. Unified Parametric Exclusions of `(2, c, 2)` (`c ≤ 6`) and `(2, 6, c, 2)` (`c ≤ 3`) -/

/-- **Unified Exclusion of `(2, c, 2)` for all `c ≤ 6` (`seven_le_between_two_and_two`)**:
Whenever `s j = 2`, `s (j + 2) = 2`, and `0 < minSlack s (j + 3)`, the
intermediate block must satisfy **`7 ≤ s (j + 1)`**. -/
theorem seven_le_between_two_and_two (s : ℕ → ℕ) {j : ℕ}
    (hsj : s j = 2) (hsj2 : s (j + 2) = 2)
    (hpos : 0 < minSlack s (j + 3)) :
    7 ≤ s (j + 1) := by
  have hsurv :=
    universal_two_visit_survival_inequality s (r := 1) hsj
      (by simpa [Nat.add_assoc] using hsj2)
      (by simpa [Nat.add_assoc] using hpos)
  simp only [coprimeRemainder, tailSteps, blockSteps, shiftSeq,
    Nat.add_zero, Nat.zero_add, pow_zero, mul_one] at hsurv
  by_contra hlt7
  have hcases :
      s (j + 1) = 0 ∨ s (j + 1) = 1 ∨ s (j + 1) = 2 ∨ s (j + 1) = 3 ∨
      s (j + 1) = 4 ∨ s (j + 1) = 5 ∨ s (j + 1) = 6 := by omega
  rcases hcases with h | h | h | h | h | h | h <;>
    { rw [h] at hsurv; norm_num at hsurv }

/-- **Unified Exclusion of `(2, 6, c, 2)` for all `c ≤ 3`
(`four_le_after_two_six_before_two`)**:
Whenever `s j = 2`, `s (j + 1) = 6`, `s (j + 3) = 2`, and `0 < minSlack s (j + 4)`,
the block `s (j + 2)` must satisfy **`4 ≤ s (j + 2)`**. -/
theorem four_le_after_two_six_before_two (s : ℕ → ℕ) {j : ℕ}
    (hsj : s j = 2) (hsj1 : s (j + 1) = 6) (hsj3 : s (j + 3) = 2)
    (hpos : 0 < minSlack s (j + 4)) :
    4 ≤ s (j + 2) := by
  have hsurv :=
    universal_two_visit_survival_inequality s (r := 2) hsj
      (by simpa [Nat.add_assoc] using hsj3)
      (by simpa [Nat.add_assoc] using hpos)
  have hR2 :
      coprimeRemainder (shiftSeq s (j + 1)) 2 =
        3 ^ (s (j + 2)) + 2 ^ (s (j + 2)) := by
    simp [coprimeRemainder, tailSteps, shiftSeq, Nat.add_assoc]
  have hS2 :
      blockSteps (shiftSeq s (j + 1)) 2 = 6 + s (j + 2) := by
    simp [blockSteps, shiftSeq, Nat.add_assoc, hsj1]
  rw [hR2, hS2, hsj1] at hsurv
  by_contra hlt4
  have hcases :
      s (j + 2) = 0 ∨ s (j + 2) = 1 ∨ s (j + 2) = 2 ∨ s (j + 2) = 3 := by
    omega
  rcases hcases with h | h | h | h <;>
    { rw [h] at hsurv; norm_num at hsurv }

end Mahler.TwoVisitSeparation
