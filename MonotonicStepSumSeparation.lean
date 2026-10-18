import UniversalTwoVisitSeparation

/-!
# Monotonic `coprimeRemainder` Lower Bounds & `r`-Independent Step-Sum Separation

This module proves monotonic lower bounds on `coprimeRemainder` across arbitrary
block horizons `r` and combines them with `universal_two_visit_survival_inequality`
to establish `r`-independent step-sum lower bounds `S_r = blockSteps (shiftSeq s (j + 1)) r`
between any two visits to `s = 2`:

1. **Monotonic Lower Bounds on `coprimeRemainder`
   (`three_pow_mul_coprimeRemainder_le`,
   `three_pow_blockSteps_le_mul_coprimeRemainder`,
   `three_pow_blockSteps_le_mul_coprimeRemainder_two`)**:
   - For every sequence `t : ℕ → ℕ`, prefix `a`, and offset `d`,
     `3^(blockSteps (shiftSeq t a) d) * coprimeRemainder t a ≤ coprimeRemainder t (a + d)`.
   - For `1 ≤ r`, `3^(blockSteps t r) ≤ 3^(t 0) * coprimeRemainder t r`.
   - For `2 ≤ r`, `(3^(t 1) + 2^(t 1)) * 3^(blockSteps t r) ≤ 3^(t 0 + t 1) * coprimeRemainder t r`.
2. **`r`-Independent Step-Sum Separation Inequalities
   (`universal_step_sum_separation_inequality`,
   `seven_le_step_sum_after_two_six`,
   `ten_le_step_sum_after_two_six_three`)**:
   - For any `1 ≤ r` with `s j = 2`, `s (j + (1 + r)) = 2`, and
     `0 < minSlack s (j + (1 + r) + 1)`:
     `9 * 2^(s (j + 1) + 3) * 3^S_r + 32 * 3^(s (j + 1)) * 2^S_r < 9 * 3^(s (j + 1)) * 3^S_r`.
   - When `s (j + 1) = 6`, this forces **`7 ≤ blockSteps (shiftSeq s (j + 1)) r`**
     for all `r ≥ 1`.
   - When `s (j + 1) = 6` and `s (j + 2) = 3` (`r ≥ 2`), the 2-prefix lower bound
     forces `629856 * 2^S_r < 15867 * 3^S_r`, hence
     **`10 ≤ blockSteps (shiftSeq s (j + 1)) r`** for all `r ≥ 2`.
-/

namespace Mahler.MonotonicSeparation

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

/-! ## 1. Monotonic Lower Bounds on `coprimeRemainder` -/

/-- For every sequence `t : ℕ → ℕ`, prefix `a`, and offset `d`,
`3^(blockSteps (shiftSeq t a) d) * coprimeRemainder t a ≤ coprimeRemainder t (a + d)`. -/
theorem three_pow_mul_coprimeRemainder_le (t : ℕ → ℕ) (a d : ℕ) :
    3 ^ (blockSteps (shiftSeq t a) d) * coprimeRemainder t a ≤
      coprimeRemainder t (a + d) := by
  induction d with
  | zero =>
      simp [blockSteps]
  | succ d ih =>
      have hmul :
          3 ^ (t (a + d)) *
              (3 ^ (blockSteps (shiftSeq t a) d) * coprimeRemainder t a) ≤
            3 ^ (t (a + d)) * coprimeRemainder t (a + d) :=
        Nat.mul_le_mul_left (3 ^ (t (a + d))) ih
      have hstep :
          coprimeRemainder t (a + (d + 1)) =
            3 ^ (t (a + d)) * coprimeRemainder t (a + d) +
              2 ^ (tailSteps t (a + d)) := by
        rw [← Nat.add_assoc]
        rfl
      have hpow :
          3 ^ (blockSteps (shiftSeq t a) (d + 1)) * coprimeRemainder t a =
            3 ^ (t (a + d)) *
              (3 ^ (blockSteps (shiftSeq t a) d) * coprimeRemainder t a) := by
        simp only [blockSteps, shiftSeq, Nat.pow_add]
        ring
      rw [hpow, hstep]
      exact le_trans hmul (Nat.le_add_right _ _)

/-- **First-Block Monotonic Lower Bound (`three_pow_blockSteps_le_mul_coprimeRemainder`)**:
For every sequence `t : ℕ → ℕ` and `r ≥ 1`,
`3^(blockSteps t r) ≤ 3^(t 0) * coprimeRemainder t r`. -/
theorem three_pow_blockSteps_le_mul_coprimeRemainder (t : ℕ → ℕ) {r : ℕ}
    (hr : 1 ≤ r) :
    3 ^ (blockSteps t r) ≤ 3 ^ (t 0) * coprimeRemainder t r := by
  have hle := three_pow_mul_coprimeRemainder_le t 1 (r - 1)
  have hidx : 1 + (r - 1) = r := by omega
  have hR1 : coprimeRemainder t 1 = 1 := by
    simp [coprimeRemainder, tailSteps]
  rw [hidx, hR1, Nat.mul_one] at hle
  have hsteps :
      blockSteps t r = t 0 + blockSteps (shiftSeq t 1) (r - 1) := by
    conv_lhs => rw [← hidx, blockSteps_add]
    simp [blockSteps]
  rw [hsteps, Nat.pow_add]
  exact Nat.mul_le_mul_left (3 ^ (t 0)) hle

/-- **Two-Block Monotonic Lower Bound (`three_pow_blockSteps_le_mul_coprimeRemainder_two`)**:
For every sequence `t : ℕ → ℕ` and `r ≥ 2`,
`(3^(t 1) + 2^(t 1)) * 3^(blockSteps t r) ≤ 3^(t 0 + t 1) * coprimeRemainder t r`. -/
theorem three_pow_blockSteps_le_mul_coprimeRemainder_two (t : ℕ → ℕ) {r : ℕ}
    (hr : 2 ≤ r) :
    (3 ^ (t 1) + 2 ^ (t 1)) * 3 ^ (blockSteps t r) ≤
      3 ^ (t 0 + t 1) * coprimeRemainder t r := by
  have hle := three_pow_mul_coprimeRemainder_le t 2 (r - 2)
  have hidx : 2 + (r - 2) = r := by omega
  have hR2 : coprimeRemainder t 2 = 3 ^ (t 1) + 2 ^ (t 1) := by
    simp [coprimeRemainder, tailSteps]
  rw [hidx, hR2] at hle
  have hsteps :
      blockSteps t r = (t 0 + t 1) + blockSteps (shiftSeq t 2) (r - 2) := by
    conv_lhs => rw [← hidx, blockSteps_add]
    simp [blockSteps]
  have hmul := Nat.mul_le_mul_left (3 ^ (t 0 + t 1)) hle
  have hlhs :
      3 ^ (t 0 + t 1) *
          (3 ^ (blockSteps (shiftSeq t 2) (r - 2)) * (3 ^ (t 1) + 2 ^ (t 1))) =
        (3 ^ (t 1) + 2 ^ (t 1)) * 3 ^ (blockSteps t r) := by
    rw [hsteps, Nat.pow_add]
    ring
  omega

/-! ## 2. `r`-Independent Step-Sum Separation Inequalities -/

/-- **Universal `r`-Independent Step-Sum Separation Inequality
(`universal_step_sum_separation_inequality`)**:
For any `1 ≤ r` with `s j = 2`, `s (j + (1 + r)) = 2`, and
`0 < minSlack s (j + (1 + r) + 1)`:
`9 * 2^(s (j + 1) + 3) * 3^S_r + 32 * 3^(s (j + 1)) * 2^S_r < 9 * 3^(s (j + 1)) * 3^S_r`. -/
theorem universal_step_sum_separation_inequality (s : ℕ → ℕ) {j r : ℕ}
    (hr : 1 ≤ r) (hsj : s j = 2) (hs_second : s (j + (1 + r)) = 2)
    (hpos : 0 < minSlack s (j + (1 + r) + 1)) :
    9 * 2 ^ (s (j + 1) + 3) * 3 ^ (blockSteps (shiftSeq s (j + 1)) r) +
        32 * 3 ^ (s (j + 1)) * 2 ^ (blockSteps (shiftSeq s (j + 1)) r) <
      9 * 3 ^ (s (j + 1)) * 3 ^ (blockSteps (shiftSeq s (j + 1)) r) := by
  have hsurv :=
    universal_two_visit_survival_inequality s hsj hs_second hpos
  have hmono :=
    three_pow_blockSteps_le_mul_coprimeRemainder (shiftSeq s (j + 1)) hr
  have hs0 : shiftSeq s (j + 1) 0 = s (j + 1) := rfl
  rw [hs0] at hmono
  have h3pos : 0 < 3 ^ (s (j + 1)) := Nat.pow_pos (by decide)
  have hmul_surv := Nat.mul_lt_mul_of_pos_left hsurv h3pos
  have hmul_mono :=
    Nat.mul_le_mul_left (9 * 2 ^ (s (j + 1) + 3)) hmono
  have h1 :
      9 * 2 ^ (s (j + 1) + 3) *
          (3 ^ (s (j + 1)) * coprimeRemainder (shiftSeq s (j + 1)) r) +
        32 * 3 ^ (s (j + 1)) * 2 ^ (blockSteps (shiftSeq s (j + 1)) r) =
      3 ^ (s (j + 1)) *
        (9 * 2 ^ (s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) r +
          32 * 2 ^ (blockSteps (shiftSeq s (j + 1)) r)) := by ring
  have h2 :
      3 ^ (s (j + 1)) * (9 * 3 ^ (blockSteps (shiftSeq s (j + 1)) r)) =
        9 * 3 ^ (s (j + 1)) * 3 ^ (blockSteps (shiftSeq s (j + 1)) r) := by ring
  omega

/-- **`r`-Independent Step-Sum Bound After `(2, 6, ...)` (`seven_le_step_sum_after_two_six`)**:
Whenever `1 ≤ r`, `s j = 2`, `s (j + 1) = 6`, `s (j + (1 + r)) = 2`, and
`0 < minSlack s (j + (1 + r) + 1)`, the intermediate step sum satisfies
**`7 ≤ blockSteps (shiftSeq s (j + 1)) r`**. -/
theorem seven_le_step_sum_after_two_six (s : ℕ → ℕ) {j r : ℕ}
    (hr : 1 ≤ r) (hsj : s j = 2) (hsj1 : s (j + 1) = 6)
    (hs_second : s (j + (1 + r)) = 2)
    (hpos : 0 < minSlack s (j + (1 + r) + 1)) :
    7 ≤ blockSteps (shiftSeq s (j + 1)) r := by
  have hineq :=
    universal_step_sum_separation_inequality s hr hsj hs_second hpos
  rw [hsj1] at hineq
  set S := blockSteps (shiftSeq s (j + 1)) r
  by_contra hlt7
  have hcases :
      S = 0 ∨ S = 1 ∨ S = 2 ∨ S = 3 ∨ S = 4 ∨ S = 5 ∨ S = 6 := by omega
  rcases hcases with h | h | h | h | h | h | h <;>
    { rw [h] at hineq; norm_num at hineq }

/-- **`r`-Independent Step-Sum Bound After `(2, 6, 3, ...)`
(`ten_le_step_sum_after_two_six_three`)**:
Whenever `2 ≤ r`, `s j = 2`, `s (j + 1) = 6`, `s (j + 2) = 3`,
`s (j + (1 + r)) = 2`, and `0 < minSlack s (j + (1 + r) + 1)`, the intermediate
step sum satisfies **`10 ≤ blockSteps (shiftSeq s (j + 1)) r`**. -/
theorem ten_le_step_sum_after_two_six_three (s : ℕ → ℕ) {j r : ℕ}
    (hr : 2 ≤ r) (hsj : s j = 2) (hsj1 : s (j + 1) = 6)
    (hsj2 : s (j + 2) = 3) (hs_second : s (j + (1 + r)) = 2)
    (hpos : 0 < minSlack s (j + (1 + r) + 1)) :
    10 ≤ blockSteps (shiftSeq s (j + 1)) r := by
  have hsurv :=
    universal_two_visit_survival_inequality s hsj hs_second hpos
  have hmono :=
    three_pow_blockSteps_le_mul_coprimeRemainder_two (shiftSeq s (j + 1)) hr
  have hs0 : shiftSeq s (j + 1) 0 = 6 := by simp [shiftSeq, hsj1]
  have hs1 : shiftSeq s (j + 1) 1 = 3 := by
    change s (j + 1 + 1) = 3
    simpa [Nat.add_assoc] using hsj2
  rw [hs0, hs1] at hmono
  rw [hsj1] at hsurv
  set S := blockSteps (shiftSeq s (j + 1)) r
  set R := coprimeRemainder (shiftSeq s (j + 1)) r
  have hmul_surv := Nat.mul_lt_mul_of_pos_left hsurv (by decide : 0 < 3 ^ (6 + 3))
  have hmul_mono := Nat.mul_le_mul_left (9 * 2 ^ (6 + 3)) hmono
  have hcomb : 161280 * 3 ^ S + 629856 * 2 ^ S < 177147 * 3 ^ S := by
    have h1 :
        9 * 2 ^ (6 + 3) * ((3 ^ 3 + 2 ^ 3) * 3 ^ S) = 161280 * 3 ^ S := by ring
    have h2 :
        9 * 2 ^ (6 + 3) * (3 ^ (6 + 3) * R) + 629856 * 2 ^ S =
          3 ^ (6 + 3) * (9 * 2 ^ (6 + 3) * R + 32 * 2 ^ S) := by ring
    have h3 :
        3 ^ (6 + 3) * (9 * 3 ^ S) = 177147 * 3 ^ S := by ring
    omega
  by_contra hlt10
  have hcases :
      S = 0 ∨ S = 1 ∨ S = 2 ∨ S = 3 ∨ S = 4 ∨
      S = 5 ∨ S = 6 ∨ S = 7 ∨ S = 8 ∨ S = 9 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;>
    { rw [h] at hcomb; norm_num at hcomb }

end Mahler.MonotonicSeparation
