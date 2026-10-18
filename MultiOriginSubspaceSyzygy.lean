import RidoutSubspaceFramework

/-!
# Multi-Origin Subspace Syzygy, Additive Separation of Variables & Dead End 15

This module explores combining multiple shifted origins `j = 0, 1, ..., r` at a
common target block `m` to test whether a higher-dimensional Schlickewei `p`-adic
Subspace Theorem system can break the single-origin Ridout `Q_m^(-2)` tangency:

1. **The Shifted Slack Affine Collapse Identity (`shifted_slack_affine_collapse`)**:
   For every sequence `s : ℕ → ℕ`, origin `r`, and horizon `d`, the `r`-shifted
   slack `integerSlack (shiftSeq s r) d` is an exact affine combination of the
   origin-`0` slack `integerSlack s (r + d)` and `3^(blockSteps (shiftSeq s r) d)`:
   `2^(blockSteps s r) * integerSlack (shiftSeq s r) d =
     integerSlack s (r + d) + 3^(blockSteps (shiftSeq s r) d) * slackDeficiency s r`.
2. **The Shifted Deficiency Cocycle (`shifted_deficiency_cocycle`)**:
   `slackDeficiency s (r + d) =
     3^(blockSteps (shiftSeq s r) d) * slackDeficiency s r +
       2^(blockSteps s r) * slackDeficiency (shiftSeq s r) d`.
3. **Additive Separation of Variables `(r, r + d)` (`additive_separation_of_shifted_slack`)**:
   Dividing by `3^(blockSteps s (r + d))` separates the two-parameter triangle of
   shifted slacks into a function of `r + d` minus a function of `r`:
   `(2^(T(r)) * integerSlack (shiftSeq s r) d : ℝ) / 3^(T(r + d)) =
     (integerSlack s (r + d) : ℝ) / 3^(T(r + d)) -
       ((integerSlack s r : ℝ) - 2^(T(r))) / 3^(T(r))`.
4. **Sub-Ceiling Origin Domination by Origin `0` (`sub_ceiling_origin_dominated_by_zero`)**:
   Whenever `integerSlack s r ≤ 2^(blockSteps s r)` (`0 ≤ slackDeficiency s r`),
   `integerSlack s (r + d) ≤ 2^(blockSteps s r) * integerSlack (shiftSeq s r) d`
   for all `d ≥ 0`. Thus no sub-ceiling origin `r` can ever turn non-positive before
   origin `0` itself turns non-positive.
5. **Super-Ceiling Origin Corridor (`super_ceiling_origin_corridor_for_unshifted_slack`)**:
   When `2^(blockSteps s r) < integerSlack s r` and the `r`-shifted slack is in a
   valid sub-ceiling state (`0 < Δ^{(r)}_d ≤ 2^(S_{r, d})`), the unshifted slack
   `integerSlack s (r + d)` is trapped in a narrow corridor of width `2^(T(r + d))`
   above `3^(S_{r, d}) * (integerSlack s r - 2^(T(r)))`.
6. **Dead End 15 — Three-Origin Schlickewei Subspace Syzygy (`three_origin_subspace_syzygy`)**:
   Because every `2^(T(r)) * Δ^{(r)}_{m - r}` lies in the 2-dimensional space
   `span{integerSlack s m, 3^(T(m))}` as `m → ∞`, any three origins `(0, r_1, r_2)`
   satisfy an exact `m`-independent linear syzygy for all `m ≥ max r_1 r_2`:
   `slackDeficiency s r_2 * 3^(T(r_1)) * (2^(T(r_1)) * Δ^{(r_1)}_{m - r_1} - Δ^{(0)}_m) =
     slackDeficiency s r_1 * 3^(T(r_2)) * (2^(T(r_2)) * Δ^{(r_2)}_{m - r_2} - Δ^{(0)}_m)`.
   Consequently, combining `k ≥ 3` shifted origins in Schlickewei's `p`-adic Subspace
   Theorem lands identically inside a fixed proper exceptional hyperplane.
-/

namespace Mahler.MultiOriginSyzygy

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

/-! ## 1. The Origin Ceiling Deficit, Shifted Slack Affine Collapse & Cocycle -/

/-- The unshifted ceiling deficit at block `r`:
`originCeilingDeficit s r = 2^(blockSteps s r) - integerSlack s r`. -/
def originCeilingDeficit (s : ℕ → ℕ) (r : ℕ) : ℤ :=
  (2 : ℤ) ^ (blockSteps s r) - integerSlack s r

/-- **Shifted Slack Affine Collapse Identity (`shifted_slack_affine_collapse`)**:
For every sequence `s : ℕ → ℕ`, origin `r`, and horizon `d`,
`2^(blockSteps s r) * integerSlack (shiftSeq s r) d =
  integerSlack s (r + d) + 3^(blockSteps (shiftSeq s r) d) * originCeilingDeficit s r`. -/
theorem shifted_slack_affine_collapse (s : ℕ → ℕ) (r d : ℕ) :
    (2 : ℤ) ^ (blockSteps s r) * integerSlack (shiftSeq s r) d =
      integerSlack s (r + d) +
        (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) * originCeilingDeficit s r := by
  have hcocycle := integerSlack_cocycle_eq s r d
  unfold originCeilingDeficit
  linarith

/-- **Shifted Deficiency Cocycle (`shifted_deficiency_cocycle`)**:
For every sequence `s : ℕ → ℕ`, origin `r`, and horizon `d`,
`originCeilingDeficit s (r + d) =
  3^(blockSteps (shiftSeq s r) d) * originCeilingDeficit s r +
    2^(blockSteps s r) * originCeilingDeficit (shiftSeq s r) d`. -/
theorem shifted_deficiency_cocycle (s : ℕ → ℕ) (r d : ℕ) :
    originCeilingDeficit s (r + d) =
      (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) * originCeilingDeficit s r +
        (2 : ℤ) ^ (blockSteps s r) * originCeilingDeficit (shiftSeq s r) d := by
  have hcol := shifted_slack_affine_collapse s r d
  have hdef_rd :
      originCeilingDeficit s (r + d) =
        (2 : ℤ) ^ (blockSteps s (r + d)) - integerSlack s (r + d) := rfl
  have hdef_shift :
      originCeilingDeficit (shiftSeq s r) d =
        (2 : ℤ) ^ (blockSteps (shiftSeq s r) d) - integerSlack (shiftSeq s r) d := rfl
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s (r + d)) =
        (2 : ℤ) ^ (blockSteps s r) * (2 : ℤ) ^ (blockSteps (shiftSeq s r) d) := by
    rw [blockSteps_add s r d, pow_add]
  rw [hdef_rd, hdef_shift, hpow2]
  linarith

/-! ## 2. Additive Separation of Variables `(r, r + d)` -/

/-- **Additive Separation of Shifted Slack (`additive_separation_of_shifted_slack`)**:
Dividing `shifted_slack_affine_collapse` by `3^(blockSteps s (r + d))` separates
the dependence on `r + d` and `r` additively:
`(2^(blockSteps s r) * integerSlack (shiftSeq s r) d : ℝ) / 3^(blockSteps s (r + d)) =
  (integerSlack s (r + d) : ℝ) / 3^(blockSteps s (r + d)) -
    ((integerSlack s r : ℝ) - 2^(blockSteps s r)) / 3^(blockSteps s r)`. -/
theorem additive_separation_of_shifted_slack (s : ℕ → ℕ) (r d : ℕ) :
    ((2 : ℝ) ^ (blockSteps s r) * (integerSlack (shiftSeq s r) d : ℝ)) /
        (3 : ℝ) ^ (blockSteps s (r + d)) =
      (integerSlack s (r + d) : ℝ) / (3 : ℝ) ^ (blockSteps s (r + d)) -
        ((integerSlack s r : ℝ) - (2 : ℝ) ^ (blockSteps s r)) /
          (3 : ℝ) ^ (blockSteps s r) := by
  have hcol := shifted_slack_affine_collapse s r d
  have hdef_r :
      originCeilingDeficit s r = (2 : ℤ) ^ (blockSteps s r) - integerSlack s r := rfl
  rw [hdef_r] at hcol
  have hcol_real :
      (2 : ℝ) ^ (blockSteps s r) * (integerSlack (shiftSeq s r) d : ℝ) =
        (integerSlack s (r + d) : ℝ) +
          (3 : ℝ) ^ (blockSteps (shiftSeq s r) d) *
            ((2 : ℝ) ^ (blockSteps s r) - (integerSlack s r : ℝ)) := by
    exact_mod_cast hcol
  have hpow3 :
      (3 : ℝ) ^ (blockSteps s (r + d)) =
        (3 : ℝ) ^ (blockSteps s r) * (3 : ℝ) ^ (blockSteps (shiftSeq s r) d) := by
    rw [blockSteps_add s r d, pow_add]
  have h3r_ne : (3 : ℝ) ^ (blockSteps s r) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3d_ne : (3 : ℝ) ^ (blockSteps (shiftSeq s r) d) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  rw [hcol_real, hpow3]
  field_simp [h3r_ne, h3d_ne]
  ring

/-! ## 3. Sub-Ceiling Origin Domination & Super-Ceiling Corridor -/

/-- **Sub-Ceiling Origin Domination by Origin `0` (`sub_ceiling_origin_dominated_by_zero`)**:
Whenever `integerSlack s r ≤ 2^(blockSteps s r)` (so origin `0` is at or below
ceiling at block `r`), we have
`integerSlack s (r + d) ≤ 2^(blockSteps s r) * integerSlack (shiftSeq s r) d`
for every `d ≥ 0`, and in particular `0 < integerSlack s (r + d) → 0 < integerSlack (shiftSeq s r) d`. -/
theorem sub_ceiling_origin_dominated_by_zero {s : ℕ → ℕ} {r : ℕ}
    (hle : integerSlack s r ≤ (2 : ℤ) ^ (blockSteps s r)) (d : ℕ) :
    integerSlack s (r + d) ≤
        (2 : ℤ) ^ (blockSteps s r) * integerSlack (shiftSeq s r) d ∧
      (0 < integerSlack s (r + d) → 0 < integerSlack (shiftSeq s r) d) := by
  have hcol := shifted_slack_affine_collapse s r d
  have hdef_nonneg : 0 ≤ originCeilingDeficit s r := by
    unfold originCeilingDeficit
    linarith
  have h3_pos : (0 : ℤ) < (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) :=
    pow_pos (by decide) _
  have hprod_nonneg :
      0 ≤ (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) * originCeilingDeficit s r :=
    mul_nonneg (le_of_lt h3_pos) hdef_nonneg
  have hineq :
      integerSlack s (r + d) ≤
        (2 : ℤ) ^ (blockSteps s r) * integerSlack (shiftSeq s r) d := by
    linarith
  refine ⟨hineq, ?_⟩
  intro hpos
  have h2_pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s r) := pow_pos (by decide) _
  have hmul_pos :
      (0 : ℤ) < (2 : ℤ) ^ (blockSteps s r) * integerSlack (shiftSeq s r) d :=
    lt_of_lt_of_le hpos hineq
  exact pos_of_mul_pos_right hmul_pos (le_of_lt h2_pos)

/-- **Super-Ceiling Origin Corridor (`super_ceiling_origin_corridor_for_unshifted_slack`)**:
If `0 < integerSlack (shiftSeq s r) d ≤ 2^(blockSteps (shiftSeq s r) d)`, then the
unshifted slack `integerSlack s (r + d)` is trapped in the width-`2^(blockSteps s (r + d))`
corridor:
`3^(blockSteps (shiftSeq s r) d) * (integerSlack s r - 2^(blockSteps s r)) <
  integerSlack s (r + d)`
and
`integerSlack s (r + d) ≤
  3^(blockSteps (shiftSeq s r) d) * (integerSlack s r - 2^(blockSteps s r)) +
    2^(blockSteps s (r + d))`. -/
theorem super_ceiling_origin_corridor_for_unshifted_slack {s : ℕ → ℕ} {r d : ℕ}
    (hpos : 0 < integerSlack (shiftSeq s r) d)
    (hle : integerSlack (shiftSeq s r) d ≤ (2 : ℤ) ^ (blockSteps (shiftSeq s r) d)) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) *
          (integerSlack s r - (2 : ℤ) ^ (blockSteps s r)) <
        integerSlack s (r + d) ∧
      integerSlack s (r + d) ≤
        (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) *
            (integerSlack s r - (2 : ℤ) ^ (blockSteps s r)) +
          (2 : ℤ) ^ (blockSteps s (r + d)) := by
  have hcol := shifted_slack_affine_collapse s r d
  have hdef :
      originCeilingDeficit s r = (2 : ℤ) ^ (blockSteps s r) - integerSlack s r := rfl
  rw [hdef] at hcol
  have h2r_pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s r) := pow_pos (by decide) _
  have hprod_pos :
      (0 : ℤ) < (2 : ℤ) ^ (blockSteps s r) * integerSlack (shiftSeq s r) d :=
    mul_pos h2r_pos hpos
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s (r + d)) =
        (2 : ℤ) ^ (blockSteps s r) * (2 : ℤ) ^ (blockSteps (shiftSeq s r) d) := by
    rw [blockSteps_add s r d, pow_add]
  have hprod_le :
      (2 : ℤ) ^ (blockSteps s r) * integerSlack (shiftSeq s r) d ≤
        (2 : ℤ) ^ (blockSteps s (r + d)) := by
    rw [hpow2]
    exact mul_le_mul_of_nonneg_left hle (le_of_lt h2r_pos)
  constructor <;> linarith

/-! ## 4. Dead End 15: Three-Origin Schlickewei Subspace Hyperplane Syzygy -/

/-- **Three-Origin Schlickewei Subspace Syzygy (`three_origin_subspace_syzygy`, Dead End 15)**:
For any sequence `s : ℕ → ℕ`, any two origins `r_1, r_2`, and any horizon `m` with
`r_1 ≤ m` and `r_2 ≤ m`, the three shifted slacks at `m` from origins `0`, `r_1`,
and `r_2` satisfy the exact `m`-independent hyperplane syzygy:
`originCeilingDeficit s r_2 * 3^(blockSteps s r_1) *
    (2^(blockSteps s r_1) * integerSlack (shiftSeq s r_1) (m - r_1) - integerSlack s m) =
  originCeilingDeficit s r_1 * 3^(blockSteps s r_2) *
    (2^(blockSteps s r_2) * integerSlack (shiftSeq s r_2) (m - r_2) - integerSlack s m)`. -/
theorem three_origin_subspace_syzygy (s : ℕ → ℕ) {r1 r2 m : ℕ}
    (hr1 : r1 ≤ m) (hr2 : r2 ≤ m) :
    originCeilingDeficit s r2 * (3 : ℤ) ^ (blockSteps s r1) *
        ((2 : ℤ) ^ (blockSteps s r1) * integerSlack (shiftSeq s r1) (m - r1) -
          integerSlack s m) =
      originCeilingDeficit s r1 * (3 : ℤ) ^ (blockSteps s r2) *
        ((2 : ℤ) ^ (blockSteps s r2) * integerSlack (shiftSeq s r2) (m - r2) -
          integerSlack s m) := by
  have hc1 := shifted_slack_affine_collapse s r1 (m - r1)
  have hc2 := shifted_slack_affine_collapse s r2 (m - r2)
  have hm1 : r1 + (m - r1) = m := by omega
  have hm2 : r2 + (m - r2) = m := by omega
  rw [hm1] at hc1
  rw [hm2] at hc2
  have hsub1 :
      (2 : ℤ) ^ (blockSteps s r1) * integerSlack (shiftSeq s r1) (m - r1) -
          integerSlack s m =
        (3 : ℤ) ^ (blockSteps (shiftSeq s r1) (m - r1)) * originCeilingDeficit s r1 := by
    linarith
  have hsub2 :
      (2 : ℤ) ^ (blockSteps s r2) * integerSlack (shiftSeq s r2) (m - r2) -
          integerSlack s m =
        (3 : ℤ) ^ (blockSteps (shiftSeq s r2) (m - r2)) * originCeilingDeficit s r2 := by
    linarith
  have hpow1 :
      (3 : ℤ) ^ (blockSteps s r1) * (3 : ℤ) ^ (blockSteps (shiftSeq s r1) (m - r1)) =
        (3 : ℤ) ^ (blockSteps s m) := by
    rw [← pow_add, ← blockSteps_add s r1 (m - r1), hm1]
  have hpow2 :
      (3 : ℤ) ^ (blockSteps s r2) * (3 : ℤ) ^ (blockSteps (shiftSeq s r2) (m - r2)) =
        (3 : ℤ) ^ (blockSteps s m) := by
    rw [← pow_add, ← blockSteps_add s r2 (m - r2), hm2]
  rw [hsub1, hsub2]
  calc
    originCeilingDeficit s r2 * (3 : ℤ) ^ (blockSteps s r1) *
        ((3 : ℤ) ^ (blockSteps (shiftSeq s r1) (m - r1)) * originCeilingDeficit s r1) =
      originCeilingDeficit s r1 * originCeilingDeficit s r2 *
        ((3 : ℤ) ^ (blockSteps s r1) * (3 : ℤ) ^ (blockSteps (shiftSeq s r1) (m - r1))) := by
      ring
    _ = originCeilingDeficit s r1 * originCeilingDeficit s r2 * (3 : ℤ) ^ (blockSteps s m) := by
      rw [hpow1]
    _ = originCeilingDeficit s r1 * originCeilingDeficit s r2 *
        ((3 : ℤ) ^ (blockSteps s r2) * (3 : ℤ) ^ (blockSteps (shiftSeq s r2) (m - r2))) := by
      rw [hpow2]
    _ = originCeilingDeficit s r1 * (3 : ℤ) ^ (blockSteps s r2) *
        ((3 : ℤ) ^ (blockSteps (shiftSeq s r2) (m - r2)) * originCeilingDeficit s r2) := by
      ring

/-! ## 5. Complete Elimination of `shiftSeq` from `0 < minSlack s m` -/

/-- **Unshifted Difference Formula for Scaled Shifted Slack
(`scaled_shifted_slack_eq_unshifted_diff`)**:
For every sequence `s : ℕ → ℕ` and `j ≤ m`, multiplying
`2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)` by `3^(blockSteps s j)`
eliminates `shiftSeq` completely:
`3^(blockSteps s j) * (2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) =
  3^(blockSteps s j) * integerSlack s m -
    3^(blockSteps s m) * (integerSlack s j - 2^(blockSteps s j))`. -/
theorem scaled_shifted_slack_eq_unshifted_diff (s : ℕ → ℕ) {j m : ℕ} (hjm : j ≤ m) :
    (3 : ℤ) ^ (blockSteps s j) *
        ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) =
      (3 : ℤ) ^ (blockSteps s j) * integerSlack s m -
        (3 : ℤ) ^ (blockSteps s m) *
          (integerSlack s j - (2 : ℤ) ^ (blockSteps s j)) := by
  have hcol := shifted_slack_affine_collapse s j (m - j)
  have hdef :
      originCeilingDeficit s j = (2 : ℤ) ^ (blockSteps s j) - integerSlack s j := rfl
  have hm : j + (m - j) = m := by omega
  rw [hm, hdef] at hcol
  have hpow3 :
      (3 : ℤ) ^ (blockSteps s j) * (3 : ℤ) ^ (blockSteps (shiftSeq s j) (m - j)) =
        (3 : ℤ) ^ (blockSteps s m) := by
    rw [← pow_add, ← blockSteps_add s j (m - j), hm]
  calc
    (3 : ℤ) ^ (blockSteps s j) *
        ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) =
      (3 : ℤ) ^ (blockSteps s j) *
        (integerSlack s m +
          (3 : ℤ) ^ (blockSteps (shiftSeq s j) (m - j)) *
            ((2 : ℤ) ^ (blockSteps s j) - integerSlack s j)) := by
      rw [hcol]
    _ = (3 : ℤ) ^ (blockSteps s j) * integerSlack s m -
          ((3 : ℤ) ^ (blockSteps s j) *
            (3 : ℤ) ^ (blockSteps (shiftSeq s j) (m - j))) *
            (integerSlack s j - (2 : ℤ) ^ (blockSteps s j)) := by
      ring
    _ = (3 : ℤ) ^ (blockSteps s j) * integerSlack s m -
          (3 : ℤ) ^ (blockSteps s m) *
            (integerSlack s j - (2 : ℤ) ^ (blockSteps s j)) := by
      rw [hpow3]

/-- **Shift-Free Characterization of `0 < minSlack s m`
(`minSlack_pos_iff_unshifted_ceiling_comparison`)**:
`0 < minSlack s m` holds if and only if for every `j ≤ m`, the unshifted sequence
`integerSlack s` satisfies:
`3^(blockSteps s m) * (integerSlack s j - 2^(blockSteps s j)) <
  3^(blockSteps s j) * integerSlack s m`. -/
theorem minSlack_pos_iff_unshifted_ceiling_comparison (s : ℕ → ℕ) (m : ℕ) :
    0 < minSlack s m ↔
      ∀ j ≤ m,
        (3 : ℤ) ^ (blockSteps s m) *
            (integerSlack s j - (2 : ℤ) ^ (blockSteps s j)) <
          (3 : ℤ) ^ (blockSteps s j) * integerSlack s m := by
  rw [minSlack_pos_iff_all_shifted_pos]
  constructor
  · intro hall j hjm
    have hj_pos := hall j hjm
    have h2_pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s j) := pow_pos (by decide) _
    have h3_pos : (0 : ℤ) < (3 : ℤ) ^ (blockSteps s j) := pow_pos (by decide) _
    have hprod_pos :
        (0 : ℤ) <
          (3 : ℤ) ^ (blockSteps s j) *
            ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) :=
      mul_pos h3_pos (mul_pos h2_pos hj_pos)
    have hid := scaled_shifted_slack_eq_unshifted_diff s hjm
    linarith
  · intro hall j hjm
    have hj_lt := hall j hjm
    have hid := scaled_shifted_slack_eq_unshifted_diff s hjm
    have hprod_pos :
        (0 : ℤ) <
          (3 : ℤ) ^ (blockSteps s j) *
            ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) := by
      linarith
    have h2_pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s j) := pow_pos (by decide) _
    have h3_pos : (0 : ℤ) < (3 : ℤ) ^ (blockSteps s j) := pow_pos (by decide) _
    have h2_pos' :
        (0 : ℤ) < (2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j) :=
      pos_of_mul_pos_right hprod_pos (le_of_lt h3_pos)
    exact pos_of_mul_pos_right h2_pos' (le_of_lt h2_pos)

end Mahler.MultiOriginSyzygy
