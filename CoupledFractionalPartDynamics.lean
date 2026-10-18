import ThreeAdicAndSeedGCDLocks

/-!
# Coupled `(×2, ×3)` Fractional-Part Dynamics, Autonomous Expanding Map & Disjoint Partition

This module formalizes Path 7 (Modules 105–106): the coupled `(×2, ×3)`
fractional-part dynamics of `baseTwoSlackRatio`, `baseThreeSlackRatio`, and
`normalizedMinSlack`:

1. **The Autonomous Expanding Recurrence for `baseTwoSlackRatio`
   (`baseTwoSlackRatio_succ_eq`)**:
   Define `baseTwoSlackRatio s m = (integerSlack s m : ℝ) / 2^(blockSteps s m)`.
   For every sequence `s : ℕ → ℕ` and index `m`, dividing
   `integerSlack s (m + 1) = 3^(s m) * integerSlack s m - 2^(blockSteps s (m + 1) + 1)`
   by `2^(blockSteps s (m + 1))` cancels `2^(blockSteps s m)` to yield the
   time-homogeneous expanding map:
   `baseTwoSlackRatio s (m + 1) = (3 / 2 : ℝ)^(s m) * baseTwoSlackRatio s m - 2`.
2. **The Autonomous 1D Piecewise-Expanding Map for `normalizedMinSlack`
   (`normalizedMinSlack_succ_eq`, `normalizedMinSlack_in_unit_interval`)**:
   Define `normalizedMinSlack s m = (minSlack s m : ℝ) / 2^(blockSteps s m)`.
   Then `normalizedMinSlack s 0 = 1`, `normalizedMinSlack s m ≤ 1`, and for all `m`:
   `normalizedMinSlack s (m + 1) =
     min 1 ((3 / 2 : ℝ)^(s m) * normalizedMinSlack s m - 2)`.
   Moreover, `0 < minSlack s m ↔ 0 < normalizedMinSlack s m ∧ normalizedMinSlack s m ≤ 1`.
3. **The Disjoint Lüroth–Markov Partition of `(0, 1]` by `I_c = (2*(2/3)^c, 3*(2/3)^c]`
   (`sub_ceiling_transition_dyadic_corridor`,
   `dyadic_partition_adjacent_boundary_eq`,
   `dyadic_partition_cells_disjoint`)**:
   - Whenever `0 < baseTwoSlackRatio s (m + 1) ≤ 1`, `baseTwoSlackRatio s m` lies
     in the cell `I_{s m}`:
     `2 * (2 / 3 : ℝ)^(s m) < baseTwoSlackRatio s m ≤ 3 * (2 / 3 : ℝ)^(s m)`.
   - The upper endpoint of `I_{c + 1}` equals the lower endpoint of `I_c`:
     `3 * (2 / 3 : ℝ)^(c + 1) = 2 * (2 / 3 : ℝ)^c`.
   - For any `c1 < c2`, `3 * (2 / 3 : ℝ)^c2 ≤ 2 * (2 / 3 : ℝ)^c1`, so no real number
     `θ ∈ (0, 1]` can belong to two distinct cells `I_{c1}` and `I_{c2}`.
4. **Coupled `(×2, ×3)` Solenoidal Evolution (`coupled_solenoidal_ratio_identity`)**:
   Define `baseThreeSlackRatio s m = (integerSlack s m : ℝ) / 3^(blockSteps s m)`.
   Then `baseThreeSlackRatio s m = (2 / 3 : ℝ)^(blockSteps s m) * baseTwoSlackRatio s m`
   and `baseThreeSlackRatio s (m + 1) = baseThreeSlackRatio s m - 2 * (2 / 3 : ℝ)^(blockSteps s (m + 1))`.
-/

namespace Mahler.CoupledFractionalDynamics

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

/-! ## 1. Definitions & Autonomous Expanding Recurrence for `baseTwoSlackRatio` -/

/-- The Base-2 normalized slack ratio `θ_2(s, m) = integerSlack s m / 2^(blockSteps s m)`. -/
noncomputable def baseTwoSlackRatio (s : ℕ → ℕ) (m : ℕ) : ℝ :=
  (integerSlack s m : ℝ) / (2 : ℝ) ^ (blockSteps s m)

/-- The Base-3 normalized slack ratio `θ_3(s, m) = integerSlack s m / 3^(blockSteps s m)`. -/
noncomputable def baseThreeSlackRatio (s : ℕ → ℕ) (m : ℕ) : ℝ :=
  (integerSlack s m : ℝ) / (3 : ℝ) ^ (blockSteps s m)

/-- The normalized minimum slack `μ_2(s, m) = minSlack s m / 2^(blockSteps s m)`. -/
noncomputable def normalizedMinSlack (s : ℕ → ℕ) (m : ℕ) : ℝ :=
  (minSlack s m : ℝ) / (2 : ℝ) ^ (blockSteps s m)

/-- **Autonomous Expanding Recurrence for `baseTwoSlackRatio` (`baseTwoSlackRatio_succ_eq`)**:
For every sequence `s : ℕ → ℕ` and index `m`,
`baseTwoSlackRatio s (m + 1) = (3 / 2 : ℝ)^(s m) * baseTwoSlackRatio s m - 2`. -/
theorem baseTwoSlackRatio_succ_eq (s : ℕ → ℕ) (m : ℕ) :
    baseTwoSlackRatio s (m + 1) =
      (3 / 2 : ℝ) ^ (s m) * baseTwoSlackRatio s m - 2 := by
  unfold baseTwoSlackRatio
  have hsucc := integerSlack_succ s m
  have hcast :
      (integerSlack s (m + 1) : ℝ) =
        (3 : ℝ) ^ (s m) * (integerSlack s m : ℝ) -
          (2 : ℝ) ^ (blockSteps s (m + 1) + 1) := by
    exact_mod_cast hsucc
  have hpow2 :
      (2 : ℝ) ^ (blockSteps s (m + 1)) =
        (2 : ℝ) ^ (blockSteps s m) * (2 : ℝ) ^ (s m) := by
    change (2 : ℝ) ^ (blockSteps s m + s m) = _
    rw [pow_add]
  have hpow2_succ :
      (2 : ℝ) ^ (blockSteps s (m + 1) + 1) =
        2 * ((2 : ℝ) ^ (blockSteps s m) * (2 : ℝ) ^ (s m)) := by
    rw [pow_succ', hpow2]
  have h2m_ne : (2 : ℝ) ^ (blockSteps s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2s_ne : (2 : ℝ) ^ (s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hcast, hpow2_succ, hpow2, div_pow]
  field_simp [h2m_ne, h2s_ne]
  ring

/-! ## 2. Autonomous 1D Interval Map for `normalizedMinSlack` -/

/-- **Autonomous 1D Interval Map for `normalizedMinSlack` (`normalizedMinSlack_succ_eq`)**:
For every sequence `s : ℕ → ℕ` and index `m`,
`normalizedMinSlack s (m + 1) =
  min 1 ((3 / 2 : ℝ)^(s m) * normalizedMinSlack s m - 2)`. -/
theorem normalizedMinSlack_succ_eq (s : ℕ → ℕ) (m : ℕ) :
    normalizedMinSlack s (m + 1) =
      min 1 ((3 / 2 : ℝ) ^ (s m) * normalizedMinSlack s m - 2) := by
  unfold normalizedMinSlack
  have hdef :
      minSlack s (m + 1) =
        min ((2 : ℤ) ^ (blockSteps s (m + 1)))
          ((3 : ℤ) ^ (s m) * minSlack s m -
            (2 : ℤ) ^ (blockSteps s (m + 1) + 1)) := rfl
  have hcast :
      (minSlack s (m + 1) : ℝ) =
        min ((2 : ℝ) ^ (blockSteps s (m + 1)))
          ((3 : ℝ) ^ (s m) * (minSlack s m : ℝ) -
            (2 : ℝ) ^ (blockSteps s (m + 1) + 1)) := by
    rw [hdef]
    push_cast
    rfl
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (blockSteps s (m + 1)) :=
    pow_pos (by norm_num) _
  have h2_ne : (2 : ℝ) ^ (blockSteps s (m + 1)) ≠ 0 := ne_of_gt h2_pos
  have hmin_div :
      min ((2 : ℝ) ^ (blockSteps s (m + 1)))
          ((3 : ℝ) ^ (s m) * (minSlack s m : ℝ) -
            (2 : ℝ) ^ (blockSteps s (m + 1) + 1)) /
        (2 : ℝ) ^ (blockSteps s (m + 1)) =
      min
        ((2 : ℝ) ^ (blockSteps s (m + 1)) / (2 : ℝ) ^ (blockSteps s (m + 1)))
        (((3 : ℝ) ^ (s m) * (minSlack s m : ℝ) -
            (2 : ℝ) ^ (blockSteps s (m + 1) + 1)) /
          (2 : ℝ) ^ (blockSteps s (m + 1))) := by
    rcases le_total
      ((2 : ℝ) ^ (blockSteps s (m + 1)))
      ((3 : ℝ) ^ (s m) * (minSlack s m : ℝ) -
        (2 : ℝ) ^ (blockSteps s (m + 1) + 1)) with hle | hge
    · rw [min_eq_left hle, min_eq_left (div_le_div_of_nonneg_right hle (le_of_lt h2_pos))]
    · rw [min_eq_right hge, min_eq_right (div_le_div_of_nonneg_right hge (le_of_lt h2_pos))]
  rw [hcast, hmin_div, div_self h2_ne]
  congr 1
  have hpow2 :
      (2 : ℝ) ^ (blockSteps s (m + 1)) =
        (2 : ℝ) ^ (blockSteps s m) * (2 : ℝ) ^ (s m) := by
    change (2 : ℝ) ^ (blockSteps s m + s m) = _
    rw [pow_add]
  have hpow2_succ :
      (2 : ℝ) ^ (blockSteps s (m + 1) + 1) =
        2 * ((2 : ℝ) ^ (blockSteps s m) * (2 : ℝ) ^ (s m)) := by
    rw [pow_succ', hpow2]
  have h2m_ne : (2 : ℝ) ^ (blockSteps s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2s_ne : (2 : ℝ) ^ (s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hpow2_succ, hpow2, div_pow]
  field_simp [h2m_ne, h2s_ne]
  ring

/-- `0 < minSlack s m` is equivalent to `normalizedMinSlack s m ∈ (0, 1]`. -/
theorem normalizedMinSlack_in_unit_interval (s : ℕ → ℕ) (m : ℕ) :
    normalizedMinSlack s m ≤ 1 ∧
      (0 < minSlack s m ↔
        0 < normalizedMinSlack s m ∧ normalizedMinSlack s m ≤ 1) := by
  unfold normalizedMinSlack
  have hle_int := minSlack_le_two_pow s m
  have hle_real : (minSlack s m : ℝ) ≤ (2 : ℝ) ^ (blockSteps s m) := by
    exact_mod_cast hle_int
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (blockSteps s m) := pow_pos (by norm_num) _
  have hle_one : (minSlack s m : ℝ) / (2 : ℝ) ^ (blockSteps s m) ≤ 1 := by
    rw [div_le_one h2_pos]
    exact hle_real
  refine ⟨hle_one, ?_⟩
  constructor
  · intro hpos
    have hpos_real : (0 : ℝ) < (minSlack s m : ℝ) := by exact_mod_cast hpos
    exact ⟨div_pos hpos_real h2_pos, hle_one⟩
  · rintro ⟨hdiv_pos, _⟩
    have hpos_real : (0 : ℝ) < (minSlack s m : ℝ) :=
      (div_pos_iff_of_pos_right h2_pos).mp hdiv_pos
    exact_mod_cast hpos_real

/-! ## 3. The Disjoint Lüroth–Markov Partition of `(0, 1]` -/

/-- **Sub-Ceiling Transition Dyadic Corridor (`sub_ceiling_transition_dyadic_corridor`)**:
Whenever `0 < baseTwoSlackRatio s (m + 1)` and `baseTwoSlackRatio s (m + 1) ≤ 1`,
`baseTwoSlackRatio s m` lies in the partition cell
`I_{s m} = (2 * (2 / 3)^(s m), 3 * (2 / 3)^(s m)]`:
`2 * (2 / 3 : ℝ)^(s m) < baseTwoSlackRatio s m` and
`baseTwoSlackRatio s m ≤ 3 * (2 / 3 : ℝ)^(s m)`. -/
theorem sub_ceiling_transition_dyadic_corridor {s : ℕ → ℕ} {m : ℕ}
    (hpos : 0 < baseTwoSlackRatio s (m + 1))
    (hle : baseTwoSlackRatio s (m + 1) ≤ 1) :
    2 * (2 / 3 : ℝ) ^ (s m) < baseTwoSlackRatio s m ∧
      baseTwoSlackRatio s m ≤ 3 * (2 / 3 : ℝ) ^ (s m) := by
  rw [baseTwoSlackRatio_succ_eq] at hpos hle
  have h23_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (s m) := pow_pos (by norm_num) _
  have hprod :
      (2 / 3 : ℝ) ^ (s m) * (3 / 2 : ℝ) ^ (s m) = 1 := by
    rw [← mul_pow]
    norm_num
  constructor
  · have hmul := mul_lt_mul_of_pos_left (by linarith : (2 : ℝ) < (3 / 2 : ℝ) ^ (s m) * baseTwoSlackRatio s m) h23_pos
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left (by linarith : (3 / 2 : ℝ) ^ (s m) * baseTwoSlackRatio s m ≤ 3) (le_of_lt h23_pos)
    nlinarith

/-- **Exact Partition Boundary Matching (`dyadic_partition_adjacent_boundary_eq`)**:
For every `c : ℕ`, the upper endpoint of `I_{c + 1}` equals the lower endpoint of `I_c`,
and for any `c1 < c2`, `3 * (2 / 3 : ℝ)^c2 ≤ 2 * (2 / 3 : ℝ)^c1`. Thus the cells
`I_c = (2 * (2 / 3)^c, 3 * (2 / 3)^c]` are pairwise disjoint. -/
theorem dyadic_partition_adjacent_boundary_eq (c : ℕ) :
    3 * (2 / 3 : ℝ) ^ (c + 1) = 2 * (2 / 3 : ℝ) ^ c := by
  rw [pow_succ]
  ring

theorem dyadic_partition_cells_disjoint {c1 c2 : ℕ} (hlt : c1 < c2) :
    3 * (2 / 3 : ℝ) ^ c2 ≤ 2 * (2 / 3 : ℝ) ^ c1 := by
  have hc2 : c2 = (c1 + 1) + (c2 - (c1 + 1)) := by omega
  rw [hc2, pow_add, ← mul_assoc, dyadic_partition_adjacent_boundary_eq]
  have hpow_le : (2 / 3 : ℝ) ^ (c2 - (c1 + 1)) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) ≤ 2 * (2 / 3 : ℝ) ^ c1 := by positivity
  nlinarith

/-! ## 4. Coupled `(×2, ×3)` Solenoidal Evolution -/

/-- **Coupled `(×2, ×3)` Solenoidal Evolution (`coupled_solenoidal_ratio_identity`)**:
For every sequence `s : ℕ → ℕ` and index `m`:
1. `baseThreeSlackRatio s m = (2 / 3 : ℝ)^(blockSteps s m) * baseTwoSlackRatio s m`, and
2. `baseThreeSlackRatio s (m + 1) =
     baseThreeSlackRatio s m - 2 * (2 / 3 : ℝ)^(blockSteps s (m + 1))`. -/
theorem coupled_solenoidal_ratio_identity (s : ℕ → ℕ) (m : ℕ) :
    baseThreeSlackRatio s m =
        (2 / 3 : ℝ) ^ (blockSteps s m) * baseTwoSlackRatio s m ∧
      baseThreeSlackRatio s (m + 1) =
        baseThreeSlackRatio s m - 2 * (2 / 3 : ℝ) ^ (blockSteps s (m + 1)) := by
  unfold baseThreeSlackRatio baseTwoSlackRatio
  have h2_ne : (2 : ℝ) ^ (blockSteps s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3_ne : (3 : ℝ) ^ (blockSteps s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [div_pow]
    field_simp [h2_ne, h3_ne]
    ring
  · have hsucc := integerSlack_succ s m
    have hcast :
        (integerSlack s (m + 1) : ℝ) =
          (3 : ℝ) ^ (s m) * (integerSlack s m : ℝ) -
            (2 : ℝ) ^ (blockSteps s (m + 1) + 1) := by
      exact_mod_cast hsucc
    have hpow3 :
        (3 : ℝ) ^ (blockSteps s (m + 1)) =
          (3 : ℝ) ^ (blockSteps s m) * (3 : ℝ) ^ (s m) := by
      change (3 : ℝ) ^ (blockSteps s m + s m) = _
      rw [pow_add]
    have hpow2_succ :
        (2 : ℝ) ^ (blockSteps s (m + 1) + 1) =
          2 * (2 : ℝ) ^ (blockSteps s (m + 1)) := by
      rw [pow_succ']
    have h3s_ne : (3 : ℝ) ^ (s m) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hcast, hpow2_succ, div_pow, hpow3]
    field_simp [h3_ne, h3s_ne]
    ring

end Mahler.CoupledFractionalDynamics
