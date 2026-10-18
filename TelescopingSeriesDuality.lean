import CeilingSaturationSynthesis

/-!
# The Telescoping `(2/3)^(T(k)+1)` Series & Dual-Metric (`ℤ_2` vs. `ℝ`) Master Identity

This module formalizes the exact telescoping `(2/3)^(T(k)+1)` series representation
of `integerSlack` and unifies the 2-adic valuation recurrence with the Archimedean
`1/3` budget:

1. **The Cumulative Drain Sum `blockDrainSum` & Rational Slack Series `slackSeries`
   (`slackSeries_eq_one_third_sub_blockDrainSum`,
   `integerSlack_eq_three_pow_mul_slackSeries`,
   `slackSeries_eq_integerSlack_div`)**:
   Define `blockDrainSum s m = ∑_{k=1}^m (2/3)^(T(k) + 1)` and
   `slackSeries s m = 1/3 - blockDrainSum s m`.
   Dividing `integerSlack s (m + 1) = 3^(s m) * integerSlack s m - 2^(T(m + 1) + 1)`
   by `3^(T(m + 1) + 1)` telescopes to the exact identity:
   `(integerSlack s m : ℝ) = 3^(blockSteps s m + 1) * (1/3 - blockDrainSum s m)`.
2. **The Dual-Metric Master Identity (`dual_metric_series_identity`)**:
   Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`),
   `(2 * a_0 + 1) - (1/3 - blockDrainSum s m) =
     2^(blockSteps s (m + 1) + 1) * u m / 3^(blockSteps s m + 1)`.
3. **Multi-Origin `1/3` Budget Equivalence (`integerSlack_pos_iff_blockDrainSum_lt_one_third`,
   `minSlack_pos_iff_all_shifted_blockDrainSum_lt_one_third`,
   `blockDrainSum_lt_one_third_of_three_le`)**:
   - `0 < integerSlack s m ↔ blockDrainSum s m < 1/3`.
   - `0 < minSlack s m ↔ ∀ j ≤ m, blockDrainSum (shiftSeq s j) (m - j) < 1/3`.
   - Whenever `3 ≤ s k` for all `k < m`, `blockDrainSum (shiftSeq s j) (m - j) < 1/3`
     holds automatically for all `j ≤ m`.
4. **Exact 2-adic Residual Valuation Lock (`two_adic_residual_numerator_valuation`)**:
   Clearing the odd denominator `3^(T(m) + 1)` of `(2 * a_0 + 1) - slackSeries s m`,
   the residual numerator `3^(T(m) + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat`
   has exact 2-adic valuation `T(m + 1) + 1` (divisible by `2^(T(m + 1) + 1)` and
   not by `2^(T(m + 1) + 2)`).
-/

namespace Mahler.TelescopingDuality

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

/-! ## 1. `blockDrainSum`, `slackSeries`, and the Telescoping Identity -/

/-- The cumulative Archimedean drain sum `∑_{k=1}^m (2/3)^(blockSteps s k + 1)`. -/
noncomputable def blockDrainSum (s : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => blockDrainSum s m + (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1)

/-- The remaining Archimedean slack series `1/3 - ∑_{k=1}^m (2/3)^(blockSteps s k + 1)`. -/
noncomputable def slackSeries (s : ℕ → ℕ) : ℕ → ℝ
  | 0 => (1 / 3 : ℝ)
  | m + 1 => slackSeries s m - (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1)

theorem slackSeries_eq_one_third_sub_blockDrainSum (s : ℕ → ℕ) (m : ℕ) :
    slackSeries s m = (1 / 3 : ℝ) - blockDrainSum s m := by
  induction m with
  | zero =>
      simp [slackSeries, blockDrainSum]
  | succ m ih =>
      simp only [slackSeries, blockDrainSum, ih]
      ring

/-- **Exact Telescoping Identity (`integerSlack_eq_three_pow_mul_slackSeries`)**:
For every sequence `s` and index `m`,
`(integerSlack s m : ℝ) = 3^(blockSteps s m + 1) * slackSeries s m`. -/
theorem integerSlack_eq_three_pow_mul_slackSeries (s : ℕ → ℕ) (m : ℕ) :
    (integerSlack s m : ℝ) =
      (3 : ℝ) ^ (blockSteps s m + 1) * slackSeries s m := by
  induction m with
  | zero =>
      simp [integerSlack, blockSteps, coprimeRemainder, slackSeries]
  | succ m ih =>
      have hsucc := integerSlack_succ s m
      have hcast :
          (integerSlack s (m + 1) : ℝ) =
            (3 : ℝ) ^ (s m) * (integerSlack s m : ℝ) -
              (2 : ℝ) ^ (blockSteps s (m + 1) + 1) := by
        exact_mod_cast hsucc
      rw [hcast, ih]
      have hpow3 :
          (3 : ℝ) ^ (blockSteps s (m + 1) + 1) =
            (3 : ℝ) ^ (s m) * (3 : ℝ) ^ (blockSteps s m + 1) := by
        simp only [blockSteps]
        rw [show blockSteps s m + s m + 1 = s m + (blockSteps s m + 1) by omega, pow_add]
      have hdiv_pow :
          (3 : ℝ) ^ (blockSteps s (m + 1) + 1) *
              (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1) =
            (2 : ℝ) ^ (blockSteps s (m + 1) + 1) := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num))]
      simp only [slackSeries]
      calc
        (3 : ℝ) ^ (s m) * ((3 : ℝ) ^ (blockSteps s m + 1) * slackSeries s m) -
            (2 : ℝ) ^ (blockSteps s (m + 1) + 1) =
          (3 : ℝ) ^ (blockSteps s (m + 1) + 1) * slackSeries s m -
            (3 : ℝ) ^ (blockSteps s (m + 1) + 1) *
              (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1) := by
          rw [hdiv_pow, hpow3]
          ring
        _ = (3 : ℝ) ^ (blockSteps s (m + 1) + 1) *
              (slackSeries s m - (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1)) := by
          ring

/-- Dividing by `3^(blockSteps s m + 1)` expresses `slackSeries s m` as
`integerSlack s m / 3^(blockSteps s m + 1)`. -/
theorem slackSeries_eq_integerSlack_div (s : ℕ → ℕ) (m : ℕ) :
    slackSeries s m =
      (integerSlack s m : ℝ) / (3 : ℝ) ^ (blockSteps s m + 1) := by
  rw [integerSlack_eq_three_pow_mul_slackSeries]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))).symm

/-! ## 2. The Dual-Metric Master Identity -/

/-- **The Dual-Metric Master Identity (`dual_metric_series_identity`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`),
`(2 * a_0 + 1) - (1/3 - blockDrainSum s m) =
  2^(blockSteps s (m + 1) + 1) * u m / 3^(blockSteps s m + 1)`. -/
theorem dual_metric_series_identity {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    (2 * (a_0 : ℝ) + 1) - ((1 / 3 : ℝ) - blockDrainSum s m) =
      (2 : ℝ) ^ (blockSteps s (m + 1) + 1) * (u m : ℝ) /
        (3 : ℝ) ^ (blockSteps s m + 1) := by
  rw [← slackSeries_eq_one_third_sub_blockDrainSum, slackSeries_eq_integerSlack_div]
  have hslack := integerSlack_eq_orbit_slack hmK hchain
  have hcast :
      (integerSlack s m : ℝ) =
        (3 : ℝ) ^ (blockSteps s m + 1) * (2 * (a_0 : ℝ) + 1) -
          (2 : ℝ) ^ (blockSteps s (m + 1) + 1) * (u m : ℝ) := by
    exact_mod_cast hslack
  have h3ne : (3 : ℝ) ^ (blockSteps s m + 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  rw [hcast]
  field_simp [h3ne]
  ring

/-! ## 3. Multi-Origin `1/3` Budget Equivalence & Automatic Satisfaction on `{s ≥ 3}` -/

/-- `0 < integerSlack s m` holds if and only if `blockDrainSum s m < 1/3`. -/
theorem integerSlack_pos_iff_blockDrainSum_lt_one_third (s : ℕ → ℕ) (m : ℕ) :
    0 < integerSlack s m ↔ blockDrainSum s m < (1 / 3 : ℝ) := by
  have hpos3 : (0 : ℝ) < (3 : ℝ) ^ (blockSteps s m + 1) :=
    pow_pos (by norm_num) _
  have hid := integerSlack_eq_three_pow_mul_slackSeries s m
  rw [slackSeries_eq_one_third_sub_blockDrainSum] at hid
  constructor
  · intro h
    have hreal : (0 : ℝ) < (integerSlack s m : ℝ) := by exact_mod_cast h
    rw [hid] at hreal
    have hsub : (0 : ℝ) < (1 / 3 : ℝ) - blockDrainSum s m :=
      pos_of_mul_pos_right hreal (le_of_lt hpos3)
    linarith
  · intro hlt
    have hsub : (0 : ℝ) < (1 / 3 : ℝ) - blockDrainSum s m := by linarith
    have hreal : (0 : ℝ) < (integerSlack s m : ℝ) := by
      rw [hid]
      exact mul_pos hpos3 hsub
    exact_mod_cast hreal

/-- **Multi-Origin `1/3` Budget Equivalence (`minSlack_pos_iff_all_shifted_blockDrainSum_lt_one_third`)**:
`0 < minSlack s m` holds if and only if every shifted drain sum satisfies
`blockDrainSum (shiftSeq s j) (m - j) < 1/3` (`0 ≤ j ≤ m`). -/
theorem minSlack_pos_iff_all_shifted_blockDrainSum_lt_one_third
    (s : ℕ → ℕ) (m : ℕ) :
    0 < minSlack s m ↔
      ∀ j ≤ m, blockDrainSum (shiftSeq s j) (m - j) < (1 / 3 : ℝ) := by
  rw [minSlack_pos_iff_all_shifted_pos]
  constructor <;> intro hall j hjm
  · exact (integerSlack_pos_iff_blockDrainSum_lt_one_third
      (shiftSeq s j) (m - j)).mp (hall j hjm)
  · exact (integerSlack_pos_iff_blockDrainSum_lt_one_third
      (shiftSeq s j) (m - j)).mpr (hall j hjm)

/-- **Automatic `1/3` Budget Satisfaction on `{s ≥ 3}` (`blockDrainSum_lt_one_third_of_three_le`)**:
Whenever `3 ≤ s k` for all `k < m`, every shifted drain sum satisfies
`blockDrainSum (shiftSeq s j) (m - j) < 1/3`. -/
theorem blockDrainSum_lt_one_third_of_three_le (s : ℕ → ℕ) (m : ℕ)
    (hs3 : ∀ k < m, 3 ≤ s k) :
    ∀ j ≤ m, blockDrainSum (shiftSeq s j) (m - j) < (1 / 3 : ℝ) := by
  have hpos := (all_shifted_slacks_pos_of_three_le s m hs3).1
  exact (minSlack_pos_iff_all_shifted_blockDrainSum_lt_one_third s m).mp hpos

/-! ## 4. Exact 2-adic Valuation Lock on the Greedy Series Residual -/

/-- **Exact 2-adic Residual Valuation Lock (`two_adic_residual_numerator_valuation`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`) with
`0 < integerSlack s m`, the cleared residual numerator
`3^(blockSteps s m + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat`
equals `2^(blockSteps s (m + 1) + 1) * u m` and therefore has exact 2-adic
valuation `blockSteps s (m + 1) + 1`:
- `2^(blockSteps s (m + 1) + 1)` divides `3^(blockSteps s m + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat`, and
- `2^(blockSteps s (m + 1) + 2)` does not. -/
theorem two_adic_residual_numerator_valuation {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m) :
    3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat =
        2 ^ (blockSteps s (m + 1) + 1) * u m ∧
      2 ^ (blockSteps s (m + 1) + 1) ∣
        (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat) ∧
      ¬ (2 ^ (blockSteps s (m + 1) + 2) ∣
        (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat)) := by
  have hdecomp := base_two_slack_decomposition hmK hchain hpos
  have hpow2 :
      2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) =
        2 ^ (blockSteps s (m + 1) + 1) * u m := by
    simp only [blockSteps]
    rw [show blockSteps s m + s m + 1 = blockSteps s m + (s m + 1) by omega, Nat.pow_add]
    ring
  rw [hpow2] at hdecomp
  have hsub :
      3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) - (integerSlack s m).toNat =
        2 ^ (blockSteps s (m + 1) + 1) * u m := by
    omega
  rcases hchain m hmK with ⟨_, hum_odd, _⟩
  refine ⟨hsub, ?_, ?_⟩
  · rw [hsub]
    exact ⟨u m, rfl⟩
  · rw [hsub]
    rintro ⟨q, hq⟩
    have hsplit :
        2 ^ (blockSteps s (m + 1) + 2) * q =
          2 ^ (blockSteps s (m + 1) + 1) * (2 * q) := by
      rw [show blockSteps s (m + 1) + 2 = (blockSteps s (m + 1) + 1) + 1 by omega,
        Nat.pow_add]
      ring
    rw [hsplit] at hq
    have hpos2 : 0 < 2 ^ (blockSteps s (m + 1) + 1) := Nat.pow_pos (by decide)
    have hum_eq : u m = 2 * q := Nat.eq_of_mul_eq_mul_left hpos2 hq
    omega

end Mahler.TelescopingDuality
