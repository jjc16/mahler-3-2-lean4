import MultiStepQuotientGCD

/-!
# Mahler's Power-Series Functional Equation, Dual-Place (`ℝ × ℚ_2`) Convergence & Padé–Hankel Factorization

This module formalizes Path 4 (Modules 101–102): the power-series and
Padé–Hankel determinant structure of `blockDrainSum s m = ∑_{k=1}^m (2/3)^(T(k) + 1)`:

1. **Exact Rational Formula for `blockDrainSum` (`blockDrainSum_eq_remainder_div_three_pow`)**:
   For every sequence `s : ℕ → ℕ` and horizon `m` (requiring no `ValidBlockChain`
   hypothesis),
   `blockDrainSum s m = (2^(s 0 + 1) * coprimeRemainder s m : ℝ) / 3^(blockSteps s m + 1)`.
2. **Mahler's Power-Series Shift Functional Equation (`blockDrainSum_add_eq_shift`)**:
   For every sequence `s : ℕ → ℕ`, origin `r`, and lookahead `d`,
   `blockDrainSum s (r + d) =
     blockDrainSum s r + (2 / 3 : ℝ)^(blockSteps s r) * blockDrainSum (shiftSeq s r) d`.
3. **Dual-Place (`ℝ × ℚ_2`) Rational Gap Identity (`dual_place_series_rational_gap_identity`)**:
   Along any `ValidBlockChain a_0 s u K` (`m < K`),
   `blockDrainSum s m + (6 * a_0 + 2 : ℝ) / 3 =
     (2^(blockSteps s (m + 1) + 1) * u m : ℝ) / 3^(blockSteps s m + 1)`.
   Thus the partial sums `blockDrainSum s m` simultaneously stay bounded by `1/3`
   in `ℝ` while converging 2-adically (mod `2^(T(m + 1) + 1)`) to the negative
   rational number `-(6 * a_0 + 2) / 3`.
4. **Two-Sided Archimedean Squeeze on Tail Increments (`blockDrainSum_tail_increment_squeeze`)**:
   Whenever `1 ≤ d` and `0 < integerSlack (shiftSeq s r) d`,
   `2^(blockSteps s (r + 1) + 1) / 3^(blockSteps s (r + d) + 1) ≤
     blockDrainSum s (r + d) - blockDrainSum s r <
     (1 / 3 : ℝ) * (2 / 3 : ℝ)^(blockSteps s r)`.
5. **Dead End 18 — Exact Factorization of the Padé–Hankel Determinant
   (`pade_hankel_quotient_determinant_factorization`)**:
   Along any `ValidBlockChain a_0 s u K` (`r + d < K`), the `2 × 2` Padé–Hankel
   determinant eliminating `-(6 * a_0 + 2) / 3` between steps `r` and `r + d`
   factors identically as:
   `3^(blockSteps s r + 1) * (2^(blockSteps s (r + d + 1) + 1) * u (r + d)) -
     3^(blockSteps s (r + d) + 1) * (2^(blockSteps s (r + 1) + 1) * u r) =
     3^(blockSteps s r + 1) * 2^(blockSteps s (r + 1) + 1) *
       coprimeRemainder (shiftSeq s r) d`.
-/

namespace Mahler.SeriesHankel

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

/-! ## 1. Closed-Form Rational Formula for `blockDrainSum` -/

/-- **Exact Rational Formula for `blockDrainSum` (`blockDrainSum_eq_remainder_div_three_pow`)**:
For every sequence `s : ℕ → ℕ` and index `m`,
`blockDrainSum s m =
  ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℝ) /
    (3 : ℝ) ^ (blockSteps s m + 1)`. -/
theorem blockDrainSum_eq_remainder_div_three_pow (s : ℕ → ℕ) (m : ℕ) :
    blockDrainSum s m =
      ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℝ) /
        (3 : ℝ) ^ (blockSteps s m + 1) := by
  have h1 := slackSeries_eq_one_third_sub_blockDrainSum s m
  have h2 := slackSeries_eq_integerSlack_div s m
  have hdef :
      (integerSlack s m : ℝ) =
        (3 : ℝ) ^ (blockSteps s m) -
          ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℝ) := by
    unfold integerSlack
    push_cast
    rfl
  have h3_ne : (3 : ℝ) ^ (blockSteps s m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpow3 :
      (3 : ℝ) ^ (blockSteps s m + 1) = (3 : ℝ) ^ (blockSteps s m) * 3 := by
    rw [pow_succ]
  rw [h1, hdef, hpow3] at h2
  have hdrain :
      blockDrainSum s m =
        (1 / 3 : ℝ) -
          ((3 : ℝ) ^ (blockSteps s m) -
              ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℝ)) /
            ((3 : ℝ) ^ (blockSteps s m) * 3) := by
    linarith
  rw [hdrain, hpow3]
  field_simp [h3_ne]

/-! ## 2. Mahler's Power-Series Shift Functional Equation -/

/-- **Mahler's Power-Series Shift Functional Equation (`blockDrainSum_add_eq_shift`)**:
For every sequence `s : ℕ → ℕ`, origin `r`, and lookahead `d`,
`blockDrainSum s (r + d) =
  blockDrainSum s r +
    (2 / 3 : ℝ) ^ (blockSteps s r) * blockDrainSum (shiftSeq s r) d`. -/
theorem blockDrainSum_add_eq_shift (s : ℕ → ℕ) (r d : ℕ) :
    blockDrainSum s (r + d) =
      blockDrainSum s r +
        (2 / 3 : ℝ) ^ (blockSteps s r) * blockDrainSum (shiftSeq s r) d := by
  induction d with
  | zero =>
      simp [blockDrainSum]
  | succ d ih =>
      have hadd_succ : r + (d + 1) = (r + d) + 1 := by omega
      rw [hadd_succ]
      simp only [blockDrainSum]
      rw [ih]
      have hsteps :
          blockSteps s (r + d + 1) + 1 =
            blockSteps s r + (blockSteps (shiftSeq s r) (d + 1) + 1) := by
        have hidx : r + d + 1 = r + (d + 1) := by omega
        rw [hidx, blockSteps_add]
        omega
      rw [hsteps, pow_add]
      ring

/-! ## 3. Dual-Place (`ℝ × ℚ_2`) Rational Gap Identity & Tail Squeeze -/

/-- **Dual-Place (`ℝ × ℚ_2`) Rational Gap Identity (`dual_place_series_rational_gap_identity`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`),
`blockDrainSum s m + (6 * (a_0 : ℝ) + 2) / 3 =
  ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) /
    (3 : ℝ) ^ (blockSteps s m + 1)`. -/
theorem dual_place_series_rational_gap_identity
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    blockDrainSum s m + (6 * (a_0 : ℝ) + 2) / 3 =
      ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) /
        (3 : ℝ) ^ (blockSteps s m + 1) := by
  have hd := dual_metric_series_identity hmK hchain
  push_cast
  linarith

/-- **Two-Sided Archimedean Squeeze on Power-Series Tail Increments
(`blockDrainSum_tail_increment_squeeze`)**:
Whenever `1 ≤ d` and `0 < integerSlack (shiftSeq s r) d`, the tail increment
`blockDrainSum s (r + d) - blockDrainSum s r` satisfies:
`(2 : ℝ)^(blockSteps s (r + 1) + 1) / (3 : ℝ)^(blockSteps s (r + d) + 1) ≤
  blockDrainSum s (r + d) - blockDrainSum s r`
and
`blockDrainSum s (r + d) - blockDrainSum s r <
  (1 / 3 : ℝ) * (2 / 3 : ℝ)^(blockSteps s r)`. -/
theorem blockDrainSum_tail_increment_squeeze
    {s : ℕ → ℕ} {r d : ℕ}
    (hd : 1 ≤ d) (hpos : 0 < integerSlack (shiftSeq s r) d) :
    (2 : ℝ) ^ (blockSteps s (r + 1) + 1) /
          (3 : ℝ) ^ (blockSteps s (r + d) + 1) ≤
        blockDrainSum s (r + d) - blockDrainSum s r ∧
      blockDrainSum s (r + d) - blockDrainSum s r <
        (1 / 3 : ℝ) * (2 / 3 : ℝ) ^ (blockSteps s r) := by
  have hshift := blockDrainSum_add_eq_shift s r d
  have hdiff :
      blockDrainSum s (r + d) - blockDrainSum s r =
        (2 / 3 : ℝ) ^ (blockSteps s r) * blockDrainSum (shiftSeq s r) d := by
    linarith
  rw [hdiff]
  refine ⟨?_, ?_⟩
  · rw [blockDrainSum_eq_remainder_div_three_pow (shiftSeq s r) d]
    have hR_pos : 1 ≤ coprimeRemainder (shiftSeq s r) d :=
      coprimeRemainder_pos (shiftSeq s r) hd
    have hshift0 : shiftSeq s r 0 = s r := rfl
    have hstep_r : blockSteps s (r + 1) + 1 = blockSteps s r + (s r + 1) := by
      change blockSteps s r + s r + 1 = blockSteps s r + (s r + 1)
      omega
    have hstep_rd :
        blockSteps s (r + d) + 1 =
          blockSteps s r + (blockSteps (shiftSeq s r) d + 1) := by
      rw [blockSteps_add s r d]
      omega
    have hnum_le :
        (2 : ℝ) ^ (s r + 1) ≤
          ((2 ^ (shiftSeq s r 0 + 1) * coprimeRemainder (shiftSeq s r) d : ℕ) : ℝ) := by
      rw [hshift0]
      have hnat :
          2 ^ (s r + 1) ≤ 2 ^ (s r + 1) * coprimeRemainder (shiftSeq s r) d :=
        Nat.le_mul_of_pos_right _ hR_pos
      exact_mod_cast hnat
    have h3d_pos : (0 : ℝ) < (3 : ℝ) ^ (blockSteps (shiftSeq s r) d + 1) :=
      pow_pos (by norm_num) _
    have h23_pos : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ (blockSteps s r) :=
      pow_nonneg (by norm_num) _
    have hdiv_le :
        (2 : ℝ) ^ (s r + 1) / (3 : ℝ) ^ (blockSteps (shiftSeq s r) d + 1) ≤
          ((2 ^ (shiftSeq s r 0 + 1) * coprimeRemainder (shiftSeq s r) d : ℕ) : ℝ) /
            (3 : ℝ) ^ (blockSteps (shiftSeq s r) d + 1) :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt h3d_pos)
    have hmul_le := mul_le_mul_of_nonneg_left hdiv_le h23_pos
    have hlhs :
        (2 / 3 : ℝ) ^ (blockSteps s r) *
            ((2 : ℝ) ^ (s r + 1) / (3 : ℝ) ^ (blockSteps (shiftSeq s r) d + 1)) =
          (2 : ℝ) ^ (blockSteps s (r + 1) + 1) /
            (3 : ℝ) ^ (blockSteps s (r + d) + 1) := by
      rw [div_pow, div_mul_div_comm, ← pow_add, ← pow_add, hstep_r, hstep_rd]
    rwa [hlhs] at hmul_le
  · have hlt_third :
        blockDrainSum (shiftSeq s r) d < (1 / 3 : ℝ) :=
      (integerSlack_pos_iff_blockDrainSum_lt_one_third (shiftSeq s r) d).mp hpos
    have h23_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (blockSteps s r) :=
      pow_pos (by norm_num) _
    nlinarith

/-! ## 4. Dead End 18: Exact Factorization of the Padé–Hankel Determinant -/

/-- **Padé–Hankel Quotient Determinant Factorization
(`pade_hankel_quotient_determinant_factorization`, Dead End 18)**:
Along any `ValidBlockChain a_0 s u K` (`r + d < K`), the `2 × 2` Padé–Hankel
determinant of the denominators `3^(T + 1)` and numerators `2^(T(k + 1) + 1) * u k`
between steps `r` and `r + d` factors identically as:
`3^(blockSteps s r + 1) * (2^(blockSteps s (r + d + 1) + 1) * u (r + d)) -
  3^(blockSteps s (r + d) + 1) * (2^(blockSteps s (r + 1) + 1) * u r) =
  3^(blockSteps s r + 1) * 2^(blockSteps s (r + 1) + 1) *
    coprimeRemainder (shiftSeq s r) d`. -/
theorem pade_hankel_quotient_determinant_factorization
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hrd : r + d < K) (hchain : ValidBlockChain a_0 s u K) :
    3 ^ (blockSteps s r + 1) *
          (2 ^ (blockSteps s (r + d + 1) + 1) * u (r + d)) -
        3 ^ (blockSteps s (r + d) + 1) *
          (2 ^ (blockSteps s (r + 1) + 1) * u r) =
      3 ^ (blockSteps s r + 1) * 2 ^ (blockSteps s (r + 1) + 1) *
        coprimeRemainder (shiftSeq s r) d := by
  have hid := shifted_coprime_quotient_m_step_identity hrd hchain
  have hpow2 :
      2 ^ (blockSteps s (r + d + 1) + 1) =
        2 ^ (blockSteps s (r + 1) + 1) * 2 ^ (tailSteps (shiftSeq s r) d) := by
    have htail := add_tailSteps_eq_blockSteps_succ (shiftSeq s r) d
    have hshift0 : shiftSeq s r 0 = s r := rfl
    rw [hshift0] at htail
    have hstep_r1 : blockSteps s (r + 1) = blockSteps s r + s r := rfl
    have hstep_rd1 :
        blockSteps s (r + d + 1) =
          blockSteps s r + blockSteps (shiftSeq s r) (d + 1) := by
      have hidx : r + d + 1 = r + (d + 1) := by omega
      rw [hidx, blockSteps_add]
    have hexp :
        blockSteps s (r + d + 1) + 1 =
          (blockSteps s (r + 1) + 1) + tailSteps (shiftSeq s r) d := by
      omega
    rw [hexp, Nat.pow_add]
  have hpow3 :
      3 ^ (blockSteps s (r + d) + 1) =
        3 ^ (blockSteps s r + 1) * 3 ^ (blockSteps (shiftSeq s r) d) := by
    have hexp :
        blockSteps s (r + d) + 1 =
          (blockSteps s r + 1) + blockSteps (shiftSeq s r) d := by
      rw [blockSteps_add s r d]
      omega
    rw [hexp, Nat.pow_add]
  have hterm1 :
      3 ^ (blockSteps s r + 1) *
          (2 ^ (blockSteps s (r + d + 1) + 1) * u (r + d)) =
        3 ^ (blockSteps s r + 1) * 2 ^ (blockSteps s (r + 1) + 1) *
          (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) := by
    rw [hpow2]
    ring
  have hterm2 :
      3 ^ (blockSteps s (r + d) + 1) *
          (2 ^ (blockSteps s (r + 1) + 1) * u r) =
        3 ^ (blockSteps s r + 1) * 2 ^ (blockSteps s (r + 1) + 1) *
          (3 ^ (blockSteps (shiftSeq s r) d) * u r) := by
    rw [hpow3]
    ring
  rw [hterm1, hterm2, ← Nat.mul_sub_left_distrib, hid, Nat.add_sub_cancel_left]

end Mahler.SeriesHankel
