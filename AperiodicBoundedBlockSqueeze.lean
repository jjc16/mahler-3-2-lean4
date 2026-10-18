import ParametricRemainderCorridor

/-!
# The Exact `slackDeficiency` Step-Drift Law & Aperiodic Bounded-Block Squeeze 1

This module proves the exact 1-step drift identity for `slackDeficiency s c k`
under **arbitrary** block lengths `s k` and generalizes Squeeze 1 from constant
runs (`s (k + i) = c`) to **arbitrary aperiodic bounded runs (`s (k + i) ≤ c`)**:

1. **Dual Parametric Remainder Lower Bounds
   (`two_pow_mul_three_pow_le_three_pow_mul_two_pow`,
   `parametric_coprimeRemainder_lower_bound_tail`,
   `parametric_coprimeRemainder_lower_bound`)**:
   - Whenever `n ≤ c`, `2^c * 3^n ≤ 3^c * 2^n`.
   - Whenever `1 ≤ m` and `∀ k, 1 ≤ k → k < m → s k ≤ c`,
     `3^(c + tailSteps s (m - 1)) ≤ (3^c - 2^c) * coprimeRemainder s m + 2^c * 2^(tailSteps s (m - 1))`.
   - Whenever `1 ≤ m` and `∀ k < m, s k ≤ c`,
     `3^(blockSteps s m) ≤ (3^c - 2^c) * coprimeRemainder s m + 2^c * 2^(tailSteps s (m - 1))`.
2. **Exact Step-Drift Identity for `slackDeficiency` (`slackDeficiency_step_drift`,
   `slackDeficiency_step_ge_of_le`, `slackDeficiency_step_le_of_ge`)**:
   - For **every** sequence `s`, reference block size `c`, and index `k`:
     `slackDeficiency s c (k + 1) - 3^(s k) * slackDeficiency s c k =
       2^(blockSteps s k + 1) * (3^c * 2^(s k) - 2^c * 3^(s k))`.
   - Consequently:
     - if `s k ≤ c`, `3^(s k) * slackDeficiency s c k ≤ slackDeficiency s c (k + 1)`;
     - if `c ≤ s k`, `slackDeficiency s c (k + 1) ≤ 3^(s k) * slackDeficiency s c k`.
3. **Aperiodic Bounded-Block Squeeze 1 & Explicit Linear Cutoff
   (`slackDeficiency_chain_ge_of_le`,
   `aperiodic_bounded_deficiency_squeeze`,
   `aperiodic_bounded_deficiency_linear_cutoff`)**:
   - Across any `m`-block run with `∀ i < m, s (k + i) ≤ c`,
     `3^(blockSteps (shiftSeq s k) m) * slackDeficiency s c k ≤ slackDeficiency s c (k + m)`.
   - Whenever `1 ≤ c` and `0 < integerSlack s (k + m)`,
     `3^(blockSteps (shiftSeq s k) m) * slackDeficiency s c k <
       2^(blockSteps (shiftSeq s k) m + c + blockSteps s k + 1)`.
   - In the sub-critical regime (`1 ≤ slackDeficiency s c k`), any aperiodic
     bounded run (`∀ i < m, s (k + i) ≤ c`) must terminate before
     `2 * (c + blockSteps s k + 1)` total steps:
     `blockSteps (shiftSeq s k) m < 2 * (c + blockSteps s k + 1)`.
-/

namespace Mahler.AperiodicBoundedSqueeze

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

/-! ## 1. Dual Parametric Remainder Lower Bounds (`s k ≤ c`) -/

/-- Whenever `n ≤ c`, `2^c * 3^n ≤ 3^c * 2^n`. -/
theorem two_pow_mul_three_pow_le_three_pow_mul_two_pow {n c : ℕ}
    (hnc : n ≤ c) :
    2 ^ c * 3 ^ n ≤ 3 ^ c * 2 ^ n := by
  have h := three_pow_mul_two_pow_le_two_pow_mul_three_pow hnc
  linarith

/-- **Tail-Only Parametric Remainder Lower Bound
(`parametric_coprimeRemainder_lower_bound_tail`)**:
Whenever `1 ≤ m` and `∀ k, 1 ≤ k → k < m → s k ≤ c` (with no hypothesis on `s 0`!),
`3^(c + tailSteps s (m - 1)) ≤ (3^c - 2^c) * coprimeRemainder s m + 2^c * 2^(tailSteps s (m - 1))`. -/
theorem parametric_coprimeRemainder_lower_bound_tail {s : ℕ → ℕ} {c m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k, 1 ≤ k → k < m → s k ≤ c) :
    3 ^ (c + tailSteps s (m - 1)) ≤
      (3 ^ c - 2 ^ c) * coprimeRemainder s m +
        2 ^ c * 2 ^ (tailSteps s (m - 1)) := by
  have h2le3 : 2 ^ c ≤ 3 ^ c := Nat.pow_le_pow_left (by decide : 2 ≤ 3) c
  have hsum_c : (3 ^ c - 2 ^ c) + 2 ^ c = 3 ^ c := Nat.sub_add_cancel h2le3
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          simp only [coprimeRemainder, tailSteps, Nat.sub_self,
            Nat.add_zero, Nat.pow_zero, Nat.mul_one]
          omega
      | succ n =>
          have ihn := ih (by omega) (fun k hk1 hk2 => hs k hk1 (by omega))
          have hsn1 : s (n + 1) ≤ c := hs (n + 1) (by omega) (by omega)
          have hstep := two_pow_mul_three_pow_le_three_pow_mul_two_pow hsn1
          have htail :
              tailSteps s (n + 1) = tailSteps s n + s (n + 1) := rfl
          calc
            3 ^ (c + tailSteps s (n + 1)) =
                3 ^ (s (n + 1)) * 3 ^ (c + tailSteps s n) := by
              rw [htail, show c + (tailSteps s n + s (n + 1)) =
                s (n + 1) + (c + tailSteps s n) by omega, Nat.pow_add]
            _ ≤ 3 ^ (s (n + 1)) *
                  ((3 ^ c - 2 ^ c) * coprimeRemainder s (n + 1) +
                    2 ^ c * 2 ^ (tailSteps s n)) :=
              Nat.mul_le_mul_left (3 ^ (s (n + 1))) ihn
            _ = (3 ^ c - 2 ^ c) * 3 ^ (s (n + 1)) * coprimeRemainder s (n + 1) +
                  2 ^ (tailSteps s n) * (2 ^ c * 3 ^ (s (n + 1))) := by ring
            _ ≤ (3 ^ c - 2 ^ c) * 3 ^ (s (n + 1)) * coprimeRemainder s (n + 1) +
                  2 ^ (tailSteps s n) * (3 ^ c * 2 ^ (s (n + 1))) :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_left (2 ^ (tailSteps s n)) hstep) _
            _ = (3 ^ c - 2 ^ c) * 3 ^ (s (n + 1)) * coprimeRemainder s (n + 1) +
                  ((3 ^ c - 2 ^ c) + 2 ^ c) * 2 ^ (tailSteps s (n + 1)) := by
              rw [hsum_c, htail, Nat.pow_add]
              ring
            _ = (3 ^ c - 2 ^ c) * coprimeRemainder s (n + 2) +
                  2 ^ c * 2 ^ (tailSteps s (n + 1)) := by
              simp only [coprimeRemainder]
              ring

/-- **Full Parametric Remainder Lower Bound (`parametric_coprimeRemainder_lower_bound`)**:
Whenever `1 ≤ m` and `∀ k < m, s k ≤ c`,
`3^(blockSteps s m) ≤ (3^c - 2^c) * coprimeRemainder s m + 2^c * 2^(tailSteps s (m - 1))`. -/
theorem parametric_coprimeRemainder_lower_bound {s : ℕ → ℕ} {c m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, s k ≤ c) :
    3 ^ (blockSteps s m) ≤
      (3 ^ c - 2 ^ c) * coprimeRemainder s m +
        2 ^ c * 2 ^ (tailSteps s (m - 1)) := by
  have htail :=
    parametric_coprimeRemainder_lower_bound_tail hm (fun k _ hk => hs k hk)
  have hs0 : s 0 ≤ c := hs 0 hm
  have hsteps : blockSteps s m = s 0 + tailSteps s (m - 1) := by
    have h := add_tailSteps_eq_blockSteps_succ s (m - 1)
    have hidx : m - 1 + 1 = m := by omega
    rw [hidx] at h
    exact h.symm
  have hpow : 3 ^ (blockSteps s m) ≤ 3 ^ (c + tailSteps s (m - 1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
  exact le_trans hpow htail

/-! ## 2. The Exact 1-Step Drift Law for `slackDeficiency` -/

/-- **Exact 1-Step Drift Identity (`slackDeficiency_step_drift`)**:
For **every** sequence `s`, reference block size `c`, and index `k`:
`slackDeficiency s c (k + 1) - 3^(s k) * slackDeficiency s c k =
  2^(blockSteps s k + 1) * (3^c * 2^(s k) - 2^c * 3^(s k))`. -/
theorem slackDeficiency_step_drift (s : ℕ → ℕ) (c k : ℕ) :
    slackDeficiency s c (k + 1) -
        (3 : ℤ) ^ (s k) * slackDeficiency s c k =
      (2 : ℤ) ^ (blockSteps s k + 1) *
        ((3 : ℤ) ^ c * (2 : ℤ) ^ (s k) - (2 : ℤ) ^ c * (3 : ℤ) ^ (s k)) := by
  unfold slackDeficiency
  rw [integerSlack_succ]
  have hp1 :
      (2 : ℤ) ^ (c + blockSteps s (k + 1) + 1) =
        (2 : ℤ) ^ (blockSteps s k + 1) *
          ((2 : ℤ) ^ c * (2 : ℤ) ^ (s k)) := by
    simp only [blockSteps]
    rw [show c + (blockSteps s k + s k) + 1 =
      (blockSteps s k + 1) + (c + s k) by omega,
      pow_add (2 : ℤ) (blockSteps s k + 1) (c + s k),
      pow_add (2 : ℤ) c (s k)]
  have hp2 :
      (2 : ℤ) ^ (blockSteps s (k + 1) + 1) =
        (2 : ℤ) ^ (blockSteps s k + 1) * (2 : ℤ) ^ (s k) := by
    simp only [blockSteps]
    rw [show blockSteps s k + s k + 1 = (blockSteps s k + 1) + s k by omega, pow_add]
  have hp3 :
      (2 : ℤ) ^ (c + blockSteps s k + 1) =
        (2 : ℤ) ^ (blockSteps s k + 1) * (2 : ℤ) ^ c := by
    rw [show c + blockSteps s k + 1 = (blockSteps s k + 1) + c by omega, pow_add]
  rw [hp1, hp2, hp3]
  ring

/-- Whenever `s k ≤ c`, `3^(s k) * slackDeficiency s c k ≤ slackDeficiency s c (k + 1)`. -/
theorem slackDeficiency_step_ge_of_le (s : ℕ → ℕ) {c k : ℕ}
    (hsk : s k ≤ c) :
    (3 : ℤ) ^ (s k) * slackDeficiency s c k ≤
      slackDeficiency s c (k + 1) := by
  have hdrift := slackDeficiency_step_drift s c k
  have hpow :
      ((2 ^ c * 3 ^ (s k) : ℕ) : ℤ) ≤ ((3 ^ c * 2 ^ (s k) : ℕ) : ℤ) := by
    exact_mod_cast two_pow_mul_three_pow_le_three_pow_mul_two_pow hsk
  push_cast at hpow
  have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ (blockSteps s k + 1) :=
    pow_nonneg (by decide) _
  have hnonneg :
      (0 : ℤ) ≤ (2 : ℤ) ^ (blockSteps s k + 1) *
        ((3 : ℤ) ^ c * (2 : ℤ) ^ (s k) - (2 : ℤ) ^ c * (3 : ℤ) ^ (s k)) :=
    mul_nonneg h2pos (by linarith)
  linarith

/-- Whenever `c ≤ s k`, `slackDeficiency s c (k + 1) ≤ 3^(s k) * slackDeficiency s c k`. -/
theorem slackDeficiency_step_le_of_ge (s : ℕ → ℕ) {c k : ℕ}
    (hsk : c ≤ s k) :
    slackDeficiency s c (k + 1) ≤
      (3 : ℤ) ^ (s k) * slackDeficiency s c k := by
  have hdrift := slackDeficiency_step_drift s c k
  have hpow :
      ((3 ^ c * 2 ^ (s k) : ℕ) : ℤ) ≤ ((2 ^ c * 3 ^ (s k) : ℕ) : ℤ) := by
    exact_mod_cast three_pow_mul_two_pow_le_two_pow_mul_three_pow hsk
  push_cast at hpow
  have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ (blockSteps s k + 1) :=
    pow_nonneg (by decide) _
  have hnonpos :
      (2 : ℤ) ^ (blockSteps s k + 1) *
        ((3 : ℤ) ^ c * (2 : ℤ) ^ (s k) - (2 : ℤ) ^ c * (3 : ℤ) ^ (s k)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h2pos (by linarith)
  linarith

/-! ## 3. Aperiodic Bounded-Block Squeeze 1 & Explicit Linear Cutoff -/

/-- **Aperiodic Bounded-Block Chain Inequality (`slackDeficiency_chain_ge_of_le`)**:
Across any `m`-block run with `∀ i < m, s (k + i) ≤ c`,
`3^(blockSteps (shiftSeq s k) m) * slackDeficiency s c k ≤ slackDeficiency s c (k + m)`. -/
theorem slackDeficiency_chain_ge_of_le (s : ℕ → ℕ) {c k m : ℕ}
    (hrun : ∀ i < m, s (k + i) ≤ c) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) * slackDeficiency s c k ≤
      slackDeficiency s c (k + m) := by
  induction m with
  | zero => simp [blockSteps]
  | succ m ih =>
      have ihm := ih (fun i hi => hrun i (by omega))
      have hm : s (k + m) ≤ c := hrun m (by omega)
      have hstep := slackDeficiency_step_ge_of_le s hm
      have h3pos : (0 : ℤ) ≤ (3 : ℤ) ^ (s (k + m)) := pow_nonneg (by decide) _
      have hmul := mul_le_mul_of_nonneg_left ihm h3pos
      have hexp :
          (3 : ℤ) ^ (s (k + m)) *
              ((3 : ℤ) ^ (blockSteps (shiftSeq s k) m) * slackDeficiency s c k) =
            (3 : ℤ) ^ (blockSteps (shiftSeq s k) (m + 1)) * slackDeficiency s c k := by
        simp only [blockSteps, shiftSeq, pow_add]
        ring
      rw [← Nat.add_assoc]
      linarith

/-- **Aperiodic Bounded-Block Squeeze 1 (`aperiodic_bounded_deficiency_squeeze`)**:
If `1 ≤ c`, `∀ i < m, s (k + i) ≤ c` (varying arbitrarily in `{1, ..., c}`!),
and `0 < integerSlack s (k + m)`, then
`3^(blockSteps (shiftSeq s k) m) * slackDeficiency s c k <
  2^(blockSteps (shiftSeq s k) m + c + blockSteps s k + 1)`. -/
theorem aperiodic_bounded_deficiency_squeeze (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) ≤ c)
    (hpos : 0 < integerSlack s (k + m)) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) * slackDeficiency s c k <
      (2 : ℤ) ^ (blockSteps (shiftSeq s k) m + c + blockSteps s k + 1) := by
  have hchain := slackDeficiency_chain_ge_of_le s hrun
  have hrhs :
      slackDeficiency s c (k + m) =
        (2 : ℤ) ^ (c + blockSteps s (k + m) + 1) -
          ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * integerSlack s (k + m) := rfl
  have hsteps :
      c + blockSteps s (k + m) + 1 =
        blockSteps (shiftSeq s k) m + c + blockSteps s k + 1 := by
    rw [blockSteps_add]
    omega
  rw [hrhs, hsteps] at hchain
  have h2lt3 : (2 : ℤ) ^ c < (3 : ℤ) ^ c := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_pos : 0 < ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * integerSlack s (k + m) :=
    mul_pos (by linarith) hpos
  linarith

/-- **Aperiodic Bounded-Block Linear Step Cutoff
(`aperiodic_bounded_deficiency_linear_cutoff`)**:
In the sub-critical deficiency regime (`1 ≤ slackDeficiency s c k`), **any**
aperiodic run of `m` blocks satisfying `∀ i < m, s (k + i) ≤ c` with
`0 < integerSlack s (k + m)` must terminate strictly before
`2 * (c + blockSteps s k + 1)` total steps:
`blockSteps (shiftSeq s k) m < 2 * (c + blockSteps s k + 1)`. -/
theorem aperiodic_bounded_deficiency_linear_cutoff (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) ≤ c)
    (hpos : 0 < integerSlack s (k + m))
    (hdef : 1 ≤ slackDeficiency s c k) :
    blockSteps (shiftSeq s k) m < 2 * (c + blockSteps s k + 1) := by
  by_contra hge
  set S := blockSteps (shiftSeq s k) m
  set B := c + blockSteps s k + 1
  have h2B : 2 * B ≤ S := by omega
  have hsq := aperiodic_bounded_deficiency_squeeze s hc hrun hpos
  have h3pos : (0 : ℤ) < (3 : ℤ) ^ S := pow_pos (by decide) _
  have h1le : (3 : ℤ) ^ S ≤ (3 : ℤ) ^ S * slackDeficiency s c k := by
    have := mul_le_mul_of_nonneg_left hdef (le_of_lt h3pos)
    linarith
  have hlt_int : (3 : ℤ) ^ S < (2 : ℤ) ^ (S + B) := by
    have hlt' := lt_of_le_of_lt h1le hsq
    simpa [S, B, Nat.add_assoc] using hlt'
  have hlt_nat : 3 ^ S < 2 ^ (S + B) := by
    exact_mod_cast hlt_int
  have hpow_le : 2 ^ (S + B) ≤ 3 ^ S := by
    have hsplit2 : S + B = 3 * B + (S - 2 * B) := by omega
    have hsplit3 : S = 2 * B + (S - 2 * B) := by omega
    rw [hsplit2, Nat.pow_add]
    conv_rhs => rw [hsplit3, Nat.pow_add]
    exact Nat.mul_le_mul
      (two_pow_three_mul_le_three_pow_two_mul B)
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (S - 2 * B))
  omega

end Mahler.AperiodicBoundedSqueeze
