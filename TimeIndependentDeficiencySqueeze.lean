import AperiodicBoundedBlockSqueeze

/-!
# Multi-Origin Minimum Slack Deficiency & Time-Independent Escape Bounds

This module defines the multi-origin minimum slack deficiency
`minSlackDeficiency s c k = 2^(c + blockSteps s k + 1) - (3^c - 2^c) * minSlack s k`
and proves **time-independent (`T(k)`-free and `a_0`-free) escape bounds** on
any aperiodic bounded-block run (`∀ i < m, s (k + i) ≤ c`):

1. **The Multi-Origin Minimum Slack Deficiency (`minSlackDeficiency`,
   `minSlackDeficiency_two_pos`, `minSlackDeficiency_step_ge_of_le`,
   `minSlackDeficiency_chain_ge_of_le`)**:
   - At `c = 2`, because `minSlack s k ≤ 2^(blockSteps s k)` always holds,
     `minSlackDeficiency s 2 k = 8 * 2^T(k) - 5 * minSlack s k ≥ 3 * 2^T(k) > 0`
     holds **universally at every step `k`**.
   - Whenever `s k ≤ c`,
     `3^(s k) * minSlackDeficiency s c k ≤ minSlackDeficiency s c (k + 1)`.
   - Across any `m`-block aperiodic run with `∀ i < m, s (k + i) ≤ c`,
     `3^(blockSteps (shiftSeq s k) m) * minSlackDeficiency s c k ≤
       minSlackDeficiency s c (k + m)`.
2. **Time-Independent (`T(k)`-Free) Bounded-Block Escape Squeeze
   (`time_independent_bounded_block_squeeze`)**:
   Suppose at step `k`, `(q : ℤ) * minSlack s k ≤ p * 2^(blockSteps s k)` (`1 ≤ q`),
   and for the next `m` blocks we have `∀ i < m, s (k + i) ≤ c` (`1 ≤ c`) with
   `0 < minSlack s (k + m)`.
   Canceling `2^(blockSteps s k)` from both sides yields the completely
   `T(k)`-independent and `a_0`-independent inequality:
   `(q * 2^(c + 1) - (3^c - 2^c) * p) * 3^(blockSteps (shiftSeq s k) m) <
     q * 2^(c + 1) * 2^(blockSteps (shiftSeq s k) m)`.
3. **Concrete Universal Time-Independent Step Ceilings
   (`universal_two_run_step_bound`,
   `six_step_ceiling_on_three_bounded_run`,
   `post_two_four_step_ceiling_on_five_bounded_run`)**:
   - For `c = 2` at **any** step `k` (`p = 1, q = 1`), any run with `s (k + i) ≤ 2`
     satisfies `3 * 3^S_m < 8 * 2^S_m`, hence `S_m ≤ 2` (at most one block of
     length `2`).
   - For `c = 3` whenever `19 * minSlack s k ≤ 15 * 2^T(k)` (`p = 15, q = 19`),
     any aperiodic run with `s (k + i) ≤ 3` satisfies `19 * 3^S_m < 304 * 2^S_m`,
     hence **`blockSteps (shiftSeq s k) m ≤ 6`** at *any* depth `T(k)`.
   - Right after `s k = 2` (`4 * minSlack s (k + 1) ≤ 2^T(k + 1)`), for `c = 5`
     (`p = 1, q = 4`), any run at `k + 1` with `s (k + 1 + i) ≤ 5` satisfies
     `45 * 3^S_m < 256 * 2^S_m`, hence **`blockSteps (shiftSeq s (k + 1)) m ≤ 4`**.
-/

namespace Mahler.TimeIndependentSqueeze

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

/-! ## 1. The Multi-Origin Minimum Slack Deficiency `minSlackDeficiency` -/

/-- The multi-origin minimum slack deficiency
`D^min_k(c) = 2^(c + blockSteps s k + 1) - (3^c - 2^c) * minSlack s k`. -/
def minSlackDeficiency (s : ℕ → ℕ) (c k : ℕ) : ℤ :=
  (2 : ℤ) ^ (c + blockSteps s k + 1) -
    ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * minSlack s k

/-- At `c = 2`, `minSlackDeficiency s 2 k ≥ 3 * 2^(blockSteps s k)` holds
universally at every step `k`. -/
theorem minSlackDeficiency_two_ge (s : ℕ → ℕ) (k : ℕ) :
    3 * (2 : ℤ) ^ (blockSteps s k) ≤ minSlackDeficiency s 2 k := by
  unfold minSlackDeficiency
  have hceil := minSlack_le_two_pow s k
  have hpow :
      (2 : ℤ) ^ (2 + blockSteps s k + 1) =
        8 * (2 : ℤ) ^ (blockSteps s k) := by
    rw [show 2 + blockSteps s k + 1 = blockSteps s k + 3 by omega, pow_add]
    ring
  rw [hpow]
  linarith

/-- Lower bound on the 1-step drift of `minSlackDeficiency`:
`minSlackDeficiency s c (k + 1) - 3^(s k) * minSlackDeficiency s c k ≥
  2^(blockSteps s k + 1) * (3^c * 2^(s k) - 2^c * 3^(s k))`. -/
theorem minSlackDeficiency_step_drift_ge (s : ℕ → ℕ) {c k : ℕ} (hc : 1 ≤ c) :
    (2 : ℤ) ^ (blockSteps s k + 1) *
        ((3 : ℤ) ^ c * (2 : ℤ) ^ (s k) - (2 : ℤ) ^ c * (3 : ℤ) ^ (s k)) ≤
      minSlackDeficiency s c (k + 1) -
        (3 : ℤ) ^ (s k) * minSlackDeficiency s c k := by
  unfold minSlackDeficiency
  have hstep := minSlack_succ_le_step s k
  have h2lt3 : (2 : ℤ) ^ c < (3 : ℤ) ^ c := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ c - (2 : ℤ) ^ c := by linarith
  have hmul := mul_le_mul_of_nonneg_left hstep hdiff_nonneg
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
  rw [hp1, hp3]
  rw [hp2] at hmul
  linarith

/-- Whenever `1 ≤ c` and `s k ≤ c`,
`3^(s k) * minSlackDeficiency s c k ≤ minSlackDeficiency s c (k + 1)`. -/
theorem minSlackDeficiency_step_ge_of_le (s : ℕ → ℕ) {c k : ℕ}
    (hc : 1 ≤ c) (hsk : s k ≤ c) :
    (3 : ℤ) ^ (s k) * minSlackDeficiency s c k ≤
      minSlackDeficiency s c (k + 1) := by
  have hdrift := minSlackDeficiency_step_drift_ge s (k := k) hc
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

/-- **Multi-Origin Bounded-Block Chain Inequality
(`minSlackDeficiency_chain_ge_of_le`)**:
Across any `m`-block aperiodic run with `∀ i < m, s (k + i) ≤ c` (`1 ≤ c`),
`3^(blockSteps (shiftSeq s k) m) * minSlackDeficiency s c k ≤
  minSlackDeficiency s c (k + m)`. -/
theorem minSlackDeficiency_chain_ge_of_le (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) ≤ c) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) * minSlackDeficiency s c k ≤
      minSlackDeficiency s c (k + m) := by
  induction m with
  | zero => simp [blockSteps]
  | succ m ih =>
      have ihm := ih (fun i hi => hrun i (by omega))
      have hm : s (k + m) ≤ c := hrun m (by omega)
      have hstep := minSlackDeficiency_step_ge_of_le s hc hm
      have h3pos : (0 : ℤ) ≤ (3 : ℤ) ^ (s (k + m)) := pow_nonneg (by decide) _
      have hmul := mul_le_mul_of_nonneg_left ihm h3pos
      have hexp :
          (3 : ℤ) ^ (s (k + m)) *
              ((3 : ℤ) ^ (blockSteps (shiftSeq s k) m) *
                minSlackDeficiency s c k) =
            (3 : ℤ) ^ (blockSteps (shiftSeq s k) (m + 1)) *
              minSlackDeficiency s c k := by
        simp only [blockSteps, shiftSeq, pow_add]
        ring
      rw [← Nat.add_assoc]
      linarith

/-- **Aperiodic Bounded-Block Squeeze for `minSlackDeficiency`
(`aperiodic_minSlackDeficiency_squeeze`)**:
If `1 ≤ c`, `∀ i < m, s (k + i) ≤ c`, and `0 < minSlack s (k + m)`, then
`3^(blockSteps (shiftSeq s k) m) * minSlackDeficiency s c k <
  2^(blockSteps (shiftSeq s k) m + c + blockSteps s k + 1)`. -/
theorem aperiodic_minSlackDeficiency_squeeze (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) ≤ c)
    (hpos : 0 < minSlack s (k + m)) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) * minSlackDeficiency s c k <
      (2 : ℤ) ^ (blockSteps (shiftSeq s k) m + c + blockSteps s k + 1) := by
  have hchain := minSlackDeficiency_chain_ge_of_le s hc hrun
  have hrhs :
      minSlackDeficiency s c (k + m) =
        (2 : ℤ) ^ (c + blockSteps s (k + m) + 1) -
          ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * minSlack s (k + m) := rfl
  have hsteps :
      c + blockSteps s (k + m) + 1 =
        blockSteps (shiftSeq s k) m + c + blockSteps s k + 1 := by
    rw [blockSteps_add]
    omega
  rw [hrhs, hsteps] at hchain
  have h2lt3 : (2 : ℤ) ^ c < (3 : ℤ) ^ c := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_pos : 0 < ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * minSlack s (k + m) :=
    mul_pos (by linarith) hpos
  linarith

/-! ## 2. Time-Independent (`T(k)`-Free) Bounded-Block Escape Squeeze -/

/-- **Time-Independent Bounded-Block Escape Squeeze
(`time_independent_bounded_block_squeeze`)**:
Suppose at step `k`, `(q : ℤ) * minSlack s k ≤ p * 2^(blockSteps s k)` (`0 < q`),
and for the next `m` blocks we have `∀ i < m, s (k + i) ≤ c` (`1 ≤ c`) with
`0 < minSlack s (k + m)`.
Canceling `2^(blockSteps s k)` from both sides yields the completely
`T(k)`-independent and `a_0`-independent inequality:
`(q * 2^(c + 1) - (3^c - 2^c) * p) * 3^(blockSteps (shiftSeq s k) m) <
  q * 2^(c + 1) * 2^(blockSteps (shiftSeq s k) m)`. -/
theorem time_independent_bounded_block_squeeze (s : ℕ → ℕ) {c k m : ℕ}
    {p q : ℤ} (hc : 1 ≤ c) (hq : 0 < q)
    (hratio : q * minSlack s k ≤ p * (2 : ℤ) ^ (blockSteps s k))
    (hrun : ∀ i < m, s (k + i) ≤ c)
    (hpos : 0 < minSlack s (k + m)) :
    (q * (2 : ℤ) ^ (c + 1) - ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * p) *
        (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) <
      q * (2 : ℤ) ^ (c + 1) * (2 : ℤ) ^ (blockSteps (shiftSeq s k) m) := by
  have hsq := aperiodic_minSlackDeficiency_squeeze s hc hrun hpos
  have h2lt3 : (2 : ℤ) ^ c < (3 : ℤ) ^ c := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ c - (2 : ℤ) ^ c := by linarith
  have hmul_ratio := mul_le_mul_of_nonneg_left hratio hdiff_nonneg
  have hdef_lower :
      (q * (2 : ℤ) ^ (c + 1) - ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * p) *
          (2 : ℤ) ^ (blockSteps s k) ≤
        q * minSlackDeficiency s c k := by
    unfold minSlackDeficiency
    have hpow :
        (2 : ℤ) ^ (c + blockSteps s k + 1) =
          (2 : ℤ) ^ (c + 1) * (2 : ℤ) ^ (blockSteps s k) := by
      rw [show c + blockSteps s k + 1 = (c + 1) + blockSteps s k by omega, pow_add]
    rw [hpow]
    linarith
  have h3pos : (0 : ℤ) ≤ (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) :=
    pow_nonneg (by decide) _
  have hmul_def := mul_le_mul_of_nonneg_right hdef_lower h3pos
  have hmul_sq := mul_lt_mul_of_pos_left hsq hq
  have hrhs_eq :
      q * (2 : ℤ) ^ (blockSteps (shiftSeq s k) m + c + blockSteps s k + 1) =
        (q * (2 : ℤ) ^ (c + 1) * (2 : ℤ) ^ (blockSteps (shiftSeq s k) m)) *
          (2 : ℤ) ^ (blockSteps s k) := by
    rw [show blockSteps (shiftSeq s k) m + c + blockSteps s k + 1 =
      (c + 1) + blockSteps (shiftSeq s k) m + blockSteps s k by omega,
      pow_add, pow_add]
    ring
  have hlhs_eq :
      (q * (2 : ℤ) ^ (c + 1) - ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * p) *
          (2 : ℤ) ^ (blockSteps s k) *
          (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) =
        ((q * (2 : ℤ) ^ (c + 1) - ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * p) *
          (3 : ℤ) ^ (blockSteps (shiftSeq s k) m)) *
          (2 : ℤ) ^ (blockSteps s k) := by ring
  have hcomb :
      ((q * (2 : ℤ) ^ (c + 1) - ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * p) *
          (3 : ℤ) ^ (blockSteps (shiftSeq s k) m)) *
          (2 : ℤ) ^ (blockSteps s k) <
        (q * (2 : ℤ) ^ (c + 1) * (2 : ℤ) ^ (blockSteps (shiftSeq s k) m)) *
          (2 : ℤ) ^ (blockSteps s k) := by
    linarith
  have h2k_pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s k) := pow_pos (by decide) _
  exact lt_of_mul_lt_mul_right hcomb (le_of_lt h2k_pos)

/-! ## 3. Concrete Universal Time-Independent Step Ceilings -/

/-- **Universal `S_m ≤ 2` Ceiling on `{s ≤ 2}` Runs (`universal_two_run_step_bound`)**:
At **any** step `k`, any run of `m` blocks with `∀ i < m, s (k + i) ≤ 2` and
`0 < minSlack s (k + m)` has total step length `blockSteps (shiftSeq s k) m ≤ 2`. -/
theorem universal_two_run_step_bound (s : ℕ → ℕ) {k m : ℕ}
    (hrun : ∀ i < m, s (k + i) ≤ 2)
    (hpos : 0 < minSlack s (k + m)) :
    blockSteps (shiftSeq s k) m ≤ 2 := by
  have hceil : (1 : ℤ) * minSlack s k ≤ 1 * (2 : ℤ) ^ (blockSteps s k) := by
    simpa using minSlack_le_two_pow s k
  have hsq :=
    time_independent_bounded_block_squeeze s (by decide : 1 ≤ 2)
      (by decide : (0 : ℤ) < 1) hceil hrun hpos
  norm_num at hsq
  have hineq_nat :
      3 * 3 ^ (blockSteps (shiftSeq s k) m) <
        8 * 2 ^ (blockSteps (shiftSeq s k) m) := by
    exact_mod_cast hsq
  by_contra hgt2
  have hsplit :
      blockSteps (shiftSeq s k) m =
        3 + (blockSteps (shiftSeq s k) m - 3) := by omega
  have hle :
      2 ^ (blockSteps (shiftSeq s k) m - 3) ≤
        3 ^ (blockSteps (shiftSeq s k) m - 3) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
  have hge :
      8 * 2 ^ (blockSteps (shiftSeq s k) m) ≤
        3 * 3 ^ (blockSteps (shiftSeq s k) m) := by
    calc
      8 * 2 ^ (blockSteps (shiftSeq s k) m) =
          64 * 2 ^ (blockSteps (shiftSeq s k) m - 3) := by
        conv_lhs => rw [hsplit, Nat.pow_add]
        ring
      _ ≤ 81 * 2 ^ (blockSteps (shiftSeq s k) m - 3) :=
        Nat.mul_le_mul_right _ (by decide : 64 ≤ 81)
      _ ≤ 81 * 3 ^ (blockSteps (shiftSeq s k) m - 3) :=
        Nat.mul_le_mul_left 81 hle
      _ = 3 * 3 ^ (blockSteps (shiftSeq s k) m) := by
        conv_rhs => rw [hsplit, Nat.pow_add]
        ring
  omega

/-- **Time-Independent `S_m ≤ 6` Ceiling on `{s ≤ 3}` Runs
(`six_step_ceiling_on_three_bounded_run`)**:
Whenever `19 * minSlack s k ≤ 15 * 2^(blockSteps s k)`, any aperiodic run of
`m` blocks with `∀ i < m, s (k + i) ≤ 3` and `0 < minSlack s (k + m)` has total
step length **`blockSteps (shiftSeq s k) m ≤ 6`** (independent of `k` and `T(k)`!). -/
theorem six_step_ceiling_on_three_bounded_run (s : ℕ → ℕ) {k m : ℕ}
    (hratio : 19 * minSlack s k ≤ 15 * (2 : ℤ) ^ (blockSteps s k))
    (hrun : ∀ i < m, s (k + i) ≤ 3)
    (hpos : 0 < minSlack s (k + m)) :
    blockSteps (shiftSeq s k) m ≤ 6 := by
  have hsq :=
    time_independent_bounded_block_squeeze s (by decide : 1 ≤ 3)
      (by decide : (0 : ℤ) < 19) hratio hrun hpos
  norm_num at hsq
  have hineq_nat :
      19 * 3 ^ (blockSteps (shiftSeq s k) m) <
        304 * 2 ^ (blockSteps (shiftSeq s k) m) := by
    exact_mod_cast hsq
  by_contra hgt6
  have hsplit :
      blockSteps (shiftSeq s k) m =
        7 + (blockSteps (shiftSeq s k) m - 7) := by omega
  have hle :
      2 ^ (blockSteps (shiftSeq s k) m - 7) ≤
        3 ^ (blockSteps (shiftSeq s k) m - 7) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
  have hge :
      304 * 2 ^ (blockSteps (shiftSeq s k) m) ≤
        19 * 3 ^ (blockSteps (shiftSeq s k) m) := by
    calc
      304 * 2 ^ (blockSteps (shiftSeq s k) m) =
          38912 * 2 ^ (blockSteps (shiftSeq s k) m - 7) := by
        conv_lhs => rw [hsplit, Nat.pow_add]
        ring
      _ ≤ 41553 * 2 ^ (blockSteps (shiftSeq s k) m - 7) :=
        Nat.mul_le_mul_right _ (by decide : 38912 ≤ 41553)
      _ ≤ 41553 * 3 ^ (blockSteps (shiftSeq s k) m - 7) :=
        Nat.mul_le_mul_left 41553 hle
      _ = 19 * 3 ^ (blockSteps (shiftSeq s k) m) := by
        conv_rhs => rw [hsplit, Nat.pow_add]
        ring
  omega

/-- **Post-`s k = 2` Time-Independent `S_m ≤ 4` Ceiling on `{s ≤ 5}` Runs
(`post_two_four_step_ceiling_on_five_bounded_run`)**:
Whenever `s k = 2`, any subsequent run of `m` blocks starting at `k + 1` with
`∀ i < m, s (k + 1 + i) ≤ 5` and `0 < minSlack s (k + 1 + m)` has total step
length **`blockSteps (shiftSeq s (k + 1)) m ≤ 4`**. -/
theorem post_two_four_step_ceiling_on_five_bounded_run (s : ℕ → ℕ) {k m : ℕ}
    (hsk : s k = 2)
    (hrun : ∀ i < m, s (k + 1 + i) ≤ 5)
    (hpos : 0 < minSlack s (k + 1 + m)) :
    blockSteps (shiftSeq s (k + 1)) m ≤ 4 := by
  have hq : 4 * minSlack s (k + 1) ≤ 1 * (2 : ℤ) ^ (blockSteps s (k + 1)) := by
    simpa using post_two_minSlack_le_quarter s hsk
  have hsq :=
    time_independent_bounded_block_squeeze s (k := k + 1) (by decide : 1 ≤ 5)
      (by decide : (0 : ℤ) < 4) hq hrun hpos
  norm_num at hsq
  have hineq_nat :
      45 * 3 ^ (blockSteps (shiftSeq s (k + 1)) m) <
        256 * 2 ^ (blockSteps (shiftSeq s (k + 1)) m) := by
    exact_mod_cast hsq
  by_contra hgt4
  have hsplit :
      blockSteps (shiftSeq s (k + 1)) m =
        5 + (blockSteps (shiftSeq s (k + 1)) m - 5) := by omega
  have hle :
      2 ^ (blockSteps (shiftSeq s (k + 1)) m - 5) ≤
        3 ^ (blockSteps (shiftSeq s (k + 1)) m - 5) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
  have hge :
      256 * 2 ^ (blockSteps (shiftSeq s (k + 1)) m) ≤
        45 * 3 ^ (blockSteps (shiftSeq s (k + 1)) m) := by
    calc
      256 * 2 ^ (blockSteps (shiftSeq s (k + 1)) m) =
          8192 * 2 ^ (blockSteps (shiftSeq s (k + 1)) m - 5) := by
        conv_lhs => rw [hsplit, Nat.pow_add]
        ring
      _ ≤ 10935 * 2 ^ (blockSteps (shiftSeq s (k + 1)) m - 5) :=
        Nat.mul_le_mul_right _ (by decide : 8192 ≤ 10935)
      _ ≤ 10935 * 3 ^ (blockSteps (shiftSeq s (k + 1)) m - 5) :=
        Nat.mul_le_mul_left 10935 hle
      _ = 45 * 3 ^ (blockSteps (shiftSeq s (k + 1)) m) := by
        conv_rhs => rw [hsplit, Nat.pow_add]
        ring
  omega

end Mahler.TimeIndependentSqueeze
