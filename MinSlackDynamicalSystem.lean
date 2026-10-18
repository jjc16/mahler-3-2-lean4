import AperiodicSlackCocycle

/-!
# The 1D Multi-Origin Minimum-Slack Dynamical System & Recovery Barriers

This module collapses the quadratic family of shifted multi-origin slack
constraints `{0 < integerSlack (shiftSeq s j) (m - j)}_{0 ≤ j ≤ m}` into a
single 1-dimensional integer dynamical system `minSlack s m` with a hard
exponential ceiling `minSlack s m ≤ 2^(blockSteps s m)`:

1. **The 1D Multi-Origin Minimum-Slack Recurrence (`minSlack`, `minSlack_le_two_pow`)**:
   Define
   - `minSlack s 0 = 1`,
   - `minSlack s (m + 1) = min (2^(blockSteps s (m + 1))) (3^(s m) * minSlack s m - 2^(blockSteps s (m + 1) + 1))`.
   Unlike `integerSlack s m` (which can grow up to `3^(blockSteps s m)`),
   `minSlack s m` satisfies the universal ceiling `minSlack s m ≤ 2^(blockSteps s m)`
   for every `m`.
2. **Exact Multi-Origin Equivalence (`scaled_shifted_slack_succ`,
   `minSlack_le_scaled_shifted_slack`, `exists_origin_eq_minSlack`,
   `minSlack_pos_iff_all_shifted_pos`, `minSlack_pos_of_validCompanionUpTo`)**:
   - Every scaled shifted slack `2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)`
     (`j ≤ m`) evolves across step `m → m + 1` by the same strictly increasing map
     `X ↦ 3^(s m) * X - 2^(blockSteps s (m + 1) + 1)`.
   - Consequently, `minSlack s m` is the exact minimum of
     `2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)` over all `0 ≤ j ≤ m`,
     and `0 < minSlack s m ↔ ∀ j ≤ m, 0 < integerSlack (shiftSeq s j) (m - j)`.
3. **The Universal Recovery Barrier (`recovery_barrier_of_minSlack_le`,
   `three_le_of_nine_mul_minSlack_le`, `post_two_minSlack_le_quarter`)**:
   - Whenever `0 < minSlack s (m + 1)` and `3^B * minSlack s m ≤ 2^(blockSteps s m + B + 1)`,
     the next block must satisfy `B + 1 ≤ s m`.
   - In particular (`B = 2`), whenever `9 * minSlack s m ≤ 8 * 2^(blockSteps s m)`,
     `3 ≤ s m` (`s m = 2` is forbidden).
   - Every occurrence of `s m = 2` knocks `minSlack s (m + 1)` down to at most
     one quarter of the ceiling (`4 * minSlack s (m + 1) ≤ 2^(blockSteps s (m + 1))`),
     forcing a recovery phase before `s = 2` can ever occur again.
4. **Back-to-Back Huge-Block Cascade (`seven_le_after_subword_2_6_3_3_2_10`)**:
   After `(2, 6, 3, 3, 2)`, where `10 ≤ s (j + 5)` is forced, choosing the minimal
   allowed block `s (j + 5) = 10` leaves `integerSlack = 8976097` at step `T = 26`,
   which still satisfies `3^6 * 8976097 ≤ 2^(26 + 6 + 1)` and therefore forces a
   second consecutive large block **`7 ≤ s (j + 6)`**.
-/

namespace Mahler.MinSlackSystem

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

/-! ## 1. The 1D Multi-Origin Minimum-Slack Recurrence & Universal Ceiling -/

/-- The 1D multi-origin minimum slack `M_m = min_{0 ≤ j ≤ m} 2^T(j) * Δ^{(j)}_{m - j}`. -/
def minSlack (s : ℕ → ℕ) : ℕ → ℤ
  | 0 => 1
  | m + 1 =>
      min ((2 : ℤ) ^ (blockSteps s (m + 1)))
        ((3 : ℤ) ^ (s m) * minSlack s m - (2 : ℤ) ^ (blockSteps s (m + 1) + 1))

/-- **Universal Exponential Ceiling (`minSlack_le_two_pow`)**:
For every sequence `s` and index `m`, `minSlack s m ≤ 2^(blockSteps s m)`. -/
theorem minSlack_le_two_pow (s : ℕ → ℕ) (m : ℕ) :
    minSlack s m ≤ (2 : ℤ) ^ (blockSteps s m) := by
  cases m with
  | zero => simp [minSlack, blockSteps]
  | succ m => exact min_le_left _ _

theorem minSlack_succ_le_step (s : ℕ → ℕ) (m : ℕ) :
    minSlack s (m + 1) ≤
      (3 : ℤ) ^ (s m) * minSlack s m - (2 : ℤ) ^ (blockSteps s (m + 1) + 1) :=
  min_le_right _ _

/-! ## 2. Exact Multi-Origin Equivalence -/

/-- **One-Step Evolution of Scaled Shifted Slacks (`scaled_shifted_slack_succ`)**:
For every origin `j ≤ m`, the scaled shifted slack
`2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)` evolves across
`m → m + 1` by `X ↦ 3^(s m) * X - 2^(blockSteps s (m + 1) + 1)`. -/
theorem scaled_shifted_slack_succ (s : ℕ → ℕ) {j m : ℕ} (hjm : j ≤ m) :
    (2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m + 1 - j) =
      (3 : ℤ) ^ (s m) *
          ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) -
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by
  have hsub : m + 1 - j = (m - j) + 1 := by omega
  rw [hsub, integerSlack_succ]
  have hshift_m : shiftSeq s j (m - j) = s m := by
    simp only [shiftSeq]
    congr 1
    omega
  have hsteps :
      blockSteps s j + (blockSteps (shiftSeq s j) (m - j + 1) + 1) =
        blockSteps s (m + 1) + 1 := by
    have hadd := blockSteps_add s j (m - j + 1)
    have hidx : j + (m - j + 1) = m + 1 := by omega
    rw [hidx] at hadd
    omega
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s j) *
          (2 : ℤ) ^ (blockSteps (shiftSeq s j) (m - j + 1) + 1) =
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by
    rw [← pow_add, hsteps]
  rw [hshift_m]
  calc
    (2 : ℤ) ^ (blockSteps s j) *
        ((3 : ℤ) ^ (s m) * integerSlack (shiftSeq s j) (m - j) -
          (2 : ℤ) ^ (blockSteps (shiftSeq s j) (m - j + 1) + 1)) =
      (3 : ℤ) ^ (s m) *
          ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) -
        (2 : ℤ) ^ (blockSteps s j) *
          (2 : ℤ) ^ (blockSteps (shiftSeq s j) (m - j + 1) + 1) := by ring
    _ = (3 : ℤ) ^ (s m) *
          ((2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j)) -
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by rw [hpow2]

/-- **Lower Bound Below Every Shifted Origin (`minSlack_le_scaled_shifted_slack`)**:
For every `j ≤ m`,
`minSlack s m ≤ 2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)`. -/
theorem minSlack_le_scaled_shifted_slack (s : ℕ → ℕ) {j m : ℕ} (hjm : j ≤ m) :
    minSlack s m ≤
      (2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j) := by
  induction m with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      simp [minSlack, integerSlack, blockSteps, coprimeRemainder]
  | succ m ih =>
      rcases Nat.of_le_succ hjm with hle | rfl
      · have ihm := ih hle
        have hstep := scaled_shifted_slack_succ s hle
        have h3nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ (s m) := pow_nonneg (by decide) _
        have hmul := mul_le_mul_of_nonneg_left ihm h3nonneg
        have hmin := minSlack_succ_le_step s m
        linarith
      · simp only [Nat.sub_self, integerSlack, blockSteps, coprimeRemainder,
          pow_zero, Nat.cast_zero, mul_zero, sub_zero, mul_one]
        exact min_le_left _ _

/-- **Attainment by Some Shifted Origin (`exists_origin_eq_minSlack`)**:
For every `m`, there exists an origin `j ≤ m` such that
`minSlack s m = 2^(blockSteps s j) * integerSlack (shiftSeq s j) (m - j)`. -/
theorem exists_origin_eq_minSlack (s : ℕ → ℕ) (m : ℕ) :
    ∃ j ≤ m,
      minSlack s m =
        (2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j) := by
  induction m with
  | zero =>
      exact ⟨0, le_rfl, by simp [minSlack, integerSlack, blockSteps, coprimeRemainder]⟩
  | succ m ih =>
      rcases ih with ⟨j, hjm, hj_eq⟩
      unfold minSlack
      rcases min_choice
        ((2 : ℤ) ^ (blockSteps s (m + 1)))
        ((3 : ℤ) ^ (s m) * minSlack s m - (2 : ℤ) ^ (blockSteps s (m + 1) + 1)) with hleft | hright
      · refine ⟨m + 1, le_rfl, ?_⟩
        rw [hleft]
        simp [integerSlack, blockSteps, coprimeRemainder]
      · refine ⟨j, by omega, ?_⟩
        rw [hright, hj_eq, ← scaled_shifted_slack_succ s hjm]

/-- **Exact Multi-Origin Positivity Equivalence (`minSlack_pos_iff_all_shifted_pos`)**:
`0 < minSlack s m` holds if and only if `0 < integerSlack (shiftSeq s j) (m - j)`
for all `0 ≤ j ≤ m`. -/
theorem minSlack_pos_iff_all_shifted_pos (s : ℕ → ℕ) (m : ℕ) :
    0 < minSlack s m ↔
      ∀ j ≤ m, 0 < integerSlack (shiftSeq s j) (m - j) := by
  constructor
  · intro hpos j hjm
    have hle := minSlack_le_scaled_shifted_slack s hjm
    have hprod_pos :
        0 < (2 : ℤ) ^ (blockSteps s j) * integerSlack (shiftSeq s j) (m - j) :=
      lt_of_lt_of_le hpos hle
    have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s j) := pow_pos (by decide) _
    exact pos_of_mul_pos_right hprod_pos (le_of_lt h2pos)
  · intro hall
    rcases exists_origin_eq_minSlack s m with ⟨j, hjm, hj_eq⟩
    rw [hj_eq]
    exact mul_pos (pow_pos (by decide) _) (hall j hjm)

/-- Along any surviving orbit (`m < K`), `0 < minSlack s m`. -/
theorem minSlack_pos_of_validCompanionUpTo {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (m + 1))) :
    0 < minSlack s m := by
  rw [minSlack_pos_iff_all_shifted_pos]
  intro j hjm
  rcases Nat.eq_or_lt_of_le hjm with rfl | hjlt
  · simp [integerSlack, blockSteps, coprimeRemainder]
  · have hjmK : j + (m - j) < K := by omega
    have hsurv' : ValidCompanionUpTo a_0 ξ (blockSteps s (j + (m - j) + 1)) := by
      have hidx : j + (m - j) + 1 = m + 1 := by omega
      rw [hidx]
      exact hsurv
    exact shift_invariant_integerSlack_pos hjmK hchain hsurv'

/-! ## 3. The Universal Recovery Barrier & Post-`s m = 2` Quarter Cap -/

/-- **Universal Recovery Barrier (`recovery_barrier_of_minSlack_le`)**:
If `0 < minSlack s (m + 1)` and `3^B * minSlack s m ≤ 2^(blockSteps s m + B + 1)`,
then the block length `s m` must satisfy `B + 1 ≤ s m`. -/
theorem recovery_barrier_of_minSlack_le (s : ℕ → ℕ) {m B : ℕ}
    (hpos_next : 0 < minSlack s (m + 1))
    (hbarrier : (3 : ℤ) ^ B * minSlack s m ≤ (2 : ℤ) ^ (blockSteps s m + B + 1)) :
    B + 1 ≤ s m := by
  by_contra hlt
  have hsm_le : s m ≤ B := by omega
  have hstep := minSlack_succ_le_step s m
  have hpos_m : 0 < minSlack s m := by
    have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1) + 1) :=
      pow_pos (by decide) _
    have h3pos : (0 : ℤ) < (3 : ℤ) ^ (s m) := pow_pos (by decide) _
    have hprod_pos : (0 : ℤ) < (3 : ℤ) ^ (s m) * minSlack s m := by linarith
    exact pos_of_mul_pos_right hprod_pos (le_of_lt h3pos)
  have hpow2_split :
      (2 : ℤ) ^ (blockSteps s m + B + 1) =
        (2 : ℤ) ^ (B - s m) * (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by
    simp only [blockSteps]
    rw [← pow_add]
    congr 1
    omega
  have hpow3_split :
      (3 : ℤ) ^ B * minSlack s m =
        (3 : ℤ) ^ (B - s m) * ((3 : ℤ) ^ (s m) * minSlack s m) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  have h2le3 : (2 : ℤ) ^ (B - s m) ≤ (3 : ℤ) ^ (B - s m) := by
    exact_mod_cast Nat.pow_le_pow_left (by decide : 2 ≤ 3) (B - s m)
  have h2pos_step : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1) + 1) :=
    pow_pos (by decide) _
  have h3pos_diff : (0 : ℤ) < (3 : ℤ) ^ (B - s m) := pow_pos (by decide) _
  have hmul1 :
      (2 : ℤ) ^ (B - s m) * (2 : ℤ) ^ (blockSteps s (m + 1) + 1) ≤
        (3 : ℤ) ^ (B - s m) * (2 : ℤ) ^ (blockSteps s (m + 1) + 1) :=
    mul_le_mul_of_nonneg_right h2le3 (le_of_lt h2pos_step)
  have hstrict :
      (2 : ℤ) ^ (blockSteps s (m + 1) + 1) < (3 : ℤ) ^ (s m) * minSlack s m := by
    linarith
  have hmul2 :
      (3 : ℤ) ^ (B - s m) * (2 : ℤ) ^ (blockSteps s (m + 1) + 1) <
        (3 : ℤ) ^ (B - s m) * ((3 : ℤ) ^ (s m) * minSlack s m) :=
    mul_lt_mul_of_pos_left hstrict h3pos_diff
  linarith

/-- **No-Return-to-`2` Barrier (`three_le_of_nine_mul_minSlack_le`)**:
Whenever `0 < minSlack s (m + 1)` and `9 * minSlack s m ≤ 8 * 2^(blockSteps s m)`,
we have `3 ≤ s m` (so `s m = 2` is impossible). -/
theorem three_le_of_nine_mul_minSlack_le (s : ℕ → ℕ) {m : ℕ}
    (hpos_next : 0 < minSlack s (m + 1))
    (hbarrier : 9 * minSlack s m ≤ 8 * (2 : ℤ) ^ (blockSteps s m)) :
    3 ≤ s m := by
  have hb :
      (3 : ℤ) ^ 2 * minSlack s m ≤ (2 : ℤ) ^ (blockSteps s m + 2 + 1) := by
    have hpow :
        (2 : ℤ) ^ (blockSteps s m + 2 + 1) =
          8 * (2 : ℤ) ^ (blockSteps s m) := by
      rw [show blockSteps s m + 2 + 1 = blockSteps s m + 3 by omega, pow_add]
      ring
    linarith
  exact recovery_barrier_of_minSlack_le s hpos_next hb

/-- **Post-`s m = 2` Quarter Cap (`post_two_minSlack_le_quarter`)**:
Whenever `s m = 2`, `4 * minSlack s (m + 1) ≤ 2^(blockSteps s (m + 1))`. -/
theorem post_two_minSlack_le_quarter (s : ℕ → ℕ) {m : ℕ} (hsm : s m = 2) :
    4 * minSlack s (m + 1) ≤ (2 : ℤ) ^ (blockSteps s (m + 1)) := by
  have hstep := minSlack_succ_le_step s m
  have hceil := minSlack_le_two_pow s m
  have hpow_step :
      (2 : ℤ) ^ (blockSteps s (m + 1)) = 4 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm, pow_add]
    ring
  have hpow_next :
      (2 : ℤ) ^ (blockSteps s (m + 1) + 1) = 8 * (2 : ℤ) ^ (blockSteps s m) := by
    rw [pow_succ, hpow_step]
    ring
  rw [hsm, hpow_next] at hstep
  linarith

/-! ## 4. Back-to-Back Huge-Block Cascade After `(2, 6, 3, 3, 2, 10)` -/

/-- Exact evaluation of `integerSlack` at `m = 6` for `(2, 6, 3, 3, 2, 10)`. -/
theorem integerSlack_of_prefix_2_6_3_3_2_10 {t : ℕ → ℕ}
    (h0 : t 0 = 2) (h1 : t 1 = 6) (h2 : t 2 = 3)
    (h3 : t 3 = 3) (h4 : t 4 = 2) (h5 : t 5 = 10) :
    integerSlack t 6 = 8976097 := by
  have hd5 := (integerSlack_of_prefix_2_6_3_3_2 h0 h1 h2 h3 h4).2.2.2.2
  have hs6 := integerSlack_succ t 5
  have hb6 : blockSteps t 6 = 26 := by
    simp [blockSteps, h0, h1, h2, h3, h4, h5]
  rw [h5, hb6, hd5] at hs6
  norm_num at hs6
  exact hs6

/-- **Back-to-Back Huge-Block Cascade (`seven_le_after_subword_2_6_3_3_2_10`)**:
If `(s j, ..., s (j + 5)) = (2, 6, 3, 3, 2, 10)` occurs at any block index `j`
(`j + 7 < K`) along a surviving orbit, then even after the forced block
`s (j + 5) = 10`, the next block must satisfy **`7 ≤ s (j + 6)`**. -/
theorem seven_le_after_subword_2_6_3_3_2_10 {a_0 : ℕ} {s u : ℕ → ℕ} {K j : ℕ}
    (hj : j + 7 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs0 : s j = 2) (hs1 : s (j + 1) = 6) (hs2 : s (j + 2) = 3)
    (hs3 : s (j + 3) = 3) (hs4 : s (j + 4) = 2) (hs5 : s (j + 5) = 10)
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + 7 + 1))) :
    7 ≤ s (j + 6) := by
  have hchain_sub : ValidBlockChain a_0 s u (j + 8) :=
    fun k hk => hchain k (by omega)
  have hchain_shift := validBlockChain_shift hchain_sub
  have hsteps :
      blockSteps s (j + 7 + 1) =
        blockSteps s j + blockSteps (shiftSeq s j) (7 + 1) := by
    rw [show j + 7 + 1 = j + (7 + 1) by omega, blockSteps_add]
  rw [hsteps] at hsurv
  have hsurv_shift :=
    validCompanionUpTo_shift (blockSteps s j)
      (blockSteps (shiftSeq s j) (7 + 1)) hsurv
  have hpos7 : 0 < minSlack (shiftSeq s j) 7 :=
    minSlack_pos_of_validCompanionUpTo (by omega : 7 < 8) hchain_shift hsurv_shift
  have hle6 : minSlack (shiftSeq s j) 6 ≤ integerSlack (shiftSeq s j) 6 := by
    have h := minSlack_le_scaled_shifted_slack (shiftSeq s j) (Nat.zero_le 6)
    simpa [blockSteps, shiftSeq_add] using h
  have hd6 : integerSlack (shiftSeq s j) 6 = 8976097 :=
    integerSlack_of_prefix_2_6_3_3_2_10
      (by simp [shiftSeq, hs0])
      (by simp [shiftSeq, hs1])
      (by simp [shiftSeq, hs2])
      (by simp [shiftSeq, hs3])
      (by simp [shiftSeq, hs4])
      (by simp [shiftSeq, hs5])
  have hb6 : blockSteps (shiftSeq s j) 6 = 26 := by
    simp [blockSteps, shiftSeq, hs0, hs1, hs2, hs3, hs4, hs5]
  have hbarrier :
      (3 : ℤ) ^ 6 * minSlack (shiftSeq s j) 6 ≤
        (2 : ℤ) ^ (blockSteps (shiftSeq s j) 6 + 6 + 1) := by
    rw [hb6]
    rw [hd6] at hle6
    norm_num
    linarith
  exact recovery_barrier_of_minSlack_le (shiftSeq s j) hpos7 hbarrier

end Mahler.MinSlackSystem
