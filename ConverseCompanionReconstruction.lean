import TelescopingSeriesDuality

/-!
# Converse Companion Reconstruction & The Terminal `minSlack` Equivalence Theorem

This module proves the **Converse Reconstruction Theorem**: along any valid
block chain `ValidBlockChain a_0 s u K` (`1 ≤ K`), positivity of the single
terminal integer `minSlack s (K - 1)` is **both necessary and sufficient** for
the existence of a real Mahler companion `ξ ∈ ℝ` surviving all `blockSteps s K`
steps:

1. **Monotone Decrease of `upperBound` Across Interior Even Steps
   (`upperBound_le_of_even`, `upperBound_even_chain_le`,
   `upperBound_block_end_le_interior`)**:
   - Whenever `orbit a_0 n % 2 = 0`, `upperBound a_0 (n + 1) ≤ upperBound a_0 n`.
   - Across any interior step `blockSteps s j + k` (`1 ≤ k ≤ s j`) of block `j`,
     all remaining steps up to `blockSteps s (j + 1)` are even, so
     `upperBound a_0 (blockSteps s (j + 1)) ≤ upperBound a_0 (blockSteps s j + k)`.
2. **Block-Boundary Pinch from Shifted Slack Positivity
   (`block_boundary_pinch_of_integerSlack_pos`)**:
   Whenever `0 < integerSlack (shiftSeq s j) (K - 1 - j)` (`j < K`), multiplying
   `2^(S_{r+1} + 1) * u (K - 1) < 3^(S_r + 1) * (2 * b_j + 1)` by `3^(s (K - 1) - 1)`
   establishes `lowerBound a_0 (blockSteps s K) < upperBound a_0 (blockSteps s j)`.
3. **The Terminal `minSlack` Equivalence Theorem
   (`exists_validCompanionUpTo_iff_minSlack_pos`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ K`),
   `(∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s K)) ↔ 0 < minSlack s (K - 1)`.
4. **Ceiling-Saturated Companion Sufficiency Theorem
   (`exists_validCompanionUpTo_of_three_le`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ K`), if `3 ≤ s k` for all
   `k < K - 1`, then `minSlack s (K - 1) = 2^(blockSteps s (K - 1)) > 0`, so a
   valid real companion `ξ ∈ ℝ` surviving through `blockSteps s K` is
   **guaranteed to exist**.
-/

namespace Mahler.ConverseReconstruction

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

/-! ## 1. Monotone Decrease of `upperBound` Across Interior Even Steps -/

/-- At any even step (`orbit a_0 n % 2 = 0`), `upperBound` decreases:
`upperBound a_0 (n + 1) ≤ upperBound a_0 n`. -/
theorem upperBound_le_of_even (a_0 n : ℕ) (heven : orbit a_0 n % 2 = 0) :
    upperBound a_0 (n + 1) ≤ upperBound a_0 n := by
  have hdiff := upperBound_step_diff a_0 n
  rw [heven] at hdiff
  have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
  linarith

/-- Across `d` consecutive even steps starting at `n`,
`upperBound a_0 (n + d) ≤ upperBound a_0 n`. -/
theorem upperBound_even_chain_le (a_0 n d : ℕ)
    (heven : ∀ i < d, orbit a_0 (n + i) % 2 = 0) :
    upperBound a_0 (n + d) ≤ upperBound a_0 n := by
  induction d with
  | zero => simp
  | succ d ih =>
      have ihd := ih (fun i hi => heven i (by omega))
      have hd := upperBound_le_of_even a_0 (n + d) (heven d (by omega))
      rw [← Nat.add_assoc]
      exact le_trans hd ihd

/-- At any interior or right-endpoint offset `1 ≤ k ≤ s j` inside block `j`,
`upperBound a_0 (blockSteps s (j + 1)) ≤ upperBound a_0 (blockSteps s j + k)`. -/
theorem upperBound_block_end_le_interior {a_0 : ℕ} {s u : ℕ → ℕ} {K j k : ℕ}
    (hjK : j < K) (hchain : ValidBlockChain a_0 s u K)
    (hk1 : 1 ≤ k) (hks : k ≤ s j) :
    upperBound a_0 (blockSteps s (j + 1)) ≤
      upperBound a_0 (blockSteps s j + k) := by
  rcases hchain j hjK with ⟨hsj, _, hdecomp_j⟩
  have hsteps :
      blockSteps s (j + 1) = (blockSteps s j + k) + (s j - k) := by
    simp only [blockSteps]
    omega
  rw [hsteps]
  apply upperBound_even_chain_le
  intro i hi
  have hassoc :
      (blockSteps s j + k) + i = blockSteps s j + (k + i) := by omega
  rw [hassoc, orbit_add]
  exact orbit_odd_block_even_interior (by omega : 1 ≤ k + i)
    (by omega : k + i < s j) hdecomp_j

/-! ## 2. Block-Boundary Pinch from Shifted Slack Positivity -/

/-- Whenever `0 < integerSlack (shiftSeq s j) (K - 1 - j)` (`j < K`), the
block-boundary pinch `lowerBound a_0 (blockSteps s K) < upperBound a_0 (blockSteps s j)`
holds. -/
theorem block_boundary_pinch_of_integerSlack_pos {a_0 : ℕ} {s u : ℕ → ℕ} {K j : ℕ}
    (hjK : j < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack (shiftSeq s j) (K - 1 - j)) :
    lowerBound a_0 (blockSteps s K) < upperBound a_0 (blockSteps s j) := by
  set r := K - 1 - j
  have hjr_succ : j + (r + 1) = K := by omega
  have hchain_sub : ValidBlockChain a_0 s u (j + (r + 1)) := by
    rw [hjr_succ]
    exact hchain
  have hchain_shift := validBlockChain_shift hchain_sub
  have hslack := integerSlack_eq_orbit_slack (Nat.lt_succ_self r) hchain_shift
  have hlt_int :
      (2 : ℤ) ^ (blockSteps (shiftSeq s j) (r + 1) + 1) *
          ((shiftSeq u j r : ℕ) : ℤ) <
        (3 : ℤ) ^ (blockSteps (shiftSeq s j) r + 1) *
          (2 * (orbit a_0 (blockSteps s j) : ℤ) + 1) := by
    linarith
  have hlt_nat :
      2 ^ (blockSteps (shiftSeq s j) (r + 1) + 1) * shiftSeq u j r <
        3 ^ (blockSteps (shiftSeq s j) r + 1) *
          (2 * orbit a_0 (blockSteps s j) + 1) := by
    exact_mod_cast hlt_int
  have hK1 : j + r < K := by omega
  rcases hchain (j + r) hK1 with ⟨hs_last, _, hdecomp_last⟩
  have hret :
      orbit a_0 (blockSteps s K) =
        3 ^ (s (j + r) - 1) * shiftSeq u j r := by
    have hK_eq : K = (j + r) + 1 := by omega
    rw [hK_eq]
    simp only [blockSteps]
    rw [orbit_add, orbit_odd_block_return hs_last hdecomp_last]
    rfl
  have h3pos : 0 < 3 ^ (s (j + r) - 1) := Nat.pow_pos (by decide)
  have hmul := Nat.mul_lt_mul_of_pos_left hlt_nat h3pos
  have hlhs :
      3 ^ (s (j + r) - 1) *
          (2 ^ (blockSteps (shiftSeq s j) (r + 1) + 1) * shiftSeq u j r) =
        2 ^ (blockSteps (shiftSeq s j) (r + 1) + 1) *
          orbit a_0 (blockSteps s K) := by
    rw [hret]
    ring
  have hrhs :
      3 ^ (s (j + r) - 1) *
          (3 ^ (blockSteps (shiftSeq s j) r + 1) *
            (2 * orbit a_0 (blockSteps s j) + 1)) =
        3 ^ (blockSteps (shiftSeq s j) (r + 1)) *
          (2 * orbit a_0 (blockSteps s j) + 1) := by
    have hexp :
        (s (j + r) - 1) + (blockSteps (shiftSeq s j) r + 1) =
          blockSteps (shiftSeq s j) (r + 1) := by
      simp only [blockSteps, shiftSeq]
      omega
    rw [← mul_assoc, ← Nat.pow_add, hexp]
  rw [hlhs, hrhs] at hmul
  have hsteps_K :
      blockSteps s j + blockSteps (shiftSeq s j) (r + 1) = blockSteps s K := by
    rw [← blockSteps_add, hjr_succ]
  have hpinch :
      IntegerPinch a_0 (blockSteps s j) (blockSteps (shiftSeq s j) (r + 1)) := by
    unfold IntegerPinch
    rw [hsteps_K]
    exact hmul
  have hbounds :=
    (lowerBound_lt_upperBound_iff_integerPinch
      a_0 (blockSteps s j) (blockSteps (shiftSeq s j) (r + 1))).mpr hpinch
  rwa [hsteps_K] at hbounds

/-! ## 3. Locating Any Step `n ≤ blockSteps s K` Inside a Block -/

/-- Any step `n ≤ blockSteps s K` is either the terminal boundary `blockSteps s K`
or has the form `blockSteps s j + k` for some `j < K` and `k < s j`. -/
theorem locate_step_in_block (s : ℕ → ℕ) (K n : ℕ) (hn : n ≤ blockSteps s K) :
    n = blockSteps s K ∨
      ∃ j < K, ∃ k < s j, n = blockSteps s j + k := by
  induction K with
  | zero =>
      left
      simp [blockSteps] at hn ⊢
      omega
  | succ K ih =>
      by_cases hle : n ≤ blockSteps s K
      · rcases ih hle with rfl | ⟨j, hjK, k, hks, rfl⟩
        · by_cases hsK0 : s K = 0
          · left
            simp [blockSteps, hsK0]
          · right
            exact ⟨K, Nat.lt_succ_self K, 0, by omega, by simp⟩
        · right
          exact ⟨j, by omega, k, hks, rfl⟩
      · rcases Nat.eq_or_lt_of_le hn with rfl | hlt
        · left
          rfl
        · right
          refine ⟨K, Nat.lt_succ_self K, n - blockSteps s K, ?_, by omega⟩
          simp only [blockSteps] at hlt
          omega

/-! ## 4. The Terminal `minSlack` Equivalence & Ceiling-Saturated Sufficiency -/

/-- **Converse Companion Reconstruction (`validCompanionUpTo_of_minSlack_pos`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ K`), if `0 < minSlack s (K - 1)`,
then `lowerBound a_0 (blockSteps s K)` is a valid real Mahler companion
surviving through step `blockSteps s K`. -/
theorem validCompanionUpTo_of_minSlack_pos {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < minSlack s (K - 1)) :
    ValidCompanionUpTo a_0 (lowerBound a_0 (blockSteps s K)) (blockSteps s K) := by
  have hall := (minSlack_pos_iff_all_shifted_pos s (K - 1)).mp hpos
  intro n hn
  rw [validCompanionAt_iff_bounds]
  refine ⟨lowerBound_mono a_0 hn, ?_⟩
  have hterm_lt :
      ∀ j ≤ K, lowerBound a_0 (blockSteps s K) < upperBound a_0 (blockSteps s j) := by
    intro j hjK
    rcases Nat.eq_or_lt_of_le hjK with hj_eq | hjlt
    · subst hj_eq
      unfold lowerBound upperBound
      have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ (blockSteps s j) := by positivity
      linarith
    · exact block_boundary_pinch_of_integerSlack_pos hjlt hchain
        (hall j (by omega))
  rcases locate_step_in_block s K n hn with rfl | ⟨j, hjK, k, hks, rfl⟩
  · exact hterm_lt K le_rfl
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hterm_lt j (by omega)
    · have hle_end :=
        upperBound_block_end_le_interior hjK hchain hkpos (by omega)
      exact lt_of_lt_of_le (hterm_lt (j + 1) (by omega)) hle_end

/-- **The Terminal `minSlack` Equivalence Theorem (`exists_validCompanionUpTo_iff_minSlack_pos`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ K`), a real Mahler companion `ξ ∈ ℝ`
surviving through step `blockSteps s K` exists **if and only if**
`0 < minSlack s (K - 1)`. -/
theorem exists_validCompanionUpTo_iff_minSlack_pos {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hchain : ValidBlockChain a_0 s u K) :
    (∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s K)) ↔
      0 < minSlack s (K - 1) := by
  constructor
  · rintro ⟨ξ, hξ⟩
    have hK_idx : K - 1 + 1 = K := by omega
    have hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (K - 1 + 1)) := by
      rwa [hK_idx]
    exact minSlack_pos_of_validCompanionUpTo (by omega : K - 1 < K) hchain hsurv
  · intro hpos
    exact ⟨lowerBound a_0 (blockSteps s K),
      validCompanionUpTo_of_minSlack_pos hK hchain hpos⟩

/-- **Ceiling-Saturated Companion Sufficiency Theorem (`exists_validCompanionUpTo_of_three_le`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ K`), if `3 ≤ s k` for all `k < K - 1`,
then a real Mahler companion `ξ ∈ ℝ` surviving through step `blockSteps s K`
is guaranteed to exist. -/
theorem exists_validCompanionUpTo_of_three_le {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hchain : ValidBlockChain a_0 s u K)
    (hs3 : ∀ k < K - 1, 3 ≤ s k) :
    ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s K) := by
  rw [exists_validCompanionUpTo_iff_minSlack_pos hK hchain]
  exact (all_shifted_slacks_pos_of_three_le s (K - 1) hs3).1

end Mahler.ConverseReconstruction
