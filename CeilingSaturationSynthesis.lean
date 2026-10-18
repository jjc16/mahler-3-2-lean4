import BaseTwoDivModLock

/-!
# Ceiling Saturation (`s ≥ 3`), Three-Step Compound Locks & Complete 48-Module Synthesis

This capstone module completes **Path 1**, **Path 2**, and **Path 3**:

1. **Path 1 — The Ceiling Saturation Theorem & Modulo-8 Equivalence
   (`minSlack_eq_two_pow_of_three_le`, `all_shifted_slacks_pos_of_three_le`,
   `ceiling_saturated_chain_iff_mod_eight`)**:
   - Whenever `3 ≤ c`, `3 * 2^c ≤ 3^c`, so
     `2^(T + c) ≤ 3^c * 2^T - 2^(T + c + 1)`.
   - Consequently, if `3 ≤ s k` for all `k < m`, the multi-origin minimum slack
     stays pinned at its ceiling:
     `minSlack s m = 2^(blockSteps s m)`, and
     `∀ j ≤ m, 0 < integerSlack (shiftSeq s j) (m - j)` holds automatically.
   - Along any valid block chain `ValidBlockChain a_0 s u K`, staying in the
     ceiling-saturated regime (`∀ k, k + 1 < K → 3 ≤ s (k + 1)`) is equivalent to
     the pure modulo-8 lock:
     `∀ k, k + 1 < K → (s k % 2 = 0 ∧ u k % 8 = 7) ∨ (s k % 2 = 1 ∧ u k % 8 = 5)`.
2. **Path 2 — Multi-Step Compound Coprime Locks on Ceiling-Saturated Chains
   (`two_step_ceiling_saturated_dvd`, `three_step_compound_coprime_identity`,
   `three_step_ceiling_saturated_dvd`)**:
   - Any two consecutive blocks in `{s ≥ 3}` force `64 = 2^6` to divide
     `3^(s k + s (k + 1)) * u k + (3^(s (k + 1)) + 2^(s (k + 1)))`.
   - Across any three consecutive blocks `k → k + 1 → k + 2 → k + 3`,
     `2^(s (k + 1) + s (k + 2) + s (k + 3)) * u (k + 3) =
       3^(s k + s (k + 1) + s (k + 2)) * u k +
         (3^(s (k + 1) + s (k + 2)) + 3^(s (k + 2)) * 2^(s (k + 1)) + 2^(s (k + 1) + s (k + 2)))`,
     so any three consecutive blocks in `{s ≥ 3}` force `512 = 2^9` to divide
     that 3-step linear form.
3. **Path 3 — Complete 48-Module Master Synthesis (`mahler_complete_48_module_synthesis`)**:
   Unites the flagship theorems across the entire 48-module formalization.
-/

namespace Mahler.CeilingSynthesis

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

/-! ## 1. Path 1: The Ceiling Saturation Theorem (`s k ≥ 3 ⟹ minSlack s m = 2^T(m)`) -/

/-- For every `c ≥ 3`, `3 * 2^c ≤ 3^c`. -/
theorem three_mul_two_pow_le_three_pow {c : ℕ} (hc : 3 ≤ c) :
    3 * 2 ^ c ≤ 3 ^ c := by
  have hsplit : c = 3 + (c - 3) := by omega
  have hle : 2 ^ (c - 3) ≤ 3 ^ (c - 3) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) (c - 3)
  calc
    3 * 2 ^ c = 24 * 2 ^ (c - 3) := by
      conv_lhs => rw [hsplit, Nat.pow_add]
      ring
    _ ≤ 27 * 2 ^ (c - 3) :=
      Nat.mul_le_mul_right (2 ^ (c - 3)) (by decide : 24 ≤ 27)
    _ ≤ 27 * 3 ^ (c - 3) := Nat.mul_le_mul_left 27 hle
    _ = 3 ^ c := by
      conv_rhs => rw [hsplit, Nat.pow_add]

/-- **The Ceiling Saturation Theorem (`minSlack_eq_two_pow_of_three_le`)**:
If `3 ≤ s k` for all `k < m`, then `minSlack s m = 2^(blockSteps s m)`. -/
theorem minSlack_eq_two_pow_of_three_le (s : ℕ → ℕ) (m : ℕ)
    (hs3 : ∀ k < m, 3 ≤ s k) :
    minSlack s m = (2 : ℤ) ^ (blockSteps s m) := by
  induction m with
  | zero => simp [minSlack, blockSteps]
  | succ m ih =>
      have ihm := ih (fun k hk => hs3 k (by omega))
      have hsm : 3 ≤ s m := hs3 m (by omega)
      have hpow_le : (3 : ℤ) * (2 : ℤ) ^ (s m) ≤ (3 : ℤ) ^ (s m) := by
        exact_mod_cast three_mul_two_pow_le_three_pow hsm
      have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ (blockSteps s m) :=
        pow_nonneg (by decide) _
      have hmul := mul_le_mul_of_nonneg_right hpow_le h2pos
      have hstep_ge :
          (2 : ℤ) ^ (blockSteps s (m + 1)) ≤
            (3 : ℤ) ^ (s m) * (2 : ℤ) ^ (blockSteps s m) -
              (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by
        have hp1 :
            (2 : ℤ) ^ (blockSteps s (m + 1)) =
              (2 : ℤ) ^ (s m) * (2 : ℤ) ^ (blockSteps s m) := by
          simp only [blockSteps, pow_add]
          ring
        have hp2 :
            (2 : ℤ) ^ (blockSteps s (m + 1) + 1) =
              2 * ((2 : ℤ) ^ (s m) * (2 : ℤ) ^ (blockSteps s m)) := by
          rw [pow_succ, hp1]
          ring
        linarith
      unfold minSlack
      rw [ihm]
      exact min_eq_left hstep_ge

/-- **Automatic Multi-Origin Slack Positivity on `{s ≥ 3}` (`all_shifted_slacks_pos_of_three_le`)**:
Whenever `3 ≤ s k` for all `k < m`, `0 < minSlack s m` and every shifted slack
`integerSlack (shiftSeq s j) (m - j)` (`0 ≤ j ≤ m`) is strictly positive. -/
theorem all_shifted_slacks_pos_of_three_le (s : ℕ → ℕ) (m : ℕ)
    (hs3 : ∀ k < m, 3 ≤ s k) :
    0 < minSlack s m ∧
      ∀ j ≤ m, 0 < integerSlack (shiftSeq s j) (m - j) := by
  have hpos : 0 < minSlack s m := by
    rw [minSlack_eq_two_pow_of_three_le s m hs3]
    exact pow_pos (by decide) _
  exact ⟨hpos, (minSlack_pos_iff_all_shifted_pos s m).mp hpos⟩

/-- **Ceiling-Saturated Modulo-8 Equivalence (`ceiling_saturated_chain_iff_mod_eight`)**:
Along any valid block chain `ValidBlockChain a_0 s u K`, having `3 ≤ s (k + 1)`
for all `k + 1 < K` is equivalent to the pure modulo-8 phase condition
`∀ k, k + 1 < K → (s k % 2 = 0 ∧ u k % 8 = 7) ∨ (s k % 2 = 1 ∧ u k % 8 = 5)`. -/
theorem ceiling_saturated_chain_iff_mod_eight {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hchain : ValidBlockChain a_0 s u K) :
    (∀ k, k + 1 < K → 3 ≤ s (k + 1)) ↔
      (∀ k, k + 1 < K →
        (s k % 2 = 0 ∧ u k % 8 = 7) ∨ (s k % 2 = 1 ∧ u k % 8 = 5)) := by
  constructor
  · intro hall k hk
    exact (three_le_next_block_iff_mod_eight hk hchain).mp (hall k hk)
  · intro hall k hk
    exact (three_le_next_block_iff_mod_eight hk hchain).mpr (hall k hk)

/-! ## 2. Path 2: Multi-Step Compound Coprime Locks on Ceiling-Saturated Chains -/

/-- **Two-Step `mod 64` Divisibility Lock on `{s ≥ 3}` (`two_step_ceiling_saturated_dvd`)**:
If `k + 2 < K`, `3 ≤ s (k + 1)`, and `3 ≤ s (k + 2)` along `ValidBlockChain a_0 s u K`,
then `64` divides `3^(s k + s (k + 1)) * u k + (3^(s (k + 1)) + 2^(s (k + 1)))`. -/
theorem two_step_ceiling_saturated_dvd {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs1 : 3 ≤ s (k + 1)) (hs2 : 3 ≤ s (k + 2)) :
    64 ∣ (3 ^ (s k + s (k + 1)) * u k + (3 ^ (s (k + 1)) + 2 ^ (s (k + 1)))) := by
  have hdvd :=
    two_step_compound_coprime_dvd (B := 6) hk hchain (by omega)
  simpa using hdvd

/-- **Three-Step Compound Coprime Identity (`three_step_compound_coprime_identity`)**:
Across any three consecutive transitions `k → k + 1 → k + 2 → k + 3` (`k + 3 < K`)
of `ValidBlockChain a_0 s u K`,
`2^(s (k + 1) + s (k + 2) + s (k + 3)) * u (k + 3) =
  3^(s k + s (k + 1) + s (k + 2)) * u k +
    (3^(s (k + 1) + s (k + 2)) + 3^(s (k + 2)) * 2^(s (k + 1)) + 2^(s (k + 1) + s (k + 2)))`. -/
theorem three_step_compound_coprime_identity {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk : k + 3 < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (s (k + 1) + s (k + 2) + s (k + 3)) * u (k + 3) =
      3 ^ (s k + s (k + 1) + s (k + 2)) * u k +
        (3 ^ (s (k + 1) + s (k + 2)) +
          3 ^ (s (k + 2)) * 2 ^ (s (k + 1)) +
          2 ^ (s (k + 1) + s (k + 2))) := by
  have h2 := two_step_compound_coprime_identity (by omega : k + 2 < K) hchain
  have h3 := coprime_quotient_recurrence (by omega : k + 2 + 1 < K) hchain
  calc
    2 ^ (s (k + 1) + s (k + 2) + s (k + 3)) * u (k + 3) =
        2 ^ (s (k + 1) + s (k + 2)) * (2 ^ (s (k + 3)) * u (k + 3)) := by
          rw [Nat.pow_add (2 : ℕ) (s (k + 1) + s (k + 2)) (s (k + 3))]
          ring
    _ = 2 ^ (s (k + 1) + s (k + 2)) * (3 ^ (s (k + 2)) * u (k + 2) + 1) := by
          rw [h3]
    _ = 3 ^ (s (k + 2)) * (2 ^ (s (k + 1) + s (k + 2)) * u (k + 2)) +
          2 ^ (s (k + 1) + s (k + 2)) := by ring
    _ = 3 ^ (s (k + 2)) *
          (3 ^ (s k + s (k + 1)) * u k + (3 ^ (s (k + 1)) + 2 ^ (s (k + 1)))) +
          2 ^ (s (k + 1) + s (k + 2)) := by rw [h2]
    _ = 3 ^ (s k + s (k + 1) + s (k + 2)) * u k +
          (3 ^ (s (k + 1) + s (k + 2)) +
            3 ^ (s (k + 2)) * 2 ^ (s (k + 1)) +
            2 ^ (s (k + 1) + s (k + 2))) := by
          rw [Nat.pow_add (3 : ℕ) (s k + s (k + 1)) (s (k + 2)),
            Nat.pow_add (3 : ℕ) (s (k + 1)) (s (k + 2))]
          ring

/-- **Three-Step `mod 512` Divisibility Lock on `{s ≥ 3}` (`three_step_ceiling_saturated_dvd`)**:
If `k + 3 < K`, `3 ≤ s (k + 1)`, `3 ≤ s (k + 2)`, and `3 ≤ s (k + 3)` along
`ValidBlockChain a_0 s u K`, then `512 = 2^9` divides the 3-step linear form. -/
theorem three_step_ceiling_saturated_dvd {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk : k + 3 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs1 : 3 ≤ s (k + 1)) (hs2 : 3 ≤ s (k + 2)) (hs3 : 3 ≤ s (k + 3)) :
    512 ∣
      (3 ^ (s k + s (k + 1) + s (k + 2)) * u k +
        (3 ^ (s (k + 1) + s (k + 2)) +
          3 ^ (s (k + 2)) * 2 ^ (s (k + 1)) +
          2 ^ (s (k + 1) + s (k + 2)))) := by
  rw [← three_step_compound_coprime_identity hk hchain]
  have hdvd : 2 ^ 9 ∣ 2 ^ (s (k + 1) + s (k + 2) + s (k + 3)) :=
    Nat.pow_dvd_pow 2 (by omega : 9 ≤ s (k + 1) + s (k + 2) + s (k + 3))
  simpa using dvd_mul_of_dvd_left hdvd (u (k + 3))

/-! ## 3. Path 3: Complete 48-Module Master Synthesis -/

/-- **Complete 48-Module Master Synthesis (`mahler_complete_48_module_synthesis`)**:
Bundles the core machine-checked equivalences, dual Base-3 / Base-2 div/mod locks,
1D `minSlack` dynamical system, global `3m - 1` step-rate bound, and ceiling-saturation
theorems into a single theorem statement. -/
theorem mahler_complete_48_module_synthesis :
    -- 1. Pure Integer Pinch Equivalence (eliminating ℝ):
    (∀ a_0 N : ℕ,
      (∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ N) ↔
        ∀ j ≤ N, IntegerPinch a_0 j (N - j)) ∧
    -- 2. Universal Conservation Law 2 * Q + Δ = 3^(T + 1):
    (∀ (s : ℕ → ℕ) (m : ℕ),
      2 * (kernelQuotient s m : ℤ) + integerSlack s m =
        (3 : ℤ) ^ (blockSteps s m + 1)) ∧
    -- 3. Universal Aperiodic Slack Cocycle Identity:
    (∀ (s : ℕ → ℕ) (r m : ℕ),
      integerSlack s (r + m) +
          (2 : ℤ) ^ (blockSteps s r + s r + 1) *
            (coprimeRemainder (shiftSeq s r) m : ℤ) =
        (3 : ℤ) ^ (blockSteps (shiftSeq s r) m) * integerSlack s r) ∧
    -- 4. 1D Multi-Origin `minSlack` Ceiling & Positivity Equivalence:
    (∀ (s : ℕ → ℕ) (m : ℕ),
      minSlack s m ≤ (2 : ℤ) ^ (blockSteps s m) ∧
      (0 < minSlack s m ↔
        ∀ j ≤ m, 0 < integerSlack (shiftSeq s j) (m - j))) ∧
    -- 5. Global `3m - 1` Step-Rate Bound on Surviving Orbits:
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ} {ξ : ℝ},
      m + 1 < K → ValidBlockChain a_0 s u K →
      ValidCompanionUpTo a_0 ξ (blockSteps s (m + 2)) →
      3 * m ≤ blockSteps s m + 1) ∧
    -- 6. Ceiling Saturation on `{s ≥ 3}`:
    (∀ (s : ℕ → ℕ) (m : ℕ),
      (∀ k < m, 3 ≤ s k) → minSlack s m = (2 : ℤ) ^ (blockSteps s m)) := by
  refine ⟨exists_validCompanionUpTo_iff_integerPinch, two_mul_kernelQuotient_add_slack,
    integerSlack_add_coprimeRemainder_eq, ?_, ?_, minSlack_eq_two_pow_of_three_le⟩
  · intro s m
    exact ⟨minSlack_le_two_pow s m, minSlack_pos_iff_all_shifted_pos s m⟩
  · intro a_0 s u K m ξ hmK hchain hsurv
    exact surviving_orbit_three_mul_step_rate hmK hchain hsurv

end Mahler.CeilingSynthesis
