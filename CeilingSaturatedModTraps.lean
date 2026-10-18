import MonotonicStepSumSeparation

/-!
# Ceiling-Saturated Modulo-`2^(c+3)` Traps & The Modulo-16 Phase Classifier

This module formalizes **Attack Vector 1** (the Universal Modulo-`2^(c+3)` Trap
Cascading on Ceiling-Saturated Blocks) and the **Modulo-16 Phase Classifier**
from **Attack Vector 2** (the 2-adic period-4 structure of `3^s mod 16`):

1. **Universal Ceiling-Saturated Modulo-`2^(c+3)` Trap (`ceiling_saturated_mod_two_pow_add_three`,
   `s_eq_three_forces_mod_64_eq_40`, `s_eq_four_forces_mod_128_eq_112`)**:
   - Whenever `s (k + 1) = c` and `3 ≤ s (k + 2)` (`k + 2 < K`) along
     `ValidBlockChain a_0 s u K`,
     `(3^(s k) * u k + 1) % 2^(c + 3) = 2^c * (7 - 2 * (c % 2))`.
   - For `c = 3`: `(3^(s k) * u k + 1) % 64 = 40`.
   - For `c = 4`: `(3^(s k) * u k + 1) % 128 = 112`.
2. **The Two-Step `(3, 3)` Modulo-512 Trap (`two_step_three_three_forces_mod_512_eq_296`)**:
   Whenever `s (k + 1) = 3`, `s (k + 2) = 3`, and `3 ≤ s (k + 3)` (`k + 3 < K`),
   `(3^(s k) * u k + 1) % 512 = 296`, locking 9 binary bits at once.
3. **The Modulo-16 Period-4 Law & Exact Classification of `s(k + 1) = 3` vs. `4 ≤ s(k + 1)`
   (`three_pow_mod_16_classifier`, `s_eq_three_iff_mod_16`, `four_le_s_iff_mod_16`,
   `next_block_eq_three_iff_mod_16`, `four_le_next_block_iff_mod_16`)**:
   - `3^s % 16` has exact period `4`: `1, 3, 9, 11` for `s % 4 = 0, 1, 2, 3`.
   - Knowing `s k % 4` partitions the ceiling-saturated mod-8 class into:
     - a single residue mod `16` (`7, 13, 15, 5` for `s k % 4 = 0, 1, 2, 3`)
       where `s (k + 1) = 3` exactly, and
     - a single residue mod `16` (`15, 5, 7, 13` for `s k % 4 = 0, 1, 2, 3`)
       where `4 ≤ s (k + 1)`.
-/

namespace Mahler.CeilingModTraps

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

/-! ## 1. Attack Vector 1: Universal Modulo-`2^(c+3)` Trap on Ceiling-Saturated Blocks -/

/-- For any `c` and `u'`, `(2^c * u') % 2^(c + 3) = 2^c * (u' % 8)`. -/
theorem two_pow_mul_mod_two_pow_add_three (c u' : ℕ) :
    (2 ^ c * u') % 2 ^ (c + 3) = 2 ^ c * (u' % 8) := by
  rw [Nat.pow_add, Nat.mul_mod_mul_left]

/-- **Universal Ceiling-Saturated Modulo-`2^(c+3)` Lock
(`ceiling_saturated_mod_two_pow_add_three`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`), if `s (k + 1) = c` and
`3 ≤ s (k + 2)`, then
`(3^(s k) * u k + 1) % 2^(c + 3) = 2^c * (7 - 2 * (c % 2))`. -/
theorem ceiling_saturated_mod_two_pow_add_three {a_0 : ℕ} {s u : ℕ → ℕ} {K k c : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsc : s (k + 1) = c) (hs2 : 3 ≤ s (k + 2)) :
    (3 ^ (s k) * u k + 1) % 2 ^ (c + 3) =
      2 ^ c * (7 - 2 * (c % 2)) := by
  have hrec := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hmod8 :=
    (three_le_next_block_iff_mod_eight (by omega : (k + 1) + 1 < K) hchain).mp hs2
  rw [hsc] at hrec hmod8
  have hu_mod8 : u (k + 1) % 8 = 7 - 2 * (c % 2) := by
    rcases hmod8 with ⟨hc0, hu7⟩ | ⟨hc1, hu5⟩ <;> omega
  rw [← hrec, two_pow_mul_mod_two_pow_add_three, hu_mod8]

/-- **The `s(k + 1) = 3` Modulo-64 Lock (`s_eq_three_forces_mod_64_eq_40`)**:
Whenever `s (k + 1) = 3` and `3 ≤ s (k + 2)` (`k + 2 < K`),
`(3^(s k) * u k + 1) % 64 = 40`. -/
theorem s_eq_three_forces_mod_64_eq_40 {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs1 : s (k + 1) = 3) (hs2 : 3 ≤ s (k + 2)) :
    (3 ^ (s k) * u k + 1) % 64 = 40 := by
  have h := ceiling_saturated_mod_two_pow_add_three hk2 hchain hs1 hs2
  simpa using h

/-- **The `s(k + 1) = 4` Modulo-128 Lock (`s_eq_four_forces_mod_128_eq_112`)**:
Whenever `s (k + 1) = 4` and `3 ≤ s (k + 2)` (`k + 2 < K`),
`(3^(s k) * u k + 1) % 128 = 112`. -/
theorem s_eq_four_forces_mod_128_eq_112 {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs1 : s (k + 1) = 4) (hs2 : 3 ≤ s (k + 2)) :
    (3 ^ (s k) * u k + 1) % 128 = 112 := by
  have h := ceiling_saturated_mod_two_pow_add_three hk2 hchain hs1 hs2
  simpa using h

/-- **The Two-Step `(3, 3)` Modulo-512 Lock (`two_step_three_three_forces_mod_512_eq_296`)**:
Whenever `s (k + 1) = 3`, `s (k + 2) = 3`, and `3 ≤ s (k + 3)` (`k + 3 < K`),
`(3^(s k) * u k + 1) % 512 = 296`. -/
theorem two_step_three_three_forces_mod_512_eq_296 {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk3 : k + 3 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs1 : s (k + 1) = 3) (hs2 : s (k + 2) = 3) (hs3 : 3 ≤ s (k + 3)) :
    (3 ^ (s k) * u k + 1) % 512 = 296 := by
  have h2step := two_step_compound_coprime_identity (by omega : k + 2 < K) hchain
  rw [hs1, hs2] at h2step
  have hmod8 :=
    (three_le_next_block_iff_mod_eight (by omega : (k + 2) + 1 < K) hchain).mp hs3
  rw [hs2] at hmod8
  have hu2_mod8 : u (k + 2) % 8 = 5 := by
    rcases hmod8 with ⟨h0, _⟩ | ⟨_, h5⟩
    · omega
    · exact h5
  have h64 : (64 * u (k + 2)) % 512 = 320 := by
    have hmul := Nat.mul_mod_mul_left 64 (u (k + 2)) 8
    simpa [hu2_mod8] using hmul
  have hrhs :
      3 ^ (s k + 3) * u k + (3 ^ 3 + 2 ^ 3) =
        27 * (3 ^ (s k) * u k + 1) + 8 := by
    rw [Nat.pow_add]
    ring
  rw [hrhs] at h2step
  have h512 : (27 * (3 ^ (s k) * u k + 1) + 8) % 512 = 320 := by
    rw [← h2step]
    exact h64
  omega

/-! ## 2. Attack Vector 2: Period-4 Law for `3^s mod 16` & Modulo-16 Phase Classifier -/

/-- Because `3^4 = 81 ≡ 1 (mod 16)`, `3^s % 16` is completely determined by `s % 4`:
`1, 3, 9, 11` for `s % 4 = 0, 1, 2, 3`. -/
theorem three_pow_mod_16_classifier (s : ℕ) :
    (s % 4 = 0 → 3 ^ s % 16 = 1) ∧
    (s % 4 = 1 → 3 ^ s % 16 = 3) ∧
    (s % 4 = 2 → 3 ^ s % 16 = 9) ∧
    (s % 4 = 3 → 3 ^ s % 16 = 11) := by
  induction s with
  | zero => decide
  | succ s ih =>
      rcases ih with ⟨ih0, ih1, ih2, ih3⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hs
      · have h3 : s % 4 = 3 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, ih3 h3]
      · have h0 : s % 4 = 0 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, ih0 h0]
      · have h1 : s % 4 = 1 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, ih1 h1]
      · have h2 : s % 4 = 2 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, ih2 h2]

/-- Algebraic classification of `s' = 3` when `2^s' * u' = 3^s * u + 1` (`u, u'` odd):
`s' = 3` holds if and only if
`(s % 4 = 0 ∧ u % 16 = 7) ∨ (s % 4 = 1 ∧ u % 16 = 13) ∨
 (s % 4 = 2 ∧ u % 16 = 15) ∨ (s % 4 = 3 ∧ u % 16 = 5)`. -/
theorem s_eq_three_iff_mod_16 {s u s' u' : ℕ}
    (hu : u % 2 = 1) (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (heq : 2 ^ s' * u' = 3 ^ s * u + 1) :
    s' = 3 ↔
      ((s % 4 = 0 ∧ u % 16 = 7) ∨
       (s % 4 = 1 ∧ u % 16 = 13) ∨
       (s % 4 = 2 ∧ u % 16 = 15) ∨
       (s % 4 = 3 ∧ u % 16 = 5)) := by
  rcases three_pow_mod_16_classifier s with ⟨h0, h1, h2, h3⟩
  have hmod16_rhs :
      (3 ^ s * u + 1) % 16 = ((3 ^ s % 16) * (u % 16) + 1) % 16 := by
    rw [Nat.add_mod, Nat.mul_mod]
    omega
  constructor
  · intro hs'3
    subst s'
    have h8 : (3 ^ s * u + 1) % 16 = 8 := by
      rw [← heq]
      omega
    rw [hmod16_rhs] at h8
    have hrem : s % 4 = 0 ∨ s % 4 = 1 ∨ s % 4 = 2 ∨ s % 4 = 3 := by omega
    rcases hrem with hs0 | hs1 | hs2 | hs3
    · rw [h0 hs0] at h8
      exact Or.inl ⟨hs0, by omega⟩
    · rw [h1 hs1] at h8
      exact Or.inr (Or.inl ⟨hs1, by omega⟩)
    · rw [h2 hs2] at h8
      exact Or.inr (Or.inr (Or.inl ⟨hs2, by omega⟩))
    · rw [h3 hs3] at h8
      exact Or.inr (Or.inr (Or.inr ⟨hs3, by omega⟩))
  · intro hcond
    have h8 : (3 ^ s * u + 1) % 16 = 8 := by
      rw [hmod16_rhs]
      rcases hcond with ⟨hs0, hu7⟩ | ⟨hs1, hu13⟩ | ⟨hs2, hu15⟩ | ⟨hs3, hu5⟩
      · rw [h0 hs0, hu7]
      · rw [h1 hs1, hu13]
      · rw [h2 hs2, hu15]
      · rw [h3 hs3, hu5]
    rw [← heq] at h8
    by_cases hs'_lt3 : s' < 3
    · have hcases : s' = 1 ∨ s' = 2 := by omega
      rcases hcases with rfl | rfl <;> omega
    · by_cases hs'3 : s' = 3
      · exact hs'3
      · have hs'4 : 4 ≤ s' := by omega
        have hdvd16 : 16 ∣ 2 ^ s' * u' := by
          have hsplit : s' = 4 + (s' - 4) := by omega
          rw [hsplit, Nat.pow_add]
          exact ⟨2 ^ (s' - 4) * u', by ring⟩
        have hzero : (2 ^ s' * u') % 16 = 0 := Nat.mod_eq_zero_of_dvd hdvd16
        omega

/-- Algebraic classification of `4 ≤ s'` when `2^s' * u' = 3^s * u + 1` (`u, u'` odd):
`4 ≤ s'` holds if and only if
`(s % 4 = 0 ∧ u % 16 = 15) ∨ (s % 4 = 1 ∧ u % 16 = 5) ∨
 (s % 4 = 2 ∧ u % 16 = 7) ∨ (s % 4 = 3 ∧ u % 16 = 13)`. -/
theorem four_le_s_iff_mod_16 {s u s' u' : ℕ}
    (hu : u % 2 = 1) (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (heq : 2 ^ s' * u' = 3 ^ s * u + 1) :
    4 ≤ s' ↔
      ((s % 4 = 0 ∧ u % 16 = 15) ∨
       (s % 4 = 1 ∧ u % 16 = 5) ∨
       (s % 4 = 2 ∧ u % 16 = 7) ∨
       (s % 4 = 3 ∧ u % 16 = 13)) := by
  rcases three_pow_mod_16_classifier s with ⟨h0, h1, h2, h3⟩
  have hmod16_rhs :
      (3 ^ s * u + 1) % 16 = ((3 ^ s % 16) * (u % 16) + 1) % 16 := by
    rw [Nat.add_mod, Nat.mul_mod]
    omega
  constructor
  · intro hs'4
    have hdvd16 : 16 ∣ 2 ^ s' * u' := by
      have hsplit : s' = 4 + (s' - 4) := by omega
      rw [hsplit, Nat.pow_add]
      exact ⟨2 ^ (s' - 4) * u', by ring⟩
    have hzero : (3 ^ s * u + 1) % 16 = 0 := by
      rw [← heq]
      exact Nat.mod_eq_zero_of_dvd hdvd16
    rw [hmod16_rhs] at hzero
    have hrem : s % 4 = 0 ∨ s % 4 = 1 ∨ s % 4 = 2 ∨ s % 4 = 3 := by omega
    rcases hrem with hs0 | hs1 | hs2 | hs3
    · rw [h0 hs0] at hzero
      exact Or.inl ⟨hs0, by omega⟩
    · rw [h1 hs1] at hzero
      exact Or.inr (Or.inl ⟨hs1, by omega⟩)
    · rw [h2 hs2] at hzero
      exact Or.inr (Or.inr (Or.inl ⟨hs2, by omega⟩))
    · rw [h3 hs3] at hzero
      exact Or.inr (Or.inr (Or.inr ⟨hs3, by omega⟩))
  · intro hcond
    have hzero : (3 ^ s * u + 1) % 16 = 0 := by
      rw [hmod16_rhs]
      rcases hcond with ⟨hs0, hu15⟩ | ⟨hs1, hu5⟩ | ⟨hs2, hu7⟩ | ⟨hs3, hu13⟩
      · rw [h0 hs0, hu15]
      · rw [h1 hs1, hu5]
      · rw [h2 hs2, hu7]
      · rw [h3 hs3, hu13]
    rw [← heq] at hzero
    by_contra hlt4
    have hcases : s' = 1 ∨ s' = 2 ∨ s' = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;> omega

/-- Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), `s (k + 1) = 3` holds
if and only if `u k % 16` matches the exact mod-16 target for `s k % 4`. -/
theorem next_block_eq_three_iff_mod_16 {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    s (k + 1) = 3 ↔
      ((s k % 4 = 0 ∧ u k % 16 = 7) ∨
       (s k % 4 = 1 ∧ u k % 16 = 13) ∨
       (s k % 4 = 2 ∧ u k % 16 = 15) ∨
       (s k % 4 = 3 ∧ u k % 16 = 5)) := by
  rcases hchain k (by omega) with ⟨_, huk, _⟩
  rcases hchain (k + 1) hk1 with ⟨hsk1, huk1, _⟩
  exact s_eq_three_iff_mod_16 huk hsk1 huk1 (coprime_quotient_recurrence hk1 hchain)

/-- Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), `4 ≤ s (k + 1)` holds
if and only if `u k % 16` matches the exact mod-16 target for `s k % 4`. -/
theorem four_le_next_block_iff_mod_16 {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    4 ≤ s (k + 1) ↔
      ((s k % 4 = 0 ∧ u k % 16 = 15) ∨
       (s k % 4 = 1 ∧ u k % 16 = 5) ∨
       (s k % 4 = 2 ∧ u k % 16 = 7) ∨
       (s k % 4 = 3 ∧ u k % 16 = 13)) := by
  rcases hchain k (by omega) with ⟨_, huk, _⟩
  rcases hchain (k + 1) hk1 with ⟨hsk1, huk1, _⟩
  exact four_le_s_iff_mod_16 huk hsk1 huk1 (coprime_quotient_recurrence hk1 hchain)

end Mahler.CeilingModTraps
