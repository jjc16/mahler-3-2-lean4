import DeadEnds
import CoprimeQuotientPhaseLock

/-!
# Capstone: Level-2 Phase-Locking (`u_k ≡ 7 mod 64`) & Master Reduction Synthesis

This module completes our Lean 4 formalization of Mahler's `3/2` problem by
proving the **Level-2 Phase-Lock Theorem** (`s_k = 2 ⟹ u_k % 64 = 7`),
combining Level-1 (`mod 4`) and Level-2 (`mod 64`) phase-lock ruptures into a
unified finite-obstruction theorem against infinite companions, and bundling the
crown-jewel theorems of all 12 modules into `mahler_framework_master_synthesis`:

1. **Algebraic 6-Bit Equivalence (`six_le_s_iff_u_mod_64_eq_7`)**:
   Whenever `2^s' * u' = 9 * u + 1` with `u'` odd, `6 ≤ s'` holds if and only
   if `u % 64 = 7` (since `9 * 7 + 1 = 64`).
2. **The Level-2 Phase-Lock Theorem (`level_two_phase_lock_of_s_eq_two`)**:
   Along any valid block chain `ValidBlockChain a_0 s u m` with `k + 1 < m`, if
   `s k = 2` and the trajectory survives through step `blockSteps s (k + 2) + 1`,
   then `6 ≤ s (k + 1)` (`s_eq_two_forces_next_block_ge_six`), which forces the
   6-bit congruence `u k % 64 = 7`.
3. **Combined Phase-Lock Rupture Obstruction (`no_infinite_companion_of_phase_lock_rupture`)**:
   If at any block `k` (`k + 1 < m`), either Level-1 phase-locking (`mod 4`) or
   Level-2 phase-locking (`s k = 2 ∧ u k % 64 ≠ 7`) ruptures, then `a_0` cannot
   have an infinite Mahler companion `ξ ∈ ℝ`.
4. **Master Synthesis (`mahler_framework_master_synthesis`)**:
   Unites the key machine-checked theorems across the entire project.
-/

namespace Mahler.MasterReduction

open Mahler
open Mahler.Adversarial
open Mahler.DeadEnds
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

/-! ## 1. The Level-2 Phase-Lock Theorem (`s_k = 2 ⟹ u_k % 64 = 7`) -/

/-- Algebraic 6-bit congruence: if `2^s' * u' = 9 * u + 1` with `u'` odd, then
`6 ≤ s'` holds if and only if `u % 64 = 7`. -/
theorem six_le_s_iff_u_mod_64_eq_7 {u s' u' : ℕ}
    (hu' : u' % 2 = 1) (heq : 2 ^ s' * u' = 9 * u + 1) :
    6 ≤ s' ↔ u % 64 = 7 := by
  constructor
  · intro hs6
    have hdvd64 : 64 ∣ 2 ^ s' * u' := by
      have hsplit : s' = 6 + (s' - 6) := by omega
      rw [hsplit, Nat.pow_add]
      exact ⟨2 ^ (s' - 6) * u', by ring⟩
    have h0 : (9 * u + 1) % 64 = 0 := by
      rw [← heq]
      exact Nat.mod_eq_zero_of_dvd hdvd64
    omega
  · intro hu7
    by_contra hlt6
    have hs'_le5 : s' ≤ 5 := by omega
    have h64_div : 64 ∣ 9 * u + 1 := by
      refine ⟨(9 * u + 1) / 64, ?_⟩
      omega
    rw [← heq] at h64_div
    rcases h64_div with ⟨k, hk⟩
    have h64_split : 64 = 2 ^ s' * 2 ^ (6 - s') := by
      rw [← Nat.pow_add, show s' + (6 - s') = 6 by omega]
    rw [h64_split] at hk
    have hmul_eq : 2 ^ s' * u' = 2 ^ s' * (2 ^ (6 - s') * k) := by
      calc
        2 ^ s' * u' = 2 ^ s' * 2 ^ (6 - s') * k := hk
        _ = 2 ^ s' * (2 ^ (6 - s') * k) := by ring
    have hpos : 0 < 2 ^ s' := Nat.pow_pos (by decide)
    have hu'_eq : u' = 2 ^ (6 - s') * k := Nat.eq_of_mul_eq_mul_left hpos hmul_eq
    have heven : u' % 2 = 0 := by
      have hsub : 6 - s' = (5 - s') + 1 := by omega
      rw [hu'_eq, hsub, Nat.pow_succ]
      have : 2 ^ (5 - s') * 2 * k = 2 * (2 ^ (5 - s') * k) := by ring
      rw [this]
      omega
    omega

/-- Helper shifting `ValidCompanionAt` by `T` steps along the orbit. -/
theorem validCompanionAt_shift {a_0 : ℕ} {ξ : ℝ} (T n : ℕ)
    (h : ValidCompanionAt a_0 ξ (T + n)) :
    ValidCompanionAt (orbit a_0 T) (ξ * (3 / 2 : ℝ) ^ T) n := by
  unfold ValidCompanionAt at h ⊢
  rw [← orbit_add, mul_assoc, ← pow_add]
  exact h

/-- **The Level-2 Phase-Lock Theorem (`level_two_phase_lock_of_s_eq_two`)**:
Along any valid block chain `ValidBlockChain a_0 s u m` with `k + 1 < m`, if
`s k = 2` and the trajectory survives through step `blockSteps s (k + 2) + 1`,
then `6 ≤ s (k + 1)` and `u k % 64 = 7`. -/
theorem level_two_phase_lock_of_s_eq_two {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m)
    (hsk2 : s k = 2) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (k + 2) + 1)) :
    6 ≤ s (k + 1) ∧ u k % 64 = 7 := by
  rcases hchain k (by omega) with ⟨_, huk, hdecomp_k⟩
  rcases hchain (k + 1) hk1 with ⟨hsk1, huk1, hdecomp_k1⟩
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [hsk2] at hdecomp_k hrec
  have h9 : 3 ^ 2 * u k + 1 = 9 * u k + 1 := by ring
  rw [h9] at hrec
  have hTk1 : blockSteps s (k + 1) = blockSteps s k + 2 := by
    simp [blockSteps, hsk2]
  have hTk2 : blockSteps s (k + 2) = blockSteps s k + 2 + s (k + 1) := by
    change blockSteps s (k + 1) + s (k + 1) = blockSteps s k + 2 + s (k + 1)
    rw [hTk1]
  rw [hTk1, orbit_add] at hdecomp_k1
  have h0_shift : ValidCompanionAt (orbit a_0 (blockSteps s k))
      (ξ * (3 / 2 : ℝ) ^ (blockSteps s k)) 0 :=
    validCompanionAt_shift (blockSteps s k) 0
      (hsurv (blockSteps s k + 0) (by omega))
  have hs'_shift : ValidCompanionAt (orbit (orbit a_0 (blockSteps s k)) 2)
      (ξ * (3 / 2 : ℝ) ^ (blockSteps s k) * (3 / 2 : ℝ) ^ 2) (s (k + 1)) := by
    rw [← orbit_add, mul_assoc, ← pow_add]
    exact validCompanionAt_shift (blockSteps s k + 2) (s (k + 1))
      (hsurv (blockSteps s k + 2 + s (k + 1)) (by omega))
  have hs'1_shift : ValidCompanionAt (orbit (orbit a_0 (blockSteps s k)) 2)
      (ξ * (3 / 2 : ℝ) ^ (blockSteps s k) * (3 / 2 : ℝ) ^ 2) (s (k + 1) + 1) := by
    rw [← orbit_add, mul_assoc, ← pow_add]
    exact validCompanionAt_shift (blockSteps s k + 2) (s (k + 1) + 1)
      (hsurv (blockSteps s k + 2 + (s (k + 1) + 1)) (by omega))
  have hge6 : 6 ≤ s (k + 1) :=
    s_eq_two_forces_next_block_ge_six huk hdecomp_k hsk1 huk1 hdecomp_k1
      h0_shift hs'_shift hs'1_shift
  exact ⟨hge6, (six_le_s_iff_u_mod_64_eq_7 huk1 hrec).mp hge6⟩

/-! ## 2. Combined Phase-Lock Rupture Obstruction Against Infinite Companions -/

/-- Combined Level-1 (`mod 4`) and Level-2 (`s k = 2 ∧ u k % 64 ≠ 7`)
phase-lock rupture at block `k`. -/
def PhaseLockRupture (s u : ℕ → ℕ) (k : ℕ) : Prop :=
  (s k % 2 = 0 ∧ u k % 4 = 1) ∨
  (s k % 2 = 1 ∧ u k % 4 = 3) ∨
  (s k = 2 ∧ u k % 64 ≠ 7)

/-- If `PhaseLockRupture s u k` occurs at any block `k` (`k + 1 < m`) of a
valid block chain for `a_0`, then `a_0` cannot have an infinite Mahler companion. -/
theorem no_infinite_companion_of_phase_lock_rupture {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m)
    (hrupture : PhaseLockRupture s u k) :
    ¬ ∃ ξ : ℝ, IsInfiniteCompanion a_0 ξ := by
  rintro ⟨ξ, hξ⟩
  rcases hrupture with h1 | h2 | ⟨hsk2, hu64⟩
  · exact no_companion_of_phase_lock_rupture hk1 hchain (Or.inl h1)
      ⟨ξ, validCompanionUpTo_of_isInfiniteCompanion hξ _⟩
  · exact no_companion_of_phase_lock_rupture hk1 hchain (Or.inr h2)
      ⟨ξ, validCompanionUpTo_of_isInfiniteCompanion hξ _⟩
  · have hlock2 := level_two_phase_lock_of_s_eq_two hk1 hchain hsk2
      (validCompanionUpTo_of_isInfiniteCompanion hξ _)
    exact hu64 hlock2.2

/-! ## 3. Master Synthesis of the Lean 4 Mahler Framework -/

theorem mahler_framework_master_synthesis :
    -- 1. Demand A (Anti-repetition bound):
    (∀ {m length T i j : ℕ}, 0 < m → i < j → j ≤ T →
      (m + 1) * 3 ^ T < 2 ^ (length + T) →
      ∃ k, k < length ∧ orbit m (i + k) % 2 ≠ orbit m (j + k) % 2) ∧
    -- 2. Refutation of Fractional-Only Demand B:
    (∃ s : ℕ → Bool,
      (∀ n, HasSum (tailTerm s n) (fractionalTail s n)) ∧
      (∀ n, 0 ≤ fractionalTail s n ∧ fractionalTail s n ≤ (9 / 19 : ℝ) ∧
        fractionalTail s n < (1 / 2 : ℝ)) ∧
      (∀ L, 2 ^ (L / 3) ≤ blockComplexity s L)) ∧
    -- 3. Pure Integer Pinch Elimination of ℝ:
    (∀ m N : ℕ,
      (∃ ξ : ℝ, ValidCompanionUpTo m ξ N) ↔ ∀ j ≤ N, IntegerPinch m j (N - j)) ∧
    -- 4. Bridge 1 Equivalence to Unbounded Residue Exclusion:
    ((∀ m : ℕ, 0 < m → ∃ N : ℕ, ¬ ∃ ξ : ℝ, ValidCompanionUpTo m ξ N) ↔
      (∀ B : ℕ, ∃ N : ℕ, B ≤ 2 ^ N ∧
        ∀ r : ℕ, 0 < r → r < B → survivesSteps r N = false)) ∧
    -- 5. Bridge 3 Universal Mixed-Cycle Repetition Ceiling:
    (∀ {T K : ℕ}, 0 < K → ∀ a : ℕ → ℕ, ∀ d : ℕ,
      (∀ k < d, 2 ^ T * a (k + 1) = 3 ^ T * a k + K) →
      2 ^ (T * d) ∣ ((3 ^ T - 2 ^ T) * a 0 + K) ∧
        2 ^ (T * d) ≤ (3 ^ T - 2 ^ T) * a 0 + K) ∧
    -- 6. Level-1 & Level-2 Phase-Lock Rupture Obstruction:
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ},
      k + 1 < m → ValidBlockChain a_0 s u m → PhaseLockRupture s u k →
      ¬ ∃ ξ : ℝ, IsInfiniteCompanion a_0 ξ) := by
  refine ⟨fun hm hij hj hb => early_window_distinguishing_index hm hij hj hb,
    ?_, exists_validCompanionUpTo_iff_integerPinch,
    every_positive_fails_iff_unbounded_exclusion,
    fun hK a d hstep => mixed_cycle_repeat_bound hK a d hstep,
    fun hk1 hchain hrup => no_infinite_companion_of_phase_lock_rupture hk1 hchain hrup⟩
  rcases infinite_adversarial_witness with ⟨s, hsum, hbounds, _, hcomp⟩
  exact ⟨s, hsum, hbounds, hcomp⟩

end Mahler.MasterReduction
