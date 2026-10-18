import MahlerMasterReduction

/-!
# The Modulo-8 Phase Classifier, the Modulo-256 Trap, and Memoryless 3-adic Erasure

This module formalizes three deeper attacks on Part B derived from the coprime
quotient recurrence `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1`:

1. **Universal Period-2 Law for `3^s mod 8` (`three_pow_mod_eight`)**:
   Because `3^2 = 9 ≡ 1 (mod 8)`, `3^s % 8` has period `2` (not `4`):
   `3^s % 8 = 1` for all even `s`, and `3^s % 8 = 3` for all odd `s`.
2. **Exact Modulo-8 Classification of `s(k + 1)` (`next_block_eq_two_iff_mod_eight`,
   `three_le_next_block_iff_mod_eight`)**:
   Knowing only the parity `s k % 2` partitions all four odd residues of
   `u k % 8 ∈ {1, 3, 5, 7}`:
   - Two residues (`{1, 5}` for even `s k`, `{3, 7}` for odd `s k`) give
     `s(k + 1) = 1` and die in 2 steps (`no_companion_of_phase_lock_rupture`).
   - One residue (`u k % 8 = 3` for even `s k`, `u k % 8 = 1` for odd `s k`)
     forces **`s(k + 1) = 2` exactly** (`next_block_eq_two_iff_mod_eight`).
   - Only **one** residue (`u k % 8 = 7` for even `s k`, `u k % 8 = 5` for odd
     `s k`) can achieve **`3 ≤ s(k + 1)`** (`three_le_next_block_iff_mod_eight`).
3. **The Modulo-256 Trap Theorem (`mod_eight_trap_forces_mod_256_eq_28`)**:
   Whenever `(s k % 2 = 0 ∧ u k % 8 = 3) ∨ (s k % 2 = 1 ∧ u k % 8 = 1)`,
   `s(k + 1) = 2` is forced, which by Level-2 Phase-Locking (`u(k + 1) % 64 = 7`)
   forces the 8-bit congruence
   `(3^(s k) * u k + 1) % 256 = 28`, eliminating 31 of the 32 sub-classes mod 256.
4. **Memoryless Modulo-`3^(s k)` Erasure Law (`memoryless_mod_three_pow_erasure`)**:
   Reducing `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1` modulo `3^(s k)`
   erases `u k` completely:
   `(2^(s (k + 1)) * u (k + 1)) % 3^(s k) = 1`.
-/

namespace Mahler.ModEightClassifier

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

/-! ## 1. Universal Period-2 Law for `3^s mod 8` -/

/-- Because `3^2 = 9 ≡ 1 (mod 8)`, `3^s % 8` depends only on `s % 2`:
it is `1` when `s` is even and `3` when `s` is odd. -/
theorem three_pow_mod_eight (s : ℕ) :
    (s % 2 = 0 → 3 ^ s % 8 = 1) ∧
    (s % 2 = 1 → 3 ^ s % 8 = 3) := by
  induction s with
  | zero => decide
  | succ s ih =>
      rcases ih with ⟨ihe, iho⟩
      constructor <;> intro hs
      · have hs1 : s % 2 = 1 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, iho hs1]
      · have hs0 : s % 2 = 0 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, ihe hs0]

/-! ## 2. Exact Modulo-8 Classification of `s(k + 1) = 2` vs. `s(k + 1) ≥ 3` -/

/-- Algebraic classification of `s' = 2` when `2^s' * u' = 3^s * u + 1` (`u, u'` odd):
`s' = 2` holds if and only if `(s % 2 = 0 ∧ u % 8 = 3) ∨ (s % 2 = 1 ∧ u % 8 = 1)`. -/
theorem s_eq_two_iff_mod_eight {s u s' u' : ℕ}
    (hu : u % 2 = 1) (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (heq : 2 ^ s' * u' = 3 ^ s * u + 1) :
    s' = 2 ↔ ((s % 2 = 0 ∧ u % 8 = 3) ∨ (s % 2 = 1 ∧ u % 8 = 1)) := by
  have h3 := three_pow_mod_eight s
  have hmod8_rhs :
      (3 ^ s * u + 1) % 8 = ((3 ^ s % 8) * (u % 8) + 1) % 8 := by
    rw [Nat.add_mod, Nat.mul_mod]
    omega
  constructor
  · intro hs'2
    subst s'
    have hmod8_lhs : (2 ^ 2 * u') % 8 = 4 := by omega
    have h4 : (3 ^ s * u + 1) % 8 = 4 := by
      rw [← heq]
      exact hmod8_lhs
    rw [hmod8_rhs] at h4
    have hpar : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hpar with hs0 | hs1
    · have h30 := h3.1 hs0
      rw [h30] at h4
      exact Or.inl ⟨hs0, by omega⟩
    · have h31 := h3.2 hs1
      rw [h31] at h4
      exact Or.inr ⟨hs1, by omega⟩
  · intro hcond
    have h4 : (3 ^ s * u + 1) % 8 = 4 := by
      rw [hmod8_rhs]
      rcases hcond with ⟨hs0, hu3⟩ | ⟨hs1, hu1⟩
      · rw [h3.1 hs0, hu3]
      · rw [h3.2 hs1, hu1]
    rw [← heq] at h4
    by_cases hs'1 : s' = 1
    · subst s'
      omega
    · by_cases hs'2 : s' = 2
      · exact hs'2
      · have hs'3 : 3 ≤ s' := by omega
        have hdvd8 : 8 ∣ 2 ^ s' * u' := by
          have hsplit : s' = 3 + (s' - 3) := by omega
          rw [hsplit, Nat.pow_add]
          exact ⟨2 ^ (s' - 3) * u', by ring⟩
        have h0 : (2 ^ s' * u') % 8 = 0 := Nat.mod_eq_zero_of_dvd hdvd8
        omega

/-- Algebraic classification of `3 ≤ s'` when `2^s' * u' = 3^s * u + 1` (`u, u'` odd):
`3 ≤ s'` holds if and only if `(s % 2 = 0 ∧ u % 8 = 7) ∨ (s % 2 = 1 ∧ u % 8 = 5)`. -/
theorem three_le_s_iff_mod_eight {s u s' u' : ℕ}
    (hu : u % 2 = 1) (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (heq : 2 ^ s' * u' = 3 ^ s * u + 1) :
    3 ≤ s' ↔ ((s % 2 = 0 ∧ u % 8 = 7) ∨ (s % 2 = 1 ∧ u % 8 = 5)) := by
  have h3 := three_pow_mod_eight s
  have hmod8_rhs :
      (3 ^ s * u + 1) % 8 = ((3 ^ s % 8) * (u % 8) + 1) % 8 := by
    rw [Nat.add_mod, Nat.mul_mod]
    omega
  constructor
  · intro hs'3
    have hdvd8 : 8 ∣ 2 ^ s' * u' := by
      have hsplit : s' = 3 + (s' - 3) := by omega
      rw [hsplit, Nat.pow_add]
      exact ⟨2 ^ (s' - 3) * u', by ring⟩
    have h0 : (3 ^ s * u + 1) % 8 = 0 := by
      rw [← heq]
      exact Nat.mod_eq_zero_of_dvd hdvd8
    rw [hmod8_rhs] at h0
    have hpar : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hpar with hs0 | hs1
    · have h30 := h3.1 hs0
      rw [h30] at h0
      exact Or.inl ⟨hs0, by omega⟩
    · have h31 := h3.2 hs1
      rw [h31] at h0
      exact Or.inr ⟨hs1, by omega⟩
  · intro hcond
    have h0 : (3 ^ s * u + 1) % 8 = 0 := by
      rw [hmod8_rhs]
      rcases hcond with ⟨hs0, hu7⟩ | ⟨hs1, hu5⟩
      · rw [h3.1 hs0, hu7]
      · rw [h3.2 hs1, hu5]
    rw [← heq] at h0
    by_contra hlt3
    have hcases : s' = 1 ∨ s' = 2 := by omega
    rcases hcases with rfl | rfl <;> omega

/-- Along any valid block chain `ValidBlockChain a_0 s u m` (`k + 1 < m`),
`3 ≤ s (k + 1)` holds if and only if
`(s k % 2 = 0 ∧ u k % 8 = 7) ∨ (s k % 2 = 1 ∧ u k % 8 = 5)`. -/
theorem three_le_next_block_iff_mod_eight {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m) :
    3 ≤ s (k + 1) ↔
      ((s k % 2 = 0 ∧ u k % 8 = 7) ∨ (s k % 2 = 1 ∧ u k % 8 = 5)) := by
  rcases hchain k (by omega) with ⟨_, huk, _⟩
  rcases hchain (k + 1) hk1 with ⟨hsk1, huk1, _⟩
  exact three_le_s_iff_mod_eight huk hsk1 huk1
    (coprime_quotient_recurrence hk1 hchain)

/-! ## 3. The Modulo-256 Trap Theorem (`(3^(s k) * u k + 1) % 256 = 28`) -/

/-- **The Modulo-256 Trap Theorem (`mod_eight_trap_forces_mod_256_eq_28`)**:
Along a valid block chain `ValidBlockChain a_0 s u m` with `k + 2 < m`, if
`(s k % 2 = 0 ∧ u k % 8 = 3) ∨ (s k % 2 = 1 ∧ u k % 8 = 1)`, then `s (k + 1) = 2`
is forced; consequently, surviving through step `blockSteps s (k + 3) + 1`
forces `6 ≤ s (k + 2)`, `u (k + 1) % 64 = 7`, and the 8-bit congruence
`(3 ^ (s k) * u k + 1) % 256 = 28`. -/
theorem mod_eight_trap_forces_mod_256_eq_28 {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk2 : k + 2 < m) (hchain : ValidBlockChain a_0 s u m)
    (htrap : (s k % 2 = 0 ∧ u k % 8 = 3) ∨ (s k % 2 = 1 ∧ u k % 8 = 1))
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (k + 3) + 1)) :
    s (k + 1) = 2 ∧
    6 ≤ s (k + 2) ∧
    u (k + 1) % 64 = 7 ∧
    (3 ^ (s k) * u k + 1) % 256 = 28 := by
  rcases hchain k (by omega) with ⟨_, huk, _⟩
  rcases hchain (k + 1) (by omega) with ⟨hsk1, huk1, _⟩
  have hrec := coprime_quotient_recurrence (by omega : k + 1 < m) hchain
  have hsk1_eq2 : s (k + 1) = 2 :=
    (s_eq_two_iff_mod_eight huk hsk1 huk1 hrec).mpr htrap
  have hlevel2 :=
    level_two_phase_lock_of_s_eq_two (k := k + 1) hk2 hchain hsk1_eq2 hsurv
  rw [hsk1_eq2] at hrec
  have hmod256 : (3 ^ (s k) * u k + 1) % 256 = 28 := by
    have hu64 : u (k + 1) % 64 = 7 := hlevel2.2
    omega
  exact ⟨hsk1_eq2, hlevel2.1, hlevel2.2, hmod256⟩

/-! ## 4. Memoryless Modulo-`3^(s k)` Erasure Law -/

/-- **Memoryless Modulo-`3^(s k)` Erasure Law (`memoryless_mod_three_pow_erasure`)**:
Along any valid block chain `ValidBlockChain a_0 s u m` with `k + 1 < m`,
`(2 ^ (s (k + 1)) * u (k + 1)) % 3 ^ (s k) = 1`.
Thus `u (k + 1) mod 3 ^ (s k)` is determined purely by `(s k, s (k + 1))`,
erasing all memory of `u k` modulo `3 ^ (s k)`. -/
theorem memoryless_mod_three_pow_erasure {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m) :
    (2 ^ (s (k + 1)) * u (k + 1)) % 3 ^ (s k) = 1 := by
  rcases hchain k (by omega) with ⟨hsk, _, _⟩
  have hrec := coprime_quotient_recurrence hk1 hchain
  have hgt1 : 1 < 3 ^ (s k) := by
    have hsub : s k = (s k - 1) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    have hpos : 0 < 3 ^ (s k - 1) := Nat.pow_pos (by decide)
    omega
  have hrew : 3 ^ (s k) * u k + 1 = 1 + 3 ^ (s k) * u k := by ring
  rw [hrec, hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hgt1]

end Mahler.ModEightClassifier
