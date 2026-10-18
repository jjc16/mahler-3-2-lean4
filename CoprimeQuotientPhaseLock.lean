import EscapeBranchTwoCap

/-!
# The Coprime Quotient Recurrence, Parity–Mod-4 Phase-Locking, and `3^(s-1)`-Compressed Approximation

This module formalizes the three structural laws uncovered while analyzing Part B:

1. **The Variable-Exponent Coprime Quotient Recurrence (`coprime_quotient_recurrence`,
   `odd_quotient_mod_six`)**:
   Factoring `orbit a_0 (T_k + s_k) = 3^(s_k - 1) * u_k` out of the `(k + 1)`-st
   odd block equation `3 * orbit a_0 T_{k+1} + 1 = 2^(s_{k+1}) * u_{k+1}`
   eliminates `orbit a_0` and yields a direct recurrence on the odd quotients
   `u_k` (which satisfy `u_k % 6 = 1 ∨ u_k % 6 = 5`):
   `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1`.
2. **The Parity–Mod-4 Phase-Locking Law (`parity_mod_four_phase_lock_iff`,
   `phase_lock_of_survives_next_block`, `no_companion_of_phase_lock_rupture`)**:
   - Because `3^s % 4` alternates between `1` (`s` even) and `3` (`s` odd),
     `2 ≤ s (k + 1)` holds if and only if
     `(s k % 2 = 0 ∧ u k % 4 = 3) ∨ (s k % 2 = 1 ∧ u k % 4 = 1)`.
   - Since `s (k + 1) = 1` dies in 2 steps (`s_eq_one_impossible`), any block
     chain surviving 2 steps past `T_{k+1}` must keep `s k % 2` and `u k % 4`
     phase-locked; any phase-lock rupture kills the trajectory within 2 steps.
3. **Even-Exponent Modulo-8 Reduction (`three_even_pow_mul_add_one_mod_eight`)**:
   When `s k = 2 * m` is even, `3^(2 * m) ≡ 1 (mod 8)`, so
   `(3^(2 * m) * u k + 1) % 8 = (u k + 1) % 8`.
4. **The `3^(s_k - 1)`-Compressed Real Approximation Identity & Squeeze
   (`compressed_real_iterate_identity`, `compressed_real_approximation_bounds`)**:
   Dividing `ξ * (3/2)^(T_k + s_k) = 3^(s_k - 1) * u_k + r_{T_k + s_k}` by
   `3^(s_k - 1)` keeps `u_k` an integer while compressing the fractional part
   by `3^(s_k - 1)`:
   `1 / 3^(s k) ≤ ξ * (3^(T_k + 1) / 2^(T_k + s k)) - u k < 1 / (2 * 3^(s k - 1))`.
-/

namespace Mahler.PhaseLock

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

/-! ## 1. The Coprime Quotient Recurrence (`2^s(k+1) * u(k+1) = 3^s(k) * u(k) + 1`) -/

/-- Every odd quotient `u k` in a valid block chain is coprime to `6`, i.e.,
`u k % 6 = 1 ∨ u k % 6 = 5`. -/
theorem odd_quotient_mod_six {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk : k < m) (hchain : ValidBlockChain a_0 s u m) :
    u k % 6 = 1 ∨ u k % 6 = 5 := by
  rcases hchain k hk with ⟨_, huk_odd, hdecomp⟩
  have hnot3 : ¬ (3 ∣ u k) := not_three_dvd_odd_part hdecomp
  have hmod3 : u k % 3 ≠ 0 := fun h0 => hnot3 (Nat.dvd_of_mod_eq_zero h0)
  omega

/-- **The Variable-Exponent Coprime Quotient Recurrence (`coprime_quotient_recurrence`)**:
For any `k + 1 < m` in a valid block chain `ValidBlockChain a_0 s u m`,
`2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1`. -/
theorem coprime_quotient_recurrence {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m) :
    2 ^ (s (k + 1)) * u (k + 1) = 3 ^ (s k) * u k + 1 := by
  rcases hchain k (by omega) with ⟨hsk, _, hdecomp_k⟩
  rcases hchain (k + 1) hk1 with ⟨_, _, hdecomp_k1⟩
  have hret :
      orbit a_0 (blockSteps s (k + 1)) = 3 ^ (s k - 1) * u k := by
    simp only [blockSteps]
    rw [orbit_add]
    exact orbit_odd_block_return hsk hdecomp_k
  have h3s : 3 * 3 ^ (s k - 1) = 3 ^ (s k) := by
    have hsub : s k = (s k - 1) + 1 := by omega
    conv_rhs => rw [hsub, Nat.pow_succ]
    ring
  rw [hret] at hdecomp_k1
  calc
    2 ^ (s (k + 1)) * u (k + 1) = 3 * (3 ^ (s k - 1) * u k) + 1 := hdecomp_k1.symm
    _ = (3 * 3 ^ (s k - 1)) * u k + 1 := by ring
    _ = 3 ^ (s k) * u k + 1 := by rw [h3s]

/-! ## 2. Parity–Mod-4 Phase-Locking and Even-Exponent Mod-8 Reduction -/

/-- Exact behavior of `3^s mod 4` depending on `s % 2`. -/
theorem three_pow_mod_four (s : ℕ) :
    (s % 2 = 0 → 3 ^ s % 4 = 1) ∧
    (s % 2 = 1 → 3 ^ s % 4 = 3) := by
  induction s with
  | zero => decide
  | succ s ih =>
      rcases ih with ⟨ihe, iho⟩
      constructor <;> intro hs
      · have hs1 : s % 2 = 1 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, iho hs1]
      · have hs0 : s % 2 = 0 := by omega
        rw [Nat.pow_succ, Nat.mul_mod, ihe hs0]

/-- When `s = 2 * m` is even, `3^(2 * m) % 8 = 1`, so
`(3^(2 * m) * u + 1) % 8 = (u + 1) % 8`. -/
theorem three_even_pow_mul_add_one_mod_eight (m u : ℕ) :
    (3 ^ (2 * m) * u + 1) % 8 = (u + 1) % 8 := by
  have h9 : 3 ^ (2 * m) % 8 = 1 := by
    induction m with
    | zero => rfl
    | succ m ih =>
        have hsplit : 2 * (m + 1) = 2 * m + 2 := by omega
        rw [hsplit, Nat.pow_add, Nat.mul_mod, ih]
  rw [Nat.add_mod, Nat.mul_mod, h9, one_mul]
  omega

/-- **Algebraic Parity–Mod-4 Phase-Locking Equivalence (`parity_mod_four_phase_lock_iff`)**:
Suppose `2^s' * u' = 3^s * u + 1` with `u, u'` odd and `1 ≤ s'`. Then `2 ≤ s'`
holds if and only if `(s % 2 = 0 ∧ u % 4 = 3) ∨ (s % 2 = 1 ∧ u % 4 = 1)`. -/
theorem parity_mod_four_phase_lock_iff {s u s' u' : ℕ}
    (hu : u % 2 = 1) (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (heq : 2 ^ s' * u' = 3 ^ s * u + 1) :
    2 ≤ s' ↔ ((s % 2 = 0 ∧ u % 4 = 3) ∨ (s % 2 = 1 ∧ u % 4 = 1)) := by
  have h3 := three_pow_mod_four s
  have hmod4_rhs :
      (3 ^ s * u + 1) % 4 = ((3 ^ s % 4) * (u % 4) + 1) % 4 := by
    rw [Nat.add_mod, Nat.mul_mod]
    omega
  constructor
  · intro hs'2
    have hdvd4 : 4 ∣ 2 ^ s' * u' := by
      have hsplit : s' = 2 + (s' - 2) := by omega
      rw [hsplit, Nat.pow_add]
      exact ⟨2 ^ (s' - 2) * u', by ring⟩
    have h0 : (3 ^ s * u + 1) % 4 = 0 := by
      rw [← heq]
      exact Nat.mod_eq_zero_of_dvd hdvd4
    rw [hmod4_rhs] at h0
    have hpar : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hpar with hs0 | hs1
    · have h30 := h3.1 hs0
      rw [h30] at h0
      exact Or.inl ⟨hs0, by omega⟩
    · have h31 := h3.2 hs1
      rw [h31] at h0
      exact Or.inr ⟨hs1, by omega⟩
  · intro hlock
    by_contra hlt2
    have hs'1 : s' = 1 := by omega
    subst s'
    have hmod4_lhs : (2 ^ 1 * u') % 4 = 2 := by omega
    have h0 : (3 ^ s * u + 1) % 4 = 2 := by
      rw [← heq]
      exact hmod4_lhs
    rw [hmod4_rhs] at h0
    rcases hlock with ⟨hs0, hu3⟩ | ⟨hs1, hu1⟩
    · have h30 := h3.1 hs0
      rw [h30, hu3] at h0
      omega
    · have h31 := h3.2 hs1
      rw [h31, hu1] at h0
      omega

/-- **Phase-Locking Along Any Surviving Block Chain (`phase_lock_of_survives_next_block`)**:
If `ValidBlockChain a_0 s u m` holds with `k + 1 < m` and the trajectory
survives to step `blockSteps s (k + 1) + 2`, then `s k` and `u k` must be
phase-locked:
`(s k % 2 = 0 ∧ u k % 4 = 3) ∨ (s k % 2 = 1 ∧ u k % 4 = 1)`. -/
theorem phase_lock_of_survives_next_block {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (k + 1) + 2)) :
    (s k % 2 = 0 ∧ u k % 4 = 3) ∨ (s k % 2 = 1 ∧ u k % 4 = 1) := by
  rcases hchain k (by omega) with ⟨_, huk, _⟩
  rcases hchain (k + 1) hk1 with ⟨hsk1, huk1, hdecomp_k1⟩
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [← parity_mod_four_phase_lock_iff huk hsk1 huk1 hrec]
  by_contra hlt2
  have hsk1_eq : s (k + 1) = 1 := by omega
  rw [hsk1_eq] at hdecomp_k1
  have hshift_surv :
      ValidCompanionUpTo (orbit a_0 (blockSteps s (k + 1)))
        (ξ * (3 / 2 : ℝ) ^ (blockSteps s (k + 1))) 2 := by
    intro n hn
    unfold ValidCompanionAt
    rw [← orbit_add, mul_assoc, ← pow_add]
    exact hsurv (blockSteps s (k + 1) + n) (by omega)
  exact s_eq_one_impossible huk1 hdecomp_k1 ⟨_, hshift_surv⟩

/-- **The Phase-Lock Rupture Death Theorem (`no_companion_of_phase_lock_rupture`)**:
If at block `k` (`k + 1 < m`), phase-locking ruptures
(`(s k % 2 = 0 ∧ u k % 4 = 1) ∨ (s k % 2 = 1 ∧ u k % 4 = 3)`), then no real
companion `ξ` can survive through step `blockSteps s (k + 1) + 2`. -/
theorem no_companion_of_phase_lock_rupture {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk1 : k + 1 < m) (hchain : ValidBlockChain a_0 s u m)
    (hrupture : (s k % 2 = 0 ∧ u k % 4 = 1) ∨ (s k % 2 = 1 ∧ u k % 4 = 3)) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s (k + 1) + 2) := by
  rintro ⟨ξ, hξ⟩
  have hlock := phase_lock_of_survives_next_block hk1 hchain hξ
  rcases hrupture with ⟨hs0, hu1⟩ | ⟨hs1, hu3⟩ <;>
    rcases hlock with ⟨hs0', hu3'⟩ | ⟨hs1', hu1'⟩ <;> omega

/-! ## 3. The `3^(s_k - 1)`-Compressed Real Approximation Identity & Squeeze -/

/-- **The `3^(s_k - 1)`-Compressed Real Iterate Identity (`compressed_real_iterate_identity`)**:
At the end of block `k` (`T_{k+1} = T_k + s_k`), dividing the real iterate
`ξ * (3/2)^(T_k + s_k) = 3^(s_k - 1) * u_k + fracPart a_0 ξ (T_k + s_k)` by
`3^(s_k - 1)` yields:
`ξ * (3^(blockSteps s k + 1) / 2^(blockSteps s k + s k)) - u k =
  fracPart a_0 ξ (blockSteps s k + s k) / 3^(s k - 1)`. -/
theorem compressed_real_iterate_identity {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk : k < m) (hchain : ValidBlockChain a_0 s u m) (ξ : ℝ) :
    ξ * ((3 : ℝ) ^ (blockSteps s k + 1) / (2 : ℝ) ^ (blockSteps s k + s k)) -
        (u k : ℝ) =
      fracPart a_0 ξ (blockSteps s k + s k) / (3 : ℝ) ^ (s k - 1) := by
  rcases hchain k hk with ⟨hsk, _, hdecomp⟩
  have hret :
      orbit a_0 (blockSteps s k + s k) = 3 ^ (s k - 1) * u k := by
    rw [orbit_add]
    exact orbit_odd_block_return hsk hdecomp
  have hret_real :
      (orbit a_0 (blockSteps s k + s k) : ℝ) =
        (3 : ℝ) ^ (s k - 1) * (u k : ℝ) := by
    exact_mod_cast hret
  have hpow3 :
      (3 : ℝ) ^ (blockSteps s k + s k) =
        (3 : ℝ) ^ (blockSteps s k + 1) * (3 : ℝ) ^ (s k - 1) := by
    have hsum : blockSteps s k + s k = (blockSteps s k + 1) + (s k - 1) := by omega
    rw [hsum, pow_add]
  have h3_ne : (3 : ℝ) ^ (s k - 1) ≠ 0 := by positivity
  unfold fracPart
  rw [hret_real, div_pow, hpow3]
  apply mul_right_cancel₀ h3_ne
  calc
    (ξ * ((3 : ℝ) ^ (blockSteps s k + 1) / (2 : ℝ) ^ (blockSteps s k + s k)) -
        (u k : ℝ)) * (3 : ℝ) ^ (s k - 1) =
      ξ * ((3 : ℝ) ^ (blockSteps s k + 1) * (3 : ℝ) ^ (s k - 1) /
        (2 : ℝ) ^ (blockSteps s k + s k)) -
        (3 : ℝ) ^ (s k - 1) * (u k : ℝ) := by ring
    _ = ((ξ * ((3 : ℝ) ^ (blockSteps s k + 1) * (3 : ℝ) ^ (s k - 1) /
          (2 : ℝ) ^ (blockSteps s k + s k)) -
          (3 : ℝ) ^ (s k - 1) * (u k : ℝ)) / (3 : ℝ) ^ (s k - 1)) *
          (3 : ℝ) ^ (s k - 1) := by
          rw [div_mul_cancel₀ _ h3_ne]

/-- **The `3^(s_k - 1)`-Compressed Real Approximation Squeeze
(`compressed_real_approximation_bounds`)**:
Whenever the trajectory survives one step past the `(k + 1)`-st odd return
(`T_k + s_k + 1`), the distance from `ξ * (3^(T_k + 1) / 2^(T_k + s_k))` to
the coprime integer `u k` is squeezed into `[1 / 3^(s k), 1 / (2 * 3^(s k - 1)))`,
of width `1 / (6 * 3^(s k - 1))`. -/
theorem compressed_real_approximation_bounds {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk : k < m) (hchain : ValidBlockChain a_0 s u m) {ξ : ℝ}
    (hvalid0 : ValidCompanionAt a_0 ξ (blockSteps s k + s k))
    (hvalid1 : ValidCompanionAt a_0 ξ (blockSteps s k + s k + 1)) :
    1 / (3 : ℝ) ^ (s k) ≤
        ξ * ((3 : ℝ) ^ (blockSteps s k + 1) / (2 : ℝ) ^ (blockSteps s k + s k)) -
          (u k : ℝ) ∧
      ξ * ((3 : ℝ) ^ (blockSteps s k + 1) / (2 : ℝ) ^ (blockSteps s k + s k)) -
          (u k : ℝ) <
        1 / (2 * (3 : ℝ) ^ (s k - 1)) := by
  rw [compressed_real_iterate_identity hk hchain ξ]
  rcases hchain k hk with ⟨hsk, huk, hdecomp⟩
  have hret_odd : orbit a_0 (blockSteps s k + s k) % 2 = 1 := by
    rw [orbit_add]
    exact orbit_odd_block_return_odd hsk huk hdecomp
  have hr_lo : (1 / 3 : ℝ) ≤ fracPart a_0 ξ (blockSteps s k + s k) :=
    (even_odd_step_straddles_one_third (blockSteps s k + s k) hvalid0 hvalid1).2 hret_odd
  have hr_hi : fracPart a_0 ξ (blockSteps s k + s k) < 1 / 2 :=
    ((validCompanionAt_iff_fracPart a_0 ξ (blockSteps s k + s k)).mp hvalid0).2
  have h3_pos : (0 : ℝ) < (3 : ℝ) ^ (s k - 1) := by positivity
  have h3s : (3 : ℝ) ^ (s k) = 3 * (3 : ℝ) ^ (s k - 1) := by
    have hsub : s k = (s k - 1) + 1 := by omega
    conv_lhs => rw [hsub, pow_succ]
    ring
  constructor
  · have hdiv := div_le_div_of_nonneg_right hr_lo (le_of_lt h3_pos)
    have h13 : (1 / 3 : ℝ) / (3 : ℝ) ^ (s k - 1) = 1 / (3 : ℝ) ^ (s k) := by
      rw [h3s, div_div]
    rwa [h13] at hdiv
  · have hdiv := div_lt_div_of_pos_right hr_hi h3_pos
    have h12 : (1 / 2 : ℝ) / (3 : ℝ) ^ (s k - 1) = 1 / (2 * (3 : ℝ) ^ (s k - 1)) := by
      rw [div_div]
    rwa [h12] at hdiv

end Mahler.PhaseLock
