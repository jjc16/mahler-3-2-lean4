import OddBlockCoupling

/-!
# Approach 3: The First-Split Pinch After Any Shared Parity Block

This module formalizes Approach 3, analyzing what happens when two states
`a ≤ b` (such as `orbit m i` and `orbit m j` along a single orbit) share a
length-`L` parity block and then split at step `L`:

1. **Exact Carry Synchronization (`carry_eq_of_sameParityBlock`)**:
   Whenever `SameParityBlock a b L` holds, the multi-step carry integers of `a`
   and `b` over those `L` steps are identical (`carry a 0 L = carry b 0 L`).
2. **Exact 2-adic Valuation / First-Split Equivalence (`first_split_iff_two_pow_dvd`)**:
   For any `a ≤ b` and `L`, `SameParityBlock a b L` holds together with a parity
   split at step `L` (`orbit a L % 2 ≠ orbit b L % 2`) if and only if
   `2^L ∣ (b - a)` and `¬ (2^(L + 1) ∣ (b - a))`. Thus the shared parity prefix
   length is identically the 2-adic valuation `v_2(b - a)`.
3. **Exact Fractional Difference Amplification (`fracPart_diff_of_sameParityBlock`)
   and Exponential Proximity (`abs_fracPart_diff_lt_of_sameParityBlock`)**:
   Across a shared length-`L` parity block,
   `fracPart b ξ_b L - fracPart a ξ_a L = (3/2)^L * (fracPart b ξ_b 0 - fracPart a ξ_a 0)`,
   forcing `|fracPart b ξ_b 0 - fracPart a ξ_a 0| < (1/2) * (2/3)^L`.
4. **Threshold Straddling at the Split (`first_split_straddles_one_third`)**:
   At the split step `L`, whichever branch is even has fractional part `< 1/3`
   and whichever branch is odd has fractional part `≥ 1/3`.
5. **Tightened Split-Carry Pinch (`split_carry_tightened_pinch`)**:
   Because one branch is odd at step `L` while both branches share the same
   carry `carry a 0 L = carry b 0 L`, surviving one step past the split tightens
   the carry bound from `6 * carry a 0 L < 3^(L + 1)` to
   `6 * carry a 0 L + 2^(L + 1) < 3^(L + 1)`.
-/

namespace Mahler.SplitPinch

open Mahler
open Mahler.Pinch
open Mahler.OddBlock

/-! ## 1. Exact Carry Synchronization Across Shared Parity Blocks -/

theorem carry_zero_right (m j : ℕ) : carry m j 0 = 0 := by
  unfold carry
  simp

/-- If `a` and `b` share their first `L` parity bits, their `L`-step carry
integers are identical. -/
theorem carry_eq_of_sameParityBlock {a b L : ℕ}
    (h : SameParityBlock a b L) :
    carry a 0 L = carry b 0 L := by
  induction L with
  | zero => simp [carry_zero_right]
  | succ L ih =>
      have hprefix : SameParityBlock a b L := fun k hk => h k (by omega)
      have hbit : orbit a L % 2 = orbit b L % 2 := h L (by omega)
      rw [carry_succ a 0 L, carry_succ b 0 L, ih hprefix]
      simp [hbit]

/-- Along a single orbit, `carry m j k = carry (orbit m j) 0 k`. -/
theorem carry_eq_carry_orbit (m j k : ℕ) :
    carry m j k = carry (orbit m j) 0 k := by
  unfold carry
  rw [orbit_add]
  simp [orbit]

/-- Along a single orbit, any two positions `i` and `j` with the same length-`L`
parity block have the exact same `L`-step carry integer. -/
theorem orbit_carry_eq_of_sameParityBlock {m i j L : ℕ}
    (h : SameParityBlock (orbit m i) (orbit m j) L) :
    carry m i L = carry m j L := by
  rw [carry_eq_carry_orbit m i L, carry_eq_carry_orbit m j L]
  exact carry_eq_of_sameParityBlock h

/-! ## 2. Exact 2-adic Valuation Equivalence for the First Parity Split -/

private theorem three_pow_mod_two (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- If `2^L ∣ (b - a)` with `a ≤ b`, then `a` and `b` share a length-`L` parity block. -/
theorem sameParityBlock_of_two_pow_dvd {a b L : ℕ} (hab : a ≤ b)
    (hdvd : 2 ^ L ∣ b - a) :
    SameParityBlock a b L := by
  rcases hdvd with ⟨q, hq⟩
  have hb : b = 2 ^ L * q + a := by omega
  intro k hk
  have horb := orbit_add_two_pow_mul L q a k (by omega)
  rw [hb, horb]
  have hsub : L - k = (L - k - 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  have hmul :
      3 ^ k * (2 ^ (L - k - 1) * 2) * q + orbit a k =
        2 * (3 ^ k * 2 ^ (L - k - 1) * q) + orbit a k := by ring
  rw [hmul]
  omega

/-- Exact 2-adic Valuation / First-Split Equivalence:
`a ≤ b` share their first `L` parity steps and split at step `L` if and only if
`2^L ∣ (b - a)` and `¬ (2^(L + 1) ∣ (b - a))`. -/
theorem first_split_iff_two_pow_dvd {a b L : ℕ} (hab : a ≤ b) :
    (SameParityBlock a b L ∧ orbit a L % 2 ≠ orbit b L % 2) ↔
      (2 ^ L ∣ b - a ∧ ¬ (2 ^ (L + 1) ∣ b - a)) := by
  constructor
  · rintro ⟨hsame, hsplit⟩
    have hdvd : 2 ^ L ∣ b - a := parity_block_dvd_difference hab hsame
    refine ⟨hdvd, ?_⟩
    intro hdvd_succ
    have hsame_succ : SameParityBlock a b (L + 1) :=
      sameParityBlock_of_two_pow_dvd hab hdvd_succ
    exact hsplit (hsame_succ L (by omega))
  · rintro ⟨hdvd, hnot_dvd⟩
    have hsame : SameParityBlock a b L := sameParityBlock_of_two_pow_dvd hab hdvd
    refine ⟨hsame, ?_⟩
    intro heq
    have hsame_succ : SameParityBlock a b (L + 1) := by
      intro k hk
      by_cases hkL : k < L
      · exact hsame k hkL
      · have hk_eq : k = L := by omega
        subst k
        exact heq
    exact hnot_dvd (parity_block_dvd_difference hab hsame_succ)

/-! ## 3. Exact Fractional Difference Amplification & Exponential Proximity -/

/-- Relation between `fracPart a ξ L`, `fracPart a ξ 0`, and `carry a 0 L`. -/
theorem two_pow_mul_fracPart_eq (a : ℕ) (ξ : ℝ) (L : ℕ) :
    (2 : ℝ) ^ L * fracPart a ξ L =
      (3 : ℝ) ^ L * fracPart a ξ 0 - (carry a 0 L : ℝ) := by
  unfold fracPart
  have hcarry : 2 ^ L * orbit a L = 3 ^ L * a + carry a 0 L := by
    simpa [orbit] using two_pow_mul_orbit_eq_add_carry a 0 L
  have hreal : (2 : ℝ) ^ L * (orbit a L : ℝ) =
      (3 : ℝ) ^ L * (a : ℝ) + (carry a 0 L : ℝ) := by
    exact_mod_cast hcarry
  have h23 : (2 : ℝ) ^ L * (3 / 2 : ℝ) ^ L = (3 : ℝ) ^ L := by
    rw [← mul_pow]
    norm_num
  simp only [orbit, pow_zero, mul_one]
  calc
    (2 : ℝ) ^ L * (ξ * (3 / 2 : ℝ) ^ L - (orbit a L : ℝ)) =
        ξ * ((2 : ℝ) ^ L * (3 / 2 : ℝ) ^ L) - (2 : ℝ) ^ L * (orbit a L : ℝ) := by
          ring
    _ = ξ * (3 : ℝ) ^ L - ((3 : ℝ) ^ L * (a : ℝ) + (carry a 0 L : ℝ)) := by
          rw [h23, hreal]
    _ = (3 : ℝ) ^ L * (ξ - (a : ℝ)) - (carry a 0 L : ℝ) := by
          ring

/-- Because the `L`-step carry cancels across a shared parity block, the
fractional difference scales by `(3/2)^L` with zero rounding error. -/
theorem fracPart_diff_of_sameParityBlock {a b L : ℕ}
    (h : SameParityBlock a b L) (ξ_a ξ_b : ℝ) :
    fracPart b ξ_b L - fracPart a ξ_a L =
      (3 / 2 : ℝ) ^ L * (fracPart b ξ_b 0 - fracPart a ξ_a 0) := by
  have hc : (carry a 0 L : ℝ) = (carry b 0 L : ℝ) := by
    exact_mod_cast carry_eq_of_sameParityBlock h
  have ha := two_pow_mul_fracPart_eq a ξ_a L
  have hb := two_pow_mul_fracPart_eq b ξ_b L
  have h2L : (2 : ℝ) ^ L ≠ 0 := by positivity
  have h23 : (2 : ℝ) ^ L * (3 / 2 : ℝ) ^ L = (3 : ℝ) ^ L := by
    rw [← mul_pow]
    norm_num
  apply mul_left_cancel₀ h2L
  calc
    (2 : ℝ) ^ L * (fracPart b ξ_b L - fracPart a ξ_a L) =
        (2 : ℝ) ^ L * fracPart b ξ_b L - (2 : ℝ) ^ L * fracPart a ξ_a L := by
          ring
    _ = ((3 : ℝ) ^ L * fracPart b ξ_b 0 - (carry b 0 L : ℝ)) -
          ((3 : ℝ) ^ L * fracPart a ξ_a 0 - (carry a 0 L : ℝ)) := by
          rw [hb, ha]
    _ = (3 : ℝ) ^ L * (fracPart b ξ_b 0 - fracPart a ξ_a 0) := by
          rw [hc]
          ring
    _ = ((2 : ℝ) ^ L * (3 / 2 : ℝ) ^ L) * (fracPart b ξ_b 0 - fracPart a ξ_a 0) := by
          rw [h23]
    _ = (2 : ℝ) ^ L * ((3 / 2 : ℝ) ^ L * (fracPart b ξ_b 0 - fracPart a ξ_a 0)) := by
          ring

/-- If both states remain valid at step `L`, their initial fractional parts
must lie within `(1/2) * (2/3)^L` of each other. -/
theorem fracPart_initial_close_of_sameParityBlock {a b L : ℕ}
    (h : SameParityBlock a b L) {ξ_a ξ_b : ℝ}
    (haL : ValidCompanionAt a ξ_a L) (hbL : ValidCompanionAt b ξ_b L) :
    -(1 / 2 : ℝ) * (2 / 3 : ℝ) ^ L < fracPart b ξ_b 0 - fracPart a ξ_a 0 ∧
      fracPart b ξ_b 0 - fracPart a ξ_a 0 < (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ L := by
  have ha := (validCompanionAt_iff_fracPart a ξ_a L).mp haL
  have hb := (validCompanionAt_iff_fracPart b ξ_b L).mp hbL
  have hdiff := fracPart_diff_of_sameParityBlock h ξ_a ξ_b
  have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ L := by positivity
  have hinv : (2 / 3 : ℝ) ^ L * (3 / 2 : ℝ) ^ L = 1 := by
    rw [← mul_pow]
    norm_num
  have hlo : -(1 / 2 : ℝ) < (3 / 2 : ℝ) ^ L * (fracPart b ξ_b 0 - fracPart a ξ_a 0) := by
    linarith
  have hhi : (3 / 2 : ℝ) ^ L * (fracPart b ξ_b 0 - fracPart a ξ_a 0) < 1 / 2 := by
    linarith
  constructor
  · have hm := mul_lt_mul_of_pos_left hlo hp
    nlinarith
  · have hm := mul_lt_mul_of_pos_left hhi hp
    nlinarith

/-! ## 4. Threshold Straddling (`1/3`) and the Tightened Split-Carry Pinch -/

/-- An even step surviving to the next step must have fractional part `< 1/3`,
while an odd step surviving to the next step must have fractional part `≥ 1/3`. -/
theorem even_odd_step_straddles_one_third {a : ℕ} {ξ : ℝ} (n : ℕ)
    (hn : ValidCompanionAt a ξ n) (hn1 : ValidCompanionAt a ξ (n + 1)) :
    (orbit a n % 2 = 0 → fracPart a ξ n < 1 / 3) ∧
    (orbit a n % 2 = 1 → 1 / 3 ≤ fracPart a ξ n) := by
  have h0 := (validCompanionAt_iff_fracPart a ξ n).mp hn
  have h1 := (validCompanionAt_iff_fracPart a ξ (n + 1)).mp hn1
  have hsucc := fracPart_succ a ξ n
  constructor
  · intro heven
    rw [heven] at hsucc
    norm_num at hsucc
    linarith
  · intro hodd
    rw [hodd] at hsucc
    norm_num at hsucc
    linarith

/-- At a parity split (`orbit a L % 2 ≠ orbit b L % 2`), one branch has
fractional part `< 1/3` and the other has fractional part `≥ 1/3`. -/
theorem first_split_straddles_one_third {a b L : ℕ}
    (hsplit : orbit a L % 2 ≠ orbit b L % 2) {ξ_a ξ_b : ℝ}
    (haL : ValidCompanionAt a ξ_a L) (haL1 : ValidCompanionAt a ξ_a (L + 1))
    (hbL : ValidCompanionAt b ξ_b L) (hbL1 : ValidCompanionAt b ξ_b (L + 1)) :
    (fracPart a ξ_a L < 1 / 3 ∧ 1 / 3 ≤ fracPart b ξ_b L) ∨
      (fracPart b ξ_b L < 1 / 3 ∧ 1 / 3 ≤ fracPart a ξ_a L) := by
  have ha := even_odd_step_straddles_one_third L haL haL1
  have hb := even_odd_step_straddles_one_third L hbL hbL1
  have hcases :
      (orbit a L % 2 = 0 ∧ orbit b L % 2 = 1) ∨
        (orbit a L % 2 = 1 ∧ orbit b L % 2 = 0) := by omega
  rcases hcases with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
  · exact Or.inl ⟨ha.1 ha0, hb.2 hb1⟩
  · exact Or.inr ⟨hb.1 hb0, ha.2 ha1⟩

/-- **The Tightened Split-Carry Pinch**:
If `a` and `b` share a length-`L` parity block, split at step `L`, and both
satisfy `IntegerPinch` at step `L + 1`, then their shared `L`-step carry
satisfies `6 * carry a 0 L + 2^(L + 1) < 3^(L + 1)`. -/
theorem split_carry_tightened_pinch {a b L : ℕ}
    (hsame : SameParityBlock a b L)
    (hsplit : orbit a L % 2 ≠ orbit b L % 2)
    (ha : IntegerPinch a 0 (L + 1))
    (hb : IntegerPinch b 0 (L + 1)) :
    6 * carry a 0 L + 2 ^ (L + 1) < 3 ^ (L + 1) := by
  have hcarry_eq : carry a 0 L = carry b 0 L := carry_eq_of_sameParityBlock hsame
  have ha_lt : 2 * carry a 0 (L + 1) < 3 ^ (L + 1) :=
    (integerPinch_iff_two_mul_carry_lt a 0 (L + 1)).mp ha
  have hb_lt : 2 * carry b 0 (L + 1) < 3 ^ (L + 1) :=
    (integerPinch_iff_two_mul_carry_lt b 0 (L + 1)).mp hb
  have ha_succ := carry_succ a 0 L
  have hb_succ := carry_succ b 0 L
  simp only [Nat.zero_add] at ha_succ hb_succ
  have hcases :
      orbit a L % 2 = 1 ∨ orbit b L % 2 = 1 := by omega
  have hpow : 2 * 2 ^ L = 2 ^ (L + 1) := by ring
  rcases hcases with ha1 | hb1
  · rw [ha_succ, ha1, Nat.mul_one] at ha_lt
    omega
  · rw [hb_succ, ← hcarry_eq, hb1, Nat.mul_one] at hb_lt
    omega

/-- Along a single orbit `m`, if positions `i` and `j` share a length-`L`
parity block, split at step `L`, and the orbit satisfies `IntegerPinch` at
`(i, L + 1)` and `(j, L + 1)`, then `6 * carry m i L + 2^(L + 1) < 3^(L + 1)`. -/
theorem orbit_split_carry_tightened_pinch {m i j L : ℕ}
    (hsame : SameParityBlock (orbit m i) (orbit m j) L)
    (hsplit : orbit m (i + L) % 2 ≠ orbit m (j + L) % 2)
    (hi : IntegerPinch m i (L + 1))
    (hj : IntegerPinch m j (L + 1)) :
    6 * carry m i L + 2 ^ (L + 1) < 3 ^ (L + 1) := by
  rw [carry_eq_carry_orbit m i L]
  have hsplit' : orbit (orbit m i) L % 2 ≠ orbit (orbit m j) L % 2 := by
    simpa [orbit_add] using hsplit
  have hi' : IntegerPinch (orbit m i) 0 (L + 1) := by
    rw [integerPinch_iff_two_mul_carry_lt] at hi ⊢
    rwa [← carry_eq_carry_orbit m i (L + 1)]
  have hj' : IntegerPinch (orbit m j) 0 (L + 1) := by
    rw [integerPinch_iff_two_mul_carry_lt] at hj ⊢
    rwa [← carry_eq_carry_orbit m j (L + 1)]
  exact split_carry_tightened_pinch hsame hsplit' hi' hj'

end Mahler.SplitPinch
