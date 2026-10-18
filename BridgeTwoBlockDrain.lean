import BridgeOneArchimedean

/-!
# Bridge 2: Partition Windows, Multi-Block Drain, and Fixed-Point Divisibility

This module formalizes **Bridge 2**, establishing the coupled real-and-2-adic
laws that govern odd-to-odd blocks of arbitrary length `s ≥ 1`:

1. **Exact Partition Window Theorem (`odd_block_admissible_window`)**:
   Define the partition boundary `windowLow s = 1/3 + (1/3) * (2/3)^s`.
   Notice that `1/3 + (1/2) * (2/3)^s = windowLow (s - 1)` for all `s ≥ 1`.
   Consequently, if an odd integer `a` has block length `s` (`3a + 1 = 2^s * u`
   with `u` odd) and survives through the next odd step `s + 1`, its initial
   fractional part `r_0` is trapped in `[windowLow s, windowLow (s - 1))`.
   Since `windowLow s` is strictly decreasing, these windows form a pairwise
   disjoint partition of `(1/3, 1/2)`.
2. **Symbolic Exclusion of `s = 1` and Recharge Bound `s = 2 ⟹ s' ≥ 6`
   (`s_eq_one_impossible`, `s_eq_two_forces_next_block_ge_six`)**:
   - For `s = 1`, `windowLow 1 = 5/9 > 1/2`, so no `s = 1` block can survive 2 steps.
   - For `s = 2`, `r_2 < 3/8 < 275/729 = windowLow 5`, so the next odd block
     `s'` cannot lie in `{1, 2, 3, 4, 5}` and must satisfy `6 ≤ s'`.
3. **Universal Fixed-Point Coupling for Any Block Length `s ≥ 1`
   (`odd_block_fracPart_fixed_point`, `odd_block_integer_fixed_point`,
   `odd_block_repeat_bound`)**:
   - On the fractional side, `r_s - r*(s) = (3/2)^s * (r_0 - r*(s))` around the
     expanding fixed point `r*(s) = 3^(s-1) / (3^s - 2^s)`.
   - On the integer side, `a' = orbit a s` satisfies the dual identity around
     `-r*(s)`: `2^s * ((3^s - 2^s) * a' + 3^(s-1)) = 3^s * ((3^s - 2^s) * a + 3^(s-1))`.
   - Across `m` consecutive blocks of length `s`, coprimality of `2^(s*m)` and
     `3^(s*m)` forces `2^(s*m) ∣ ((3^s - 2^s) * a_0 + 3^(s-1))` and hence the
     explicit Archimedean repetition ceiling `2^(s*m) ≤ (3^s - 2^s) * a_0 + 3^(s-1)`.
-/

namespace Mahler.BridgeTwo

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne

/-! ## 1. The Partition Boundary `windowLow s` and Exact Admissibility Windows -/

/-- Lower boundary of the fractional admissibility window for an odd-to-odd
block of length `s`: `L(s) = 1/3 + (1/3) * (2/3)^s`. -/
noncomputable def windowLow (s : ℕ) : ℝ :=
  1 / 3 + (1 / 3 : ℝ) * (2 / 3 : ℝ) ^ s

theorem windowLow_strictAnti {s₁ s₂ : ℕ} (h : s₁ < s₂) :
    windowLow s₂ < windowLow s₁ := by
  unfold windowLow
  have hp : (2 / 3 : ℝ) ^ s₂ < (2 / 3 : ℝ) ^ s₁ :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) h
  linarith

theorem windowLow_anti {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    windowLow s₂ ≤ windowLow s₁ := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (windowLow_strictAnti hlt)

/-- Key telescoping identity: the upper threshold `1/3 + (1/2) * (2/3)^s` of
block `s` equals the lower threshold `windowLow (s - 1)` of block `s - 1`. -/
theorem windowUpper_eq_windowLow_pred {s : ℕ} (hs : 1 ≤ s) :
    (1 / 3 : ℝ) + (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ s = windowLow (s - 1) := by
  unfold windowLow
  have hsub : s = (s - 1) + 1 := by omega
  conv_lhs => rw [hsub, pow_succ]
  ring

/-- **Exact Partition Window Theorem**:
If an odd starting integer `a` has block length `s ≥ 1` (`3a + 1 = 2^s * u`
with `u` odd) and survives through step `s + 1`, then its initial fractional
part `fracPart a ξ 0` must lie in `[windowLow s, windowLow (s - 1))`. -/
theorem odd_block_admissible_window {a s u : ℕ} (hs : 1 ≤ s) (hu : u % 2 = 1)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) {ξ : ℝ}
    (hs_valid : ValidCompanionAt a ξ s)
    (hs1_valid : ValidCompanionAt a ξ (s + 1)) :
    windowLow s ≤ fracPart a ξ 0 ∧ fracPart a ξ 0 < windowLow (s - 1) := by
  have hret_odd : orbit a s % 2 = 1 :=
    orbit_odd_block_return_odd hs hu hdecomp
  have hrs_lo : (1 / 3 : ℝ) ≤ fracPart a ξ s :=
    (even_odd_step_straddles_one_third s hs_valid hs1_valid).2 hret_odd
  have hrs_hi : fracPart a ξ s < 1 / 2 :=
    ((validCompanionAt_iff_fracPart a ξ s).mp hs_valid).2
  have hmacro := fracPart_odd_block hs hdecomp ξ
  rw [hmacro] at hrs_lo hrs_hi
  have hp23 : (0 : ℝ) < (2 / 3 : ℝ) ^ s := by positivity
  have hinv : (2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← windowUpper_eq_windowLow_pred hs]
  unfold windowLow
  constructor
  · have hm := mul_le_mul_of_nonneg_left hrs_lo (le_of_lt hp23)
    nlinarith
  · have hm := mul_lt_mul_of_pos_left hrs_hi hp23
    nlinarith

/-! ## 2. Symbolic Exclusion of `s = 1` and Recharge Theorem `s = 2 ⟹ s' ≥ 6` -/

/-- **Universal Exclusion of `s = 1` Blocks**:
No integer `a` with `3a + 1 = 2 * u` (`u` odd) can survive 2 steps, because
`windowLow 1 = 5/9 > 1/2`. -/
theorem s_eq_one_impossible {a u : ℕ} (hu : u % 2 = 1)
    (hdecomp : 3 * a + 1 = 2 ^ 1 * u) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a ξ 2 := by
  rintro ⟨ξ, hξ⟩
  have h0 : fracPart a ξ 0 < 1 / 2 :=
    ((validCompanionAt_iff_fracPart a ξ 0).mp (hξ 0 (by decide))).2
  have hwin := odd_block_admissible_window (by decide : 1 ≤ 1) hu hdecomp
    (hξ 1 (by decide)) (hξ 2 (by decide))
  have hw1 : windowLow 1 = 5 / 9 := by
    unfold windowLow
    norm_num
  linarith

/-- **Symbolic Proof that `s = 2` Forces Next Odd Block `s' ≥ 6`**:
Suppose `a` has block length `s = 2` (`3a + 1 = 4u`, `u` odd), its next odd
integer `a' = orbit a 2` has block length `s' ≥ 1` (`3a' + 1 = 2^s' * u'`,
`u'` odd), and the trajectory survives through step `2 + s' + 1`. Then `6 ≤ s'`. -/
theorem s_eq_two_forces_next_block_ge_six {a u s' u' : ℕ}
    (hu : u % 2 = 1) (hdecomp : 3 * a + 1 = 2 ^ 2 * u)
    (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (hdecomp' : 3 * orbit a 2 + 1 = 2 ^ s' * u')
    {ξ : ℝ} (h0 : ValidCompanionAt a ξ 0)
    (hs'_valid : ValidCompanionAt (orbit a 2) (ξ * (3 / 2 : ℝ) ^ 2) s')
    (hs'1_valid : ValidCompanionAt (orbit a 2) (ξ * (3 / 2 : ℝ) ^ 2) (s' + 1)) :
    6 ≤ s' := by
  have hdrain : fracPart a ξ 2 < 3 / 8 :=
    (s_eq_two_fractional_drain hu hdecomp h0).2.1
  have hshift : fracPart (orbit a 2) (ξ * (3 / 2 : ℝ) ^ 2) 0 = fracPart a ξ 2 := by
    simp [fracPart, orbit]
  have hwin' := (odd_block_admissible_window hs' hu' hdecomp' hs'_valid hs'1_valid).1
  rw [hshift] at hwin'
  by_contra hlt6
  have hs'_le5 : s' ≤ 5 := by omega
  have hw5_le : windowLow 5 ≤ windowLow s' := windowLow_anti hs'_le5
  have hw5_val : windowLow 5 = 275 / 729 := by
    unfold windowLow
    norm_num
  linarith

/-! ## 3. Universal Fixed-Point Expansion and Divisibility Laws -/

/-- Expanding fractional fixed point `r*(s) = 3^(s-1) / (3^s - 2^s)` of block `s`. -/
noncomputable def blockFixedPoint (s : ℕ) : ℝ :=
  (3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)

/-- Across an odd-to-odd block of length `s ≥ 1`, the distance of `fracPart`
from `blockFixedPoint s` expands by the factor `(3/2)^s > 1`. -/
theorem odd_block_fracPart_fixed_point {a s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) (ξ : ℝ) :
    fracPart a ξ s - blockFixedPoint s =
      (3 / 2 : ℝ) ^ s * (fracPart a ξ 0 - blockFixedPoint s) := by
  rw [fracPart_odd_block hs hdecomp ξ]
  unfold blockFixedPoint
  have h2lt3 : (2 : ℝ) ^ s < (3 : ℝ) ^ s :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hden_ne : (3 : ℝ) ^ s - (2 : ℝ) ^ s ≠ 0 := by linarith
  have h2s_ne : (2 : ℝ) ^ s ≠ 0 := by positivity
  have h3s : (3 : ℝ) ^ (s - 1) * 3 = (3 : ℝ) ^ s := by
    have hsub : s = (s - 1) + 1 := by omega
    conv_rhs => rw [hsub, pow_succ]
  have h23 : (3 / 2 : ℝ) ^ s * (2 : ℝ) ^ s = (3 : ℝ) ^ s := by
    rw [← mul_pow]
    norm_num
  have h1 : (3 : ℝ) ^ s * (1 / 3) = (3 : ℝ) ^ (s - 1) := by
    rw [← h3s]
    ring
  apply mul_right_cancel₀ h2s_ne
  apply mul_right_cancel₀ hden_ne
  calc
    ((3 / 2 : ℝ) ^ s * (fracPart a ξ 0 - 1 / 3) -
        (3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) *
        (2 : ℝ) ^ s * ((3 : ℝ) ^ s - (2 : ℝ) ^ s) =
      ((3 / 2 : ℝ) ^ s * (2 : ℝ) ^ s) * (fracPart a ξ 0 - 1 / 3) *
        ((3 : ℝ) ^ s - (2 : ℝ) ^ s) -
      (2 : ℝ) ^ s *
        (((3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) *
          ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) := by ring
    _ = ((3 : ℝ) ^ s * fracPart a ξ 0 - (3 : ℝ) ^ s * (1 / 3)) *
          ((3 : ℝ) ^ s - (2 : ℝ) ^ s) -
          (2 : ℝ) ^ s * (3 : ℝ) ^ (s - 1) := by
          rw [h23, div_mul_cancel₀ _ hden_ne]
          ring
    _ = ((3 : ℝ) ^ s * fracPart a ξ 0 - (3 : ℝ) ^ (s - 1)) *
          ((3 : ℝ) ^ s - (2 : ℝ) ^ s) -
          (2 : ℝ) ^ s * (3 : ℝ) ^ (s - 1) := by
          rw [h1]
    _ = (3 : ℝ) ^ s *
          (fracPart a ξ 0 * ((3 : ℝ) ^ s - (2 : ℝ) ^ s) - (3 : ℝ) ^ (s - 1)) := by
          ring
    _ = ((3 / 2 : ℝ) ^ s * (2 : ℝ) ^ s) *
          (fracPart a ξ 0 -
            (3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) *
          ((3 : ℝ) ^ s - (2 : ℝ) ^ s) := by
          rw [h23]
          calc
            (3 : ℝ) ^ s *
                (fracPart a ξ 0 * ((3 : ℝ) ^ s - (2 : ℝ) ^ s) - (3 : ℝ) ^ (s - 1)) =
              (3 : ℝ) ^ s *
                (fracPart a ξ 0 * ((3 : ℝ) ^ s - (2 : ℝ) ^ s) -
                  ((3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) *
                    ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) := by
                rw [div_mul_cancel₀ _ hden_ne]
            _ = (3 : ℝ) ^ s *
                  (fracPart a ξ 0 -
                    (3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) *
                  ((3 : ℝ) ^ s - (2 : ℝ) ^ s) := by ring
    _ = (3 / 2 : ℝ) ^ s *
          (fracPart a ξ 0 -
            (3 : ℝ) ^ (s - 1) / ((3 : ℝ) ^ s - (2 : ℝ) ^ s)) *
          (2 : ℝ) ^ s * ((3 : ℝ) ^ s - (2 : ℝ) ^ s) := by ring

/-- **Universal Integer Fixed-Point Identity**:
Across an odd-to-odd block of length `s ≥ 1` (`3a + 1 = 2^s * u`), the next
integer `a' = orbit a s` satisfies
`2^s * ((3^s - 2^s) * orbit a s + 3^(s-1)) = 3^s * ((3^s - 2^s) * a + 3^(s-1))`. -/
theorem odd_block_integer_fixed_point {a s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    2 ^ s * ((3 ^ s - 2 ^ s) * orbit a s + 3 ^ (s - 1)) =
      3 ^ s * ((3 ^ s - 2 ^ s) * a + 3 ^ (s - 1)) := by
  have hret := orbit_odd_block_return hs hdecomp
  have hmul : 2 ^ s * orbit a s = 3 ^ (s - 1) * (3 * a + 1) := by
    rw [hret, hdecomp]
    ring
  have h3s : 3 ^ (s - 1) * 3 = 3 ^ s := by
    have hsub : s = (s - 1) + 1 := by omega
    conv_rhs => rw [hsub, Nat.pow_succ]
  have hpow : 3 ^ (s - 1) * (3 * a + 1) = 3 ^ s * a + 3 ^ (s - 1) := by
    rw [← h3s]
    ring
  rw [hpow] at hmul
  have hle : 2 ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by decide) s
  calc
    2 ^ s * ((3 ^ s - 2 ^ s) * orbit a s + 3 ^ (s - 1)) =
        (3 ^ s - 2 ^ s) * (2 ^ s * orbit a s) + 2 ^ s * 3 ^ (s - 1) := by ring
    _ = (3 ^ s - 2 ^ s) * (3 ^ s * a + 3 ^ (s - 1)) + 2 ^ s * 3 ^ (s - 1) := by
          rw [hmul]
    _ = 3 ^ s * ((3 ^ s - 2 ^ s) * a) +
          ((3 ^ s - 2 ^ s) * 3 ^ (s - 1) + 2 ^ s * 3 ^ (s - 1)) := by ring
    _ = 3 ^ s * ((3 ^ s - 2 ^ s) * a) +
          ((3 ^ s - 2 ^ s + 2 ^ s) * 3 ^ (s - 1)) := by
          rw [Nat.add_mul]
    _ = 3 ^ s * ((3 ^ s - 2 ^ s) * a + 3 ^ (s - 1)) := by
          rw [Nat.sub_add_cancel hle]
          ring

/-- Across `m` consecutive odd-to-odd blocks of the same length `s ≥ 1`
(`a_0, a_1, ..., a_m` with `a_{k+1} = orbit a_k s`), we have
`2^(s * m) * ((3^s - 2^s) * a_m + 3^(s-1)) = 3^(s * m) * ((3^s - 2^s) * a_0 + 3^(s-1))`. -/
theorem odd_block_chain_fixed_point {s : ℕ} (hs : 1 ≤ s)
    (a u : ℕ → ℕ) (m : ℕ)
    (hstep : ∀ k < m, 3 * a k + 1 = 2 ^ s * u k ∧ a (k + 1) = orbit (a k) s) :
    2 ^ (s * m) * ((3 ^ s - 2 ^ s) * a m + 3 ^ (s - 1)) =
      3 ^ (s * m) * ((3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ih' := ih (fun k hk => hstep k (by omega))
      rcases hstep m (by omega) with ⟨hdecomp, hnext⟩
      have hsingle := odd_block_integer_fixed_point hs hdecomp
      rw [← hnext] at hsingle
      calc
        2 ^ (s * (m + 1)) * ((3 ^ s - 2 ^ s) * a (m + 1) + 3 ^ (s - 1)) =
            2 ^ (s * m) * (2 ^ s * ((3 ^ s - 2 ^ s) * a (m + 1) + 3 ^ (s - 1))) := by
              rw [Nat.mul_succ, Nat.pow_add]
              ring
        _ = 2 ^ (s * m) * (3 ^ s * ((3 ^ s - 2 ^ s) * a m + 3 ^ (s - 1))) := by
              rw [hsingle]
        _ = 3 ^ s * (2 ^ (s * m) * ((3 ^ s - 2 ^ s) * a m + 3 ^ (s - 1))) := by
              ring
        _ = 3 ^ s * (3 ^ (s * m) * ((3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1))) := by
              rw [ih']
        _ = 3 ^ (s * (m + 1)) * ((3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1)) := by
              rw [Nat.mul_succ, Nat.pow_add]
              ring

/-- **The Universal Block-Repetition Ceiling (`odd_block_repeat_bound`)**:
If an initial integer `a 0` undergoes `m` consecutive odd-to-odd blocks of the
same length `s ≥ 1`, then `2^(s * m)` divides `(3^s - 2^s) * a 0 + 3^(s - 1)`,
and consequently `2^(s * m) ≤ (3^s - 2^s) * a 0 + 3^(s - 1)`. -/
theorem odd_block_repeat_bound {s : ℕ} (hs : 1 ≤ s)
    (a u : ℕ → ℕ) (m : ℕ)
    (hstep : ∀ k < m, 3 * a k + 1 = 2 ^ s * u k ∧ a (k + 1) = orbit (a k) s) :
    2 ^ (s * m) ∣ ((3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1)) ∧
      2 ^ (s * m) ≤ (3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1) := by
  have hchain := odd_block_chain_fixed_point hs a u m hstep
  have hd : 2 ^ (s * m) ∣ 3 ^ (s * m) * ((3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1)) := by
    rw [← hchain]
    exact Nat.dvd_mul_right _ _
  have hg : Nat.gcd (2 ^ (s * m)) (3 ^ (s * m)) = 1 :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)
  have hdvd : 2 ^ (s * m) ∣ ((3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1)) := by
    have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
    simpa only [hg, Nat.one_mul] using hc
  have hpos : 0 < (3 ^ s - 2 ^ s) * a 0 + 3 ^ (s - 1) := by
    have h3 : 0 < 3 ^ (s - 1) := Nat.pow_pos (by decide)
    omega
  exact ⟨hdvd, Nat.le_of_dvd hpos hdvd⟩

end Mahler.BridgeTwo
