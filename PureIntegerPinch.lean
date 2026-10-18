import MahlerDemandA
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Pure Integer Pinch & Backward Floor Laws

This module formalizes Approach 1: eliminating the real number `ξ` and the
real fractional parts `r_n` from Mahler's `3/2` survival problem in favor of
exact integer inequalities, floor divisions, and modulo-`3^k` residues on the
forward orbit `a_{n+1} = ⌈3 a_n / 2⌉`:

1. **Real-Bound Monotonicity and Parity Drift**:
   The lower bound `L_n = (2/3)^n a_n` is monotonically non-decreasing, while
   the upper bound `U_n = (2/3)^n (a_n + 1/2)` drops on even steps and rises
   on odd steps.
2. **Elimination of `ℝ` (`exists_validCompanionUpTo_iff_integerPinch`)**:
   There exists a real `ξ` keeping `0 ≤ ξ (3/2)^n - a_n < 1/2` for all `n ≤ N`
   if and only if the **Pure Integer Pinch Inequality**
   `2^(k+1) * a_{j+k} < 3^k * (2 * a_j + 1)` holds for all `j + k ≤ N`.
3. **Exact Backward Floor Recovery (`integerPinch_iff_floor_eq_two_mul`)**:
   Because `3^k * (2 * a_j) ≤ 2^(k+1) * a_{j+k}` holds unconditionally, the
   pinch inequality holds if and only if the natural-number floor quotient
   `(2^(k+1) * a_{j+k}) / 3^k` equals `2 * a_j` (which is always even).
4. **First-Failure Odd Jump (`first_failure_floor_odd`)**:
   If the pinch inequality holds at `(j, k)` and fails at `(j, k+1)`, then
   `(2^(k+2) * a_{j+k+1}) / 3^(k+1) = 2 * a_j + 1` (odd).
5. **Dual Modulo-`3^k` Residue Law (`integerPinch_iff_div_and_mod_three_pow`)**:
   The pinch inequality is equivalent to `(2^k * a_{j+k}) / 3^k = a_j` together
   with `2 * ((2^k * a_{j+k}) % 3^k) < 3^k`.
-/

namespace Mahler.Pinch

open Mahler

/-! ## 1. Universal Lower Squeeze and the Carry Integer -/

/-- `3 * a ≤ 2 * step a` for every natural number `a`. -/
theorem three_mul_le_two_mul_step (a : ℕ) :
    3 * a ≤ 2 * step a := by
  have h := step_identity a
  omega

/-- `2 * step a ≤ 3 * a + 1` for every natural number `a`. -/
theorem two_mul_step_le_three_mul_add_one (a : ℕ) :
    2 * step a ≤ 3 * a + 1 := by
  have h := step_identity a
  omega

/-- Universal lower squeeze: `3^k * a_j ≤ 2^k * a_{j+k}` for all `m, j, k`. -/
theorem three_pow_mul_orbit_le (m j k : ℕ) :
    3 ^ k * orbit m j ≤ 2 ^ k * orbit m (j + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := three_mul_le_two_mul_step (orbit m (j + k))
      have h3 : 3 * (3 ^ k * orbit m j) ≤ 3 * (2 ^ k * orbit m (j + k)) :=
        Nat.mul_le_mul_left 3 ih
      have h2 :
          2 ^ k * (3 * orbit m (j + k)) ≤ 2 ^ k * (2 * step (orbit m (j + k))) :=
        Nat.mul_le_mul_left (2 ^ k) hstep
      calc
        3 ^ (k + 1) * orbit m j = 3 * (3 ^ k * orbit m j) := by ring
        _ ≤ 3 * (2 ^ k * orbit m (j + k)) := h3
        _ = 2 ^ k * (3 * orbit m (j + k)) := by ring
        _ ≤ 2 ^ k * (2 * step (orbit m (j + k))) := h2
        _ = 2 ^ (k + 1) * orbit m (j + (k + 1)) := by
              rw [← Nat.add_assoc]
              simp only [orbit]
              ring

/-- Doubled universal lower squeeze: `3^k * (2 * a_j) ≤ 2^(k+1) * a_{j+k}`. -/
theorem three_pow_mul_two_orbit_le (m j k : ℕ) :
    3 ^ k * (2 * orbit m j) ≤ 2 ^ (k + 1) * orbit m (j + k) := by
  have h := Nat.mul_le_mul_left 2 (three_pow_mul_orbit_le m j k)
  calc
    3 ^ k * (2 * orbit m j) = 2 * (3 ^ k * orbit m j) := by ring
    _ ≤ 2 * (2 ^ k * orbit m (j + k)) := h
    _ = 2 ^ (k + 1) * orbit m (j + k) := by ring

/-- The multi-step carry integer `C_{j,k} = 2^k a_{j+k} - 3^k a_j`. -/
def carry (m j k : ℕ) : ℕ :=
  2 ^ k * orbit m (j + k) - 3 ^ k * orbit m j

theorem two_pow_mul_orbit_eq_add_carry (m j k : ℕ) :
    2 ^ k * orbit m (j + k) = 3 ^ k * orbit m j + carry m j k := by
  unfold carry
  have h := three_pow_mul_orbit_le m j k
  omega

theorem carry_succ (m j k : ℕ) :
    carry m j (k + 1) =
      3 * carry m j k + 2 ^ k * (orbit m (j + k) % 2) := by
  have hk := two_pow_mul_orbit_eq_add_carry m j k
  have hk1 := two_pow_mul_orbit_eq_add_carry m j (k + 1)
  have hstep := step_identity (orbit m (j + k))
  have horbit : orbit m (j + (k + 1)) = step (orbit m (j + k)) := by
    rw [← Nat.add_assoc]
    rfl
  rw [horbit] at hk1
  have hcomb :
      2 ^ (k + 1) * step (orbit m (j + k)) =
        2 ^ k * (2 * step (orbit m (j + k))) := by ring
  rw [hcomb, hstep] at hk1
  have hdist :
      2 ^ k * (3 * orbit m (j + k) + orbit m (j + k) % 2) =
        3 * (2 ^ k * orbit m (j + k)) + 2 ^ k * (orbit m (j + k) % 2) := by ring
  rw [hdist, hk] at hk1
  have hring :
      3 * (3 ^ k * orbit m j + carry m j k) =
        3 ^ (k + 1) * orbit m j + 3 * carry m j k := by ring
  rw [hring] at hk1
  omega

/-! ## 2. The Pure Integer Pinch Inequality and Its Equivalent Forms -/

/-- The Pure Integer Pinch Inequality at base index `j` and offset `k`. -/
def IntegerPinch (m j k : ℕ) : Prop :=
  2 ^ (k + 1) * orbit m (j + k) < 3 ^ k * (2 * orbit m j + 1)

theorem integerPinch_zero (m j : ℕ) : IntegerPinch m j 0 := by
  unfold IntegerPinch
  simp

/-- `IntegerPinch m j k` holds iff `2 * carry m j k < 3^k`. -/
theorem integerPinch_iff_two_mul_carry_lt (m j k : ℕ) :
    IntegerPinch m j k ↔ 2 * carry m j k < 3 ^ k := by
  unfold IntegerPinch
  have h := two_pow_mul_orbit_eq_add_carry m j k
  have h2 :
      2 ^ (k + 1) * orbit m (j + k) =
        3 ^ k * (2 * orbit m j) + 2 * carry m j k := by
    calc
      2 ^ (k + 1) * orbit m (j + k) = 2 * (2 ^ k * orbit m (j + k)) := by ring
      _ = 2 * (3 ^ k * orbit m j + carry m j k) := by rw [h]
      _ = 3 ^ k * (2 * orbit m j) + 2 * carry m j k := by ring
  have h3 :
      3 ^ k * (2 * orbit m j + 1) = 3 ^ k * (2 * orbit m j) + 3 ^ k := by ring
  rw [h2, h3]
  omega

/-- Exact Backward Floor Recovery: `IntegerPinch m j k` holds iff the floor
quotient `(2^(k+1) * a_{j+k}) / 3^k` equals `2 * a_j`. -/
theorem integerPinch_iff_floor_eq_two_mul (m j k : ℕ) :
    IntegerPinch m j k ↔
      (2 ^ (k + 1) * orbit m (j + k)) / 3 ^ k = 2 * orbit m j := by
  unfold IntegerPinch
  have hlo := three_pow_mul_two_orbit_le m j k
  have hpos : 0 < 3 ^ k := Nat.pow_pos (by decide)
  constructor
  · intro hhi
    apply Nat.le_antisymm
    · exact Nat.div_lt_iff_lt_mul hpos |>.mpr (by
        simpa [Nat.mul_comm] using hhi) |> Nat.le_of_lt_succ
    · exact (Nat.le_div_iff_mul_le hpos).mpr (by
        simpa [Nat.mul_comm] using hlo)
  · intro hdiv
    have hlt : (2 ^ (k + 1) * orbit m (j + k)) / 3 ^ k < 2 * orbit m j + 1 := by
      omega
    have hm := (Nat.div_lt_iff_lt_mul hpos).mp hlt
    simpa [Nat.mul_comm] using hm

/-- Whenever `IntegerPinch m j k` holds, the backward floor quotient is even. -/
theorem floor_even_of_integerPinch {m j k : ℕ} (h : IntegerPinch m j k) :
    ((2 ^ (k + 1) * orbit m (j + k)) / 3 ^ k) % 2 = 0 := by
  rw [(integerPinch_iff_floor_eq_two_mul m j k).mp h]
  omega

/-- At the very next step after a valid `IntegerPinch m j k`, `2 * carry m j (k+1)`
is strictly below `2 * 3^(k+1)`, so if `IntegerPinch m j (k+1)` fails, the floor
quotient `(2^(k+2) * a_{j+k+1}) / 3^(k+1)` jumps to the odd integer `2 * a_j + 1`. -/
theorem first_failure_floor_eq_two_mul_add_one {m j k : ℕ}
    (hok : IntegerPinch m j k) (hfail : ¬ IntegerPinch m j (k + 1)) :
    (2 ^ (k + 2) * orbit m (j + (k + 1))) / 3 ^ (k + 1) =
      2 * orbit m j + 1 := by
  have hc_ok : 2 * carry m j k < 3 ^ k :=
    (integerPinch_iff_two_mul_carry_lt m j k).mp hok
  have hc_fail : 3 ^ (k + 1) ≤ 2 * carry m j (k + 1) := by
    have hnot : ¬ (2 * carry m j (k + 1) < 3 ^ (k + 1)) :=
      fun h => hfail ((integerPinch_iff_two_mul_carry_lt m j (k + 1)).mpr h)
    omega
  have hpow : 2 ^ (k + 1) ≤ 2 * 3 ^ k := by
    have h23 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ 2 * 3 ^ k := Nat.mul_le_mul_left 2 h23
  have hmod : orbit m (j + k) % 2 ≤ 1 := by omega
  have h2pow : 2 ^ (k + 1) * (orbit m (j + k) % 2) ≤ 2 ^ (k + 1) := by
    calc
      2 ^ (k + 1) * (orbit m (j + k) % 2) ≤ 2 ^ (k + 1) * 1 :=
        Nat.mul_le_mul_left _ hmod
      _ = 2 ^ (k + 1) := Nat.mul_one _
  have hc_upper : 2 * carry m j (k + 1) < 2 * 3 ^ (k + 1) := by
    have hcs := carry_succ m j k
    have hpow3 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    have h2k : 2 * (2 ^ k * (orbit m (j + k) % 2)) =
        2 ^ (k + 1) * (orbit m (j + k) % 2) := by ring
    omega
  have hexpand :
      2 ^ (k + 2) * orbit m (j + (k + 1)) =
        3 ^ (k + 1) * (2 * orbit m j) + 2 * carry m j (k + 1) := by
    have h := two_pow_mul_orbit_eq_add_carry m j (k + 1)
    calc
      2 ^ (k + 2) * orbit m (j + (k + 1)) =
          2 * (2 ^ (k + 1) * orbit m (j + (k + 1))) := by ring
      _ = 2 * (3 ^ (k + 1) * orbit m j + carry m j (k + 1)) := by rw [h]
      _ = 3 ^ (k + 1) * (2 * orbit m j) + 2 * carry m j (k + 1) := by ring
  have hpos : 0 < 3 ^ (k + 1) := Nat.pow_pos (by decide)
  have hlo :
      (2 * orbit m j + 1) * 3 ^ (k + 1) ≤ 2 ^ (k + 2) * orbit m (j + (k + 1)) := by
    rw [hexpand]
    have : (2 * orbit m j + 1) * 3 ^ (k + 1) =
        3 ^ (k + 1) * (2 * orbit m j) + 3 ^ (k + 1) := by ring
    omega
  have hhi :
      2 ^ (k + 2) * orbit m (j + (k + 1)) < (2 * orbit m j + 2) * 3 ^ (k + 1) := by
    rw [hexpand]
    have : (2 * orbit m j + 2) * 3 ^ (k + 1) =
        3 ^ (k + 1) * (2 * orbit m j) + 2 * 3 ^ (k + 1) := by ring
    omega
  apply Nat.le_antisymm
  · exact (Nat.div_lt_iff_lt_mul hpos).mpr hhi |> Nat.le_of_lt_succ
  · exact (Nat.le_div_iff_mul_le hpos).mpr hlo

/-- Dual Modulo-`3^k` Residue Law: `IntegerPinch m j k` holds iff
`(2^k * a_{j+k}) / 3^k = a_j` and `2 * ((2^k * a_{j+k}) % 3^k) < 3^k`. -/
theorem integerPinch_iff_div_and_mod_three_pow (m j k : ℕ) :
    IntegerPinch m j k ↔
      (2 ^ k * orbit m (j + k)) / 3 ^ k = orbit m j ∧
      2 * ((2 ^ k * orbit m (j + k)) % 3 ^ k) < 3 ^ k := by
  rw [integerPinch_iff_two_mul_carry_lt]
  have heq := two_pow_mul_orbit_eq_add_carry m j k
  have hpos : 0 < 3 ^ k := Nat.pow_pos (by decide)
  constructor
  · intro hlt
    have hc : carry m j k < 3 ^ k := by omega
    have hdiv : (2 ^ k * orbit m (j + k)) / 3 ^ k = orbit m j := by
      apply Nat.le_antisymm
      · have hlt' : 2 ^ k * orbit m (j + k) < (orbit m j + 1) * 3 ^ k := by
          rw [heq]
          have : (orbit m j + 1) * 3 ^ k = 3 ^ k * orbit m j + 3 ^ k := by ring
          omega
        exact (Nat.div_lt_iff_lt_mul hpos).mpr hlt' |> Nat.le_of_lt_succ
      · have hle' : orbit m j * 3 ^ k ≤ 2 ^ k * orbit m (j + k) := by
          rw [heq]
          have : orbit m j * 3 ^ k = 3 ^ k * orbit m j := by ring
          omega
        exact (Nat.le_div_iff_mul_le hpos).mpr hle'
    have hmod : (2 ^ k * orbit m (j + k)) % 3 ^ k = carry m j k := by
      have hdm := Nat.div_add_mod (2 ^ k * orbit m (j + k)) (3 ^ k)
      rw [hdiv] at hdm
      omega
    exact ⟨hdiv, by simpa [hmod] using hlt⟩
  · rintro ⟨hdiv, hmod_lt⟩
    have hdm := Nat.div_add_mod (2 ^ k * orbit m (j + k)) (3 ^ k)
    rw [hdiv] at hdm
    have hmod : (2 ^ k * orbit m (j + k)) % 3 ^ k = carry m j k := by omega
    simpa [hmod] using hmod_lt

/-! ## 3. Complete Elimination of `ℝ` for Mahler Companion Survival -/

/-- `ξ` has integer part `orbit m n` and fractional part in `[0, 1/2)` at step `n`. -/
def ValidCompanionAt (m : ℕ) (ξ : ℝ) (n : ℕ) : Prop :=
  (orbit m n : ℝ) ≤ ξ * (3 / 2 : ℝ) ^ n ∧
    ξ * (3 / 2 : ℝ) ^ n < (orbit m n : ℝ) + 1 / 2

def ValidCompanionUpTo (m : ℕ) (ξ : ℝ) (N : ℕ) : Prop :=
  ∀ n ≤ N, ValidCompanionAt m ξ n

noncomputable def lowerBound (m n : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ n * (orbit m n : ℝ)

noncomputable def upperBound (m n : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ n * ((orbit m n : ℝ) + 1 / 2)

private theorem two_thirds_mul_three_halves (n : ℕ) :
    (2 / 3 : ℝ) ^ n * (3 / 2 : ℝ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

theorem validCompanionAt_iff_bounds (m : ℕ) (ξ : ℝ) (n : ℕ) :
    ValidCompanionAt m ξ n ↔ lowerBound m n ≤ ξ ∧ ξ < upperBound m n := by
  unfold ValidCompanionAt lowerBound upperBound
  have hp23 : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
  have hp32 : (0 : ℝ) < (3 / 2 : ℝ) ^ n := by positivity
  have hinv := two_thirds_mul_three_halves n
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h := mul_le_mul_of_nonneg_left hlo (le_of_lt hp23)
      nlinarith
    · have h := mul_lt_mul_of_pos_left hhi hp23
      nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h := mul_le_mul_of_nonneg_right hlo (le_of_lt hp32)
      nlinarith
    · have h := mul_lt_mul_of_pos_right hhi hp32
      nlinarith

/-- The lower bound `L_n = (2/3)^n a_n` is monotonically non-decreasing. -/
theorem lowerBound_step_le (m n : ℕ) :
    lowerBound m n ≤ lowerBound m (n + 1) := by
  unfold lowerBound
  have hstep : (3 : ℝ) * (orbit m n : ℝ) ≤ 2 * (orbit m (n + 1) : ℝ) := by
    exact_mod_cast three_mul_le_two_mul_step (orbit m n)
  have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
  rw [pow_succ]
  nlinarith

theorem lowerBound_mono (m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    lowerBound m i ≤ lowerBound m j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact le_rfl
      · exact le_trans (ih (by omega)) (lowerBound_step_le m j)

/-- Exact drift of the upper bound `U_n`: drops on even steps, rises on odd steps. -/
theorem upperBound_step_diff (m n : ℕ) :
    upperBound m (n + 1) - upperBound m n =
      (2 / 3 : ℝ) ^ n * ((2 * ((orbit m n % 2 : ℕ) : ℝ) - 1) / 6) := by
  unfold upperBound
  have hstep : 2 * (orbit m (n + 1) : ℝ) =
      3 * (orbit m n : ℝ) + ((orbit m n % 2 : ℕ) : ℝ) := by
    exact_mod_cast step_identity (orbit m n)
  rw [pow_succ]
  calc
    (2 / 3 : ℝ) ^ n * (2 / 3) * ((orbit m (n + 1) : ℝ) + 1 / 2) -
        (2 / 3 : ℝ) ^ n * ((orbit m n : ℝ) + 1 / 2) =
      (2 / 3 : ℝ) ^ n *
        ((2 * (orbit m (n + 1) : ℝ) - 3 * (orbit m n : ℝ) - 1 / 2) / 3) := by
        ring
    _ = (2 / 3 : ℝ) ^ n * ((2 * ((orbit m n % 2 : ℕ) : ℝ) - 1) / 6) := by
        rw [hstep]
        ring

private theorem two_thirds_mul_three_pow (k : ℕ) :
    (2 / 3 : ℝ) ^ k * (3 : ℝ) ^ k = (2 : ℝ) ^ k := by
  rw [← mul_pow]
  norm_num

/-- Bridge between the real bounds `L_{j+k} < U_j` and `IntegerPinch m j k`. -/
theorem lowerBound_lt_upperBound_iff_integerPinch (m j k : ℕ) :
    lowerBound m (j + k) < upperBound m j ↔ IntegerPinch m j k := by
  unfold lowerBound upperBound IntegerPinch
  have hpj : (0 : ℝ) < (2 / 3 : ℝ) ^ j := by positivity
  have h23k : (0 : ℝ) < 2 * (3 : ℝ) ^ k := by positivity
  have hmul_3k := two_thirds_mul_three_pow k
  have hL :
      (2 / 3 : ℝ) ^ (j + k) * (orbit m (j + k) : ℝ) * (2 * (3 : ℝ) ^ k) =
        (2 / 3 : ℝ) ^ j * ((2 : ℝ) ^ (k + 1) * (orbit m (j + k) : ℝ)) := by
    rw [pow_add, pow_succ]
    calc
      (2 / 3 : ℝ) ^ j * (2 / 3 : ℝ) ^ k * (orbit m (j + k) : ℝ) * (2 * (3 : ℝ) ^ k) =
          (2 / 3 : ℝ) ^ j * ((2 / 3 : ℝ) ^ k * (3 : ℝ) ^ k) * 2 * (orbit m (j + k) : ℝ) := by
            ring
      _ = (2 / 3 : ℝ) ^ j * ((2 : ℝ) ^ k * 2 * (orbit m (j + k) : ℝ)) := by
            rw [hmul_3k]
            ring
  have hU :
      (2 / 3 : ℝ) ^ j * ((orbit m j : ℝ) + 1 / 2) * (2 * (3 : ℝ) ^ k) =
        (2 / 3 : ℝ) ^ j * ((3 : ℝ) ^ k * (2 * (orbit m j : ℝ) + 1)) := by
    ring
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right h h23k
    rw [hL, hU] at h1
    have h2 : (2 : ℝ) ^ (k + 1) * (orbit m (j + k) : ℝ) <
        (3 : ℝ) ^ k * (2 * (orbit m j : ℝ) + 1) := by nlinarith
    exact_mod_cast h2
  · intro h
    have hreal : (2 : ℝ) ^ (k + 1) * (orbit m (j + k) : ℝ) <
        (3 : ℝ) ^ k * (2 * (orbit m j : ℝ) + 1) := by
      exact_mod_cast h
    have h1 := mul_lt_mul_of_pos_left hreal hpj
    rw [← hL, ← hU] at h1
    nlinarith

/-- Complete elimination of `ℝ` at horizon `N`: a valid real companion `ξ`
exists up to step `N` if and only if `IntegerPinch m j (N - j)` holds for all
`j ≤ N` (with the explicit rational witness `ξ = lowerBound m N`). -/
theorem exists_validCompanionUpTo_iff_integerPinch (m N : ℕ) :
    (∃ ξ : ℝ, ValidCompanionUpTo m ξ N) ↔
      ∀ j ≤ N, IntegerPinch m j (N - j) := by
  constructor
  · rintro ⟨ξ, hξ⟩ j hj
    have hN := (validCompanionAt_iff_bounds m ξ N).mp (hξ N (Nat.le_refl N))
    have hj' := (validCompanionAt_iff_bounds m ξ j).mp (hξ j hj)
    have hlt : lowerBound m (j + (N - j)) < upperBound m j := by
      have hsum : j + (N - j) = N := by omega
      rw [hsum]
      linarith
    exact (lowerBound_lt_upperBound_iff_integerPinch m j (N - j)).mp hlt
  · intro hpinch
    refine ⟨lowerBound m N, ?_⟩
    intro n hn
    rw [validCompanionAt_iff_bounds]
    refine ⟨lowerBound_mono m hn, ?_⟩
    have hlt := (lowerBound_lt_upperBound_iff_integerPinch m n (N - n)).mpr (hpinch n hn)
    have hsum : n + (N - n) = N := by omega
    rwa [hsum] at hlt

end Mahler.Pinch
