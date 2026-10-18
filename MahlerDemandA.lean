import Std

/-!
# Demand A for Mahler's integer recurrence

Run `lake build` with the toolchain pinned in `lean-toolchain`.
This module uses only Lean's bundled standard library. The separate infinite
adversarial construction additionally uses the project's pinned Mathlib.

The recurrence is `a_(t+1) = ceil(3*a_t/2)`, implemented on natural numbers
as `(3*a_t + 1) / 2`. Matching length-L parity blocks imply divisibility
of the ordered starting-value difference by `2^L`.

The main theorem, `early_window_distinguishing_index`, says that for m > 0,
any two distinct positions in [0,T] have different length-L parity blocks
whenever `(m+1)*3^T < 2^(L+T)`. Multiplying the informal real inequality
`(m+1)*(3/2)^T < 2^L` by the positive denominator `2^T` gives exactly this
integer threshold. Blocks may extend beyond T; T bounds their start positions.

This proves only Demand A. No fractional-part hypothesis, Demand B,
or claim of nonexistence of Z-numbers is assumed or proved.
-/

namespace Mahler

def step (a : Nat) : Nat := (3 * a + 1) / 2

def orbit (m : Nat) : Nat → Nat
  | 0 => m
  | t + 1 => step (orbit m t)

def SameParityBlock (a b length : Nat) : Prop :=
  ∀ k, k < length → orbit a k % 2 = orbit b k % 2

theorem step_identity (a : Nat) : 2 * step a = 3 * a + a % 2 := by
  unfold step
  omega

theorem step_mono {a b : Nat} (h : a ≤ b) : step a ≤ step b := by
  unfold step
  omega

theorem le_step (a : Nat) : a ≤ step a := by
  unfold step
  omega

theorem lt_step {a : Nat} (h : 0 < a) : a < step a := by
  unfold step
  omega

theorem orbit_mono_start {a b : Nat} (h : a ≤ b) (t : Nat) :
    orbit a t ≤ orbit b t := by
  induction t with
  | zero => exact h
  | succ t ih => exact step_mono ih

theorem orbit_le_of_le (m : Nat) {i j : Nat} (h : i ≤ j) :
    orbit m i ≤ orbit m j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (le_step _)

theorem orbit_pos {m : Nat} (hm : 0 < m) (t : Nat) : 0 < orbit m t := by
  have h := orbit_le_of_le m (i := 0) (j := t) (Nat.zero_le t)
  exact Nat.lt_of_lt_of_le hm h

theorem orbit_lt_of_lt {m i j : Nat} (hm : 0 < m) (hij : i < j) :
    orbit m i < orbit m j := by
  have hstep : orbit m i < orbit m (i + 1) := lt_step (orbit_pos hm i)
  exact Nat.lt_of_lt_of_le hstep (orbit_le_of_le m (by omega))

theorem orbit_add (m i k : Nat) :
    orbit m (i + k) = orbit (orbit m i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change step (orbit m (i + k)) = step (orbit (orbit m i) k)
      exact congrArg step ih

theorem step_difference {a b : Nat} (hab : a ≤ b) (hp : a % 2 = b % 2) :
    2 * (step b - step a) = 3 * (b - a) := by
  have ha := step_identity a
  have hb := step_identity b
  have hs := step_mono hab
  omega

theorem scaled_difference {a b length : Nat} (hab : a ≤ b)
    (h : SameParityBlock a b length) :
    2 ^ length * (orbit b length - orbit a length) =
      3 ^ length * (b - a) := by
  induction length with
  | zero => simp [orbit]
  | succ length ih =>
      have hprefix : SameParityBlock a b length := fun k hk => h k (by omega)
      have hs := step_difference (orbit_mono_start hab length)
        (h length (by omega))
      calc
        2 ^ (length + 1) * (orbit b (length + 1) - orbit a (length + 1)) =
            2 ^ length * (2 * (step (orbit b length) - step (orbit a length))) := by
              simp only [orbit, Nat.pow_succ, Nat.mul_assoc]
        _ = 2 ^ length * (3 * (orbit b length - orbit a length)) := by rw [hs]
        _ = 3 * (2 ^ length * (orbit b length - orbit a length)) := by
              simp only [Nat.mul_left_comm]
        _ = 3 * (3 ^ length * (b - a)) := by rw [ih hprefix]
        _ = 3 ^ (length + 1) * (b - a) := by
              simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Equal parity blocks force the starting values to agree modulo `2^length`. -/
theorem parity_block_dvd_difference {a b length : Nat} (hab : a ≤ b)
    (h : SameParityBlock a b length) : 2 ^ length ∣ b - a := by
  have hd : 2 ^ length ∣ 3 ^ length * (b - a) := by
    rw [← scaled_difference hab h]
    exact Nat.dvd_mul_right _ _
  have hg : Nat.gcd (2 ^ length) (3 ^ length) = 1 :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)
  have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
  simpa only [hg, Nat.one_mul] using hc

theorem parity_block_separation {a b length : Nat} (hab : a < b)
    (h : SameParityBlock a b length) : 2 ^ length ≤ b - a :=
  Nat.le_of_dvd (by omega) (parity_block_dvd_difference (Nat.le_of_lt hab) h)

theorem step_growth (a : Nat) : 2 * (step a + 1) ≤ 3 * (a + 1) := by
  have h := step_identity a
  omega

theorem orbit_growth (m t : Nat) :
    (orbit m t + 1) * 2 ^ t ≤ (m + 1) * 3 ^ t := by
  induction t with
  | zero => simp [orbit]
  | succ t ih =>
      calc
        (orbit m (t + 1) + 1) * 2 ^ (t + 1) =
            (2 * (step (orbit m t) + 1)) * 2 ^ t := by
              simp only [orbit, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]
        _ ≤ (3 * (orbit m t + 1)) * 2 ^ t :=
              Nat.mul_le_mul_right _ (step_growth _)
        _ = 3 * ((orbit m t + 1) * 2 ^ t) := by rw [Nat.mul_assoc]
        _ ≤ 3 * ((m + 1) * 3 ^ t) := Nat.mul_le_mul_left 3 ih
        _ = (m + 1) * 3 ^ (t + 1) := by
              simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem orbit_growth_strict (m t : Nat) :
    orbit m t * 2 ^ t < (m + 1) * 3 ^ t := by
  have h : orbit m t * 2 ^ t < (orbit m t + 1) * 2 ^ t :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.pow_pos (by decide))
  exact Nat.lt_of_lt_of_le h (orbit_growth m t)

/-- An inclusive start-position window contains no repeated length-L parity block. -/
theorem early_window_no_repeat {m length T i j : Nat}
    (hm : 0 < m) (hij : i < j) (hj : j ≤ T)
    (hbound : (m + 1) * 3 ^ T < 2 ^ (length + T)) :
    ¬ (∀ k, k < length → orbit m (i + k) % 2 = orbit m (j + k) % 2) := by
  intro h
  have hp : SameParityBlock (orbit m i) (orbit m j) length := by
    intro k hk
    simpa only [orbit_add] using h k hk
  have hsep := parity_block_separation (orbit_lt_of_lt hm hij) hp
  have hend := orbit_le_of_le m hj
  have hsmall : orbit m T < 2 ^ length := by
    have hg := Nat.lt_trans (orbit_growth_strict m T) hbound
    rw [Nat.pow_add] at hg
    exact Nat.lt_of_mul_lt_mul_right hg
  omega

/-- Demand A: a differing parity label exists inside each pair of early blocks. -/
theorem early_window_distinguishing_index {m length T i j : Nat}
    (hm : 0 < m) (hij : i < j) (hj : j ≤ T)
    (hbound : (m + 1) * 3 ^ T < 2 ^ (length + T)) :
    ∃ k, k < length ∧ orbit m (i + k) % 2 ≠ orbit m (j + k) % 2 := by
  apply Classical.byContradiction
  intro h
  apply early_window_no_repeat hm hij hj hbound
  intro k hk
  apply Classical.byContradiction
  intro hne
  exact h ⟨k, hk, hne⟩

end Mahler
