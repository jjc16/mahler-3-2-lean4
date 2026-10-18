import MahlerDemandA
import Adversarial

/-! Kernel-checked examples and axiom reports. Run with `lake build`. -/

open Mahler

example : [orbit 1 0, orbit 1 1, orbit 1 2, orbit 1 3, orbit 1 4] =
    [1, 2, 3, 5, 8] := by decide

private theorem ten_step_collision : SameParityBlock 1 1025 10 := by
  have h : ∀ k : Fin 10, orbit 1 k.val % 2 = orbit 1025 k.val % 2 := by decide
  exact fun k hk => h ⟨k, hk⟩

example : 2 ^ 10 ∣ 1025 - 1 :=
  parity_block_dvd_difference (by decide) ten_step_collision

example (i j : Nat) (hij : i < j) (hj : j ≤ 15) :
    ∃ k, k < 10 ∧ orbit 1 (i + k) % 2 ≠ orbit 1 (j + k) % 2 :=
  early_window_distinguishing_index (by decide) hij hj (by decide)

example (a b : Nat) (hab : a ≤ b) :
    2 ^ 0 ∣ b - a :=
  parity_block_dvd_difference hab (fun k hk => by omega)

example : SameParityBlock 0 0 0 := by
  intro k hk
  omega

example : orbit 0 0 = orbit 0 1 := by decide

example : (0 + 1) * 3 ^ 1 < 2 ^ (3 + 1) := by decide

example : ∀ k, orbit 0 (0 + k) % 2 = orbit 0 (1 + k) % 2 := by
  have hz : ∀ t, orbit 0 t = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => simp [orbit, ih, step]
  intro k
  simp only [hz]

#print axioms Mahler.parity_block_dvd_difference
#print axioms Mahler.orbit_growth
#print axioms Mahler.early_window_no_repeat
#print axioms Mahler.early_window_distinguishing_index

example : Adversarial.encode [true, false, true] =
    [true, false, false, false, false, false, true, false, false] := by decide

example : Adversarial.numerator (Adversarial.encode [true]) = 9 := by decide

example : Adversarial.numerator (Adversarial.encode [true, true]) = 315 := by decide

example (w : List Bool) :
    2 * Adversarial.numerator (Adversarial.encode w) < 3 ^ (Adversarial.encode w).length := by
  simpa using Adversarial.zero_prefix_strict_half 0 w

example (w : List Bool) :
    2 * Adversarial.numerator (false :: Adversarial.encode w) <
      3 ^ (false :: Adversarial.encode w).length := by
  simpa using Adversarial.zero_prefix_strict_half 1 w

example (w : List Bool) :
    2 * Adversarial.numerator (false :: false :: Adversarial.encode w) <
      3 ^ (false :: false :: Adversarial.encode w).length := by
  simpa using Adversarial.zero_prefix_strict_half 2 w

#print axioms Mahler.Adversarial.encode_length
#print axioms Mahler.Adversarial.encode_injective
#print axioms Mahler.Adversarial.encoded_weight_bound
#print axioms Mahler.Adversarial.zero_prefix_strict_half
