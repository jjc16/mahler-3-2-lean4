import Adversarial
import Mathlib.Data.Nat.Basic

/-! The stream encoding shared by the infinite-series and complexity proofs. -/

namespace Mahler.Adversarial

def encodeStream (s : ℕ → Bool) (k : ℕ) : Bool :=
  if k % 3 = 0 then s (k / 3) else false

@[simp] theorem encodeStream_three_mul (s : ℕ → Bool) (k : ℕ) :
    encodeStream s (3 * k) = s k := by
  simp [encodeStream]

@[simp] theorem encodeStream_three_mul_add_one (s : ℕ → Bool) (k : ℕ) :
    encodeStream s (3 * k + 1) = false := by
  simp [encodeStream, Nat.add_mod]

@[simp] theorem encodeStream_three_mul_add_two (s : ℕ → Bool) (k : ℕ) :
    encodeStream s (3 * k + 2) = false := by
  simp [encodeStream, Nat.add_mod]

end Mahler.Adversarial
