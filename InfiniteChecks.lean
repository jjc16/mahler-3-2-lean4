import InfiniteAdversarial

/-! Infinite witness boundary checks and transitive axiom audit. -/

open Mahler.Adversarial

example : 1 ≤ blockComplexity (encodeStream universalStream) 0 := by
  simpa using encoded_complexity_lower_bound 0

example : 32 ≤ blockComplexity (encodeStream universalStream) 15 := by
  simpa using encoded_complexity_lower_bound 15

example : 1024 ≤ blockComplexity (encodeStream universalStream) 30 := by
  simpa using encoded_complexity_lower_bound 30

example (n : ℕ) :
    (1 / 38 : ℝ) ≤ 1 / 2 - fractionalTail (encodeStream universalStream) n :=
  encoded_fractionalTail_margin _ _

example (s : ℕ → Bool) (n : ℕ) :
    HasSum (tailTerm (encodeStream s) n) (fractionalTail (encodeStream s) n) :=
  fractionalTail_hasSum _ _

example (n : ℕ) : fractionalTail (encodeStream (fun _ => false)) n = 0 := by
  simp [fractionalTail, tailTerm, encodeStream]

#print axioms Mahler.Adversarial.fractionalTail_hasSum
#print axioms Mahler.Adversarial.encoded_fractionalTail_bound
#print axioms Mahler.Adversarial.fractionalTail_recurrence
#print axioms Mahler.Adversarial.universalStream_contains
#print axioms Mahler.Adversarial.encoded_complexity_lower_bound
#print axioms Mahler.Adversarial.infinite_adversarial_witness
