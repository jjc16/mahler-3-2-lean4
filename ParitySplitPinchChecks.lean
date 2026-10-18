import ParitySplitPinch

/-! Kernel-checked examples and axiom reports for ParitySplitPinch. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch

-- Example 1: a = 4 and b = 20 have b - a = 16 = 2^4, so they share a length-4
-- parity block and split at step 4 (`2^4 ∣ 16` and `¬ (2^5 ∣ 16)`).
example : SameParityBlock 4 20 4 ∧ orbit 4 4 % 2 ≠ orbit 20 4 % 2 :=
  (first_split_iff_two_pow_dvd (a := 4) (b := 20) (L := 4) (by decide)).mpr
    ⟨by decide, by decide⟩

-- Their 4-step carry integers are identical (`carry 4 0 4 = carry 20 0 4 = 12`).
example : carry 4 0 4 = 12 ∧ carry 20 0 4 = 12 := by
  unfold carry
  decide

-- And because `6 * 12 + 2^5 = 72 + 32 = 104 < 243 = 3^5`, both pass the
-- tightened split-carry pinch at step 5!
example : 6 * carry 4 0 4 + 2 ^ 5 < 3 ^ 5 := by
  unfold carry
  decide

#print axioms Mahler.SplitPinch.carry_eq_of_sameParityBlock
#print axioms Mahler.SplitPinch.first_split_iff_two_pow_dvd
#print axioms Mahler.SplitPinch.fracPart_diff_of_sameParityBlock
#print axioms Mahler.SplitPinch.fracPart_initial_close_of_sameParityBlock
#print axioms Mahler.SplitPinch.first_split_straddles_one_third
#print axioms Mahler.SplitPinch.split_carry_tightened_pinch
#print axioms Mahler.SplitPinch.orbit_split_carry_tightened_pinch
