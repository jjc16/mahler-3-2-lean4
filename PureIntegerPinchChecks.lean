import PureIntegerPinch

/-! Kernel-checked examples and axiom reports for PureIntegerPinch. -/

open Mahler
open Mahler.Pinch

-- m = 1 survives up to N = 3 (with witness ξ = lowerBound 1 3 = 40/27),
-- and fails at N = 4 where the backward floor jumps from 2*a_2 = 6 to 7 (odd).
example : IntegerPinch 1 0 3 ∧ IntegerPinch 1 1 2 ∧ IntegerPinch 1 2 1 ∧ IntegerPinch 1 3 0 := by
  unfold IntegerPinch
  decide

example : ¬ IntegerPinch 1 2 2 := by
  unfold IntegerPinch
  decide

example : (2 ^ 3 * orbit 1 (2 + 2)) / 3 ^ 2 = 2 * orbit 1 2 + 1 :=
  first_failure_floor_eq_two_mul_add_one
    (by unfold IntegerPinch; decide)
    (by unfold IntegerPinch; decide)

-- m = 4 survives 11 steps and fails at step 12 against j = 10 (k = 2).
example : IntegerPinch 4 10 1 ∧ ¬ IntegerPinch 4 10 2 := by
  unfold IntegerPinch
  decide

#print axioms Mahler.Pinch.three_pow_mul_orbit_le
#print axioms Mahler.Pinch.integerPinch_iff_two_mul_carry_lt
#print axioms Mahler.Pinch.integerPinch_iff_floor_eq_two_mul
#print axioms Mahler.Pinch.first_failure_floor_eq_two_mul_add_one
#print axioms Mahler.Pinch.integerPinch_iff_div_and_mod_three_pow
#print axioms Mahler.Pinch.lowerBound_mono
#print axioms Mahler.Pinch.upperBound_step_diff
#print axioms Mahler.Pinch.lowerBound_lt_upperBound_iff_integerPinch
#print axioms Mahler.Pinch.exists_validCompanionUpTo_iff_integerPinch
