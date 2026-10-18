import FormulationBJumpValuation

/-! Kernel-checked examples and axiom reports for FormulationBJumpValuation. -/

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

-- Example 1: At T(2) = 8, `r_2 = 9` has `orbit 9 8 = 243`, and `243 % 4 = 3`!
-- Therefore:
-- - Branch 1 (continuing from step 8 as an odd return with any `s(2) ≥ 2`):
--   `double_jump_of_return_mod_four_eq_three` forces a DOUBLE jump `9 + 2^9 = 521 ≤ a_0`.
-- - Branch 2 (using the odd quotient `q = 1`, `a_0 = 265 = 9 + 2^8`):
--   `odd_quotient_flips_return_to_even` proves `orbit 265 8 % 2 = 0` (flips step 8 to even!).
example :
    orbit 9 8 % 4 = 3 ∧
    orbit (2 ^ 8 * 1 + 9) 8 % 2 = 0 ∧
    orbit (2 ^ 8 * 2 + 9) 8 % 2 = 1 := by
  decide

-- Example 2: For `a_0 = 149`, after its first block `s(0) = 6` (`T(1) = 6`),
-- the minimal residue is `r_1 = 149 % 64 = 21`, with `orbit 21 6 = 243` (`243 % 4 = 3`),
-- so `jumpQuotient` to the second block (`s(1) = 4`) is `q_1 = 2`, jumping by `+2^7 = +128`
-- from `21` to `21 + 128 = 149`!
example :
    149 % 2 ^ 6 = 21 ∧
    orbit 21 6 % 4 = 3 ∧
    21 + 2 ^ (6 + 1) = 149 := by
  decide

#print axioms Mahler.JumpValuation.orbit_next_residue_at_return
#print axioms Mahler.JumpValuation.three_mul_orbit_next_residue_add_one
#print axioms Mahler.JumpValuation.jump_quotient_even
#print axioms Mahler.JumpValuation.odd_quotient_flips_return_to_even
#print axioms Mahler.JumpValuation.two_pow_dvd_jump_quotient_iff
#print axioms Mahler.JumpValuation.valuation_boosted_high_bit_jump
#print axioms Mahler.JumpValuation.double_jump_of_return_mod_four_eq_three
