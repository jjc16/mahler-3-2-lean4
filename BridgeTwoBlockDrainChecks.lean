import BridgeTwoBlockDrain

/-! Kernel-checked examples and axiom reports for BridgeTwoBlockDrain. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo

-- Example 1: Partition boundaries for s = 2, 3, 4 match [13/27, 1/2), [35/81, 13/27), [97/243, 35/81).
example : windowLow 2 = 13 / 27 ∧ windowLow 3 = 35 / 81 ∧ windowLow 4 = 97 / 243 := by
  unfold windowLow
  norm_num

-- Example 2: Fixed point of s = 3 (`OEE`) is 9/19, and fixed point of s = 2 (`OE`) is 3/5.
example : blockFixedPoint 3 = 9 / 19 ∧ blockFixedPoint 2 = 3 / 5 := by
  unfold blockFixedPoint
  norm_num

-- Example 3: For s = 3 and a = 5 (`3*5 + 1 = 16 = 2^3 * 2`? No, a = 13 has `3*13 + 1 = 40 = 2^3 * 5`),
-- `orbit 13 3 = 45`, and `8 * (19 * 45 + 9) = 6912 = 27 * (19 * 13 + 9)`.
example :
    2 ^ 3 * ((3 ^ 3 - 2 ^ 3) * orbit 13 3 + 3 ^ 2) =
      3 ^ 3 * ((3 ^ 3 - 2 ^ 3) * 13 + 3 ^ 2) :=
  odd_block_integer_fixed_point (a := 13) (s := 3) (u := 5) (by decide) (by decide)

#print axioms Mahler.BridgeTwo.windowLow_strictAnti
#print axioms Mahler.BridgeTwo.windowUpper_eq_windowLow_pred
#print axioms Mahler.BridgeTwo.odd_block_admissible_window
#print axioms Mahler.BridgeTwo.s_eq_one_impossible
#print axioms Mahler.BridgeTwo.s_eq_two_forces_next_block_ge_six
#print axioms Mahler.BridgeTwo.odd_block_fracPart_fixed_point
#print axioms Mahler.BridgeTwo.odd_block_integer_fixed_point
#print axioms Mahler.BridgeTwo.odd_block_repeat_bound
