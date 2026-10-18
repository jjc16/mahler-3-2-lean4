import BridgeThreeMixedBlocks

/-! Kernel-checked examples and axiom reports for BridgeThreeMixedBlocks. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree

-- Example 1: For the 2-block sequence `s = (2, 5)` (`OEOEEEEO`),
-- `blockSteps = 7` and `blockKernel = 1053` (which is odd),
-- and `6 * 1053 + 2^8 = 6574 > 6561 = 3^8`, so `mixed_block_return_pinch`
-- immediately certifies that NO starting integer can realize `(2, 5)` and survive!
def seq2_5 : ℕ → ℕ
  | 0 => 2
  | 1 => 5
  | _ => 2

example : blockSteps seq2_5 2 = 7 ∧ blockKernel seq2_5 2 = 1053 := by
  decide

example : ¬ (6 * blockKernel seq2_5 2 + 2 ^ (blockSteps seq2_5 2 + 1) <
    3 ^ (blockSteps seq2_5 2 + 1)) := by
  decide

-- Whereas for `s = (2, 6)` (`OEOEEEEEO`, realized by `a_0 = 9`),
-- `blockSteps = 8`, `blockKernel = 3159`, and `6 * 3159 + 2^9 = 19466 < 19683 = 3^9`!
def seq2_6 : ℕ → ℕ
  | 0 => 2
  | 1 => 6
  | _ => 2

example :
    blockSteps seq2_6 2 = 8 ∧
    blockKernel seq2_6 2 = 3159 ∧
    6 * blockKernel seq2_6 2 + 2 ^ (blockSteps seq2_6 2 + 1) <
      3 ^ (blockSteps seq2_6 2 + 1) ∧
    2 ^ 8 ∣ (3 ^ 8 * 9 + blockKernel seq2_6 2) := by
  decide

#print axioms Mahler.BridgeThree.blockKernel_odd
#print axioms Mahler.BridgeThree.mixed_block_integer_identity
#print axioms Mahler.BridgeThree.blockKernel_eq_carry
#print axioms Mahler.BridgeThree.mixed_block_fracPart_identity
#print axioms Mahler.BridgeThree.mixed_block_return_pinch
#print axioms Mahler.BridgeThree.mixed_block_cross_return_squeeze
#print axioms Mahler.BridgeThree.mixed_cycle_fixed_point
#print axioms Mahler.BridgeThree.mixed_cycle_repeat_bound
