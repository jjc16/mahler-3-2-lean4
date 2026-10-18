import ShiftInvariantSlack

/-! Kernel-checked examples and axiom reports for ShiftInvariantSlack. -/

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
open Mahler.EscapeBranchCap
open Mahler.PhaseLock
open Mahler.MasterReduction
open Mahler.ModEightClassifier
open Mahler.CoprimeSlack
open Mahler.ShiftSlack

-- Example 1: Verify the integer slack sequence `Δ_1 = 601, Δ_2 = 46633, Δ_3 = 3744505, Δ_4 = 24559308697`
-- on the 28-step survivor `a_0 = 149` (`s = [6, 4, 4, 8, 5]`):
private def s149 : ℕ → ℕ
  | 0 => 6 | 1 => 4 | 2 => 4 | 3 => 8 | 4 => 5 | _ => 1

example :
    integerSlack s149 1 = 601 ∧
    integerSlack s149 2 = 46633 ∧
    integerSlack s149 3 = 3744505 ∧
    integerSlack s149 4 = 24559308697 := by
  decide

#print axioms Mahler.ShiftSlack.integerSlack_succ
#print axioms Mahler.ShiftSlack.integerSlack_eq_orbit_slack
#print axioms Mahler.ShiftSlack.validBlockChain_shift
#print axioms Mahler.ShiftSlack.shift_invariant_tail_budget
#print axioms Mahler.ShiftSlack.shift_invariant_integerSlack_pos
#print axioms Mahler.ShiftSlack.no_companion_of_subword_2_6_2
#print axioms Mahler.ShiftSlack.no_companion_of_subword_2_6_3_2
