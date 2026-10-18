import GlobalStepRateBounds

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
open Mahler.KernelDuality
open Mahler.Coasting
open Mahler.TwoSidedSqueeze
open Mahler.SharpenedSqueezes
open Mahler.AperiodicCocycle
open Mahler.MinSlackSystem
open Mahler.GlobalStepRate

#check @two_le_of_minSlack_pos
#check @six_le_after_two_of_minSlack_pos
#check @four_mul_minSlack_after_two_six_le
#check @three_le_after_two_six_of_minSlack_pos
#check @four_mul_minSlack_after_two_six_three_le
#check @three_le_after_two_six_three_of_minSlack_pos
#check @two_block_separation_after_two
#check @global_step_rate_disjunction
#check @three_mul_le_blockSteps_add_one
#check @surviving_orbit_three_mul_step_rate

#print axioms two_le_of_minSlack_pos
#print axioms six_le_after_two_of_minSlack_pos
#print axioms four_mul_minSlack_after_two_six_le
#print axioms three_le_after_two_six_of_minSlack_pos
#print axioms four_mul_minSlack_after_two_six_three_le
#print axioms three_le_after_two_six_three_of_minSlack_pos
#print axioms two_block_separation_after_two
#print axioms global_step_rate_disjunction
#print axioms three_mul_le_blockSteps_add_one
#print axioms surviving_orbit_three_mul_step_rate
