import CeilingSaturationSynthesis

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
open Mahler.BaseTwoLock
open Mahler.CeilingSynthesis

#check @three_mul_two_pow_le_three_pow
#check @minSlack_eq_two_pow_of_three_le
#check @all_shifted_slacks_pos_of_three_le
#check @ceiling_saturated_chain_iff_mod_eight
#check @two_step_ceiling_saturated_dvd
#check @three_step_compound_coprime_identity
#check @three_step_ceiling_saturated_dvd
#check @mahler_complete_48_module_synthesis

#print axioms three_mul_two_pow_le_three_pow
#print axioms minSlack_eq_two_pow_of_three_le
#print axioms all_shifted_slacks_pos_of_three_le
#print axioms ceiling_saturated_chain_iff_mod_eight
#print axioms two_step_ceiling_saturated_dvd
#print axioms three_step_compound_coprime_identity
#print axioms three_step_ceiling_saturated_dvd
#print axioms mahler_complete_48_module_synthesis
