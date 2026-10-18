import FullStepSumValuation

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
open Mahler.TelescopingDuality
open Mahler.ConverseReconstruction
open Mahler.ExplicitCutoffs
open Mahler.DeficitAmplification
open Mahler.TwoVisitSeparation
open Mahler.MonotonicSeparation
open Mahler.CeilingModTraps
open Mahler.TwoAdicLTE
open Mahler.FullStepValuation

#check @oddGeomSum
#check @one_add_mul_oddGeomSum
#check @oddGeomSum_mod_two
#check @three_pow_two_pow_mul_eq_one_add
#check @three_pow_even_step_valuation
#check @odd_step_sum_u0_add_remainder_mod_four
#check @even_step_sum_u0_add_remainder_valuation
#check @cross_horizon_even_step_sum_valuation_lock

#print axioms one_add_mul_oddGeomSum
#print axioms oddGeomSum_mod_two
#print axioms three_pow_two_pow_mul_eq_one_add
#print axioms three_pow_even_step_valuation
#print axioms odd_step_sum_u0_add_remainder_mod_four
#print axioms even_step_sum_u0_add_remainder_valuation
#print axioms cross_horizon_even_step_sum_valuation_lock
