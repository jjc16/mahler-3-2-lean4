import CoprimeUnitRigidity

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
open Mahler.RemainderAdditionLaw
open Mahler.TwoAdicCauchy
open Mahler.AllHistoryRecovery
open Mahler.ParametricCorridor
open Mahler.AperiodicBoundedSqueeze
open Mahler.TimeIndependentSqueeze
open Mahler.SlackDeadEnds
open Mahler.GrandSynthesis
open Mahler.Mod256Sieve
open Mahler.UnitRigidity

#check @u_coprime_six_of_validBlockChain
#check @three_pow_add_one_mod_eight
#check @three_pow_add_one_not_dvd_eight
#check @u_eq_one_forces_next_block_le_two
#check @ceiling_saturated_five_le_u
#check @coasting_five_mul_single_block_bound
#check @seven_mul_u_next_le_of_s_eq_two
#check @hundred_thirteen_mul_u_next_le_of_s_eq_two_ten

#print axioms u_coprime_six_of_validBlockChain
#print axioms three_pow_add_one_mod_eight
#print axioms three_pow_add_one_not_dvd_eight
#print axioms u_eq_one_forces_next_block_le_two
#print axioms ceiling_saturated_five_le_u
#print axioms coasting_five_mul_single_block_bound
#print axioms seven_mul_u_next_le_of_s_eq_two
#print axioms hundred_thirteen_mul_u_next_le_of_s_eq_two_ten
