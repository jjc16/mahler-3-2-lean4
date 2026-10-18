import TimeIndependentDeficiencySqueeze

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

#check @minSlackDeficiency
#check @minSlackDeficiency_two_ge
#check @minSlackDeficiency_step_drift_ge
#check @minSlackDeficiency_step_ge_of_le
#check @minSlackDeficiency_chain_ge_of_le
#check @aperiodic_minSlackDeficiency_squeeze
#check @time_independent_bounded_block_squeeze
#check @universal_two_run_step_bound
#check @six_step_ceiling_on_three_bounded_run
#check @post_two_four_step_ceiling_on_five_bounded_run

#print axioms minSlackDeficiency_two_ge
#print axioms minSlackDeficiency_step_drift_ge
#print axioms minSlackDeficiency_step_ge_of_le
#print axioms minSlackDeficiency_chain_ge_of_le
#print axioms aperiodic_minSlackDeficiency_squeeze
#print axioms time_independent_bounded_block_squeeze
#print axioms universal_two_run_step_bound
#print axioms six_step_ceiling_on_three_bounded_run
#print axioms post_two_four_step_ceiling_on_five_bounded_run
