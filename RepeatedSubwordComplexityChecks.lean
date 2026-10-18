import RepeatedSubwordComplexity

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
open Mahler.DeterminantCollapse
open Mahler.BakerMatveev
open Mahler.RidoutSubspace
open Mahler.MultiOriginSyzygy
open Mahler.SubwordComplexity

#check @blockSteps_congr
#check @tailSteps_congr
#check @coprimeRemainder_congr
#check @integerSlack_congr
#check @validBlockChain_a0_pos
#check @orbit_blockSteps_strict_mono
#check @u_lt_of_lt_of_eq_block
#check @repeated_subword_quotient_diff_eq
#check @repeated_subword_simultaneous_divisibility
#check @repeated_subword_exponential_barrier
#check @repeated_subword_linear_step_cutoff
#check @repeated_subword_block_count_bound
#check @repeated_subword_common_even_multiplier
#check @sharpened_repeated_subword_linear_cutoff

#print axioms blockSteps_congr
#print axioms tailSteps_congr
#print axioms coprimeRemainder_congr
#print axioms integerSlack_congr
#print axioms validBlockChain_a0_pos
#print axioms orbit_blockSteps_strict_mono
#print axioms u_lt_of_lt_of_eq_block
#print axioms repeated_subword_quotient_diff_eq
#print axioms repeated_subword_simultaneous_divisibility
#print axioms repeated_subword_exponential_barrier
#print axioms repeated_subword_linear_step_cutoff
#print axioms repeated_subword_block_count_bound
#print axioms repeated_subword_common_even_multiplier
#print axioms sharpened_repeated_subword_linear_cutoff
