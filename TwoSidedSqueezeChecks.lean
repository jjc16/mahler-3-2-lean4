import TwoSidedSqueeze

/-! Kernel-checked examples and axiom reports for TwoSidedSqueeze. -/

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

-- Example 1: Along `(2, 6, 3, 3, 3)` (`c = 3` starting at `k = 2`),
-- `slackDeficiency` at `k = 2, 3, 4` equals `-27, -729, -19683` (`-3^3, -3^6, -3^9`),
-- matching `slackDeficiency_step` (`-27 * 27 = -729`, `-729 * 27 = -19683`)!
private def seq2_6_3s : ℕ → ℕ
  | 0 => 2
  | 1 => 6
  | _ => 3

example :
    slackDeficiency seq2_6_3s 3 2 = -27 ∧
    slackDeficiency seq2_6_3s 3 3 = -729 ∧
    slackDeficiency seq2_6_3s 3 4 = -19683 := by
  decide

-- Example 2: At `k = 2` (`T = 8`, `integerSlack = 217`), for `c = 2` (`3^2 - 2^2 = 5`),
-- `slackDeficiency seq2_6_3s 2 2 = 2^11 - 5 * 217 = 2048 - 1085 = +963 > 0` (sub-critical!),
-- so Squeeze 1 (`3^(2*m) * 963 < 2^(2*m + 11)`) fails already at `m = 1` (`9 * 963 = 8667 > 8192 = 2^13`),
-- immediately ruling out `s 2 = 2`!
example :
    slackDeficiency seq2_6_3s 2 2 = 963 ∧
    ¬ ((3 : ℤ) ^ (2 * 1) * slackDeficiency seq2_6_3s 2 2 <
        (2 : ℤ) ^ (2 * 1 + 2 + blockSteps seq2_6_3s 2 + 1)) := by
  decide

#print axioms Mahler.TwoSidedSqueeze.slackDeficiency_step
#print axioms Mahler.TwoSidedSqueeze.slackDeficiency_chain
#print axioms Mahler.TwoSidedSqueeze.archimedean_deficiency_conservation
#print axioms Mahler.TwoSidedSqueeze.archimedean_deficiency_squeeze
#print axioms Mahler.TwoSidedSqueeze.coupled_intermediate_repeat_squeeze
#print axioms Mahler.TwoSidedSqueeze.coasting_intermediate_repeat_squeeze
