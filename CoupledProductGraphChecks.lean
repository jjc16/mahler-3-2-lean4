import CoupledProductGraph

/-! Kernel-checked examples and axiom reports for CoupledProductGraph. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph

-- Exactly 5 residue classes mod 8 (`0, 1, 4, 5, 6`) survive 3 steps in G_{3, 6}.
example :
    (List.range 8).filter (fun res => residueSurvives 3 6 3 res) =
      [0, 1, 4, 5, 6] := by
  decide

-- Any integer congruent to 7 (mod 8), such as 15 or 23, is certified to have
-- no valid Mahler companion up to step 3 via G_{3, 6} pruning.
example : ¬ ∃ ξ : ℝ, ValidCompanionUpTo 15 ξ 3 :=
  mod_eight_2_3_7_excluded 15 (Or.inr (Or.inr (by decide)))

#print axioms Mahler.ProductGraph.step_mod_two_pow_dichotomy
#print axioms Mahler.ProductGraph.validBinStep_of_validCompanion
#print axioms Mahler.ProductGraph.coupledEdge_of_validCompanion_step
#print axioms Mahler.ProductGraph.stateSurvives_of_validCompanion_window
#print axioms Mahler.ProductGraph.residueSurvives_of_validCompanionUpTo
#print axioms Mahler.ProductGraph.no_validCompanionUpTo_of_residueSurvives_false
#print axioms Mahler.ProductGraph.g3_6_pruned_residues
#print axioms Mahler.ProductGraph.mod_eight_2_3_7_excluded
