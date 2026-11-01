import BaseSixMultiplicationAutomaton

/-!
# Verification Checks for `BaseSixMultiplicationAutomaton`
-/

namespace Mahler.BaseSixAutomaton.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.BaseSixAutomaton

-- 1. Verify digit-range preservation and radius-1 local rule
example {d : ℤ → ℕ} (hd : IsBaseSixConfig d) (n : ℕ) :
    IsBaseSixConfig (mulThreeHalvesCA^[n] d) :=
  isBaseSixConfig_iterate_mulThreeHalvesCA hd n

-- 2. Verify exact integer and rational value homomorphism on a concrete configuration (`8 = 12_6`)
example :
    baseSixScaledNat (natToBaseSixConfig 8) 0 2 = 8 ∧
      baseSixScaledNat (mulThreeHalvesCA (natToBaseSixConfig 8)) (-1) 4 = 72 ∧
      baseSixWindowVal (natToBaseSixConfig 8) 0 2 = 8 ∧
      baseSixWindowVal (mulThreeHalvesCA (natToBaseSixConfig 8)) (-1) 4 = 12 := by
  have h1 : baseSixScaledNat (natToBaseSixConfig 8) 0 2 = 8 := by decide
  have h2 : baseSixScaledNat (mulThreeHalvesCA (natToBaseSixConfig 8)) (-1) 4 = 72 := by decide
  refine ⟨h1, h2, ?_, ?_⟩ <;> norm_num [baseSixWindowVal, h1, h2]

-- 3. Verify space-time trace escapes for seeds 1 and 8
example :
    (mulThreeHalvesCA^[0] (natToBaseSixConfig 1)) (-1) = 0 ∧
      (mulThreeHalvesCA^[1] (natToBaseSixConfig 1)) (-1) = 3 ∧
      (mulThreeHalvesCA^[0] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[1] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[2] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[3] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[4] (natToBaseSixConfig 8)) (-1) = 3 ∧
      (mulThreeHalvesCA^[5] (natToBaseSixConfig 8)) (-1) = 4 :=
  seed_one_and_eight_base_six_trace_escape

#check @isBaseSixConfig_mulThreeCA
#check @isBaseSixConfig_mulThreeHalvesCA
#check @isBaseSixConfig_iterate_mulThreeHalvesCA
#check @mulThreeHalvesCA_eq_local_rule
#check @mulThreeHalvesCA_local_congr
#check @mulThreeHalvesCA_iterate_causal_cone_congr
#check @baseSixScaledNat_mulThreeCA_flux
#check @baseSixScaledNat_mulThreeCA_eq
#check @baseSixScaledNat_mulThreeHalvesCA_eq
#check @baseSixWindowVal_mulThreeHalvesCA
#check @fract_lt_half_iff_digit_neg_one_lt_three
#check @noncanonical_tail_endpoint_counterexample
#check @left_zero_boundary_mulThreeHalvesCA
#check @left_zero_boundary_mulThreeHalvesCA_iterate
#check @seed_one_and_eight_base_six_trace_escape
#check @zero_and_two_adic_ghost_trace_obstruction

#print axioms isBaseSixConfig_mulThreeCA
#print axioms isBaseSixConfig_mulThreeHalvesCA
#print axioms isBaseSixConfig_iterate_mulThreeHalvesCA
#print axioms mulThreeHalvesCA_eq_local_rule
#print axioms mulThreeHalvesCA_local_congr
#print axioms mulThreeHalvesCA_iterate_causal_cone_congr
#print axioms baseSixScaledNat_mulThreeCA_flux
#print axioms baseSixScaledNat_mulThreeCA_eq
#print axioms baseSixScaledNat_mulThreeHalvesCA_eq
#print axioms baseSixWindowVal_mulThreeHalvesCA
#print axioms fract_lt_half_iff_digit_neg_one_lt_three
#print axioms noncanonical_tail_endpoint_counterexample
#print axioms left_zero_boundary_mulThreeHalvesCA
#print axioms left_zero_boundary_mulThreeHalvesCA_iterate
#print axioms seed_one_and_eight_base_six_trace_escape
#print axioms zero_and_two_adic_ghost_trace_obstruction

end Mahler.BaseSixAutomaton.Checks
