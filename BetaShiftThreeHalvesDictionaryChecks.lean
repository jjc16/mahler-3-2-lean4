import BetaShiftThreeHalvesDictionary

/-!
# Verification Checks for `BetaShiftThreeHalvesDictionary`
-/

namespace Mahler.BetaShiftDictionary.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection
open Mahler.BetaShiftDictionary

-- 1. Verify exact kneading sequence prefix and (2, 6, 3, 3, 2, 10, 7) block lengths
example :
    List.map kneadingDigit (List.range 27) =
      [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] ∧
    ((List.range 34).filter (fun n => decide (kneadingDigit n = 1)) =
      [0, 2, 8, 11, 14, 16, 26, 33]) ∧
    [2 - 0, 8 - 2, 11 - 8, 14 - 11, 16 - 14, 26 - 16, 33 - 26] = [2, 6, 3, 3, 2, 10, 7] :=
  kneading_prefix_27_and_blocks_2_6_3_3_2_10_7

-- 2. Verify concrete admissibleResidueFinset counts |G_N| ≥ (3/2)^N for N = 0, 1, 2, 3, 4
-- At N = 0: |G_0| = 1; N = 1: |G_1| = 2; N = 2: |G_2| = 3; N = 3: |G_3| = 5; N = 4: |G_4| = 8!
example :
    (admissibleResidueFinset 0).card = 1 ∧
      (admissibleResidueFinset 1).card = 2 ∧
      (admissibleResidueFinset 2).card = 3 ∧
      (admissibleResidueFinset 3).card = 5 ∧
      (admissibleResidueFinset 4).card = 8 := by
  decide

#check @fract_dynamics_conj_betaMap
#check @kneading_prefix_27_and_blocks_2_6_3_3_2_10_7
#check @parry_forbidden_prefixes_and_admissible_101000001
#check @three_halves_not_monic_integer_root
#check @survivesSteps_mod_two_pow_eq
#check @survivor_count_eq_admissible_card_mul_two_pow
#check @halfBetaStep_in_half_interval
#check @halfBetaStep_iterate_in_half_interval
#check @orbit_add_itinerary_mul_three_halves_pow
#check @two_pow_mul_admissible_card_ge_three_pow
#check @orbit_mod_two_pow_mem_admissibleResidueFinset_of_validCompanionForever
#check @periodic_itinerary_two_adic_seed_neg

#print axioms fract_dynamics_conj_betaMap
#print axioms kneading_prefix_27_and_blocks_2_6_3_3_2_10_7
#print axioms parry_forbidden_prefixes_and_admissible_101000001
#print axioms three_halves_not_monic_integer_root
#print axioms survivesSteps_mod_two_pow_eq
#print axioms survivor_count_eq_admissible_card_mul_two_pow
#print axioms halfBetaStep_in_half_interval
#print axioms halfBetaStep_iterate_in_half_interval
#print axioms orbit_add_itinerary_mul_three_halves_pow
#print axioms two_pow_mul_admissible_card_ge_three_pow
#print axioms orbit_mod_two_pow_mem_admissibleResidueFinset_of_validCompanionForever
#print axioms periodic_itinerary_two_adic_seed_neg

end Mahler.BetaShiftDictionary.Checks
