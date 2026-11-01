import BoundedOddPartAndThreeAdicSieve

/-!
# Verification Checks for `BoundedOddPartAndThreeAdicSieve`
-/

namespace Mahler.BoundedOddPartAndSieve.Checks

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
open Mahler.GeneralizedDefectAllRung
open Mahler.BaseSixAutomaton
open Mahler.BoundedOddPartAndSieve

-- 1. Verify golden-ratio subsum interval overlap at r = 2/3
example :
    let r : ℚ := 2 / 3
    let S_max : ℚ := 1 / (1 - r ^ 2)
    r ^ 2 + r = (10 / 9 : ℚ) ∧
      1 < r ^ 2 + r ∧
      S_max = (9 / 5 : ℚ) ∧
      r * S_max = (6 / 5 : ℚ) ∧
      1 + r ^ 2 * S_max = S_max ∧
      1 < r * S_max ∧
      r * S_max - 1 = (1 / 5 : ℚ) :=
  no_eleven_subsum_interval_overlap_at_two_thirds

-- 2. Verify mod-3 and mod-9 backward sieve on concrete orbits
example (a_0 : ℕ) :
    orbit a_0 1 % 3 ≠ 1 ∧
      (orbit a_0 2 % 9 = 8 ↔ (orbit a_0 0 % 2 = 1 ∧ orbit a_0 1 % 2 = 1)) :=
  ⟨orbit_mod_three_ne_one a_0 (by decide : 1 ≤ 1),
    (orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd a_0 0).1⟩

#check @four_term_sunit_epoch_equation_no_vanishing_subsum
#check @bounded_odd_part_iff_runs_saturate_budget
#check @strictMono_boundaries_injective_on_j_and_V
#check @no_simultaneously_bounded_j_and_V_along_strictMono_boundaries
#check @no_bounded_odd_part_orbit_of_sunit_finiteness
#check @step_mod_three_ne_one
#check @orbit_mod_three_ne_one
#check @orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd
#check @orbit_mod_six_pow_eq_iff_surrounding_window_parity_eq
#check @not_validCompanionUpTo_of_zero_offset
#check @fract_lt_half_iff_floor_two_mul_even
#check @minimal_z_floor_not_dvd_three
#check @no_eleven_subsum_interval_overlap_at_two_thirds
#check @monotone_complexity_telescope_sum
#check @sigma1_bounded_box_escape_of_survivesSteps_false
#check @pi2_unbounded_lower_bound_iff_mahler
#check @raw_orbit_multi_collision_ultrametric_pq_cutoff
#check @baseSixScaledNat_natToBaseSixConfig_eq

#print axioms four_term_sunit_epoch_equation_no_vanishing_subsum
#print axioms bounded_odd_part_iff_runs_saturate_budget
#print axioms strictMono_boundaries_injective_on_j_and_V
#print axioms no_simultaneously_bounded_j_and_V_along_strictMono_boundaries
#print axioms no_bounded_odd_part_orbit_of_sunit_finiteness
#print axioms step_mod_three_ne_one
#print axioms orbit_mod_three_ne_one
#print axioms orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd
#print axioms orbit_mod_six_pow_eq_iff_surrounding_window_parity_eq
#print axioms not_validCompanionUpTo_of_zero_offset
#print axioms fract_lt_half_iff_floor_two_mul_even
#print axioms minimal_z_floor_not_dvd_three
#print axioms no_eleven_subsum_interval_overlap_at_two_thirds
#print axioms monotone_complexity_telescope_sum
#print axioms sigma1_bounded_box_escape_of_survivesSteps_false
#print axioms pi2_unbounded_lower_bound_iff_mahler
#print axioms raw_orbit_multi_collision_ultrametric_pq_cutoff
#print axioms baseSixScaledNat_natToBaseSixConfig_eq

end Mahler.BoundedOddPartAndSieve.Checks
