import SolenoidRigidityDiscrepancyAndRenormalization

/-!
# Verification Checks for `SolenoidRigidityDiscrepancyAndRenormalization`
-/

namespace Mahler.SolenoidDiscrepancyAndRenorm.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.BaseSixAutomaton
open Mahler.TransferJSRAndFourier
open Mahler.SolenoidDiscrepancyAndRenorm

-- 1. Verify single-generator ×(3/2) orbit is neither ×2- nor ×3-invariant
example {x_0 : ℝ} (hx0 : 0 < x_0) :
    2 * x_0 ∉ orbitSetThreeHalves x_0 ∧ 3 * x_0 ∉ orbitSetThreeHalves x_0 :=
  ⟨(single_generator_orbit_not_two_or_three_invariant hx0).2.1,
    (single_generator_orbit_not_two_or_three_invariant hx0).2.2⟩

-- 2. Verify discrepancy-to-escape and Erdős–Turán reduction
example (α : ℝ) {N : ℕ} (hN : 1 ≤ N) (hlt : halfIntervalDiscrepancy α N < (1 / 2 : ℝ)) :
    1 ≤ upperHalfCount α N ∧
      ∃ n < N, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n) :=
  (discrepancy_lt_half_forces_mahler_escape α hN).2 hlt

-- 3. Verify dyadic uniqueness witness 149 and renormalization mismatch
example :
    128 ≤ 149 ∧ 149 < 256 ∧
      fastSeedSurvives 149 28 = true ∧
      fastSeedSurvives 149 29 = false :=
  ⟨single_dyadic_survivor_witness_149.1, single_dyadic_survivor_witness_149.2.1,
    single_dyadic_survivor_witness_149.2.2.1, single_dyadic_survivor_witness_149.2.2.2.1⟩

#check @three_pow_ne_two_pow_succ_and_three_mul_two_pow
#check @single_generator_orbit_not_two_or_three_invariant
#check @finite_horizon_confinement_not_two_or_three_invariant
#check @lowerHalfCount_add_upperHalfCount_eq
#check @discrepancy_lt_half_forces_mahler_escape
#check @erdos_turan_conditional_mahler_reduction
#check @distinct_dyadic_seeds_cannot_share_prefix_past_W
#check @single_dyadic_survivor_witness_149
#check @mahler_method_irrational_value_excludes_integer_seed
#check @first_return_two_adic_defect_and_multiplier_mismatch

#print axioms three_pow_ne_two_pow_succ_and_three_mul_two_pow
#print axioms single_generator_orbit_not_two_or_three_invariant
#print axioms finite_horizon_confinement_not_two_or_three_invariant
#print axioms lowerHalfCount_add_upperHalfCount_eq
#print axioms discrepancy_lt_half_forces_mahler_escape
#print axioms erdos_turan_conditional_mahler_reduction
#print axioms distinct_dyadic_seeds_cannot_share_prefix_past_W
#print axioms single_dyadic_survivor_witness_149
#print axioms mahler_method_irrational_value_excludes_integer_seed
#print axioms first_return_two_adic_defect_and_multiplier_mismatch

end Mahler.SolenoidDiscrepancyAndRenorm.Checks
