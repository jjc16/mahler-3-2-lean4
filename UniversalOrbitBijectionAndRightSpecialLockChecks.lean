import UniversalOrbitBijectionAndRightSpecialLock

/-!
# Verification Checks for `UniversalOrbitBijectionAndRightSpecialLock`
-/

namespace Mahler.UniversalOrbitBijection.Checks

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

-- 1. Verify universal forward 2^m / backward 3^m orbit bijection
example (a_0 n₁ n₂ m : ℕ) :
    (orbit a_0 n₁ % 2 ^ m = orbit a_0 n₂ % 2 ^ m ↔
      ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ∧
    ((∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ↔
      orbit a_0 (n₁ + m) % 3 ^ m = orbit a_0 (n₂ + m) % 3 ^ m) :=
  orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₂ m

-- 2. Verify concrete mod-3 valuation trichotomy on b = 1 (`s = 2`, `19*1+9 = 28 = 4 * 7`),
-- b = 3 (`s = 1`, `19*3+9 = 66 = 2 * 33`), b = 5 (`s = 4`, `19*5+9 = 104 = 8 * 13`),
-- and b = 13 (`s = 3`, `19*13+9 = 256 = 16 * 16`)
example :
    (3 * 1 + 1 = 4 * 1 ∧ (19 * 1 + 9) % 4 = 0 ∧ (19 * 1 + 9) % 8 ≠ 0) ∧
      (3 * 3 + 1 = 2 * 5 ∧ (19 * 3 + 9) % 2 = 0 ∧ (19 * 3 + 9) % 4 ≠ 0) ∧
      (3 * 5 + 1 = 16 * 1 ∧ (19 * 5 + 9) % 8 = 0 ∧ (19 * 5 + 9) % 16 ≠ 0) ∧
      (3 * 13 + 1 = 8 * 5 ∧ (19 * 13 + 9) % 16 = 0) := by
  decide

#check @lt_step_and_two_mul_step_add_one_le
#check @orbit_strictMono_of_pos
#check @orbit_add_eq
#check @two_pow_mul_orbit_add_eq
#check @orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow
#check @right_special_orbit_exact_two_and_three_adic_lock
#check @three_occurrence_raw_orbit_two_pow_add_one_dvd
#check @raw_orbit_repeated_parity_window_pq_cutoff
#check @raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds
#check @three_mul_affInv_eq_nineteen_mul_add_eight
#check @two_adic_valuation_affInv_trichotomy
#check @epoch_period_three_run_exit_trichotomy

#print axioms lt_step_and_two_mul_step_add_one_le
#print axioms orbit_strictMono_of_pos
#print axioms orbit_add_eq
#print axioms two_pow_mul_orbit_add_eq
#print axioms orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow
#print axioms right_special_orbit_exact_two_and_three_adic_lock
#print axioms three_occurrence_raw_orbit_two_pow_add_one_dvd
#print axioms raw_orbit_repeated_parity_window_pq_cutoff
#print axioms raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds
#print axioms three_mul_affInv_eq_nineteen_mul_add_eight
#print axioms two_adic_valuation_affInv_trichotomy
#print axioms epoch_period_three_run_exit_trichotomy

end Mahler.UniversalOrbitBijection.Checks
