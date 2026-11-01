import ParitySurplusPotentialsAndSafetyGame

/-!
# Verification Checks for `ParitySurplusPotentialsAndSafetyGame`
-/

namespace Mahler.ParitySurplusAndGames.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames

-- 1. Verify universal shift-submultiplicativity of signedMargin
example (ε : ℕ → ℕ) (k m : ℕ) :
    signedMargin ε (k + m) ≤ (2 : ℤ) ^ k * signedMargin (shiftStream ε k) m :=
  signedMargin_add_le_two_pow_mul_shift ε k m

-- 2. Verify look-ahead-free finite odd-count bound on signedMargin and seeds
example (N : ℕ) (ε : ℕ → ℕ) (hpos : 0 < signedMargin ε N) :
    3 * oddParityCount ε N ≤ N + 3 :=
  three_mul_oddParityCount_le_add_three_of_signedMargin_pos N ε hpos

example {a_0 : ℕ} {α : ℝ} (hforever : ValidCompanionForever a_0 α) (N : ℕ) :
    3 * oddCount a_0 N ≤ N + 3 :=
  three_mul_oddCount_le_add_three_of_validCompanionForever hforever N

-- 3. Verify Phase C3 concrete finite parity-surplus and mod-4 checks on seeds 1, 8, and 149
-- Seed 1: orbit 1 = [1, 2, 3, 5, 8, ...]; at n = 2, orbit 1 2 = 3 ≡ 3 (mod 4)!
-- Seed 8: orbit 8 = [8, 12, 18, 27, ...]; at n = 3, orbit 8 3 = 27 ≡ 3 (mod 4)!
-- Seed 149: survives 28 steps and fails at 29; satisfies 3 * oddCount 149 28 ≤ 28 + 3 = 31.
example :
    orbit 1 2 % 4 = 3 ∧
      orbit 8 3 % 4 = 3 ∧
      3 * oddCount 1 4 > 4 + 3 ∧
      3 * oddCount 149 28 ≤ 28 + 3 := by
  decide

#check @signedMargin_add_le_two_pow_mul_shift
#check @signedMargin_shift_pos_of_add_pos
#check @signedMargin_add_eq_two_pow_mul_shift_of_ceiling
#check @signedMargin_post_101_five_zeros_lock
#check @three_mul_oddParityCount_le_add_three_of_signedMargin_pos
#check @three_mul_oddCount_le_add_three_of_validCompanionUpTo
#check @three_mul_oddCount_le_add_three_of_validCompanionForever
#check @two_pow_dvd_of_oddCount_eq_zero
#check @exists_odd_orbit_step_of_pos
#check @mahler_conjecture_of_forall_pos_seed_parity_surplus
#check @mahler_conjecture_of_forall_pos_seed_hits_three_mod_four
#check @deficitPotential_nonneg_of_signedMargin_pos
#check @deficitPotential_indifference_on_100_and_increase_on_1000
#check @linear_coupled_margin_deficit_stationary_on_100_cycle
#check @stabilized_seed_100_two_adic_valuation_drop
#check @mem_survivorKernel_iff_forall_validCompanionUpTo
#check @safety_game_kernel_and_rank_completeness

#print axioms signedMargin_add_le_two_pow_mul_shift
#print axioms signedMargin_shift_pos_of_add_pos
#print axioms signedMargin_add_eq_two_pow_mul_shift_of_ceiling
#print axioms signedMargin_post_101_five_zeros_lock
#print axioms three_mul_oddParityCount_le_add_three_of_signedMargin_pos
#print axioms three_mul_oddCount_le_add_three_of_validCompanionUpTo
#print axioms three_mul_oddCount_le_add_three_of_validCompanionForever
#print axioms two_pow_dvd_of_oddCount_eq_zero
#print axioms exists_odd_orbit_step_of_pos
#print axioms mahler_conjecture_of_forall_pos_seed_parity_surplus
#print axioms mahler_conjecture_of_forall_pos_seed_hits_three_mod_four
#print axioms deficitPotential_nonneg_of_signedMargin_pos
#print axioms deficitPotential_indifference_on_100_and_increase_on_1000
#print axioms linear_coupled_margin_deficit_stationary_on_100_cycle
#print axioms stabilized_seed_100_two_adic_valuation_drop
#print axioms mem_survivorKernel_iff_forall_validCompanionUpTo
#print axioms safety_game_kernel_and_rank_completeness

end Mahler.ParitySurplusAndGames.Checks
