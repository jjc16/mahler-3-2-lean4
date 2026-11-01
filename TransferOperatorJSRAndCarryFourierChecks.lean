import TransferOperatorJSRAndCarryFourier

/-!
# Verification Checks for `TransferOperatorJSRAndCarryFourier`
-/

namespace Mahler.TransferJSRAndFourier.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier

-- 1. Verify Perron-Frobenius-free sub-invariant weight bound
example {r : ℕ} (M : Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ) (ρ : ℚ)
    (hM : ∀ i j : Fin r, 0 ≤ M i j) (hρ : 0 ≤ ρ)
    (hsub : ∀ i : Fin r, (∑ j : Fin r, M i j * w j) ≤ ρ * w i) (n : ℕ) :
    (∀ i : Fin r, iterTransferWeight M w n i ≤ ρ ^ n * w i) ∧
      (∀ i : Fin r, (∑ j : Fin r, (M ^ n) i j * w j) ≤ ρ ^ n * w i) :=
  subinvariant_weight_matrix_pow_bound M w ρ hM hρ hsub n

-- 2. Verify 3-adic carry memory erasure and word-to-carry injectivity on concrete 3-bit words
-- The 8 binary words of length 3 map bijectively to 8 distinct residues modulo 3^3 = 27!
example :
    wordCarry (fun _ => 0) 3 % 27 = 0 ∧
      wordCarry (fun n => if n = 0 then 1 else 0) 3 % 27 = 9 ∧
      wordCarry (fun n => if n = 1 then 1 else 0) 3 % 27 = 6 ∧
      wordCarry (fun n => if n = 2 then 1 else 0) 3 % 27 = 4 := by
  decide

#check @iterTransferWeight_eq_matrix_pow_sum
#check @subinvariant_weight_matrix_pow_bound
#check @common_subinvariant_weight_jsr_bound
#check @no_subcritical_weight_of_self_loop
#check @no_subcritical_weight_of_three_cycle
#check @archimedean_only_density_fallacy_supercritical
#check @mod_two_pow_ghost_self_loop_at_all_depths
#check @wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift
#check @wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod
#check @wordCarry_mod_three_pow_eq_iff_parity_eq
#check @aligned_carry_collision_iff_exact_factor_match

#print axioms iterTransferWeight_eq_matrix_pow_sum
#print axioms subinvariant_weight_matrix_pow_bound
#print axioms common_subinvariant_weight_jsr_bound
#print axioms no_subcritical_weight_of_self_loop
#print axioms no_subcritical_weight_of_three_cycle
#print axioms archimedean_only_density_fallacy_supercritical
#print axioms mod_two_pow_ghost_self_loop_at_all_depths
#print axioms wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift
#print axioms wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod
#print axioms wordCarry_mod_three_pow_eq_iff_parity_eq
#print axioms aligned_carry_collision_iff_exact_factor_match

end Mahler.TransferJSRAndFourier.Checks
