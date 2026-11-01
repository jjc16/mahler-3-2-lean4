import GeneralizedDefectFactorizationAndAllRungDescent

/-!
# Verification Checks for `GeneralizedDefectFactorizationAndAllRungDescent`
-/

namespace Mahler.GeneralizedDefectAllRung.Checks

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

-- 1. Verify universal -72 * (3^(s-3) - 2^(s-3)) factorization on s = 4, 5, 6
-- At s = 4: E(4) = 9*16 - 8*27 = 144 - 216 = -72 = -72 * (3 - 2)
-- At s = 5: E(5) = 9*32 - 8*81 = 288 - 648 = -360 = -72 * (9 - 4)
-- At s = 6: E(6) = 9*64 - 8*243 = 576 - 1944 = -1368 = -72 * (27 - 8)
example :
    (8 * 3 ^ 3 - 9 * 2 ^ 4 = 72 * (3 ^ 1 - 2 ^ 1)) ∧
      (8 * 3 ^ 4 - 9 * 2 ^ 5 = 72 * (3 ^ 2 - 2 ^ 2)) ∧
      (8 * 3 ^ 5 - 9 * 2 ^ 6 = 72 * (3 ^ 3 - 2 ^ 3)) ∧
      Nat.Coprime (3 ^ 1 - 2 ^ 1) 6 ∧
      Nat.Coprime (3 ^ 2 - 2 ^ 2) 6 ∧
      Nat.Coprime (3 ^ 3 - 2 ^ 3) 6 := by
  decide

-- 2. Verify composite (2, s1) defect identity at s1 = 6:
-- 12 * 3^6 + 4 * (-1368) = 8748 - 5472 = +3276 = 36 * (27 + 64) = 36 * 91!
example :
    (12 * (3 : ℤ) ^ 6 + 4 * (-72 * ((3 : ℤ) ^ 3 - (2 : ℤ) ^ 3)) = 3276) ∧
      36 * ((3 : ℤ) ^ 3 + (2 : ℤ) ^ 6) = 3276 ∧
      Nat.Coprime (3 ^ 3 + 2 ^ 6) 6 := by
  decide

#check @defectError_eq_neg_seventy_two_mul
#check @three_pow_sub_two_pow_coprime_six
#check @post_defect_quotient_divisible_by_nine_and_normalized_recurrence
#check @general_s_ge_four_sparse_defect_strict_descent
#check @no_infinite_all_rung_sparse_defect_chain
#check @composite_defect_two_s1_identity_and_coprime_six
#check @recovery_pair_two_s1_deficitPotential_increase
#check @mod_three_valuation_incompatibility_s_ge_four_vs_two_pair
#check @two_adic_coincidence_law_and_mod_eight_lock
#check @p_adic_baker_yu_vs_archimedean_budget_comparison

#print axioms defectError_eq_neg_seventy_two_mul
#print axioms three_pow_sub_two_pow_coprime_six
#print axioms post_defect_quotient_divisible_by_nine_and_normalized_recurrence
#print axioms general_s_ge_four_sparse_defect_strict_descent
#print axioms no_infinite_all_rung_sparse_defect_chain
#print axioms composite_defect_two_s1_identity_and_coprime_six
#print axioms recovery_pair_two_s1_deficitPotential_increase
#print axioms mod_three_valuation_incompatibility_s_ge_four_vs_two_pair
#print axioms two_adic_coincidence_law_and_mod_eight_lock
#print axioms p_adic_baker_yu_vs_archimedean_budget_comparison

end Mahler.GeneralizedDefectAllRung.Checks
