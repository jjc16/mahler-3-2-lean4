import SparseDefectCocycleAndValuationLock

/-!
# Verification Checks for `SparseDefectCocycleAndValuationLock`
-/

namespace Mahler.SparseDefectCocycle.Checks

open Mahler
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.SparseDefectCocycle

-- 1. Verify small values of the signed defect E(c) = 9 * 2^c - 8 * 3^(c-1)
example :
    defectTerm 1 = 10 ∧
      defectTerm 2 = 12 ∧
      defectTerm 3 = 0 ∧
      defectTerm 4 = -72 ∧
      defectTerm 5 = -360 :=
  defectTerm_small_values

-- 2. Verify exact 2-adic valuation v_2(E(c)) = 3 (8 | E(c) and ¬ 16 | E(c)) for all c ≥ 4
example {c : ℕ} (hc : 4 ≤ c) :
    (8 : ℤ) ∣ defectTerm c ∧ ¬ ((16 : ℤ) ∣ defectTerm c) :=
  ⟨(defectTerm_eq_eight_mul_odd_of_four_le hc).2.2.1,
    (defectTerm_eq_eight_mul_odd_of_four_le hc).2.2.2⟩

-- 3. Verify iterated multi-block signed defect cocycle
example {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m ≤ K) (hchain : ValidBlockChain a_0 s u K) :
    (2 : ℤ) ^ (blockSteps s m) * affInv (orbit a_0 (blockSteps s m)) =
      (3 : ℤ) ^ (blockSteps s m) * affInv a_0 + defectCocycleSum s m :=
  iterated_signed_defect_cocycle hmK hchain

-- 4. Verify 2-adic valuation non-cancellation & first-defect lock
example {a_0 : ℕ} {s u : ℕ → ℕ} {K j_0 m : ℕ}
    (hm1 : j_0 + 1 ≤ m) (hmK : m ≤ K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs3 : ∀ k < j_0, s k = 3) (hs_j0 : 4 ≤ s j_0) :
    2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) ∧
      ¬ (2 ^ (3 * j_0 + 4) ∣ (19 * a_0 + 9)) :=
  ⟨(first_defect_valuation_lock_and_non_cancellation hm1 hmK hchain hs3 hs_j0).1,
    (first_defect_valuation_lock_and_non_cancellation hm1 hmK hchain hs3 hs_j0).2.1⟩

-- 5. Verify explicit Finset.sum expansion of defectCocycleSum and short local prefix first-defect lock
example (s : ℕ → ℕ) (m : ℕ) :
    defectCocycleSum s m =
      ∑ j ∈ Finset.range m,
        (3 : ℤ) ^ (blockSteps s m - blockSteps s (j + 1)) *
          (2 : ℤ) ^ (blockSteps s j) * defectTerm (s j) :=
  defectCocycleSum_eq_finset_sum s m

example {a_0 : ℕ} {s u : ℕ → ℕ} {j_0 : ℕ}
    (hchain : ValidBlockChain a_0 s u (j_0 + 1))
    (hs3 : ∀ k < j_0, s k = 3) (hs_j0 : 4 ≤ s j_0) :
    2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) ∧
      ¬ (2 ^ (3 * j_0 + 4) ∣ (19 * a_0 + 9)) :=
  ⟨(local_prefix_first_defect_valuation_lock hchain hs3 hs_j0).2.1,
    (local_prefix_first_defect_valuation_lock hchain hs3 hs_j0).2.2⟩

#print axioms Mahler.SparseDefectCocycle.single_block_signed_defect_identity
#print axioms Mahler.SparseDefectCocycle.defectTerm_eq_eight_mul_odd_of_four_le
#print axioms Mahler.SparseDefectCocycle.defectCocycleSum_eq_finset_sum
#print axioms Mahler.SparseDefectCocycle.iterated_signed_defect_cocycle
#print axioms Mahler.SparseDefectCocycle.defectCocycleSum_mod_after_first_defect
#print axioms Mahler.SparseDefectCocycle.first_defect_valuation_lock_and_non_cancellation
#print axioms Mahler.SparseDefectCocycle.local_single_block_affInv_identity
#print axioms Mahler.SparseDefectCocycle.local_single_defect_valuation_three
#print axioms Mahler.SparseDefectCocycle.local_prefix_first_defect_valuation_lock
#print axioms Mahler.SparseDefectCocycle.defectCocycle_residual_eq_growing_boundary_affInv
#print axioms Mahler.SparseDefectCocycle.mahler_next_stage_research_synthesis

end Mahler.SparseDefectCocycle.Checks
