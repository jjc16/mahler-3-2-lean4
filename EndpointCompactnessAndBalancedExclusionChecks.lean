import EndpointCompactnessAndBalancedExclusion

/-!
# Verification Checks for `EndpointCompactnessAndBalancedExclusion`
-/

namespace Mahler.EndpointAndBalancedExclusion.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeOne
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion

-- 1. Verify the perpetual finite feasibility endpoint alternative
example {a_0 : ℕ} (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) :
    ValidCompanionForever a_0 (supCompanion a_0) ∨
      ∃ j : ℕ,
        supCompanion a_0 = upperBound a_0 j ∧
          ValidCompanionForever (orbit a_0 (j + 1))
            (supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1)) :=
  perpetual_finite_survival_endpoint_alternative hperp

-- 2. Verify high-precision rational convergents `3^q < 2^(p+q)` to log_2(3/2)
example :
    3 ^ 5 < 2 ^ (3 + 5) ∧
      3 ^ 17 < 2 ^ (10 + 17) ∧
      3 ^ 46 < 2 ^ (27 + 46) ∧
      3 ^ 99 < 2 ^ (58 + 99) :=
  high_precision_rational_log_convergents

-- 3. Verify standard prefix factor complexity pigeonhole theorem
example (s : ℕ → ℕ) (L C : ℕ) (hcard : prefixFactorCount s L C ≤ C) :
    ∃ r1 r2 : ℕ, r1 < r2 ∧ r2 ≤ C ∧ ∀ i < L, s (r1 + i) = s (r2 + i) :=
  exists_repeated_subword_of_prefixFactorCount_le s L C hcard

-- 4. Verify bounded cumulative discrepancy of arbitrary two-letter mechanical sequences
example {a b : ℕ} {α ρ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    |(blockSteps (mechTwoLetterSeq a b α ρ) n : ℝ) -
        ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) * (n : ℝ)| ≤
      ((b - a : ℕ) : ℝ) :=
  mechTwoLetterSeq_balanced_discrepancy hα0 hα1 n

-- 5. Verify derived mechanical factor complexity ≤ L + 1 and unconditional mechanical chain exclusion
example (a b : ℕ) (α ρ : ℝ) (L C : ℕ) :
    prefixFactorCount (mechTwoLetterSeq a b α ρ) L C ≤ L + 1 :=
  mechTwoLetterSeq_prefixFactorCount_le a b α ρ L C

example {a b a_0 : ℕ} {α ρ : ℝ}
    (ha3 : 3 ≤ a) (hab : a ≤ b) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 (mechTwoLetterSeq a b α ρ) u K) :=
  no_infinite_mechanical_two_letter_block_chain ha3 hab hα0 hα1

-- 6. Verify real logarithmic threshold rational selection and asymptotic-mean / liminf-complexity exclusion
example {kappa : ℝ} (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ)) :
    ∃ p q : ℕ, 1 ≤ q ∧ 3 ^ q < 2 ^ (p + q) ∧ (p : ℝ) * kappa < (q : ℝ) :=
  exists_pq_of_lt_log_threshold hlog

-- 7. Verify normalized maxPrefixDiscrepancy convergence, scale-local balance, non-stationary epoch family, and uniform window mean bridge
example {s : ℕ → ℕ} {lam : ℝ}
    (htend : Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ))
      Filter.atTop (nhds lam)) :
    Filter.Tendsto (fun H : ℕ => maxPrefixDiscrepancy s lam H / (H : ℝ))
      Filter.atTop (nhds 0) :=
  maxPrefixDiscrepancy_div_tendsto_zero htend

example {a b a_0 : ℕ} (ha3 : 3 ≤ a) (hab_lt : a < b) :
    (¬ ∃ lam : ℝ,
      Filter.Tendsto
        (fun n : ℕ => (blockSteps (nonStationaryEpochSeq a b) n : ℝ) / (n : ℝ))
        Filter.atTop (nhds lam)) ∧
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 (nonStationaryEpochSeq a b) u K) :=
  ⟨nonStationaryEpochSeq_no_limiting_mean hab_lt,
    no_infinite_nonStationaryEpochSeq_block_chain ha3 hab_lt⟩

#print axioms Mahler.EndpointAndBalancedExclusion.perpetual_finite_survival_endpoint_alternative
#print axioms Mahler.EndpointAndBalancedExclusion.exists_positive_infinite_companion_of_perpetual_finite_survival
#print axioms Mahler.EndpointAndBalancedExclusion.exists_positive_seed_ge_one_of_pos_companion
#print axioms Mahler.EndpointAndBalancedExclusion.exists_repeated_subword_of_prefixFactorCount_le
#print axioms Mahler.EndpointAndBalancedExclusion.parameterized_pq_repeated_subword_cutoff
#print axioms Mahler.EndpointAndBalancedExclusion.balanced_discrepancy_and_factor_complexity_exclusion
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_balanced_subcritical_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.mechTwoLetterSeq_balanced_discrepancy
#print axioms Mahler.EndpointAndBalancedExclusion.arbitrary_two_letter_ceiling_saturated_sturmian_exclusion
#print axioms Mahler.EndpointAndBalancedExclusion.mechTwoLetterSeq_finset_factor_card_le
#print axioms Mahler.EndpointAndBalancedExclusion.mechTwoLetterSeq_prefixFactorCount_le
#print axioms Mahler.EndpointAndBalancedExclusion.unconditional_mechanical_two_letter_finite_cutoff
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_mechanical_two_letter_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.exists_pq_of_lt_log_threshold
#print axioms Mahler.EndpointAndBalancedExclusion.asymptotic_mean_discrepancy_of_tendsto
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_asymptotic_mean_liminf_subcritical_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_tendsto_mean_log_threshold_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.balanced_cutoff_with_maxPrefixDiscrepancy
#print axioms Mahler.EndpointAndBalancedExclusion.prefixFactorCount_le_iff_exists_repeated_subword
#print axioms Mahler.EndpointAndBalancedExclusion.maxPrefixDiscrepancy_div_tendsto_zero
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_global_complexity_log_threshold_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_scale_local_balanced_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.nonStationaryEpochSeq_no_limiting_mean
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_nonStationaryEpochSeq_block_chain
#print axioms Mahler.EndpointAndBalancedExclusion.tendsto_mean_of_uniformWindowMean
#print axioms Mahler.EndpointAndBalancedExclusion.no_infinite_uniformWindowMean_global_complexity_block_chain

end Mahler.EndpointAndBalancedExclusion.Checks
