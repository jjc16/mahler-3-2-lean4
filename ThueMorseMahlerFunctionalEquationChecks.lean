import ThueMorseMahlerFunctionalEquation

/-!
# Verification Checks for `ThueMorseMahlerFunctionalEquation`
-/

namespace Mahler.ThueMorseMahler.Checks

open Mahler
open Mahler.Adversarial
open Mahler.ThueMorseMahler

-- 1. Verify initial Thue-Morse values and pair-complementarity
example :
    tmBit 0 = 0 ∧ tmBit 1 = 1 ∧ tmBit 2 = 1 ∧ tmBit 3 = 0 ∧
      tmBit 4 = 1 ∧ tmBit 5 = 0 ∧ tmBit 6 = 0 ∧ tmBit 7 = 1 :=
  tmBit_initial_eight

example (k : ℕ) : tmBit (2 * k) + tmBit (2 * k + 1) = 1 :=
  tmBit_pair_sum_eq_one k

-- 2. Verify 6-step pair balance of the encoded Thue-Morse parity stream
example (k : ℕ) : (∑ i ∈ Finset.range 6, tmEncodedParity (6 * k + i)) = 1 :=
  tmEncodedParity_six_step_pair_balance k

-- 3. Verify closed infinite Mahler functional equation at z = 8/27
example :
    tmSeries (8 / 27 : ℝ) =
      (19 / 27 : ℝ) * tmSeries (64 / 729 : ℝ) + (216 / 665 : ℝ) :=
  tmSeries_eight_twenty_sevenths_functional_equation

-- 4. Verify 2-adic seed Mahler bridge at horizon 6*M
example {a_0 M : ℕ}
    (hmatch : ∀ n < 6 * M, orbit a_0 n % 2 = tmEncodedParity n % 2) :
    64 ^ M ∣ (729 ^ M * (665 * a_0 + 72) + 113715 * tmIntCarry 64 729 M) :=
  (tm_six_mul_seed_mahler_bridge hmatch).2

-- 5. Verify all-scale encoded Thue-Morse repetition and finite seed cutoff (< 30 * 2^k and < 60 * W)
example (k : ℕ) {i : ℕ} (hi : i < 12 * 2 ^ k) :
    tmEncodedParity i = tmEncodedParity (18 * 2 ^ k + i) :=
  tmEncodedParity_scaled_window_repeat k hi

example {a_0 W k : ℕ} (ha0 : 0 < a_0) (hW : a_0 < 2 ^ W) (hk : W ≤ 2 ^ k) :
    ¬ (∀ n < 30 * 2 ^ k, orbit a_0 n % 2 = tmEncodedParity n) :=
  tmEncodedParity_finite_seed_cutoff ha0 hW hk

example {a_0 W : ℕ} (ha0 : 0 < a_0) (hW1 : 1 ≤ W) (hW : a_0 < 2 ^ W) :
    ∃ n < 60 * W, orbit a_0 n % 2 ≠ tmEncodedParity n :=
  tmEncodedParity_mismatch_lt_sixty_mul_bit_length ha0 hW1 hW

-- 6. Verify unconditional non-realization by any nonnegative integer and non-stabilization of seedResidue
example (a_0 : ℕ) :
    (∃ n : ℕ, orbit a_0 n % 2 ≠ tmEncodedParity n) ∧
      ¬ (∃ N_0 : ℕ, ∀ N ≥ N_0, Mahler.SeedResidueTree.seedResidue tmEncodedParity N = a_0) :=
  ⟨(no_nonneg_seed_realizes_tmEncodedParity a_0).1,
    tmEncodedParity_seedResidue_never_stabilizes.1 a_0⟩

-- 7. Verify quantitative seedResidue growth, < 60*N_0 forced jump, Thue-Morse block coding, and Period-Doubling exclusion
example (k : ℕ) :
    2 ^ (2 ^ k) ≤ Mahler.SeedResidueTree.seedResidue tmEncodedParity (30 * 2 ^ k) :=
  seedResidue_tmEncodedParity_ge_two_pow k

example {N_0 : ℕ} (hN0 : 1 ≤ N_0) :
    ∃ N : ℕ, N_0 ≤ N ∧ N < 60 * N_0 ∧
      Mahler.SeedResidueTree.seedResidue tmEncodedParity N <
        Mahler.SeedResidueTree.seedResidue tmEncodedParity (N + 1) ∧
      Mahler.SeedResidueTree.seedBit tmEncodedParity
        (Mahler.SeedResidueTree.seedResidue tmEncodedParity N) N = 1 :=
  tmEncodedParity_forced_seedBit_in_sixty_mul_window hN0

example {a b a_0 : ℕ} (ha3 : 3 ≤ a) (hab : a ≤ b) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, Mahler.BridgeThree.ValidBlockChain a_0 (tmBlockSeq a b) u K) :=
  no_infinite_tmBlockSeq_block_chain ha3 hab

example {a_0 W : ℕ} (ha0 : 0 < a_0) (hW1 : 1 ≤ W) (hW : a_0 < 2 ^ W) :
    ∃ n < 42 * W, orbit a_0 n % 2 ≠ pdEncodedParity n :=
  pdEncodedParity_cutoff_and_exclusion.2.1 ha0 hW1 hW

#print axioms Mahler.ThueMorseMahler.seedResidue_tmEncodedParity_ge_two_pow
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_forced_seedBit_in_sixty_mul_window
#print axioms Mahler.ThueMorseMahler.dyadic_inflated_repetition_cutoff
#print axioms Mahler.ThueMorseMahler.tmBlockSeq_finite_seed_cutoff
#print axioms Mahler.ThueMorseMahler.no_infinite_tmBlockSeq_block_chain
#print axioms Mahler.ThueMorseMahler.pdBit_scaled_window_repeat
#print axioms Mahler.ThueMorseMahler.pdEncodedParity_cutoff_and_exclusion
#print axioms Mahler.ThueMorseMahler.pdBit_not_eventually_periodic
#print axioms Mahler.ThueMorseMahler.pdEncodedParity_not_eventually_periodic
#print axioms Mahler.ThueMorseMahler.seedResidue_pdEncodedParity_ge_two_pow

#print axioms Mahler.ThueMorseMahler.tmBit_pair_sum_eq_one
#print axioms Mahler.ThueMorseMahler.tmEncodedStream_fractionalTail_admissible
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_six_step_pair_balance
#print axioms Mahler.ThueMorseMahler.tmPartialSum_two_mul_eq
#print axioms Mahler.ThueMorseMahler.tmPartialSum_mahler_functional_identity
#print axioms Mahler.ThueMorseMahler.tmSeries_mahler_functional_equation
#print axioms Mahler.ThueMorseMahler.tmSeries_eight_twenty_sevenths_functional_equation
#print axioms Mahler.ThueMorseMahler.tmIntCarry_two_mul_functional_equation
#print axioms Mahler.ThueMorseMahler.tm_six_mul_seed_mahler_bridge
#print axioms Mahler.ThueMorseMahler.tmBit_scaled_window_repeat
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_scaled_window_repeat
#print axioms Mahler.ThueMorseMahler.scalable_early_repetition_cutoff
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_finite_seed_cutoff
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_mismatch_lt_sixty_mul_bit_length
#print axioms Mahler.ThueMorseMahler.no_nonneg_seed_realizes_tmEncodedParity
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_seedResidue_never_stabilizes
#print axioms Mahler.ThueMorseMahler.tmEncodedStream_aperiodic_fractional_survivor_not_integer_realizable
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_shifted_finite_seed_cutoff
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_orbit_preperiod_cutoff
#print axioms Mahler.ThueMorseMahler.tmComplementEncodedParity_finite_seed_cutoff
#print axioms Mahler.ThueMorseMahler.tmBit_not_eventually_periodic
#print axioms Mahler.ThueMorseMahler.tmEncodedParity_not_eventually_periodic

end Mahler.ThueMorseMahler.Checks
