import ExactSeedResidueTreeAndStabilization

/-!
# Verification Checks for `ExactSeedResidueTreeAndStabilization`
-/

namespace Mahler.SeedResidueTree.Checks

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree

-- 1. Verify bidirectional parity-prefix equivalence
example (a b N : ℕ) :
    (∀ n < N, orbit a n % 2 = orbit b n % 2) ↔ a % 2 ^ N = b % 2 ^ N :=
  orbit_parity_eq_upto_iff_mod_two_pow a b N

-- 2. Verify constructive seedResidue values on periodicThreeParity (`100100...`)
-- Note: `-9/19 ≡ 5 (mod 8)` (`19 * 5 + 9 = 104 = 8 * 13`) and `-9/19 ≡ 13 (mod 64)` (`19 * 13 + 9 = 256 = 64 * 4`).
example :
    seedResidue periodicThreeParity 3 = 5 ∧
      seedResidue periodicThreeParity 6 = 13 ∧
      (19 * 5 + 9) % 8 = 0 ∧
      (19 * 13 + 9) % 64 = 0 := by
  decide

-- 3. Verify stabilization equivalence for ordinary nonnegative integer seeds
example (ε : ℕ → ℕ) (a_0 : ℕ) :
    (∀ n : ℕ, orbit a_0 n % 2 = ε n % 2) ↔
      ∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue ε N = a_0 :=
  exists_nonneg_seed_iff_seedResidue_stabilizes ε a_0

-- 4. Verify superLacunarySeq exclusion
example :
    (∀ m : ℕ, 0 < Mahler.MinSlackSystem.minSlack superLacunarySeq m) ∧
      (∀ r1 r2 : ℕ, r1 < r2 → superLacunarySeq r1 < superLacunarySeq r2) ∧
      (∀ {a_0 W K m : ℕ} {u : ℕ → ℕ},
        m < K → a_0 < 2 ^ W → ValidBlockChain a_0 superLacunarySeq u K →
          6 * 2 ^ m ≤ 5 * W + 16) :=
  superLacunarySeq_properties_and_exclusion

-- 5. Verify exact rational offset feasibility criterion and well-founded odd-quotient descent
example {ε : ℕ → ℕ} {a N : ℕ} (hmod : a % 2 ^ N = seedResidue ε N) :
    (∃ ξ : ℝ, ValidCompanionUpTo a ξ N) ↔
      ratLowerOffset ε N < ratIntervalHi ε N :=
  validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi hmod

example {a_0 m_0 : ℕ} {s : ℕ → ℕ}
    (hgrowth : ∀ m ≥ m_0, 3 ≤ s (m + 1) ∧ 3 ^ (s m) < 2 ^ (s (m + 1))) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 s u K) :=
  no_infinite_rapid_growth_block_chain hgrowth

-- 6. Verify canonical FeasibleSeedNode, full companion-set membership, signedMargin, and step-29 bound
example (ε : ℕ → ℕ) (N : ℕ) (node : FeasibleSeedNode ε N) :
    node = FeasibleSeedNode.canonical ε N :=
  FeasibleSeedNode.eq_canonical node

example {ε : ℕ → ℕ} {a N : ℕ} {x : ℝ} (hmod : a % 2 ^ N = seedResidue ε N) :
    ValidCompanionUpTo a ((a : ℝ) + x) N ↔
      (((ratLowerOffset ε N : ℚ) : ℝ) ≤ x ∧ x < ((ratIntervalHi ε N : ℚ) : ℝ)) :=
  validCompanionUpTo_add_offset_iff_mem_ratInterval hmod

example {m : ℕ} (hm : 0 < m) (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo m ξ 29) :
    4096 ≤ m :=
  positive_survivor_step29_ge_4096 hm hsurv

#print axioms Mahler.SeedResidueTree.FeasibleSeedNode.eq_canonical
#print axioms Mahler.SeedResidueTree.validCompanionUpTo_add_offset_iff_mem_ratInterval
#print axioms Mahler.SeedResidueTree.signedMargin_cast_rat
#print axioms Mahler.SeedResidueTree.validCompanionUpTo_iff_signedMargin_pos
#print axioms Mahler.SeedResidueTree.coupled_seedQuotient_and_margin_transition
#print axioms Mahler.SeedResidueTree.general_mahler_conjecture_iff_positive_stabilized_branch_escape
#print axioms Mahler.SeedResidueTree.no_perpetual_feasible_stabilized_branch_of_rank_certificate
#print axioms Mahler.SeedResidueTree.seed_149_survives_28_and_fails_29
#print axioms Mahler.SeedResidueTree.positive_survivor_step29_ge_4096
#print axioms Mahler.SeedResidueTree.leastPositiveSurvivor_certified_bounds
#print axioms Mahler.SeedResidueTree.mahler_conjecture_iff_leastPositiveSurvivor_unbounded
#print axioms Mahler.SeedResidueTree.signedMargin_10101_neg
#print axioms Mahler.SeedResidueTree.signedMargin_100_ceiling_recovery

#print axioms Mahler.SeedResidueTree.orbit_parity_eq_upto_iff_mod_two_pow
#print axioms Mahler.SeedResidueTree.orbit_add_two_pow_step_eq
#print axioms Mahler.SeedResidueTree.orbit_seedResidue_mod_two
#print axioms Mahler.SeedResidueTree.orbit_parity_match_iff_mod_two_pow_eq_seedResidue
#print axioms Mahler.SeedResidueTree.exists_nonneg_seed_iff_seedResidue_stabilizes
#print axioms Mahler.SeedResidueTree.exists_pos_seed_iff_seedResidue_stabilizes_pos
#print axioms Mahler.SeedResidueTree.constant_three_wordCarry_identity
#print axioms Mahler.SeedResidueTree.constant_three_seedResidue_never_stabilizes
#print axioms Mahler.SeedResidueTree.single_block_pq_spike_cutoff
#print axioms Mahler.SeedResidueTree.superLacunarySeq_properties_and_exclusion
#print axioms Mahler.SeedResidueTree.no_infinite_superLacunary_block_chain
#print axioms Mahler.SeedResidueTree.lowerBound_and_upperBound_eq_add_ratOffset
#print axioms Mahler.SeedResidueTree.validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi
#print axioms Mahler.SeedResidueTree.residue_class_feasibility_iff_seedResidue
#print axioms Mahler.SeedResidueTree.odd_quotient_transition_identity
#print axioms Mahler.SeedResidueTree.three_pow_add_one_not_dvd_eight
#print axioms Mahler.SeedResidueTree.odd_quotient_one_forces_short_next_block
#print axioms Mahler.SeedResidueTree.odd_quotient_strict_descent_of_exp_growth
#print axioms Mahler.SeedResidueTree.no_infinite_rapid_growth_block_chain

end Mahler.SeedResidueTree.Checks
