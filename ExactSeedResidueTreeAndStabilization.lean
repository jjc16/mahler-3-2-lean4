import EndpointCompactnessAndBalancedExclusion

/-!
# The Exact Seed-Residue Tree, Parity-Prefix Bijection & Nonperiodic Spike Exclusion

This module implements **Stage 2** of `RESEARCH_OUTLINE_NEXT_STAGE.md`:

1. **Symbolic Parity Carry & Exact Step Identity (`wordCarry`,
   `wordCarry_eq_carry_of_parity_match`, `orbit_add_two_pow_step_eq`)**:
   - For any symbolic parity sequence `ε : ℕ → ℕ`, defines the cumulative carry
     `wordCarry ε N = ∑_{j < N} (ε j % 2) * 2^j * 3^(N - 1 - j)` recursively.
   - Proves that if `∀ n < N, orbit a n % 2 = ε n % 2`, then `wordCarry ε N = carry a 0 N`
     and `2^N * orbit a N = 3^N * a + wordCarry ε N`.
   - Proves the exact 2-adic bit-perturbation law: if `a` and `a + 2^N` share the
     first `N` parities, then `orbit (a + 2^N) N = orbit a N + 3^N`, which flips the
     step-`N` parity (`orbit (a + 2^N) N % 2 ≠ orbit a N % 2`).

2. **Bidirectional Parity-Prefix Bijection & Constructive Seed-Residue Tree
   (`orbit_parity_eq_upto_iff_mod_two_pow`, `seedBit`, `seedResidue`,
   `seedResidue_lt_two_pow`, `seedResidue_succ_mod`, `orbit_seedResidue_mod_two`,
   `orbit_parity_match_iff_mod_two_pow_eq_seedResidue`)**:
   - Proves both directions of the parity-prefix equivalence:
     `(∀ n < N, orbit a n % 2 = orbit b n % 2) ↔ a % 2^N = b % 2^N`.
   - Constructively defines the unique least residue `seedResidue ε N < 2^N` and
     extension bit `seedBit ε (seedResidue ε N) N ∈ {0, 1}` satisfying
     `seedResidue ε (N + 1) = seedResidue ε N + seedBit ε (seedResidue ε N) N * 2^N`
     and `∀ n < N, orbit (seedResidue ε N) n % 2 = ε n % 2`.

3. **Exact Stabilization Characterization of Ordinary Integer Seeds
   (`exists_nonneg_seed_iff_seedResidue_stabilizes`,
   `zero_seed_all_zero_exception`,
   `exists_pos_seed_iff_seedResidue_stabilizes_pos`)**:
   - An infinite parity stream `ε` comes from an ordinary nonnegative integer `a_0 : ℕ`
     (`∀ n, orbit a_0 n % 2 = ε n % 2`) **if and only if** the monotonic residue
     sequence `seedResidue ε N` eventually stabilizes (`∃ N_0 a_0, ∀ N ≥ N_0, seedResidue ε N = a_0`).
   - Separates the `a_0 = 0` exception (`∀ n, orbit 0 n = 0` and `ValidCompanionForever 0 0`)
     from positive seeds `1 ≤ a_0`.

4. **Baseline Recovery & Nonperiodic Unbalanced Family Exclusion
   (`constant_three_wordCarry_identity`, `constant_three_seedResidue_never_stabilizes`,
   `single_block_pq_spike_cutoff`, `superLacunarySeq`,
   `superLacunarySeq_properties_and_exclusion`)**:
   - Recovers the constant-length-3 (`100100...`) obstruction directly from the
     seed-residue tree: `19 * wordCarry ε_3 (3 * m) + 9 * 8^m = 9 * 27^m`, forcing
     `8^m ∣ (19 * seedResidue ε_3 (3 * m) + 9)` and proving that `seedResidue ε_3`
     can never stabilize at any nonnegative integer `a_0`.
   - Proves the single-block parameterized `(p, q)` spike cutoff
     `q * (s m - 1) + 1 ≤ p * blockSteps s m + q * W + p` (`5 * s m ≤ 3 * blockSteps s m + 5 * W + 7`),
     and uses it to exclude the nonperiodic, unbalanced, repetition-free family
     `superLacunarySeq k = 3 * 2^k` (where `minSlack > 0` holds forever and no
     subword ever repeats).

5. **Exact Rational Feasibility Intervals Coupled to Seed Stabilization & Odd-Quotient Descent
   (`ratLowerOffset`, `ratUpperOffset`, `ratIntervalHi`, `FeasibleSeedNode`,
   `lowerBound_and_upperBound_eq_add_ratOffset`,
   `validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi`,
   `no_infinite_superLacunary_block_chain`,
   `odd_quotient_transition_identity`, `three_pow_add_one_not_dvd_eight`,
   `odd_quotient_one_forces_short_next_block`,
   `odd_quotient_strict_descent_of_exp_growth`,
   `no_infinite_rapid_growth_block_chain`)**:
   - Couples the seed-residue tree to the exact rational fractional-offset interval
     `[C_N / 3^N, min_{0 ≤ j ≤ N} (C_j / 3^j + (1/2) * (2/3)^j))` and proves that
     every nonnegative seed `a ≡ seedResidue ε N (mod 2^N)` has a valid companion
     up to horizon `N` if and only if `ratLowerOffset ε N < ratIntervalHi ε N`.
   - Proves the exact odd-quotient transition law `2^(s (m + 1)) * u (m + 1) = 3^(s m) * u m + 1`,
     the mod-8 parity trap `¬ (8 ∣ 3^c + 1)` forcing `s (m + 1) ≤ 2` whenever `u m = 1`,
     and the well-founded odd-quotient descent `u (m + 1) + 2 ≤ u m` whenever
     `3 ≤ s (m + 1)` and `3^(s m) < 2^(s (m + 1))`, unconditionally excluding the
     entire nonperiodic rapid-growth block family.
-/

namespace Mahler.SeedResidueTree

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB
open Mahler.JumpValuation
open Mahler.EscapeBranchCap
open Mahler.PhaseLock
open Mahler.MasterReduction
open Mahler.ModEightClassifier
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.KernelDuality
open Mahler.Coasting
open Mahler.TwoSidedSqueeze
open Mahler.SharpenedSqueezes
open Mahler.AperiodicCocycle
open Mahler.MinSlackSystem
open Mahler.GlobalStepRate
open Mahler.BaseTwoLock
open Mahler.CeilingSynthesis
open Mahler.TelescopingDuality
open Mahler.ConverseReconstruction
open Mahler.ExplicitCutoffs
open Mahler.DeficitAmplification
open Mahler.TwoVisitSeparation
open Mahler.MonotonicSeparation
open Mahler.CeilingModTraps
open Mahler.TwoAdicLTE
open Mahler.FullStepValuation
open Mahler.RemainderAdditionLaw
open Mahler.TwoAdicCauchy
open Mahler.AllHistoryRecovery
open Mahler.ParametricCorridor
open Mahler.AperiodicBoundedSqueeze
open Mahler.TimeIndependentSqueeze
open Mahler.SlackDeadEnds
open Mahler.GrandSynthesis
open Mahler.Mod256Sieve
open Mahler.UnitRigidity
open Mahler.DeterminantCollapse
open Mahler.BakerMatveev
open Mahler.RidoutSubspace
open Mahler.MultiOriginSyzygy
open Mahler.SubwordComplexity
open Mahler.SimultaneousBaseDigits
open Mahler.MultiStepGCD
open Mahler.SeriesHankel
open Mahler.ThreeAdicSeedLocks
open Mahler.CoupledFractionalDynamics
open Mahler.Mod2304Sieve
open Mahler.TwoSidedCRTObstructions
open Mahler.ThreeAdicConservation
open Mahler.Mod216QuotientFloor
open Mahler.InfiniteZNumberBridge
open Mahler.SturmianComplexityExclusion
open Mahler.FiniteSeedAndBackwardDescent
open Mahler.SubstitutionAndGrandSynthesis
open Mahler.EndpointAndBalancedExclusion

/-! ## 1. Symbolic Parity Carry & Bidirectional Parity-Prefix Bijection -/

/-- Symbolic carry integer `C_N = ∑_{j < N} (ε j % 2) * 2^j * 3^(N - 1 - j)`
associated to a parity stream `ε : ℕ → ℕ`. -/
def wordCarry (ε : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 3 * wordCarry ε N + 2 ^ N * (ε N % 2)

/-- If `a : ℕ` has orbit parities matching `ε` on `0, ..., N - 1`, then
`carry a 0 N = wordCarry ε N` and `2^N * orbit a N = 3^N * a + wordCarry ε N`. -/
theorem wordCarry_eq_carry_of_parity_match {a N : ℕ} {ε : ℕ → ℕ}
    (hmatch : ∀ n < N, orbit a n % 2 = ε n % 2) :
    carry a 0 N = wordCarry ε N ∧
      2 ^ N * orbit a N = 3 ^ N * a + wordCarry ε N := by
  have hc : carry a 0 N = wordCarry ε N := by
    induction N with
    | zero => simp [carry, wordCarry]
    | succ N ih =>
        have ihN := ih (fun n hn => hmatch n (by omega))
        have hN := hmatch N (Nat.lt_succ_self N)
        have hsucc := carry_succ a 0 N
        simp only [Nat.zero_add] at hsucc
        simp only [wordCarry]
        rw [hsucc, ihN, hN]
  refine ⟨hc, ?_⟩
  have hid := two_pow_mul_orbit_eq_add_carry a 0 N
  simp only [Nat.zero_add, orbit] at hid
  rw [hid, hc]

/-- Forward direction of the parity-prefix bijection: if `orbit a` and `orbit b`
have the same parities for all `n < N`, then `a % 2^N = b % 2^N`. -/
theorem mod_two_pow_eq_of_orbit_parity_eq {a b N : ℕ}
    (hpar : ∀ n < N, orbit a n % 2 = orbit b n % 2) :
    a % 2 ^ N = b % 2 ^ N := by
  have hca := (wordCarry_eq_carry_of_parity_match (ε := fun n => orbit b n % 2)
    (a := a) (N := N) (fun n hn => by simpa using hpar n hn)).2
  have hcb := (wordCarry_eq_carry_of_parity_match (ε := fun n => orbit b n % 2)
    (a := b) (N := N) (fun n _ => by simp)).2
  have hcop : Nat.Coprime (2 ^ N) (3 ^ N) :=
    (by decide : Nat.Coprime 2 3).pow N N
  rcases le_total b a with hba | hab
  · have h3le : 3 ^ N * b ≤ 3 ^ N * a := Nat.mul_le_mul_left (3 ^ N) hba
    have h2le : 2 ^ N * orbit b N ≤ 2 ^ N * orbit a N := by omega
    have horb_le : orbit b N ≤ orbit a N :=
      Nat.le_of_mul_le_mul_left h2le (Nat.pow_pos (by decide))
    have hdiff : 2 ^ N * (orbit a N - orbit b N) = 3 ^ N * (a - b) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      omega
    have hdvd_mul : 2 ^ N ∣ 3 ^ N * (a - b) := ⟨orbit a N - orbit b N, hdiff.symm⟩
    have hdvd : 2 ^ N ∣ a - b := hcop.dvd_of_dvd_mul_left hdvd_mul
    rcases hdvd with ⟨q, hq⟩
    have ha_eq : a = b + 2 ^ N * q := by omega
    rw [ha_eq, Nat.add_mul_mod_self_left]
  · have h3le : 3 ^ N * a ≤ 3 ^ N * b := Nat.mul_le_mul_left (3 ^ N) hab
    have h2le : 2 ^ N * orbit a N ≤ 2 ^ N * orbit b N := by omega
    have horb_le : orbit a N ≤ orbit b N :=
      Nat.le_of_mul_le_mul_left h2le (Nat.pow_pos (by decide))
    have hdiff : 2 ^ N * (orbit b N - orbit a N) = 3 ^ N * (b - a) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      omega
    have hdvd_mul : 2 ^ N ∣ 3 ^ N * (b - a) := ⟨orbit b N - orbit a N, hdiff.symm⟩
    have hdvd : 2 ^ N ∣ b - a := hcop.dvd_of_dvd_mul_left hdvd_mul
    rcases hdvd with ⟨q, hq⟩
    have hb_eq : b = a + 2 ^ N * q := by omega
    rw [hb_eq, Nat.add_mul_mod_self_left]

/-- Converse direction of the parity-prefix bijection: if `a % 2^N = b % 2^N`,
then `orbit a n % 2 = orbit b n % 2` for all `n < N`. -/
theorem orbit_parity_eq_of_mod_two_pow_eq {a b N : ℕ}
    (hmod : a % 2 ^ N = b % 2 ^ N) :
    ∀ n < N, orbit a n % 2 = orbit b n % 2 := by
  induction N with
  | zero =>
      intro n hn
      omega
  | succ N ih =>
      have hmodN : a % 2 ^ N = b % 2 ^ N := by
        have hdvd : 2 ^ N ∣ 2 ^ (N + 1) := ⟨2, by rw [Nat.pow_succ]⟩
        rw [← Nat.mod_mod_of_dvd a hdvd, ← Nat.mod_mod_of_dvd b hdvd, hmod]
      have ihN := ih hmodN
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
      · exact ihN n hlt
      · subst heq
        have hca := (wordCarry_eq_carry_of_parity_match (ε := fun k => orbit b k % 2)
          (a := a) (N := n) (fun k hk => by simpa using ihN k hk)).2
        have hcb := (wordCarry_eq_carry_of_parity_match (ε := fun k => orbit b k % 2)
          (a := b) (N := n) (fun k _ => by simp)).2
        have hrhs_mod :
            (3 ^ n * a + wordCarry (fun k => orbit b k % 2) n) % 2 ^ (n + 1) =
              (3 ^ n * b + wordCarry (fun k => orbit b k % 2) n) % 2 ^ (n + 1) := by
          rw [Nat.add_mod, Nat.mul_mod (3 ^ n) a, hmod, ← Nat.mul_mod (3 ^ n) b, ← Nat.add_mod]
        rw [← hca, ← hcb] at hrhs_mod
        have hpow_succ : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
        rw [hpow_succ, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hrhs_mod
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2)) hrhs_mod

/-- **Bidirectional Parity-Prefix Bijection (`orbit_parity_eq_upto_iff_mod_two_pow`)**:
For any natural numbers `a, b, N`, the first `N` parities of `orbit a` and `orbit b`
coincide if and only if `a ≡ b (mod 2^N)`. -/
theorem orbit_parity_eq_upto_iff_mod_two_pow (a b N : ℕ) :
    (∀ n < N, orbit a n % 2 = orbit b n % 2) ↔ a % 2 ^ N = b % 2 ^ N :=
  ⟨mod_two_pow_eq_of_orbit_parity_eq, orbit_parity_eq_of_mod_two_pow_eq⟩

/-- **Exact Bit-Perturbation Shift Law (`orbit_add_two_pow_step_eq`)**:
For any seed `a : ℕ` and horizon `N : ℕ`, adding `2^N` to `a` preserves all parities
before step `N` and shifts `orbit (a + 2^N) N` by exactly `3^N`:
`orbit (a + 2^N) N = orbit a N + 3^N`. -/
theorem orbit_add_two_pow_step_eq (a N : ℕ) :
    orbit (a + 2 ^ N) N = orbit a N + 3 ^ N := by
  have hmod : (a + 2 ^ N) % 2 ^ N = a % 2 ^ N := Nat.add_mod_right a (2 ^ N)
  have hpar := orbit_parity_eq_of_mod_two_pow_eq hmod
  have hca := (wordCarry_eq_carry_of_parity_match (ε := fun k => orbit a k % 2)
    (a := a) (N := N) (fun _ _ => by simp)).2
  have hc_add := (wordCarry_eq_carry_of_parity_match (ε := fun k => orbit a k % 2)
    (a := a + 2 ^ N) (N := N) (fun k hk => by simpa using hpar k hk)).2
  have hcomb :
      2 ^ N * orbit (a + 2 ^ N) N = 2 ^ N * (orbit a N + 3 ^ N) := by
    calc
      2 ^ N * orbit (a + 2 ^ N) N =
          3 ^ N * (a + 2 ^ N) + wordCarry (fun k => orbit a k % 2) N := hc_add
      _ = (3 ^ N * a + wordCarry (fun k => orbit a k % 2) N) + 2 ^ N * 3 ^ N := by ring
      _ = 2 ^ N * orbit a N + 2 ^ N * 3 ^ N := by rw [← hca]
      _ = 2 ^ N * (orbit a N + 3 ^ N) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hcomb

/-! ## 2. Constructive Seed-Residue Tree & Monotonic Bit Extension -/

/-- The `N`-th extension bit `η_N ∈ {0, 1}` required to match parity `ε N % 2`
starting from residue `r_N`. -/
def seedBit (ε : ℕ → ℕ) (r_N N : ℕ) : ℕ :=
  if orbit r_N N % 2 = ε N % 2 then 0 else 1

/-- Constructive definition of the unique seed residue `seedResidue ε N ∈ [0, 2^N)`
whose first `N` orbit parities match `ε`. -/
def seedResidue (ε : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => seedResidue ε N + seedBit ε (seedResidue ε N) N * 2 ^ N

theorem seedBit_le_one (ε : ℕ → ℕ) (r_N N : ℕ) : seedBit ε r_N N ≤ 1 := by
  unfold seedBit
  split_ifs <;> omega

/-- Every `seedResidue ε N` lies strictly in `[0, 2^N)`. -/
theorem seedResidue_lt_two_pow (ε : ℕ → ℕ) (N : ℕ) :
    seedResidue ε N < 2 ^ N := by
  induction N with
  | zero => simp [seedResidue]
  | succ N ih =>
      simp only [seedResidue, Nat.pow_succ]
      have hb := seedBit_le_one ε (seedResidue ε N) N
      have hmul : seedBit ε (seedResidue ε N) N * 2 ^ N ≤ 1 * 2 ^ N :=
        Nat.mul_le_mul_right (2 ^ N) hb
      omega

/-- The residue sequence `seedResidue ε` is monotonically non-decreasing:
`seedResidue ε N ≤ seedResidue ε (N + 1)`. -/
theorem seedResidue_le_succ (ε : ℕ → ℕ) (N : ℕ) :
    seedResidue ε N ≤ seedResidue ε (N + 1) := by
  simp only [seedResidue]
  omega

/-- Monotonicity of `seedResidue ε`: if `N ≤ M`, then `seedResidue ε N ≤ seedResidue ε M`. -/
theorem seedResidue_mono (ε : ℕ → ℕ) {N M : ℕ} (hNM : N ≤ M) :
    seedResidue ε N ≤ seedResidue ε M := by
  induction M with
  | zero =>
      have hN0 : N = 0 := by omega
      subst hN0
      exact le_rfl
  | succ M ih =>
      rcases Nat.eq_or_lt_of_le hNM with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega)) (seedResidue_le_succ ε M)

/-- Projective compatibility: `seedResidue ε (N + 1) % 2^N = seedResidue ε N`. -/
theorem seedResidue_succ_mod (ε : ℕ → ℕ) (N : ℕ) :
    seedResidue ε (N + 1) % 2 ^ N = seedResidue ε N := by
  simp only [seedResidue, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (seedResidue_lt_two_pow ε N)

/-- Projective compatibility across arbitrary depths `N ≤ M`:
`seedResidue ε M % 2^N = seedResidue ε N`. -/
theorem seedResidue_mod_two_pow_of_le (ε : ℕ → ℕ) {N M : ℕ} (hNM : N ≤ M) :
    seedResidue ε M % 2 ^ N = seedResidue ε N := by
  induction M with
  | zero =>
      have hN0 : N = 0 := by omega
      subst hN0
      simp [seedResidue]
  | succ M ih =>
      rcases Nat.eq_or_lt_of_le hNM with heq | hlt
      · subst heq
        exact Nat.mod_eq_of_lt (seedResidue_lt_two_pow ε (M + 1))
      · have hdvd : 2 ^ N ∣ 2 ^ M := Nat.pow_dvd_pow 2 (by omega)
        rw [← Nat.mod_mod_of_dvd (seedResidue ε (M + 1)) hdvd,
          seedResidue_succ_mod, ih (by omega)]

private theorem three_pow_mod_two' (N : ℕ) : 3 ^ N % 2 = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **Exact Parity Realization of `seedResidue` (`orbit_seedResidue_mod_two`)**:
For every `N : ℕ` and every `n < N`, `orbit (seedResidue ε N) n % 2 = ε n % 2`. -/
theorem orbit_seedResidue_mod_two (ε : ℕ → ℕ) (N : ℕ) :
    ∀ n < N, orbit (seedResidue ε N) n % 2 = ε n % 2 := by
  induction N with
  | zero =>
      intro n hn
      omega
  | succ N ih =>
      intro n hn
      have hmod_succ :
          seedResidue ε (N + 1) % 2 ^ N = (seedResidue ε N) % 2 ^ N := by
        rw [seedResidue_succ_mod, Nat.mod_eq_of_lt (seedResidue_lt_two_pow ε N)]
      have hpar_prev := orbit_parity_eq_of_mod_two_pow_eq hmod_succ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
      · rw [hpar_prev n hlt, ih n hlt]
      · subst heq
        simp only [seedResidue, seedBit]
        split_ifs with h
        · simpa using h
        · have hshift := orbit_add_two_pow_step_eq (seedResidue ε n) n
          have h1 : seedResidue ε n + 1 * 2 ^ n = seedResidue ε n + 2 ^ n := by ring
          rw [h1, hshift, Nat.add_mod, three_pow_mod_two']
          omega

/-- **Exact Characterization of Parity-Matching Seeds (`orbit_parity_match_iff_mod_two_pow_eq_seedResidue`)**:
A natural number `a` has first `N` orbit parities matching `ε` if and only if
`a % 2^N = seedResidue ε N`. -/
theorem orbit_parity_match_iff_mod_two_pow_eq_seedResidue (ε : ℕ → ℕ) (a N : ℕ) :
    (∀ n < N, orbit a n % 2 = ε n % 2) ↔ a % 2 ^ N = seedResidue ε N := by
  have hres := orbit_seedResidue_mod_two ε N
  constructor
  · intro ha
    have heq : ∀ n < N, orbit a n % 2 = orbit (seedResidue ε N) n % 2 := by
      intro n hn
      rw [ha n hn, hres n hn]
    rw [mod_two_pow_eq_of_orbit_parity_eq heq]
    exact Nat.mod_eq_of_lt (seedResidue_lt_two_pow ε N)
  · intro hmod n hn
    have hmod' : a % 2 ^ N = (seedResidue ε N) % 2 ^ N := by
      rw [hmod, Nat.mod_eq_of_lt (seedResidue_lt_two_pow ε N)]
    rw [orbit_parity_eq_of_mod_two_pow_eq hmod' n hn, hres n hn]

/-! ## 3. Stabilization Characterization of Ordinary Nonnegative & Positive Integer Seeds -/

private theorem n_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- **Exact Stabilization Characterization of Nonnegative Integer Seeds
(`exists_nonneg_seed_iff_seedResidue_stabilizes`)**:
An infinite parity stream `ε : ℕ → ℕ` is generated by an ordinary nonnegative
integer seed `a_0 : ℕ` (`∀ n : ℕ, orbit a_0 n % 2 = ε n % 2`) **if and only if**
its least-residue sequence `seedResidue ε N` eventually stabilizes at `a_0`
(`∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue ε N = a_0`). -/
theorem exists_nonneg_seed_iff_seedResidue_stabilizes (ε : ℕ → ℕ) (a_0 : ℕ) :
    (∀ n : ℕ, orbit a_0 n % 2 = ε n % 2) ↔
      ∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue ε N = a_0 := by
  constructor
  · intro hall
    refine ⟨a_0, fun N hN => ?_⟩
    have hmatch : ∀ n < N, orbit a_0 n % 2 = ε n % 2 := fun n _ => hall n
    have hmod := (orbit_parity_match_iff_mod_two_pow_eq_seedResidue ε a_0 N).mp hmatch
    have hlt : a_0 < 2 ^ N :=
      lt_of_lt_of_le (n_lt_two_pow a_0) (Nat.pow_le_pow_right (by decide) hN)
    rw [Nat.mod_eq_of_lt hlt] at hmod
    exact hmod.symm
  · rintro ⟨N_0, hstab⟩ n
    set N := max N_0 (n + 1)
    have hN0 : N_0 ≤ N := le_max_left N_0 (n + 1)
    have hnN : n < N := by
      have h : n + 1 ≤ N := le_max_right N_0 (n + 1)
      omega
    have hres := orbit_seedResidue_mod_two ε N n hnN
    rwa [hstab N hN0] at hres

/-- **The All-Zero Seed Exception (`zero_seed_all_zero_exception`)**:
For `a_0 = 0`, `orbit 0 n = 0` for all `n : ℕ`, `seedResidue (fun _ => 0) N = 0`
for all `N : ℕ`, and `ValidCompanionForever 0 0` holds trivially. -/
theorem zero_seed_all_zero_exception :
    (∀ n : ℕ, orbit 0 n = 0) ∧
      (∀ N : ℕ, seedResidue (fun _ => 0) N = 0) ∧
      ValidCompanionForever 0 0 := by
  have horb : ∀ n : ℕ, orbit 0 n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [orbit, ih, step]
  refine ⟨horb, ?_, ?_⟩
  · intro N
    have hmatch : ∀ n < N, orbit 0 n % 2 = (fun _ => 0) n % 2 := by
      intro n _
      simp [horb n]
    have hmod := (orbit_parity_match_iff_mod_two_pow_eq_seedResidue (fun _ => 0) 0 N).mp hmatch
    simpa using hmod.symm
  · intro n
    unfold ValidCompanionAt
    simp [horb n]

/-- **Exact Stabilization Characterization of Positive Integer Seeds
(`exists_pos_seed_iff_seedResidue_stabilizes_pos`)**:
There exists a positive integer seed `1 ≤ a_0` generating `ε` if and only if
`seedResidue ε N` eventually stabilizes at a positive constant `1 ≤ a_0`. -/
theorem exists_pos_seed_iff_seedResidue_stabilizes_pos (ε : ℕ → ℕ) :
    (∃ a_0 : ℕ, 1 ≤ a_0 ∧ ∀ n : ℕ, orbit a_0 n % 2 = ε n % 2) ↔
      ∃ a_0 N_0 : ℕ, 1 ≤ a_0 ∧ ∀ N ≥ N_0, seedResidue ε N = a_0 := by
  constructor
  · rintro ⟨a_0, ha0, hall⟩
    obtain ⟨N_0, hstab⟩ := (exists_nonneg_seed_iff_seedResidue_stabilizes ε a_0).mp hall
    exact ⟨a_0, N_0, ha0, hstab⟩
  · rintro ⟨a_0, N_0, ha0, hstab⟩
    exact ⟨a_0, ha0, (exists_nonneg_seed_iff_seedResidue_stabilizes ε a_0).mpr ⟨N_0, hstab⟩⟩

/-! ## 4. Baseline Recovery (`100100...`) & Nonperiodic Unbalanced Spike Exclusion -/

/-- The periodic parity stream `100100...` of constant block length `3`. -/
def periodicThreeParity (n : ℕ) : ℕ :=
  if n % 3 = 0 then 1 else 0

/-- **Baseline Recovery via `wordCarry` (`constant_three_wordCarry_identity`)**:
For the constant-length-3 parity stream `periodicThreeParity`, the carry at step
`3 * m` satisfies the exact closed formula:
`19 * wordCarry periodicThreeParity (3 * m) + 9 * 8^m = 9 * 27^m`,
and every seed residue `seedResidue periodicThreeParity (3 * m)` satisfies
`8^m ∣ (19 * seedResidue periodicThreeParity (3 * m) + 9)`. -/
theorem constant_three_wordCarry_identity (m : ℕ) :
    19 * wordCarry periodicThreeParity (3 * m) + 9 * 8 ^ m = 9 * 27 ^ m ∧
      8 ^ m ∣ (19 * seedResidue periodicThreeParity (3 * m) + 9) := by
  have hcarry :
      19 * wordCarry periodicThreeParity (3 * m) + 9 * 8 ^ m = 9 * 27 ^ m := by
    induction m with
    | zero => rfl
    | succ m ih =>
        have hstep0 : (3 * m) % 3 = 0 := by omega
        have hstep1 : (3 * m + 1) % 3 = 1 := by omega
        have hstep2 : (3 * m + 2) % 3 = 2 := by omega
        have hc1 :
            wordCarry periodicThreeParity (3 * m + 1) =
              3 * wordCarry periodicThreeParity (3 * m) + 2 ^ (3 * m) := by
          simp [wordCarry, periodicThreeParity, hstep0]
        have hc2 :
            wordCarry periodicThreeParity (3 * m + 2) =
              3 * wordCarry periodicThreeParity (3 * m + 1) := by
          simp [wordCarry, periodicThreeParity, hstep1]
        have hc3 :
            wordCarry periodicThreeParity (3 * (m + 1)) =
              3 * wordCarry periodicThreeParity (3 * m + 2) := by
          have h3 : 3 * (m + 1) = (3 * m + 2) + 1 := by omega
          rw [h3]
          simp [wordCarry, periodicThreeParity, hstep2]
        have hpow2 : 2 ^ (3 * m) = 8 ^ m := by
          rw [Nat.pow_mul]
        rw [hc3, hc2, hc1, hpow2, Nat.pow_succ 8 m, Nat.pow_succ 27 m]
        omega
  refine ⟨hcarry, ?_⟩
  set r := seedResidue periodicThreeParity (3 * m)
  have hmatch := orbit_seedResidue_mod_two periodicThreeParity (3 * m)
  have hid := (wordCarry_eq_carry_of_parity_match hmatch).2
  have hpow2 : 2 ^ (3 * m) = 8 ^ m := by rw [Nat.pow_mul]
  have hpow3 : 3 ^ (3 * m) = 27 ^ m := by rw [Nat.pow_mul]
  rw [hpow2, hpow3] at hid
  have h19 :
      8 ^ m * (19 * orbit r (3 * m) + 9) = 27 ^ m * (19 * r + 9) := by
    calc
      8 ^ m * (19 * orbit r (3 * m) + 9) =
          19 * (8 ^ m * orbit r (3 * m)) + 9 * 8 ^ m := by ring
      _ = 19 * (27 ^ m * r + wordCarry periodicThreeParity (3 * m)) + 9 * 8 ^ m := by
        rw [hid]
      _ = 27 ^ m * 19 * r + (19 * wordCarry periodicThreeParity (3 * m) + 9 * 8 ^ m) := by
        ring
      _ = 27 ^ m * 19 * r + 9 * 27 ^ m := by rw [hcarry]
      _ = 27 ^ m * (19 * r + 9) := by ring
  have hdvd_mul : 8 ^ m ∣ 27 ^ m * (19 * r + 9) :=
    ⟨19 * orbit r (3 * m) + 9, h19.symm⟩
  have hcop : Nat.Coprime (8 ^ m) (27 ^ m) :=
    (by decide : Nat.Coprime 8 27).pow m m
  exact hcop.dvd_of_dvd_mul_left hdvd_mul

/-- The residue sequence `seedResidue periodicThreeParity` never stabilizes at
any ordinary nonnegative integer `a_0` (because `8^m ∣ 19 * a_0 + 9` fails for large `m`). -/
theorem constant_three_seedResidue_never_stabilizes (a_0 : ℕ) :
    ¬ (∀ n : ℕ, orbit a_0 n % 2 = periodicThreeParity n % 2) := by
  intro hall
  obtain ⟨N_0, hstab⟩ :=
    (exists_nonneg_seed_iff_seedResidue_stabilizes periodicThreeParity a_0).mp hall
  set m := max N_0 (19 * a_0 + 9)
  have hm_ge : N_0 ≤ 3 * m := by
    have h : N_0 ≤ m := le_max_left N_0 (19 * a_0 + 9)
    omega
  have hdvd := (constant_three_wordCarry_identity m).2
  rw [hstab (3 * m) hm_ge] at hdvd
  have hle : 8 ^ m ≤ 19 * a_0 + 9 := Nat.le_of_dvd (by omega) hdvd
  have hm_gt : 19 * a_0 + 9 < 8 ^ m := by
    have h1 : 19 * a_0 + 9 ≤ m := le_max_right N_0 (19 * a_0 + 9)
    have h2 : m < 2 ^ m := n_lt_two_pow m
    have h3 : 2 ^ m ≤ 8 ^ m := Nat.pow_le_pow_left (by decide) m
    omega
  omega

/-- **Single-Block Parameterized `(p, q)` Spike Cutoff (`single_block_pq_spike_cutoff`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`, `a_0 < 2^W`) with `0 < integerSlack s m`,
no repetition of subwords is required to bound the single block length `s m`:
because `1 ≤ u m`, `2^(blockSteps s m + s m + 1) < 3^(blockSteps s m + 1) * (2 * a_0 + 1)`,
and for every `(p, q)` with `1 ≤ q` and `3^q < 2^(p + q)`:
`q * (s m - 1) + 1 ≤ p * blockSteps s m + q * W + p`
(in particular `5 * s m ≤ 3 * blockSteps s m + 5 * W + 7`). -/
theorem single_block_pq_spike_cutoff
    {p q a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (hmK : m < K) (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    2 ^ (blockSteps s m + s m + 1) < 3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) ∧
      q * (s m - 1) + 1 ≤ p * blockSteps s m + q * W + p ∧
      5 * s m ≤ 3 * blockSteps s m + 5 * W + 7 := by
  rcases hchain m hmK with ⟨hsm, hum_odd, _⟩
  have hum_pos : 1 ≤ u m := by omega
  have horbit := integerSlack_eq_orbit_slack hmK hchain
  have hlt_int :
      (2 : ℤ) ^ (blockSteps s (m + 1) + 1) * (u m : ℤ) <
        (3 : ℤ) ^ (blockSteps s m + 1) * (2 * (a_0 : ℤ) + 1) := by
    linarith
  have hlt_nat :
      2 ^ (blockSteps s (m + 1) + 1) * u m <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
    exact_mod_cast hlt_int
  have hsteps_succ : blockSteps s (m + 1) = blockSteps s m + s m := rfl
  rw [hsteps_succ] at hlt_nat
  have h1le :
      2 ^ (blockSteps s m + s m + 1) ≤
        2 ^ (blockSteps s m + s m + 1) * u m :=
    Nat.le_mul_of_pos_right _ hum_pos
  have hexp :
      2 ^ (blockSteps s m + s m + 1) <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) :=
    lt_of_le_of_lt h1le hlt_nat
  have hexp' :
      2 ^ (blockSteps s m + (s m - 1) + 2) <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
    have heq : blockSteps s m + (s m - 1) + 2 = blockSteps s m + s m + 1 := by omega
    rwa [heq]
  have hpq_bound := pq_cutoff_of_exp_bound hq hpq ha0 hexp'
  have h53_bound :=
    pq_cutoff_of_exp_bound (p := 3) (q := 5) (by decide) (by decide) ha0 hexp'
  refine ⟨hexp, hpq_bound, by omega⟩

/-- The nonperiodic, unbalanced, repetition-free super-lacunary block sequence
`superLacunarySeq k = 3 * 2^k`. -/
def superLacunarySeq (k : ℕ) : ℕ :=
  3 * 2 ^ k

/-- Exact cumulative step formula for `superLacunarySeq`:
`blockSteps superLacunarySeq m + 3 = 3 * 2^m = superLacunarySeq m`. -/
theorem blockSteps_superLacunarySeq_eq (m : ℕ) :
    blockSteps superLacunarySeq m + 3 = 3 * 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [blockSteps, superLacunarySeq, Nat.pow_succ]
      omega

/-- **Exclusion of the Unbalanced Repetition-Free Family `superLacunarySeq`
(`superLacunarySeq_properties_and_exclusion`)**:
1. Every entry satisfies `3 ≤ superLacunarySeq k`, so `minSlack superLacunarySeq m = 2^(blockSteps superLacunarySeq m) > 0`
   holds forever,
2. `superLacunarySeq` is strictly increasing (`superLacunarySeq r1 ≠ superLacunarySeq r2` for `r1 < r2`),
   so **no subword of any positive length `L ≥ 1` ever repeats**, and
3. Along any `ValidBlockChain a_0 superLacunarySeq u K` (`m < K`, `a_0 < 2^W`),
   the single-block spike cutoff forces `6 * 2^m ≤ 5 * W + 16`. -/
theorem superLacunarySeq_properties_and_exclusion :
    (∀ m : ℕ, 0 < minSlack superLacunarySeq m) ∧
      (∀ r1 r2 : ℕ, r1 < r2 → superLacunarySeq r1 < superLacunarySeq r2) ∧
      (∀ {a_0 W K m : ℕ} {u : ℕ → ℕ},
        m < K → a_0 < 2 ^ W → ValidBlockChain a_0 superLacunarySeq u K →
          6 * 2 ^ m ≤ 5 * W + 16) := by
  have hge3 : ∀ k : ℕ, 3 ≤ superLacunarySeq k := by
    intro k
    unfold superLacunarySeq
    have hpos : 1 ≤ 2 ^ k := Nat.pow_pos (by decide)
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact (all_shifted_slacks_pos_of_three_le superLacunarySeq m (fun k _ => hge3 k)).1
  · intro r1 r2 hr12
    unfold superLacunarySeq
    have hpow : 2 ^ r1 < 2 ^ r2 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hr12
    omega
  · intro a_0 W K m u hmK ha0 hchain
    have hslack : 0 < integerSlack superLacunarySeq m := by
      have h := (all_shifted_slacks_pos_of_three_le superLacunarySeq m (fun k _ => hge3 k)).2 0 (Nat.zero_le m)
      have hshift0 : shiftSeq superLacunarySeq 0 = superLacunarySeq := by
        funext k
        simp [shiftSeq]
      rwa [hshift0, Nat.sub_zero] at h
    have hspike :=
      (single_block_pq_spike_cutoff (p := 3) (q := 5) (by decide) (by decide)
        hmK ha0 hchain hslack).2.2
    have hsteps := blockSteps_superLacunarySeq_eq m
    change 5 * (3 * 2 ^ m) ≤ 3 * blockSteps superLacunarySeq m + 5 * W + 7 at hspike
    omega

/-- **Infinite-Horizon Exclusion of `superLacunarySeq` (`no_infinite_superLacunary_block_chain`)**:
For every nonnegative integer seed `a_0 : ℕ`, there is no infinite valid integer
block chain with block lengths `superLacunarySeq k = 3 * 2^k`. -/
theorem no_infinite_superLacunary_block_chain (a_0 : ℕ) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 superLacunarySeq u K) := by
  rintro ⟨u, hchain⟩
  have ha0 : a_0 < 2 ^ a_0 := n_lt_two_pow a_0
  set m := 5 * a_0 + 16
  have hcut :=
    superLacunarySeq_properties_and_exclusion.2.2
      (m := m) (K := m + 1) (Nat.lt_succ_self m) ha0 (hchain (m + 1))
  have hm_lt : m < 2 ^ m := n_lt_two_pow m
  omega

/-! ## 5. Exact Rational Offset Feasibility Intervals Coupled to the Seed-Residue Tree -/

/-- Exact rational lower fractional offset `C_j / 3^j` at step `j`. -/
def ratLowerOffset (ε : ℕ → ℕ) (j : ℕ) : ℚ :=
  (wordCarry ε j : ℚ) / (3 : ℚ) ^ j

/-- Exact rational upper fractional offset `C_j / 3^j + (1/2) * (2/3)^j` at step `j`. -/
def ratUpperOffset (ε : ℕ → ℕ) (j : ℕ) : ℚ :=
  ratLowerOffset ε j + (1 / 2 : ℚ) * (2 / 3 : ℚ) ^ j

/-- Exact rational cumulative upper endpoint `min_{0 ≤ j ≤ N} ratUpperOffset ε j` at depth `N`. -/
def ratIntervalHi (ε : ℕ → ℕ) (N : ℕ) : ℚ :=
  ((Finset.range (N + 1)).image (ratUpperOffset ε)).min' (by simp)

/-- Coupled node in the exact feasible seed-residue tree at depth `N`,
with enforced equality invariants tying `residue`, `lo`, and `hi` to the
canonical depth-`N` seed residue and rational interval endpoints. -/
structure FeasibleSeedNode (ε : ℕ → ℕ) (N : ℕ) where
  residue : ℕ := seedResidue ε N
  lo : ℚ := ratLowerOffset ε N
  hi : ℚ := ratIntervalHi ε N
  hresidue : residue = seedResidue ε N := by rfl
  hlo : lo = ratLowerOffset ε N := by rfl
  hhi : hi = ratIntervalHi ε N := by rfl

/-- Canonical constructor for `FeasibleSeedNode ε N`. -/
def FeasibleSeedNode.canonical (ε : ℕ → ℕ) (N : ℕ) : FeasibleSeedNode ε N := {}

/-- Every `FeasibleSeedNode ε N` is uniquely determined by `(ε, N)` and equals
`FeasibleSeedNode.canonical ε N`. -/
theorem FeasibleSeedNode.eq_canonical {ε : ℕ → ℕ} {N : ℕ} (node : FeasibleSeedNode ε N) :
    node = FeasibleSeedNode.canonical ε N := by
  cases node with
  | mk res lo hi hres hlo hhi =>
      subst hres; subst hlo; subst hhi; rfl

/-- **Exact Decomposition of `lowerBound` and `upperBound` into Seed + Rational Offset
(`lowerBound_and_upperBound_eq_add_ratOffset`)**:
Whenever `a` matches the parity prefix `ε` up to step `N` (equivalently
`a % 2^N = seedResidue ε N`), for every `j ≤ N`:
1. `lowerBound a j = (a : ℝ) + ((ratLowerOffset ε j : ℚ) : ℝ)`, and
2. `upperBound a j = (a : ℝ) + ((ratUpperOffset ε j : ℚ) : ℝ)`. -/
theorem lowerBound_and_upperBound_eq_add_ratOffset
    {ε : ℕ → ℕ} {a N j : ℕ}
    (hmod : a % 2 ^ N = seedResidue ε N) (hj : j ≤ N) :
    lowerBound a j = (a : ℝ) + ((ratLowerOffset ε j : ℚ) : ℝ) ∧
      upperBound a j = (a : ℝ) + ((ratUpperOffset ε j : ℚ) : ℝ) := by
  have hmatchN := (orbit_parity_match_iff_mod_two_pow_eq_seedResidue ε a N).mpr hmod
  have hmatch_j : ∀ n < j, orbit a n % 2 = ε n % 2 :=
    fun n hn => hmatchN n (lt_of_lt_of_le hn hj)
  have hid := (wordCarry_eq_carry_of_parity_match hmatch_j).2
  have hid_real :
      (2 : ℝ) ^ j * (orbit a j : ℝ) =
        (3 : ℝ) ^ j * (a : ℝ) + (wordCarry ε j : ℝ) := by
    exact_mod_cast hid
  have h3_ne : (3 : ℝ) ^ j ≠ 0 := by positivity
  have h23 : (2 / 3 : ℝ) ^ j = (2 : ℝ) ^ j / (3 : ℝ) ^ j := by
    rw [div_pow]
  have hlo : lowerBound a j = (a : ℝ) + ((ratLowerOffset ε j : ℚ) : ℝ) := by
    unfold lowerBound ratLowerOffset
    push_cast
    rw [h23]
    calc
      (2 : ℝ) ^ j / (3 : ℝ) ^ j * (orbit a j : ℝ) =
          ((2 : ℝ) ^ j * (orbit a j : ℝ)) / (3 : ℝ) ^ j := by ring
      _ = ((3 : ℝ) ^ j * (a : ℝ) + (wordCarry ε j : ℝ)) / (3 : ℝ) ^ j := by
        rw [hid_real]
      _ = (a : ℝ) + (wordCarry ε j : ℝ) / (3 : ℝ) ^ j := by
        field_simp [h3_ne]
        ring
  refine ⟨hlo, ?_⟩
  unfold upperBound ratUpperOffset
  push_cast
  calc
    (2 / 3 : ℝ) ^ j * ((orbit a j : ℝ) + 1 / 2) =
        lowerBound a j + 1 / 2 * (2 / 3 : ℝ) ^ j := by
      unfold lowerBound
      ring
    _ = (a : ℝ) + (((ratLowerOffset ε j : ℚ) : ℝ) + 1 / 2 * (2 / 3 : ℝ) ^ j) := by
      rw [hlo]
      ring

/-- **Exact Rational Feasibility Criterion for the Seed-Residue Tree
(`validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi`)**:
For any parity stream `ε : ℕ → ℕ`, horizon `N : ℕ`, and nonnegative integer seed `a : ℕ`
satisfying `a % 2^N = seedResidue ε N` (in particular `a = seedResidue ε N`),
`(∃ ξ : ℝ, ValidCompanionUpTo a ξ N) ↔ ratLowerOffset ε N < ratIntervalHi ε N`. -/
theorem validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi
    {ε : ℕ → ℕ} {a N : ℕ} (hmod : a % 2 ^ N = seedResidue ε N) :
    (∃ ξ : ℝ, ValidCompanionUpTo a ξ N) ↔
      ratLowerOffset ε N < ratIntervalHi ε N := by
  have hN := lowerBound_and_upperBound_eq_add_ratOffset hmod le_rfl
  constructor
  · rintro ⟨ξ, hξ⟩
    have hmem :
        ratIntervalHi ε N ∈ (Finset.range (N + 1)).image (ratUpperOffset ε) :=
      Finset.min'_mem _ _
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    rcases hmem with ⟨j, hj_lt, hj_eq⟩
    have hj : j ≤ N := by omega
    have hj_bounds := lowerBound_and_upperBound_eq_add_ratOffset hmod hj
    have hcomp_N := (validCompanionAt_iff_bounds a ξ N).mp (hξ N le_rfl)
    have hcomp_j := (validCompanionAt_iff_bounds a ξ j).mp (hξ j hj)
    have hlt_real :
        ((ratLowerOffset ε N : ℚ) : ℝ) < ((ratUpperOffset ε j : ℚ) : ℝ) := by
      linarith [hcomp_N.1, hcomp_j.2, hN.1, hj_bounds.2]
    have hlt_rat : ratLowerOffset ε N < ratUpperOffset ε j := by
      exact_mod_cast hlt_real
    rwa [hj_eq] at hlt_rat
  · intro hlt_rat
    refine ⟨lowerBound a N, ?_⟩
    intro j hj
    rw [validCompanionAt_iff_bounds]
    refine ⟨lowerBound_mono a hj, ?_⟩
    have hj_mem :
        ratUpperOffset ε j ∈ (Finset.range (N + 1)).image (ratUpperOffset ε) := by
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨j, by omega, rfl⟩
    have hmin_le : ratIntervalHi ε N ≤ ratUpperOffset ε j :=
      Finset.min'_le _ _ hj_mem
    have hlt_j : ratLowerOffset ε N < ratUpperOffset ε j :=
      lt_of_lt_of_le hlt_rat hmin_le
    have hlt_real :
        ((ratLowerOffset ε N : ℚ) : ℝ) < ((ratUpperOffset ε j : ℚ) : ℝ) := by
      exact_mod_cast hlt_j
    have hj_bounds := lowerBound_and_upperBound_eq_add_ratOffset hmod hj
    linarith [hN.1, hj_bounds.2, hlt_real]

/-- **Residue-Class Invariance of Finite-Horizon Feasibility (`residue_class_feasibility_iff_seedResidue`)**:
Every nonnegative integer `a` in the congruence class `a % 2^N = seedResidue ε N`
has a valid companion up to horizon `N` if and only if the least residue
`seedResidue ε N` itself has a valid companion up to horizon `N`, which holds
if and only if `ratLowerOffset ε N < ratIntervalHi ε N`. -/
theorem residue_class_feasibility_iff_seedResidue
    {ε : ℕ → ℕ} {a N : ℕ} (hmod : a % 2 ^ N = seedResidue ε N) :
    ((∃ ξ : ℝ, ValidCompanionUpTo a ξ N) ↔
      (∃ ξ : ℝ, ValidCompanionUpTo (seedResidue ε N) ξ N)) ∧
    ((∃ ξ : ℝ, ValidCompanionUpTo (seedResidue ε N) ξ N) ↔
      ratLowerOffset ε N < ratIntervalHi ε N) := by
  have hmod_res : (seedResidue ε N) % 2 ^ N = seedResidue ε N :=
    Nat.mod_eq_of_lt (seedResidue_lt_two_pow ε N)
  have h1 := validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi hmod
  have h2 := validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi hmod_res
  exact ⟨h1.trans h2.symm, h2⟩

/-! ## 6. Exact Odd-Quotient Transition, the $u_m = 1$ Mod-8 Trap & Well-Founded Descent -/

/-- **Exact Odd-Quotient Transition Identity (`odd_quotient_transition_identity`)**:
Along any `ValidBlockChain a_0 s u K`, for every `m` with `m + 1 < K`:
`2 ^ (s (m + 1)) * u (m + 1) = 3 ^ (s m) * u m + 1`. -/
theorem odd_quotient_transition_identity
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : m + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (s (m + 1)) * u (m + 1) = 3 ^ (s m) * u m + 1 := by
  rcases hchain m (by omega) with ⟨hsm, _, hdecomp_m⟩
  rcases hchain (m + 1) hm1 with ⟨_, _, hdecomp_m1⟩
  have horb_m1 : orbit a_0 (blockSteps s (m + 1)) = 3 ^ (s m - 1) * u m := by
    have hsteps : blockSteps s (m + 1) = blockSteps s m + s m := rfl
    rw [hsteps, orbit_add]
    exact orbit_odd_block_return hsm hdecomp_m
  have hpow3 : 3 * 3 ^ (s m - 1) = 3 ^ (s m) := by
    have hsm_eq : s m = (s m - 1) + 1 := by omega
    conv_rhs => rw [hsm_eq, Nat.pow_succ]
    ring
  calc
    2 ^ (s (m + 1)) * u (m + 1) = 3 * orbit a_0 (blockSteps s (m + 1)) + 1 :=
      hdecomp_m1.symm
    _ = 3 * (3 ^ (s m - 1) * u m) + 1 := by rw [horb_m1]
    _ = (3 * 3 ^ (s m - 1)) * u m + 1 := by ring
    _ = 3 ^ (s m) * u m + 1 := by rw [hpow3]

/-- **Mod-8 Parity Trap for `3^c + 1` (`three_pow_add_one_not_dvd_eight`)**:
For every natural number `c : ℕ`, `(3^c + 1) % 8 = 2` (when `c` is even) or
`(3^c + 1) % 8 = 4` (when `c` is odd); in particular, `¬ (8 ∣ 3^c + 1)`. -/
theorem three_pow_add_one_not_dvd_eight (c : ℕ) :
    ((3 ^ c + 1) % 8 = 2 ∨ (3 ^ c + 1) % 8 = 4) ∧ ¬ (8 ∣ (3 ^ c + 1)) := by
  have hmod : (3 ^ c + 1) % 8 = 2 ∨ (3 ^ c + 1) % 8 = 4 := by
    induction c with
    | zero => decide
    | succ c ih =>
        rw [Nat.pow_succ]
        rcases ih with h2 | h4 <;> omega
  refine ⟨hmod, ?_⟩
  rintro ⟨q, hq⟩
  rcases hmod with h2 | h4 <;> omega

/-- **The `u_m = 1` Return Trap (`odd_quotient_one_forces_short_next_block`)**:
Along any `ValidBlockChain a_0 s u K` (`m + 1 < K`):
1. If `u m = 1`, then `s (m + 1) ≤ 2` (no block of length `≥ 3` can follow `u m = 1`), and
2. Equivalently, if `3 ≤ s (m + 1)`, then `3 ≤ u m`. -/
theorem odd_quotient_one_forces_short_next_block
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : m + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    (u m = 1 → s (m + 1) ≤ 2) ∧ (3 ≤ s (m + 1) → 3 ≤ u m) := by
  have htrans := odd_quotient_transition_identity hm1 hchain
  have h1 : u m = 1 → s (m + 1) ≤ 2 := by
    intro hum1
    rw [hum1, Nat.mul_one] at htrans
    by_contra hge3
    have h3 : 3 ≤ s (m + 1) := by omega
    have hdvd8 : 8 ∣ 2 ^ (s (m + 1)) := by
      change 2 ^ 3 ∣ 2 ^ (s (m + 1))
      exact Nat.pow_dvd_pow 2 h3
    have hdvd_sum : 8 ∣ (3 ^ (s m) + 1) :=
      dvd_trans hdvd8 ⟨u (m + 1), htrans.symm⟩
    exact (three_pow_add_one_not_dvd_eight (s m)).2 hdvd_sum
  refine ⟨h1, ?_⟩
  intro hs3
  rcases hchain m (by omega) with ⟨_, hum_odd, _⟩
  have hne1 : u m ≠ 1 := fun hum1 => by
    have hle2 := h1 hum1
    omega
  omega

/-- **Strict Well-Founded Odd-Quotient Descent (`odd_quotient_strict_descent_of_exp_growth`)**:
Along any `ValidBlockChain a_0 s u K` (`m + 1 < K`), whenever `3 ≤ s (m + 1)` and
`3 ^ (s m) < 2 ^ (s (m + 1))`, the odd quotient `u` strictly decreases by at least `2`:
`u (m + 1) + 2 ≤ u m`. -/
theorem odd_quotient_strict_descent_of_exp_growth
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : m + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs_next : 3 ≤ s (m + 1))
    (hgrowth : 3 ^ (s m) < 2 ^ (s (m + 1))) :
    u (m + 1) + 2 ≤ u m := by
  have hu_ge3 : 3 ≤ u m :=
    (odd_quotient_one_forces_short_next_block hm1 hchain).2 hs_next
  have htrans := odd_quotient_transition_identity hm1 hchain
  have hle_pow : 3 ^ (s m) + 1 ≤ 2 ^ (s (m + 1)) := by omega
  have hmul_lt :
      2 ^ (s (m + 1)) * u (m + 1) < 2 ^ (s (m + 1)) * u m := by
    calc
      2 ^ (s (m + 1)) * u (m + 1) = 3 ^ (s m) * u m + 1 := htrans
      _ ≤ (2 ^ (s (m + 1)) - 1) * u m + 1 := by
        have h : 3 ^ (s m) ≤ 2 ^ (s (m + 1)) - 1 := by omega
        have hm := Nat.mul_le_mul_right (u m) h
        omega
      _ < 2 ^ (s (m + 1)) * u m := by
        have hpos : 1 ≤ 2 ^ (s (m + 1)) := Nat.pow_pos (by decide)
        rw [Nat.sub_mul, Nat.one_mul]
        have h2 : u m ≤ 2 ^ (s (m + 1)) * u m := Nat.le_mul_of_pos_left _ hpos
        omega
  have hlt_u : u (m + 1) < u m :=
    Nat.lt_of_mul_lt_mul_left hmul_lt
  rcases hchain m (by omega) with ⟨_, hum_odd, _⟩
  rcases hchain (m + 1) hm1 with ⟨_, hum1_odd, _⟩
  omega

/-- Iterated odd-quotient descent over `M` rapid-growth blocks:
`u (m_0 + M) + 2 * M ≤ u m_0`. -/
theorem odd_quotient_iterated_descent
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m_0 M : ℕ}
    (hMK : m_0 + M < K) (hchain : ValidBlockChain a_0 s u K)
    (hgrowth : ∀ m, m_0 ≤ m → m < m_0 + M →
      3 ≤ s (m + 1) ∧ 3 ^ (s m) < 2 ^ (s (m + 1))) :
    u (m_0 + M) + 2 * M ≤ u m_0 := by
  induction M with
  | zero => simp
  | succ M ih =>
      have ihM := ih (by omega) (fun m hm1 hm2 => hgrowth m hm1 (by omega))
      rcases hgrowth (m_0 + M) (by omega) (by omega) with ⟨hs3, hexp⟩
      have hstep :=
        odd_quotient_strict_descent_of_exp_growth (by omega : (m_0 + M) + 1 < K) hchain hs3 hexp
      have hidx : (m_0 + M) + 1 = m_0 + (M + 1) := by omega
      rw [hidx] at hstep
      omega

/-- **Unconditional Infinite-Horizon Exclusion of the Rapid-Growth Nonperiodic Family
(`no_infinite_rapid_growth_block_chain`)**:
Via the well-founded natural-number ranking `u m : ℕ` and the `u m = 1` mod-8 trap,
for **any** block sequence `s : ℕ → ℕ` and start index `m_0 : ℕ` satisfying
`∀ m ≥ m_0, 3 ≤ s (m + 1) ∧ 3 ^ (s m) < 2 ^ (s (m + 1))` (a broad nonperiodic,
unbalanced, repetition-free class), and **any** integer seed `a_0 : ℕ`, there is
**no** infinite valid integer block chain `∀ K, ValidBlockChain a_0 s u K`. -/
theorem no_infinite_rapid_growth_block_chain
    {a_0 m_0 : ℕ} {s : ℕ → ℕ}
    (hgrowth : ∀ m ≥ m_0, 3 ≤ s (m + 1) ∧ 3 ^ (s m) < 2 ^ (s (m + 1))) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 s u K) := by
  rintro ⟨u, hchain⟩
  set M := u m_0 + 1
  have hdesc :=
    odd_quotient_iterated_descent (K := m_0 + M + 1) (m_0 := m_0) (M := M)
      (Nat.lt_succ_self (m_0 + M)) (hchain (m_0 + M + 1))
      (fun m hm _ => hgrowth m hm)
  omega

/-! ## 7. Full Companion-Set Membership, Signed Integer Margin $D_N$, Coupled Quotient Transitions & General Escape Equivalence -/

/-- **Exact Full Companion-Set Membership Theorem (`validCompanionUpTo_add_offset_iff_mem_ratInterval`)**:
Whenever `a % 2^N = seedResidue ε N`, a real number `(a : ℝ) + x` is a valid companion
for `a` up to horizon `N` if and only if the offset `x` lies in the half-open rational
interval `[ratLowerOffset ε N, ratIntervalHi ε N)`. -/
theorem validCompanionUpTo_add_offset_iff_mem_ratInterval
    {ε : ℕ → ℕ} {a N : ℕ} {x : ℝ} (hmod : a % 2 ^ N = seedResidue ε N) :
    ValidCompanionUpTo a ((a : ℝ) + x) N ↔
      (((ratLowerOffset ε N : ℚ) : ℝ) ≤ x ∧ x < ((ratIntervalHi ε N : ℚ) : ℝ)) := by
  have hN := lowerBound_and_upperBound_eq_add_ratOffset hmod le_rfl
  constructor
  · intro hξ
    have hcomp_N := (validCompanionAt_iff_bounds a ((a : ℝ) + x) N).mp (hξ N le_rfl)
    have hlo : ((ratLowerOffset ε N : ℚ) : ℝ) ≤ x := by linarith [hcomp_N.1, hN.1]
    have hmem :
        ratIntervalHi ε N ∈ (Finset.range (N + 1)).image (ratUpperOffset ε) :=
      Finset.min'_mem _ _
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    rcases hmem with ⟨j, hj_lt, hj_eq⟩
    have hj : j ≤ N := by omega
    have hj_bounds := lowerBound_and_upperBound_eq_add_ratOffset hmod hj
    have hcomp_j := (validCompanionAt_iff_bounds a ((a : ℝ) + x) j).mp (hξ j hj)
    have hhi_j : x < ((ratUpperOffset ε j : ℚ) : ℝ) := by linarith [hcomp_j.2, hj_bounds.2]
    rw [hj_eq] at hhi_j
    exact ⟨hlo, hhi_j⟩
  · rintro ⟨hlo, hhi⟩ j hj
    rw [validCompanionAt_iff_bounds]
    have hj_bounds := lowerBound_and_upperBound_eq_add_ratOffset hmod hj
    have hlo_mono : lowerBound a j ≤ lowerBound a N := lowerBound_mono a hj
    have hj_mem :
        ratUpperOffset ε j ∈ (Finset.range (N + 1)).image (ratUpperOffset ε) := by
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨j, by omega, rfl⟩
    have hmin_le : ratIntervalHi ε N ≤ ratUpperOffset ε j :=
      Finset.min'_le _ _ hj_mem
    have hmin_real : ((ratIntervalHi ε N : ℚ) : ℝ) ≤ ((ratUpperOffset ε j : ℚ) : ℝ) := by
      exact_mod_cast hmin_le
    refine ⟨by linarith [hlo_mono, hN.1, hlo], by linarith [hj_bounds.2, hhi, hmin_real]⟩

/-- Rational-offset specialization of `validCompanionUpTo_add_offset_iff_mem_ratInterval`. -/
theorem validCompanionUpTo_add_rat_offset_iff_mem_ratInterval
    {ε : ℕ → ℕ} {a N : ℕ} {x : ℚ} (hmod : a % 2 ^ N = seedResidue ε N) :
    ValidCompanionUpTo a ((a : ℝ) + (x : ℝ)) N ↔
      (ratLowerOffset ε N ≤ x ∧ x < ratIntervalHi ε N) := by
  rw [validCompanionUpTo_add_offset_iff_mem_ratInterval hmod]
  exact ⟨fun ⟨h1, h2⟩ => ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    fun ⟨h1, h2⟩ => ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩⟩

/-- Base value `ratIntervalHi ε 0 = 1 / 2`. -/
@[simp] theorem ratIntervalHi_zero (ε : ℕ → ℕ) :
    ratIntervalHi ε 0 = (1 / 2 : ℚ) := by
  unfold ratIntervalHi ratUpperOffset ratLowerOffset
  simp [wordCarry]

/-- Step recurrence for the cumulative rational upper endpoint:
`ratIntervalHi ε (N + 1) = min (ratIntervalHi ε N) (ratUpperOffset ε (N + 1))`. -/
theorem ratIntervalHi_succ (ε : ℕ → ℕ) (N : ℕ) :
    ratIntervalHi ε (N + 1) = min (ratIntervalHi ε N) (ratUpperOffset ε (N + 1)) := by
  apply le_antisymm
  · apply le_min
    · have hmem :
          ratIntervalHi ε N ∈ (Finset.range (N + 1)).image (ratUpperOffset ε) :=
        Finset.min'_mem _ _
      simp only [Finset.mem_image, Finset.mem_range] at hmem
      rcases hmem with ⟨j, hj_lt, hj_eq⟩
      rw [← hj_eq]
      apply Finset.min'_le
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨j, by omega, rfl⟩
    · apply Finset.min'_le
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨N + 1, by omega, rfl⟩
  · have hmem :
        ratIntervalHi ε (N + 1) ∈ (Finset.range (N + 2)).image (ratUpperOffset ε) :=
      Finset.min'_mem _ _
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    rcases hmem with ⟨j, hj_lt, hj_eq⟩
    rw [← hj_eq]
    rcases (by omega : j < N + 1 ∨ j = N + 1) with hj_le | rfl
    · refine le_trans (min_le_left _ _) ?_
      apply Finset.min'_le
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨j, hj_le, rfl⟩
    · exact min_le_right _ _

/-- Denominator-cleared integer upper scale `M_N = 2 * 3^N * ratIntervalHi ε N`. -/
def signedUpperScale (ε : ℕ → ℕ) : ℕ → ℤ
  | 0 => 1
  | N + 1 =>
      min (3 * signedUpperScale ε N)
        (2 * (wordCarry ε (N + 1) : ℤ) + (2 : ℤ) ^ (N + 1))

/-- **Signed Denominator-Cleared Integer Feasibility Margin (`signedMargin`)**:
`D_0 = 1` and `D_{N+1} = min(2^{N+1}, 3 * D_N - 2^{N+1} * (ε_N mod 2))`. -/
def signedMargin (ε : ℕ → ℕ) : ℕ → ℤ
  | 0 => 1
  | N + 1 =>
      min ((2 : ℤ) ^ (N + 1))
        (3 * signedMargin ε N - (2 : ℤ) ^ (N + 1) * ((ε N % 2 : ℕ) : ℤ))

/-- Exact algebraic identity `signedMargin ε N = signedUpperScale ε N - 2 * wordCarry ε N`. -/
theorem signedMargin_eq_signedUpperScale_sub (ε : ℕ → ℕ) (N : ℕ) :
    signedMargin ε N = signedUpperScale ε N - 2 * (wordCarry ε N : ℤ) := by
  induction N with
  | zero => simp [signedMargin, signedUpperScale, wordCarry]
  | succ N ih =>
      simp only [signedMargin, signedUpperScale, wordCarry]
      rw [ih, min_comm]
      have hcarry :
          (2 : ℤ) * ((3 * wordCarry ε N + 2 ^ N * (ε N % 2) : ℕ) : ℤ) =
            6 * (wordCarry ε N : ℤ) + (2 : ℤ) ^ (N + 1) * ((ε N % 2 : ℕ) : ℤ) := by
        push_cast
        rw [pow_succ]
        ring
      omega

/-- Exact rational identity `(signedUpperScale ε N : ℚ) = 2 * 3^N * ratIntervalHi ε N`. -/
theorem signedUpperScale_cast_rat (ε : ℕ → ℕ) (N : ℕ) :
    (signedUpperScale ε N : ℚ) = 2 * (3 : ℚ) ^ N * ratIntervalHi ε N := by
  induction N with
  | zero => simp [signedUpperScale]
  | succ N ih =>
      rw [ratIntervalHi_succ]
      simp only [signedUpperScale, Int.cast_min, Int.cast_mul, Int.cast_add,
        Int.cast_ofNat, Int.cast_natCast, Int.cast_pow]
      have hpos : (0 : ℚ) ≤ 2 * (3 : ℚ) ^ (N + 1) := by positivity
      rw [mul_min_of_nonneg _ _ hpos]
      congr 1
      · rw [pow_succ, ih]
        ring
      · unfold ratUpperOffset ratLowerOffset
        have h3_ne : (3 : ℚ) ^ (N + 1) ≠ 0 := by positivity
        rw [div_pow]
        field_simp [h3_ne]
        ring

/-- **Exact Denominator-Cleared Margin Identity (`signedMargin_cast_rat`)**:
For every parity stream `ε : ℕ → ℕ` and horizon `N : ℕ`:
`(signedMargin ε N : ℚ) = 2 * 3^N * (ratIntervalHi ε N - ratLowerOffset ε N)`. -/
theorem signedMargin_cast_rat (ε : ℕ → ℕ) (N : ℕ) :
    (signedMargin ε N : ℚ) =
      2 * (3 : ℚ) ^ N * (ratIntervalHi ε N - ratLowerOffset ε N) := by
  rw [signedMargin_eq_signedUpperScale_sub, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, signedUpperScale_cast_rat]
  unfold ratLowerOffset
  have h3_ne : (3 : ℚ) ^ N ≠ 0 := by positivity
  field_simp [h3_ne]
  ring

/-- **Exact Integer Margin Feasibility Equivalence (`signedMargin_pos_iff_ratLowerOffset_lt_ratIntervalHi`)**:
Finite-horizon feasibility `ratLowerOffset ε N < ratIntervalHi ε N` holds if and only if
the integer margin satisfies `0 < signedMargin ε N`. -/
theorem signedMargin_pos_iff_ratLowerOffset_lt_ratIntervalHi (ε : ℕ → ℕ) (N : ℕ) :
    0 < signedMargin ε N ↔ ratLowerOffset ε N < ratIntervalHi ε N := by
  have hcast : (0 : ℚ) < (signedMargin ε N : ℚ) ↔ 0 < signedMargin ε N := by
    exact_mod_cast Iff.rfl
  rw [← hcast, signedMargin_cast_rat]
  have hpos : (0 : ℚ) < 2 * (3 : ℚ) ^ N := by positivity
  rw [mul_pos_iff_of_pos_left hpos, sub_pos]

/-- **Exact Companion Feasibility via `signedMargin` (`validCompanionUpTo_iff_signedMargin_pos`)**:
Whenever `a % 2^N = seedResidue ε N`, `(∃ ξ : ℝ, ValidCompanionUpTo a ξ N) ↔ 0 < signedMargin ε N`. -/
theorem validCompanionUpTo_iff_signedMargin_pos
    {ε : ℕ → ℕ} {a N : ℕ} (hmod : a % 2 ^ N = seedResidue ε N) :
    (∃ ξ : ℝ, ValidCompanionUpTo a ξ N) ↔ 0 < signedMargin ε N := by
  rw [validCompanionUpTo_iff_ratLowerOffset_lt_ratIntervalHi hmod,
    signedMargin_pos_iff_ratLowerOffset_lt_ratIntervalHi]

/-- **Absorbing Nonpositivity of `signedMargin` (`signedMargin_nonpos_of_nonpos`)**:
Once `signedMargin ε N ≤ 0`, every subsequent margin satisfies
`signedMargin ε (N + 1) = 3 * signedMargin ε N - 2^(N + 1) * (ε N % 2) ≤ 0`,
and by induction `signedMargin ε M ≤ 0` for all `M ≥ N`. -/
theorem signedMargin_nonpos_of_nonpos {ε : ℕ → ℕ} {N : ℕ}
    (hnonpos : signedMargin ε N ≤ 0) :
    signedMargin ε (N + 1) =
      3 * signedMargin ε N - (2 : ℤ) ^ (N + 1) * ((ε N % 2 : ℕ) : ℤ) ∧
    (∀ M ≥ N, signedMargin ε M ≤ 0) := by
  have hstep :
      ∀ k, signedMargin ε k ≤ 0 →
        signedMargin ε (k + 1) =
          3 * signedMargin ε k - (2 : ℤ) ^ (k + 1) * ((ε k % 2 : ℕ) : ℤ) ∧
        signedMargin ε (k + 1) ≤ 0 := by
    intro k hk
    simp only [signedMargin]
    have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ (k + 1) := by positivity
    have hbit_nonneg : (0 : ℤ) ≤ ((ε k % 2 : ℕ) : ℤ) := by positivity
    have hmul_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (k + 1) * ((ε k % 2 : ℕ) : ℤ) :=
      mul_nonneg (le_of_lt hpow_pos) hbit_nonneg
    have hrhs_le : 3 * signedMargin ε k - (2 : ℤ) ^ (k + 1) * ((ε k % 2 : ℕ) : ℤ) ≤ 0 := by
      linarith
    have hmin :
        min ((2 : ℤ) ^ (k + 1))
          (3 * signedMargin ε k - (2 : ℤ) ^ (k + 1) * ((ε k % 2 : ℕ) : ℤ)) =
          3 * signedMargin ε k - (2 : ℤ) ^ (k + 1) * ((ε k % 2 : ℕ) : ℤ) :=
      min_eq_right (by linarith)
    exact ⟨hmin, by linarith⟩
  refine ⟨(hstep N hnonpos).1, ?_⟩
  intro M hM
  induction M with
  | zero =>
      have hN0 : N = 0 := by omega
      subst hN0
      exact hnonpos
  | succ M ih =>
      rcases Nat.eq_or_lt_of_le hM with rfl | hlt
      · exact hnonpos
      · exact (hstep M (ih (by omega))).2

/-- The exact integer orbit quotient `q_N = orbit (seedResidue ε N) N` at depth `N`. -/
def seedQuotient (ε : ℕ → ℕ) (N : ℕ) : ℕ :=
  orbit (seedResidue ε N) N

/-- Exact division relation `2^N * seedQuotient ε N = 3^N * seedResidue ε N + wordCarry ε N`. -/
theorem two_pow_mul_seedQuotient_eq (ε : ℕ → ℕ) (N : ℕ) :
    2 ^ N * seedQuotient ε N = 3 ^ N * seedResidue ε N + wordCarry ε N :=
  (wordCarry_eq_carry_of_parity_match (orbit_seedResidue_mod_two ε N)).2

/-- **Exact Coupled Quotient-Residue-Margin Transition Law (`coupled_seedQuotient_and_margin_transition`)**:
At every depth `N : ℕ`, writing `r_N = seedResidue ε N`, `q_N = seedQuotient ε N`,
`η_N = seedBit ε r_N N`, and `e_N = ε N % 2`:
1. `e_N = (q_N + η_N) % 2`,
2. `seedResidue ε (N + 1) = r_N + η_N * 2^N`,
3. `2 * seedQuotient ε (N + 1) = 3 * q_N + 3^(N + 1) * η_N + e_N`
   (and `seedQuotient ε (N + 1) = (3 * q_N + 3^(N + 1) * η_N + e_N) / 2`),
4. When `η_N = 0`, `seedResidue ε (N + 1) = r_N` and `seedQuotient ε (N + 1) = step q_N`. -/
theorem coupled_seedQuotient_and_margin_transition (ε : ℕ → ℕ) (N : ℕ) :
    ε N % 2 = (seedQuotient ε N + seedBit ε (seedResidue ε N) N) % 2 ∧
      seedResidue ε (N + 1) =
        seedResidue ε N + seedBit ε (seedResidue ε N) N * 2 ^ N ∧
      2 * seedQuotient ε (N + 1) =
        3 * seedQuotient ε N + 3 ^ (N + 1) * seedBit ε (seedResidue ε N) N + (ε N % 2) ∧
      seedQuotient ε (N + 1) =
        (3 * seedQuotient ε N + 3 ^ (N + 1) * seedBit ε (seedResidue ε N) N + (ε N % 2)) / 2 ∧
      (seedBit ε (seedResidue ε N) N = 0 →
        seedResidue ε (N + 1) = seedResidue ε N ∧
          seedQuotient ε (N + 1) = step (seedQuotient ε N)) := by
  have hpar : ε N % 2 = (seedQuotient ε N + seedBit ε (seedResidue ε N) N) % 2 := by
    unfold seedQuotient seedBit
    split_ifs with h <;> omega
  have hres :
      seedResidue ε (N + 1) =
        seedResidue ε N + seedBit ε (seedResidue ε N) N * 2 ^ N := rfl
  have h2q :
      2 * seedQuotient ε (N + 1) =
        3 * seedQuotient ε N + 3 ^ (N + 1) * seedBit ε (seedResidue ε N) N + (ε N % 2) := by
    have horb_N :
        orbit (seedResidue ε (N + 1)) N =
          seedQuotient ε N + 3 ^ N * seedBit ε (seedResidue ε N) N := by
      rw [hres]
      unfold seedQuotient
      unfold seedBit
      split_ifs with h
      · simp
      · have h1 : seedResidue ε N + 1 * 2 ^ N = seedResidue ε N + 2 ^ N := by ring
        rw [h1, orbit_add_two_pow_step_eq]
        ring
    have hmod_N : orbit (seedResidue ε (N + 1)) N % 2 = ε N % 2 :=
      orbit_seedResidue_mod_two ε (N + 1) N (Nat.lt_succ_self N)
    have hstep_id := step_identity (orbit (seedResidue ε (N + 1)) N)
    change 2 * seedQuotient ε (N + 1) =
      3 * orbit (seedResidue ε (N + 1)) N + orbit (seedResidue ε (N + 1)) N % 2 at hstep_id
    rw [hmod_N, horb_N] at hstep_id
    rw [Nat.pow_succ]
    linarith
  have hdiv :
      seedQuotient ε (N + 1) =
        (3 * seedQuotient ε N + 3 ^ (N + 1) * seedBit ε (seedResidue ε N) N + (ε N % 2)) / 2 := by
    rw [← h2q, Nat.mul_div_right _ (by decide : 0 < 2)]
  refine ⟨hpar, hres, h2q, hdiv, ?_⟩
  intro hbit0
  have hres0 : seedResidue ε (N + 1) = seedResidue ε N := by
    rw [hres, hbit0, Nat.zero_mul, Nat.add_zero]
  refine ⟨hres0, ?_⟩
  unfold seedQuotient
  rw [hres0]
  rfl

/-- **General-Case Positive-Stabilized-Branch Escape Equivalence
(`general_mahler_conjecture_iff_positive_stabilized_branch_escape`)**:
Unifies the five principal formulations of the general Mahler $3/2$ problem:
1. **Classical Positive-Real Formulation**: For every real `0 < α`, there exists `n : ℕ`
   with `1 / 2 ≤ Int.fract (α * (3 / 2)^n)`.
2. **Infinite Companion Formulation**: No positive integer `1 ≤ a_0` admits a real `α`
   with `ValidCompanionForever a_0 α`.
3. **Finite-Horizon Seed Escape**: Every positive integer `1 ≤ a_0` fails
   `ValidCompanionUpTo a_0 α N` at some finite horizon `N`.
4. **Positive-Stabilized Seed-Branch Infeasibility (Outline Section 2)**:
   Every parity stream `ε : ℕ → ℕ` whose least-residue sequence `seedResidue ε`
   eventually stabilizes at a positive integer `1 ≤ a_0` eventually hits a
   nonpositive integer margin `signedMargin ε N ≤ 0` (equivalently, every perpetually
   feasible stream `∀ N, 0 < signedMargin ε N` either stabilizes at `0` or takes
   infinitely many strict upward extension steps `seedResidue ε N < seedResidue ε (N + 1)`).
5. **Unbounded Certified Seed Lower Bounds (Outline Section 3)**:
   For every bound `B : ℕ`, there exists a horizon `N : ℕ` with `B ≤ 2^N` such that
   every positive residue `0 < r < B` fails `survivesSteps r N`. -/
theorem general_mahler_conjecture_iff_positive_stabilized_branch_escape :
    ((∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) ↔
      (∀ a_0 : ℕ, 1 ≤ a_0 → ¬ ∃ α : ℝ, ValidCompanionForever a_0 α)) ∧
    ((∀ a_0 : ℕ, 1 ≤ a_0 → ¬ ∃ α : ℝ, ValidCompanionForever a_0 α) ↔
      (∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N)) ∧
    ((∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) ↔
      (∀ ε : ℕ → ℕ,
        (∃ a_0 N_0 : ℕ, 1 ≤ a_0 ∧ ∀ N ≥ N_0, seedResidue ε N = a_0) →
          ∃ N : ℕ, signedMargin ε N ≤ 0)) ∧
    ((∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) ↔
      (∀ B : ℕ, ∃ N : ℕ, B ≤ 2 ^ N ∧
        ∀ r : ℕ, 0 < r → r < B → survivesSteps r N = false)) := by
  have h12 :
      (∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) ↔
        (∀ a_0 : ℕ, 1 ≤ a_0 → ¬ ∃ α : ℝ, ValidCompanionForever a_0 α) := by
    constructor
    · intro hfract a_0 ha0 ⟨α, hforever⟩
      have h0 : ValidCompanionAt a_0 α 0 := hforever 0
      unfold ValidCompanionAt at h0
      simp only [orbit, pow_zero, mul_one] at h0
      have ha0_real : (1 : ℝ) ≤ (a_0 : ℝ) := by exact_mod_cast ha0
      have hα_pos : 0 < α := by linarith [h0.1, ha0_real]
      obtain ⟨n, hn_ge⟩ := hfract α hα_pos
      have hn_lt := ((validCompanionForever_iff_floor_and_forall_fract_lt_half a_0 α).mp hforever).2 n
      linarith
    · intro hno_pos α hα
      by_contra hno
      push_neg at hno
      set a_0 : ℕ := Int.toNat ⌊α⌋
      have hfl_nonneg : 0 ≤ ⌊α⌋ := Int.floor_nonneg.mpr (le_of_lt hα)
      have hfl_eq : ⌊α⌋ = (a_0 : ℤ) := (Int.toNat_of_nonneg hfl_nonneg).symm
      have hforever : ValidCompanionForever a_0 α :=
        (validCompanionForever_iff_floor_and_forall_fract_lt_half a_0 α).mpr ⟨hfl_eq, hno⟩
      obtain ⟨b_0, β, hb0, _, hβ_forever⟩ :=
        exists_positive_seed_ge_one_of_pos_companion hα hforever
      exact hno_pos b_0 hb0 ⟨β, hβ_forever⟩
  have h23 :
      (∀ a_0 : ℕ, 1 ≤ a_0 → ¬ ∃ α : ℝ, ValidCompanionForever a_0 α) ↔
        (∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) := by
    constructor
    · intro hno_inf a_0 ha0
      by_contra hperp
      push_neg at hperp
      obtain ⟨b_0, β, hb0, _, hβ_forever⟩ :=
        exists_positive_infinite_companion_of_perpetual_finite_survival ha0 hperp
      exact hno_inf b_0 hb0 ⟨β, hβ_forever⟩
    · intro hfin a_0 ha0 ⟨α, hforever⟩
      obtain ⟨N, hN⟩ := hfin a_0 ha0
      exact hN ⟨α, fun n _ => hforever n⟩
  have h34 :
      (∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) ↔
        (∀ ε : ℕ → ℕ,
          (∃ a_0 N_0 : ℕ, 1 ≤ a_0 ∧ ∀ N ≥ N_0, seedResidue ε N = a_0) →
            ∃ N : ℕ, signedMargin ε N ≤ 0) := by
    constructor
    · intro hfin ε ⟨a_0, N_0, ha0, hstab⟩
      have hall := (exists_nonneg_seed_iff_seedResidue_stabilizes ε a_0).mpr ⟨N_0, hstab⟩
      obtain ⟨N, hN⟩ := hfin a_0 ha0
      refine ⟨N, ?_⟩
      by_contra hpos
      push_neg at hpos
      have hmod : a_0 % 2 ^ N = seedResidue ε N :=
        (orbit_parity_match_iff_mod_two_pow_eq_seedResidue ε a_0 N).mp (fun n _ => hall n)
      exact hN ((validCompanionUpTo_iff_signedMargin_pos hmod).mpr hpos)
    · intro hbranch a_0 ha0
      set ε : ℕ → ℕ := fun n => orbit a_0 n % 2
      obtain ⟨N_0, hstab⟩ :=
        (exists_nonneg_seed_iff_seedResidue_stabilizes ε a_0).mp (fun _ => by simp [ε])
      obtain ⟨N, hmargin_le⟩ := hbranch ε ⟨a_0, N_0, ha0, hstab⟩
      refine ⟨N, ?_⟩
      have hmod : a_0 % 2 ^ N = seedResidue ε N :=
        (orbit_parity_match_iff_mod_two_pow_eq_seedResidue ε a_0 N).mp (fun _ _ => by simp [ε])
      rw [validCompanionUpTo_iff_signedMargin_pos hmod]
      omega
  have h35 :
      (∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) ↔
        (∀ B : ℕ, ∃ N : ℕ, B ≤ 2 ^ N ∧
          ∀ r : ℕ, 0 < r → r < B → survivesSteps r N = false) := by
    simpa [Nat.succ_le_iff] using every_positive_fails_iff_unbounded_exclusion
  exact ⟨h12, h23, h34, h35⟩

/-- **Parameterized Arithmetic Escape Certificate Interface (`ParameterizedSeedEscapeCertificate`)**:
Given a state invariant `Inv : (ℕ → ℕ) → ℕ → Prop` and a nonnegative integer rank
`rank : (ℕ → ℕ) → ℕ → ℕ` on paths `(ε, N)`, if from every reachable state `(ε, N)`
with `0 < signedMargin ε N` and zero extension bit `seedBit ε (seedResidue ε N) N = 0`,
the next step `(ε, N + 1)` either fails feasibility (`signedMargin ε (N + 1) ≤ 0`) or
preserves `Inv` while strictly decreasing `rank` (`rank ε (N + 1) < rank ε N`), then no
branch starting in `Inv ε N_0` with zero extension bits forever from `N_0` onward can
remain perpetually feasible (`∀ N, 0 < signedMargin ε N`). -/
theorem no_perpetual_feasible_stabilized_branch_of_rank_certificate
    {Inv : (ℕ → ℕ) → ℕ → Prop} {rank : (ℕ → ℕ) → ℕ → ℕ}
    (hstep : ∀ (ε : ℕ → ℕ) (N : ℕ),
      Inv ε N → 0 < signedMargin ε N → seedBit ε (seedResidue ε N) N = 0 →
        signedMargin ε (N + 1) ≤ 0 ∨ (Inv ε (N + 1) ∧ rank ε (N + 1) < rank ε N))
    {ε : ℕ → ℕ} {N_0 : ℕ}
    (hinit : Inv ε N_0)
    (hzero_tail : ∀ N ≥ N_0, seedBit ε (seedResidue ε N) N = 0) :
    ∃ N ≥ N_0, signedMargin ε N ≤ 0 := by
  by_contra hperp
  push_neg at hperp
  have hdesc : ∀ k : ℕ, Inv ε (N_0 + k) ∧ rank ε (N_0 + k) + k ≤ rank ε N_0 := by
    intro k
    induction k with
    | zero => simp [hinit]
    | succ k ih =>
        rcases ih with ⟨hinv_k, hrank_k⟩
        have hpos_k : 0 < signedMargin ε (N_0 + k) := hperp (N_0 + k) (by omega)
        have hbit_k : seedBit ε (seedResidue ε (N_0 + k)) (N_0 + k) = 0 :=
          hzero_tail (N_0 + k) (by omega)
        rcases hstep ε (N_0 + k) hinv_k hpos_k hbit_k with hfail | ⟨hinv_next, hlt_next⟩
        · have hpos_next : 0 < signedMargin ε (N_0 + k + 1) := hperp (N_0 + k + 1) (by omega)
          omega
        · have hidx : N_0 + (k + 1) = N_0 + k + 1 := by omega
          rw [hidx]
          exact ⟨hinv_next, by omega⟩
  have hcontra := (hdesc (rank ε N_0 + 1)).2
  omega

/-- Tail-recursive single-pass loop advancing `(orb, p2, D)` by `k` steps in $O(k)$ kernel reductions. -/
def fastSeedLoop (orb : ℕ) (p2 D : ℤ) : ℕ → ℕ × ℤ × ℤ
  | 0 => (orb, p2, D)
  | k + 1 =>
      fastSeedLoop (step orb) (2 * p2)
        (min (2 * p2) (3 * D - (2 * p2) * ((orb % 2 : ℕ) : ℤ))) k

/-- Tail-recursive short-circuiting Boolean survival check advancing `(orb, p2, D)` by `k` steps
and returning `false` as soon as `D ≤ 0`. -/
def fastSeedSurvivesLoop (orb : ℕ) (p2 D : ℤ) : ℕ → Bool
  | 0 => decide (0 < D)
  | k + 1 =>
      if D ≤ 0 then false
      else
        fastSeedSurvivesLoop (step orb) (2 * p2)
          (min (2 * p2) (3 * D - (2 * p2) * ((orb % 2 : ℕ) : ℤ))) k

/-- Single-pass computable state `(orbit m N, 2^N, signedMargin (fun n => orbit m n % 2) N)`. -/
def fastSeedState (m N : ℕ) : ℕ × ℤ × ℤ :=
  fastSeedLoop m 1 1 N

/-- Fast computable Boolean check for `N`-step survival of seed `m`. -/
def fastSeedSurvives (m N : ℕ) : Bool :=
  fastSeedSurvivesLoop m 1 1 N

theorem fastSeedLoop_eq (m : ℕ) :
    ∀ j k : ℕ,
      fastSeedLoop (orbit m j) ((2 : ℤ) ^ j)
        (signedMargin (fun n => orbit m n % 2) j) k =
        (orbit m (j + k), (2 : ℤ) ^ (j + k),
          signedMargin (fun n => orbit m n % 2) (j + k)) := by
  intro j k
  induction k generalizing j with
  | zero => simp [fastSeedLoop]
  | succ k ih =>
      simp only [fastSeedLoop]
      have horb : step (orbit m j) = orbit m (j + 1) := rfl
      have hp2 : (2 : ℤ) * (2 : ℤ) ^ j = (2 : ℤ) ^ (j + 1) := by rw [pow_succ']
      have hmod : (orbit m j % 2) % 2 = orbit m j % 2 := by omega
      have hD :
          min ((2 : ℤ) ^ (j + 1))
            (3 * signedMargin (fun n => orbit m n % 2) j -
              (2 : ℤ) ^ (j + 1) * ((orbit m j % 2 : ℕ) : ℤ)) =
            signedMargin (fun n => orbit m n % 2) (j + 1) := by
        simp [signedMargin, hmod]
      rw [horb, hp2, hD, ih (j + 1)]
      have hidx : j + 1 + k = j + (k + 1) := by omega
      rw [hidx]

/-- Exactness of `fastSeedState`: its components equal `orbit m N`, `2^N`, and
`signedMargin (fun n => orbit m n % 2) N`. -/
theorem fastSeedState_eq (m N : ℕ) :
    fastSeedState m N =
      (orbit m N, (2 : ℤ) ^ N, signedMargin (fun n => orbit m n % 2) N) := by
  simpa [fastSeedState, orbit, signedMargin] using fastSeedLoop_eq m 0 N

theorem fastSeedSurvivesLoop_eq (m : ℕ) :
    ∀ j k : ℕ,
      fastSeedSurvivesLoop (orbit m j) ((2 : ℤ) ^ j)
        (signedMargin (fun n => orbit m n % 2) j) k =
        decide (0 < signedMargin (fun n => orbit m n % 2) (j + k)) := by
  intro j k
  induction k generalizing j with
  | zero => simp [fastSeedSurvivesLoop]
  | succ k ih =>
      simp only [fastSeedSurvivesLoop]
      split_ifs with hnonpos
      · have hle := (signedMargin_nonpos_of_nonpos hnonpos).2 (j + (k + 1)) (by omega)
        simp [not_lt.mpr hle]
      · have horb : step (orbit m j) = orbit m (j + 1) := rfl
        have hp2 : (2 : ℤ) * (2 : ℤ) ^ j = (2 : ℤ) ^ (j + 1) := by rw [pow_succ']
        have hmod : (orbit m j % 2) % 2 = orbit m j % 2 := by omega
        have hD :
            min ((2 : ℤ) ^ (j + 1))
              (3 * signedMargin (fun n => orbit m n % 2) j -
                (2 : ℤ) ^ (j + 1) * ((orbit m j % 2 : ℕ) : ℤ)) =
              signedMargin (fun n => orbit m n % 2) (j + 1) := by
          simp [signedMargin, hmod]
        rw [horb, hp2, hD, ih (j + 1)]
        have hidx : j + 1 + k = j + (k + 1) := by omega
        rw [hidx]

/-- **Exact Equivalence of `fastSeedSurvives`, `survivesSteps`, and `ValidCompanionUpTo`
(`fastSeedSurvives_iff_validCompanionUpTo`)**:
For every seed `m : ℕ` and horizon `N : ℕ`, `fastSeedSurvives m N = survivesSteps m N`,
and `fastSeedSurvives m N = true ↔ ∃ ξ : ℝ, ValidCompanionUpTo m ξ N`. -/
theorem fastSeedSurvives_iff_validCompanionUpTo (m N : ℕ) :
    (fastSeedSurvives m N = true ↔ ∃ ξ : ℝ, ValidCompanionUpTo m ξ N) ∧
      fastSeedSurvives m N = survivesSteps m N := by
  have hmod : m % 2 ^ N = seedResidue (fun n => orbit m n % 2) N :=
    (orbit_parity_match_iff_mod_two_pow_eq_seedResidue (fun n => orbit m n % 2) m N).mp
      (fun _ _ => by simp)
  have hloop :
      fastSeedSurvives m N = decide (0 < signedMargin (fun n => orbit m n % 2) N) := by
    simpa [fastSeedSurvives, orbit, signedMargin] using fastSeedSurvivesLoop_eq m 0 N
  have h1 : fastSeedSurvives m N = true ↔ 0 < signedMargin (fun n => orbit m n % 2) N := by
    rw [hloop, decide_eq_true_eq]
  have h2 := (validCompanionUpTo_iff_signedMargin_pos hmod).symm
  have h3 := h1.trans h2
  have hsurv : fastSeedSurvives m N = true ↔ survivesSteps m N = true := by
    rw [h3, exists_validCompanionUpTo_iff_integerPinch, survivesSteps_eq_true_iff]
  refine ⟨h3, ?_⟩
  cases hfast : fastSeedSurvives m N <;> cases hst : survivesSteps m N <;>
    simp_all

/-- **Certified Extremal Seed `149` Horizon-28 Survival and Horizon-29 Failure
(`seed_149_survives_28_and_fails_29`)**:
Certifies in Lean that seed `149` (the extremal survivor in `1 ≤ m < 4096`) admits
a valid real companion through step `28` (`fastSeedSurvives 149 28 = true`) and fails
at step `29` (`fastSeedSurvives 149 29 = false`). -/
theorem seed_149_survives_28_and_fails_29 :
    fastSeedSurvives 149 28 = true ∧
      fastSeedSurvives 149 29 = false ∧
      (∃ ξ : ℝ, ValidCompanionUpTo 149 ξ 28) ∧
      ¬ (∃ ξ : ℝ, ValidCompanionUpTo 149 ξ 29) := by
  have hs28 : fastSeedSurvives 149 28 = true := by decide
  have hs29 : fastSeedSurvives 149 29 = false := by decide
  refine ⟨hs28, hs29, (fastSeedSurvives_iff_validCompanionUpTo 149 28).1.mp hs28, ?_⟩
  intro hcomp29
  have htrue := (fastSeedSurvives_iff_validCompanionUpTo 149 29).1.mpr hcomp29
  rw [hs29] at htrue
  cases htrue

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
private theorem below_4096_fast_excluded_at_29_blocks :
    ∀ hi : Fin 64, ∀ lo : Fin 64,
      0 < 64 * hi.val + lo.val →
        fastSeedSurvives (64 * hi.val + lo.val) 29 = false := by
  decide

private theorem below_4096_fast_excluded_at_29 {r : ℕ} (hr0 : 0 < r) (hr4096 : r < 4096) :
    fastSeedSurvives r 29 = false := by
  have hhi : r / 64 < 64 := by omega
  have hlo : r % 64 < 64 := by omega
  have hdecomp : 64 * (r / 64) + r % 64 = r := Nat.div_add_mod r 64
  have hpos : 0 < 64 * (⟨r / 64, hhi⟩ : Fin 64).val + (⟨r % 64, hlo⟩ : Fin 64).val := by
    simpa [hdecomp] using hr0
  have h := below_4096_fast_excluded_at_29_blocks ⟨r / 64, hhi⟩ ⟨r % 64, hlo⟩ hpos
  simpa [hdecomp] using h

/-- **Certified Global Bound at Step 29 (`positive_survivor_step29_ge_4096`)**:
Certifies the bounded-seed experiment in Lean: every positive residue `0 < r < 4096`
fails by horizon `29`, and therefore **every** positive integer `m > 0` (including
arbitrary `m ≥ 2^29`) that admits a valid Mahler companion up to step `29` satisfies
`4096 ≤ m` (`2^12 ≤ m`). -/
theorem positive_survivor_step29_ge_4096 {m : ℕ} (hm : 0 < m)
    (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo m ξ 29) :
    4096 ≤ m := by
  refine positive_survivor_ge_of_residues_excluded hm (by decide : 4096 ≤ 2 ^ 29) ?_ hsurv
  intro r hr0 hr4096
  rw [← (fastSeedSurvives_iff_validCompanionUpTo r 29).2]
  exact below_4096_fast_excluded_at_29 hr0 hr4096

/-- For every horizon `N : ℕ`, the positive seed `2^N` survives through step `N`. -/
theorem two_pow_survives_horizon (N : ℕ) :
    0 < 2 ^ N ∧
      (∃ ξ : ℝ, ValidCompanionUpTo (2 ^ N) ξ N) ∧
      survivesSteps (2 ^ N) N = true := by
  have hpos : 0 < 2 ^ N := Nat.pow_pos (by decide)
  have h0 : ∃ ξ : ℝ, ValidCompanionUpTo 0 ξ N :=
    ⟨0, fun n _ => zero_seed_all_zero_exception.2.2 n⟩
  have hcomp : ∃ ξ : ℝ, ValidCompanionUpTo (2 ^ N) ξ N := by
    rw [exists_validCompanionUpTo_mod_two_pow_iff (2 ^ N) N, Nat.mod_self]
    exact h0
  have hsurv : survivesSteps (2 ^ N) N = true := by
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact hcomp
  exact ⟨hpos, hcomp, hsurv⟩

/-- **The Least Positive Surviving Seed `B(N)` (`leastPositiveSurvivor`)**:
The smallest positive integer `m > 0` admitting a valid Mahler companion through horizon `N`. -/
noncomputable def leastPositiveSurvivor (N : ℕ) : ℕ :=
  Nat.find (⟨2 ^ N, (two_pow_survives_horizon N).1, (two_pow_survives_horizon N).2.2⟩ :
    ∃ m : ℕ, 0 < m ∧ survivesSteps m N = true)

/-- Basic properties of `leastPositiveSurvivor N`:
1. `1 ≤ leastPositiveSurvivor N ≤ 2^N`,
2. `leastPositiveSurvivor N` survives through horizon `N`, and
3. Every positive seed `m > 0` surviving through horizon `N` satisfies `leastPositiveSurvivor N ≤ m`. -/
theorem leastPositiveSurvivor_spec (N : ℕ) :
    1 ≤ leastPositiveSurvivor N ∧
      leastPositiveSurvivor N ≤ 2 ^ N ∧
      (∃ ξ : ℝ, ValidCompanionUpTo (leastPositiveSurvivor N) ξ N) ∧
      (∀ m : ℕ, 0 < m → (∃ ξ : ℝ, ValidCompanionUpTo m ξ N) →
        leastPositiveSurvivor N ≤ m) := by
  have hex : ∃ m : ℕ, 0 < m ∧ survivesSteps m N = true :=
    ⟨2 ^ N, (two_pow_survives_horizon N).1, (two_pow_survives_horizon N).2.2⟩
  have hspec := Nat.find_spec hex
  have hle_pow : leastPositiveSurvivor N ≤ 2 ^ N :=
    Nat.find_min' hex ⟨(two_pow_survives_horizon N).1, (two_pow_survives_horizon N).2.2⟩
  have hcomp : ∃ ξ : ℝ, ValidCompanionUpTo (leastPositiveSurvivor N) ξ N := by
    rw [exists_validCompanionUpTo_iff_integerPinch, ← survivesSteps_eq_true_iff]
    exact hspec.2
  refine ⟨hspec.1, hle_pow, hcomp, ?_⟩
  intro m hm hm_comp
  have hm_surv : survivesSteps m N = true := by
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact hm_comp
  exact Nat.find_min' hex ⟨hm, hm_surv⟩

/-- **Monotonicity of `leastPositiveSurvivor` (`leastPositiveSurvivor_mono`)**:
Whenever `N₁ ≤ N₂`, `leastPositiveSurvivor N₁ ≤ leastPositiveSurvivor N₂`. -/
theorem leastPositiveSurvivor_mono {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    leastPositiveSurvivor N₁ ≤ leastPositiveSurvivor N₂ := by
  rcases leastPositiveSurvivor_spec N₂ with ⟨hpos2, _, ⟨ξ, hξ2⟩, _⟩
  exact (leastPositiveSurvivor_spec N₁).2.2.2 (leastPositiveSurvivor N₂) hpos2
    ⟨ξ, validCompanionUpTo_mono hN hξ2⟩

/-- **Certified Lower Bounds on `leastPositiveSurvivor` (`leastPositiveSurvivor_certified_bounds`)**:
`4 ≤ leastPositiveSurvivor 4`, `53 ≤ leastPositiveSurvivor 12`, and
`4096 ≤ leastPositiveSurvivor 29`. -/
theorem leastPositiveSurvivor_certified_bounds :
    4 ≤ leastPositiveSurvivor 4 ∧
      53 ≤ leastPositiveSurvivor 12 ∧
      4096 ≤ leastPositiveSurvivor 29 := by
  rcases leastPositiveSurvivor_spec 4 with ⟨hpos4, _, hcomp4, _⟩
  rcases leastPositiveSurvivor_spec 12 with ⟨hpos12, _, hcomp12, _⟩
  rcases leastPositiveSurvivor_spec 29 with ⟨hpos29, _, hcomp29, _⟩
  exact ⟨positive_survivor_step4_ge_4 hpos4 hcomp4,
    positive_survivor_step12_ge_53 hpos12 hcomp12,
    positive_survivor_step29_ge_4096 hpos29 hcomp29⟩

/-- **Equivalence with Unbounded Growth of `leastPositiveSurvivor`
(`mahler_conjecture_iff_leastPositiveSurvivor_unbounded`)**:
The general Mahler $3/2$ conjecture holds for all positive reals `0 < α` if and only if
`leastPositiveSurvivor N` grows without bound (`∀ B : ℕ, ∃ N : ℕ, B ≤ leastPositiveSurvivor N`). -/
theorem mahler_conjecture_iff_leastPositiveSurvivor_unbounded :
    (∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) ↔
      (∀ B : ℕ, ∃ N : ℕ, B ≤ leastPositiveSurvivor N) := by
  rcases general_mahler_conjecture_iff_positive_stabilized_branch_escape with
    ⟨h12, h23, _, h35⟩
  rw [h12, h23]
  constructor
  · intro hfin B
    obtain ⟨N, hBN, hexcl⟩ := h35.mp hfin B
    rcases leastPositiveSurvivor_spec N with ⟨hpos, _, hcomp, _⟩
    exact ⟨N, positive_survivor_ge_of_residues_excluded hpos hBN hexcl hcomp⟩
  · intro hunb a_0 ha0
    obtain ⟨N, hBN⟩ := hunb (a_0 + 1)
    refine ⟨N, ?_⟩
    intro hcomp
    have hle := (leastPositiveSurvivor_spec N).2.2.2 a_0 ha0 hcomp
    omega

/-- **Universal Upper Cap on `signedMargin` (`signedMargin_le_two_pow`)**:
For every parity stream `ε : ℕ → ℕ` and depth `N : ℕ`, `signedMargin ε N ≤ 2^N`. -/
theorem signedMargin_le_two_pow (ε : ℕ → ℕ) (N : ℕ) :
    signedMargin ε N ≤ (2 : ℤ) ^ N := by
  cases N with
  | zero => simp [signedMargin]
  | succ N =>
      simp only [signedMargin]
      exact min_le_left _ _

/-- **Exact Odd-Step Margin Contraction (`signedMargin_odd_step_eq`)**:
Whenever `ε N % 2 = 1`, the minimum in `signedMargin ε (N + 1)` is strictly attained
by the right branch:
`signedMargin ε (N + 1) = 3 * signedMargin ε N - 2^(N + 1)` and
`signedMargin ε (N + 1) ≤ 2^N`. -/
theorem signedMargin_odd_step_eq {ε : ℕ → ℕ} {N : ℕ} (hodd : ε N % 2 = 1) :
    signedMargin ε (N + 1) = 3 * signedMargin ε N - (2 : ℤ) ^ (N + 1) ∧
      signedMargin ε (N + 1) ≤ (2 : ℤ) ^ N := by
  have hcap := signedMargin_le_two_pow ε N
  have hpow : (2 : ℤ) ^ (N + 1) = 2 * (2 : ℤ) ^ N := by rw [pow_succ]; ring
  have hpos : (0 : ℤ) < (2 : ℤ) ^ N := by positivity
  simp only [signedMargin, hodd, Nat.cast_one, mul_one]
  have hle : 3 * signedMargin ε N - (2 : ℤ) ^ (N + 1) ≤ (2 : ℤ) ^ N := by linarith
  have hmin :
      min ((2 : ℤ) ^ (N + 1)) (3 * signedMargin ε N - (2 : ℤ) ^ (N + 1)) =
        3 * signedMargin ε N - (2 : ℤ) ^ (N + 1) :=
    min_eq_right (by linarith)
  exact ⟨hmin, by linarith⟩

/-- **Universal 2-Step `11` Margin Death (`signedMargin_two_ones_neg`)**:
At any depth `N`, two consecutive odd parities `ε N % 2 = 1` and `ε (N + 1) % 2 = 1`
force `signedMargin ε (N + 2) ≤ - 2^N < 0`. -/
theorem signedMargin_two_ones_neg {ε : ℕ → ℕ} {N : ℕ}
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 1) :
    signedMargin ε (N + 2) ≤ -((2 : ℤ) ^ N) ∧ signedMargin ε (N + 2) < 0 := by
  have hs1 := (signedMargin_odd_step_eq h0).2
  have hs2 := (signedMargin_odd_step_eq h1).1
  have hpow : (2 : ℤ) ^ (N + 2) = 4 * (2 : ℤ) ^ N := by
    rw [pow_succ, pow_succ]; ring
  have hpos : (0 : ℤ) < (2 : ℤ) ^ N := by positivity
  exact ⟨by linarith, by linarith⟩

/-- On any even parity step (`ε N % 2 = 0`), `signedMargin ε (N + 1) ≤ 3 * signedMargin ε N`. -/
theorem signedMargin_even_step_le {ε : ℕ → ℕ} {N : ℕ} (heven : ε N % 2 = 0) :
    signedMargin ε (N + 1) ≤ 3 * signedMargin ε N := by
  change min ((2 : ℤ) ^ (N + 1))
    (3 * signedMargin ε N - (2 : ℤ) ^ (N + 1) * ((ε N % 2 : ℕ) : ℤ)) ≤
    3 * signedMargin ε N
  rw [heven, Nat.cast_zero, mul_zero, sub_zero]
  exact min_le_right _ _

/-- **Universal 5-Step `10101` Margin Death (`signedMargin_10101_neg`)**:
At any depth `N`, the parity pattern `1, 0, 1, 0, 1` (two `s = 2` blocks followed by `1`)
forces `signedMargin ε (N + 5) ≤ -23 * 2^N < 0`. -/
theorem signedMargin_10101_neg {ε : ℕ → ℕ} {N : ℕ}
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 0)
    (h2 : ε (N + 2) % 2 = 1) (h3 : ε (N + 3) % 2 = 0)
    (h4 : ε (N + 4) % 2 = 1) :
    signedMargin ε (N + 5) ≤ -23 * (2 : ℤ) ^ N ∧ signedMargin ε (N + 5) < 0 := by
  have hd1 := (signedMargin_odd_step_eq h0).2
  have hd2 : signedMargin ε (N + 2) ≤ 3 * (2 : ℤ) ^ N := by
    have he2 := signedMargin_even_step_le h1
    linarith
  have hd3 : signedMargin ε (N + 3) ≤ (2 : ℤ) ^ N := by
    have eq3 := (signedMargin_odd_step_eq h2).1
    have hp3 : (2 : ℤ) ^ (N + 3) = 8 * (2 : ℤ) ^ N := by
      rw [pow_succ, pow_succ, pow_succ]; ring
    linarith
  have hd4 : signedMargin ε (N + 4) ≤ 3 * (2 : ℤ) ^ N := by
    have he4 := signedMargin_even_step_le h3
    linarith
  have eq5 := (signedMargin_odd_step_eq h4).1
  have hp5 : (2 : ℤ) ^ (N + 5) = 32 * (2 : ℤ) ^ N := by
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ]; ring
  have hpos : (0 : ℤ) < (2 : ℤ) ^ N := by positivity
  exact ⟨by linarith, by linarith⟩

/-- **Why `s ≥ 3` (`100`) Blocks Escape Pure Scalar-Margin Contraction
(`signedMargin_100_ceiling_recovery`)**:
If `signedMargin ε N = 2^N` and `(ε N % 2, ε (N + 1) % 2, ε (N + 2) % 2) = (1, 0, 0)`,
then after contracting to `2^N` at `N + 1` and `3 * 2^N` at `N + 2`, the second even step
satisfies `9 * 2^N ≥ 8 * 2^N = 2^(N + 3)`, so `signedMargin ε (N + 3) = 2^(N + 3)`
recovers the full ceiling cap. Thus scalar margin alone cannot exclude `s ≥ 3` blocks
without the coupled seed-residue / quotient arithmetic. -/
theorem signedMargin_100_ceiling_recovery {ε : ℕ → ℕ} {N : ℕ}
    (hcap : signedMargin ε N = (2 : ℤ) ^ N)
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 0) (h2 : ε (N + 2) % 2 = 0) :
    signedMargin ε (N + 1) = (2 : ℤ) ^ N ∧
      signedMargin ε (N + 2) = 3 * (2 : ℤ) ^ N ∧
      signedMargin ε (N + 3) = (2 : ℤ) ^ (N + 3) := by
  have hpos : (0 : ℤ) < (2 : ℤ) ^ N := by positivity
  have hp1 : (2 : ℤ) ^ (N + 1) = 2 * (2 : ℤ) ^ N := by rw [pow_succ]; ring
  have hp2 : (2 : ℤ) ^ (N + 2) = 4 * (2 : ℤ) ^ N := by rw [pow_succ, pow_succ]; ring
  have hp3 : (2 : ℤ) ^ (N + 3) = 8 * (2 : ℤ) ^ N := by rw [pow_succ, pow_succ, pow_succ]; ring
  have hd1 : signedMargin ε (N + 1) = (2 : ℤ) ^ N := by
    have eq1 := (signedMargin_odd_step_eq h0).1
    linarith
  have hd2 : signedMargin ε (N + 2) = 3 * (2 : ℤ) ^ N := by
    change min ((2 : ℤ) ^ (N + 2))
      (3 * signedMargin ε (N + 1) - (2 : ℤ) ^ (N + 2) * ((ε (N + 1) % 2 : ℕ) : ℤ)) =
      3 * (2 : ℤ) ^ N
    rw [hd1, h1, Nat.cast_zero, mul_zero, sub_zero]
    exact min_eq_right (by linarith)
  have hd3 : signedMargin ε (N + 3) = (2 : ℤ) ^ (N + 3) := by
    change min ((2 : ℤ) ^ (N + 3))
      (3 * signedMargin ε (N + 2) - (2 : ℤ) ^ (N + 3) * ((ε (N + 2) % 2 : ℕ) : ℤ)) =
      (2 : ℤ) ^ (N + 3)
    rw [hd2, h2, Nat.cast_zero, mul_zero, sub_zero]
    exact min_eq_left (by linarith)
  exact ⟨hd1, hd2, hd3⟩

end Mahler.SeedResidueTree
