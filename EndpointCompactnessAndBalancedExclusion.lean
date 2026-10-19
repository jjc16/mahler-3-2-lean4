import SubstitutionMahlerMethodAndGrandSynthesis

/-!
# Infinite-Horizon Supremum Bridge, Sharp Balanced Complexity Threshold & Arbitrary Two-Letter Mechanical Exclusions

This module implements **Stage 0** and **Stage 1** of `RESEARCH_OUTLINE_NEXT_STAGE.md`:

1. **Stage 0 — Perpetual Finite Feasibility & The Exact Dyadic-Endpoint Shift Alternative
   (`lowerBound_lt_upperBound_of_perpetual`, `supCompanion`,
   `lowerBound_le_supCompanion_and_le_upperBound`,
   `odd_mul_three_pow_ne_odd_mul_two_pow`,
   `supCompanion_lt_upperBound_after_hit`,
   `perpetual_finite_survival_endpoint_alternative`,
   `exists_positive_infinite_companion_of_perpetual_finite_survival`)**:
   - If a seed `a_0` admits a valid companion separately at every finite horizon
     (`∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N`), then `lowerBound a_0 m < upperBound a_0 n`
     holds for all `m, n : ℕ`, and `supCompanion a_0 := ⨆ n, lowerBound a_0 n`
     satisfies `lowerBound a_0 n ≤ supCompanion a_0 ≤ upperBound a_0 n` for every `n : ℕ`.
   - Distinguishes strict survival from an upper-endpoint hit: if `supCompanion a_0 = upperBound a_0 j`,
     then for every `k ≥ 1`, `(2 * orbit a_0 j + 1) * 3^k ≠ (2 * orbit a_0 (j + k) + 1) * 2^k`
     (odd vs. even), so `supCompanion a_0 < upperBound a_0 (j + k)` holds **strictly** for all `k ≥ 1`.
   - Consequently, perpetual finite survival implies either:
     (a) `ValidCompanionForever a_0 (supCompanion a_0)` (strict survival of `a_0`), or
     (b) `∃ j : ℕ, supCompanion a_0 = upperBound a_0 j ∧ ValidCompanionForever (orbit a_0 (j + 1)) (supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1))`
         (strict infinite survival after shifting past the unique dyadic endpoint hit at `j`).

2. **Stage 1A — Standard Factor Windows & Prefix Subword Complexity Bridge
   (`factorWindow`, `prefixFactorSet`, `prefixFactorCount`,
   `exists_repeated_subword_of_prefixFactorCount_le`)**:
   Defines standard length-`L` factor windows `factorWindow s L r : Fin L → ℕ` and
   the prefix factor complexity `prefixFactorCount s L C := ((Finset.range (C + 1)).image (factorWindow s L)).card`,
   proving directly from `Finset.card_image_of_injOn` that `prefixFactorCount s L C ≤ C`
   guarantees `∃ r1 r2 : ℕ, r1 < r2 ∧ r2 ≤ C ∧ ∀ i < L, s (r1 + i) = s (r2 + i)`.

3. **Stage 1B — Parameterized `(p, q)` Rational Approximations to $\gamma = \log_2(3/2)$ & Sharp Balanced Exclusion
   (`parameterized_pq_repeated_subword_cutoff`,
   `balanced_discrepancy_and_factor_complexity_exclusion`,
   `no_infinite_balanced_subcritical_block_chain`)**:
   - For **any** integers `p, q : ℕ` with `1 ≤ q` and `3^q < 2^(p + q)` (giving the
     rational upper bound $\log_2(3/2) < p / q$, certified for `(3, 5)`, `(10, 17)`,
     `(27, 46)`, and `(58, 99)` where $99 / 58 > 1.70689$), any repeated length-`L`
     window at `r1 < r2` satisfies:
     `q * blockSteps (shiftSeq s r1) L + 1 ≤ p * blockSteps s r2 + q * W + p`.
   - Under standard balanced cumulative-step discrepancy `|(blockSteps s n : ℝ) - lam * n| ≤ D`
     (`lam > 0`) and factor complexity `prefixFactorCount s L C ≤ C ≤ kappa * L + C_0`,
     this yields:
     `lam * (q - p * kappa) * L + 1 ≤ (2 * q + p) * D + p * lam * C_0 + q * W + p`,
     excluding infinite survival for **every** complexity slope `kappa < q / p` up to
     the sharp limiting threshold $1 / \log_2(3/2) \approx 1.709511$.

4. **Stage 1C — General Two-Letter Mechanical / Sturmian Codings over Arbitrary `{a, b}` & Derived Factor Complexity $\le L + 1$
   (`mechStep`, `mechTwoLetterSeq`, `blockSteps_mechTwoLetterSeq_eq`,
   `mechTwoLetterSeq_balanced_discrepancy`, `mechPhase`, `mechCrossedSet`,
   `mechThresholdCount`, `mechTwoLetterSeq_finset_factor_card_le`,
   `mechTwoLetterSeq_prefixFactorCount_le`,
   `unconditional_mechanical_two_letter_finite_cutoff`,
   `no_infinite_mechanical_two_letter_block_chain`)**:
   Formalizes mechanical block sequences over **any** two block lengths `a ≤ b`
   (not restricted to `[3, 5]`), proves exact telescoping of `blockSteps`,
   bounded cumulative discrepancy `|T(n) - (a + (b - a) α) n| ≤ b - a`, and
   **derives directly from the phase `x_r = fract(α r + ρ)` that every finite set
   of origins generates at most `L + 1` distinct length-`L` factors**
   (`prefixFactorCount (mechTwoLetterSeq a b α ρ) L C ≤ L + 1` for all `a, b, α, ρ, L, C`),
   yielding the complete **unconditional** exclusion of infinite valid block chains
   with lengths `mechTwoLetterSeq a b α ρ` (`3 ≤ a ≤ b`, `0 ≤ α ≤ 1`).

5. **Stage 1D — Real Logarithmic Threshold Bridge, Asymptotic Mean & Liminf Complexity Exclusion
   (`exists_pq_of_lt_log_threshold`, `prefixFactorCount_le_of_global_factor_finset`,
   `asymptotic_mean_discrepancy_of_tendsto`,
   `no_infinite_asymptotic_mean_liminf_subcritical_block_chain`,
   `no_infinite_tendsto_mean_log_threshold_block_chain`)**:
   - Proves that for **every** real slope `kappa` satisfying `kappa * Real.log (3 / 2) < Real.log 2`
     (i.e. `kappa < 1 / log_2(3 / 2) ≈ 1.709511`), there exist natural numbers `p, q` with
     `1 ≤ q`, `3^q < 2^(p + q)`, and `p * kappa < q`.
   - Replaces the global bounded-discrepancy hypothesis `|T(n) - lam * n| ≤ D` with an
     **asymptotic mean** `T(n) / n → lam > 0`, and replaces all-length complexity bounds
     with a **liminf complexity** hypothesis holding only at arbitrarily large lengths `L`.
-/

namespace Mahler.EndpointAndBalancedExclusion

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

/-! ## 1. Stage 0: Perpetual Finite Feasibility & The Exact Dyadic-Endpoint Shift Alternative -/

/-- If `a_0` admits a valid companion at every finite horizon `N`, then every
lower bound `lowerBound a_0 m` lies strictly below every upper bound `upperBound a_0 n`. -/
theorem lowerBound_lt_upperBound_of_perpetual {a_0 : ℕ}
    (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) (m n : ℕ) :
    lowerBound a_0 m < upperBound a_0 n := by
  obtain ⟨α, hα⟩ := hperp (max m n)
  have hm : lowerBound a_0 m ≤ α :=
    ((validCompanionAt_iff_bounds a_0 α m).mp (hα m (le_max_left m n))).1
  have hn : α < upperBound a_0 n :=
    ((validCompanionAt_iff_bounds a_0 α n).mp (hα n (le_max_right m n))).2
  exact lt_of_le_of_lt hm hn

/-- Under perpetual finite feasibility, the set of lower bounds `Set.range (lowerBound a_0)`
is bounded above by `upperBound a_0 0`. -/
theorem bddAbove_range_lowerBound_of_perpetual {a_0 : ℕ}
    (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) :
    BddAbove (Set.range (lowerBound a_0)) := by
  refine ⟨upperBound a_0 0, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact le_of_lt (lowerBound_lt_upperBound_of_perpetual hperp m 0)

/-- The canonical supremum candidate companion `supCompanion a_0 = ⨆ n, lowerBound a_0 n`. -/
noncomputable def supCompanion (a_0 : ℕ) : ℝ :=
  ⨆ n : ℕ, lowerBound a_0 n

/-- Under perpetual finite feasibility, `supCompanion a_0` lies in the closed interval
`[lowerBound a_0 n, upperBound a_0 n]` for every `n : ℕ`. -/
theorem lowerBound_le_supCompanion_and_le_upperBound {a_0 : ℕ}
    (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) (n : ℕ) :
    lowerBound a_0 n ≤ supCompanion a_0 ∧ supCompanion a_0 ≤ upperBound a_0 n := by
  refine ⟨le_ciSup (bddAbove_range_lowerBound_of_perpetual hperp) n, ?_⟩
  exact ciSup_le (fun m => le_of_lt (lowerBound_lt_upperBound_of_perpetual hperp m n))

private theorem three_pow_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem two_pow_mod_two {k : ℕ} (hk : 1 ≤ k) : 2 ^ k % 2 = 0 := by
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq, Nat.pow_succ]
  omega

/-- **Parity Obstruction to Repeated Dyadic Upper Endpoints (`odd_mul_three_pow_ne_odd_mul_two_pow`)**:
For any natural numbers `B, N, k` with `1 ≤ k`, `(2 * B + 1) * 3^k` is odd whereas
`(2 * N + 1) * 2^k` is even, so they can never be equal. -/
theorem odd_mul_three_pow_ne_odd_mul_two_pow {B N k : ℕ} (hk : 1 ≤ k) :
    (2 * B + 1) * 3 ^ k ≠ (2 * N + 1) * 2 ^ k := by
  intro heq
  have hmod := congrArg (fun x => x % 2) heq
  dsimp at hmod
  have hlhs : ((2 * B + 1) * 3 ^ k) % 2 = 1 := by
    rw [Nat.mul_mod, three_pow_mod_two]
    omega
  have hrhs : ((2 * N + 1) * 2 ^ k) % 2 = 0 := by
    rw [Nat.mul_mod, two_pow_mod_two hk]
    omega
  omega

/-- No two upper bounds `upperBound a_0 j` and `upperBound a_0 (j + k)` (`1 ≤ k`)
can ever coincide. -/
theorem upperBound_ne_upperBound_add_pos (a_0 j k : ℕ) (hk : 1 ≤ k) :
    upperBound a_0 j ≠ upperBound a_0 (j + k) := by
  intro heq
  have hscale : ∀ n : ℕ,
      upperBound a_0 n * (2 * (3 : ℝ) ^ n) =
        (2 : ℝ) ^ n * (2 * (orbit a_0 n : ℝ) + 1) := by
    intro n
    unfold upperBound
    have h23 : (2 / 3 : ℝ) ^ n * (3 : ℝ) ^ n = (2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    calc
      (2 / 3 : ℝ) ^ n * ((orbit a_0 n : ℝ) + 1 / 2) * (2 * (3 : ℝ) ^ n) =
          ((2 / 3 : ℝ) ^ n * (3 : ℝ) ^ n) * (2 * (orbit a_0 n : ℝ) + 1) := by ring
      _ = (2 : ℝ) ^ n * (2 * (orbit a_0 n : ℝ) + 1) := by rw [h23]
  have hmul := congrArg (fun x : ℝ => x * (2 * (3 : ℝ) ^ (j + k))) heq
  dsimp at hmul
  have hlhs :
      upperBound a_0 j * (2 * (3 : ℝ) ^ (j + k)) =
        (2 : ℝ) ^ j * ((2 * (orbit a_0 j : ℝ) + 1) * (3 : ℝ) ^ k) := by
    rw [pow_add (3 : ℝ) j k]
    calc
      upperBound a_0 j * (2 * ((3 : ℝ) ^ j * (3 : ℝ) ^ k)) =
          (upperBound a_0 j * (2 * (3 : ℝ) ^ j)) * (3 : ℝ) ^ k := by ring
      _ = (2 : ℝ) ^ j * ((2 * (orbit a_0 j : ℝ) + 1) * (3 : ℝ) ^ k) := by
        rw [hscale j]
        ring
  have hrhs :
      upperBound a_0 (j + k) * (2 * (3 : ℝ) ^ (j + k)) =
        (2 : ℝ) ^ j * ((2 * (orbit a_0 (j + k) : ℝ) + 1) * (2 : ℝ) ^ k) := by
    rw [hscale (j + k), pow_add (2 : ℝ) j k]
    ring
  rw [hlhs, hrhs] at hmul
  have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hcancel :
      (2 * (orbit a_0 j : ℝ) + 1) * (3 : ℝ) ^ k =
        (2 * (orbit a_0 (j + k) : ℝ) + 1) * (2 : ℝ) ^ k :=
    mul_left_cancel₀ (ne_of_gt h2j_pos) hmul
  have hnat :
      (2 * orbit a_0 j + 1) * 3 ^ k = (2 * orbit a_0 (j + k) + 1) * 2 ^ k := by
    exact_mod_cast hcancel
  exact odd_mul_three_pow_ne_odd_mul_two_pow hk hnat

/-- **Strict Post-Hit Upper-Bound Separation (`supCompanion_lt_upperBound_after_hit`)**:
Under perpetual finite feasibility, if `supCompanion a_0 = upperBound a_0 j`, then
for every `1 ≤ k`, `supCompanion a_0 < upperBound a_0 (j + k)` holds strictly. -/
theorem supCompanion_lt_upperBound_after_hit {a_0 j k : ℕ}
    (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N)
    (hhit : supCompanion a_0 = upperBound a_0 j) (hk : 1 ≤ k) :
    supCompanion a_0 < upperBound a_0 (j + k) := by
  have hle := (lowerBound_le_supCompanion_and_le_upperBound hperp (j + k)).2
  have hne : supCompanion a_0 ≠ upperBound a_0 (j + k) := by
    rw [hhit]
    exact upperBound_ne_upperBound_add_pos a_0 j k hk
  exact lt_of_le_of_ne hle hne

/-- If `supCompanion a_0 = upperBound a_0 j`, then shifting forward to step `j + 1`
produces a strict infinite companion `supCompanion a_0 * (3 / 2)^ (j + 1)` for
the shifted integer seed `orbit a_0 (j + 1)`. -/
theorem validCompanionForever_shifted_of_endpoint_hit {a_0 j : ℕ}
    (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N)
    (hhit : supCompanion a_0 = upperBound a_0 j) :
    ValidCompanionForever (orbit a_0 (j + 1))
      (supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1)) := by
  intro m
  unfold ValidCompanionAt
  rw [← orbit_add a_0 (j + 1) m]
  have hpow :
      supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1) * (3 / 2 : ℝ) ^ m =
        supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1 + m) := by
    rw [pow_add (3 / 2 : ℝ) (j + 1) m, mul_assoc]
  rw [hpow]
  change ValidCompanionAt a_0 (supCompanion a_0) (j + 1 + m)
  rw [validCompanionAt_iff_bounds]
  refine ⟨(lowerBound_le_supCompanion_and_le_upperBound hperp (j + 1 + m)).1, ?_⟩
  have hlt := supCompanion_lt_upperBound_after_hit hperp hhit (k := 1 + m) (by omega)
  simpa [Nat.add_assoc] using hlt

/-- **Global Perpetual-to-Infinite Endpoint Alternative (`perpetual_finite_survival_endpoint_alternative`)**:
If a seed `a_0` admits a valid companion separately at every finite horizon `N`,
then either:
1. `supCompanion a_0` is a strict infinite companion for `a_0` itself
   (`ValidCompanionForever a_0 (supCompanion a_0)`), or
2. `supCompanion a_0` hits the upper endpoint `upperBound a_0 j` at a unique step `j`,
   and the shifted real `supCompanion a_0 * (3 / 2)^(j + 1)` is a strict infinite
   companion for the shifted seed `orbit a_0 (j + 1)`. -/
theorem perpetual_finite_survival_endpoint_alternative {a_0 : ℕ}
    (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) :
    ValidCompanionForever a_0 (supCompanion a_0) ∨
      ∃ j : ℕ,
        supCompanion a_0 = upperBound a_0 j ∧
          ValidCompanionForever (orbit a_0 (j + 1))
            (supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1)) := by
  by_cases hhit : ∃ j : ℕ, supCompanion a_0 = upperBound a_0 j
  · right
    rcases hhit with ⟨j, hj⟩
    exact ⟨j, hj, validCompanionForever_shifted_of_endpoint_hit hperp hj⟩
  · left
    intro n
    rw [validCompanionAt_iff_bounds]
    rcases lowerBound_le_supCompanion_and_le_upperBound hperp n with ⟨hlo, hhi⟩
    have hne : supCompanion a_0 ≠ upperBound a_0 n := fun h => hhit ⟨n, h⟩
    exact ⟨hlo, lt_of_le_of_ne hhi hne⟩

private theorem orbit_pos_of_pos {a_0 : ℕ} (ha0 : 1 ≤ a_0) (n : ℕ) :
    1 ≤ orbit a_0 n := by
  induction n with
  | zero => simpa [orbit] using ha0
  | succ n ih =>
      simp only [orbit]
      have h := step_identity (orbit a_0 n)
      omega

/-- **Existence of a Strict Positive Infinite Companion from Perpetual Finite Survival
(`exists_positive_infinite_companion_of_perpetual_finite_survival`)**:
If a positive integer seed `1 ≤ a_0` admits a valid companion at every finite horizon `N`,
then there exist a positive integer seed `1 ≤ b_0` (either `a_0` or a forward orbit image
`orbit a_0 (j + 1)`) and a real `β ≥ 1` satisfying `ValidCompanionForever b_0 β`. -/
theorem exists_positive_infinite_companion_of_perpetual_finite_survival {a_0 : ℕ}
    (ha0 : 1 ≤ a_0) (hperp : ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) :
    ∃ (b_0 : ℕ) (β : ℝ), 1 ≤ b_0 ∧ (1 : ℝ) ≤ β ∧ ValidCompanionForever b_0 β := by
  rcases perpetual_finite_survival_endpoint_alternative hperp with hstrict | ⟨j, _, hshift⟩
  · have h0 := hstrict 0
    unfold ValidCompanionAt at h0
    simp only [orbit, pow_zero, mul_one] at h0
    have ha0_real : (1 : ℝ) ≤ (a_0 : ℝ) := by exact_mod_cast ha0
    exact ⟨a_0, supCompanion a_0, ha0, le_trans ha0_real h0.1, hstrict⟩
  · have hb0 : 1 ≤ orbit a_0 (j + 1) := orbit_pos_of_pos ha0 (j + 1)
    have h0 := hshift 0
    unfold ValidCompanionAt at h0
    simp only [orbit, pow_zero, mul_one] at h0
    have hb0_real : (1 : ℝ) ≤ (orbit a_0 (j + 1) : ℝ) := by exact_mod_cast hb0
    exact ⟨orbit a_0 (j + 1), supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1),
      hb0, le_trans hb0_real h0.1, hshift⟩

private theorem bernoulli_three_halves (k : ℕ) :
    (1 : ℝ) + (k : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hpos : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
      nlinarith

/-- **Global Forward-Shift Reduction from Arbitrary Positive Reals $\alpha > 0$ to $\beta \ge 1$
(`exists_positive_seed_ge_one_of_pos_companion`)**:
If **any** real `0 < α` (including `0 < α < 1` with `a_0 = 0`) satisfies
`ValidCompanionForever a_0 α`, then shifting forward to a step `k` where
`1 ≤ α * (3 / 2)^k` yields a positive integer seed `1 ≤ b_0 = orbit a_0 k` and
a real `1 ≤ β = α * (3 / 2)^k` satisfying `ValidCompanionForever b_0 β`. -/
theorem exists_positive_seed_ge_one_of_pos_companion {a_0 : ℕ} {α : ℝ}
    (hα : 0 < α) (hforever : ValidCompanionForever a_0 α) :
    ∃ (b_0 : ℕ) (β : ℝ), 1 ≤ b_0 ∧ (1 : ℝ) ≤ β ∧ ValidCompanionForever b_0 β := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / α)
  have hpow : (1 : ℝ) ≤ α * (3 / 2 : ℝ) ^ k := by
    have hb := bernoulli_three_halves k
    have h1 : 2 < (k : ℝ) * α := (div_lt_iff₀ hα).mp hk
    have h2 : α * (1 + (k : ℝ) / 2) ≤ α * (3 / 2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hb (le_of_lt hα)
    linarith
  have hcomp_k := hforever k
  unfold ValidCompanionAt at hcomp_k
  have horb_gt : (0 : ℝ) < (orbit a_0 k : ℝ) := by linarith [hcomp_k.2]
  have hb0_pos : 1 ≤ orbit a_0 k := by
    have hpos : 0 < orbit a_0 k := by exact_mod_cast horb_gt
    omega
  refine ⟨orbit a_0 k, α * (3 / 2 : ℝ) ^ k, hb0_pos, hpow, ?_⟩
  intro m
  unfold ValidCompanionAt
  rw [← orbit_add a_0 k m]
  have hmul : α * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = α * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rw [hmul]
  exact hforever (k + m)

/-! ## 2. Stage 1A: Standard Factor Windows & Prefix Subword Complexity Bridge -/

/-- The standard length-`L` factor window of `s` starting at origin `r`. -/
def factorWindow (s : ℕ → ℕ) (L r : ℕ) : Fin L → ℕ :=
  fun i => s (r + i.val)

/-- Two factor windows at `r1` and `r2` are equal iff `s (r1 + i) = s (r2 + i)` for all `i < L`. -/
theorem factorWindow_eq_iff (s : ℕ → ℕ) (L r1 r2 : ℕ) :
    factorWindow s L r1 = factorWindow s L r2 ↔
      ∀ i < L, s (r1 + i) = s (r2 + i) := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.isLt

/-- The finite set of distinct length-`L` factors occurring at origins `0 ≤ r ≤ C`. -/
noncomputable def prefixFactorSet (s : ℕ → ℕ) (L C : ℕ) : Finset (Fin L → ℕ) :=
  (Finset.range (C + 1)).image (factorWindow s L)

/-- The number of distinct length-`L` factors occurring among the first `C + 1` origins `0, ..., C`. -/
noncomputable def prefixFactorCount (s : ℕ → ℕ) (L C : ℕ) : ℕ :=
  (prefixFactorSet s L C).card

/-- **Standard Prefix Factor Complexity Pigeonhole Bridge (`exists_repeated_subword_of_prefixFactorCount_le`)**:
If the number of distinct length-`L` factors among origins `0 ≤ r ≤ C` is at most `C`
(`prefixFactorCount s L C ≤ C`), then there exist `r1 < r2 ≤ C` whose length-`L`
windows coincide (`∀ i < L, s (r1 + i) = s (r2 + i)`). -/
theorem exists_repeated_subword_of_prefixFactorCount_le
    (s : ℕ → ℕ) (L C : ℕ) (hcard : prefixFactorCount s L C ≤ C) :
    ∃ r1 r2 : ℕ, r1 < r2 ∧ r2 ≤ C ∧ ∀ i < L, s (r1 + i) = s (r2 + i) := by
  by_contra hno
  have hinj : Set.InjOn (factorWindow s L) ↑(Finset.range (C + 1)) := by
    intro a ha b hb heq
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hw := (factorWindow_eq_iff s L a b).mp heq
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hno ⟨a, b, hlt, by omega, hw⟩
    · exact hno ⟨b, a, hgt, by omega, fun i hi => (hw i hi).symm⟩
  have hcard_eq : prefixFactorCount s L C = C + 1 := by
    unfold prefixFactorCount prefixFactorSet
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  omega

/-! ## 3. Stage 1B: Parameterized `(p, q)` Power Comparisons & Sharp Balanced Exclusion -/

private theorem pow_strict_mono_left_nat {a b n : ℕ} (hn : 1 ≤ n) (hlt : a < b) :
    a ^ n < b ^ n := by
  have hb_pos : 0 < b := by omega
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · rw [Nat.zero_pow (by omega : 0 < n)]
    exact Nat.pow_pos hb_pos
  · induction n with
    | zero => omega
    | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simpa using hlt
        · have ihn := ih hpos
          rw [Nat.pow_succ, Nat.pow_succ]
          have h1 : a ^ n * a < b ^ n * a := Nat.mul_lt_mul_of_pos_right ihn ha_pos
          have h2 : b ^ n * a ≤ b ^ n * b := Nat.mul_le_mul_left (b ^ n) (by omega)
          exact lt_of_lt_of_le h1 h2

private theorem pow_le_pow_left_nat' {a b n : ℕ} (hle : a ≤ b) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih hle

private theorem exp_lt_of_two_pow_lt' {A B : ℕ} (h : 2 ^ A < 2 ^ B) : A < B := by
  by_contra hge
  have hle : 2 ^ B ≤ 2 ^ A := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- For any `p, q : ℕ` with `3^q < 2^(p + q)` and any `T : ℕ`,
`(3^(T + 1))^q < 2^((p + q) * (T + 1))`. -/
theorem three_pow_succ_pow_q_lt_two_pow {p q : ℕ} (hpq : 3 ^ q < 2 ^ (p + q)) (T : ℕ) :
    (3 ^ (T + 1)) ^ q < 2 ^ ((p + q) * (T + 1)) := by
  have hcomm : (3 ^ (T + 1)) ^ q = (3 ^ q) ^ (T + 1) := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  rw [hcomm, Nat.pow_mul 2 (p + q) (T + 1)]
  exact pow_strict_mono_left_nat (by omega : 1 ≤ T + 1) hpq

/-- **Parameterized `(p, q)` Exponential Cutoff Lemma (`pq_cutoff_of_exp_bound`)**:
Whenever `1 ≤ q`, `3^q < 2^(p + q)`, `a_0 < 2^W`, and
`2^(T + S + 2) < 3^(T + 1) * (2 * a_0 + 1)`, raising both sides to the `q`-th
power gives:
`q * S + 1 ≤ p * T + q * W + p`. -/
theorem pq_cutoff_of_exp_bound {p q T S a_0 W : ℕ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q)) (ha0 : a_0 < 2 ^ W)
    (hsharp : 2 ^ (T + S + 2) < 3 ^ (T + 1) * (2 * a_0 + 1)) :
    q * S + 1 ≤ p * T + q * W + p := by
  have hpow_q := pow_strict_mono_left_nat hq hsharp
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have h2a0_q : (2 * a_0 + 1) ^ q ≤ (2 ^ (W + 1)) ^ q :=
    pow_le_pow_left_nat' h2a0
  have h3_q := three_pow_succ_pow_q_lt_two_pow hpq T
  have hlhs : (2 ^ (T + S + 2)) ^ q = 2 ^ ((T + S + 2) * q) := by
    rw [← Nat.pow_mul]
  have hrhs :
      (3 ^ (T + 1) * (2 * a_0 + 1)) ^ q <
        2 ^ ((p + q) * (T + 1) + (W + 1) * q) := by
    rw [Nat.mul_pow]
    have hpos : 0 < (2 * a_0 + 1) ^ q := Nat.pow_pos (by omega)
    have h1 :
        (3 ^ (T + 1)) ^ q * (2 * a_0 + 1) ^ q <
          2 ^ ((p + q) * (T + 1)) * (2 * a_0 + 1) ^ q :=
      Nat.mul_lt_mul_of_pos_right h3_q hpos
    have h2 :
        2 ^ ((p + q) * (T + 1)) * (2 * a_0 + 1) ^ q ≤
          2 ^ ((p + q) * (T + 1)) * (2 ^ (W + 1)) ^ q :=
      Nat.mul_le_mul_left _ h2a0_q
    have h3 :
        2 ^ ((p + q) * (T + 1)) * (2 ^ (W + 1)) ^ q =
          2 ^ ((p + q) * (T + 1) + (W + 1) * q) := by
      rw [← Nat.pow_mul, ← Nat.pow_add]
    exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (le_of_eq h3)
  rw [hlhs] at hpow_q
  have hexp := exp_lt_of_two_pow_lt' (lt_trans hpow_q hrhs)
  have hexpand1 : (T + S + 2) * q = q * T + q * S + 2 * q := by ring
  have hexpand2 :
      (p + q) * (T + 1) + (W + 1) * q =
        p * T + q * T + p + q * W + 2 * q := by ring
  rw [hexpand1, hexpand2] at hexp
  clear hpow_q h2a0_q h3_q hlhs hrhs hexpand1 hexpand2
  omega

/-- **Parameterized `(p, q)` Repeated-Subword Cutoff (`parameterized_pq_repeated_subword_cutoff`)**:
For any `p, q : ℕ` with `1 ≤ q` and `3^q < 2^(p + q)`, along any `ValidBlockChain a_0 s u K`
with `a_0 < 2^W` and `0 < integerSlack s r2`, any `1 ≤ L`-block subword repeating at
`r1 < r2` (`r2 + (L - 1) < K`) satisfies:
`q * blockSteps (shiftSeq s r1) L + 1 ≤ p * blockSteps s r2 + q * W + p`. -/
theorem parameterized_pq_repeated_subword_cutoff
    {p q a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    q * blockSteps (shiftSeq s r1) L + 1 ≤ p * blockSteps s r2 + q * W + p :=
  pq_cutoff_of_exp_bound hq hpq ha0
    (sharpened_repeated_subword_linear_cutoff hL hr12 hr2L ha0 hchain hslack hmatch).1

/-- Concrete high-precision rational convergents `3^q < 2^(p + q)` to $\gamma = \log_2(3/2)$,
reaching threshold slopes $q / p = 5/3 \approx 1.6667$, $17/10 = 1.7$,
$46/27 \approx 1.7037$, and $99/58 \approx 1.706896$. -/
theorem high_precision_rational_log_convergents :
    3 ^ 5 < 2 ^ (3 + 5) ∧
      3 ^ 17 < 2 ^ (10 + 17) ∧
      3 ^ 46 < 2 ^ (27 + 46) ∧
      3 ^ 99 < 2 ^ (58 + 99) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Sharp Balanced Discrepancy & Factor Complexity Exclusion (`balanced_discrepancy_and_factor_complexity_exclusion`)**:
Suppose a surviving block chain `ValidBlockChain a_0 s u K` (`a_0 < 2^W`, `0 < minSlack s C`,
`C + L ≤ K`, `1 ≤ L`) satisfies:
1. **Balanced Cumulative Discrepancy**: `∀ n ≤ K, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ D` (`0 < lam`, `0 ≤ D`),
2. **Prefix Factor Complexity**: `prefixFactorCount s L C ≤ C` with `(C : ℝ) ≤ kappa * (L : ℝ) + C_0`, and
3. **Rational Power Bound**: `1 ≤ q` and `3^q < 2^(p + q)`.
Then:
`lam * ((q : ℝ) - (p : ℝ) * kappa) * (L : ℝ) + 1 ≤
  (2 * (q : ℝ) + (p : ℝ)) * D + (p : ℝ) * lam * C_0 + (q : ℝ) * (W : ℝ) + (p : ℝ)`. -/
theorem balanced_discrepancy_and_factor_complexity_exclusion
    {p q a_0 W L C K : ℕ} {s u : ℕ → ℕ} {lam D kappa C_0 : ℝ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (hL : 1 ≤ L) (hK : C + L ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hminSlack : 0 < minSlack s C)
    (hlam : 0 < lam)
    (hbal : ∀ n ≤ K, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ D)
    (hcard : prefixFactorCount s L C ≤ C)
    (hC_bound : (C : ℝ) ≤ kappa * (L : ℝ) + C_0) :
    lam * ((q : ℝ) - (p : ℝ) * kappa) * (L : ℝ) + 1 ≤
      (2 * (q : ℝ) + (p : ℝ)) * D + (p : ℝ) * lam * C_0 +
        (q : ℝ) * (W : ℝ) + (p : ℝ) := by
  obtain ⟨r1, r2, hr12, hr2C, hmatch⟩ :=
    exists_repeated_subword_of_prefixFactorCount_le s L C hcard
  have hr2L : r2 + (L - 1) < K := by omega
  have hslack_r2 : 0 < integerSlack s r2 :=
    (minSlack_pos_of_le s hr2C hminSlack).2
  have hpq_cut :=
    parameterized_pq_repeated_subword_cutoff hq hpq hL hr12 hr2L ha0 hchain hslack_r2 hmatch
  have hpq_real :
      (q : ℝ) * (blockSteps (shiftSeq s r1) L : ℝ) + 1 ≤
        (p : ℝ) * (blockSteps s r2 : ℝ) + (q : ℝ) * (W : ℝ) + (p : ℝ) := by
    exact_mod_cast hpq_cut
  have hr1_le : r1 ≤ K := by omega
  have hr1L_le : r1 + L ≤ K := by omega
  have hr2_le : r2 ≤ K := by omega
  have hbal_r1 := abs_le.mp (hbal r1 hr1_le)
  have hbal_r1L := abs_le.mp (hbal (r1 + L) hr1L_le)
  have hbal_r2 := abs_le.mp (hbal r2 hr2_le)
  have hsteps_add :
      (blockSteps s (r1 + L) : ℝ) =
        (blockSteps s r1 : ℝ) + (blockSteps (shiftSeq s r1) L : ℝ) := by
    exact_mod_cast blockSteps_add s r1 L
  have hcast_r1L : ((r1 + L : ℕ) : ℝ) = (r1 : ℝ) + (L : ℝ) := by push_cast; ring
  rw [hcast_r1L] at hbal_r1L
  have hS_lo : lam * (L : ℝ) - 2 * D ≤ (blockSteps (shiftSeq s r1) L : ℝ) := by
    linarith [hbal_r1.2, hbal_r1L.1, hsteps_add]
  have hr2_le_C : (r2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hr2C
  have hT_hi : (blockSteps s r2 : ℝ) ≤ lam * (kappa * (L : ℝ) + C_0) + D := by
    nlinarith [hbal_r2.2, hr2_le_C, hC_bound, hlam]
  have hq_nonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  nlinarith [hpq_real, hS_lo, hT_hi, hq_nonneg, hp_nonneg]

/-- **Infinite-Horizon Exclusion of Balanced Sub-Critical Block Chains
(`no_infinite_balanced_subcritical_block_chain`)**:
Suppose `1 ≤ q`, `3^q < 2^(p + q)`, `0 < lam`, `0 ≤ D`, `0 ≤ C_0`, and `(p : ℝ) * kappa < (q : ℝ)`.
Then no infinite surviving block chain (`∀ K, ValidBlockChain a_0 s u K` and
`∀ m, 0 < minSlack s m`) can simultaneously have balanced cumulative steps
`∀ n, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ D` and sub-critical factor complexity
`∀ L ≥ 1, prefixFactorCount s L (C L) ≤ C L ∧ (C L : ℝ) ≤ kappa * (L : ℝ) + C_0`. -/
theorem no_infinite_balanced_subcritical_block_chain
    {p q a_0 W : ℕ} {s u C : ℕ → ℕ} {lam D kappa C_0 : ℝ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (ha0 : a_0 < 2 ^ W)
    (hlam : 0 < lam) (hD : 0 ≤ D) (hC0 : 0 ≤ C_0)
    (hsub : (p : ℝ) * kappa < (q : ℝ))
    (hbal : ∀ n : ℕ, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ D)
    (hcomp : ∀ L : ℕ, 1 ≤ L →
      prefixFactorCount s L (C L) ≤ C L ∧ (C L : ℝ) ≤ kappa * (L : ℝ) + C_0) :
    ¬ ((∀ K : ℕ, ValidBlockChain a_0 s u K) ∧ (∀ m : ℕ, 0 < minSlack s m)) := by
  rintro ⟨hchain, hminSlack⟩
  set δ : ℝ := lam * ((q : ℝ) - (p : ℝ) * kappa)
  have hδ_pos : 0 < δ := mul_pos hlam (by linarith)
  set RHS : ℝ :=
    (2 * (q : ℝ) + (p : ℝ)) * D + (p : ℝ) * lam * C_0 + (q : ℝ) * (W : ℝ) + (p : ℝ)
  have hRHS_nonneg : 0 ≤ RHS := by
    unfold RHS
    positivity
  obtain ⟨L0, hL0⟩ := exists_nat_gt (RHS / δ + 1)
  have hL : 1 ≤ L0 := by
    have hdiv_nonneg : 0 ≤ RHS / δ := div_nonneg hRHS_nonneg (le_of_lt hδ_pos)
    have hgt1 : (1 : ℝ) < (L0 : ℝ) := by linarith
    exact_mod_cast (le_of_lt hgt1)
  rcases hcomp L0 hL with ⟨hcard, hC_bound⟩
  have hbound :=
    balanced_discrepancy_and_factor_complexity_exclusion hq hpq hL le_rfl ha0
      (hchain (C L0 + L0)) (hminSlack (C L0)) hlam (fun n _ => hbal n) hcard hC_bound
  have hmul_gt : RHS < (L0 : ℝ) * δ := by
    have h1 : RHS / δ < (L0 : ℝ) := by linarith
    exact (div_lt_iff₀ hδ_pos).mp h1
  change δ * (L0 : ℝ) + 1 ≤ RHS at hbound
  linarith

/-! ## 4. Stage 1C: General Two-Letter Mechanical / Sturmian Codings over Arbitrary `{a, b}` -/

/-- The mechanical difference bit `⌊α (k + 1) + ρ⌋ - ⌊α k + ρ⌋` (as a natural number)
for `0 ≤ α ≤ 1`. -/
noncomputable def mechStep (α ρ : ℝ) (k : ℕ) : ℕ :=
  Int.toNat (⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ - ⌊α * (k : ℝ) + ρ⌋)

/-- The two-letter mechanical block sequence over arbitrary block lengths `a ≤ b`. -/
noncomputable def mechTwoLetterSeq (a b : ℕ) (α ρ : ℝ) (k : ℕ) : ℕ :=
  a + (b - a) * mechStep α ρ k

/-- For `0 ≤ α ≤ 1`, `mechStep α ρ k ≤ 1` and its integer cast equals
`⌊α (k + 1) + ρ⌋ - ⌊α k + ρ⌋`. -/
theorem mechStep_cast_and_le_one {α : ℝ} (ρ : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ((mechStep α ρ k : ℕ) : ℤ) =
      ⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ - ⌊α * (k : ℝ) + ρ⌋ ∧
    mechStep α ρ k ≤ 1 := by
  have hle_real : α * (k : ℝ) + ρ ≤ α * ((k + 1 : ℕ) : ℝ) + ρ := by
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
  have hfl_le : ⌊α * (k : ℝ) + ρ⌋ ≤ ⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ :=
    Int.floor_mono hle_real
  have hnonneg : 0 ≤ ⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ - ⌊α * (k : ℝ) + ρ⌋ := by omega
  have hcast_eq :
      ((mechStep α ρ k : ℕ) : ℤ) =
        ⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ - ⌊α * (k : ℝ) + ρ⌋ :=
    Int.toNat_of_nonneg hnonneg
  have hhi_real :
      α * ((k + 1 : ℕ) : ℝ) + ρ < ((⌊α * (k : ℝ) + ρ⌋ + 2 : ℤ) : ℝ) := by
    have hlt := Int.lt_floor_add_one (α * (k : ℝ) + ρ)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    push_cast
    linarith
  have hfl_lt : ⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ < ⌊α * (k : ℝ) + ρ⌋ + 2 := by
    have hle := Int.floor_le (α * ((k + 1 : ℕ) : ℝ) + ρ)
    have hlt_real :
        ((⌊α * ((k + 1 : ℕ) : ℝ) + ρ⌋ : ℤ) : ℝ) <
          ((⌊α * (k : ℝ) + ρ⌋ + 2 : ℤ) : ℝ) :=
      lt_of_le_of_lt hle hhi_real
    exact_mod_cast hlt_real
  refine ⟨hcast_eq, by omega⟩

/-- Every entry of `mechTwoLetterSeq a b α ρ` (`a ≤ b`, `0 ≤ α ≤ 1`) lies in `[a, b]`. -/
theorem mechTwoLetterSeq_bounds {a b : ℕ} {α ρ : ℝ}
    (hab : a ≤ b) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    a ≤ mechTwoLetterSeq a b α ρ k ∧ mechTwoLetterSeq a b α ρ k ≤ b := by
  have hstep := (mechStep_cast_and_le_one ρ hα0 hα1 k).2
  unfold mechTwoLetterSeq
  refine ⟨by omega, ?_⟩
  have hmul : (b - a) * mechStep α ρ k ≤ (b - a) * 1 :=
    Nat.mul_le_mul_left (b - a) hstep
  omega

/-- **Exact Telescoping Formula for Mechanical Cumulative Steps (`blockSteps_mechTwoLetterSeq_eq`)**:
For any `a ≤ b`, `0 ≤ α ≤ 1`, and `n : ℕ`,
`(blockSteps (mechTwoLetterSeq a b α ρ) n : ℤ) =
  (a : ℤ) * (n : ℤ) + ((b - a : ℕ) : ℤ) * (⌊α * (n : ℝ) + ρ⌋ - ⌊ρ⌋)`. -/
theorem blockSteps_mechTwoLetterSeq_eq (a b : ℕ) {α : ℝ} (ρ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    (blockSteps (mechTwoLetterSeq a b α ρ) n : ℤ) =
      (a : ℤ) * (n : ℤ) +
        ((b - a : ℕ) : ℤ) * (⌊α * (n : ℝ) + ρ⌋ - ⌊ρ⌋) := by
  induction n with
  | zero => simp [blockSteps]
  | succ n ih =>
      simp only [blockSteps, Nat.cast_add]
      rw [ih]
      have hstep := (mechStep_cast_and_le_one ρ hα0 hα1 n).1
      have hmech :
          (mechTwoLetterSeq a b α ρ n : ℤ) =
            (a : ℤ) + ((b - a : ℕ) : ℤ) * ((mechStep α ρ n : ℕ) : ℤ) := by
        unfold mechTwoLetterSeq
        push_cast
        rfl
      rw [hmech, hstep, Nat.cast_add, Nat.cast_one]
      ring

/-- **Bounded Cumulative Discrepancy of General `{a, b}` Mechanical Sequences
(`mechTwoLetterSeq_balanced_discrepancy`)**:
For **any** two block lengths `a ≤ b` and `0 ≤ α ≤ 1`, the cumulative steps of
`mechTwoLetterSeq a b α ρ` satisfy:
`|(blockSteps (mechTwoLetterSeq a b α ρ) n : ℝ) - ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) * (n : ℝ)| ≤ ((b - a : ℕ) : ℝ)`
for every `n : ℕ`. -/
theorem mechTwoLetterSeq_balanced_discrepancy {a b : ℕ} {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    |(blockSteps (mechTwoLetterSeq a b α ρ) n : ℝ) -
        ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) * (n : ℝ)| ≤
      ((b - a : ℕ) : ℝ) := by
  have htel :
      (blockSteps (mechTwoLetterSeq a b α ρ) n : ℝ) =
        (a : ℝ) * (n : ℝ) +
          ((b - a : ℕ) : ℝ) * (((⌊α * (n : ℝ) + ρ⌋ : ℤ) : ℝ) - ((⌊ρ⌋ : ℤ) : ℝ)) := by
    have h := blockSteps_mechTwoLetterSeq_eq a b ρ hα0 hα1 n
    exact_mod_cast h
  have hfl_n_le := Int.floor_le (α * (n : ℝ) + ρ)
  have hfl_n_gt := Int.lt_floor_add_one (α * (n : ℝ) + ρ)
  have hfl_0_le := Int.floor_le ρ
  have hfl_0_gt := Int.lt_floor_add_one ρ
  have hdiff_lo :
      α * (n : ℝ) - 1 ≤ ((⌊α * (n : ℝ) + ρ⌋ : ℤ) : ℝ) - ((⌊ρ⌋ : ℤ) : ℝ) := by
    linarith
  have hdiff_hi :
      ((⌊α * (n : ℝ) + ρ⌋ : ℤ) : ℝ) - ((⌊ρ⌋ : ℤ) : ℝ) ≤ α * (n : ℝ) + 1 := by
    linarith
  have hba_nonneg : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg (b - a)
  rw [htel, abs_le]
  constructor <;> nlinarith

/-- **Unconditional Exclusion of Arbitrary Two-Letter `{a, b}` (`3 ≤ a ≤ b`) Balanced / Sturmian Sequences
(`arbitrary_two_letter_ceiling_saturated_sturmian_exclusion`)**:
For **any** two block lengths `3 ≤ a ≤ b` (arbitrarily large, not restricted to `[3, 5]`),
if a valid block chain `ValidBlockChain a_0 s u K` (`a_0 < 2^W`, `2 * L + C_0 ≤ K`, `1 ≤ L`)
has `a ≤ s k` for all `k < K` (so `minSlack` positivity is automatic), satisfies the
balanced cumulative discrepancy `|(blockSteps s n : ℝ) - lam * n| ≤ b - a` with `a ≤ lam ≤ b`,
and has prefix factor complexity `prefixFactorCount s L (L + C_0) ≤ L + C_0`, then:
`2 * lam * (L : ℝ) + 1 ≤ 13 * ((b - a : ℕ) : ℝ) + 3 * lam * (C_0 : ℝ) + 5 * (W : ℝ) + 3`. -/
theorem arbitrary_two_letter_ceiling_saturated_sturmian_exclusion
    {a b a_0 W L C_0 K : ℕ} {s u : ℕ → ℕ} {lam : ℝ}
    (ha3 : 3 ≤ a)
    (hL : 1 ≤ L) (hK : 2 * L + C_0 ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_lo : ∀ k < K, a ≤ s k)
    (hlam_lo : (a : ℝ) ≤ lam)
    (hbal : ∀ n ≤ K, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ ((b - a : ℕ) : ℝ))
    (hcard : prefixFactorCount s L (L + C_0) ≤ L + C_0) :
    2 * lam * (L : ℝ) + 1 ≤
      13 * ((b - a : ℕ) : ℝ) + 3 * lam * (C_0 : ℝ) + 5 * (W : ℝ) + 3 := by
  have hminSlack : 0 < minSlack s (L + C_0) := by
    have h3 : ∀ k < L + C_0, 3 ≤ s k := by
      intro k hk
      have h := hs_lo k (by omega)
      omega
    exact (all_shifted_slacks_pos_of_three_le s (L + C_0) h3).1
  have hlam_pos : 0 < lam := by
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    linarith
  have hC_bound : ((L + C_0 : ℕ) : ℝ) ≤ 1 * (L : ℝ) + (C_0 : ℝ) := by
    push_cast
    linarith
  have hmain :=
    balanced_discrepancy_and_factor_complexity_exclusion
      (p := 3) (q := 5) (C := L + C_0) (D := ((b - a : ℕ) : ℝ))
      (kappa := 1) (C_0 := (C_0 : ℝ))
      (by decide : 1 ≤ 5) (by decide : 3 ^ 5 < 2 ^ (3 + 5))
      hL (by omega : (L + C_0) + L ≤ K) ha0 hchain hminSlack hlam_pos hbal hcard hC_bound
  norm_num at hmain
  linarith

/-! ## 5. Derived Mechanical Factor Complexity $\le L + 1$ & Unconditional Mechanical Exclusion -/

/-- Fractional part `mechPhase z = z - ⌊z⌋ ∈ [0, 1)` of a real number `z`. -/
noncomputable def mechPhase (z : ℝ) : ℝ :=
  z - ((⌊z⌋ : ℤ) : ℝ)

theorem mechPhase_bounds (z : ℝ) :
    0 ≤ mechPhase z ∧ mechPhase z < 1 := by
  unfold mechPhase
  have hlo := Int.floor_le z
  have hhi := Int.lt_floor_add_one z
  constructor <;> linarith

theorem eq_floor_add_mechPhase (z : ℝ) :
    z = ((⌊z⌋ : ℤ) : ℝ) + mechPhase z := by
  unfold mechPhase
  ring

private theorem floor_eq_of_bounds {A : ℝ} {B : ℤ}
    (hlo : (B : ℝ) ≤ A) (hhi : A < (B : ℝ) + 1) : ⌊A⌋ = B := by
  have h1 : ((⌊A⌋ : ℤ) : ℝ) < ((B + 1 : ℤ) : ℝ) := by
    push_cast
    linarith [Int.floor_le A]
  have h2 : (B : ℝ) < ((⌊A⌋ + 1 : ℤ) : ℝ) := by
    push_cast
    linarith [Int.lt_floor_add_one A]
  have h1' : ⌊A⌋ < B + 1 := by exact_mod_cast h1
  have h2' : B < ⌊A⌋ + 1 := by exact_mod_cast h2
  omega

/-- Exact floor addition identity in terms of `mechPhase`:
`⌊z + y⌋ = ⌊z⌋ + ⌊y⌋ + (if 1 - mechPhase y ≤ mechPhase z then 1 else 0)`. -/
theorem floor_add_eq_floor_add_ite (z y : ℝ) :
    ⌊z + y⌋ = ⌊z⌋ + ⌊y⌋ + (if 1 - mechPhase y ≤ mechPhase z then 1 else 0) := by
  rcases mechPhase_bounds z with ⟨hz0, hz1⟩
  rcases mechPhase_bounds y with ⟨hy0, hy1⟩
  have hz_eq := eq_floor_add_mechPhase z
  have hy_eq := eq_floor_add_mechPhase y
  split_ifs with h
  · apply floor_eq_of_bounds
    · push_cast; linarith
    · push_cast; linarith
  · apply floor_eq_of_bounds
    · push_cast; linarith
    · push_cast; linarith

open Classical in
/-- The subset of indices `j ∈ {1, ..., L}` whose phase threshold `1 - mechPhase (α * j)`
is crossed by the origin phase `mechPhase (α * r + ρ)`. -/
noncomputable def mechCrossedSet (α ρ : ℝ) (L r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (fun j => 1 - mechPhase (α * (j : ℝ)) ≤ mechPhase (α * (r : ℝ) + ρ))

open Classical in
/-- The number of thresholds in `{1, ..., L}` crossed by `mechPhase (α * r + ρ)`. -/
noncomputable def mechThresholdCount (α ρ : ℝ) (L r : ℕ) : ℕ :=
  (mechCrossedSet α ρ L r).card

/-- For every `α, ρ, L, r`, `mechThresholdCount α ρ L r ≤ L`. -/
theorem mechThresholdCount_le (α ρ : ℝ) (L r : ℕ) :
    mechThresholdCount α ρ L r ≤ L := by
  unfold mechThresholdCount mechCrossedSet
  calc
    ((Finset.Icc 1 L).filter _).card ≤ (Finset.Icc 1 L).card := Finset.card_filter_le _ _
    _ = L := by simp

open Classical in
/-- For every `j ≤ L`, the cumulative floor difference `⌊α (r + j) + ρ⌋ - ⌊α r + ρ⌋`
is completely determined by whether `j ∈ mechCrossedSet α ρ L r`. -/
theorem mech_cumulative_floor_diff_eq_of_le (α ρ : ℝ) {L r j : ℕ} (hj : j ≤ L) :
    ⌊α * ((r + j : ℕ) : ℝ) + ρ⌋ - ⌊α * (r : ℝ) + ρ⌋ =
      ⌊α * (j : ℝ)⌋ + (if j ∈ mechCrossedSet α ρ L r then 1 else 0) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj_pos
  · have hnot : 0 ∉ mechCrossedSet α ρ L r := by
      simp [mechCrossedSet]
    simp [hnot]
  · have hj1 : 1 ≤ j := by omega
    have hj_mem :
        j ∈ mechCrossedSet α ρ L r ↔
          1 - mechPhase (α * (j : ℝ)) ≤ mechPhase (α * (r : ℝ) + ρ) := by
      simp [mechCrossedSet, hj1, hj]
    have hadd :
        α * ((r + j : ℕ) : ℝ) + ρ = (α * (r : ℝ) + ρ) + (α * (j : ℝ)) := by
      push_cast
      ring
    rw [hadd, floor_add_eq_floor_add_ite (α * (r : ℝ) + ρ) (α * (j : ℝ))]
    by_cases hcond : 1 - mechPhase (α * (j : ℝ)) ≤ mechPhase (α * (r : ℝ) + ρ)
    · have hm : j ∈ mechCrossedSet α ρ L r := hj_mem.mpr hcond
      simp only [if_pos hcond, if_pos hm]
      ring
    · have hm : j ∉ mechCrossedSet α ρ L r := fun h => hcond (hj_mem.mp h)
      simp only [if_neg hcond, if_neg hm]
      ring

/-- If two origins `r1, r2` have the same crossed-threshold set `mechCrossedSet α ρ L`,
then their length-`L` mechanical factor windows are identical. -/
theorem mech_factorWindow_eq_of_mechCrossedSet_eq
    (a b : ℕ) (α ρ : ℝ) (L r1 r2 : ℕ)
    (heq : mechCrossedSet α ρ L r1 = mechCrossedSet α ρ L r2) :
    factorWindow (mechTwoLetterSeq a b α ρ) L r1 =
      factorWindow (mechTwoLetterSeq a b α ρ) L r2 := by
  rw [factorWindow_eq_iff]
  intro i hi
  have hi_le : i ≤ L := by omega
  have hi1_le : i + 1 ≤ L := by omega
  have h1_i := mech_cumulative_floor_diff_eq_of_le α ρ (r := r1) hi_le
  have h2_i := mech_cumulative_floor_diff_eq_of_le α ρ (r := r2) hi_le
  have h1_i1 := mech_cumulative_floor_diff_eq_of_le α ρ (r := r1) hi1_le
  have h2_i1 := mech_cumulative_floor_diff_eq_of_le α ρ (r := r2) hi1_le
  rw [heq] at h1_i h1_i1
  have hdiff_i :
      ⌊α * ((r1 + i : ℕ) : ℝ) + ρ⌋ - ⌊α * (r1 : ℝ) + ρ⌋ =
        ⌊α * ((r2 + i : ℕ) : ℝ) + ρ⌋ - ⌊α * (r2 : ℝ) + ρ⌋ :=
    h1_i.trans h2_i.symm
  have hdiff_i1 :
      ⌊α * ((r1 + (i + 1) : ℕ) : ℝ) + ρ⌋ - ⌊α * (r1 : ℝ) + ρ⌋ =
        ⌊α * ((r2 + (i + 1) : ℕ) : ℝ) + ρ⌋ - ⌊α * (r2 : ℝ) + ρ⌋ :=
    h1_i1.trans h2_i1.symm
  have hstep_diff :
      ⌊α * ((r1 + i + 1 : ℕ) : ℝ) + ρ⌋ - ⌊α * ((r1 + i : ℕ) : ℝ) + ρ⌋ =
        ⌊α * ((r2 + i + 1 : ℕ) : ℝ) + ρ⌋ - ⌊α * ((r2 + i : ℕ) : ℝ) + ρ⌋ := by
    rw [Nat.add_assoc r1 i 1, Nat.add_assoc r2 i 1]
    omega
  have hmechStep : mechStep α ρ (r1 + i) = mechStep α ρ (r2 + i) := by
    unfold mechStep
    rw [hstep_diff]
  unfold mechTwoLetterSeq
  rw [hmechStep]

/-- Nestedness of `mechCrossedSet`: if `mechPhase (α * r1 + ρ) ≤ mechPhase (α * r2 + ρ)`,
then `mechCrossedSet α ρ L r1 ⊆ mechCrossedSet α ρ L r2`. -/
theorem mechCrossedSet_subset_of_phase_le (α ρ : ℝ) (L r1 r2 : ℕ)
    (hphase : mechPhase (α * (r1 : ℝ) + ρ) ≤ mechPhase (α * (r2 : ℝ) + ρ)) :
    mechCrossedSet α ρ L r1 ⊆ mechCrossedSet α ρ L r2 := by
  intro j hj
  unfold mechCrossedSet at hj ⊢
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans hj.2 hphase⟩

/-- Two origins `r1, r2` with the same `mechThresholdCount α ρ L` have the same
`mechCrossedSet` and hence the same length-`L` mechanical factor window. -/
theorem mech_factorWindow_eq_of_mechThresholdCount_eq
    (a b : ℕ) (α ρ : ℝ) (L r1 r2 : ℕ)
    (hcard : mechThresholdCount α ρ L r1 = mechThresholdCount α ρ L r2) :
    factorWindow (mechTwoLetterSeq a b α ρ) L r1 =
      factorWindow (mechTwoLetterSeq a b α ρ) L r2 := by
  apply mech_factorWindow_eq_of_mechCrossedSet_eq
  rcases le_total (mechPhase (α * (r1 : ℝ) + ρ)) (mechPhase (α * (r2 : ℝ) + ρ)) with hle | hge
  · exact Finset.eq_of_subset_of_card_le
      (mechCrossedSet_subset_of_phase_le α ρ L r1 r2 hle) (le_of_eq hcard.symm)
  · exact (Finset.eq_of_subset_of_card_le
      (mechCrossedSet_subset_of_phase_le α ρ L r2 r1 hge) (le_of_eq hcard)).symm

open Classical in
/-- **Universal Factor Complexity Bound $\le L + 1$ for Mechanical Sequences
(`mechTwoLetterSeq_finset_factor_card_le`)**:
For **any** parameters `a, b : ℕ`, **any** real slope `α` and intercept `ρ`,
**any** window length `L : ℕ` (including `L = 0`), and **any** finite set of
origins `S : Finset ℕ`, the number of distinct length-`L` factors of
`mechTwoLetterSeq a b α ρ` occurring at origins in `S` is at most `L + 1`. -/
theorem mechTwoLetterSeq_finset_factor_card_le
    (a b : ℕ) (α ρ : ℝ) (L : ℕ) (S : Finset ℕ) :
    (S.image (factorWindow (mechTwoLetterSeq a b α ρ) L)).card ≤ L + 1 := by
  set f := factorWindow (mechTwoLetterSeq a b α ρ) L
  set g := mechThresholdCount α ρ L
  let φ : (Fin L → ℕ) → ℕ := fun w =>
    if h : ∃ r ∈ S, f r = w then g (Classical.choose h) else 0
  have hmaps : Set.MapsTo φ ↑(S.image f) ↑(Finset.range (L + 1)) := by
    intro w hw
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
    simp only [Finset.coe_range, Set.mem_Iio, φ, dif_pos hw]
    have hle : g (Classical.choose hw) ≤ L := mechThresholdCount_le α ρ L (Classical.choose hw)
    omega
  have hinj : Set.InjOn φ ↑(S.image f) := by
    intro w1 hw1 w2 hw2 heq
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw1 hw2
    simp only [φ, dif_pos hw1, dif_pos hw2] at heq
    have hr1 := (Classical.choose_spec hw1).2
    have hr2 := (Classical.choose_spec hw2).2
    have hfw := mech_factorWindow_eq_of_mechThresholdCount_eq a b α ρ L
      (Classical.choose hw1) (Classical.choose hw2) heq
    exact hr1.symm.trans (hfw.trans hr2)
  calc
    (S.image f).card ≤ (Finset.range (L + 1)).card :=
      Finset.card_le_card_of_injOn φ hmaps hinj
    _ = L + 1 := Finset.card_range (L + 1)

/-- **Derived Prefix Factor Complexity Bound for `mechTwoLetterSeq`
(`mechTwoLetterSeq_prefixFactorCount_le`)**:
For every `a, b, L, C : ℕ` and `α, ρ : ℝ`,
`prefixFactorCount (mechTwoLetterSeq a b α ρ) L C ≤ L + 1`. -/
theorem mechTwoLetterSeq_prefixFactorCount_le
    (a b : ℕ) (α ρ : ℝ) (L C : ℕ) :
    prefixFactorCount (mechTwoLetterSeq a b α ρ) L C ≤ L + 1 :=
  mechTwoLetterSeq_finset_factor_card_le a b α ρ L (Finset.range (C + 1))

/-- **Unconditional Finite-Horizon Cutoff for Arbitrary Two-Letter Mechanical Block Chains
(`unconditional_mechanical_two_letter_finite_cutoff`)**:
For **any** two block lengths `3 ≤ a ≤ b`, slope `0 ≤ α ≤ 1`, intercept `ρ : ℝ`,
seed `a_0 < 2^W`, window length `1 ≤ L`, and horizon `2 * L + 1 ≤ K`, if
`ValidBlockChain a_0 (mechTwoLetterSeq a b α ρ) u K` holds, then (with **no**
assumed complexity or discrepancy hypothesis):
`2 * ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) * (L : ℝ) + 1 ≤
  13 * ((b - a : ℕ) : ℝ) + 3 * ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) + 5 * (W : ℝ) + 3`. -/
theorem unconditional_mechanical_two_letter_finite_cutoff
    {a b a_0 W L K : ℕ} {α ρ : ℝ} {u : ℕ → ℕ}
    (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hL : 1 ≤ L) (hK : 2 * L + 1 ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 (mechTwoLetterSeq a b α ρ) u K) :
    2 * ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) * (L : ℝ) + 1 ≤
      13 * ((b - a : ℕ) : ℝ) +
        3 * ((a : ℝ) + ((b - a : ℕ) : ℝ) * α) + 5 * (W : ℝ) + 3 := by
  set lam : ℝ := (a : ℝ) + ((b - a : ℕ) : ℝ) * α
  have hs_lo : ∀ k < K, a ≤ mechTwoLetterSeq a b α ρ k := fun k _ =>
    (mechTwoLetterSeq_bounds hab hα0 hα1 k).1
  have hlam_lo : (a : ℝ) ≤ lam := by
    unfold lam
    have hba : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg (b - a)
    nlinarith
  have hbal : ∀ n ≤ K,
      |(blockSteps (mechTwoLetterSeq a b α ρ) n : ℝ) - lam * (n : ℝ)| ≤
        ((b - a : ℕ) : ℝ) := fun n _ =>
    mechTwoLetterSeq_balanced_discrepancy hα0 hα1 n
  have hcard : prefixFactorCount (mechTwoLetterSeq a b α ρ) L (L + 1) ≤ L + 1 :=
    mechTwoLetterSeq_prefixFactorCount_le a b α ρ L (L + 1)
  have hcut :=
    arbitrary_two_letter_ceiling_saturated_sturmian_exclusion
      (C_0 := 1) ha3 hL hK ha0 hchain hs_lo hlam_lo hbal hcard
  simpa using hcut

private theorem n_lt_two_pow_ep (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- **Unconditional Infinite-Horizon Exclusion of Mechanical / Sturmian Block Chains
(`no_infinite_mechanical_two_letter_block_chain`)**:
For **any** two block lengths `3 ≤ a ≤ b`, slope `0 ≤ α ≤ 1`, intercept `ρ : ℝ`,
and nonnegative integer seed `a_0 : ℕ`, there is **no** infinite valid integer
block chain with block lengths `mechTwoLetterSeq a b α ρ`. -/
theorem no_infinite_mechanical_two_letter_block_chain
    {a b a_0 : ℕ} {α ρ : ℝ}
    (ha3 : 3 ≤ a) (hab : a ≤ b) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 (mechTwoLetterSeq a b α ρ) u K) := by
  rintro ⟨u, hchain⟩
  have ha0 : a_0 < 2 ^ a_0 := n_lt_two_pow_ep a_0
  set lam : ℝ := (a : ℝ) + ((b - a : ℕ) : ℝ) * α
  have hlam_pos : 0 < lam := by
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hba : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg (b - a)
    unfold lam
    nlinarith
  set RHS : ℝ := 13 * ((b - a : ℕ) : ℝ) + 3 * lam + 5 * (a_0 : ℝ) + 3
  have hRHS_pos : 0 ≤ RHS := by unfold RHS; positivity
  obtain ⟨L, hL_gt⟩ := exists_nat_gt (RHS / (2 * lam) + 1)
  have hL1 : 1 ≤ L := by
    have hdiv : 0 ≤ RHS / (2 * lam) := div_nonneg hRHS_pos (by linarith)
    have hgt1 : (1 : ℝ) < (L : ℝ) := by linarith
    exact_mod_cast (le_of_lt hgt1)
  have hcut :=
    unconditional_mechanical_two_letter_finite_cutoff
      ha3 hab hα0 hα1 hL1 le_rfl ha0 (hchain (2 * L + 1))
  have hmul_gt : RHS < 2 * lam * (L : ℝ) := by
    have h1 : RHS / (2 * lam) < (L : ℝ) := by linarith
    have h2 : RHS < (L : ℝ) * (2 * lam) := (div_lt_iff₀ (by linarith)).mp h1
    linarith
  change 2 * lam * (L : ℝ) + 1 ≤ RHS at hcut
  linarith

/-! ## 6. Real Logarithmic Threshold Bridge, Asymptotic Mean & Liminf Complexity Exclusion -/

/-- **Real Logarithmic Threshold Rational Selection Bridge (`exists_pq_of_lt_log_threshold`)**:
For **every** real complexity slope `kappa` strictly below `1 / log_2(3 / 2) = log 2 / log(3 / 2)`
(equivalently `kappa * Real.log (3 / 2) < Real.log 2`), there exist natural numbers
`p, q : ℕ` such that `1 ≤ q`, `3^q < 2^(p + q)`, and `(p : ℝ) * kappa < (q : ℝ)`. -/
theorem exists_pq_of_lt_log_threshold {kappa : ℝ}
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ)) :
    ∃ p q : ℕ, 1 ≤ q ∧ 3 ^ q < 2 ^ (p + q) ∧ (p : ℝ) * kappa < (q : ℝ) := by
  by_cases hkap : kappa ≤ 0
  · refine ⟨1, 1, le_rfl, by decide, ?_⟩
    push_cast
    linarith
  · push_neg at hkap
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog32 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
    set γ : ℝ := Real.log (3 / 2 : ℝ) / Real.log (2 : ℝ)
    have hγ_pos : 0 < γ := div_pos hlog32 hlog2
    have hγ_kap : γ * kappa < 1 := by
      unfold γ
      rw [div_mul_eq_mul_div, div_lt_one hlog2]
      linarith
    set gap : ℝ := 1 - γ * kappa
    have hgap_pos : 0 < gap := by unfold gap; linarith
    obtain ⟨q, hq_gt⟩ := exists_nat_gt (kappa / gap + 1)
    have hdiv_pos : 0 < kappa / gap := div_pos hkap hgap_pos
    have hq_ge1 : 1 ≤ q := by
      have h1 : (1 : ℝ) < (q : ℝ) := by linarith
      exact_mod_cast (le_of_lt h1)
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_ge1
    have hkap_lt : kappa < (q : ℝ) * gap := by
      have h1 : kappa / gap < (q : ℝ) := by linarith
      exact (div_lt_iff₀ hgap_pos).mp h1
    set p : ℕ := Int.toNat (⌊γ * (q : ℝ)⌋ + 1)
    have hγq_pos : 0 < γ * (q : ℝ) := mul_pos hγ_pos hq_pos
    have hfl_nonneg : 0 ≤ ⌊γ * (q : ℝ)⌋ := Int.floor_nonneg.mpr (le_of_lt hγq_pos)
    have hp_cast : (p : ℝ) = ((⌊γ * (q : ℝ)⌋ : ℤ) : ℝ) + 1 := by
      have h : ((p : ℕ) : ℤ) = ⌊γ * (q : ℝ)⌋ + 1 :=
        Int.toNat_of_nonneg (by omega)
      exact_mod_cast h
    have hp_gt : γ * (q : ℝ) < (p : ℝ) := by
      rw [hp_cast]
      exact Int.lt_floor_add_one (γ * (q : ℝ))
    have hp_le : (p : ℝ) ≤ γ * (q : ℝ) + 1 := by
      rw [hp_cast]
      linarith [Int.floor_le (γ * (q : ℝ))]
    have hp_kap : (p : ℝ) * kappa < (q : ℝ) := by
      have h1 : (p : ℝ) * kappa ≤ (γ * (q : ℝ) + 1) * kappa :=
        mul_le_mul_of_nonneg_right hp_le (le_of_lt hkap)
      have h2 : (γ * (q : ℝ) + 1) * kappa < (q : ℝ) := by
        unfold gap at hkap_lt
        nlinarith
      exact lt_of_le_of_lt h1 h2
    have hlog_ineq : (q : ℝ) * Real.log (3 / 2 : ℝ) < (p : ℝ) * Real.log (2 : ℝ) := by
      have h1 : γ * (q : ℝ) * Real.log (2 : ℝ) < (p : ℝ) * Real.log (2 : ℝ) :=
        mul_lt_mul_of_pos_right hp_gt hlog2
      have h2 : γ * (q : ℝ) * Real.log (2 : ℝ) = (q : ℝ) * Real.log (3 / 2 : ℝ) := by
        unfold γ
        have hne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2
        field_simp [hne]
        ring
      linarith
    have hlog3_eq : Real.log (3 : ℝ) = Real.log (3 / 2 : ℝ) + Real.log (2 : ℝ) := by
      have hmul : (3 : ℝ) = (3 / 2 : ℝ) * (2 : ℝ) := by norm_num
      conv_lhs => rw [hmul]
      exact Real.log_mul (by norm_num) (by norm_num)
    have hlog_pow : Real.log ((3 : ℝ) ^ q) < Real.log ((2 : ℝ) ^ (p + q)) := by
      rw [Real.log_pow, Real.log_pow, hlog3_eq, Nat.cast_add]
      linarith
    have hpow_real : (3 : ℝ) ^ q < (2 : ℝ) ^ (p + q) := by
      have hexp := Real.exp_lt_exp.mpr hlog_pow
      rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hexp
    have hpow_nat : 3 ^ q < 2 ^ (p + q) := by exact_mod_cast hpow_real
    exact ⟨p, q, hq_ge1, hpow_nat, hp_kap⟩

/-- If a finite set `F` contains every length-`L` factor of `s`, then
`prefixFactorCount s L C ≤ F.card` for every prefix horizon `C`. -/
theorem prefixFactorCount_le_of_global_factor_finset
    (s : ℕ → ℕ) (L C : ℕ) (F : Finset (Fin L → ℕ))
    (hF : ∀ r : ℕ, factorWindow s L r ∈ F) :
    prefixFactorCount s L C ≤ F.card := by
  unfold prefixFactorCount prefixFactorSet
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_image] at hw
  rcases hw with ⟨r, _, rfl⟩
  exact hF r

/-- **Bridge from `Filter.Tendsto` of Average Block Length to Linear Prefix Discrepancy
(`asymptotic_mean_discrepancy_of_tendsto`)**:
If `Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ)) Filter.atTop (nhds lam)`,
then for every `ε > 0`, there exists `N_0 : ℕ` such that for all `n ≥ N_0`,
`|(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ ε * (n : ℝ)`. -/
theorem asymptotic_mean_discrepancy_of_tendsto
    {s : ℕ → ℕ} {lam : ℝ}
    (htend : Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ))
      Filter.atTop (nhds lam)) :
    ∀ ε > 0, ∃ N_0 : ℕ, ∀ n ≥ N_0,
      |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ ε * (n : ℝ) := by
  intro ε hε
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N_1, hN_1⟩ := htend ε hε
  refine ⟨max N_1 1, ?_⟩
  intro n hn
  have hn1 : N_1 ≤ n := le_trans (le_max_left N_1 1) hn
  have hn_pos : 1 ≤ n := le_trans (le_max_right N_1 1) hn
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  have hdist := hN_1 n hn1
  rw [Real.dist_eq] at hdist
  have hmul :
      |(blockSteps s n : ℝ) / (n : ℝ) - lam| * (n : ℝ) ≤ ε * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt hdist) (le_of_lt hn_real_pos)
  have heq :
      (blockSteps s n : ℝ) - lam * (n : ℝ) =
        ((blockSteps s n : ℝ) / (n : ℝ) - lam) * (n : ℝ) := by
    field_simp [hn_ne]
    ring
  rw [heq, abs_mul, abs_of_pos hn_real_pos]
  exact hmul

/-- Uniform bound on `|T(n) - lam * n|` over `0 ≤ n ≤ K` from an eventual linear bound
after `N_0`. -/
private theorem prefix_discrepancy_bound_of_eventual
    (s : ℕ → ℕ) (lam ε : ℝ) (N_0 K : ℕ) (hε : 0 ≤ ε)
    (hev : ∀ n ≥ N_0, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ ε * (n : ℝ)) :
    ∀ n ≤ K,
      |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤
        (∑ k ∈ Finset.range N_0, |(blockSteps s k : ℝ) - lam * (k : ℝ)|) +
          ε * (K : ℝ) := by
  intro n hnK
  have hsum_nonneg :
      0 ≤ ∑ k ∈ Finset.range N_0, |(blockSteps s k : ℝ) - lam * (k : ℝ)| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg _)
  by_cases hn : n < N_0
  · have hmem : n ∈ Finset.range N_0 := Finset.mem_range.mpr hn
    have hle_sum :
        |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤
          ∑ k ∈ Finset.range N_0, |(blockSteps s k : ℝ) - lam * (k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(blockSteps s k : ℝ) - lam * (k : ℝ)|)
        (fun k _ => abs_nonneg _) hmem
    have hK_nonneg : 0 ≤ ε * (K : ℝ) := mul_nonneg hε (Nat.cast_nonneg K)
    linarith
  · push_neg at hn
    have h1 := hev n hn
    have hnK_real : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnK
    have h2 : ε * (n : ℝ) ≤ ε * (K : ℝ) := mul_le_mul_of_nonneg_left hnK_real hε
    linarith

/-- **Infinite-Horizon Exclusion Under Asymptotic Mean & Liminf Sub-Critical Complexity
(`no_infinite_asymptotic_mean_liminf_subcritical_block_chain`)**:
Suppose `1 ≤ q`, `3^q < 2^(p + q)`, `0 < lam`, `0 ≤ kappa`, `0 ≤ C_0`, and
`(p : ℝ) * kappa < (q : ℝ)`. If a sequence `s` has:
1. **Asymptotic Mean**: `∀ ε > 0, ∃ N_0 : ℕ, ∀ n ≥ N_0, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ ε * (n : ℝ)`, and
2. **Liminf Sub-Critical Complexity**: for every `L_min : ℕ`, there exists `L ≥ L_min`
   such that `prefixFactorCount s L (C L) ≤ C L` and `(C L : ℝ) ≤ kappa * (L : ℝ) + C_0`,
then no infinite surviving integer block chain can have block lengths `s`. -/
theorem no_infinite_asymptotic_mean_liminf_subcritical_block_chain
    {p q a_0 W : ℕ} {s u C : ℕ → ℕ} {lam kappa C_0 : ℝ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (ha0 : a_0 < 2 ^ W)
    (hlam : 0 < lam) (hkap : 0 ≤ kappa) (hC0 : 0 ≤ C_0)
    (hsub : (p : ℝ) * kappa < (q : ℝ))
    (hmean : ∀ ε > 0, ∃ N_0 : ℕ, ∀ n ≥ N_0,
      |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ ε * (n : ℝ))
    (hliminf : ∀ L_min : ℕ, ∃ L ≥ L_min,
      prefixFactorCount s L (C L) ≤ C L ∧ (C L : ℝ) ≤ kappa * (L : ℝ) + C_0) :
    ¬ ((∀ K : ℕ, ValidBlockChain a_0 s u K) ∧ (∀ m : ℕ, 0 < minSlack s m)) := by
  rintro ⟨hchain, hminSlack⟩
  set δ : ℝ := lam * ((q : ℝ) - (p : ℝ) * kappa)
  have hδ_pos : 0 < δ := mul_pos hlam (by linarith)
  set A : ℝ := 2 * (q : ℝ) + (p : ℝ)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hA_pos : 0 < A := by unfold A; linarith
  have hkap1_pos : 0 < kappa + 1 := by linarith
  set ε : ℝ := δ / (2 * A * (kappa + 1))
  have hε_pos : 0 < ε := by unfold ε; positivity
  obtain ⟨N_0, hN_0⟩ := hmean ε hε_pos
  set M_0 : ℝ := ∑ k ∈ Finset.range N_0, |(blockSteps s k : ℝ) - lam * (k : ℝ)|
  have hM0_nonneg : 0 ≤ M_0 := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  set ConstRHS : ℝ :=
    A * (M_0 + ε * C_0) + (p : ℝ) * lam * C_0 + (q : ℝ) * (W : ℝ) + (p : ℝ)
  have hConst_nonneg : 0 ≤ ConstRHS := by unfold ConstRHS; positivity
  obtain ⟨L_min, hL_min⟩ := exists_nat_gt (ConstRHS / (δ / 2) + 1)
  have hL_min_ge1 : 1 ≤ L_min := by
    have hdiv : 0 ≤ ConstRHS / (δ / 2) := div_nonneg hConst_nonneg (by linarith)
    have h1 : (1 : ℝ) < (L_min : ℝ) := by linarith
    exact_mod_cast (le_of_lt h1)
  obtain ⟨L, hL_ge, hcard, hC_bound⟩ := hliminf L_min
  have hL1 : 1 ≤ L := le_trans hL_min_ge1 hL_ge
  set D_L : ℝ := M_0 + ε * (C_0 + (kappa + 1) * (L : ℝ))
  have hbal_L : ∀ n ≤ C L + L, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ D_L := by
    intro n hn
    have h1 := prefix_discrepancy_bound_of_eventual s lam ε N_0 (C L + L)
      (le_of_lt hε_pos) hN_0 n hn
    have hCL_cast : ((C L + L : ℕ) : ℝ) ≤ C_0 + (kappa + 1) * (L : ℝ) := by
      push_cast
      linarith
    have h2 : ε * ((C L + L : ℕ) : ℝ) ≤ ε * (C_0 + (kappa + 1) * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hCL_cast (le_of_lt hε_pos)
    unfold D_L
    linarith
  have hcut :=
    balanced_discrepancy_and_factor_complexity_exclusion
      (D := D_L) hq hpq hL1 le_rfl ha0 (hchain (C L + L)) (hminSlack (C L))
      hlam hbal_L hcard hC_bound
  change δ * (L : ℝ) + 1 ≤
    A * D_L + (p : ℝ) * lam * C_0 + (q : ℝ) * (W : ℝ) + (p : ℝ) at hcut
  have hA_eps : A * (ε * ((kappa + 1) * (L : ℝ))) = (δ / 2) * (L : ℝ) := by
    unfold ε
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hk_ne : kappa + 1 ≠ 0 := ne_of_gt hkap1_pos
    field_simp [hA_ne, hk_ne]
    ring
  have hRHS_expand :
      A * D_L + (p : ℝ) * lam * C_0 + (q : ℝ) * (W : ℝ) + (p : ℝ) =
        ConstRHS + (δ / 2) * (L : ℝ) := by
    unfold D_L ConstRHS
    linear_combination hA_eps
  rw [hRHS_expand] at hcut
  have hL_real_ge : (L_min : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge
  have hmul_gt : ConstRHS < (δ / 2) * (L : ℝ) := by
    have h1 : ConstRHS / (δ / 2) < (L : ℝ) := by linarith
    have h2 : ConstRHS < (L : ℝ) * (δ / 2) := (div_lt_iff₀ (by linarith)).mp h1
    linarith
  linarith

/-- **Full Logarithmic-Threshold Exclusion Under `Filter.Tendsto` Mean & Liminf Complexity
(`no_infinite_tendsto_mean_log_threshold_block_chain`)**:
For **every** complexity slope `0 ≤ kappa` satisfying `kappa * Real.log (3 / 2) < Real.log 2`
(`kappa < 1 / log_2(3 / 2) ≈ 1.709511`), if `Filter.Tendsto (fun n => (blockSteps s n : ℝ) / (n : ℝ)) Filter.atTop (nhds lam)`
with `0 < lam` and `s` has liminf complexity `(C L : ℝ) ≤ kappa * L + C_0` (`0 ≤ C_0`)
at arbitrarily large lengths `L`, then no infinite surviving integer block chain exists. -/
theorem no_infinite_tendsto_mean_log_threshold_block_chain
    {a_0 : ℕ} {s u C : ℕ → ℕ} {lam kappa C_0 : ℝ}
    (hlam : 0 < lam) (hkap : 0 ≤ kappa) (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ))
    (htend : Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ))
      Filter.atTop (nhds lam))
    (hliminf : ∀ L_min : ℕ, ∃ L ≥ L_min,
      prefixFactorCount s L (C L) ≤ C L ∧ (C L : ℝ) ≤ kappa * (L : ℝ) + C_0) :
    ¬ ((∀ K : ℕ, ValidBlockChain a_0 s u K) ∧ (∀ m : ℕ, 0 < minSlack s m)) := by
  obtain ⟨p, q, hq, hpq, hsub⟩ := exists_pq_of_lt_log_threshold hlog
  have ha0 : a_0 < 2 ^ a_0 := n_lt_two_pow_ep a_0
  exact no_infinite_asymptotic_mean_liminf_subcritical_block_chain
    hq hpq ha0 hlam hkap hC0 hsub
    (asymptotic_mean_discrepancy_of_tendsto htend) hliminf

/-- The maximum cumulative discrepancy `E_H = max_{0 ≤ n ≤ H} |T(n) - lam * n|` over a finite prefix `0, ..., H`. -/
noncomputable def maxPrefixDiscrepancy (s : ℕ → ℕ) (lam : ℝ) (H : ℕ) : ℝ :=
  ((Finset.range (H + 1)).image (fun n : ℕ => |(blockSteps s n : ℝ) - lam * (n : ℝ)|)).max'
    (by simp)

/-- For every `n ≤ H`, `|(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ maxPrefixDiscrepancy s lam H`. -/
theorem abs_blockSteps_sub_le_maxPrefixDiscrepancy
    (s : ℕ → ℕ) (lam : ℝ) {H n : ℕ} (hn : n ≤ H) :
    |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ maxPrefixDiscrepancy s lam H := by
  unfold maxPrefixDiscrepancy
  apply Finset.le_max'
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨n, by omega, rfl⟩

/-- **Explicit `D = E_L` Finite Cutoff Formula (`balanced_cutoff_with_maxPrefixDiscrepancy`)**:
Applying `balanced_discrepancy_and_factor_complexity_exclusion` with
`D = maxPrefixDiscrepancy s lam (C + L)` and `(C : ℝ) ≤ kappa * (L : ℝ)` (`C_0 = 0`) yields:
`lam * ((q : ℝ) - (p : ℝ) * kappa) * (L : ℝ) + 1 ≤
  (2 * (q : ℝ) + (p : ℝ)) * maxPrefixDiscrepancy s lam (C + L) + (q : ℝ) * (W : ℝ) + (p : ℝ)`. -/
theorem balanced_cutoff_with_maxPrefixDiscrepancy
    {p q a_0 W L C K : ℕ} {s u : ℕ → ℕ} {lam kappa : ℝ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (hL : 1 ≤ L) (hK : C + L ≤ K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hminSlack : 0 < minSlack s C)
    (hlam : 0 < lam)
    (hcard : prefixFactorCount s L C ≤ C)
    (hC_bound : (C : ℝ) ≤ kappa * (L : ℝ)) :
    lam * ((q : ℝ) - (p : ℝ) * kappa) * (L : ℝ) + 1 ≤
      (2 * (q : ℝ) + (p : ℝ)) * maxPrefixDiscrepancy s lam (C + L) +
        (q : ℝ) * (W : ℝ) + (p : ℝ) := by
  have hC0 : (C : ℝ) ≤ kappa * (L : ℝ) + 0 := by linarith
  have hchain_CL : ValidBlockChain a_0 s u (C + L) :=
    fun k hk => hchain k (by omega)
  have hbal : ∀ n ≤ C + L,
      |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ maxPrefixDiscrepancy s lam (C + L) :=
    fun n hn => abs_blockSteps_sub_le_maxPrefixDiscrepancy s lam hn
  have hcut :=
    balanced_discrepancy_and_factor_complexity_exclusion
      (K := C + L) (D := maxPrefixDiscrepancy s lam (C + L)) (C_0 := 0)
      hq hpq hL le_rfl ha0 hchain_CL hminSlack hlam hbal hcard hC0
  linarith

/-! ## 6. Normalized Discrepancy Convergence, Scale-Local Balance, Non-Stationary Family & Recurrence Bridge -/

/-- Exact converse to `exists_repeated_subword_of_prefixFactorCount_le`:
if `r1 < r2 ≤ C` have matching length-`L` windows, then `prefixFactorCount s L C ≤ C`. -/
theorem prefixFactorCount_le_of_repeated_subword
    (s : ℕ → ℕ) {L C r1 r2 : ℕ}
    (hr12 : r1 < r2) (hr2C : r2 ≤ C)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    prefixFactorCount s L C ≤ C := by
  have hwin : factorWindow s L r1 = factorWindow s L r2 :=
    (factorWindow_eq_iff s L r1 r2).mpr hmatch
  have hsub :
      prefixFactorSet s L C ⊆ ((Finset.range (C + 1)).erase r2).image (factorWindow s L) := by
    intro w hw
    unfold prefixFactorSet at hw
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase] at hw ⊢
    rcases hw with ⟨r, hr, rfl⟩
    by_cases heq : r = r2
    · subst heq
      exact ⟨r1, ⟨by omega, by omega⟩, hwin⟩
    · exact ⟨r, ⟨heq, hr⟩, rfl⟩
  have hcard1 :
      prefixFactorCount s L C ≤
        (((Finset.range (C + 1)).erase r2).image (factorWindow s L)).card :=
    Finset.card_le_card hsub
  have hcard2 :
      (((Finset.range (C + 1)).erase r2).image (factorWindow s L)).card ≤
        ((Finset.range (C + 1)).erase r2).card :=
    Finset.card_image_le
  have hmem_r2 : r2 ∈ Finset.range (C + 1) := Finset.mem_range.mpr (by omega)
  have hcard3 : ((Finset.range (C + 1)).erase r2).card = C := by
    rw [Finset.card_erase_of_mem hmem_r2, Finset.card_range]
    omega
  omega

/-- Exact two-way equivalence between `prefixFactorCount s L C ≤ C` and existence of a
repeated length-`L` subword at `r1 < r2 ≤ C`. -/
theorem prefixFactorCount_le_iff_exists_repeated_subword (s : ℕ → ℕ) (L C : ℕ) :
    prefixFactorCount s L C ≤ C ↔
      ∃ r1 r2 : ℕ, r1 < r2 ∧ r2 ≤ C ∧ ∀ i < L, s (r1 + i) = s (r2 + i) :=
  ⟨exists_repeated_subword_of_prefixFactorCount_le s L C,
    fun ⟨_, _, hr12, hr2C, hmatch⟩ => prefixFactorCount_le_of_repeated_subword s hr12 hr2C hmatch⟩

/-- Nonnegativity of `maxPrefixDiscrepancy s lam H` (since at `n = 0`, `|T(0) - lam * 0| = 0`). -/
theorem maxPrefixDiscrepancy_nonneg (s : ℕ → ℕ) (lam : ℝ) (H : ℕ) :
    0 ≤ maxPrefixDiscrepancy s lam H := by
  have h0 := abs_blockSteps_sub_le_maxPrefixDiscrepancy s lam (Nat.zero_le H)
  exact le_trans (abs_nonneg _) h0

/-- Upper bound criterion for `maxPrefixDiscrepancy s lam H`: if `|(blockSteps s n : ℝ) - lam * n| ≤ B`
for all `n ≤ H`, then `maxPrefixDiscrepancy s lam H ≤ B`. -/
theorem maxPrefixDiscrepancy_le_of_forall_le
    {s : ℕ → ℕ} {lam B : ℝ} {H : ℕ}
    (hB : ∀ n ≤ H, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ B) :
    maxPrefixDiscrepancy s lam H ≤ B := by
  unfold maxPrefixDiscrepancy
  apply Finset.max'_le
  intro y hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  rcases hy with ⟨n, hn_lt, rfl⟩
  exact hB n (by omega)

/-- **Normalized Maximum-Discrepancy Convergence (`maxPrefixDiscrepancy_div_tendsto_zero`)**:
If `Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ)) Filter.atTop (nhds lam)`,
then `maxPrefixDiscrepancy s lam H / (H : ℝ) → 0` as `H → ∞`. -/
theorem maxPrefixDiscrepancy_div_tendsto_zero
    {s : ℕ → ℕ} {lam : ℝ}
    (htend : Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ))
      Filter.atTop (nhds lam)) :
    Filter.Tendsto (fun H : ℕ => maxPrefixDiscrepancy s lam H / (H : ℝ))
      Filter.atTop (nhds 0) := by
  have hmean := asymptotic_mean_discrepancy_of_tendsto htend
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨N_0, hN_0⟩ := hmean (ε / 3) hε3
  set M_0 : ℝ := ∑ k ∈ Finset.range N_0, |(blockSteps s k : ℝ) - lam * (k : ℝ)|
  have hM0_nonneg : 0 ≤ M_0 := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  obtain ⟨H_0, hH_0⟩ := exists_nat_gt (M_0 / (ε / 3) + 1)
  refine ⟨max H_0 1, ?_⟩
  intro H hH
  have hH0_le : H_0 ≤ H := le_trans (le_max_left H_0 1) hH
  have hH1 : 1 ≤ H := le_trans (le_max_right H_0 1) hH
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
  have hmax_le : maxPrefixDiscrepancy s lam H ≤ M_0 + (ε / 3) * (H : ℝ) := by
    apply maxPrefixDiscrepancy_le_of_forall_le
    intro n hn
    exact prefix_discrepancy_bound_of_eventual s lam (ε / 3) N_0 H (le_of_lt hε3) hN_0 n hn
  have hM0_lt : M_0 < (ε / 3) * (H : ℝ) := by
    have hH_ge : (H_0 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH0_le
    have h1 : M_0 / (ε / 3) < (H : ℝ) := by linarith
    have h2 : M_0 < (H : ℝ) * (ε / 3) := (div_lt_iff₀ hε3).mp h1
    linarith
  have hdiv_le : maxPrefixDiscrepancy s lam H / (H : ℝ) ≤ 2 * (ε / 3) := by
    rw [div_le_iff₀ hH_pos]
    linarith
  have hdiv_nonneg : 0 ≤ maxPrefixDiscrepancy s lam H / (H : ℝ) :=
    div_nonneg (maxPrefixDiscrepancy_nonneg s lam H) (le_of_lt hH_pos)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdiv_nonneg]
  linarith

/-- Global set of all length-`L` factors occurring anywhere in `s`. -/
def globalFactorSet (s : ℕ → ℕ) (L : ℕ) : Set (Fin L → ℕ) :=
  Set.range (factorWindow s L)

/-- Global factor complexity `P(L) = Nat.card (globalFactorSet s L)`. -/
noncomputable def globalFactorComplexity (s : ℕ → ℕ) (L : ℕ) : ℕ :=
  Nat.card (globalFactorSet s L)

/-- Whenever `globalFactorSet s L` is finite, every prefix factor count is bounded by
the global factor complexity `globalFactorComplexity s L`. -/
theorem prefixFactorCount_le_globalFactorComplexity
    (s : ℕ → ℕ) (L C : ℕ) (hfin : (globalFactorSet s L).Finite) :
    prefixFactorCount s L C ≤ globalFactorComplexity s L := by
  unfold globalFactorComplexity
  rw [Set.Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  apply prefixFactorCount_le_of_global_factor_finset s L C hfin.toFinset
  intro r
  rw [Set.Finite.mem_toFinset]
  exact ⟨r, rfl⟩

/-- **Global-Factor-Complexity & Liminf Wrapper (`no_infinite_global_complexity_log_threshold_block_chain`)**:
If a sequence `s` has a positive limiting mean `T(n) / n → lam > 0`, finite global
factor sets at each length, and `globalFactorComplexity s L ≤ kappa * L + C_0` at
arbitrarily large lengths `L` for some `kappa * log(3/2) < log 2`, then no infinite
surviving integer block chain exists. -/
theorem no_infinite_global_complexity_log_threshold_block_chain
    {a_0 : ℕ} {s u : ℕ → ℕ} {lam kappa C_0 : ℝ}
    (hlam : 0 < lam) (hkap : 0 ≤ kappa) (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ))
    (htend : Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ))
      Filter.atTop (nhds lam))
    (hfin : ∀ L : ℕ, (globalFactorSet s L).Finite)
    (hliminf : ∀ L_min : ℕ, ∃ L ≥ L_min,
      (globalFactorComplexity s L : ℝ) ≤ kappa * (L : ℝ) + C_0) :
    ¬ ((∀ K : ℕ, ValidBlockChain a_0 s u K) ∧ (∀ m : ℕ, 0 < minSlack s m)) := by
  apply no_infinite_tendsto_mean_log_threshold_block_chain
    (C := globalFactorComplexity s) hlam hkap hC0 hlog htend
  intro L_min
  obtain ⟨L, hL_ge, hbound⟩ := hliminf L_min
  exact ⟨L, hL_ge,
    prefixFactorCount_le_globalFactorComplexity s L (globalFactorComplexity s L) (hfin L),
    hbound⟩

/-- **Scale-Local Balance Exclusion Without a Global Limiting Mean
(`no_infinite_scale_local_balanced_block_chain`)**:
Suppose `0 < lam_min`, `0 ≤ kappa`, `0 ≤ C_0`, and `kappa * Real.log (3 / 2) < Real.log 2`.
If for every length threshold `L_min : ℕ` and relative error `ε > 0`, there exist a
good scale `L ≥ L_min`, prefix horizon `C`, and scale-local slope `lam_L ≥ lam_min`
satisfying:
1. `prefixFactorCount s L C ≤ C`,
2. `(C : ℝ) ≤ kappa * (L : ℝ) + C_0`, and
3. `maxPrefixDiscrepancy s lam_L (C + L) ≤ ε * lam_L * (L : ℝ)`,
then no infinite surviving integer block chain can have block lengths `s`—even when
`blockSteps s n / n` has no global limit as `n → ∞`. -/
theorem no_infinite_scale_local_balanced_block_chain
    {a_0 : ℕ} {s u : ℕ → ℕ} {lam_min kappa C_0 : ℝ}
    (hlam_min : 0 < lam_min) (_hkap : 0 ≤ kappa) (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ))
    (hscale : ∀ (L_min : ℕ) (ε : ℝ), 0 < ε →
      ∃ (L C : ℕ) (lam_L : ℝ),
        L_min ≤ L ∧ lam_min ≤ lam_L ∧
          prefixFactorCount s L C ≤ C ∧
          (C : ℝ) ≤ kappa * (L : ℝ) + C_0 ∧
          maxPrefixDiscrepancy s lam_L (C + L) ≤ ε * lam_L * (L : ℝ)) :
    ¬ ((∀ K : ℕ, ValidBlockChain a_0 s u K) ∧ (∀ m : ℕ, 0 < minSlack s m)) := by
  rintro ⟨hchain, hminSlack⟩
  obtain ⟨p, q, hq, hpq, hsub⟩ := exists_pq_of_lt_log_threshold hlog
  have ha0 : a_0 < 2 ^ a_0 := n_lt_two_pow_ep a_0
  set gap : ℝ := (q : ℝ) - (p : ℝ) * kappa
  have hgap_pos : 0 < gap := by unfold gap; linarith
  set A : ℝ := 2 * (q : ℝ) + (p : ℝ)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hA_pos : 0 < A := by unfold A; linarith
  set ε : ℝ := gap / (2 * A)
  have hε_pos : 0 < ε := by unfold ε; positivity
  set B_const : ℝ :=
    (p : ℝ) * C_0 + ((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min
  have hB_nonneg : 0 ≤ B_const := by unfold B_const; positivity
  obtain ⟨L_min, hL_min⟩ := exists_nat_gt (B_const / (gap / 2) + 1)
  obtain ⟨L, C, lam_L, hL_ge, hlam_L_ge, hcard, hC_bound, hdisc⟩ :=
    hscale (max L_min 1) ε hε_pos
  have hL1 : 1 ≤ L := le_trans (le_max_right L_min 1) hL_ge
  have hL_ge_min : L_min ≤ L := le_trans (le_max_left L_min 1) hL_ge
  have hlam_L_pos : 0 < lam_L := lt_of_lt_of_le hlam_min hlam_L_ge
  have hbal : ∀ n ≤ C + L,
      |(blockSteps s n : ℝ) - lam_L * (n : ℝ)| ≤ maxPrefixDiscrepancy s lam_L (C + L) :=
    fun n hn => abs_blockSteps_sub_le_maxPrefixDiscrepancy s lam_L hn
  have hcut :=
    balanced_discrepancy_and_factor_complexity_exclusion
      (K := C + L) (W := a_0) (D := maxPrefixDiscrepancy s lam_L (C + L))
      hq hpq hL1 le_rfl ha0 (hchain (C + L)) (hminSlack C)
      hlam_L_pos hbal hcard hC_bound
  change lam_L * gap * (L : ℝ) + 1 ≤
    A * maxPrefixDiscrepancy s lam_L (C + L) + (p : ℝ) * lam_L * C_0 +
      (q : ℝ) * (a_0 : ℝ) + (p : ℝ) at hcut
  have hA_disc :
      A * maxPrefixDiscrepancy s lam_L (C + L) ≤ lam_L * (gap / 2) * (L : ℝ) := by
    have h1 : A * maxPrefixDiscrepancy s lam_L (C + L) ≤ A * (ε * lam_L * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hdisc (le_of_lt hA_pos)
    have h2 : A * (ε * lam_L * (L : ℝ)) = lam_L * (gap / 2) * (L : ℝ) := by
      unfold ε
      have hA_ne : A ≠ 0 := ne_of_gt hA_pos
      field_simp [hA_ne]
      ring
    exact le_of_le_of_eq h1 h2
  have hseed_le :
      (q : ℝ) * (a_0 : ℝ) + (p : ℝ) ≤
        lam_L * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min) := by
    have hnum_nonneg : 0 ≤ (q : ℝ) * (a_0 : ℝ) + (p : ℝ) := by positivity
    have h1 :
        lam_min * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min) =
          (q : ℝ) * (a_0 : ℝ) + (p : ℝ) :=
      mul_div_cancel₀ _ (ne_of_gt hlam_min)
    have h2 :
        lam_min * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min) ≤
          lam_L * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min) :=
      mul_le_mul_of_nonneg_right hlam_L_ge (div_nonneg hnum_nonneg (le_of_lt hlam_min))
    linarith
  have h1_bound :
      lam_L * gap * (L : ℝ) + 1 ≤
        lam_L * (gap / 2) * (L : ℝ) + (p : ℝ) * lam_L * C_0 +
          lam_L * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min) :=
    calc
      lam_L * gap * (L : ℝ) + 1 ≤
          A * maxPrefixDiscrepancy s lam_L (C + L) + (p : ℝ) * lam_L * C_0 +
            (q : ℝ) * (a_0 : ℝ) + (p : ℝ) := hcut
      _ = (A * maxPrefixDiscrepancy s lam_L (C + L) + (p : ℝ) * lam_L * C_0) +
            ((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) := by ring
      _ ≤ (lam_L * (gap / 2) * (L : ℝ) + (p : ℝ) * lam_L * C_0) +
            lam_L * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min) :=
        add_le_add (add_le_add_right hA_disc _) hseed_le
  have hhalf_le :
      lam_L * (gap / 2) * (L : ℝ) + 1 ≤ lam_L * B_const := by
    have hlin :
        lam_L * B_const - (lam_L * (gap / 2) * (L : ℝ) + 1) =
          (lam_L * (gap / 2) * (L : ℝ) + (p : ℝ) * lam_L * C_0 +
            lam_L * (((q : ℝ) * (a_0 : ℝ) + (p : ℝ)) / lam_min)) -
            (lam_L * gap * (L : ℝ) + 1) := by
      unfold B_const
      ring
    linarith [h1_bound, hlin]
  have hL_real_ge : (L_min : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_min
  have hB_lt : B_const < (gap / 2) * (L : ℝ) := by
    have h1 : B_const / (gap / 2) < (L : ℝ) := by linarith
    have h2 : B_const < (L : ℝ) * (gap / 2) := (div_lt_iff₀ (by linarith)).mp h1
    linarith
  have hmul_lt : lam_L * B_const < lam_L * ((gap / 2) * (L : ℝ)) :=
    mul_lt_mul_of_pos_left hB_lt hlam_L_pos
  have hcomm : lam_L * ((gap / 2) * (L : ℝ)) = lam_L * (gap / 2) * (L : ℝ) := by ring
  linarith

/-- Rapidly growing epoch boundaries `epochBound 0 = 0`,
`epochBound (k + 1) = (k + 4) * (epochBound k + 1)`. -/
def epochBound : ℕ → ℕ
  | 0 => 0
  | k + 1 => (k + 4) * (epochBound k + 1)

theorem epochBound_lt_succ (k : ℕ) : epochBound k < epochBound (k + 1) := by
  simp only [epochBound]
  nlinarith

theorem epochBound_strictMono : StrictMono epochBound :=
  strictMono_nat_of_lt_succ epochBound_lt_succ

theorem id_lt_epochBound_succ (n : ℕ) : n < epochBound (n + 1) := by
  induction n with
  | zero => simp [epochBound]
  | succ n ih =>
      have hlt := epochBound_lt_succ (n + 1)
      omega

/-- Epoch index `epochIndex n`: the unique `k` such that `epochBound k ≤ n < epochBound (k + 1)`. -/
noncomputable def epochIndex (n : ℕ) : ℕ :=
  Nat.find (⟨n, id_lt_epochBound_succ n⟩ : ∃ k : ℕ, n < epochBound (k + 1))

theorem epochIndex_eq_of_mem {k n : ℕ}
    (hlo : epochBound k ≤ n) (hhi : n < epochBound (k + 1)) :
    epochIndex n = k := by
  unfold epochIndex
  have hex : ∃ j : ℕ, n < epochBound (j + 1) := ⟨n, id_lt_epochBound_succ n⟩
  apply le_antisymm
  · exact Nat.find_min' hex hhi
  · by_contra hlt
    have hle : Nat.find hex + 1 ≤ k := by omega
    have hmono := epochBound_strictMono.monotone hle
    have hspec := Nat.find_spec hex
    omega

/-- **Concrete Non-Stationary Oscillating-Epoch Block Sequence (`nonStationaryEpochSeq`)**:
Alternates between `a` on even epochs `[epochBound (2*m), epochBound (2*m + 1))` and
`b` on odd epochs `[epochBound (2*m + 1), epochBound (2*m + 2))`. -/
noncomputable def nonStationaryEpochSeq (a b n : ℕ) : ℕ :=
  if epochIndex n % 2 = 0 then a else b

theorem nonStationaryEpochSeq_eq_on_epoch (a b k : ℕ) {n : ℕ}
    (hlo : epochBound k ≤ n) (hhi : n < epochBound (k + 1)) :
    nonStationaryEpochSeq a b n = if k % 2 = 0 then a else b := by
  unfold nonStationaryEpochSeq
  rw [epochIndex_eq_of_mem hlo hhi]

theorem nonStationaryEpochSeq_bounds {a b : ℕ} (hab : a ≤ b) (n : ℕ) :
    a ≤ nonStationaryEpochSeq a b n ∧ nonStationaryEpochSeq a b n ≤ b := by
  unfold nonStationaryEpochSeq
  split_ifs <;> refine ⟨by omega, by omega⟩

/-- On any interval `[H, n]` where `s j = c` for all `H ≤ j < n`,
`blockSteps s n = blockSteps s H + c * (n - H)`. -/
theorem blockSteps_eq_add_const_on_interval {s : ℕ → ℕ} {H c n : ℕ}
    (hHn : H ≤ n) (hconst : ∀ j, H ≤ j → j < n → s j = c) :
    blockSteps s n = blockSteps s H + c * (n - H) := by
  induction n with
  | zero =>
      have hH0 : H = 0 := by omega
      subst hH0
      simp [blockSteps]
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hHn with rfl | hlt
      · simp [blockSteps]
      · have ihn := ih (by omega) (fun j hj1 hj2 => hconst j hj1 (by omega))
        have hsn : s n = c := hconst n (by omega) (by omega)
        simp only [blockSteps]
        rw [ihn, hsn]
        have hsub : n + 1 - H = (n - H) + 1 := by omega
        rw [hsub]
        ring

/-- Global step bounds `a * n ≤ blockSteps (nonStationaryEpochSeq a b) n ≤ b * n`. -/
theorem blockSteps_nonStationaryEpochSeq_bounds {a b : ℕ} (hab : a ≤ b) (n : ℕ) :
    a * n ≤ blockSteps (nonStationaryEpochSeq a b) n ∧
      blockSteps (nonStationaryEpochSeq a b) n ≤ b * n := by
  induction n with
  | zero => simp [blockSteps]
  | succ n ih =>
      simp only [blockSteps]
      have hb := nonStationaryEpochSeq_bounds hab n
      refine ⟨by nlinarith, by nlinarith⟩

/-- **Non-Existence of a Global Limiting Mean for `nonStationaryEpochSeq`
(`nonStationaryEpochSeq_no_limiting_mean`)**:
Whenever `a < b`, the Cesàro average `blockSteps (nonStationaryEpochSeq a b) n / n`
oscillates between values `≤ a + (b - a) / 4` at the end of even epochs and values
`≥ b - (b - a) / 4` at the end of odd epochs, and therefore has **no** real limit as `n → ∞`. -/
theorem nonStationaryEpochSeq_no_limiting_mean {a b : ℕ} (hab_lt : a < b) :
    ¬ (∃ lam : ℝ,
      Filter.Tendsto
        (fun n : ℕ => (blockSteps (nonStationaryEpochSeq a b) n : ℝ) / (n : ℝ))
        Filter.atTop (nhds lam)) := by
  rintro ⟨lam, htend⟩
  have hab : a ≤ b := le_of_lt hab_lt
  have hab_real : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab_lt
  have hba_pos : (0 : ℝ) < (b : ℝ) - (a : ℝ) := sub_pos.mpr hab_real
  set ε : ℝ := ((b : ℝ) - (a : ℝ)) / 8
  have hε_pos : 0 < ε := by unfold ε; linarith
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N_0, hN_0⟩ := htend ε hε_pos
  set m : ℕ := N_0 + 1
  set n_even : ℕ := epochBound (2 * m + 1)
  set n_odd : ℕ := epochBound (2 * m + 2)
  have hn_even_ge : N_0 ≤ n_even := by
    have h1 : 2 * m < n_even := id_lt_epochBound_succ (2 * m)
    omega
  have hn_odd_ge : N_0 ≤ n_odd := by
    have h1 : 2 * m + 1 < n_odd := id_lt_epochBound_succ (2 * m + 1)
    omega
  have heven_eq :
      blockSteps (nonStationaryEpochSeq a b) n_even =
        blockSteps (nonStationaryEpochSeq a b) (epochBound (2 * m)) +
          a * (n_even - epochBound (2 * m)) := by
    apply blockSteps_eq_add_const_on_interval
      (le_of_lt (epochBound_lt_succ (2 * m)))
    intro j hj1 hj2
    have h := nonStationaryEpochSeq_eq_on_epoch a b (2 * m) hj1 hj2
    have hmod : (2 * m) % 2 = 0 := by omega
    simp [hmod] at h
    exact h
  have hodd_eq :
      blockSteps (nonStationaryEpochSeq a b) n_odd =
        blockSteps (nonStationaryEpochSeq a b) n_even +
          b * (n_odd - n_even) := by
    apply blockSteps_eq_add_const_on_interval
      (le_of_lt (epochBound_lt_succ (2 * m + 1)))
    intro j hj1 hj2
    have h := nonStationaryEpochSeq_eq_on_epoch a b (2 * m + 1) hj1 hj2
    have hmod : (2 * m + 1) % 2 = 1 := by omega
    simp [hmod] at h
    exact h
  have heven_hi :
      4 * blockSteps (nonStationaryEpochSeq a b) n_even ≤ (3 * a + b) * n_even := by
    have hb_prev := (blockSteps_nonStationaryEpochSeq_bounds hab (epochBound (2 * m))).2
    have hdef : n_even = (2 * m + 4) * (epochBound (2 * m) + 1) := rfl
    set H0 := epochBound (2 * m)
    have hle_n : 4 * H0 ≤ n_even := by
      rw [hdef]
      nlinarith
    have hsub : H0 + (n_even - H0) = n_even := Nat.add_sub_of_le (by omega)
    have hmul_sub : a * H0 + a * (n_even - H0) = a * n_even := by
      rw [← Nat.mul_add, hsub]
    have hba : (b - a) * H0 + a * H0 = b * H0 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hab]
    have hstep1 :
        blockSteps (nonStationaryEpochSeq a b) n_even ≤ a * n_even + (b - a) * H0 := by
      omega
    have hstep2 : 4 * ((b - a) * H0) ≤ (b - a) * n_even := by
      calc
        4 * ((b - a) * H0) = (b - a) * (4 * H0) := by ring
        _ ≤ (b - a) * n_even := Nat.mul_le_mul_left (b - a) hle_n
    have hstep3 : 4 * (a * n_even) + (b - a) * n_even = (3 * a + b) * n_even := by
      have h : 4 * a + (b - a) = 3 * a + b := by omega
      calc
        4 * (a * n_even) + (b - a) * n_even = (4 * a + (b - a)) * n_even := by ring
        _ = (3 * a + b) * n_even := by rw [h]
    omega
  have hodd_lo :
      (a + 3 * b) * n_odd ≤ 4 * blockSteps (nonStationaryEpochSeq a b) n_odd := by
    have ha_prev := (blockSteps_nonStationaryEpochSeq_bounds hab n_even).1
    have hdef : n_odd = (2 * m + 5) * (n_even + 1) := rfl
    have hle_n : 4 * n_even ≤ n_odd := by
      rw [hdef]
      nlinarith
    have hsub : n_even + (n_odd - n_even) = n_odd := Nat.add_sub_of_le (by omega)
    have hmul_b : b * n_even + b * (n_odd - n_even) = b * n_odd := by
      rw [← Nat.mul_add, hsub]
    have hba : (b - a) * n_even + a * n_even = b * n_even := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hab]
    have hstep1 :
        a * n_even + b * (n_odd - n_even) ≤
          blockSteps (nonStationaryEpochSeq a b) n_odd := by
      omega
    have hstep2 : 4 * ((b - a) * n_even) ≤ (b - a) * n_odd := by
      calc
        4 * ((b - a) * n_even) = (b - a) * (4 * n_even) := by ring
        _ ≤ (b - a) * n_odd := Nat.mul_le_mul_left (b - a) hle_n
    have hstep3 : (a + 3 * b) * n_odd + (b - a) * n_odd = 4 * (b * n_odd) := by
      have h : (a + 3 * b) + (b - a) = 4 * b := by omega
      calc
        (a + 3 * b) * n_odd + (b - a) * n_odd = ((a + 3 * b) + (b - a)) * n_odd := by ring
        _ = (4 * b) * n_odd := by rw [h]
        _ = 4 * (b * n_odd) := by ring
    omega
  have hn_even_pos : (0 : ℝ) < (n_even : ℝ) := by
    have h : 0 < n_even := lt_of_le_of_lt (Nat.zero_le _) (epochBound_lt_succ (2 * m))
    exact_mod_cast h
  have hn_odd_pos : (0 : ℝ) < (n_odd : ℝ) := by
    have h : 0 < n_odd := lt_of_le_of_lt (Nat.zero_le _) (epochBound_lt_succ (2 * m + 1))
    exact_mod_cast h
  have hdist_even := hN_0 n_even hn_even_ge
  have hdist_odd := hN_0 n_odd hn_odd_ge
  rw [Real.dist_eq, abs_lt] at hdist_even hdist_odd
  have heven_real :
      4 * (blockSteps (nonStationaryEpochSeq a b) n_even : ℝ) ≤
        (3 * (a : ℝ) + (b : ℝ)) * (n_even : ℝ) := by
    exact_mod_cast heven_hi
  have hodd_real :
      ((a : ℝ) + 3 * (b : ℝ)) * (n_odd : ℝ) ≤
        4 * (blockSteps (nonStationaryEpochSeq a b) n_odd : ℝ) := by
    exact_mod_cast hodd_lo
  have hdiv_even :
      (blockSteps (nonStationaryEpochSeq a b) n_even : ℝ) / (n_even : ℝ) ≤
        (3 * (a : ℝ) + (b : ℝ)) / 4 := by
    rw [div_le_iff₀ hn_even_pos]
    linarith
  have hdiv_odd :
      ((a : ℝ) + 3 * (b : ℝ)) / 4 ≤
        (blockSteps (nonStationaryEpochSeq a b) n_odd : ℝ) / (n_odd : ℝ) := by
    rw [le_div_iff₀ hn_odd_pos]
    linarith
  unfold ε at hdist_even hdist_odd
  linarith

/-- **Unconditional Scale-Local Exclusion of `nonStationaryEpochSeq` (`no_infinite_nonStationaryEpochSeq_block_chain`)**:
Although `nonStationaryEpochSeq a b` (`3 ≤ a < b`) has **no** global limiting mean
`blockSteps s n / n`, it satisfies the scale-local balance theorem at every even epoch
`L_m = (2 * m + 3) * (epochBound (2 * m) + 1)` with local slope `lam = a` and is
unconditionally excluded from supporting any infinite valid integer block chain. -/
theorem no_infinite_nonStationaryEpochSeq_block_chain
    {a b a_0 : ℕ} (ha3 : 3 ≤ a) (hab_lt : a < b) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 (nonStationaryEpochSeq a b) u K) := by
  rintro ⟨u, hchain⟩
  have hab : a ≤ b := le_of_lt hab_lt
  have hminSlack : ∀ m : ℕ, 0 < minSlack (nonStationaryEpochSeq a b) m := by
    intro m
    have h3 : ∀ k < m, 3 ≤ nonStationaryEpochSeq a b k := by
      intro k _
      have hb := (nonStationaryEpochSeq_bounds hab k).1
      omega
    exact (all_shifted_slacks_pos_of_three_le (nonStationaryEpochSeq a b) m h3).1
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hlog1 : (1 : ℝ) * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ) := by
    rw [one_mul]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  apply no_infinite_scale_local_balanced_block_chain
    (a_0 := a_0) (s := nonStationaryEpochSeq a b) (u := u)
    (lam_min := (a : ℝ)) (kappa := 1) (C_0 := 0)
    ha_pos (by norm_num) (by norm_num) hlog1 _ ⟨hchain, hminSlack⟩
  intro L_min ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (((b - a : ℕ) : ℝ) / (ε * (a : ℝ)) + (L_min : ℝ))
  set m : ℕ := M + L_min + 1
  set H : ℕ := epochBound (2 * m)
  set C : ℕ := H + 1
  set L : ℕ := (2 * m + 3) * (H + 1)
  have hCL_eq : H + 1 + L = epochBound (2 * m + 1) := by
    change (H + 1) + (2 * m + 3) * (H + 1) = (2 * m + 4) * (H + 1)
    ring
  have hL_ge : L_min ≤ L := by
    change L_min ≤ (2 * (M + L_min + 1) + 3) * (H + 1)
    nlinarith
  have hcard : prefixFactorCount (nonStationaryEpochSeq a b) L C ≤ C := by
    apply prefixFactorCount_le_of_repeated_subword (nonStationaryEpochSeq a b)
      (r1 := H) (r2 := H + 1) (by omega) le_rfl
    intro i hi
    have hi1 : H + i < epochBound (2 * m + 1) := by omega
    have hi2 : H + 1 + i < epochBound (2 * m + 1) := by omega
    have h1 : nonStationaryEpochSeq a b (H + i) = a := by
      have h := nonStationaryEpochSeq_eq_on_epoch a b (2 * m) (n := H + i) (by omega) hi1
      have hmod : (2 * m) % 2 = 0 := by omega
      simpa [hmod] using h
    have h2 : nonStationaryEpochSeq a b (H + 1 + i) = a := by
      have h := nonStationaryEpochSeq_eq_on_epoch a b (2 * m) (n := H + 1 + i) (by omega) hi2
      have hmod : (2 * m) % 2 = 0 := by omega
      simpa [hmod] using h
    rw [h1, h2]
  have hC_bound : (C : ℝ) ≤ 1 * (L : ℝ) + 0 := by
    have hle_nat : C ≤ L := by
      dsimp [C, L]
      nlinarith
    have hle_real : (C : ℝ) ≤ (L : ℝ) := by exact_mod_cast hle_nat
    linarith
  have hdisc :
      maxPrefixDiscrepancy (nonStationaryEpochSeq a b) (a : ℝ) (C + L) ≤
        ε * (a : ℝ) * (L : ℝ) := by
    apply maxPrefixDiscrepancy_le_of_forall_le
    intro n hn
    have hn_bounds :
        a * n ≤ blockSteps (nonStationaryEpochSeq a b) n ∧
          blockSteps (nonStationaryEpochSeq a b) n ≤ a * n + (b - a) * H := by
      refine ⟨(blockSteps_nonStationaryEpochSeq_bounds hab n).1, ?_⟩
      by_cases hnH : n ≤ H
      · have hb_n := (blockSteps_nonStationaryEpochSeq_bounds hab n).2
        have hdiff : b * n = a * n + (b - a) * n := by
          zify [hab]
          ring
        have hmul : (b - a) * n ≤ (b - a) * H := Nat.mul_le_mul_left (b - a) hnH
        omega
      · push_neg at hnH
        have hn_lt : n ≤ epochBound (2 * m + 1) := by
          have h1 : n ≤ H + 1 + L := hn
          omega
        have heq := blockSteps_eq_add_const_on_interval (c := a) (le_of_lt hnH)
          (fun j hj1 hj2 => by
            have hj_lt : j < epochBound (2 * m + 1) := lt_of_lt_of_le hj2 hn_lt
            have h := nonStationaryEpochSeq_eq_on_epoch a b (2 * m) hj1 hj_lt
            have hmod : (2 * m) % 2 = 0 := by omega
            simpa [hmod] using h)
        have hb_H := (blockSteps_nonStationaryEpochSeq_bounds hab H).2
        have hdiff : b * H = a * H + (b - a) * H := by
          zify [hab]
          ring
        have hadd : a * H + a * (n - H) = a * n := by
          zify [le_of_lt hnH]
          ring
        omega
    have hlo_real : (a : ℝ) * (n : ℝ) ≤ (blockSteps (nonStationaryEpochSeq a b) n : ℝ) := by
      exact_mod_cast hn_bounds.1
    have hhi_real :
        (blockSteps (nonStationaryEpochSeq a b) n : ℝ) ≤
          (a : ℝ) * (n : ℝ) + ((b - a : ℕ) : ℝ) * (H : ℝ) := by
      exact_mod_cast hn_bounds.2
    have habs :
        |(blockSteps (nonStationaryEpochSeq a b) n : ℝ) - (a : ℝ) * (n : ℝ)| ≤
          ((b - a : ℕ) : ℝ) * (H : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hM_lt : ((b - a : ℕ) : ℝ) / (ε * (a : ℝ)) < (2 * m + 3 : ℝ) := by
      have hm_ge : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : M ≤ m)
      have hLmin_nonneg : (0 : ℝ) ≤ (L_min : ℝ) := Nat.cast_nonneg L_min
      linarith
    have hmul_eps : ((b - a : ℕ) : ℝ) < (2 * m + 3 : ℝ) * (ε * (a : ℝ)) :=
      (div_lt_iff₀ (mul_pos hε ha_pos)).mp hM_lt
    have hH_le : (H : ℝ) ≤ (H + 1 : ℝ) := by linarith
    have hL_cast : (L : ℝ) = (2 * m + 3 : ℝ) * ((H : ℝ) + 1) := by
      dsimp [L]
      push_cast
      ring
    have hba_nonneg : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg (b - a)
    have hH1_pos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    have hstep1 : ((b - a : ℕ) : ℝ) * (H : ℝ) ≤ ((b - a : ℕ) : ℝ) * ((H : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hH_le hba_nonneg
    have hstep2 :
        ((b - a : ℕ) : ℝ) * ((H : ℝ) + 1) ≤
          ((2 * m + 3 : ℝ) * (ε * (a : ℝ))) * ((H : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (le_of_lt hmul_eps) (le_of_lt hH1_pos)
    have hstep3 :
        ((2 * m + 3 : ℝ) * (ε * (a : ℝ))) * ((H : ℝ) + 1) = ε * (a : ℝ) * (L : ℝ) := by
      rw [hL_cast]
      ring
    exact le_trans habs (le_trans hstep1 (le_of_le_of_eq hstep2 hstep3))
  exact ⟨L, C, (a : ℝ), hL_ge, le_rfl, hcard, hC_bound, hdisc⟩

/-- **Uniform Recurrence Definition (`IsUniformlyRecurrent`)**:
Every factor `factorWindow s L r0` reappears syndetically with bounded gaps `R ≥ 1`. -/
def IsUniformlyRecurrent (s : ℕ → ℕ) : Prop :=
  ∀ L r0 : ℕ, ∃ R ≥ 1, ∀ m : ℕ, ∃ r : ℕ,
    m ≤ r ∧ r ≤ m + R ∧ factorWindow s L r = factorWindow s L r0

/-- **Uniform Factor-Window Step Balance (`HasUniformWindowMean s lam`)**:
The combinatorial unique-ergodicity property for step sums: for every `ε > 0`, there
exists a window length `M ≥ 1` such that every shifted window of length `M` has step sum
within `ε * M` of `lam * M`. -/
def HasUniformWindowMean (s : ℕ → ℕ) (lam : ℝ) : Prop :=
  ∀ ε > 0, ∃ M ≥ 1, ∀ m : ℕ,
    |(blockSteps (shiftSeq s m) M : ℝ) - lam * (M : ℝ)| ≤ ε * (M : ℝ)

private theorem blockSteps_add_shiftSeq (s : ℕ → ℕ) (a b : ℕ) :
    blockSteps s (a + b) = blockSteps s a + blockSteps (shiftSeq s a) b := by
  induction b with
  | zero => simp [blockSteps]
  | succ b ih =>
      have hidx : a + (b + 1) = (a + b) + 1 := by omega
      rw [hidx]
      simp only [blockSteps, shiftSeq, ih]
      omega

/-- Decomposition of `blockSteps s (q * M)` by tiling into `q` windows of length `M`. -/
theorem blockSteps_mul_And_mod_tiling (s : ℕ → ℕ) (M q : ℕ) :
    (blockSteps s (q * M) : ℝ) =
      ∑ j ∈ Finset.range q, (blockSteps (shiftSeq s (j * M)) M : ℝ) := by
  induction q with
  | zero => simp [blockSteps]
  | succ q ih =>
      rw [Finset.sum_range_succ]
      have hadd : (q + 1) * M = q * M + M := by ring
      have hsplit :
          blockSteps s (q * M + M) =
            blockSteps s (q * M) + blockSteps (shiftSeq s (q * M)) M :=
        blockSteps_add_shiftSeq s (q * M) M
      rw [hadd]
      push_cast [hsplit]
      linarith

/-- **Combinatorial Window-Tiling Mean Bridge (`tendsto_mean_of_uniformWindowMean`)**:
If `s` is bounded (`∀ n, s n ≤ B`) and satisfies `HasUniformWindowMean s lam`, then
the global Cesàro mean converges to `lam`:
`Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ)) Filter.atTop (nhds lam)`. -/
theorem tendsto_mean_of_uniformWindowMean
    {s : ℕ → ℕ} {B : ℕ} {lam : ℝ}
    (hb : ∀ n : ℕ, s n ≤ B)
    (hunif : HasUniformWindowMean s lam) :
    Filter.Tendsto (fun n : ℕ => (blockSteps s n : ℝ) / (n : ℝ))
      Filter.atTop (nhds lam) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨M, hM1, hM_win⟩ := hunif (ε / 3) hε3
  set R_rem : ℝ := ((B : ℝ) + |lam|) * (M : ℝ)
  have hR_nonneg : 0 ≤ R_rem := by unfold R_rem; positivity
  obtain ⟨N_0, hN_0⟩ := exists_nat_gt (R_rem / (ε / 3) + 1)
  refine ⟨max N_0 1, ?_⟩
  intro n hn
  have hn0 : N_0 ≤ n := le_trans (le_max_left N_0 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N_0 1) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  set q : ℕ := n / M
  set r : ℕ := n % M
  have hdiv_mod : q * M + r = n := by
    have h1 := Nat.div_add_mod n M
    have h2 : M * q = q * M := Nat.mul_comm M q
    change M * q + r = n at h1
    linarith
  have hr_lt : r < M := Nat.mod_lt n hM1
  have hsplit_n :
      blockSteps s n = blockSteps s (q * M) + blockSteps (shiftSeq s (q * M)) r := by
    conv_lhs => rw [← hdiv_mod]
    exact blockSteps_add_shiftSeq s (q * M) r
  have hqM_diff :
      |(blockSteps s (q * M) : ℝ) - lam * ((q * M : ℕ) : ℝ)| ≤
        (ε / 3) * ((q * M : ℕ) : ℝ) := by
    rw [blockSteps_mul_And_mod_tiling s M q]
    have hlam_sum :
        lam * ((q * M : ℕ) : ℝ) = ∑ _j ∈ Finset.range q, lam * (M : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have heps_sum :
        (ε / 3) * ((q * M : ℕ) : ℝ) = ∑ _j ∈ Finset.range q, (ε / 3) * (M : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hlam_sum, heps_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun j _ => hM_win (j * M))
  have hr_bound_all : ∀ k : ℕ, blockSteps (shiftSeq s (q * M)) k ≤ B * k := by
    intro k
    induction k with
    | zero => simp [blockSteps]
    | succ k ih =>
        simp only [blockSteps]
        have hsk : shiftSeq s (q * M) k ≤ B := hb (q * M + k)
        nlinarith
  have hr_bound : blockSteps (shiftSeq s (q * M)) r ≤ B * r := hr_bound_all r
  have hr_real : (blockSteps (shiftSeq s (q * M)) r : ℝ) ≤ (B : ℝ) * (M : ℝ) := by
    have h1 : (blockSteps (shiftSeq s (q * M)) r : ℝ) ≤ (B : ℝ) * (r : ℝ) := by
      exact_mod_cast hr_bound
    have h2 : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_of_lt hr_lt)
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg B))
  have hlam_r : |lam * (r : ℝ)| ≤ |lam| * (M : ℝ) := by
    rw [abs_mul]
    have hr_abs : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg (Nat.cast_nonneg r)
    rw [hr_abs]
    have h2 : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_of_lt hr_lt)
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg lam)
  have htot_diff :
      |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ (ε / 3) * (n : ℝ) + R_rem := by
    have hdecomp :
        (blockSteps s n : ℝ) - lam * (n : ℝ) =
          ((blockSteps s (q * M) : ℝ) - lam * ((q * M : ℕ) : ℝ)) +
            (blockSteps (shiftSeq s (q * M)) r : ℝ) - lam * (r : ℝ) := by
      have hn_eq : (n : ℝ) = ((q * M : ℕ) : ℝ) + (r : ℝ) := by
        exact_mod_cast hdiv_mod.symm
      have hsp_real :
          (blockSteps s n : ℝ) =
            (blockSteps s (q * M) : ℝ) + (blockSteps (shiftSeq s (q * M)) r : ℝ) := by
        exact_mod_cast hsplit_n
      rw [hsp_real, hn_eq]
      ring
    have hqM_le_n : ((q * M : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h : q * M ≤ n := by omega
      exact_mod_cast h
    have hrem_nonneg : (0 : ℝ) ≤ (blockSteps (shiftSeq s (q * M)) r : ℝ) :=
      Nat.cast_nonneg (blockSteps (shiftSeq s (q * M)) r)
    rcases abs_le.mp hqM_diff with ⟨hlo1, hhi1⟩
    rcases abs_le.mp hlam_r with ⟨hlo2, hhi2⟩
    rw [hdecomp, abs_le]
    unfold R_rem
    have heps_le : (ε / 3) * ((q * M : ℕ) : ℝ) ≤ (ε / 3) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hqM_le_n (le_of_lt hε3)
    exact ⟨by linarith, by linarith⟩
  have hR_lt : R_rem < (ε / 3) * (n : ℝ) := by
    have hn_ge : (N_0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    have h1 : R_rem / (ε / 3) < (n : ℝ) := by linarith
    have h2 : R_rem < (n : ℝ) * (ε / 3) := (div_lt_iff₀ hε3).mp h1
    linarith
  rw [Real.dist_eq]
  have hdiv_eq :
      (blockSteps s n : ℝ) / (n : ℝ) - lam =
        ((blockSteps s n : ℝ) - lam * (n : ℝ)) / (n : ℝ) := by
    field_simp [ne_of_gt hn_pos]
    ring
  rw [hdiv_eq, abs_div, abs_of_pos hn_pos, div_lt_iff₀ hn_pos]
  linarith

/-- For any bounded sequence `∀ n, s n ≤ B`, the global factor set `globalFactorSet s L`
is finite at every factor length `L : ℕ`. -/
theorem globalFactorSet_finite_of_bounded {s : ℕ → ℕ} {B : ℕ}
    (hb : ∀ n : ℕ, s n ≤ B) (L : ℕ) :
    (globalFactorSet s L).Finite := by
  refine Set.Finite.subset
    (s := Set.univ.pi (fun _ : Fin L => Set.Iic B))
    (Set.Finite.pi (fun _ => Set.finite_Iic B)) ?_
  rintro w ⟨r, rfl⟩ i _
  exact hb (r + i.val)

/-- **Uniquely-Ergodic / Uniform-Window-Mean & Global Sub-Critical Complexity Exclusion
(`no_infinite_uniformWindowMean_global_complexity_block_chain`)**:
For any bounded sequence `∀ n, s n ≤ B` satisfying `HasUniformWindowMean s lam` (`0 < lam`)
and `globalFactorComplexity s L ≤ kappa * L + C_0` at arbitrarily large lengths `L`
with `kappa * Real.log (3 / 2) < Real.log 2`, no infinite surviving integer block chain exists. -/
theorem no_infinite_uniformWindowMean_global_complexity_block_chain
    {a_0 B : ℕ} {s u : ℕ → ℕ} {lam kappa C_0 : ℝ}
    (hb : ∀ n : ℕ, s n ≤ B)
    (hlam : 0 < lam) (hkap : 0 ≤ kappa) (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ))
    (hunif : HasUniformWindowMean s lam)
    (hliminf : ∀ L_min : ℕ, ∃ L ≥ L_min,
      (globalFactorComplexity s L : ℝ) ≤ kappa * (L : ℝ) + C_0) :
    ¬ ((∀ K : ℕ, ValidBlockChain a_0 s u K) ∧ (∀ m : ℕ, 0 < minSlack s m)) :=
  no_infinite_global_complexity_log_threshold_block_chain
    hlam hkap hC0 hlog
    (tendsto_mean_of_uniformWindowMean hb hunif)
    (globalFactorSet_finite_of_bounded hb)
    hliminf

end Mahler.EndpointAndBalancedExclusion
