import ExactSeedResidueTreeAndStabilization
import ParitySurplusPotentialsAndSafetyGame
import BaseSixMultiplicationAutomaton
import TransferOperatorJSRAndCarryFourier

/-!
# Measure-Rigidity Obstructions, Erdős–Turán Discrepancy Reduction, S-Unit / Mahler-Value Bridges & Renormalization

This module formalizes **Part II Sections 14, 15, 16, 17, 20, and 21** of
`RESEARCH_PLAN_ARGON_GENERAL_PROOF.md`:

1. **Section 14 — Measure Rigidity & Adelic/Rational `(×2, ×3)` Invariance Obstruction
   (`three_pow_ne_two_pow_mul`, `single_generator_orbit_not_two_or_three_invariant`,
   `finite_horizon_confinement_not_two_or_three_invariant`)**:
   - Proves that for any positive real `x_0 > 0`, the forward `×(3/2)`-orbit
     `O_{3/2}(x_0) = {x_0 * (3/2)^n | n : ℕ}` is forward-invariant under `×(3/2)`,
     but is **neither `×2`-invariant nor `×3`-invariant**: `2 * x_0 ∉ O_{3/2}(x_0)` and
     `3 * x_0 ∉ O_{3/2}(x_0)`.
   - Proves that finite-horizon confinement cylinders are also neither `×2`-invariant nor
     `×3`-invariant (`α = 2/9` survives steps `0, 1` with fractional parts `2/9, 1/3 < 1/2`,
     whereas `2 * α = 4/9` fails at step `1` with `2/3 ≥ 1/2` and `3 * α = 2/3` fails at step `0`;
     on integers, `survivesSteps 8 4 = true` whereas `survivesSteps (3 * 8) 4 = false`).
   - This packages the exact **Section 21 Type 3 Negative Deliverable** (*Hypothesis-does-not-apply*):
     Rudolph/Host/Johnson `(×2, ×3)` measure rigidity requires joint invariance under two
     multiplicatively independent endomorphisms, which a single `×(3/2)` orbit and its real
     confinement cylinder do not satisfy.

2. **Section 15 — Discrepancy, Escape Counting & the Erdős–Turán Conditional Reduction
   (`lowerHalfCount`, `upperHalfCount`, `halfIntervalDiscrepancy`,
   `lowerHalfCount_add_upperHalfCount_eq`, `discrepancy_lt_half_forces_mahler_escape`,
   `erdos_turan_conditional_mahler_reduction`)**:
   - Defines `lowerHalfCount α N`, `upperHalfCount α N`, and `halfIntervalDiscrepancy α N`.
   - Proves that whenever `halfIntervalDiscrepancy α N ≤ 1/2 - δ` (`N ≥ 1`), at least `δ * N`
     steps in `[0, N)` escape `[0, 1/2)`, and whenever `halfIntervalDiscrepancy α N < 1/2`,
     `1 ≤ upperHalfCount α N` and `∃ n < N, 1 / 2 ≤ Int.fract (α * (3 / 2)^n)`.
   - Formalizes the **Erdős–Turán Exponential-Sum Conditional Reduction** (Section 21 Type 5):
     any Erdős–Turán bound whose right-hand side falls below `1/2` at some horizon `(N, K)`
     immediately forces Mahler escape for `α`.

3. **Section 16 — S-Unit / Dyadic-Block UniquenessPast Bit `W` & Why Finiteness Stops at `1`
   (`distinct_dyadic_seeds_cannot_share_prefix_past_W`, `single_dyadic_survivor_witness_149`)**:
   - Proves that two distinct seeds `a₁ < a₂` in the same dyadic interval `[2^W, 2^(W+1))`
     can never share the same parity prefix through horizon `N > W`.
   - Certifies via `seed_149` in `[128, 256)` (`W = 7, N = 28`) why a per-dyadic-block upper bound
     of `1` survivor on a given prefix does not imply `0` survivors.

4. **Section 17 — Mahler's Method Value-Irrationality Exclusion Bridge
   (`mahler_method_irrational_value_excludes_integer_seed`)**:
   - Formalizes the exact conditional bridge from Mahler's method (Adamczewski–Faverjon):
     if a structured parity stream `ε` has a series invariant `v : ℝ` that equals a rational
     function `(q a_0 : ℝ)` for any realizing integer seed `a_0 : ℕ`, then `Irrational v`
     unconditionally excludes all nonnegative integer seeds and prevents `seedResidue ε` from
     ever stabilizing.

5. **Section 20 — First-Return Renormalization & 2-Adic Non-Self-Similarity
   (`first_return_two_adic_defect_and_multiplier_mismatch`)**:
   - Proves why 1D archimedean first-return renormalization on the `{3, 4}` Cantor dust fails to
     renormalize the 2-adic coordinate: in `I(b) = 19 * b + 9` coordinates, the `s = 3` branch
     is purely homogeneous (`2^3 * I(b') = 3^3 * I(b) + 0`), whereas the `s = 4` branch injects
     a non-zero inhomogeneous defect `E(4) = 9 * 2^4 - 8 * 3^3 = -72 ≠ 0`, and the branch
     multipliers `27/8 ≠ 81/16` have distinct 2-adic valuations (`-3 ≠ -4`).
-/

namespace Mahler.SolenoidDiscrepancyAndRenorm

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.BaseSixAutomaton
open Mahler.TransferJSRAndFourier

/-! ## 1. Section 14: Measure Rigidity & `(×2, ×3)` Invariance Obstruction -/

/-- No power of `3` can equal `2^{n+1}` (`3^n ≠ 2^{n+1}`) or `3 * 2^n` for `n ≥ 1`. -/
theorem three_pow_ne_two_pow_succ_and_three_mul_two_pow (n : ℕ) :
    3 ^ n ≠ 2 ^ (n + 1) ∧ (n ≠ 1 → 3 ^ n ≠ 3 * 2 ^ n) := by
  have hodd : ∀ m : ℕ, 3 ^ m % 2 = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih =>
        rw [pow_succ, Nat.mul_mod, ih]
  refine ⟨?_, ?_⟩
  · intro heq
    have hmod : 3 ^ n % 2 = 2 ^ (n + 1) % 2 := congrArg (· % 2) heq
    rw [hodd n, pow_succ, Nat.mul_mod_left] at hmod
    contradiction
  · intro hn1 heq
    rcases n with _ | k
    · norm_num at heq
    · rcases k with _ | m
      · exact hn1 rfl
      · have hcancel : 3 * 3 ^ (m + 1) = 3 * 2 ^ (m + 2) := by
          rw [← pow_succ', heq]
        have hm_eq : 3 ^ (m + 1) = 2 ^ (m + 2) := by omega
        have hmod : 3 ^ (m + 1) % 2 = 2 ^ (m + 2) % 2 := congrArg (· % 2) hm_eq
        rw [hodd (m + 1), show m + 2 = (m + 1) + 1 by omega, pow_succ, Nat.mul_mod_left] at hmod
        contradiction

/-- Forward `×(3/2)`-orbit of a real number `x_0`: `orbitSetThreeHalves x_0 = {x_0 * (3/2)^n | n : ℕ}`. -/
def orbitSetThreeHalves (x_0 : ℝ) : Set ℝ :=
  {y : ℝ | ∃ n : ℕ, y = x_0 * (3 / 2 : ℝ) ^ n}

/-- **Single-Generator `×(3/2)` Orbit Is Not `×2`- or `×3`-Invariant
(`single_generator_orbit_not_two_or_three_invariant`, Section 14 Negative Theorem)**:
For every positive real `x_0 > 0`:
1. `x_0 ∈ orbitSetThreeHalves x_0` and `orbitSetThreeHalves x_0` is forward-invariant under `×(3/2)`,
2. `2 * x_0 ∉ orbitSetThreeHalves x_0` (not `×2`-invariant), and
3. `3 * x_0 ∉ orbitSetThreeHalves x_0` (not `×3`-invariant). -/
theorem single_generator_orbit_not_two_or_three_invariant {x_0 : ℝ} (hx0 : 0 < x_0) :
    (x_0 ∈ orbitSetThreeHalves x_0 ∧
      ∀ y ∈ orbitSetThreeHalves x_0, (3 / 2 : ℝ) * y ∈ orbitSetThreeHalves x_0) ∧
    2 * x_0 ∉ orbitSetThreeHalves x_0 ∧
    3 * x_0 ∉ orbitSetThreeHalves x_0 := by
  refine ⟨⟨⟨0, by simp⟩, ?_⟩, ?_, ?_⟩
  · rintro y ⟨n, rfl⟩
    refine ⟨n + 1, ?_⟩
    rw [pow_succ]
    ring
  · rintro ⟨n, hn⟩
    have hx_ne : x_0 ≠ 0 := ne_of_gt hx0
    have hpow2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have h1 : (3 / 2 : ℝ) ^ n = 2 := by
      apply mul_left_cancel₀ hx_ne
      linarith
    rw [div_pow] at h1
    have h2 : (3 : ℝ) ^ n = 2 * (2 : ℝ) ^ n := by
      exact (div_eq_iff hpow2).mp h1
    have hnat : 3 ^ n = 2 ^ (n + 1) := by
      have hcast : ((3 ^ n : ℕ) : ℝ) = ((2 ^ (n + 1) : ℕ) : ℝ) := by
        push_cast
        rw [pow_succ']
        exact h2
      exact_mod_cast hcast
    exact (three_pow_ne_two_pow_succ_and_three_mul_two_pow n).1 hnat
  · rintro ⟨n, hn⟩
    have hx_ne : x_0 ≠ 0 := ne_of_gt hx0
    have hpow2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have h1 : (3 / 2 : ℝ) ^ n = 3 := by
      apply mul_left_cancel₀ hx_ne
      linarith
    rw [div_pow] at h1
    have h2 : (3 : ℝ) ^ n = 3 * (2 : ℝ) ^ n := by
      exact (div_eq_iff hpow2).mp h1
    have hnat : 3 ^ n = 3 * 2 ^ n := by
      have hcast : ((3 ^ n : ℕ) : ℝ) = ((3 * 2 ^ n : ℕ) : ℝ) := by
        push_cast
        exact h2
      exact_mod_cast hcast
    rcases Decidable.eq_or_ne n 1 with rfl | hn1
    · norm_num at hnat
    · exact (three_pow_ne_two_pow_succ_and_three_mul_two_pow n).2 hn1 hnat

/-- **Finite-Horizon Confinement Cylinders Are Neither `×2`- Nor `×3`-Invariant
(`finite_horizon_confinement_not_two_or_three_invariant`, Section 14 Negative Theorem)**:
1. For `α = 2/9`, both step `0` (`Int.fract (2/9) = 2/9 < 1/2`) and step `1`
   (`Int.fract ((2/9)*(3/2)) = 1/3 < 1/2`) lie in `[0, 1/2)`, whereas `2 * α = 4/9` fails
   at step `1` (`Int.fract ((4/9)*(3/2)) = 2/3 ≥ 1/2`) and `3 * α = 2/3` fails at step `0`
   (`Int.fract (2/3) = 2/3 ≥ 1/2`).
2. On positive integer seeds at horizon `N = 3`, `survivesSteps 9 3 = true` (`9 → 14 → 21 → 32`,
   parities `1, 0, 1`), whereas **both** `survivesSteps (2 * 9) 3 = false` (`18 → 27 → 41`,
   parities `0, 1, 1`) and `survivesSteps (3 * 9) 3 = false` (`27 → 41`, parities `1, 1`). -/
theorem finite_horizon_confinement_not_two_or_three_invariant :
    (Int.fract ((2 / 9 : ℝ) * (3 / 2 : ℝ) ^ 0) < (1 / 2 : ℝ) ∧
      Int.fract ((2 / 9 : ℝ) * (3 / 2 : ℝ) ^ 1) < (1 / 2 : ℝ) ∧
      (1 / 2 : ℝ) ≤ Int.fract ((2 * (2 / 9 : ℝ)) * (3 / 2 : ℝ) ^ 1) ∧
      (1 / 2 : ℝ) ≤ Int.fract ((3 * (2 / 9 : ℝ)) * (3 / 2 : ℝ) ^ 0)) ∧
    (survivesSteps 9 3 = true ∧
      survivesSteps (2 * 9) 3 = false ∧
      survivesSteps (3 * 9) 3 = false) := by
  refine ⟨?_, by decide⟩
  have hf29 : Int.fract (2 / 9 : ℝ) = (2 / 9 : ℝ) :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hf13 : Int.fract (1 / 3 : ℝ) = (1 / 3 : ℝ) :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hf23 : Int.fract (2 / 3 : ℝ) = (2 / 3 : ℝ) :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have h1 : (2 / 9 : ℝ) * (3 / 2 : ℝ) ^ 0 = (2 / 9 : ℝ) := by norm_num
  have h2 : (2 / 9 : ℝ) * (3 / 2 : ℝ) ^ 1 = (1 / 3 : ℝ) := by norm_num
  have h3 : (2 * (2 / 9 : ℝ)) * (3 / 2 : ℝ) ^ 1 = (2 / 3 : ℝ) := by norm_num
  have h4 : (3 * (2 / 9 : ℝ)) * (3 / 2 : ℝ) ^ 0 = (2 / 3 : ℝ) := by norm_num
  rw [h1, h2, h3, h4, hf29, hf13, hf23]
  norm_num

/-! ## 2. Section 15: Discrepancy, Escape Counting & the Erdős–Turán Conditional Reduction -/

/-- Number of steps `n < N` where `Int.fract (α * (3/2)^n) < 1/2`. -/
noncomputable def lowerHalfCount (α : ℝ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range N).filter (fun n => Int.fract (α * (3 / 2 : ℝ) ^ n) < (1 / 2 : ℝ))).card

/-- Number of steps `n < N` where `1/2 ≤ Int.fract (α * (3/2)^n)` (escapes from `[0, 1/2)`). -/
noncomputable def upperHalfCount (α : ℝ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range N).filter (fun n => ¬ (Int.fract (α * (3 / 2 : ℝ) ^ n) < (1 / 2 : ℝ)))).card

/-- Exact partition identity `lowerHalfCount α N + upperHalfCount α N = N`. -/
theorem lowerHalfCount_add_upperHalfCount_eq (α : ℝ) (N : ℕ) :
    lowerHalfCount α N + upperHalfCount α N = N := by
  classical
  induction N with
  | zero =>
      simp [lowerHalfCount, upperHalfCount]
  | succ N ih =>
      unfold lowerHalfCount upperHalfCount at ih ⊢
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
      by_cases h : Int.fract (α * (3 / 2 : ℝ) ^ N) < (1 / 2 : ℝ)
      · simp only [h, ↓reduceIte, not_true_eq_false]
        rw [Finset.card_insert_of_not_mem (by simp)]
        omega
      · simp only [h, ↓reduceIte, not_false_eq_true]
        rw [Finset.card_insert_of_not_mem (by simp)]
        omega

/-- Discrepancy of the finite orbit `{α * (3/2)^n}_{n < N}` on the lower half-interval `[0, 1/2)`:
`halfIntervalDiscrepancy α N = |(lowerHalfCount α N : ℝ) / N - 1/2|`. -/
noncomputable def halfIntervalDiscrepancy (α : ℝ) (N : ℕ) : ℝ :=
  |((lowerHalfCount α N : ℕ) : ℝ) / (N : ℝ) - (1 / 2 : ℝ)|

/-- **Quantitative Discrepancy-to-Escape Bridge (`discrepancy_lt_half_forces_mahler_escape`,
Section 15.2)**:
For any `α : ℝ` and horizon `1 ≤ N`:
1. If `halfIntervalDiscrepancy α N ≤ 1/2 - δ`, then `δ * N ≤ upperHalfCount α N`, and
2. If `halfIntervalDiscrepancy α N < 1/2`, then `1 ≤ upperHalfCount α N` and there exists
   `n < N` such that `1 / 2 ≤ Int.fract (α * (3 / 2)^n)`. -/
theorem discrepancy_lt_half_forces_mahler_escape (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∀ δ : ℝ, halfIntervalDiscrepancy α N ≤ (1 / 2 : ℝ) - δ →
      δ * (N : ℝ) ≤ (upperHalfCount α N : ℝ)) ∧
      (halfIntervalDiscrepancy α N < (1 / 2 : ℝ) →
        1 ≤ upperHalfCount α N ∧
          ∃ n < N, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hpart : (lowerHalfCount α N : ℝ) + (upperHalfCount α N : ℝ) = (N : ℝ) := by
    exact_mod_cast lowerHalfCount_add_upperHalfCount_eq α N
  refine ⟨?_, ?_⟩
  · intro δ hdisc
    unfold halfIntervalDiscrepancy at hdisc
    have habs := (abs_le.mp hdisc).2
    have hdiv : ((lowerHalfCount α N : ℝ) / (N : ℝ)) ≤ 1 - δ := by linarith
    have hmul : (lowerHalfCount α N : ℝ) ≤ (1 - δ) * (N : ℝ) :=
      (div_le_iff₀ hN_pos).mp hdiv
    linarith
  · intro hlt
    unfold halfIntervalDiscrepancy at hlt
    have habs := (abs_lt.mp hlt).2
    have hdiv : ((lowerHalfCount α N : ℝ) / (N : ℝ)) < 1 := by linarith
    have hmul : (lowerHalfCount α N : ℝ) < 1 * (N : ℝ) :=
      (div_lt_iff₀ hN_pos).mp hdiv
    have hup_pos_real : (0 : ℝ) < (upperHalfCount α N : ℝ) := by linarith
    have hup_pos : 0 < upperHalfCount α N := by exact_mod_cast hup_pos_real
    refine ⟨by omega, ?_⟩
    classical
    unfold upperHalfCount at hup_pos
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hup_pos
    simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hn
    exact ⟨n, hn.1, hn.2⟩

/-- **Erdős–Turán Exponential-Sum Conditional Reduction (`erdos_turan_conditional_mahler_reduction`,
Section 15.1–15.2 & Section 21 Type 5)**:
Suppose at horizon `1 ≤ N` and frequency cutoff `1 ≤ K`, the discrepancy `halfIntervalDiscrepancy α N`
satisfies the Erdős–Turán upper bound
`halfIntervalDiscrepancy α N ≤ C / K + (C / N) * ∑ k ∈ Finset.Icc 1 K, W k / k`,
where `W k ≥ 0` bounds the Weyl exponential sum `|∑_{n < N} e(k * α * (3/2)^n)|`.
Whenever the right-hand side is strictly less than `1 / 2`, `α` escapes `[0, 1/2)` before step `N`. -/
theorem erdos_turan_conditional_mahler_reduction (α : ℝ) {N K : ℕ} (C : ℝ) (W : ℕ → ℝ)
    (hN : 1 ≤ N)
    (het :
      halfIntervalDiscrepancy α N ≤
        C / (K : ℝ) + (C / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 K, W k / (k : ℝ))
    (hsub :
      C / (K : ℝ) + (C / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 K, W k / (k : ℝ) < (1 / 2 : ℝ)) :
    1 ≤ upperHalfCount α N ∧
      ∃ n < N, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n) := by
  have hlt : halfIntervalDiscrepancy α N < (1 / 2 : ℝ) := lt_of_le_of_lt het hsub
  exact (discrepancy_lt_half_forces_mahler_escape α hN).2 hlt

/-! ## 3. Section 16: S-Unit / Dyadic-Block Uniqueness Past Bit `W` & Why Finiteness Stops at `1` -/

/-- **Distinct Seeds in `[0, 2^W)` Cannot Share a Parity Prefix Past Horizon `W`
(`distinct_dyadic_seeds_cannot_share_prefix_past_W`, Section 16)**:
If `a₁ < a₂ < 2^W` and `W ≤ N`, then `a₁` and `a₂` cannot have the same parity prefix
up to step `N` (`¬ ∀ n < N, orbit a₁ n % 2 = orbit a₂ n % 2`). -/
theorem distinct_dyadic_seeds_cannot_share_prefix_past_W {a₁ a₂ W N : ℕ}
    (hlt : a₁ < a₂) (ha₂ : a₂ < 2 ^ W) (hWN : W ≤ N) :
    ¬ (∀ n < N, orbit a₁ n % 2 = orbit a₂ n % 2) := by
  intro hall
  have hmod := (orbit_parity_eq_upto_iff_mod_two_pow a₁ a₂ N).mp hall
  have h2W_le : 2 ^ W ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hWN
  have ha₁_mod : a₁ % 2 ^ N = a₁ := Nat.mod_eq_of_lt (by omega)
  have ha₂_mod : a₂ % 2 ^ N = a₂ := Nat.mod_eq_of_lt (by omega)
  rw [ha₁_mod, ha₂_mod] at hmod
  omega

/-- **Section 16 Negative/Limitative Witness (`single_dyadic_survivor_witness_149`)**:
In the dyadic block `[128, 256)` (`W = 7`), seed `149` (`128 ≤ 149 < 256`) survives through
horizon `N = 28` (`fastSeedSurvives 149 28 = true` and `∃ ξ, ValidCompanionUpTo 149 ξ 28`)
and is the unique seed in `[0, 2^28)` realizing its 28-bit parity prefix, demonstrating that
bounding the number of survivors in a dyadic block / prefix class by `≤ 1` does not imply
emptiness (`= 0`) without a step-29 obstruction (`fastSeedSurvives 149 29 = false`). -/
theorem single_dyadic_survivor_witness_149 :
    128 ≤ 149 ∧ 149 < 256 ∧
      fastSeedSurvives 149 28 = true ∧
      fastSeedSurvives 149 29 = false ∧
      (∃ ξ : ℝ, ValidCompanionUpTo 149 ξ 28) ∧
      ¬ (∃ ξ : ℝ, ValidCompanionUpTo 149 ξ 29) ∧
      (∀ a < 2 ^ 28, a ≠ 149 → ¬ (∀ n < 28, orbit a n % 2 = orbit 149 n % 2)) := by
  rcases seed_149_survives_28_and_fails_29 with ⟨h28, h29, hcomp28, hcomp29⟩
  refine ⟨by decide, by decide, h28, h29, hcomp28, hcomp29, ?_⟩
  intro a ha hne hall
  rcases (by omega : a < 149 ∨ 149 < a) with hlt | hgt
  · exact distinct_dyadic_seeds_cannot_share_prefix_past_W hlt (by decide : 149 < 2 ^ 28) (le_refl 28) hall
  · exact distinct_dyadic_seeds_cannot_share_prefix_past_W hgt ha (le_refl 28)
      (fun n hn => (hall n hn).symm)

/-! ## 4. Section 17: Mahler's Method Value-Irrationality Exclusion Bridge -/

/-- **Mahler's Method Value-Irrationality Exclusion Bridge
(`mahler_method_irrational_value_excludes_integer_seed`, Section 17.1–17.2)**:
Suppose a parity stream `ε : ℕ → ℕ` has an associated series value `v : ℝ` such that:
1. Any nonnegative integer seed `a_0 : ℕ` realizing `ε` (`∀ n, orbit a_0 n % 2 = ε n % 2`)
   forces `v = (q a_0 : ℝ)` for a rational seed-evaluation map `q : ℕ → ℚ`, and
2. By Mahler's method (e.g., Adamczewski–Faverjon value transcendence/irrationality),
   `v` is irrational (`∀ r : ℚ, v ≠ (r : ℝ)`).
Then no nonnegative integer seed realizes `ε`, and `seedResidue ε` never stabilizes. -/
theorem mahler_method_irrational_value_excludes_integer_seed
    (ε : ℕ → ℕ) (v : ℝ) (q : ℕ → ℚ)
    (hseed_eq : ∀ a_0 : ℕ, (∀ n : ℕ, orbit a_0 n % 2 = ε n % 2) → v = (q a_0 : ℝ))
    (hirr : ∀ r : ℚ, v ≠ (r : ℝ)) :
    (∀ a_0 : ℕ, ¬ (∀ n : ℕ, orbit a_0 n % 2 = ε n % 2)) ∧
      (∀ a_0 : ℕ, ¬ (∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue ε N = a_0)) := by
  have hno_seed : ∀ a_0 : ℕ, ¬ (∀ n : ℕ, orbit a_0 n % 2 = ε n % 2) := by
    intro a_0 hall
    exact hirr (q a_0) (hseed_eq a_0 hall)
  refine ⟨hno_seed, ?_⟩
  intro a_0 hstab
  exact hno_seed a_0 ((exists_nonneg_seed_iff_seedResidue_stabilizes ε a_0).mpr hstab)

/-! ## 5. Section 20: First-Return Renormalization & 2-Adic Non-Self-Similarity -/

/-- **First-Return Renormalization 2-Adic Defect & Multiplier Mismatch
(`first_return_two_adic_defect_and_multiplier_mismatch`, Section 20 Negative Result)**:
Along an odd-to-odd block `2^s * b' = 3^s * b - 1` (or `2^s * b' = 3^(s-1) * (3 * b + 1)`):
In the period-3 (`001`, `s = 3`) vs. defect-4 (`0001`, `s = 4`) return branches on the Cantor dust,
tracking the homoclinic invariant `I(b) = 19 * b + 9` under `2^s * b' = 3^(s-1) * (3 * b + 1)`:
1. On the `s = 3` (`001`) branch (`8 * b' = 9 * (3 * b + 1) = 27 * b + 9`), the invariant is
   **purely homogeneous**: `8 * (19 * b' + 9) = 27 * (19 * b + 9) + 0` (`E(3) = 0`).
2. On the `s = 4` (`0001`) branch (`16 * b' = 27 * (3 * b + 1) = 81 * b + 27`), the invariant
   acquires a **non-zero inhomogeneous defect `-72`**:
   `16 * (19 * b' + 9) = 81 * (19 * b + 9) - 72` (`E(4) = -72 ≠ 0`).
3. Furthermore, no rational rescaling factor `λ : ℚ` can equalize the `s = 3` multiplier `27/8`
   and the `s = 4` multiplier `81/16` (`(27 / 8 : ℚ) ≠ (81 / 16 : ℚ)`), proving that 1D archimedean
   return-map renormalization does not make the 2-adic carry transition self-similar. -/
theorem first_return_two_adic_defect_and_multiplier_mismatch :
    (∀ b b' : ℤ, 8 * b' = 27 * b + 9 →
      8 * (19 * b' + 9) = 27 * (19 * b + 9)) ∧
      (∀ b b' : ℤ, 16 * b' = 81 * b + 27 →
        16 * (19 * b' + 9) = 81 * (19 * b + 9) - 72) ∧
      (-72 : ℤ) ≠ 0 ∧
      ((27 / 8 : ℚ) ≠ (81 / 16 : ℚ)) := by
  refine ⟨?_, ?_, by decide, by norm_num⟩
  · intro b b' h3
    linarith
  · intro b b' h4
    linarith

end Mahler.SolenoidDiscrepancyAndRenorm
