import TwoSidedCRTAndBackwardObstructions

/-!
# Exact 3-Adic Valuation Sum Conservation, Block-Boundary Product Telescope & 112-Module Synthesis

This module formalizes Path 11 (Modules 111–112) and synthesizes the complete
112-module formalization:

1. **Exact Single-Block Orbit Transition Identity (`one_block_affine_orbit_transition`)**:
   Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), eliminating `u k` between
   `3 * orbit a_0 (blockSteps s k) + 1 = 2^(s k) * u k` and
   `orbit a_0 (blockSteps s (k + 1)) = 3^(s k - 1) * u k` yields the direct
   block-boundary recurrence:
   `2^(s k) * (3 * orbit a_0 (blockSteps s (k + 1))) =
     3^(s k) * (3 * orbit a_0 (blockSteps s k) + 1)`
   and over `ℝ`:
   `(orbit a_0 (blockSteps s (k + 1)) : ℝ) =
     (3 / 2 : ℝ)^(s k) * ((orbit a_0 (blockSteps s k) : ℝ) + 1 / 3)`.
2. **Even-Step Sum Conservation & 2-to-1 Even-to-Odd Domination
   (`evenStepSum_add_eq_blockSteps`, `surviving_even_step_domination`)**:
   Define `evenStepSum s m = ∑_{k=0}^{m-1} (s k - 1)`. Whenever `∀ k < m, 1 ≤ s k`:
   - `evenStepSum s m + m = blockSteps s m` and `evenStepSum s m = blockSteps s m - m`.
   - Along any surviving orbit (`m + 1 < K`, `ValidCompanionUpTo a_0 ξ (blockSteps s (m + 2))`),
     `2 * m ≤ evenStepSum s m + 1` (at least `2 * m - 1` even steps for every `m` odd steps).
3. **Exact 3-Adic Valuation Conservation of the Block-Boundary Orbit Product
   (`orbitBoundaryProduct_eq_three_pow_mul_quotientProduct`,
   `orbitBoundaryProduct_exact_three_adic_valuation`)**:
   Define `orbitBoundaryProduct a_0 s m = ∏_{k=0}^{m-1} orbit a_0 (blockSteps s (k + 1))`
   and `quotientProduct u m = ∏_{k=0}^{m-1} u k`. Along any `ValidBlockChain a_0 s u K`
   (`m < K`):
   - `orbitBoundaryProduct a_0 s m = 3^(blockSteps s m - m) * quotientProduct u m`,
   - `Nat.Coprime (quotientProduct u m) 6`,
   - `3^(blockSteps s m - m) ∣ orbitBoundaryProduct a_0 s m`, and
   - `¬ (3^(blockSteps s m - m + 1) ∣ orbitBoundaryProduct a_0 s m)`.
4. **The 112-Module Grand Synthesis (`mahler_grand_112_module_synthesis`)**:
   Unites the shift-free unshifted ceiling comparison, the carryless base-3
   companion characterization, the autonomous `normalizedMinSlack` interval map,
   the seed–quotient–slack GCD identity, the 3-adic valuation conservation law,
   and the exact `113`-step survival / `114`-step death of `recordHolderA0`.
-/

namespace Mahler.ThreeAdicConservation

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

/-! ## 1. Exact Single-Block Orbit Transition Identity -/

/-- **Exact Single-Block Orbit Transition Identity (`one_block_affine_orbit_transition`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`),
`2^(s k) * (3 * orbit a_0 (blockSteps s (k + 1))) =
  3^(s k) * (3 * orbit a_0 (blockSteps s k) + 1)`
and over `ℝ`:
`(orbit a_0 (blockSteps s (k + 1)) : ℝ) =
  (3 / 2 : ℝ)^(s k) * ((orbit a_0 (blockSteps s k) : ℝ) + 1 / 3)`. -/
theorem one_block_affine_orbit_transition
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (s k) * (3 * orbit a_0 (blockSteps s (k + 1))) =
        3 ^ (s k) * (3 * orbit a_0 (blockSteps s k) + 1) ∧
      (orbit a_0 (blockSteps s (k + 1)) : ℝ) =
        (3 / 2 : ℝ) ^ (s k) *
          ((orbit a_0 (blockSteps s k) : ℝ) + (1 / 3 : ℝ)) := by
  have horb_k := (hchain k (by omega)).2.2
  have hsk : 1 ≤ s k := (hchain k (by omega)).1
  have horb_k1 := (orbit_succ_eq_three_pow_mul_u hk1 hchain).1
  have hpow3 : 3 * 3 ^ (s k - 1) = 3 ^ (s k) := by
    conv_rhs => rw [show s k = (s k - 1) + 1 by omega, Nat.pow_succ]
    ring
  have hnat :
      2 ^ (s k) * (3 * orbit a_0 (blockSteps s (k + 1))) =
        3 ^ (s k) * (3 * orbit a_0 (blockSteps s k) + 1) := by
    rw [horb_k1, horb_k]
    calc
      2 ^ (s k) * (3 * (3 ^ (s k - 1) * u k)) =
          (3 * 3 ^ (s k - 1)) * (2 ^ (s k) * u k) := by ring
      _ = 3 ^ (s k) * (2 ^ (s k) * u k) := by rw [hpow3]
  refine ⟨hnat, ?_⟩
  have hreal :
      (2 : ℝ) ^ (s k) * (3 * (orbit a_0 (blockSteps s (k + 1)) : ℝ)) =
        (3 : ℝ) ^ (s k) * (3 * (orbit a_0 (blockSteps s k) : ℝ) + 1) := by
    exact_mod_cast hnat
  have h2_ne : (2 : ℝ) ^ (s k) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_pow]
  field_simp [h2_ne]
  linarith

/-! ## 2. Even-Step Sum Conservation & 2-to-1 Even-to-Odd Domination -/

/-- Cumulative number of even steps `∑_{k=0}^{m-1} (s k - 1)` in the first `m` blocks. -/
def evenStepSum (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => evenStepSum s m + (s m - 1)

/-- **Even-Step Sum Conservation (`evenStepSum_add_eq_blockSteps`)**:
Whenever `∀ k < m, 1 ≤ s k`, `evenStepSum s m + m = blockSteps s m` and
`evenStepSum s m = blockSteps s m - m`. -/
theorem evenStepSum_add_eq_blockSteps {s : ℕ → ℕ} {m : ℕ}
    (hs : ∀ k < m, 1 ≤ s k) :
    evenStepSum s m + m = blockSteps s m ∧
      evenStepSum s m = blockSteps s m - m := by
  have hadd : evenStepSum s m + m = blockSteps s m := by
    induction m with
    | zero => rfl
    | succ m ih =>
        have ihm := ih (fun k hk => hs k (by omega))
        have hsm : 1 ≤ s m := hs m (by omega)
        simp only [evenStepSum, blockSteps]
        omega
  exact ⟨hadd, by omega⟩

/-- **Surviving 2-to-1 Even-to-Odd Step Domination (`surviving_even_step_domination`)**:
Along any `ValidBlockChain a_0 s u K` (`m + 1 < K`) with
`ValidCompanionUpTo a_0 ξ (blockSteps s (m + 2))`, the cumulative even step count
satisfies `2 * m ≤ evenStepSum s m + 1`. -/
theorem surviving_even_step_domination
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (m + 2))) :
    2 * m ≤ evenStepSum s m + 1 := by
  have hrate := surviving_orbit_three_mul_step_rate hmK hchain hsurv
  have hs : ∀ k < m, 1 ≤ s k := fun k hk => (hchain k (by omega)).1
  have heven := (evenStepSum_add_eq_blockSteps hs).1
  omega

/-! ## 3. Exact 3-Adic Valuation Conservation of the Block-Boundary Orbit Product -/

/-- Product of the first `m` block-boundary orbit values `∏_{k=0}^{m-1} orbit a_0 (blockSteps s (k + 1))`. -/
def orbitBoundaryProduct (a_0 : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => orbitBoundaryProduct a_0 s m * orbit a_0 (blockSteps s (m + 1))

/-- Product of the first `m` odd coprime quotients `∏_{k=0}^{m-1} u k`. -/
def quotientProduct (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => quotientProduct u m * u m

/-- **Block-Boundary Orbit Product Factorization
(`orbitBoundaryProduct_eq_three_pow_mul_quotientProduct`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`),
`orbitBoundaryProduct a_0 s m = 3^(evenStepSum s m) * quotientProduct u m`
and `Nat.Coprime (quotientProduct u m) 6`. -/
theorem orbitBoundaryProduct_eq_three_pow_mul_quotientProduct
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    orbitBoundaryProduct a_0 s m =
        3 ^ (evenStepSum s m) * quotientProduct u m ∧
      Nat.Coprime (quotientProduct u m) 6 := by
  induction m with
  | zero =>
      simp [orbitBoundaryProduct, evenStepSum, quotientProduct]
  | succ m ih =>
      rcases ih (by omega) with ⟨ih_eq, ih_cop⟩
      have horb := (orbit_succ_eq_three_pow_mul_u hmK hchain).1
      have hu_cop :=
        (u_coprime_six_of_validBlockChain (by omega : m < K) hchain).2.2
      have hu_cop2 : Nat.Coprime (u m) 2 :=
        Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr hu_cop.1)
      have hu_cop3 : Nat.Coprime (u m) 3 :=
        Nat.Coprime.symm (Nat.prime_three.coprime_iff_not_dvd.mpr hu_cop.2)
      have hu_cop6 : Nat.Coprime (u m) 6 := by simpa using hu_cop2.mul_right hu_cop3
      refine ⟨?_, ih_cop.mul hu_cop6⟩
      simp only [orbitBoundaryProduct, evenStepSum, quotientProduct]
      rw [ih_eq, horb, Nat.pow_add]
      ring

/-- **Exact 3-Adic Valuation Conservation Law
(`orbitBoundaryProduct_exact_three_adic_valuation`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`), the exact 3-adic valuation of
`orbitBoundaryProduct a_0 s m` is `blockSteps s m - m`:
`orbitBoundaryProduct a_0 s m = 3^(blockSteps s m - m) * quotientProduct u m`,
`3^(blockSteps s m - m) ∣ orbitBoundaryProduct a_0 s m`, and
`¬ (3^(blockSteps s m - m + 1) ∣ orbitBoundaryProduct a_0 s m)`. -/
theorem orbitBoundaryProduct_exact_three_adic_valuation
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    orbitBoundaryProduct a_0 s m =
        3 ^ (blockSteps s m - m) * quotientProduct u m ∧
      3 ^ (blockSteps s m - m) ∣ orbitBoundaryProduct a_0 s m ∧
      ¬ (3 ^ (blockSteps s m - m + 1) ∣ orbitBoundaryProduct a_0 s m) := by
  rcases orbitBoundaryProduct_eq_three_pow_mul_quotientProduct hmK hchain with
    ⟨heq, hcop6⟩
  have hs : ∀ k < m, 1 ≤ s k := fun k hk => (hchain k (by omega)).1
  have heven := (evenStepSum_add_eq_blockSteps hs).2
  rw [heven] at heq
  refine ⟨heq, ⟨quotientProduct u m, heq⟩, ?_⟩
  rw [heq, Nat.pow_succ]
  rintro ⟨q, hq⟩
  have hpos : 0 < 3 ^ (blockSteps s m - m) := Nat.pow_pos (by decide)
  have hsplit :
      3 ^ (blockSteps s m - m) * 3 * q =
        3 ^ (blockSteps s m - m) * (3 * q) := by ring
  rw [hsplit] at hq
  have hquot_eq : quotientProduct u m = 3 * q :=
    Nat.eq_of_mul_eq_mul_left hpos hq
  have hcop3 : Nat.Coprime (quotientProduct u m) 3 :=
    hcop6.coprime_dvd_right (by decide : 3 ∣ 6)
  have hdvd3 : 3 ∣ quotientProduct u m := ⟨q, hquot_eq⟩
  have h1 : 3 ∣ 1 := by
    rw [← hcop3.gcd_eq_one]
    exact Nat.dvd_gcd hdvd3 (dvd_refl 3)
  omega

/-! ## 4. The 112-Module Grand Synthesis -/

/-- **The 112-Module Grand Synthesis (`mahler_grand_112_module_synthesis`)**:
Combines in a single machine-checked theorem:
1. The Shift-Free Unshifted Ceiling Comparison for `0 < minSlack s m`,
2. The Carryless Base-3 Frozen-Prefix Equivalence for `ValidCompanionUpTo`,
3. The Autonomous 1D Interval Map for `normalizedMinSlack`,
4. The Exact 3-Adic Valuation Conservation Law for `orbitBoundaryProduct`, and
5. The Exact `113`-Step Survival and `114`-Step Death of the 55-Bit Record-Holder
   `recordHolderA0 = 29871555608238677`. -/
theorem mahler_grand_112_module_synthesis :
    (∀ (s : ℕ → ℕ) (m : ℕ),
      0 < minSlack s m ↔
        ∀ j ≤ m,
          (3 : ℤ) ^ (blockSteps s m) *
              (integerSlack s j - (2 : ℤ) ^ (blockSteps s j)) <
            (3 : ℤ) ^ (blockSteps s j) * integerSlack s m) ∧
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ},
      1 ≤ K → ValidBlockChain a_0 s u K →
        ((∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s K)) ↔
          ∀ j ≤ K - 1,
            (2 ^ (blockSteps (shiftSeq s j) (K - 1 - j + 1) + 1) * u (K - 1)) /
                3 ^ (blockSteps (shiftSeq s j) (K - 1 - j)) =
              6 * orbit a_0 (blockSteps s j) + 2)) ∧
    (∀ (s : ℕ → ℕ) (m : ℕ),
      normalizedMinSlack s (m + 1) =
        min 1 ((3 / 2 : ℝ) ^ (s m) * normalizedMinSlack s m - 2)) ∧
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ},
      m < K → ValidBlockChain a_0 s u K →
        orbitBoundaryProduct a_0 s m =
            3 ^ (blockSteps s m - m) * quotientProduct u m ∧
          3 ^ (blockSteps s m - m) ∣ orbitBoundaryProduct a_0 s m ∧
          ¬ (3 ^ (blockSteps s m - m + 1) ∣ orbitBoundaryProduct a_0 s m)) ∧
    (recordHolderA0 < 2 ^ 55 ∧
      (∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 113) ∧
      ¬ (∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 114)) :=
  ⟨minSlack_pos_iff_unshifted_ceiling_comparison,
    fun hK hchain => exists_validCompanionUpTo_iff_base_three_prefixes_frozen hK hchain,
    normalizedMinSlack_succ_eq,
    fun hmK hchain => orbitBoundaryProduct_exact_three_adic_valuation hmK hchain,
    recordHolderA0_exact_113_survival_and_114_death⟩

end Mahler.ThreeAdicConservation
