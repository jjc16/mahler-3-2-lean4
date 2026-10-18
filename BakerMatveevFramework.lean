import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DeterminantFactorization

/-!
# The Baker–Matveev Linear Forms in Logarithms Framework & Pairwise Quotient Coprimality

This module formalizes the exact algebraic and Diophantine-approximation
foundations for applying Baker–Wüstholz / Matveev linear forms in logarithms to
the reduced Mahler coprime system:

1. **Pairwise Coprimality of Consecutive Quotients (`consecutive_u_coprime`,
   `multi_step_u_gcd_dvd_coprimeRemainder`)**:
   - Because `2^(s (k + 1)) * u (k + 1) - 3^(s k) * u k = 1`, consecutive
     coprime quotients are always coprime: `Nat.Coprime (u k) (u (k + 1))`.
     Thus `u (k + 1) / u k` is always in lowest terms, with exact Weil height
     `max (u k) (u (k + 1))`.
   - Across `d` steps, `Nat.gcd (u r) (u (r + d))` divides
     `coprimeRemainder (shiftSeq s r) d`.
2. **Exponentially Small 1-Step Relative Gap (`one_step_unit_sum_exponential_squeeze`,
   `one_step_relative_gap_lt_two_thirds_pow`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ m`, `m + 1 < K`) with
   `0 < integerSlack s m`:
   - `3^(blockSteps s (m + 1)) * (6 * a_0 + 2) < 2^(blockSteps s (m + 1) + 1) * (3^(s m) * u m)`.
   - Consequently, the 1-step multiplicative approximation error satisfies:
     `0 < (2^(s (m + 1)) * u (m + 1) : ℝ) / (3^(s m) * u m : ℝ) - 1 <
       (1 / (3 * a_0 + 1 : ℝ)) * (2 / 3 : ℝ)^(blockSteps s (m + 1))`.
3. **Exponentially Small Global Relative Gap in Sub-Ceiling Phases
   (`sub_ceiling_global_exponential_squeeze`)**:
   Whenever `0 < integerSlack s m ≤ 2^(blockSteps s m)` (`1 ≤ m < K`),
   `0 < (3^(blockSteps s m + 1) * (2 * a_0 + 1) : ℝ) /
     (2^(blockSteps s (m + 1) + 1) * u m : ℝ) - 1 ≤
     (1 / (6 * a_0 + 2 : ℝ)) * (2 / 3 : ℝ)^(blockSteps s m)`.
-/

namespace Mahler.BakerMatveev

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

/-! ## 1. Pairwise Coprimality of Consecutive Quotients `u k` and `u (k + 1)` -/

/-- **Pairwise Coprimality of Consecutive Coprime Quotients (`consecutive_u_coprime`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`),
`Nat.Coprime (u k) (u (k + 1))`. -/
theorem consecutive_u_coprime {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    Nat.Coprime (u k) (u (k + 1)) := by
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [Nat.Coprime, ← Nat.dvd_one]
  have hdvd_uk : Nat.gcd (u k) (u (k + 1)) ∣ 3 ^ (s k) * u k :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_left (u k) (u (k + 1))) _
  have hdvd_uk1 : Nat.gcd (u k) (u (k + 1)) ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right (u k) (u (k + 1))) _
  rw [hrec] at hdvd_uk1
  exact (Nat.dvd_add_right hdvd_uk).mp hdvd_uk1

/-- **Multi-Step GCD Divisibility (`multi_step_u_gcd_dvd_coprimeRemainder`)**:
Along any `ValidBlockChain a_0 s u K` (`r + d < K`),
`Nat.gcd (u r) (u (r + d))` divides `coprimeRemainder (shiftSeq s r) d`. -/
theorem multi_step_u_gcd_dvd_coprimeRemainder
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hrd : r + d < K) (hchain : ValidBlockChain a_0 s u K) :
    Nat.gcd (u r) (u (r + d)) ∣ coprimeRemainder (shiftSeq s r) d := by
  have hid := shifted_coprime_quotient_m_step_identity hrd hchain
  have hdvd_ur :
      Nat.gcd (u r) (u (r + d)) ∣
        3 ^ (blockSteps (shiftSeq s r) d) * u r :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_left (u r) (u (r + d))) _
  have hdvd_urd :
      Nat.gcd (u r) (u (r + d)) ∣
        2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right (u r) (u (r + d))) _
  rw [hid] at hdvd_urd
  exact (Nat.dvd_add_right hdvd_ur).mp hdvd_urd

/-! ## 2. Exponentially Small 1-Step Multiplicative Gap -/

/-- **1-Step Unit-Sum Exponential Squeeze (`one_step_unit_sum_exponential_squeeze`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ m`, `m < K`) with
`0 < integerSlack s m`,
`3^(blockSteps s (m + 1)) * (3 * a_0 + 1) <
  2^(blockSteps s (m + 1)) * (3^(s m) * u m)`. -/
theorem one_step_unit_sum_exponential_squeeze
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    3 ^ (blockSteps s (m + 1)) * (3 * a_0 + 1) <
      2 ^ (blockSteps s (m + 1)) * (3 ^ (s m) * u m) := by
  have hcor := (global_coprime_width_corridor hm1 hmK hchain hslack).1
  have hdiv2 :
      3 ^ (blockSteps s m) * (3 * a_0 + 1) <
        2 ^ (blockSteps s (m + 1)) * u m := by
    have h62 :
        3 ^ (blockSteps s m) * (6 * a_0 + 2) =
          2 * (3 ^ (blockSteps s m) * (3 * a_0 + 1)) := by ring
    have hpow2 :
        2 ^ (blockSteps s (m + 1) + 1) * u m =
          2 * (2 ^ (blockSteps s (m + 1)) * u m) := by
      rw [Nat.pow_succ]
      ring
    omega
  have h3pos : 0 < 3 ^ (s m) := Nat.pow_pos (by decide)
  have hmul := Nat.mul_lt_mul_of_pos_left hdiv2 h3pos
  have hlhs :
      3 ^ (s m) * (3 ^ (blockSteps s m) * (3 * a_0 + 1)) =
        3 ^ (blockSteps s (m + 1)) * (3 * a_0 + 1) := by
    simp only [blockSteps]
    rw [show blockSteps s m + s m = s m + blockSteps s m by omega, Nat.pow_add]
    ring
  have hrhs :
      3 ^ (s m) * (2 ^ (blockSteps s (m + 1)) * u m) =
        2 ^ (blockSteps s (m + 1)) * (3 ^ (s m) * u m) := by ring
  omega

/-- **Exponentially Small 1-Step Multiplicative Gap
(`one_step_relative_gap_lt_two_thirds_pow`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ m`, `m + 1 < K`) with
`0 < integerSlack s m`, the 1-step multiplicative ratio satisfies
`0 < (2^(s (m + 1)) * u (m + 1) : ℝ) / (3^(s m) * u m : ℝ) - 1` and
`(2^(s (m + 1)) * u (m + 1) : ℝ) / (3^(s m) * u m : ℝ) - 1 <
  (1 / (3 * (a_0 : ℝ) + 1)) * (2 / 3 : ℝ)^(blockSteps s (m + 1))`. -/
theorem one_step_relative_gap_lt_two_thirds_pow
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hm1K : m + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    0 < ((2 ^ (s (m + 1)) * u (m + 1) : ℕ) : ℝ) /
          ((3 ^ (s m) * u m : ℕ) : ℝ) - 1 ∧
      ((2 ^ (s (m + 1)) * u (m + 1) : ℕ) : ℝ) /
          ((3 ^ (s m) * u m : ℕ) : ℝ) - 1 <
        (1 / (3 * (a_0 : ℝ) + 1)) *
          (2 / 3 : ℝ) ^ (blockSteps s (m + 1)) := by
  have hrec := coprime_quotient_recurrence hm1K hchain
  have hsq :=
    one_step_unit_sum_exponential_squeeze hm1 (by omega : m < K) hchain hslack
  rcases hchain m (by omega : m < K) with ⟨_, hum_odd, _⟩
  have hum_pos : 0 < u m := by omega
  have h3um_pos_nat : 0 < 3 ^ (s m) * u m :=
    Nat.mul_pos (Nat.pow_pos (by decide)) hum_pos
  have h3um_pos : (0 : ℝ) < ((3 ^ (s m) * u m : ℕ) : ℝ) := by
    exact_mod_cast h3um_pos_nat
  have hdiff_eq :
      ((2 ^ (s (m + 1)) * u (m + 1) : ℕ) : ℝ) /
          ((3 ^ (s m) * u m : ℕ) : ℝ) - 1 =
        1 / ((3 ^ (s m) * u m : ℕ) : ℝ) := by
    rw [hrec]
    push_cast
    have hne : (3 : ℝ) ^ (s m) * (u m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h3um_pos_nat)
    field_simp [hne]
  rw [hdiff_eq]
  refine ⟨div_pos one_pos h3um_pos, ?_⟩
  have hsq_real :
      (3 : ℝ) ^ (blockSteps s (m + 1)) * (3 * (a_0 : ℝ) + 1) <
        (2 : ℝ) ^ (blockSteps s (m + 1)) * ((3 ^ (s m) * u m : ℕ) : ℝ) := by
    exact_mod_cast hsq
  have h3T_pos : (0 : ℝ) < (3 : ℝ) ^ (blockSteps s (m + 1)) :=
    pow_pos (by norm_num) _
  have ha0_pos : (0 : ℝ) < 3 * (a_0 : ℝ) + 1 := by positivity
  have hden_pos :
      (0 : ℝ) < (3 * (a_0 : ℝ) + 1) * (3 : ℝ) ^ (blockSteps s (m + 1)) :=
    mul_pos ha0_pos h3T_pos
  have hrhs :
      (1 / (3 * (a_0 : ℝ) + 1)) * (2 / 3 : ℝ) ^ (blockSteps s (m + 1)) =
        (2 : ℝ) ^ (blockSteps s (m + 1)) /
          ((3 * (a_0 : ℝ) + 1) * (3 : ℝ) ^ (blockSteps s (m + 1))) := by
    rw [div_pow, div_mul_div_comm, one_mul]
  rw [hrhs, div_lt_div_iff₀ h3um_pos hden_pos]
  linarith

/-! ## 3. Exponentially Small Global Multiplicative Gap in Sub-Ceiling Phases -/

/-- **Sub-Ceiling Global Exponential Squeeze (`sub_ceiling_global_exponential_squeeze`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ m`, `m < K`) in a sub-ceiling
phase (`0 < integerSlack s m ≤ 2^(blockSteps s m)`),
`0 < (3^(blockSteps s m + 1) * (2 * a_0 + 1) : ℝ) /
  (2^(blockSteps s (m + 1) + 1) * u m : ℝ) - 1 ≤
  (1 / (6 * a_0 + 2 : ℝ)) * (2 / 3 : ℝ)^(blockSteps s m)`. -/
theorem sub_ceiling_global_exponential_squeeze
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hle : integerSlack s m ≤ (2 : ℤ) ^ (blockSteps s m)) :
    0 < ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) /
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) - 1 ∧
      ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) /
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) - 1 ≤
        (1 / (6 * (a_0 : ℝ) + 2)) * (2 / 3 : ℝ) ^ (blockSteps s m) := by
  have hcor := (global_coprime_width_corridor hm1 hmK hchain hpos).1
  have hslack := integerSlack_eq_orbit_slack hmK hchain
  rcases hchain m hmK with ⟨_, hum_odd, _⟩
  have hum_pos : 0 < 2 ^ (blockSteps s (m + 1) + 1) * u m :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hum_real_pos :
      (0 : ℝ) < ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
    exact_mod_cast hum_pos
  have hdiff_eq :
      ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) /
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) - 1 =
        (integerSlack s m : ℝ) /
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
    have hcast :
        (integerSlack s m : ℝ) =
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) -
            ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
      exact_mod_cast hslack
    have hne : ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt hum_real_pos
    rw [hcast, div_sub_one hne]
  rw [hdiff_eq]
  have hslack_real_pos : (0 : ℝ) < (integerSlack s m : ℝ) := by
    exact_mod_cast hpos
  refine ⟨div_pos hslack_real_pos hum_real_pos, ?_⟩
  have hle_real : (integerSlack s m : ℝ) ≤ (2 : ℝ) ^ (blockSteps s m) := by
    exact_mod_cast hle
  have hcor_real :
      (3 : ℝ) ^ (blockSteps s m) * (6 * (a_0 : ℝ) + 2) <
        ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
    exact_mod_cast hcor
  have hden_pos :
      (0 : ℝ) < (6 * (a_0 : ℝ) + 2) * (3 : ℝ) ^ (blockSteps s m) := by
    positivity
  have hrhs :
      (1 / (6 * (a_0 : ℝ) + 2)) * (2 / 3 : ℝ) ^ (blockSteps s m) =
        (2 : ℝ) ^ (blockSteps s m) /
          ((6 * (a_0 : ℝ) + 2) * (3 : ℝ) ^ (blockSteps s m)) := by
    rw [div_pow, div_mul_div_comm, one_mul]
  rw [hrhs, div_le_div_iff₀ hum_real_pos hden_pos]
  nlinarith

/-! ## 4. Exponential Weil Height Lower Bound & Small-`u` Giant-Block Forcing -/

/-- **Exponential Weil Height Growth of `u(m)` (`exponential_height_growth_of_u`)**:
Dividing `one_step_unit_sum_exponential_squeeze` through by `3^(s m)` (using
`blockSteps s (m + 1) = blockSteps s m + s m`) yields the exact integer lower bound
`3^(blockSteps s m) * (3 * a_0 + 1) < 2^(blockSteps s m) * (2^(s m) * u m)`.
Together with `consecutive_u_coprime` (`Nat.Coprime (u m) (u (m + 1))`), this proves
that whenever `s m` is bounded, the reduced denominator `u m` of the rational
`u (m + 1) / u m` grows exponentially as `(3/2)^(T(m))`. -/
theorem exponential_height_growth_of_u
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    3 ^ (blockSteps s m) * (3 * a_0 + 1) <
      2 ^ (blockSteps s m) * (2 ^ (s m) * u m) := by
  have hsq := one_step_unit_sum_exponential_squeeze hm1 hmK hchain hslack
  have hT : blockSteps s (m + 1) = blockSteps s m + s m := rfl
  rw [hT, pow_add, pow_add] at hsq
  have hmul :
      3 ^ (s m) * (3 ^ (blockSteps s m) * (3 * a_0 + 1)) <
        3 ^ (s m) * (2 ^ (blockSteps s m) * (2 ^ (s m) * u m)) := by
    linarith
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- **Bounded-Block Exponential Lower Bound on `u(m)` (`bounded_block_u_exponential_lower_bound`)**:
If `s m ≤ c`, then `3^(blockSteps s m) * (3 * a_0 + 1) < 2^(blockSteps s m + c) * u m`,
and simultaneously `Nat.Coprime (u m) (u (m + 1))`. -/
theorem bounded_block_u_exponential_lower_bound
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m c : ℕ}
    (hm1 : 1 ≤ m) (hm1K : m + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) (hsc : s m ≤ c) :
    3 ^ (blockSteps s m) * (3 * a_0 + 1) <
        2 ^ (blockSteps s m + c) * u m ∧
      Nat.Coprime (u m) (u (m + 1)) := by
  refine ⟨?_, consecutive_u_coprime hm1K hchain⟩
  have hgrow := exponential_height_growth_of_u hm1 (by omega) hchain hslack
  have hpow : 2 ^ (s m) ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hsc
  have hle :
      2 ^ (blockSteps s m) * (2 ^ (s m) * u m) ≤
        2 ^ (blockSteps s m + c) * u m := by
    rw [pow_add, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
  exact lt_of_lt_of_le hgrow hle

/-- **Small-`u(m)` Giant-Block Forcing (`small_u_forces_giant_block`)**:
Conversely, if `u m ≤ U` at any block `m ≥ 1` with `0 < integerSlack s m`, then
`3^(blockSteps s m) * (3 * a_0 + 1) < 2^(blockSteps s m + s m) * U`,
forcing `2^(s m) * U` to exceed `(3/2)^(T(m)) * (3 * a_0 + 1)`. -/
theorem small_u_forces_giant_block
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m U : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) (huU : u m ≤ U) :
    3 ^ (blockSteps s m) * (3 * a_0 + 1) <
      2 ^ (blockSteps s m + s m) * U := by
  have hgrow := exponential_height_growth_of_u hm1 hmK hchain hslack
  have hle :
      2 ^ (blockSteps s m) * (2 ^ (s m) * u m) ≤
        2 ^ (blockSteps s m + s m) * U := by
    rw [pow_add, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ huU)
  exact lt_of_lt_of_le hgrow hle

/-! ## 5. Linear Forms in Logarithms: Exact Bounds via `Real.log` -/

/-- **One-Step Linear Form in Logarithms Squeeze (`one_step_linear_log_form_squeeze`)**:
Taking `Real.log` of the ratio `R = (2^(s (m + 1)) * u (m + 1)) / (3^(s m) * u m)` and
using `0 < R - 1 → 0 < Real.log R` and `Real.log R ≤ R - 1`, we obtain the explicit
3-logarithm linear form bound:
`0 < (s (m + 1) : ℝ) * Real.log 2 - (s m : ℝ) * Real.log 3 + Real.log ((u (m + 1) : ℝ) / (u m : ℝ))`
and
`(s (m + 1) : ℝ) * Real.log 2 - (s m : ℝ) * Real.log 3 + Real.log ((u (m + 1) : ℝ) / (u m : ℝ)) <
  (1 / (3 * a_0 + 1 : ℝ)) * (2 / 3 : ℝ)^(blockSteps s (m + 1))`. -/
theorem one_step_linear_log_form_squeeze
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hm1K : m + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    0 < (s (m + 1) : ℝ) * Real.log 2 - (s m : ℝ) * Real.log 3 +
          Real.log ((u (m + 1) : ℝ) / (u m : ℝ)) ∧
      (s (m + 1) : ℝ) * Real.log 2 - (s m : ℝ) * Real.log 3 +
          Real.log ((u (m + 1) : ℝ) / (u m : ℝ)) <
        (1 / (3 * (a_0 : ℝ) + 1)) * (2 / 3 : ℝ) ^ (blockSteps s (m + 1)) := by
  have hrel := one_step_relative_gap_lt_two_thirds_pow hm1 hm1K hchain hslack
  rcases hchain m (by omega) with ⟨_, hum_odd, _⟩
  rcases hchain (m + 1) hm1K with ⟨_, hum1_odd, _⟩
  have hum_pos : (0 : ℝ) < (u m : ℝ) := by
    have : 0 < u m := by omega
    exact_mod_cast this
  have hum1_pos : (0 : ℝ) < (u (m + 1) : ℝ) := by
    have : 0 < u (m + 1) := by omega
    exact_mod_cast this
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (s (m + 1)) := pow_pos (by norm_num) _
  have h3_pos : (0 : ℝ) < (3 : ℝ) ^ (s m) := pow_pos (by norm_num) _
  set R : ℝ :=
    ((2 ^ (s (m + 1)) * u (m + 1) : ℕ) : ℝ) /
      ((3 ^ (s m) * u m : ℕ) : ℝ)
  have hR_gt_one : 1 < R := by linarith [hrel.1]
  have hR_pos : 0 < R := by linarith
  have hlog_pos : 0 < Real.log R := Real.log_pos hR_gt_one
  have hlog_le : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos hR_pos
  have hlog_eq :
      Real.log R =
        (s (m + 1) : ℝ) * Real.log 2 - (s m : ℝ) * Real.log 3 +
          Real.log ((u (m + 1) : ℝ) / (u m : ℝ)) := by
    change Real.log (((2 ^ (s (m + 1)) * u (m + 1) : ℕ) : ℝ) / ((3 ^ (s m) * u m : ℕ) : ℝ)) = _
    push_cast
    rw [Real.log_div (ne_of_gt (mul_pos h2_pos hum1_pos)) (ne_of_gt (mul_pos h3_pos hum_pos)),
      Real.log_mul (ne_of_gt h2_pos) (ne_of_gt hum1_pos),
      Real.log_mul (ne_of_gt h3_pos) (ne_of_gt hum_pos),
      Real.log_pow, Real.log_pow,
      Real.log_div (ne_of_gt hum1_pos) (ne_of_gt hum_pos)]
    ring
  rw [← hlog_eq]
  exact ⟨hlog_pos, lt_of_le_of_lt hlog_le hrel.2⟩

/-- **Sub-Ceiling Global Linear Form in Logarithms Squeeze
(`sub_ceiling_global_linear_log_form_squeeze`)**:
In any sub-ceiling phase (`0 < integerSlack s m ≤ 2^(blockSteps s m)`), the global
3-logarithm linear form satisfies:
`0 < (blockSteps s m + 1 : ℝ) * Real.log 3 - (blockSteps s (m + 1) + 1 : ℝ) * Real.log 2 +
  Real.log ((2 * a_0 + 1 : ℝ) / (u m : ℝ))`
and is bounded above by `(1 / (6 * a_0 + 2 : ℝ)) * (2 / 3 : ℝ)^(blockSteps s m)`. -/
theorem sub_ceiling_global_linear_log_form_squeeze
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hle : integerSlack s m ≤ (2 : ℤ) ^ (blockSteps s m)) :
    0 < ((blockSteps s m + 1 : ℕ) : ℝ) * Real.log 3 -
          ((blockSteps s (m + 1) + 1 : ℕ) : ℝ) * Real.log 2 +
          Real.log (((2 * a_0 + 1 : ℕ) : ℝ) / (u m : ℝ)) ∧
      ((blockSteps s m + 1 : ℕ) : ℝ) * Real.log 3 -
          ((blockSteps s (m + 1) + 1 : ℕ) : ℝ) * Real.log 2 +
          Real.log (((2 * a_0 + 1 : ℕ) : ℝ) / (u m : ℝ)) ≤
        (1 / (6 * (a_0 : ℝ) + 2)) * (2 / 3 : ℝ) ^ (blockSteps s m) := by
  have hrel := sub_ceiling_global_exponential_squeeze hm1 hmK hchain hpos hle
  rcases hchain m hmK with ⟨_, hum_odd, _⟩
  have hum_pos : (0 : ℝ) < (u m : ℝ) := by
    have : 0 < u m := by omega
    exact_mod_cast this
  have ha0_pos : (0 : ℝ) < 2 * (a_0 : ℝ) + 1 := by positivity
  have h3_pos : (0 : ℝ) < (3 : ℝ) ^ (blockSteps s m + 1) := pow_pos (by norm_num) _
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (blockSteps s (m + 1) + 1) := pow_pos (by norm_num) _
  set R : ℝ :=
    ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) /
      ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ)
  have hR_gt_one : 1 < R := by linarith [hrel.1]
  have hR_pos : 0 < R := by linarith
  have hlog_pos : 0 < Real.log R := Real.log_pos hR_gt_one
  have hlog_le : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos hR_pos
  have hlog_eq :
      Real.log R =
        ((blockSteps s m + 1 : ℕ) : ℝ) * Real.log 3 -
          ((blockSteps s (m + 1) + 1 : ℕ) : ℝ) * Real.log 2 +
          Real.log (((2 * a_0 + 1 : ℕ) : ℝ) / (u m : ℝ)) := by
    change Real.log (((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) /
      ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ)) = _
    push_cast
    rw [Real.log_div (ne_of_gt (mul_pos h3_pos ha0_pos))
        (ne_of_gt (mul_pos h2_pos hum_pos)),
      Real.log_mul (ne_of_gt h3_pos) (ne_of_gt ha0_pos),
      Real.log_mul (ne_of_gt h2_pos) (ne_of_gt hum_pos),
      Real.log_pow, Real.log_pow,
      Real.log_div (ne_of_gt ha0_pos) (ne_of_gt hum_pos)]
    push_cast
    ring
  rw [← hlog_eq]
  exact ⟨hlog_pos, le_trans hlog_le hrel.2⟩

end Mahler.BakerMatveev
