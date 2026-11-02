import ConstantRungFiniteRunBoundAndKneading33

/-!
# Multi-Period $(p, q, A_p)$ Closed Form, Strict Aperiodicity of All Sub-Ceiling Trajectories & 36-Block ($T_{36} = 179$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 14 / 20 (Part XXIX, Sections C2.O14.1–C2.O14.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O14.1 (Inner Loop 1 / 5) — Multi-Period Renewal Numerator Identity $(3^q - 2^q) A_{0, R p} = A_p (3^{q R} - 2^{q R})$
   (`repeated_period_renewalNumerator_closed_form`)**:
   - For any `p, q, A_p, R : ℕ` and any sequence `s' : ℕ → ℕ` such that every $p$-block window
     `w r t = s' (r * p + t)` ($r < R$) satisfies `blockSteps (w r) p = q` and
     `renewalNumerator (w r) p = A_p`:
     `blockSteps s' (R * p) = q * R` and
     `(3 ^ q - 2 ^ q) * renewalNumerator s' (R * p) = A_p * (3 ^ (q * R) - 2 ^ (q * R))`.

2. **Section C2.O14.2 (Inner Loop 2 / 5) — Universal Closed Form for $\Sigma_{N + R p}$ and $\widehat{\Sigma}_{N + R p}$ Across $R$ Periods
   (`universal_periodic_tail_from_step_closed_form`)**:
   - Under the same $R$-period hypothesis starting at step `N`:
     - `blockSteps s (N + R * p) = T_N + q * R`,
     - `((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) =
         (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) +
           (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * R)`, and
     - `((3 : ℤ) ^ q - (2 : ℤ) ^ q) * centeredRenewalSlack s (N + R * p) =
         (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) -
           ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * R)`.

3. **Section C2.O14.3 (Inner Loop 3 / 5) — Repelling Periodic Fixed-Point Non-Vanishing & Strict Aperiodicity ($q R < 2 T_N + 3 q + 2$)
   (`no_subCeiling_periodic_tail_exceeds_horizon`)**:
   - Whenever `renewalIntSlack s N % 2 = 1` and `1 ≤ q`,
     `((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s N ≠ (2 : ℤ) ^ (blockSteps s N + 1) * (A_p : ℤ)`.
   - Moreover, if `A_p ≤ 3 ^ q` and `2 * blockSteps s N + 3 * q + 2 ≤ q * R`, then
     `renewalIntSlack s (N + R * p) < 0 ∨ 0 < centeredRenewalSlack s (N + R * p)` and
     `¬ (0 < renewalIntSlack s (N + R * p) ∧ centeredRenewalSlack s (N + R * p) < 0)`.

4. **Sections C2.O14.4 & C2.O14.5 (Inner Loops 4–5 / 5) — Certification of Blocks 34, 35, and 36 ($s_{33} = 6, s_{34} = 6, s_{35} = 3$, $T_{36} = 179$) & Mod-$2^{180}$ Uniqueness
   (`thirtyfour_to_thirtysix_block_kneading_corridor_and_two_pow_180_uniqueness`)**:
   - Certifies blocks 34–36 ($T_{36} = 179$) and proves $2^{180} \mid (b_2 - b_1)$ and $2^{180} \le b_2$
     for any two seeds sharing the 36-block prefix.
-/

namespace Mahler.PeriodicTailExclusionAndKneading36

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.SparseDefectCocycle
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection
open Mahler.BetaShiftDictionary
open Mahler.GeneralizedDefectAllRung
open Mahler.BoundedOddPartAndSieve
open Mahler.AllRungConstantOfMotion
open Mahler.ArchimedeanPinningAndRenewal
open Mahler.ConsecutiveGCDAndPillai
open Mahler.OctadicDeathAnatomy
open Mahler.RenewalCocycleAndSandwich
open Mahler.AllBlockRepeatedWindow
open Mahler.SignedCocycleRenewalBridge
open Mahler.MultiStepQuotientAndFermatGCD
open Mahler.RecoveryCascadeClosedForms
open Mahler.TwoAdicRecoveryPruningTree
open Mahler.SixBlockKneadingAndFiftyMillion
open Mahler.StrictEndpointAndSlackGrowth
open Mahler.InfiniteRenewalEquivalence
open Mahler.CanonicalOddBlockSynthesis
open Mahler.AllBlockConstantOfMotion
open Mahler.CenteredRenewalSlack
open Mahler.UniqueSubCeilingCorridor
open Mahler.UniversalSubCeilingNonBranching
open Mahler.RungShiftAndExistsUniqueKneading
open Mahler.UniversalPostTwoAndKneading13
open Mahler.ExtraBitBackwardAndKneading15
open Mahler.DyadicTriadicAndKneading18
open Mahler.ExactValuationAndKneading21
open Mahler.UniversalTwoRungAndKneading24
open Mahler.UniversalAllThreeRunAndKneading27
open Mahler.UniversalConstantRungAndKneading30
open Mahler.ConstantRungBoundAndKneading33

/-! ## 1. Section C2.O14.1: Multi-Period Renewal Numerator Identity $(3^q - 2^q) A_{0, R p} = A_p (3^{q R} - 2^{q R})$ -/

/-- **Multi-Period Renewal Numerator Identity $(3^q - 2^q) A_{0, R p} = A_p (3^{q R} - 2^{q R})$
(`repeated_period_renewalNumerator_closed_form`, Section C2.O14.1)**:
For any `p, q, A_p, R : ℕ` and any sequence `s' : ℕ → ℕ` such that for all `r < R`,
`blockSteps (fun t => s' (r * p + t)) p = q` and
`renewalNumerator (fun t => s' (r * p + t)) p = A_p`:
1. `blockSteps s' (R * p) = q * R`, and
2. `(3 ^ q - 2 ^ q) * renewalNumerator s' (R * p) = A_p * (3 ^ (q * R) - 2 ^ (q * R))`. -/
theorem repeated_period_renewalNumerator_closed_form
    {s' : ℕ → ℕ} {p q A_p R : ℕ}
    (hq : ∀ r < R, blockSteps (fun t => s' (r * p + t)) p = q)
    (hA : ∀ r < R, renewalNumerator (fun t => s' (r * p + t)) p = A_p) :
    blockSteps s' (R * p) = q * R ∧
      (3 ^ q - 2 ^ q) * renewalNumerator s' (R * p) = A_p * (3 ^ (q * R) - 2 ^ (q * R)) := by
  induction R with
  | zero =>
      simp [blockSteps, renewalNumerator]
  | succ R ih =>
      rcases ih (fun r hr => hq r (by omega)) (fun r hr => hA r (by omega)) with ⟨hT_R, hA_R⟩
      have hmul_succ : (R + 1) * p = R * p + p := by ring
      have hsh := blockSteps_add_shift s' (R * p) p
      have hq_R := hq R (by omega)
      have hA_R_win := hA R (by omega)
      have hT_succ : blockSteps s' ((R + 1) * p) = q * (R + 1) := by
        rw [hmul_succ, hsh, hT_R, hq_R]
        ring
      refine ⟨hT_succ, ?_⟩
      have hcomp := renewalNumerator_cocycle_composition s' (R * p) p
      change renewalNumerator s' (R * p + p) =
        3 ^ (blockSteps (fun t => s' (R * p + t)) p) * renewalNumerator s' (R * p) +
          2 ^ (blockSteps s' (R * p)) * renewalNumerator (fun t => s' (R * p + t)) p at hcomp
      rw [hq_R, hT_R, hA_R_win] at hcomp
      have hstep_mul :
          (3 ^ q - 2 ^ q) * renewalNumerator s' ((R + 1) * p) =
            3 ^ q * ((3 ^ q - 2 ^ q) * renewalNumerator s' (R * p)) +
              (3 ^ q - 2 ^ q) * (2 ^ (q * R) * A_p) := by
        rw [hmul_succ, hcomp]
        ring
      rw [hstep_mul, hA_R]
      have hle_q : 2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by decide) q
      have hle_qR : 2 ^ (q * R) ≤ 3 ^ (q * R) := Nat.pow_le_pow_left (by decide) (q * R)
      have hle_qR1 : 2 ^ (q * (R + 1)) ≤ 3 ^ (q * (R + 1)) :=
        Nat.pow_le_pow_left (by decide) (q * (R + 1))
      zify [hle_q, hle_qR, hle_qR1]
      rw [show q * (R + 1) = q * R + q by ring]
      simp only [pow_add]
      ring

/-! ## 2. Section C2.O14.2: Universal Closed Form for $\Sigma_{N + R p}$ and $\widehat{\Sigma}_{N + R p}$ Across $R$ Periods -/

/-- **Universal Closed Form for $\Sigma_{N + R p}$ and $\widehat{\Sigma}_{N + R p}$ Across $R$ Periods
(`universal_periodic_tail_from_step_closed_form`, Section C2.O14.2)**:
For any sequence `s : ℕ → ℕ` and `N, p, q, A_p, R : ℕ` such that for all `r < R`,
`blockSteps (fun t => s (N + (r * p + t))) p = q` and
`renewalNumerator (fun t => s (N + (r * p + t))) p = A_p`, setting
`T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
1. `blockSteps s (N + R * p) = T_N + q * R`,
2. `((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) =
     (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) +
       (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * R)`, and
3. `((3 : ℤ) ^ q - (2 : ℤ) ^ q) * centeredRenewalSlack s (N + R * p) =
     (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) -
       ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * R)`. -/
theorem universal_periodic_tail_from_step_closed_form
    {s : ℕ → ℕ} {N p q A_p R : ℕ}
    (hq : ∀ r < R, blockSteps (fun t => s (N + (r * p + t))) p = q)
    (hA : ∀ r < R, renewalNumerator (fun t => s (N + (r * p + t))) p = A_p) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    blockSteps s (N + R * p) = T_N + q * R ∧
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) =
        (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) +
          (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * R) ∧
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * centeredRenewalSlack s (N + R * p) =
        (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) -
          ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * R) := by
  intro T_N S_N
  set s' := fun t => s (N + t)
  have hcf := repeated_period_renewalNumerator_closed_form (s' := s') hq hA
  have hd : blockSteps s' (R * p) = q * R := hcf.1
  have hAR : (3 ^ q - 2 ^ q) * renewalNumerator s' (R * p) = A_p * (3 ^ (q * R) - 2 ^ (q * R)) := hcf.2
  have hsh := blockSteps_add_shift s N (R * p)
  have hT_NR : blockSteps s (N + R * p) = T_N + q * R := by
    change blockSteps s (N + R * p) = T_N + blockSteps s' (R * p) at hsh
    rw [hsh, hd]
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 N (R * p)).2.2
  change renewalIntSlack s (N + R * p) =
    (3 : ℤ) ^ (blockSteps s' (R * p)) * S_N - (2 : ℤ) ^ (T_N + 1) * (renewalNumerator s' (R * p) : ℤ) at hcoc
  have hle_q : 2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by decide) q
  have hle_qR : 2 ^ (q * R) ≤ 3 ^ (q * R) := Nat.pow_le_pow_left (by decide) (q * R)
  have hAR_z :
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * (renewalNumerator s' (R * p) : ℤ) =
        (A_p : ℤ) * ((3 : ℤ) ^ (q * R) - (2 : ℤ) ^ (q * R)) := by
    zify [hle_q, hle_qR] at hAR
    exact_mod_cast hAR
  have hS_NR :
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) =
        (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) +
          (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * R) := by
    calc
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p)
          = ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * ((3 : ℤ) ^ (q * R) * S_N) -
              (2 : ℤ) ^ (T_N + 1) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * (renewalNumerator s' (R * p) : ℤ)) := by
            rw [hcoc, hd]
            ring
      _ = ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * ((3 : ℤ) ^ (q * R) * S_N) -
              (2 : ℤ) ^ (T_N + 1) * ((A_p : ℤ) * ((3 : ℤ) ^ (q * R) - (2 : ℤ) ^ (q * R))) := by
            rw [hAR_z]
      _ = (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) +
              (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * R) := by
            simp only [pow_add, pow_succ]
            ring
  have hC_NR :
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * centeredRenewalSlack s (N + R * p) =
        (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) -
          ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * R) := by
    have hC_def :
        centeredRenewalSlack s (N + R * p) =
          renewalIntSlack s (N + R * p) - (2 : ℤ) ^ (blockSteps s (N + R * p)) := rfl
    rw [hC_def, hT_NR]
    calc
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * (renewalIntSlack s (N + R * p) - (2 : ℤ) ^ (T_N + q * R))
          = ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) -
              ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * (2 : ℤ) ^ (T_N + q * R) := by ring
      _ = (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) -
              ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * R) := by
            rw [hS_NR]
            simp only [pow_add, pow_succ]
            ring
  exact ⟨hT_NR, hS_NR, hC_NR⟩

/-! ## 3. Section C2.O14.3: Repelling Periodic Fixed-Point Non-Vanishing & Strict Aperiodicity -/

/-- **Repelling Periodic Fixed-Point Non-Vanishing & Strict Aperiodicity ($q R < 2 T_N + 3 q + 2$)
(`no_subCeiling_periodic_tail_exceeds_horizon`, Section C2.O14.3)**:
For any sequence `s : ℕ → ℕ` and `N, p, q, A_p, R : ℕ` with `renewalIntSlack s N % 2 = 1`, `1 ≤ q`,
`A_p ≤ 3 ^ q`, `2 * blockSteps s N + 3 * q + 2 ≤ q * R`, and
`∀ r < R, blockSteps (fun t => s (N + (r * p + t))) p = q ∧ renewalNumerator (fun t => s (N + (r * p + t))) p = A_p`:
1. `((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s N ≠ (2 : ℤ) ^ (blockSteps s N + 1) * (A_p : ℤ)`,
2. `renewalIntSlack s (N + R * p) < 0 ∨ 0 < centeredRenewalSlack s (N + R * p)`, and
3. `¬ (0 < renewalIntSlack s (N + R * p) ∧ centeredRenewalSlack s (N + R * p) < 0)`. -/
theorem no_subCeiling_periodic_tail_exceeds_horizon
    {s : ℕ → ℕ} {N p q A_p R : ℕ}
    (hodd : renewalIntSlack s N % 2 = 1) (hq1 : 1 ≤ q)
    (hAp_le : A_p ≤ 3 ^ q)
    (hhor : 2 * blockSteps s N + 3 * q + 2 ≤ q * R)
    (hq : ∀ r < R, blockSteps (fun t => s (N + (r * p + t))) p = q)
    (hA : ∀ r < R, renewalNumerator (fun t => s (N + (r * p + t))) p = A_p) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N ≠ (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ) ∧
      (renewalIntSlack s (N + R * p) < 0 ∨ 0 < centeredRenewalSlack s (N + R * p)) ∧
      ¬ (0 < renewalIntSlack s (N + R * p) ∧ centeredRenewalSlack s (N + R * p) < 0) := by
  intro T_N S_N
  have hcf := universal_periodic_tail_from_step_closed_form hq hA
  have hS_NR :
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) =
        (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) +
          (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * R) := hcf.2.1
  have hC_NR :
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * centeredRenewalSlack s (N + R * p) =
        (3 : ℤ) ^ (q * R) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) -
          ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * R) := hcf.2.2
  clear hcf
  have hne : ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N ≠ (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ) := by
    have h3_odd : ((3 : ℤ) ^ q) % 2 = 1 := int_three_pow_mod_two_eq_one q
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, q = j + 1 := ⟨q - 1, by omega⟩
    have h2_even : ((2 : ℤ) ^ (j + 1)) % 2 = 0 := by rw [pow_succ]; omega
    have hdiff_odd : (((3 : ℤ) ^ (j + 1) - (2 : ℤ) ^ (j + 1)) % 2) = 1 := by omega
    have hlhs_odd : ((((3 : ℤ) ^ (j + 1) - (2 : ℤ) ^ (j + 1)) * S_N) % 2) = 1 := by
      rw [Int.mul_emod, hdiff_odd, hodd]
      decide
    have hrhs_even : (((2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) % 2) = 0 := by
      have hmul2 : (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ) = 2 * ((2 : ℤ) ^ T_N * (A_p : ℤ)) := by
        rw [pow_succ]
        ring
      rw [hmul2]
      omega
    intro heq
    rw [heq] at hlhs_odd
    omega
  have hlt_q := two_pow_lt_three_pow_of_one_le hq1
  have hMq_pos : 0 < (3 : ℤ) ^ q - (2 : ℤ) ^ q := by omega
  have hR_pos : 1 ≤ R := by
    by_contra hR0
    have hR_eq : R = 0 := by omega
    rw [hR_eq, Nat.mul_zero] at hhor
    omega
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, R = 1 + k := ⟨R - 1, by omega⟩
  have hdom := two_mul_two_pow_add_lt_three_pow_of_two_mul_add_two_le
    (A := T_N + q) (B := q * k) (by
      have hqk : q * (1 + k) = q + q * k := by ring
      omega)
  have h2_lt_3qk : (2 : ℤ) ^ (T_N + 1 + q * (1 + k)) < (3 : ℤ) ^ (q * k) := by
    calc
      (2 : ℤ) ^ (T_N + 1 + q * (1 + k))
          = 2 * (2 : ℤ) ^ ((T_N + q) + q * k) := by
            rw [show T_N + 1 + q * (1 + k) = ((T_N + q) + q * k) + 1 by ring, pow_succ]
            ring
      _ < (3 : ℤ) ^ (q * k) := hdom
  have hAp_z_le : (A_p : ℤ) ≤ (3 : ℤ) ^ q := by exact_mod_cast hAp_le
  have h2_pos1 : 0 < (2 : ℤ) ^ (T_N + 1 + q * (1 + k)) := by positivity
  have h3q_pos : 0 < (3 : ℤ) ^ q := by positivity
  have hterm1_lt :
      (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * (1 + k)) < (3 : ℤ) ^ (q * (1 + k)) := by
    calc
      (A_p : ℤ) * (2 : ℤ) ^ (T_N + 1 + q * (1 + k))
          ≤ (3 : ℤ) ^ q * (2 : ℤ) ^ (T_N + 1 + q * (1 + k)) :=
            mul_le_mul_of_nonneg_right hAp_z_le (le_of_lt h2_pos1)
      _ < (3 : ℤ) ^ q * (3 : ℤ) ^ (q * k) :=
            mul_lt_mul_of_pos_left h2_lt_3qk h3q_pos
      _ = (3 : ℤ) ^ (q * (1 + k)) := by
            rw [show q * (1 + k) = q + q * k by ring, pow_add]
  have h2_pos2 : 0 < (2 : ℤ) ^ (T_N + q * (1 + k)) := by positivity
  have h2q_pos : 0 < (2 : ℤ) ^ q := by positivity
  have hAp_nonneg : 0 ≤ (A_p : ℤ) := by positivity
  have hcoeff_lt : (3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ) < (3 : ℤ) ^ q := by omega
  have h2_lt_3qk' : (2 : ℤ) ^ (T_N + q * (1 + k)) < (3 : ℤ) ^ (q * k) := by
    have hle_step : (2 : ℤ) ^ (T_N + q * (1 + k)) ≤ (2 : ℤ) ^ (T_N + 1 + q * (1 + k)) := by
      rw [show T_N + 1 + q * (1 + k) = (T_N + q * (1 + k)) + 1 by omega, pow_succ]
      omega
    omega
  have hterm2_lt :
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * (1 + k)) <
        (3 : ℤ) ^ (q * (1 + k)) := by
    calc
      ((3 : ℤ) ^ q - (2 : ℤ) ^ q - 2 * (A_p : ℤ)) * (2 : ℤ) ^ (T_N + q * (1 + k))
          < (3 : ℤ) ^ q * (2 : ℤ) ^ (T_N + q * (1 + k)) :=
            mul_lt_mul_of_pos_right hcoeff_lt h2_pos2
      _ < (3 : ℤ) ^ q * (3 : ℤ) ^ (q * k) :=
            mul_lt_mul_of_pos_left h2_lt_3qk' h3q_pos
      _ = (3 : ℤ) ^ (q * (1 + k)) := by
            rw [show q * (1 + k) = q + q * k by ring, pow_add]
  have h3qR_nonneg : 0 ≤ (3 : ℤ) ^ (q * (1 + k)) := by positivity
  have hor : renewalIntSlack s (N + (1 + k) * p) < 0 ∨ 0 < centeredRenewalSlack s (N + (1 + k) * p) := by
    rcases lt_or_gt_of_ne hne with hbelow | habove
    · left
      have hle_neg1 : ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ) ≤ -1 := by omega
      have hmul_le :
          (3 : ℤ) ^ (q * (1 + k)) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) ≤
            (3 : ℤ) ^ (q * (1 + k)) * (-1) :=
        mul_le_mul_of_nonneg_left hle_neg1 h3qR_nonneg
      have hS_mul_neg : ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + (1 + k) * p) < 0 := by omega
      by_contra hge
      push_neg at hge
      have hnonneg : 0 ≤ ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + (1 + k) * p) :=
        mul_nonneg (le_of_lt hMq_pos) hge
      omega
    · right
      have hge1 : 1 ≤ ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ) := by omega
      have hmul_ge :
          (3 : ℤ) ^ (q * (1 + k)) * 1 ≤
            (3 : ℤ) ^ (q * (1 + k)) * (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * S_N - (2 : ℤ) ^ (T_N + 1) * (A_p : ℤ)) :=
        mul_le_mul_of_nonneg_left hge1 h3qR_nonneg
      have hC_mul_pos : 0 < ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * centeredRenewalSlack s (N + (1 + k) * p) := by omega
      exact pos_of_mul_pos_right hC_mul_pos (le_of_lt hMq_pos)
  refine ⟨hne, hor, ?_⟩
  rintro ⟨hpos, hneg⟩
  rcases hor with h1 | h2 <;> omega

/-! ## 4. Sections C2.O14.4 & C2.O14.5: Certification of Blocks 34, 35, and 36 ($T_{36} = 179$) & Mod-$2^{180}$ Uniqueness -/

/-- **Certification of the 34th ($s_{33} = 6$), 35th ($s_{34} = 6$), and 36th ($s_{35} = 3$) Kneading Rungs & Mod-$2^{180}$ Uniqueness
(`thirtyfour_to_thirtysix_block_kneading_corridor_and_two_pow_180_uniqueness`, Sections C2.O14.4–C2.O14.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 33-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4)$:
1. `(0 < renewalIntSlack s 34 ∧ centeredRenewalSlack s 34 < 0) ↔ s 33 = 6`,
2. When `s 33 = 6`: `blockSteps s 34 = 170`,
   `renewalIntSlack s 34 = 372882396470759673660545147138584282519263946694689`,
   `centeredRenewalSlack s 34 = -1123695280156084914580028121562889529608410977312735`, and
   `(0 < renewalIntSlack s 35 ∧ centeredRenewalSlack s 35 < 0) ↔ s 34 = 6`,
3. When `s 33 = 6` and `s 34 = 6`: `blockSteps s 35 = 176`,
   `renewalIntSlack s 35 = 80269324418947694803744033870239294004201026867478009`,
   `centeredRenewalSlack s 35 = -15511646885170358843652655326655029971970168268997127`, and
   `(0 < renewalIntSlack s 36 ∧ centeredRenewalSlack s 36 < 0) ↔ s 35 = 3`,
4. When `s 33 = 6`, `s 34 = 6`, and `s 35 = 3`: `blockSteps s 36 = 179`,
   `renewalIntSlack s 36 = 634776218445698901342741887346151754494688603238304067`,
   `centeredRenewalSlack s 36 = -131471551987245527836431626229002837314680957853497021`, and any
   two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 36` satisfy `2 ^ 180 ∣ (b₂ - b₁)` and `2 ^ 180 ≤ b₂`. -/
theorem thirtyfour_to_thirtysix_block_kneading_corridor_and_two_pow_180_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3)
    (hs24 : s 24 = 5) (hs25 : s 25 = 8) (hs26 : s 26 = 8) (hs27 : s 27 = 3)
    (hs28 : s 28 = 6) (hs29 : s 29 = 4) (hs30 : s 30 = 5) (hs31 : s 31 = 3)
    (hs32 : s 32 = 4) :
    ((0 < renewalIntSlack s 34 ∧ centeredRenewalSlack s 34 < 0) ↔ s 33 = 6) ∧
      (s 33 = 6 →
        blockSteps s 34 = 170 ∧
          renewalIntSlack s 34 = 372882396470759673660545147138584282519263946694689 ∧
          centeredRenewalSlack s 34 = -1123695280156084914580028121562889529608410977312735 ∧
          ((0 < renewalIntSlack s 35 ∧ centeredRenewalSlack s 35 < 0) ↔ s 34 = 6)) ∧
      (s 33 = 6 → s 34 = 6 →
        blockSteps s 35 = 176 ∧
          renewalIntSlack s 35 = 80269324418947694803744033870239294004201026867478009 ∧
          centeredRenewalSlack s 35 = -15511646885170358843652655326655029971970168268997127 ∧
          ((0 < renewalIntSlack s 36 ∧ centeredRenewalSlack s 36 < 0) ↔ s 35 = 3)) ∧
      (s 33 = 6 → s 34 = 6 → s 35 = 3 →
        blockSteps s 36 = 179 ∧
          renewalIntSlack s 36 = 634776218445698901342741887346151754494688603238304067 ∧
          centeredRenewalSlack s 36 = -131471551987245527836431626229002837314680957853497021 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 36 →
              ValidBlockChain b₂ s u₂ 36 →
                2 ^ 180 ∣ (b₂ - b₁) ∧ 2 ^ 180 ≤ b₂)) := by
  have hprev :=
    (thirtyone_to_thirtythree_block_kneading_corridor_and_two_pow_165_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29).2.2.2 hs30 hs31 hs32
  have hT33 : blockSteps s 33 = 164 := hprev.1
  have hS33 : renewalIntSlack s 33 = 4617335733504045061922759512402650077880128662153 := hprev.2.1
  have hstep33 := subCeiling_step_sandwich_iff s 33
  have hiff33 :
      (0 < renewalIntSlack s 34 ∧ centeredRenewalSlack s 34 < 0) ↔ s 33 = 6 := by
    have hsand33 := hstep33.2.2
    rw [hT33, hS33] at hsand33
    exact hsand33.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 4617335733504045061922759512402650077880128662153) (T_N := 164) (s_star := 6)
      (by norm_num) (by norm_num) (s 33)).1
  have h34_vals :
      s 33 = 6 →
        blockSteps s 34 = 170 ∧
          renewalIntSlack s 34 = 372882396470759673660545147138584282519263946694689 ∧
          centeredRenewalSlack s 34 = -1123695280156084914580028121562889529608410977312735 := by
    intro hs33
    have hT34 : blockSteps s 34 = 170 := by
      change blockSteps s 33 + s 33 = 170
      rw [hT33, hs33]
    have hS34 : renewalIntSlack s 34 = 372882396470759673660545147138584282519263946694689 := by
      have h1 := hstep33.1
      rw [h1, hT33, hS33, hs33]
      norm_num
    have hC34 : centeredRenewalSlack s 34 = -1123695280156084914580028121562889529608410977312735 := by
      have h2 := hstep33.2.1
      rw [h2, hT33, hS33, hs33]
      norm_num
    exact ⟨hT34, hS34, hC34⟩
  have h35_vals :
      s 33 = 6 → s 34 = 6 →
        blockSteps s 35 = 176 ∧
          renewalIntSlack s 35 = 80269324418947694803744033870239294004201026867478009 ∧
          centeredRenewalSlack s 35 = -15511646885170358843652655326655029971970168268997127 := by
    intro hs33 hs34
    obtain ⟨hT34, hS34, _⟩ := h34_vals hs33
    have hstep34 := subCeiling_step_sandwich_iff s 34
    have hT35 : blockSteps s 35 = 176 := by
      change blockSteps s 34 + s 34 = 176
      rw [hT34, hs34]
    have hS35 : renewalIntSlack s 35 = 80269324418947694803744033870239294004201026867478009 := by
      have h1 := hstep34.1
      rw [h1, hT34, hS34, hs34]
      norm_num
    have hC35 : centeredRenewalSlack s 35 = -15511646885170358843652655326655029971970168268997127 := by
      have h2 := hstep34.2.1
      rw [h2, hT34, hS34, hs34]
      norm_num
    exact ⟨hT35, hS35, hC35⟩
  refine ⟨hiff33, ?_, ?_, ?_⟩
  · intro hs33
    obtain ⟨hT34, hS34, hC34⟩ := h34_vals hs33
    have hsand34 := (subCeiling_step_sandwich_iff s 34).2.2
    rw [hT34, hS34] at hsand34
    refine ⟨hT34, hS34, hC34, ?_⟩
    exact hsand34.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 372882396470759673660545147138584282519263946694689) (T_N := 170) (s_star := 6)
      (by norm_num) (by norm_num) (s 34)).1
  · intro hs33 hs34
    obtain ⟨hT35, hS35, hC35⟩ := h35_vals hs33 hs34
    have hsand35 := (subCeiling_step_sandwich_iff s 35).2.2
    rw [hT35, hS35] at hsand35
    refine ⟨hT35, hS35, hC35, ?_⟩
    exact hsand35.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 80269324418947694803744033870239294004201026867478009) (T_N := 176) (s_star := 3)
      (by norm_num) (by norm_num) (s 35)).1
  · intro hs33 hs34 hs35
    obtain ⟨hT35, hS35, _⟩ := h35_vals hs33 hs34
    have hstep35 := subCeiling_step_sandwich_iff s 35
    have hT36 : blockSteps s 36 = 179 := by
      change blockSteps s 35 + s 35 = 179
      rw [hT35, hs35]
    have hS36 : renewalIntSlack s 36 = 634776218445698901342741887346151754494688603238304067 := by
      have h1 := hstep35.1
      rw [h1, hT35, hS35, hs35]
      norm_num
    have hC36 : centeredRenewalSlack s 36 = -131471551987245527836431626229002837314680957853497021 := by
      have h2 := hstep35.2.1
      rw [h2, hT35, hS35, hs35]
      norm_num
    refine ⟨hT36, hS36, hC36, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 36) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 36 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT36] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 180 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.PeriodicTailExclusionAndKneading36
