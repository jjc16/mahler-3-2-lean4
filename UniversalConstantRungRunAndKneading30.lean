import UniversalAllThreeRunBifurcationAndKneading27

/-!
# Universal Constant-Rung $m^j$ Closed Form, General $\rho_*(m) = \frac{2^{m+1}}{3^m - 2^m}$ Bifurcation & 30-Block ($T_{30} = 152$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 12 / 20 (Part XXVII, Sections C2.O12.1–C2.O12.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O12.1 (Inner Loop 1 / 5) — Bellman Equality Case for Any Constant-Rung Segment $m^j$
   (`constant_rung_run_renewalNumerator_closed_form`)**:
   - For any `m, j : ℕ` and any sequence `s' : ℕ → ℕ` with `∀ t < j, s' t = m`:
     `blockSteps s' j = m * j` and
     `(3 ^ m - 2 ^ m) * renewalNumerator s' j = 2 ^ m * (3 ^ (m * j) - 2 ^ (m * j))`.

2. **Section C2.O12.2 (Inner Loop 2 / 5) — Universal Closed Form for $\Sigma_{N+j}$ and $\widehat{\Sigma}_{N+j}$ Across Any $m^j$ Run
   (`universal_constant_rung_run_from_step_closed_form`)**:
   - Whenever `∀ t < j, s (N + t) = m`, setting `T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
     - `blockSteps s (N + j) = T_N + m * j`,
     - `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) =
         (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) +
           (2 : ℤ) ^ (T_N + m + 1 + m * j)`, and
     - `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) =
         (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) -
           ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j)`.

3. **Section C2.O12.3 (Inner Loop 3 / 5) — General Rung-$m$ ($m \ge 3$) Repelling Fixed-Point Bifurcation
   (`constant_rung_run_fixed_point_bifurcation`)**:
   - For `3 ≤ m` and `∀ t < j, s (N + t) = m`, `0 < (3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m` and:
     - Above $\rho_*(m) = \frac{2^{m+1}}{3^m - 2^m}$ (`(2 : ℤ) ^ (T_N + m + 1) < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N`),
       `0 < renewalIntSlack s (N + j)` for all $j$, and `centeredRenewalSlack s (N + j) < 0` iff
       `(3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) <
         ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j)`.
     - Below $\rho_*(m)$ (`((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N < (2 : ℤ) ^ (T_N + m + 1)`),
       `centeredRenewalSlack s (N + j) < 0` for all $j$, and `0 < renewalIntSlack s (N + j)` iff
       `(3 : ℤ) ^ (m * j) * ((2 : ℤ) ^ (T_N + m + 1) - ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N) <
         (2 : ℤ) ^ (T_N + m + 1 + m * j)`.

4. **Sections C2.O12.4 & C2.O12.5 (Inner Loops 4–5 / 5) — Certification of Blocks 28, 29, and 30 ($s_{27} = 3, s_{28} = 6, s_{29} = 4$, $T_{30} = 152$) & Mod-$2^{153}$ Uniqueness
   (`twentyeight_to_thirty_block_kneading_corridor_and_two_pow_153_uniqueness`)**:
   - Crosses the 150-step binary horizon ($T_{30} = 152$) and proves $2^{153} \mid (b_2 - b_1)$
     and $2^{153} \le b_2$ for any two seeds sharing the 30-block prefix.
-/

namespace Mahler.UniversalConstantRungAndKneading30

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

/-! ## 1. Section C2.O12.1: Bellman Equality Case for Any Constant-Rung Segment $m^j$ -/

/-- **Bellman Equality Case for Any Constant-Rung Segment $m^j$
(`constant_rung_run_renewalNumerator_closed_form`, Section C2.O12.1)**:
For any `m, j : ℕ` and any sequence `s' : ℕ → ℕ` with `∀ t < j, s' t = m`:
1. `blockSteps s' j = m * j`, and
2. `(3 ^ m - 2 ^ m) * renewalNumerator s' j = 2 ^ m * (3 ^ (m * j) - 2 ^ (m * j))`. -/
theorem constant_rung_run_renewalNumerator_closed_form
    {s' : ℕ → ℕ} {m j : ℕ} (hm : ∀ t < j, s' t = m) :
    blockSteps s' j = m * j ∧
      (3 ^ m - 2 ^ m) * renewalNumerator s' j = 2 ^ m * (3 ^ (m * j) - 2 ^ (m * j)) := by
  have hd : blockSteps s' j = m * j := by
    induction j with
    | zero => simp [blockSteps]
    | succ j ih =>
        rw [blockSteps, ih (fun t ht => hm t (by omega)), hm j (by omega)]
        ring
  have hlow := renewalNumerator_bellman_lower_sandwich (s := s') (N := j) (H := m)
    (fun t ht => le_of_eq (hm t ht))
  have hupp := renewalNumerator_bellman_upper_sandwich (s := s') (N := j) (L := m)
    (fun t ht => le_of_eq (hm t ht).symm)
  rw [hd] at hlow hupp
  exact ⟨hd, Nat.le_antisymm hupp hlow⟩

/-! ## 2. Section C2.O12.2: Universal Closed Form for $\Sigma_{N+j}$ and $\widehat{\Sigma}_{N+j}$ Across Any $m^j$ Run -/

/-- **Universal Closed Form for $\Sigma_{N+j}$ and $\widehat{\Sigma}_{N+j}$ Across Any $m^j$ Run
(`universal_constant_rung_run_from_step_closed_form`, Section C2.O12.2)**:
For any sequence `s : ℕ → ℕ` and `N, m, j : ℕ` with `∀ t < j, s (N + t) = m`, setting
`T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
1. `blockSteps s (N + j) = T_N + m * j`,
2. `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) =
     (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) +
       (2 : ℤ) ^ (T_N + m + 1 + m * j)`, and
3. `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) =
     (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) -
       ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j)`. -/
theorem universal_constant_rung_run_from_step_closed_form
    {s : ℕ → ℕ} {N m j : ℕ} (hm : ∀ t < j, s (N + t) = m) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    blockSteps s (N + j) = T_N + m * j ∧
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) =
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) +
          (2 : ℤ) ^ (T_N + m + 1 + m * j) ∧
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) =
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) -
          ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j) := by
  intro T_N S_N
  set s' := fun t => s (N + t)
  have hcf := constant_rung_run_renewalNumerator_closed_form (s' := s') hm
  have hd : blockSteps s' j = m * j := hcf.1
  have hAj : (3 ^ m - 2 ^ m) * renewalNumerator s' j = 2 ^ m * (3 ^ (m * j) - 2 ^ (m * j)) := hcf.2
  have hsh := blockSteps_add_shift s N j
  have hT_Nj : blockSteps s (N + j) = T_N + m * j := by
    change blockSteps s (N + j) = T_N + blockSteps s' j at hsh
    rw [hsh, hd]
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 N j).2.2
  change renewalIntSlack s (N + j) =
    (3 : ℤ) ^ (blockSteps s' j) * S_N - (2 : ℤ) ^ (T_N + 1) * (renewalNumerator s' j : ℤ) at hcoc
  have hle_m : 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by decide) m
  have hle_mj : 2 ^ (m * j) ≤ 3 ^ (m * j) := Nat.pow_le_pow_left (by decide) (m * j)
  have hAj_z :
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * (renewalNumerator s' j : ℤ) =
        (2 : ℤ) ^ m * ((3 : ℤ) ^ (m * j) - (2 : ℤ) ^ (m * j)) := by
    zify [hle_m, hle_mj] at hAj
    exact_mod_cast hAj
  have hS_Nj :
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) =
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) +
          (2 : ℤ) ^ (T_N + m + 1 + m * j) := by
    calc
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j)
          = ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * ((3 : ℤ) ^ (m * j) * S_N) -
              (2 : ℤ) ^ (T_N + 1) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * (renewalNumerator s' j : ℤ)) := by
            rw [hcoc, hd]
            ring
      _ = ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * ((3 : ℤ) ^ (m * j) * S_N) -
              (2 : ℤ) ^ (T_N + 1) * ((2 : ℤ) ^ m * ((3 : ℤ) ^ (m * j) - (2 : ℤ) ^ (m * j))) := by
            rw [hAj_z]
      _ = (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) +
              (2 : ℤ) ^ (T_N + m + 1 + m * j) := by
            simp only [pow_add, pow_succ]
            ring
  have hC_Nj :
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) =
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) -
          ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j) := by
    have hC_def : centeredRenewalSlack s (N + j) = renewalIntSlack s (N + j) - (2 : ℤ) ^ (blockSteps s (N + j)) := rfl
    rw [hC_def, hT_Nj]
    calc
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * (renewalIntSlack s (N + j) - (2 : ℤ) ^ (T_N + m * j))
          = ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) -
              ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j) := by ring
      _ = (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) -
              ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j) := by
            rw [hS_Nj]
            simp only [pow_add, pow_succ]
            ring
  exact ⟨hT_Nj, hS_Nj, hC_Nj⟩

/-! ## 3. Section C2.O12.3: General Rung-$m$ ($m \ge 3$) Repelling Fixed-Point Bifurcation -/

/-- Auxiliary dominance lemma: `3 * (2 : ℤ) ^ m < (3 : ℤ) ^ m` for every `m ≥ 3`. -/
theorem three_mul_two_pow_lt_three_pow_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    3 * (2 : ℤ) ^ m < (3 : ℤ) ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 3 := ⟨m - 3, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
      have h1 : 3 * (2 : ℤ) ^ (k + 1 + 3) = 2 * (3 * (2 : ℤ) ^ (k + 3)) := by
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
        ring
      have h2 : (3 : ℤ) ^ (k + 1 + 3) = 3 * (3 : ℤ) ^ (k + 3) := by
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
        ring
      have hpos : 0 < (2 : ℤ) ^ (k + 3) := by positivity
      omega

/-- **General Rung-$m$ ($m \ge 3$) Repelling Fixed-Point Bifurcation
(`constant_rung_run_fixed_point_bifurcation`, Section C2.O12.3)**:
For any `3 ≤ m` and `∀ t < j, s (N + t) = m`, setting `T_N = blockSteps s N` and
`S_N = renewalIntSlack s N`:
1. `0 < (3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m`,
2. If `(2 : ℤ) ^ (T_N + m + 1) < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N` (above $\rho_*(m)$), then
   `0 < renewalIntSlack s (N + j)` and
   `centeredRenewalSlack s (N + j) < 0 ↔
     (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) <
       ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j)`,
3. If `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N < (2 : ℤ) ^ (T_N + m + 1)` (below $\rho_*(m)$), then
   `centeredRenewalSlack s (N + j) < 0` and
   `0 < renewalIntSlack s (N + j) ↔
     (3 : ℤ) ^ (m * j) * ((2 : ℤ) ^ (T_N + m + 1) - ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N) <
       (2 : ℤ) ^ (T_N + m + 1 + m * j)`. -/
theorem constant_rung_run_fixed_point_bifurcation
    {s : ℕ → ℕ} {N m j : ℕ} (hm3 : 3 ≤ m) (hm : ∀ t < j, s (N + t) = m) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    0 < (3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m ∧
      ((2 : ℤ) ^ (T_N + m + 1) < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N →
        0 < renewalIntSlack s (N + j) ∧
          (centeredRenewalSlack s (N + j) < 0 ↔
            (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) <
              ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j))) ∧
      (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N < (2 : ℤ) ^ (T_N + m + 1) →
        centeredRenewalSlack s (N + j) < 0 ∧
          (0 < renewalIntSlack s (N + j) ↔
            (3 : ℤ) ^ (m * j) * ((2 : ℤ) ^ (T_N + m + 1) - ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N) <
              (2 : ℤ) ^ (T_N + m + 1 + m * j))) := by
  intro T_N S_N
  have hcf := universal_constant_rung_run_from_step_closed_form hm
  have hS_Nj :
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) =
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) +
          (2 : ℤ) ^ (T_N + m + 1 + m * j) := hcf.2.1
  have hC_Nj :
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) =
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) -
          ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j) := hcf.2.2
  clear hcf
  have hdom := three_mul_two_pow_lt_three_pow_of_three_le hm3
  have h2m_pos : 0 < (2 : ℤ) ^ m := by positivity
  have hMm_pos : 0 < (3 : ℤ) ^ m - (2 : ℤ) ^ m := by omega
  have hCm_pos : 0 < (3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m := by omega
  have h3mj_pos : 0 < (3 : ℤ) ^ (m * j) := by positivity
  have h2_term1_pos : 0 < (2 : ℤ) ^ (T_N + m + 1 + m * j) := by positivity
  have h2_term2_pos : 0 < (2 : ℤ) ^ (T_N + m * j) := by positivity
  have hC_term_pos : 0 < ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * j) :=
    mul_pos hCm_pos h2_term2_pos
  refine ⟨hCm_pos, ?_, ?_⟩
  · intro habove
    have hdiff_pos : 0 < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1) := by omega
    have hprod_pos :
        0 < (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) :=
      mul_pos h3mj_pos hdiff_pos
    have hS_mul_pos : 0 < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) := by omega
    have hS_pos : 0 < renewalIntSlack s (N + j) :=
      pos_of_mul_pos_right hS_mul_pos (le_of_lt hMm_pos)
    refine ⟨hS_pos, ?_⟩
    have hC_iff :
        centeredRenewalSlack s (N + j) < 0 ↔
          ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) < 0 :=
      ⟨fun h => mul_neg_of_pos_of_neg hMm_pos h,
       fun h => by
         by_contra hge
         push_neg at hge
         have hnonneg : 0 ≤ ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) :=
           mul_nonneg (le_of_lt hMm_pos) hge
         omega⟩
    rw [hC_iff, hC_Nj]
    omega
  · intro hbelow
    have hdiff_pos : 0 < (2 : ℤ) ^ (T_N + m + 1) - ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N := by omega
    have hprod_pos :
        0 < (3 : ℤ) ^ (m * j) * ((2 : ℤ) ^ (T_N + m + 1) - ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N) :=
      mul_pos h3mj_pos hdiff_pos
    have hneg_eq :
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) =
          -((3 : ℤ) ^ (m * j) * ((2 : ℤ) ^ (T_N + m + 1) - ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N)) := by ring
    rw [hneg_eq] at hS_Nj hC_Nj
    have hC_mul_neg : ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) < 0 := by omega
    have hC_neg : centeredRenewalSlack s (N + j) < 0 := by
      by_contra hge
      push_neg at hge
      have hnonneg : 0 ≤ ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + j) :=
        mul_nonneg (le_of_lt hMm_pos) hge
      omega
    refine ⟨hC_neg, ?_⟩
    have hS_iff :
        0 < renewalIntSlack s (N + j) ↔
          0 < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) :=
      ⟨fun h => mul_pos hMm_pos h,
       fun h => pos_of_mul_pos_right h (le_of_lt hMm_pos)⟩
    rw [hS_iff, hS_Nj]
    omega

/-! ## 4. Sections C2.O12.4 & C2.O12.5: Certification of Blocks 28, 29, and 30 ($T_{30} = 152$) & Mod-$2^{153}$ Uniqueness -/

/-- **Certification of the 28th ($s_{27} = 3$), 29th ($s_{28} = 6$), and 30th ($s_{29} = 4$) Kneading Rungs & Mod-$2^{153}$ Uniqueness
(`twentyeight_to_thirty_block_kneading_corridor_and_two_pow_153_uniqueness`, Sections C2.O12.4–C2.O12.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 27-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8)$:
1. `(0 < renewalIntSlack s 28 ∧ centeredRenewalSlack s 28 < 0) ↔ s 27 = 3`,
2. When `s 27 = 3`: `blockSteps s 28 = 142`,
   `renewalIntSlack s 28 = 1206918290423261711266834653397765476914161`,
   `centeredRenewalSlack s 28 = -4368268009209394074117094914764324899580943`, and
   `(0 < renewalIntSlack s 29 ∧ centeredRenewalSlack s 29 < 0) ↔ s 28 = 6`,
3. When `s 27 = 3` and `s 28 = 6`: `blockSteps s 29 = 148`,
   `renewalIntSlack s 29 = 166219587365577846984379477602223464479050057`,
   `centeredRenewalSlack s 29 = -190592335810912123280192014760150319616636599`, and
   `(0 < renewalIntSlack s 30 ∧ centeredRenewalSlack s 30 < 0) ↔ s 29 = 4`,
4. When `s 27 = 3`, `s 28 = 6`, and `s 29 = 4`: `blockSteps s 30 = 152`,
   `renewalIntSlack s 30 = 2045805034964126557268449930184139531741081625`,
   `centeredRenewalSlack s 30 = -3663185735859712966964693947613841013789904871`, and any two seeds
   `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 30` satisfy `2 ^ 153 ∣ (b₂ - b₁)` and `2 ^ 153 ≤ b₂`. -/
theorem twentyeight_to_thirty_block_kneading_corridor_and_two_pow_153_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3)
    (hs24 : s 24 = 5) (hs25 : s 25 = 8) (hs26 : s 26 = 8) :
    ((0 < renewalIntSlack s 28 ∧ centeredRenewalSlack s 28 < 0) ↔ s 27 = 3) ∧
      (s 27 = 3 →
        blockSteps s 28 = 142 ∧
          renewalIntSlack s 28 = 1206918290423261711266834653397765476914161 ∧
          centeredRenewalSlack s 28 = -4368268009209394074117094914764324899580943 ∧
          ((0 < renewalIntSlack s 29 ∧ centeredRenewalSlack s 29 < 0) ↔ s 28 = 6)) ∧
      (s 27 = 3 → s 28 = 6 →
        blockSteps s 29 = 148 ∧
          renewalIntSlack s 29 = 166219587365577846984379477602223464479050057 ∧
          centeredRenewalSlack s 29 = -190592335810912123280192014760150319616636599 ∧
          ((0 < renewalIntSlack s 30 ∧ centeredRenewalSlack s 30 < 0) ↔ s 29 = 4)) ∧
      (s 27 = 3 → s 28 = 6 → s 29 = 4 →
        blockSteps s 30 = 152 ∧
          renewalIntSlack s 30 = 2045805034964126557268449930184139531741081625 ∧
          centeredRenewalSlack s 30 = -3663185735859712966964693947613841013789904871 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 30 →
              ValidBlockChain b₂ s u₂ 30 →
                2 ^ 153 ∣ (b₂ - b₁) ∧ 2 ^ 153 ≤ b₂)) := by
  have hprev :=
    (twentyfive_to_twentyseven_block_kneading_corridor_and_two_pow_140_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23).2.2.2 hs24 hs25 hs26
  have hT27 : blockSteps s 27 = 139 := hprev.1
  have hS27 : renewalIntSlack s 27 = 457677440358836047482766436656368378885347 := hprev.2.1
  have hstep27 := subCeiling_step_sandwich_iff s 27
  have hiff27 :
      (0 < renewalIntSlack s 28 ∧ centeredRenewalSlack s 28 < 0) ↔ s 27 = 3 := by
    have hsand27 := hstep27.2.2
    rw [hT27, hS27] at hsand27
    exact hsand27.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 457677440358836047482766436656368378885347) (T_N := 139) (s_star := 3)
      (by norm_num) (by norm_num) (s 27)).1
  have h28_vals :
      s 27 = 3 →
        blockSteps s 28 = 142 ∧
          renewalIntSlack s 28 = 1206918290423261711266834653397765476914161 ∧
          centeredRenewalSlack s 28 = -4368268009209394074117094914764324899580943 := by
    intro hs27
    have hT28 : blockSteps s 28 = 142 := by
      change blockSteps s 27 + s 27 = 142
      rw [hT27, hs27]
    have hS28 : renewalIntSlack s 28 = 1206918290423261711266834653397765476914161 := by
      have h1 := hstep27.1
      rw [h1, hT27, hS27, hs27]
      norm_num
    have hC28 : centeredRenewalSlack s 28 = -4368268009209394074117094914764324899580943 := by
      have h2 := hstep27.2.1
      rw [h2, hT27, hS27, hs27]
      norm_num
    exact ⟨hT28, hS28, hC28⟩
  have h29_vals :
      s 27 = 3 → s 28 = 6 →
        blockSteps s 29 = 148 ∧
          renewalIntSlack s 29 = 166219587365577846984379477602223464479050057 ∧
          centeredRenewalSlack s 29 = -190592335810912123280192014760150319616636599 := by
    intro hs27 hs28
    obtain ⟨hT28, hS28, _⟩ := h28_vals hs27
    have hstep28 := subCeiling_step_sandwich_iff s 28
    have hT29 : blockSteps s 29 = 148 := by
      change blockSteps s 28 + s 28 = 148
      rw [hT28, hs28]
    have hS29 : renewalIntSlack s 29 = 166219587365577846984379477602223464479050057 := by
      have h1 := hstep28.1
      rw [h1, hT28, hS28, hs28]
      norm_num
    have hC29 : centeredRenewalSlack s 29 = -190592335810912123280192014760150319616636599 := by
      have h2 := hstep28.2.1
      rw [h2, hT28, hS28, hs28]
      norm_num
    exact ⟨hT29, hS29, hC29⟩
  refine ⟨hiff27, ?_, ?_, ?_⟩
  · intro hs27
    obtain ⟨hT28, hS28, hC28⟩ := h28_vals hs27
    have hsand28 := (subCeiling_step_sandwich_iff s 28).2.2
    rw [hT28, hS28] at hsand28
    refine ⟨hT28, hS28, hC28, ?_⟩
    exact hsand28.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 1206918290423261711266834653397765476914161) (T_N := 142) (s_star := 6)
      (by norm_num) (by norm_num) (s 28)).1
  · intro hs27 hs28
    obtain ⟨hT29, hS29, hC29⟩ := h29_vals hs27 hs28
    have hsand29 := (subCeiling_step_sandwich_iff s 29).2.2
    rw [hT29, hS29] at hsand29
    refine ⟨hT29, hS29, hC29, ?_⟩
    exact hsand29.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 166219587365577846984379477602223464479050057) (T_N := 148) (s_star := 4)
      (by norm_num) (by norm_num) (s 29)).1
  · intro hs27 hs28 hs29
    obtain ⟨hT29, hS29, _⟩ := h29_vals hs27 hs28
    have hstep29 := subCeiling_step_sandwich_iff s 29
    have hT30 : blockSteps s 30 = 152 := by
      change blockSteps s 29 + s 29 = 152
      rw [hT29, hs29]
    have hS30 : renewalIntSlack s 30 = 2045805034964126557268449930184139531741081625 := by
      have h1 := hstep29.1
      rw [h1, hT29, hS29, hs29]
      norm_num
    have hC30 : centeredRenewalSlack s 30 = -3663185735859712966964693947613841013789904871 := by
      have h2 := hstep29.2.1
      rw [h2, hT29, hS29, hs29]
      norm_num
    refine ⟨hT30, hS30, hC30, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 30) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 30 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT30] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 153 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.UniversalConstantRungAndKneading30
