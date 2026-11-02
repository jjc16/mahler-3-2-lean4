import ParryKneadingShiftDominationAndKneading45

/-!
# Universal $(2, r, 2)$ Sandwich $(104 : 108)$, Exclusion of $(2, \le 6, 2)$, Sharpness at $(2, 7, 2)$ & 48-Block ($T_{48} = 234$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 18 / 20 (Part XXXIII, Sections C2.O18.1–C2.O18.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O18.1 (Inner Loop 1 / 5) — Exact Three-Step Closed Form for $(s_N = 2, s_{N+1} = r, s_{N+2} = 2)$
   (`three_step_two_r_two_closed_form_and_window`)**:
   - Whenever `s N = 2` and `s (N + 2) = 2`, setting `T_N = blockSteps s N`,
     `C_N = centeredRenewalSlack s N`, and `r = s (N + 1)`:
     - `renewalIntSlack s (N + 3) = 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 104 * (2 : ℤ) ^ (T_N + r)`,
     - `centeredRenewalSlack s (N + 3) = 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 120 * (2 : ℤ) ^ (T_N + r)`, and
     - Both steps `N + 2` and `N + 3` lie in the sub-ceiling corridor if and only if
       `104 * (2 : ℤ) ^ (T_N + r) < 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
         9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) < 108 * (2 : ℤ) ^ (T_N + r)`.

2. **Sections C2.O18.2 & C2.O18.3 (Inner Loops 2–3 / 5) — Universal Exclusion of $(2, \le 6, 2)$ & Exact $(2, 7, 2)$ Window
   (`universal_subCeiling_two_r_two_requires_seven_le_and_seven_window`)**:
   - At any sub-ceiling step `N` (`centeredRenewalSlack s N < 0`), if `s N = 2`, `s (N + 2) = 2`,
     and `0 < renewalIntSlack s (N + 3)`, then **`7 ≤ s (N + 1)`**!
   - When `s N = 2`, `s (N + 1) = 7`, and `s (N + 2) = 2`, steps `N + 2` and `N + 3` are both
     sub-ceiling if and only if
     `13312 * (2 : ℤ) ^ T_N < 19683 * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
       19683 * ((2 : ℤ) ^ T_N + 9 * C_N) < 13824 * (2 : ℤ) ^ T_N`.

3. **Sections C2.O18.4 & C2.O18.5 (Inner Loops 4–5 / 5) — Certification of the $(2, 7, 2)$ Kneading Subword at Blocks 46, 47, and 48 ($s_{45} = 2, s_{46} = 7, s_{47} = 2$, $T_{48} = 234$) & Mod-$2^{235}$ Uniqueness
   (`fortysix_to_fortyeight_block_kneading_corridor_and_two_pow_235_uniqueness`)**:
   - Certifies blocks 46–48 ($T_{48} = 234$) and proves $2^{235} \mid (b_2 - b_1)$ and $2^{235} \le b_2$
     for any two seeds sharing the 48-block prefix.
-/

namespace Mahler.TwoRungSandwichAndKneading48

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
open Mahler.PeriodicTailExclusionAndKneading36
open Mahler.FixedPointEigenDefectAndKneading39
open Mahler.ShiftSlackAndKneading42
open Mahler.ParryKneadingDominationAndKneading45

/-! ## 1. Section C2.O18.1: Exact Three-Step Closed Form for $(s_N = 2, s_{N+1} = r, s_{N+2} = 2)$ -/

/-- **Exact Three-Step Closed Form for $(s_N = 2, s_{N+1} = r, s_{N+2} = 2)$
(`three_step_two_r_two_closed_form_and_window`, Section C2.O18.1)**:
Whenever `s N = 2` and `s (N + 2) = 2`, setting `T_N = blockSteps s N`,
`C_N = centeredRenewalSlack s N`, and `r = s (N + 1)`:
1. `renewalIntSlack s (N + 3) = 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 104 * (2 : ℤ) ^ (T_N + r)`,
2. `centeredRenewalSlack s (N + 3) = 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 120 * (2 : ℤ) ^ (T_N + r)`, and
3. `(((0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ∧
      (0 < renewalIntSlack s (N + 3) ∧ centeredRenewalSlack s (N + 3) < 0)) ↔
     (104 * (2 : ℤ) ^ (T_N + r) < 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
       9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) < 108 * (2 : ℤ) ^ (T_N + r)))`. -/
theorem three_step_two_r_two_closed_form_and_window
    {s : ℕ → ℕ} {N : ℕ} (hs0 : s N = 2) (hs2 : s (N + 2) = 2) :
    let T_N := blockSteps s N
    let C_N := centeredRenewalSlack s N
    let r := s (N + 1)
    renewalIntSlack s (N + 3) =
        9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 104 * (2 : ℤ) ^ (T_N + r) ∧
      centeredRenewalSlack s (N + 3) =
        9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 120 * (2 : ℤ) ^ (T_N + r) ∧
      (((0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ∧
          (0 < renewalIntSlack s (N + 3) ∧ centeredRenewalSlack s (N + 3) < 0)) ↔
        (104 * (2 : ℤ) ^ (T_N + r) < 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
          9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) < 108 * (2 : ℤ) ^ (T_N + r))) := by
  intro T_N C_N r
  have hrec := post_two_recovery_rung_from_centered_slack_iff hs0
  have hS2 : renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 8 * (2 : ℤ) ^ (T_N + r) := hrec.1
  have hC2 : centeredRenewalSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 12 * (2 : ℤ) ^ (T_N + r) := hrec.2.1
  clear hrec
  have hshort := short_block_two_step_eq_nine_centered_add_two_pow hs2
  have hS3 : renewalIntSlack s (N + 3) = 9 * centeredRenewalSlack s (N + 2) + (2 : ℤ) ^ (blockSteps s (N + 2)) := hshort.1
  have hC3 : centeredRenewalSlack s (N + 3) = 9 * centeredRenewalSlack s (N + 2) - 3 * (2 : ℤ) ^ (blockSteps s (N + 2)) := hshort.2.1
  clear hshort
  have hT2 : blockSteps s (N + 2) = (T_N + r) + 2 := by
    change (T_N + s N) + r = (T_N + r) + 2
    rw [hs0]
    omega
  have hS3' : renewalIntSlack s (N + 3) = 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 104 * (2 : ℤ) ^ (T_N + r) := by
    rw [hS3, hC2, hT2, pow_add]
    ring
  have hC3' : centeredRenewalSlack s (N + 3) = 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 120 * (2 : ℤ) ^ (T_N + r) := by
    rw [hC3, hC2, hT2, pow_add]
    ring
  clear hS3 hC3 hT2
  refine ⟨hS3', hC3', ?_⟩
  rw [hS2, hC2, hS3', hC3']
  have hpos : 0 < (2 : ℤ) ^ (T_N + r) := by positivity
  have h9_assoc : 9 * (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) = 9 * ((3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N)) := by ring
  rw [h9_assoc]
  constructor <;> intro h <;> omega

/-! ## 2. Sections C2.O18.2 & C2.O18.3: Universal Exclusion of $(2, \le 6, 2)$ & Exact $(2, 7, 2)$ Window -/

/-- **Universal Exclusion of $(2, \le 6, 2)$ & Exact $(2, 7, 2)$ Sub-Ceiling Window
(`universal_subCeiling_two_r_two_requires_seven_le_and_seven_window`, Sections C2.O18.2–C2.O18.3)**:
At any step `N : ℕ` with `s N = 2` and `s (N + 2) = 2`, setting `T_N = blockSteps s N` and
`C_N = centeredRenewalSlack s N`:
1. If `C_N < 0` and `0 < renewalIntSlack s (N + 3)`, then **`7 ≤ s (N + 1)`**!
2. When `s (N + 1) = 7`:
   `(((0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ∧
      (0 < renewalIntSlack s (N + 3) ∧ centeredRenewalSlack s (N + 3) < 0)) ↔
     (13312 * (2 : ℤ) ^ T_N < 19683 * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
       19683 * ((2 : ℤ) ^ T_N + 9 * C_N) < 13824 * (2 : ℤ) ^ T_N))`. -/
theorem universal_subCeiling_two_r_two_requires_seven_le_and_seven_window
    {s : ℕ → ℕ} {N : ℕ} (hs0 : s N = 2) (hs2 : s (N + 2) = 2) :
    let T_N := blockSteps s N
    let C_N := centeredRenewalSlack s N
    (C_N < 0 → 0 < renewalIntSlack s (N + 3) → 7 ≤ s (N + 1)) ∧
      (s (N + 1) = 7 →
        (((0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ∧
            (0 < renewalIntSlack s (N + 3) ∧ centeredRenewalSlack s (N + 3) < 0)) ↔
          (13312 * (2 : ℤ) ^ T_N < 19683 * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
            19683 * ((2 : ℤ) ^ T_N + 9 * C_N) < 13824 * (2 : ℤ) ^ T_N))) := by
  intro T_N C_N
  have h3step := three_step_two_r_two_closed_form_and_window hs0 hs2
  have hS3 :
      renewalIntSlack s (N + 3) =
        9 * (3 : ℤ) ^ (s (N + 1)) * ((2 : ℤ) ^ T_N + 9 * C_N) -
          104 * (2 : ℤ) ^ (T_N + s (N + 1)) := h3step.1
  have hwin := h3step.2.2
  clear h3step
  refine ⟨?_, ?_⟩
  · intro hC_lt hS3_pos
    have hpos_T : 0 < (2 : ℤ) ^ T_N := by positivity
    by_contra hlt7
    have hcases :
        s (N + 1) = 0 ∨ s (N + 1) = 1 ∨ s (N + 1) = 2 ∨ s (N + 1) = 3 ∨
          s (N + 1) = 4 ∨ s (N + 1) = 5 ∨ s (N + 1) = 6 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · have h_eq : renewalIntSlack s (N + 3) = 81 * C_N - 95 * (2 : ℤ) ^ T_N := by
        rw [hS3, h0, add_zero]; ring
      omega
    · have h_eq : renewalIntSlack s (N + 3) = 243 * C_N - 181 * (2 : ℤ) ^ T_N := by
        rw [hS3, h1, pow_add]; ring
      omega
    · have h_eq : renewalIntSlack s (N + 3) = 729 * C_N - 335 * (2 : ℤ) ^ T_N := by
        rw [hS3, h2, pow_add]; ring
      omega
    · have h_eq : renewalIntSlack s (N + 3) = 2187 * C_N - 589 * (2 : ℤ) ^ T_N := by
        rw [hS3, h3, pow_add]; ring
      omega
    · have h_eq : renewalIntSlack s (N + 3) = 6561 * C_N - 935 * (2 : ℤ) ^ T_N := by
        rw [hS3, h4, pow_add]; ring
      omega
    · have h_eq : renewalIntSlack s (N + 3) = 19683 * C_N - 1141 * (2 : ℤ) ^ T_N := by
        rw [hS3, h5, pow_add]; ring
      omega
    · have h_eq : renewalIntSlack s (N + 3) = 59049 * C_N - 95 * (2 : ℤ) ^ T_N := by
        rw [hS3, h6, pow_add]; ring
      omega
  · intro hs1_7
    change (((0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ∧
        (0 < renewalIntSlack s (N + 3) ∧ centeredRenewalSlack s (N + 3) < 0)) ↔
      (104 * (2 : ℤ) ^ (T_N + s (N + 1)) < 9 * (3 : ℤ) ^ (s (N + 1)) * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
        9 * (3 : ℤ) ^ (s (N + 1)) * ((2 : ℤ) ^ T_N + 9 * C_N) < 108 * (2 : ℤ) ^ (T_N + s (N + 1)))) at hwin
    rw [hs1_7] at hwin
    have h104 : 104 * (2 : ℤ) ^ (T_N + 7) = 13312 * (2 : ℤ) ^ T_N := by rw [pow_add]; ring
    have h108 : 108 * (2 : ℤ) ^ (T_N + 7) = 13824 * (2 : ℤ) ^ T_N := by rw [pow_add]; ring
    have h9_3 : 9 * (3 : ℤ) ^ 7 * ((2 : ℤ) ^ T_N + 9 * C_N) = 19683 * ((2 : ℤ) ^ T_N + 9 * C_N) := by ring
    rw [h104, h108, h9_3] at hwin
    exact hwin

/-! ## 3. Sections C2.O18.4 & C2.O18.5: Certification of Blocks 46, 47, and 48 ($T_{48} = 234$) & Mod-$2^{235}$ Uniqueness -/

/-- **Certification of the $(2, 7, 2)$ Kneading Subword at Blocks 46, 47, and 48 ($s_{45} = 2, s_{46} = 7, s_{47} = 2$, $T_{48} = 234$) & Mod-$2^{235}$ Uniqueness
(`fortysix_to_fortyeight_block_kneading_corridor_and_two_pow_235_uniqueness`, Sections C2.O18.4–C2.O18.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 45-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4, 6, 6, 3, 3, 3, 3, 5, 4, 11, 6, 6, 3)$:
1. `(0 < renewalIntSlack s 46 ∧ centeredRenewalSlack s 46 < 0) ↔ s 45 = 2`,
2. When `s 45 = 2`: `blockSteps s 46 = 225`,
   `renewalIntSlack s 46 = 9455753704986742922632906357375472654764159679454708573321352925483`,
   `centeredRenewalSlack s 46 = -44464139629314536666701123816663788692510129165626436388885867572949`, and
   `(0 < renewalIntSlack s 47 ∧ centeredRenewalSlack s 47 < 0) ↔ s 46 = 7`,
3. When `s 45 = 2` and `s 46 = 7`: `blockSteps s 47 = 232`,
   `renewalIntSlack s 47 = 6876240659224879196928654479026107791066999274626674539528750400432729`,
   `centeredRenewalSlack s 47 = -25505687565684590506101383250917661384109697543712015633773823366567`, and
   `(0 < renewalIntSlack s 48 ∧ centeredRenewalSlack s 48 < 0) ↔ s 47 = 2`,
4. When `s 45 = 2`, `s 46 = 7`, and `s 47 = 2`: `blockSteps s 48 = 234`,
   `renewalIntSlack s 48 = 6672195158699402472879843413018766499994121694276978414458559813500193`,
   `centeredRenewalSlack s 48 = -20934790228462852676859180036089335309810314194404567806191537081696991`,
   and any two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 48` satisfy `2 ^ 235 ∣ (b₂ - b₁)`
   and `2 ^ 235 ≤ b₂`. -/
theorem fortysix_to_fortyeight_block_kneading_corridor_and_two_pow_235_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3)
    (hs24 : s 24 = 5) (hs25 : s 25 = 8) (hs26 : s 26 = 8) (hs27 : s 27 = 3)
    (hs28 : s 28 = 6) (hs29 : s 29 = 4) (hs30 : s 30 = 5) (hs31 : s 31 = 3)
    (hs32 : s 32 = 4) (hs33 : s 33 = 6) (hs34 : s 34 = 6) (hs35 : s 35 = 3)
    (hs36 : s 36 = 3) (hs37 : s 37 = 3) (hs38 : s 38 = 3) (hs39 : s 39 = 5)
    (hs40 : s 40 = 4) (hs41 : s 41 = 11) (hs42 : s 42 = 6) (hs43 : s 43 = 6)
    (hs44 : s 44 = 3) :
    ((0 < renewalIntSlack s 46 ∧ centeredRenewalSlack s 46 < 0) ↔ s 45 = 2) ∧
      (s 45 = 2 →
        blockSteps s 46 = 225 ∧
          renewalIntSlack s 46 = 9455753704986742922632906357375472654764159679454708573321352925483 ∧
          centeredRenewalSlack s 46 = -44464139629314536666701123816663788692510129165626436388885867572949 ∧
          ((0 < renewalIntSlack s 47 ∧ centeredRenewalSlack s 47 < 0) ↔ s 46 = 7)) ∧
      (s 45 = 2 → s 46 = 7 →
        blockSteps s 47 = 232 ∧
          renewalIntSlack s 47 = 6876240659224879196928654479026107791066999274626674539528750400432729 ∧
          centeredRenewalSlack s 47 = -25505687565684590506101383250917661384109697543712015633773823366567 ∧
          ((0 < renewalIntSlack s 48 ∧ centeredRenewalSlack s 48 < 0) ↔ s 47 = 2)) ∧
      (s 45 = 2 → s 46 = 7 → s 47 = 2 →
        blockSteps s 48 = 234 ∧
          renewalIntSlack s 48 = 6672195158699402472879843413018766499994121694276978414458559813500193 ∧
          centeredRenewalSlack s 48 = -20934790228462852676859180036089335309810314194404567806191537081696991 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 48 →
              ValidBlockChain b₂ s u₂ 48 →
                2 ^ 235 ∣ (b₂ - b₁) ∧ 2 ^ 235 ≤ b₂)) := by
  have hprev :=
    (fortythree_to_fortyfive_block_kneading_corridor_and_two_pow_224_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32 hs33 hs34 hs35 hs36 hs37
      hs38 hs39 hs40 hs41).2.2.2 hs42 hs43 hs44
  have hT45 : blockSteps s 45 = 223 := hprev.1
  have hS45 : renewalIntSlack s 45 = 13032837819287700233477885189494888372145859707735222055303977102483 := hprev.2.1
  have hstep45 := subCeiling_step_sandwich_iff s 45
  have hiff45 :
      (0 < renewalIntSlack s 46 ∧ centeredRenewalSlack s 46 < 0) ↔ s 45 = 2 := by
    have hsand45 := hstep45.2.2
    rw [hT45, hS45] at hsand45
    exact hsand45.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 13032837819287700233477885189494888372145859707735222055303977102483) (T_N := 223) (s_star := 2)
      (by norm_num) (by norm_num) (s 45)).1
  have h46_vals :
      s 45 = 2 →
        blockSteps s 46 = 225 ∧
          renewalIntSlack s 46 = 9455753704986742922632906357375472654764159679454708573321352925483 ∧
          centeredRenewalSlack s 46 = -44464139629314536666701123816663788692510129165626436388885867572949 := by
    intro hs45
    have hT46 : blockSteps s 46 = 225 := by
      change blockSteps s 45 + s 45 = 225
      rw [hT45, hs45]
    have hS46 : renewalIntSlack s 46 = 9455753704986742922632906357375472654764159679454708573321352925483 := by
      have h1 := hstep45.1
      rw [h1, hT45, hS45, hs45]
      norm_num
    have hC46 : centeredRenewalSlack s 46 = -44464139629314536666701123816663788692510129165626436388885867572949 := by
      have h2 := hstep45.2.1
      rw [h2, hT45, hS45, hs45]
      norm_num
    exact ⟨hT46, hS46, hC46⟩
  have h47_vals :
      s 45 = 2 → s 46 = 7 →
        blockSteps s 47 = 232 ∧
          renewalIntSlack s 47 = 6876240659224879196928654479026107791066999274626674539528750400432729 ∧
          centeredRenewalSlack s 47 = -25505687565684590506101383250917661384109697543712015633773823366567 := by
    intro hs45 hs46
    obtain ⟨hT46, hS46, _⟩ := h46_vals hs45
    have hstep46 := subCeiling_step_sandwich_iff s 46
    have hT47 : blockSteps s 47 = 232 := by
      change blockSteps s 46 + s 46 = 232
      rw [hT46, hs46]
    have hS47 : renewalIntSlack s 47 = 6876240659224879196928654479026107791066999274626674539528750400432729 := by
      have h1 := hstep46.1
      rw [h1, hT46, hS46, hs46]
      norm_num
    have hC47 : centeredRenewalSlack s 47 = -25505687565684590506101383250917661384109697543712015633773823366567 := by
      have h2 := hstep46.2.1
      rw [h2, hT46, hS46, hs46]
      norm_num
    exact ⟨hT47, hS47, hC47⟩
  refine ⟨hiff45, ?_, ?_, ?_⟩
  · intro hs45
    obtain ⟨hT46, hS46, hC46⟩ := h46_vals hs45
    have hsand46 := (subCeiling_step_sandwich_iff s 46).2.2
    rw [hT46, hS46] at hsand46
    refine ⟨hT46, hS46, hC46, ?_⟩
    exact hsand46.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 9455753704986742922632906357375472654764159679454708573321352925483) (T_N := 225) (s_star := 7)
      (by norm_num) (by norm_num) (s 46)).1
  · intro hs45 hs46
    obtain ⟨hT47, hS47, hC47⟩ := h47_vals hs45 hs46
    have hsand47 := (subCeiling_step_sandwich_iff s 47).2.2
    rw [hT47, hS47] at hsand47
    refine ⟨hT47, hS47, hC47, ?_⟩
    exact hsand47.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 6876240659224879196928654479026107791066999274626674539528750400432729) (T_N := 232) (s_star := 2)
      (by norm_num) (by norm_num) (s 47)).1
  · intro hs45 hs46 hs47
    obtain ⟨hT47, hS47, _⟩ := h47_vals hs45 hs46
    have hstep47 := subCeiling_step_sandwich_iff s 47
    have hT48 : blockSteps s 48 = 234 := by
      change blockSteps s 47 + s 47 = 234
      rw [hT47, hs47]
    have hS48 : renewalIntSlack s 48 = 6672195158699402472879843413018766499994121694276978414458559813500193 := by
      have h1 := hstep47.1
      rw [h1, hT47, hS47, hs47]
      norm_num
    have hC48 : centeredRenewalSlack s 48 = -20934790228462852676859180036089335309810314194404567806191537081696991 := by
      have h2 := hstep47.2.1
      rw [h2, hT47, hS47, hs47]
      norm_num
    refine ⟨hT48, hS48, hC48, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 48) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 48 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT48] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 235 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.TwoRungSandwichAndKneading48
