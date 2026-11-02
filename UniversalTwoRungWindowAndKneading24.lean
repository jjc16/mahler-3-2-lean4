import ExactValuationShiftAndKneading21

/-!
# Universal Two-Step $(s_N, 2)$ Window $(26 : 27)$, Centered-Deficit Post-`2` Recovery Formula & 24-Block ($T_{24} = 118$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 10 / 20 (Part XXV, Sections C2.O10.1–C2.O10.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O10.1 (Inner Loop 1 / 5) — Centered-Deficit Formula $\Sigma_{N+1}(2) = 9 \widehat{\Sigma}_N + 2^{T_N}$
   (`short_block_two_step_eq_nine_centered_add_two_pow`)**:
   - Whenever `s N = 2`, setting `T_N = blockSteps s N` and `C_N = centeredRenewalSlack s N`:
     `renewalIntSlack s (N + 1) = 9 * C_N + (2 : ℤ) ^ T_N` and
     `centeredRenewalSlack s (N + 1) = 9 * C_N - 3 * (2 : ℤ) ^ T_N`.
   - In any sub-ceiling state (`C_N < 0`), `s N = 2` keeps step `N + 1` sub-ceiling if and only if
     `-9 * C_N < (2 : ℤ) ^ T_N`.

2. **Section C2.O10.2 (Inner Loop 2 / 5) — Universal Two-Step $(s_N, s_{N+1} = 2)$ Sub-Ceiling Window $(26 : 27)$
   (`universal_two_step_any_then_two_subCeiling_window`)**:
   - For **any** block length `s N : ℕ`, whenever `s (N + 1) = 2`, setting `T_N = blockSteps s N`
     and `S_N = renewalIntSlack s N`:
     - `renewalIntSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 26 * (2 : ℤ) ^ (T_N + s N)`,
     - `centeredRenewalSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 30 * (2 : ℤ) ^ (T_N + s N)`, and
     - Both steps `N + 1` and `N + 2` lie in the sub-ceiling corridor if and only if
       `26 * (2 : ℤ) ^ (T_N + s N) < 9 * ((3 : ℤ) ^ (s N) * S_N) ∧
         (3 : ℤ) ^ (s N) * S_N < 3 * (2 : ℤ) ^ (T_N + s N)`.

3. **Section C2.O10.3 (Inner Loop 3 / 5) — Exact Post-`2` Recovery Rung Formula in Terms of $\widehat{\Sigma}_N$
   (`post_two_recovery_rung_from_centered_slack_iff`)**:
   - Whenever `s N = 2`, setting `T_N = blockSteps s N`, `C_N = centeredRenewalSlack s N`, and
     `r = s (N + 1)`:
     - `renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 8 * (2 : ℤ) ^ (T_N + r)`,
     - `centeredRenewalSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 12 * (2 : ℤ) ^ (T_N + r)`, and
     - Step `N + 2` lies in the sub-ceiling corridor if and only if
       `8 * (2 : ℤ) ^ (T_N + r) < (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
         (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) < 12 * (2 : ℤ) ^ (T_N + r)`.

4. **Sections C2.O10.4 & C2.O10.5 (Inner Loops 4–5 / 5) — Certification of Blocks 22, 23, and 24 ($s_{21} = 4, s_{22} = 6, s_{23} = 3$, $T_{24} = 118$) & Mod-$2^{119}$ Uniqueness
   (`twentytwo_to_twentyfour_block_kneading_corridor_and_two_pow_119_uniqueness`)**:
   - Certifies blocks 22–24 ($T_{24} = 118$) and proves $2^{119} \mid (b_2 - b_1)$ and $2^{119} \le b_2$
     for any two seeds sharing the 24-block prefix.
-/

namespace Mahler.UniversalTwoRungAndKneading24

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

/-! ## 1. Section C2.O10.1: Centered-Deficit Formula $\Sigma_{N+1}(2) = 9 \widehat{\Sigma}_N + 2^{T_N}$ -/

/-- **Centered-Deficit Formula $\Sigma_{N+1}(2) = 9 \widehat{\Sigma}_N + 2^{T_N}$
(`short_block_two_step_eq_nine_centered_add_two_pow`, Section C2.O10.1)**:
Whenever `s N = 2`, setting `T_N = blockSteps s N` and `C_N = centeredRenewalSlack s N`:
1. `renewalIntSlack s (N + 1) = 9 * C_N + (2 : ℤ) ^ T_N`,
2. `centeredRenewalSlack s (N + 1) = 9 * C_N - 3 * (2 : ℤ) ^ T_N`, and
3. When `C_N < 0`:
   `(0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
     -9 * C_N < (2 : ℤ) ^ T_N`. -/
theorem short_block_two_step_eq_nine_centered_add_two_pow
    {s : ℕ → ℕ} {N : ℕ} (hs2 : s N = 2) :
    let T_N := blockSteps s N
    let C_N := centeredRenewalSlack s N
    renewalIntSlack s (N + 1) = 9 * C_N + (2 : ℤ) ^ T_N ∧
      centeredRenewalSlack s (N + 1) = 9 * C_N - 3 * (2 : ℤ) ^ T_N ∧
      (C_N < 0 →
        ((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
          -9 * C_N < (2 : ℤ) ^ T_N)) := by
  intro T_N C_N
  have hstep := subCeiling_step_sandwich_iff s N
  have hS1 : renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * renewalIntSlack s N - 2 * (2 : ℤ) ^ (T_N + s N) := hstep.1
  have hC1 : centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * renewalIntSlack s N - 3 * (2 : ℤ) ^ (T_N + s N) := hstep.2.1
  clear hstep
  have hS_eq : renewalIntSlack s N = C_N + (2 : ℤ) ^ T_N := by
    change renewalIntSlack s N = (renewalIntSlack s N - (2 : ℤ) ^ T_N) + (2 : ℤ) ^ T_N
    ring
  have hS1' : renewalIntSlack s (N + 1) = 9 * C_N + (2 : ℤ) ^ T_N := by
    rw [hS1, hs2, hS_eq, pow_add]
    ring
  have hC1' : centeredRenewalSlack s (N + 1) = 9 * C_N - 3 * (2 : ℤ) ^ T_N := by
    rw [hC1, hs2, hS_eq, pow_add]
    ring
  clear hS1 hC1 hS_eq
  refine ⟨hS1', hC1', ?_⟩
  intro hC_lt
  rw [hS1', hC1']
  have hpos : 0 < (2 : ℤ) ^ T_N := by positivity
  constructor <;> intro h <;> omega

/-! ## 2. Section C2.O10.2: Universal Two-Step $(s_N, s_{N+1} = 2)$ Sub-Ceiling Window $(26 : 27)$ -/

/-- **Universal Two-Step $(s_N, s_{N+1} = 2)$ Sub-Ceiling Window $(26 : 27)$
(`universal_two_step_any_then_two_subCeiling_window`, Section C2.O10.2)**:
For any sequence `s : ℕ → ℕ` and index `N : ℕ` with `s (N + 1) = 2`, setting
`T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
1. `renewalIntSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 26 * (2 : ℤ) ^ (T_N + s N)`,
2. `centeredRenewalSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 30 * (2 : ℤ) ^ (T_N + s N)`, and
3. `(((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ∧
      (0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0)) ↔
     (26 * (2 : ℤ) ^ (T_N + s N) < 9 * ((3 : ℤ) ^ (s N) * S_N) ∧
       (3 : ℤ) ^ (s N) * S_N < 3 * (2 : ℤ) ^ (T_N + s N)))`. -/
theorem universal_two_step_any_then_two_subCeiling_window
    {s : ℕ → ℕ} {N : ℕ} (hs_next : s (N + 1) = 2) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    renewalIntSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 26 * (2 : ℤ) ^ (T_N + s N) ∧
      centeredRenewalSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 30 * (2 : ℤ) ^ (T_N + s N) ∧
      (((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ∧
          (0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0)) ↔
        (26 * (2 : ℤ) ^ (T_N + s N) < 9 * ((3 : ℤ) ^ (s N) * S_N) ∧
          (3 : ℤ) ^ (s N) * S_N < 3 * (2 : ℤ) ^ (T_N + s N))) := by
  intro T_N S_N
  have hstep1 := subCeiling_step_sandwich_iff s N
  have hS1 : renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 2 * (2 : ℤ) ^ (T_N + s N) := hstep1.1
  have hC1 : centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 3 * (2 : ℤ) ^ (T_N + s N) := hstep1.2.1
  clear hstep1
  have hstep2 := subCeiling_step_sandwich_iff s (N + 1)
  have hS2 : renewalIntSlack s (N + 2) =
      (3 : ℤ) ^ (s (N + 1)) * renewalIntSlack s (N + 1) - 2 * (2 : ℤ) ^ (blockSteps s (N + 1) + s (N + 1)) := hstep2.1
  have hC2 : centeredRenewalSlack s (N + 2) =
      (3 : ℤ) ^ (s (N + 1)) * renewalIntSlack s (N + 1) - 3 * (2 : ℤ) ^ (blockSteps s (N + 1) + s (N + 1)) := hstep2.2.1
  clear hstep2
  have hT1 : blockSteps s (N + 1) = T_N + s N := rfl
  have hS2' : renewalIntSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 26 * (2 : ℤ) ^ (T_N + s N) := by
    rw [hS2, hs_next, hT1, hS1, pow_add]
    ring
  have hC2' : centeredRenewalSlack s (N + 2) = 9 * ((3 : ℤ) ^ (s N) * S_N) - 30 * (2 : ℤ) ^ (T_N + s N) := by
    rw [hC2, hs_next, hT1, hS1, pow_add]
    ring
  clear hS2 hC2 hT1
  refine ⟨hS2', hC2', ?_⟩
  rw [hS1, hC1, hS2', hC2']
  have hpos : 0 < (2 : ℤ) ^ (T_N + s N) := by positivity
  constructor <;> intro h <;> omega

/-! ## 3. Section C2.O10.3: Exact Post-`2` Recovery Rung Formula in Terms of $\widehat{\Sigma}_N$ -/

/-- **Exact Post-`2` Recovery Rung Formula in Terms of $\widehat{\Sigma}_N$
(`post_two_recovery_rung_from_centered_slack_iff`, Section C2.O10.3)**:
Whenever `s N = 2`, setting `T_N = blockSteps s N`, `C_N = centeredRenewalSlack s N`, and
`r = s (N + 1)`:
1. `renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 8 * (2 : ℤ) ^ (T_N + r)`,
2. `centeredRenewalSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 12 * (2 : ℤ) ^ (T_N + r)`, and
3. `(0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ↔
    (8 * (2 : ℤ) ^ (T_N + r) < (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
      (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) < 12 * (2 : ℤ) ^ (T_N + r))`. -/
theorem post_two_recovery_rung_from_centered_slack_iff
    {s : ℕ → ℕ} {N : ℕ} (hs2 : s N = 2) :
    let T_N := blockSteps s N
    let C_N := centeredRenewalSlack s N
    let r := s (N + 1)
    renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 8 * (2 : ℤ) ^ (T_N + r) ∧
      centeredRenewalSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 12 * (2 : ℤ) ^ (T_N + r) ∧
      ((0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0) ↔
        (8 * (2 : ℤ) ^ (T_N + r) < (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) ∧
          (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) < 12 * (2 : ℤ) ^ (T_N + r))) := by
  intro T_N C_N r
  have hS1 := (short_block_two_step_eq_nine_centered_add_two_pow hs2).1
  change renewalIntSlack s (N + 1) = 9 * C_N + (2 : ℤ) ^ T_N at hS1
  have hstep2 := subCeiling_step_sandwich_iff s (N + 1)
  have hS2 : renewalIntSlack s (N + 2) =
      (3 : ℤ) ^ r * renewalIntSlack s (N + 1) - 2 * (2 : ℤ) ^ (blockSteps s (N + 1) + r) := hstep2.1
  have hC2 : centeredRenewalSlack s (N + 2) =
      (3 : ℤ) ^ r * renewalIntSlack s (N + 1) - 3 * (2 : ℤ) ^ (blockSteps s (N + 1) + r) := hstep2.2.1
  clear hstep2
  have hT1 : blockSteps s (N + 1) + r = (T_N + r) + 2 := by
    change (T_N + s N) + r = (T_N + r) + 2
    rw [hs2]
    omega
  have hS2' : renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 8 * (2 : ℤ) ^ (T_N + r) := by
    rw [hS2, hS1, hT1, pow_add]
    ring
  have hC2' : centeredRenewalSlack s (N + 2) = (3 : ℤ) ^ r * ((2 : ℤ) ^ T_N + 9 * C_N) - 12 * (2 : ℤ) ^ (T_N + r) := by
    rw [hC2, hS1, hT1, pow_add]
    ring
  clear hS1 hS2 hC2 hT1
  refine ⟨hS2', hC2', ?_⟩
  rw [hS2', hC2']
  constructor <;> intro h <;> omega

/-! ## 4. Sections C2.O10.4 & C2.O10.5: Certification of Blocks 22, 23, and 24 ($T_{24} = 118$) & Mod-$2^{119}$ Uniqueness -/

/-- **Certification of the 22nd ($s_{21} = 4$), 23rd ($s_{22} = 6$), and 24th ($s_{23} = 3$) Kneading Rungs & Mod-$2^{119}$ Uniqueness
(`twentytwo_to_twentyfour_block_kneading_corridor_and_two_pow_119_uniqueness`, Sections C2.O10.4–C2.O10.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 21-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4)$:
1. `(0 < renewalIntSlack s 22 ∧ centeredRenewalSlack s 22 < 0) ↔ s 21 = 4`,
2. When `s 21 = 4`: `blockSteps s 22 = 109`,
   `renewalIntSlack s 22 = 152354791707497719275671584658555`,
   `centeredRenewalSlack s 22 = -496682315609355734290640456493957`, and
   `(0 < renewalIntSlack s 23 ∧ centeredRenewalSlack s 23 < 0) ↔ s 22 = 6`,
3. When `s 21 = 4` and `s 22 = 6`: `blockSteps s 23 = 115`,
   `renewalIntSlack s 23 = 27989893418208595295476643948565059`,
   `centeredRenewalSlack s 23 = -13548481450070025732767326685195709`, and
   `(0 < renewalIntSlack s 24 ∧ centeredRenewalSlack s 24 < 0) ↔ s 23 = 3`,
4. When `s 21 = 4`, `s 22 = 6`, and `s 23 = 3`: `blockSteps s 24 = 118`,
   `renewalIntSlack s 24 = 91113124399174136525965856471084305`,
   `centeredRenewalSlack s 24 = -241193874547054831699985908599001839`, and any two seeds `b₁ < b₂`
   realizing `ValidBlockChain bᵢ s uᵢ 24` satisfy `2 ^ 119 ∣ (b₂ - b₁)` and `2 ^ 119 ≤ b₂`. -/
theorem twentytwo_to_twentyfour_block_kneading_corridor_and_two_pow_119_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) :
    ((0 < renewalIntSlack s 22 ∧ centeredRenewalSlack s 22 < 0) ↔ s 21 = 4) ∧
      (s 21 = 4 →
        blockSteps s 22 = 109 ∧
          renewalIntSlack s 22 = 152354791707497719275671584658555 ∧
          centeredRenewalSlack s 22 = -496682315609355734290640456493957 ∧
          ((0 < renewalIntSlack s 23 ∧ centeredRenewalSlack s 23 < 0) ↔ s 22 = 6)) ∧
      (s 21 = 4 → s 22 = 6 →
        blockSteps s 23 = 115 ∧
          renewalIntSlack s 23 = 27989893418208595295476643948565059 ∧
          centeredRenewalSlack s 23 = -13548481450070025732767326685195709 ∧
          ((0 < renewalIntSlack s 24 ∧ centeredRenewalSlack s 24 < 0) ↔ s 23 = 3)) ∧
      (s 21 = 4 → s 22 = 6 → s 23 = 3 →
        blockSteps s 24 = 118 ∧
          renewalIntSlack s 24 = 91113124399174136525965856471084305 ∧
          centeredRenewalSlack s 24 = -241193874547054831699985908599001839 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 24 →
              ValidBlockChain b₂ s u₂ 24 →
                2 ^ 119 ∣ (b₂ - b₁) ∧ 2 ^ 119 ≤ b₂)) := by
  have hprev :=
    (nineteen_to_twentyone_block_kneading_corridor_and_two_pow_106_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17).2.2.2
      hs18 hs19 hs20
  have hT21 : blockSteps s 21 = 105 := hprev.1
  have hS21 : renewalIntSlack s 21 = 17906530942484007733435748974859 := hprev.2.1
  have hstep21 := subCeiling_step_sandwich_iff s 21
  have hiff21 :
      (0 < renewalIntSlack s 22 ∧ centeredRenewalSlack s 22 < 0) ↔ s 21 = 4 := by
    have hsand21 := hstep21.2.2
    rw [hT21, hS21] at hsand21
    exact hsand21.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 17906530942484007733435748974859) (T_N := 105) (s_star := 4)
      (by norm_num) (by norm_num) (s 21)).1
  have h22_vals :
      s 21 = 4 →
        blockSteps s 22 = 109 ∧
          renewalIntSlack s 22 = 152354791707497719275671584658555 ∧
          centeredRenewalSlack s 22 = -496682315609355734290640456493957 := by
    intro hs21
    have hT22 : blockSteps s 22 = 109 := by
      change blockSteps s 21 + s 21 = 109
      rw [hT21, hs21]
    have hS22 : renewalIntSlack s 22 = 152354791707497719275671584658555 := by
      have h1 := hstep21.1
      rw [h1, hT21, hS21, hs21]
      norm_num
    have hC22 : centeredRenewalSlack s 22 = -496682315609355734290640456493957 := by
      have h2 := hstep21.2.1
      rw [h2, hT21, hS21, hs21]
      norm_num
    exact ⟨hT22, hS22, hC22⟩
  have h23_vals :
      s 21 = 4 → s 22 = 6 →
        blockSteps s 23 = 115 ∧
          renewalIntSlack s 23 = 27989893418208595295476643948565059 ∧
          centeredRenewalSlack s 23 = -13548481450070025732767326685195709 := by
    intro hs21 hs22
    obtain ⟨hT22, hS22, _⟩ := h22_vals hs21
    have hstep22 := subCeiling_step_sandwich_iff s 22
    have hT23 : blockSteps s 23 = 115 := by
      change blockSteps s 22 + s 22 = 115
      rw [hT22, hs22]
    have hS23 : renewalIntSlack s 23 = 27989893418208595295476643948565059 := by
      have h1 := hstep22.1
      rw [h1, hT22, hS22, hs22]
      norm_num
    have hC23 : centeredRenewalSlack s 23 = -13548481450070025732767326685195709 := by
      have h2 := hstep22.2.1
      rw [h2, hT22, hS22, hs22]
      norm_num
    exact ⟨hT23, hS23, hC23⟩
  refine ⟨hiff21, ?_, ?_, ?_⟩
  · intro hs21
    obtain ⟨hT22, hS22, hC22⟩ := h22_vals hs21
    have hsand22 := (subCeiling_step_sandwich_iff s 22).2.2
    rw [hT22, hS22] at hsand22
    refine ⟨hT22, hS22, hC22, ?_⟩
    exact hsand22.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 152354791707497719275671584658555) (T_N := 109) (s_star := 6)
      (by norm_num) (by norm_num) (s 22)).1
  · intro hs21 hs22
    obtain ⟨hT23, hS23, hC23⟩ := h23_vals hs21 hs22
    have hsand23 := (subCeiling_step_sandwich_iff s 23).2.2
    rw [hT23, hS23] at hsand23
    refine ⟨hT23, hS23, hC23, ?_⟩
    exact hsand23.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 27989893418208595295476643948565059) (T_N := 115) (s_star := 3)
      (by norm_num) (by norm_num) (s 23)).1
  · intro hs21 hs22 hs23
    obtain ⟨hT23, hS23, _⟩ := h23_vals hs21 hs22
    have hstep23 := subCeiling_step_sandwich_iff s 23
    have hT24 : blockSteps s 24 = 118 := by
      change blockSteps s 23 + s 23 = 118
      rw [hT23, hs23]
    have hS24 : renewalIntSlack s 24 = 91113124399174136525965856471084305 := by
      have h1 := hstep23.1
      rw [h1, hT23, hS23, hs23]
      norm_num
    have hC24 : centeredRenewalSlack s 24 = -241193874547054831699985908599001839 := by
      have h2 := hstep23.2.1
      rw [h2, hT23, hS23, hs23]
      norm_num
    refine ⟨hT24, hS24, hC24, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 24) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 24 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT24] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 119 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.UniversalTwoRungAndKneading24
