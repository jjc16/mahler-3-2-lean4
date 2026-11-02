import TwoRungSandwichAndKneading48

/-!
# Subword Return-Proximity Law $3^{d_M}(-\widehat{\Sigma}_N) < \Sigma_M(w)\cdot 2^{T_N}$, Strict Parry Rung-Jump Dichotomy ($s_{N+M} = w_M$ vs. $w_M + 1 \le s_{N+M}$) & 51-Block ($T_{51} = 247$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 19 / 20 (Part XXXIV, Sections C2.O19.1–C2.O19.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O19.1 (Inner Loop 1 / 5) — Exact Return-Proximity Criterion for Matching $M$ Kneading Blocks
   (`subCeiling_prefix_match_survives_iff_centered_deficit_bound`)**:
   - Whenever `centeredRenewalSlack s N < 0`, `∀ t < M, s (N + t) = w t`, and
     `centeredRenewalSlack w M ≤ 0`, setting `d_M = blockSteps w M` and `T_N = blockSteps s N`:
     `centeredRenewalSlack s (N + M) < 0` and
     `(0 < renewalIntSlack s (N + M) ∧ centeredRenewalSlack s (N + M) < 0) ↔
       (3 : ℤ) ^ d_M * (-centeredRenewalSlack s N) < renewalIntSlack w M * (2 : ℤ) ^ T_N`.

2. **Section C2.O19.2 (Inner Loop 2 / 5) — The Strict Parry–Kneading Rung-Jump Dichotomy ($s_{N+M} = w_M$ vs. $w_M + 1 \le s_{N+M}$)
   (`subCeiling_shift_strict_rung_jump_dichotomy`)**:
   - Suppose `centeredRenewalSlack s N < 0`, `∀ t < M, s (N + t) = w t`,
     `centeredRenewalSlack w (M + 1) ≤ 0`, and `0 < renewalIntSlack s (N + M + 1)`, with
     `d_{M+1} = blockSteps w (M + 1)` and `T_N = blockSteps s N`:
     - If `renewalIntSlack w (M + 1) * (2 : ℤ) ^ T_N ≤ (3 : ℤ) ^ d_{M+1} * (-centeredRenewalSlack s N)`,
       then **`w M + 1 ≤ s (N + M)`** (strict jump!).
     - If `(3 : ℤ) ^ d_{M+1} * (-centeredRenewalSlack s N) < renewalIntSlack w (M + 1) * (2 : ℤ) ^ T_N`
       and `centeredRenewalSlack s (N + M + 1) < 0`, then **`s (N + M) = w M`**!

3. **Section C2.O19.3 (Inner Loop 3 / 5) — Explicit 4-Block $(2, 6, 3, 3)$ vs. $(2, 6, 3, \ge 4)$ Return Threshold
   (`two_six_three_three_vs_four_return_threshold`)**:
   - Whenever `centeredRenewalSlack s N < 0`, `s N = 2`, `s (N + 1) = 6`, and `s (N + 2) = 3`:
     - If `s (N + 3) = 3`, then
       `renewalIntSlack s (N + 4) = 4782969 * centeredRenewalSlack s N + 14833 * (2 : ℤ) ^ (blockSteps s N)`.
     - If `14833 * (2 : ℤ) ^ (blockSteps s N) ≤ 4782969 * (-centeredRenewalSlack s N)` and
       `0 < renewalIntSlack s (N + 4)`, then **`4 ≤ s (N + 3)`**!

4. **Sections C2.O19.4 & C2.O19.5 (Inner Loops 4–5 / 5) — Certification of Blocks 49, 50, and 51 ($s_{48} = 6, s_{49} = 3, s_{50} = 4$, $T_{51} = 247$) & Mod-$2^{248}$ Uniqueness
   (`fortynine_to_fiftyone_block_kneading_corridor_and_two_pow_248_uniqueness`)**:
   - Certifies blocks 49–51 ($T_{51} = 247$, confirming the strict Parry jump $(2, 6, 3, 4)$ at
     $N = 47$) and proves $2^{248} \mid (b_2 - b_1)$ and $2^{248} \le b_2$.
-/

namespace Mahler.StrictParryJumpAndKneading51

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
open Mahler.TwoRungSandwichAndKneading48

/-! ## 1. Section C2.O19.1: Exact Return-Proximity Criterion for Matching $M$ Kneading Blocks -/

/-- **Exact Return-Proximity Criterion for Matching $M$ Kneading Blocks
(`subCeiling_prefix_match_survives_iff_centered_deficit_bound`, Section C2.O19.1)**:
Whenever `centeredRenewalSlack s N < 0` and `∀ t < M, s (N + t) = w t`, setting
`d_M = blockSteps w M` and `T_N = blockSteps s N`:
1. `renewalIntSlack s (N + M) =
     (3 : ℤ) ^ d_M * centeredRenewalSlack s N + (2 : ℤ) ^ T_N * renewalIntSlack w M`,
2. If `centeredRenewalSlack w M ≤ 0`, then `centeredRenewalSlack s (N + M) < 0`, and
3. If `centeredRenewalSlack w M ≤ 0`, then
   `(0 < renewalIntSlack s (N + M) ∧ centeredRenewalSlack s (N + M) < 0) ↔
     (3 : ℤ) ^ d_M * (-centeredRenewalSlack s N) < renewalIntSlack w M * (2 : ℤ) ^ T_N`. -/
theorem subCeiling_prefix_match_survives_iff_centered_deficit_bound
    {s w : ℕ → ℕ} {N M : ℕ}
    (hsub : centeredRenewalSlack s N < 0)
    (hmatch : ∀ t < M, s (N + t) = w t) :
    let d_M := blockSteps w M
    let T_N := blockSteps s N
    renewalIntSlack s (N + M) =
        (3 : ℤ) ^ d_M * centeredRenewalSlack s N + (2 : ℤ) ^ T_N * renewalIntSlack w M ∧
      (centeredRenewalSlack w M ≤ 0 →
        centeredRenewalSlack s (N + M) < 0 ∧
          ((0 < renewalIntSlack s (N + M) ∧ centeredRenewalSlack s (N + M) < 0) ↔
            (3 : ℤ) ^ d_M * (-centeredRenewalSlack s N) < renewalIntSlack w M * (2 : ℤ) ^ T_N)) := by
  intro d_M T_N
  set s' := fun t => s (N + t)
  rcases prefix_congr_blockSteps_renewalNumerator_slack (s' := s') (w := w) hmatch with
    ⟨hT_eq, _, hS_eq, _⟩
  have hshift := renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack s N M
  change renewalIntSlack s (N + M) =
    (3 : ℤ) ^ (blockSteps s' M) * centeredRenewalSlack s N +
      (2 : ℤ) ^ T_N * renewalIntSlack s' M at hshift
  rw [hT_eq, hS_eq] at hshift
  have hdom := (subCeiling_shift_lexicographic_domination hsub hmatch).1
  refine ⟨hshift, ?_⟩
  intro hCw_le
  have hC_NM_neg : centeredRenewalSlack s (N + M) < 0 := hdom hCw_le
  refine ⟨hC_NM_neg, ?_⟩
  have h_rearr :
      (3 : ℤ) ^ (blockSteps w M) * centeredRenewalSlack s N +
          (2 : ℤ) ^ T_N * renewalIntSlack w M =
        renewalIntSlack w M * (2 : ℤ) ^ T_N -
          (3 : ℤ) ^ d_M * (-centeredRenewalSlack s N) := by
    dsimp [d_M]
    ring
  rw [hshift, h_rearr]
  exact ⟨fun h => by have h1 := h.1; omega, fun h => ⟨by omega, hC_NM_neg⟩⟩

/-! ## 2. Section C2.O19.2: The Strict Parry–Kneading Rung-Jump Dichotomy -/

/-- **The Strict Parry–Kneading Rung-Jump Dichotomy ($s_{N+M} = w_M$ vs. $w_M + 1 \le s_{N+M}$)
(`subCeiling_shift_strict_rung_jump_dichotomy`, Section C2.O19.2)**:
Suppose `centeredRenewalSlack s N < 0`, `∀ t < M, s (N + t) = w t`,
`centeredRenewalSlack w (M + 1) ≤ 0`, and `0 < renewalIntSlack s (N + M + 1)`, with
`d_next = blockSteps w (M + 1)` and `T_N = blockSteps s N`:
1. `w M ≤ s (N + M)`,
2. If `s (N + M) = w M`, then
   `renewalIntSlack s (N + M + 1) =
     (3 : ℤ) ^ d_next * centeredRenewalSlack s N + (2 : ℤ) ^ T_N * renewalIntSlack w (M + 1)`, and
3. If `renewalIntSlack w (M + 1) * (2 : ℤ) ^ T_N ≤ (3 : ℤ) ^ d_next * (-centeredRenewalSlack s N)`,
   then **`w M + 1 ≤ s (N + M)`** (strict jump!). -/
theorem subCeiling_shift_strict_rung_jump_dichotomy
    {s w : ℕ → ℕ} {N M : ℕ}
    (hsub : centeredRenewalSlack s N < 0)
    (hmatch : ∀ t < M, s (N + t) = w t)
    (hCw_next : centeredRenewalSlack w (M + 1) ≤ 0)
    (hS_next_pos : 0 < renewalIntSlack s (N + M + 1)) :
    let d_next := blockSteps w (M + 1)
    let T_N := blockSteps s N
    w M ≤ s (N + M) ∧
      (s (N + M) = w M →
        renewalIntSlack s (N + M + 1) =
          (3 : ℤ) ^ d_next * centeredRenewalSlack s N +
            (2 : ℤ) ^ T_N * renewalIntSlack w (M + 1)) ∧
      (renewalIntSlack w (M + 1) * (2 : ℤ) ^ T_N ≤
          (3 : ℤ) ^ d_next * (-centeredRenewalSlack s N) →
        w M + 1 ≤ s (N + M)) := by
  intro d_next T_N
  have hw_le : w M ≤ s (N + M) :=
    (subCeiling_shift_lexicographic_domination hsub hmatch).2.2 hCw_next hS_next_pos
  have heq_case :
      s (N + M) = w M →
        renewalIntSlack s (N + M + 1) =
          (3 : ℤ) ^ d_next * centeredRenewalSlack s N +
            (2 : ℤ) ^ T_N * renewalIntSlack w (M + 1) := by
    intro heqM
    have hmatch1 : ∀ t < M + 1, s (N + t) = w t := by
      intro t ht
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
      · exact hmatch t hlt
      · exact heqM
    exact (subCeiling_prefix_match_survives_iff_centered_deficit_bound hsub hmatch1).1
  refine ⟨hw_le, heq_case, ?_⟩
  intro hdef_ge
  by_contra hnot_gt
  have heqM : s (N + M) = w M := by omega
  have hid := heq_case heqM
  have h_rearr :
      (3 : ℤ) ^ d_next * centeredRenewalSlack s N +
          (2 : ℤ) ^ T_N * renewalIntSlack w (M + 1) =
        renewalIntSlack w (M + 1) * (2 : ℤ) ^ T_N -
          (3 : ℤ) ^ d_next * (-centeredRenewalSlack s N) := by ring
  rw [hid, h_rearr] at hS_next_pos
  omega

/-! ## 3. Section C2.O19.3: Explicit 4-Block $(2, 6, 3, 3)$ vs. $(2, 6, 3, \ge 4)$ Return Threshold -/

/-- **Explicit 4-Block $(2, 6, 3, 3)$ vs. $(2, 6, 3, \ge 4)$ Return Threshold
(`two_six_three_three_vs_four_return_threshold`, Section C2.O19.3)**:
Whenever `centeredRenewalSlack s N < 0`, `s N = 2`, `s (N + 1) = 6`, and `s (N + 2) = 3`,
setting `T_N = blockSteps s N` and `C_N = centeredRenewalSlack s N`:
1. If `s (N + 3) = 3`, then
   `renewalIntSlack s (N + 4) = 4782969 * C_N + 14833 * (2 : ℤ) ^ T_N`, and
2. If `14833 * (2 : ℤ) ^ T_N ≤ 4782969 * (-C_N)` and `0 < renewalIntSlack s (N + 4)`, then
   **`4 ≤ s (N + 3)`**! -/
theorem two_six_three_three_vs_four_return_threshold
    {s : ℕ → ℕ} {N : ℕ}
    (hsub : centeredRenewalSlack s N < 0)
    (hs0 : s N = 2) (hs1 : s (N + 1) = 6) (hs2 : s (N + 2) = 3) :
    let T_N := blockSteps s N
    let C_N := centeredRenewalSlack s N
    (s (N + 3) = 3 →
      renewalIntSlack s (N + 4) = 4782969 * C_N + 14833 * (2 : ℤ) ^ T_N) ∧
      (14833 * (2 : ℤ) ^ T_N ≤ 4782969 * (-C_N) →
        0 < renewalIntSlack s (N + 4) →
          4 ≤ s (N + 3)) := by
  intro T_N C_N
  set s' := fun t => s (N + t)
  have hs'0 : s' 0 = 2 := hs0
  have hs'1 : s' 1 = 6 := hs1
  have hs'2 : s' 2 = 3 := hs2
  have h3_case :
      s (N + 3) = 3 →
        renewalIntSlack s (N + 4) = 4782969 * C_N + 14833 * (2 : ℤ) ^ T_N := by
    intro hs3
    have hs'3 : s' 3 = 3 := hs3
    have hd4 : blockSteps s' 4 = 14 := by simp [blockSteps, hs'0, hs'1, hs'2, hs'3]
    have hS4_s' : renewalIntSlack s' 4 = 14833 := by
      simp [renewalIntSlack, blockSteps, renewalNumerator, hs'0, hs'1, hs'2, hs'3]
    have hshift4 := renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack s N 4
    change renewalIntSlack s (N + 4) =
      (3 : ℤ) ^ (blockSteps s' 4) * C_N + (2 : ℤ) ^ T_N * renewalIntSlack s' 4 at hshift4
    rw [hd4, hS4_s'] at hshift4
    rw [hshift4]
    ring
  refine ⟨h3_case, ?_⟩
  intro hdef_ge hS4_pos
  have hge3 : 3 ≤ s (N + 3) :=
    ((universal_subCeiling_two_six_two_and_two_six_three_two_forbidden hsub).2 hs0 hs1 hs2).2 hS4_pos
  by_contra hlt4
  have hs3 : s (N + 3) = 3 := by omega
  have hid := h3_case hs3
  have h_rearr : 4782969 * C_N + 14833 * (2 : ℤ) ^ T_N = 14833 * (2 : ℤ) ^ T_N - 4782969 * (-C_N) := by
    ring
  rw [hid, h_rearr] at hS4_pos
  omega

/-! ## 4. Sections C2.O19.4 & C2.O19.5: Certification of Blocks 49, 50, and 51 ($T_{51} = 247$) & Mod-$2^{248}$ Uniqueness -/

/-- **Certification of the 49th ($s_{48} = 6$), 50th ($s_{49} = 3$), and 51st ($s_{50} = 4$) Kneading Rungs & Mod-$2^{248}$ Uniqueness
(`fortynine_to_fiftyone_block_kneading_corridor_and_two_pow_248_uniqueness`, Sections C2.O19.4–C2.O19.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 48-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4, 6, 6, 3, 3, 3, 3, 5, 4, 11, 6, 6, 3, 2, 7, 2)$:
1. `(0 < renewalIntSlack s 49 ∧ centeredRenewalSlack s 49 < 0) ↔ s 48 = 6`,
2. When `s 48 = 6`: `blockSteps s 49 = 240`,
   `renewalIntSlack s 49 = 1330336141135095743562810846604843746840746921376679347897077701456401145`,
   `centeredRenewalSlack s 49 = -436510923643288586020486654138074768986736975498939610224528499836218631`, and
   `(0 < renewalIntSlack s 50 ∧ centeredRenewalSlack s 50 < 0) ↔ s 49 = 3`,
3. When `s 48 = 6` and `s 49 = 3`: `blockSteps s 50 = 243`,
   `renewalIntSlack s 50 = 7649522774193435802863132846444084911460424527160439063275398718640914499`,
   `centeredRenewalSlack s 50 = -6485253744033638833803247159499263215159446647844512601697450891700043709`, and
   `(0 < renewalIntSlack s 51 ∧ centeredRenewalSlack s 51 < 0) ↔ s 50 = 4`,
4. When `s 48 = 6`, `s 49 = 3`, and `s 50 = 4`: `blockSteps s 51 = 247`,
   `renewalIntSlack s 51 = 167298496126401911658589600371783737776458509099837110846176108679003411763`,
   `centeredRenewalSlack s 51 = -58857928165231282528072479723309832249459429700242115793389485086451919565`,
   and any two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 51` satisfy `2 ^ 248 ∣ (b₂ - b₁)`
   and `2 ^ 248 ≤ b₂`. -/
theorem fortynine_to_fiftyone_block_kneading_corridor_and_two_pow_248_uniqueness
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
    (hs44 : s 44 = 3) (hs45 : s 45 = 2) (hs46 : s 46 = 7) (hs47 : s 47 = 2) :
    ((0 < renewalIntSlack s 49 ∧ centeredRenewalSlack s 49 < 0) ↔ s 48 = 6) ∧
      (s 48 = 6 →
        blockSteps s 49 = 240 ∧
          renewalIntSlack s 49 = 1330336141135095743562810846604843746840746921376679347897077701456401145 ∧
          centeredRenewalSlack s 49 = -436510923643288586020486654138074768986736975498939610224528499836218631 ∧
          ((0 < renewalIntSlack s 50 ∧ centeredRenewalSlack s 50 < 0) ↔ s 49 = 3)) ∧
      (s 48 = 6 → s 49 = 3 →
        blockSteps s 50 = 243 ∧
          renewalIntSlack s 50 = 7649522774193435802863132846444084911460424527160439063275398718640914499 ∧
          centeredRenewalSlack s 50 = -6485253744033638833803247159499263215159446647844512601697450891700043709 ∧
          ((0 < renewalIntSlack s 51 ∧ centeredRenewalSlack s 51 < 0) ↔ s 50 = 4)) ∧
      (s 48 = 6 → s 49 = 3 → s 50 = 4 →
        blockSteps s 51 = 247 ∧
          renewalIntSlack s 51 = 167298496126401911658589600371783737776458509099837110846176108679003411763 ∧
          centeredRenewalSlack s 51 = -58857928165231282528072479723309832249459429700242115793389485086451919565 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 51 →
              ValidBlockChain b₂ s u₂ 51 →
                2 ^ 248 ∣ (b₂ - b₁) ∧ 2 ^ 248 ≤ b₂)) := by
  have hprev :=
    (fortysix_to_fortyeight_block_kneading_corridor_and_two_pow_235_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32 hs33 hs34 hs35 hs36 hs37
      hs38 hs39 hs40 hs41 hs42 hs43 hs44).2.2.2 hs45 hs46 hs47
  have hT48 : blockSteps s 48 = 234 := hprev.1
  have hS48 : renewalIntSlack s 48 = 6672195158699402472879843413018766499994121694276978414458559813500193 := hprev.2.1
  have hstep48 := subCeiling_step_sandwich_iff s 48
  have hiff48 :
      (0 < renewalIntSlack s 49 ∧ centeredRenewalSlack s 49 < 0) ↔ s 48 = 6 := by
    have hsand48 := hstep48.2.2
    rw [hT48, hS48] at hsand48
    exact hsand48.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 6672195158699402472879843413018766499994121694276978414458559813500193) (T_N := 234) (s_star := 6)
      (by norm_num) (by norm_num) (s 48)).1
  have h49_vals :
      s 48 = 6 →
        blockSteps s 49 = 240 ∧
          renewalIntSlack s 49 = 1330336141135095743562810846604843746840746921376679347897077701456401145 ∧
          centeredRenewalSlack s 49 = -436510923643288586020486654138074768986736975498939610224528499836218631 := by
    intro hs48
    have hT49 : blockSteps s 49 = 240 := by
      change blockSteps s 48 + s 48 = 240
      rw [hT48, hs48]
    have hS49 : renewalIntSlack s 49 = 1330336141135095743562810846604843746840746921376679347897077701456401145 := by
      have h1 := hstep48.1
      rw [h1, hT48, hS48, hs48]
      norm_num
    have hC49 : centeredRenewalSlack s 49 = -436510923643288586020486654138074768986736975498939610224528499836218631 := by
      have h2 := hstep48.2.1
      rw [h2, hT48, hS48, hs48]
      norm_num
    exact ⟨hT49, hS49, hC49⟩
  have h50_vals :
      s 48 = 6 → s 49 = 3 →
        blockSteps s 50 = 243 ∧
          renewalIntSlack s 50 = 7649522774193435802863132846444084911460424527160439063275398718640914499 ∧
          centeredRenewalSlack s 50 = -6485253744033638833803247159499263215159446647844512601697450891700043709 := by
    intro hs48 hs49
    obtain ⟨hT49, hS49, _⟩ := h49_vals hs48
    have hstep49 := subCeiling_step_sandwich_iff s 49
    have hT50 : blockSteps s 50 = 243 := by
      change blockSteps s 49 + s 49 = 243
      rw [hT49, hs49]
    have hS50 : renewalIntSlack s 50 = 7649522774193435802863132846444084911460424527160439063275398718640914499 := by
      have h1 := hstep49.1
      rw [h1, hT49, hS49, hs49]
      norm_num
    have hC50 : centeredRenewalSlack s 50 = -6485253744033638833803247159499263215159446647844512601697450891700043709 := by
      have h2 := hstep49.2.1
      rw [h2, hT49, hS49, hs49]
      norm_num
    exact ⟨hT50, hS50, hC50⟩
  refine ⟨hiff48, ?_, ?_, ?_⟩
  · intro hs48
    obtain ⟨hT49, hS49, hC49⟩ := h49_vals hs48
    have hsand49 := (subCeiling_step_sandwich_iff s 49).2.2
    rw [hT49, hS49] at hsand49
    refine ⟨hT49, hS49, hC49, ?_⟩
    exact hsand49.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 1330336141135095743562810846604843746840746921376679347897077701456401145) (T_N := 240) (s_star := 3)
      (by norm_num) (by norm_num) (s 49)).1
  · intro hs48 hs49
    obtain ⟨hT50, hS50, hC50⟩ := h50_vals hs48 hs49
    have hsand50 := (subCeiling_step_sandwich_iff s 50).2.2
    rw [hT50, hS50] at hsand50
    refine ⟨hT50, hS50, hC50, ?_⟩
    exact hsand50.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 7649522774193435802863132846444084911460424527160439063275398718640914499) (T_N := 243) (s_star := 4)
      (by norm_num) (by norm_num) (s 50)).1
  · intro hs48 hs49 hs50
    obtain ⟨hT50, hS50, _⟩ := h50_vals hs48 hs49
    have hstep50 := subCeiling_step_sandwich_iff s 50
    have hT51 : blockSteps s 51 = 247 := by
      change blockSteps s 50 + s 50 = 247
      rw [hT50, hs50]
    have hS51 : renewalIntSlack s 51 = 167298496126401911658589600371783737776458509099837110846176108679003411763 := by
      have h1 := hstep50.1
      rw [h1, hT50, hS50, hs50]
      norm_num
    have hC51 : centeredRenewalSlack s 51 = -58857928165231282528072479723309832249459429700242115793389485086451919565 := by
      have h2 := hstep50.2.1
      rw [h2, hT50, hS50, hs50]
      norm_num
    refine ⟨hT51, hS51, hC51, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 51) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 51 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT51] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 248 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.StrictParryJumpAndKneading51
