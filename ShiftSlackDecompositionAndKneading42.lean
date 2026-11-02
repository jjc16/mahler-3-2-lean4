import FixedPointEigenDefectAndKneading39

/-!
# Mixed Shift-Slack Cocycle $\Sigma_{N+M} = 3^d \widehat{\Sigma}_N + 2^{T_N}\Sigma_M(s')$, Universal Subword Escape Inheritance & 42-Block ($T_{42} = 208$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 16 / 20 (Part XXXI, Sections C2.O16.1–C2.O16.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Sections C2.O16.1 & C2.O16.2 (Inner Loops 1–2 / 5) — Mixed Shift-Slack Cocycle & Universal Subword Escape Inheritance
   (`renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack`, `subCeiling_subword_escape_inheritance`)**:
   - For any sequence `s : ℕ → ℕ` and any `N, M : ℕ`, setting `s' t = s (N + t)` and
     `d = blockSteps s' M`:
     `renewalIntSlack s (N + M) =
       (3 : ℤ) ^ d * centeredRenewalSlack s N + (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M`.
   - Whenever `centeredRenewalSlack s N < 0` and `renewalIntSlack s' M ≤ 0`:
     `renewalIntSlack s (N + M) ≤ -(3 : ℤ) ^ d + (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M`
     and `renewalIntSlack s (N + M) < 0`.

2. **Section C2.O16.3 (Inner Loop 3 / 5) — Universal Exclusion of $(2, 6, 2)$ and $(2, 6, 3, 2)$ at Arbitrary Sub-Ceiling Steps
   (`universal_subCeiling_two_six_two_and_two_six_three_two_forbidden`)**:
   - At any sub-ceiling step `N` (`centeredRenewalSlack s N < 0`):
     - If `s N = 2` and `s (N + 1) = 6`, then `centeredRenewalSlack s (N + 2) < 0` and
       `0 < renewalIntSlack s (N + 3) → 3 ≤ s (N + 2)` (so $(2, 6, 2)$ is universally forbidden).
     - If `s N = 2`, `s (N + 1) = 6`, and `s (N + 2) = 3`, then `centeredRenewalSlack s (N + 3) < 0`
       and `0 < renewalIntSlack s (N + 4) → 3 ≤ s (N + 3)` (so $(2, 6, 3, 2)$ is universally forbidden).

3. **Sections C2.O16.4 & C2.O16.5 (Inner Loops 4–5 / 5) — Certification of Blocks 40, 41, and 42 ($s_{39} = 5, s_{40} = 4, s_{41} = 11$, $T_{42} = 208$) & Mod-$2^{209}$ Uniqueness
   (`forty_to_fortytwo_block_kneading_corridor_and_two_pow_209_uniqueness`)**:
   - Crosses the 200-step binary horizon ($T_{42} = 208$) and proves $2^{209} \mid (b_2 - b_1)$
     and $2^{209} \le b_2$ for any two seeds sharing the 42-block prefix.
-/

namespace Mahler.ShiftSlackAndKneading42

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

/-! ## 1. Sections C2.O16.1 & C2.O16.2: Mixed Shift-Slack Cocycle & Universal Subword Escape Inheritance -/

/-- **Mixed Shift-Slack Cocycle $\Sigma_{N+M}(s) = 3^d \widehat{\Sigma}_N(s) + 2^{T_N} \Sigma_M(s')$
(`renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack`, Section C2.O16.1)**:
For any sequence `s : ℕ → ℕ` and any `N, M : ℕ`, setting `s' t = s (N + t)` and
`d = blockSteps s' M`:
`renewalIntSlack s (N + M) =
  (3 : ℤ) ^ d * centeredRenewalSlack s N + (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M`. -/
theorem renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack
    (s : ℕ → ℕ) (N M : ℕ) :
    let s' := fun t => s (N + t)
    let d := blockSteps s' M
    renewalIntSlack s (N + M) =
      (3 : ℤ) ^ d * centeredRenewalSlack s N +
        (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M := by
  intro s' d
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 N M).2.2
  change renewalIntSlack s (N + M) =
    (3 : ℤ) ^ d * renewalIntSlack s N -
      (2 : ℤ) ^ (blockSteps s N + 1) * (renewalNumerator s' M : ℤ) at hcoc
  have hC_def : centeredRenewalSlack s N = renewalIntSlack s N - (2 : ℤ) ^ (blockSteps s N) := rfl
  have hS'_def : renewalIntSlack s' M = (3 : ℤ) ^ d - 2 * (renewalNumerator s' M : ℤ) := rfl
  rw [hcoc, hC_def, hS'_def, pow_succ]
  ring

/-- **Universal Subword Escape Inheritance (`subCeiling_subword_escape_inheritance`, Section C2.O16.2)**:
Whenever `centeredRenewalSlack s N < 0` and the shifted subword `s' t = s (N + t)` satisfies
`renewalIntSlack s' M ≤ 0`, setting `d = blockSteps s' M`:
1. `renewalIntSlack s (N + M) ≤ -(3 : ℤ) ^ d + (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M`, and
2. `renewalIntSlack s (N + M) < 0`. -/
theorem subCeiling_subword_escape_inheritance
    {s : ℕ → ℕ} {N M : ℕ}
    (hsub : centeredRenewalSlack s N < 0)
    (hesc : renewalIntSlack (fun t => s (N + t)) M ≤ 0) :
    let s' := fun t => s (N + t)
    let d := blockSteps s' M
    renewalIntSlack s (N + M) ≤
        -(3 : ℤ) ^ d + (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M ∧
      renewalIntSlack s (N + M) < 0 := by
  intro s' d
  have hshift := renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack s N M
  change renewalIntSlack s (N + M) =
    (3 : ℤ) ^ d * centeredRenewalSlack s N +
      (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M at hshift
  have hC_le : centeredRenewalSlack s N ≤ -1 := by omega
  have h3d_pos : 0 < (3 : ℤ) ^ d := by positivity
  have h2T_pos : 0 ≤ (2 : ℤ) ^ (blockSteps s N) := by positivity
  have hmul1 : (3 : ℤ) ^ d * centeredRenewalSlack s N ≤ (3 : ℤ) ^ d * (-1) :=
    mul_le_mul_of_nonneg_left hC_le (le_of_lt h3d_pos)
  have hmul2 : (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h2T_pos hesc
  rw [hshift]
  exact ⟨by omega, by omega⟩

/-! ## 2. Section C2.O16.3: Universal Exclusion of $(2, 6, 2)$ and $(2, 6, 3, 2)$ at Arbitrary Sub-Ceiling Steps -/

/-- **Universal Exclusion of $(2, 6, 2)$ and $(2, 6, 3, 2)$ at Arbitrary Sub-Ceiling Steps
(`universal_subCeiling_two_six_two_and_two_six_three_two_forbidden`, Section C2.O16.3)**:
At any sub-ceiling step `N` (`centeredRenewalSlack s N < 0`):
1. If `s N = 2` and `s (N + 1) = 6`, then `centeredRenewalSlack s (N + 2) < 0`, and whenever
   `0 < renewalIntSlack s (N + 3)`, `3 ≤ s (N + 2)` (so $(2, 6, 2)$ is universally forbidden).
2. If `s N = 2`, `s (N + 1) = 6`, and `s (N + 2) = 3`, then `centeredRenewalSlack s (N + 3) < 0`,
   and whenever `0 < renewalIntSlack s (N + 4)`, `3 ≤ s (N + 3)` (so $(2, 6, 3, 2)$ is universally
   forbidden). -/
theorem universal_subCeiling_two_six_two_and_two_six_three_two_forbidden
    {s : ℕ → ℕ} {N : ℕ} (hsub : centeredRenewalSlack s N < 0) :
    (s N = 2 → s (N + 1) = 6 →
      centeredRenewalSlack s (N + 2) < 0 ∧
        (0 < renewalIntSlack s (N + 3) → 3 ≤ s (N + 2))) ∧
      (s N = 2 → s (N + 1) = 6 → s (N + 2) = 3 →
        centeredRenewalSlack s (N + 3) < 0 ∧
          (0 < renewalIntSlack s (N + 4) → 3 ≤ s (N + 3))) := by
  set s' := fun t => s (N + t)
  have h2T_pos : 0 < (2 : ℤ) ^ (blockSteps s N) := by positivity
  refine ⟨?_, ?_⟩
  · intro hs0 hs1
    have hs'0 : s' 0 = 2 := hs0
    have hs'1 : s' 1 = 6 := hs1
    have hd2 : blockSteps s' 2 = 8 := by simp [blockSteps, hs'0, hs'1]
    have hS2_s' : renewalIntSlack s' 2 = 217 := by
      simp [renewalIntSlack, blockSteps, renewalNumerator, hs'0, hs'1]
    have hC2_s' : centeredRenewalSlack s' 2 = -39 := by
      simp [centeredRenewalSlack, renewalIntSlack, blockSteps, renewalNumerator, hs'0, hs'1]
    have hcoc_C2 := (centeredRenewalSlack_step_and_cocycle s 0 N 2).2.2.2
    change centeredRenewalSlack s (N + 2) =
      (3 : ℤ) ^ (blockSteps s' 2) * centeredRenewalSlack s N +
        (2 : ℤ) ^ (blockSteps s N) * centeredRenewalSlack s' 2 at hcoc_C2
    rw [hd2, hC2_s'] at hcoc_C2
    have hC2_neg : centeredRenewalSlack s (N + 2) < 0 := by omega
    refine ⟨hC2_neg, ?_⟩
    intro hS3_pos
    have hshift2 := renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack s N 2
    change renewalIntSlack s (N + 2) =
      (3 : ℤ) ^ (blockSteps s' 2) * centeredRenewalSlack s N +
        (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' 2 at hshift2
    rw [hd2, hS2_s'] at hshift2
    have hS2_lt : renewalIntSlack s (N + 2) < 217 * (2 : ℤ) ^ (blockSteps s N) := by omega
    have hT_N2 : blockSteps s (N + 2) = blockSteps s N + 8 := by
      have hsh := blockSteps_add_shift s N 2
      change blockSteps s (N + 2) = blockSteps s N + blockSteps s' 2 at hsh
      rw [hsh, hd2]
    have hstep2 := (subCeiling_step_sandwich_iff s (N + 2)).1
    change renewalIntSlack s (N + 3) =
      (3 : ℤ) ^ (s (N + 2)) * renewalIntSlack s (N + 2) -
        2 * (2 : ℤ) ^ (blockSteps s (N + 2) + s (N + 2)) at hstep2
    by_contra hlt3
    have hcases : s (N + 2) = 0 ∨ s (N + 2) = 1 ∨ s (N + 2) = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [hstep2, h0, hT_N2] at hS3_pos
      have hpow : 2 * (2 : ℤ) ^ (blockSteps s N + 8 + 0) = 512 * (2 : ℤ) ^ (blockSteps s N) := by
        rw [add_zero, pow_add]
        ring
      rw [pow_zero, one_mul, hpow] at hS3_pos
      omega
    · rw [hstep2, h1, hT_N2] at hS3_pos
      have hpow : 2 * (2 : ℤ) ^ (blockSteps s N + 8 + 1) = 1024 * (2 : ℤ) ^ (blockSteps s N) := by
        rw [pow_add, pow_add]
        ring
      rw [pow_one, hpow] at hS3_pos
      omega
    · rw [hstep2, h2, hT_N2] at hS3_pos
      have hpow : 2 * (2 : ℤ) ^ (blockSteps s N + 8 + 2) = 2048 * (2 : ℤ) ^ (blockSteps s N) := by
        rw [pow_add, pow_add]
        ring
      have h3_2 : (3 : ℤ) ^ 2 = 9 := by norm_num
      rw [h3_2, hpow] at hS3_pos
      omega
  · intro hs0 hs1 hs2
    have hs'0 : s' 0 = 2 := hs0
    have hs'1 : s' 1 = 6 := hs1
    have hs'2 : s' 2 = 3 := hs2
    have hd3 : blockSteps s' 3 = 11 := by simp [blockSteps, hs'0, hs'1, hs'2]
    have hS3_s' : renewalIntSlack s' 3 = 1763 := by
      simp [renewalIntSlack, blockSteps, renewalNumerator, hs'0, hs'1, hs'2]
    have hC3_s' : centeredRenewalSlack s' 3 = -285 := by
      simp [centeredRenewalSlack, renewalIntSlack, blockSteps, renewalNumerator, hs'0, hs'1, hs'2]
    have hcoc_C3 := (centeredRenewalSlack_step_and_cocycle s 0 N 3).2.2.2
    change centeredRenewalSlack s (N + 3) =
      (3 : ℤ) ^ (blockSteps s' 3) * centeredRenewalSlack s N +
        (2 : ℤ) ^ (blockSteps s N) * centeredRenewalSlack s' 3 at hcoc_C3
    rw [hd3, hC3_s'] at hcoc_C3
    have hC3_neg : centeredRenewalSlack s (N + 3) < 0 := by omega
    refine ⟨hC3_neg, ?_⟩
    intro hS4_pos
    have hshift3 := renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack s N 3
    change renewalIntSlack s (N + 3) =
      (3 : ℤ) ^ (blockSteps s' 3) * centeredRenewalSlack s N +
        (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' 3 at hshift3
    rw [hd3, hS3_s'] at hshift3
    have hS3_lt : renewalIntSlack s (N + 3) < 1763 * (2 : ℤ) ^ (blockSteps s N) := by omega
    have hT_N3 : blockSteps s (N + 3) = blockSteps s N + 11 := by
      have hsh := blockSteps_add_shift s N 3
      change blockSteps s (N + 3) = blockSteps s N + blockSteps s' 3 at hsh
      rw [hsh, hd3]
    have hstep3 := (subCeiling_step_sandwich_iff s (N + 3)).1
    change renewalIntSlack s (N + 4) =
      (3 : ℤ) ^ (s (N + 3)) * renewalIntSlack s (N + 3) -
        2 * (2 : ℤ) ^ (blockSteps s (N + 3) + s (N + 3)) at hstep3
    by_contra hlt3
    have hcases : s (N + 3) = 0 ∨ s (N + 3) = 1 ∨ s (N + 3) = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [hstep3, h0, hT_N3] at hS4_pos
      have hpow : 2 * (2 : ℤ) ^ (blockSteps s N + 11 + 0) = 4096 * (2 : ℤ) ^ (blockSteps s N) := by
        rw [add_zero, pow_add]
        ring
      rw [pow_zero, one_mul, hpow] at hS4_pos
      omega
    · rw [hstep3, h1, hT_N3] at hS4_pos
      have hpow : 2 * (2 : ℤ) ^ (blockSteps s N + 11 + 1) = 8192 * (2 : ℤ) ^ (blockSteps s N) := by
        rw [pow_add, pow_add]
        ring
      rw [pow_one, hpow] at hS4_pos
      omega
    · rw [hstep3, h2, hT_N3] at hS4_pos
      have hpow : 2 * (2 : ℤ) ^ (blockSteps s N + 11 + 2) = 16384 * (2 : ℤ) ^ (blockSteps s N) := by
        rw [pow_add, pow_add]
        ring
      have h3_2 : (3 : ℤ) ^ 2 = 9 := by norm_num
      rw [h3_2, hpow] at hS4_pos
      omega

/-! ## 3. Sections C2.O16.4 & C2.O16.5: Certification of Blocks 40, 41, and 42 ($T_{42} = 208$) & Mod-$2^{209}$ Uniqueness -/

/-- **Certification of the 40th ($s_{39} = 5$), 41st ($s_{40} = 4$), and 42nd ($s_{41} = 11$) Kneading Rungs & Mod-$2^{209}$ Uniqueness
(`forty_to_fortytwo_block_kneading_corridor_and_two_pow_209_uniqueness`, Sections C2.O16.4–C2.O16.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 39-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4, 6, 6, 3, 3, 3, 3)$:
1. `(0 < renewalIntSlack s 40 ∧ centeredRenewalSlack s 40 < 0) ↔ s 39 = 5`,
2. When `s 39 = 5`: `blockSteps s 40 = 193`,
   `renewalIntSlack s 40 = 5022694395181773286585404118082582947874518957604893168043`,
   `centeredRenewalSlack s 40 = -7531509075591588241086174728332749884330191931323175857749`, and
   `(0 < renewalIntSlack s 41 ∧ centeredRenewalSlack s 41 < 0) ↔ s 40 = 4`,
3. When `s 39 = 5` and `s 40 = 4`: `blockSteps s 41 = 197`,
   `renewalIntSlack s 41 = 5103734944976067327927210479398568147285287120298137786139`,
   `centeredRenewalSlack s 41 = -195763520587397717114818051063246757167990087102550966626533`, and
   `(0 < renewalIntSlack s 42 ∧ centeredRenewalSlack s 42 < 0) ↔ s 41 = 11`,
4. When `s 39 = 5`, `s 40 = 4`, and `s 41 = 11`: `blockSteps s 42 = 208`,
   `renewalIntSlack s 42 = 81359055637072377862836963515342899095778824682664282726860921`,
   `centeredRenewalSlack s 42 = -330017083693229132675905332123994727149905141725730683110291335`,
   and any two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 42` satisfy `2 ^ 209 ∣ (b₂ - b₁)`
   and `2 ^ 209 ≤ b₂`. -/
theorem forty_to_fortytwo_block_kneading_corridor_and_two_pow_209_uniqueness
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
    (hs36 : s 36 = 3) (hs37 : s 37 = 3) (hs38 : s 38 = 3) :
    ((0 < renewalIntSlack s 40 ∧ centeredRenewalSlack s 40 < 0) ↔ s 39 = 5) ∧
      (s 39 = 5 →
        blockSteps s 40 = 193 ∧
          renewalIntSlack s 40 = 5022694395181773286585404118082582947874518957604893168043 ∧
          centeredRenewalSlack s 40 = -7531509075591588241086174728332749884330191931323175857749 ∧
          ((0 < renewalIntSlack s 41 ∧ centeredRenewalSlack s 41 < 0) ↔ s 40 = 4)) ∧
      (s 39 = 5 → s 40 = 4 →
        blockSteps s 41 = 197 ∧
          renewalIntSlack s 41 = 5103734944976067327927210479398568147285287120298137786139 ∧
          centeredRenewalSlack s 41 = -195763520587397717114818051063246757167990087102550966626533 ∧
          ((0 < renewalIntSlack s 42 ∧ centeredRenewalSlack s 42 < 0) ↔ s 41 = 11)) ∧
      (s 39 = 5 → s 40 = 4 → s 41 = 11 →
        blockSteps s 42 = 208 ∧
          renewalIntSlack s 42 = 81359055637072377862836963515342899095778824682664282726860921 ∧
          centeredRenewalSlack s 42 = -330017083693229132675905332123994727149905141725730683110291335 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 42 →
              ValidBlockChain b₂ s u₂ 42 →
                2 ^ 209 ∣ (b₂ - b₁) ∧ 2 ^ 209 ≤ b₂)) := by
  have hprev :=
    (thirtyseven_to_thirtynine_block_kneading_corridor_and_two_pow_189_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32 hs33 hs34 hs35).2.2.2
      hs36 hs37 hs38
  have hT39 : blockSteps s 39 = 188 := hprev.1
  have hS39 : renewalIntSlack s 39 = 123996301797236610460611365477009253548493583273502186089 := hprev.2.1
  have hstep39 := subCeiling_step_sandwich_iff s 39
  have hiff39 :
      (0 < renewalIntSlack s 40 ∧ centeredRenewalSlack s 40 < 0) ↔ s 39 = 5 := by
    have hsand39 := hstep39.2.2
    rw [hT39, hS39] at hsand39
    exact hsand39.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 123996301797236610460611365477009253548493583273502186089) (T_N := 188) (s_star := 5)
      (by norm_num) (by norm_num) (s 39)).1
  have h40_vals :
      s 39 = 5 →
        blockSteps s 40 = 193 ∧
          renewalIntSlack s 40 = 5022694395181773286585404118082582947874518957604893168043 ∧
          centeredRenewalSlack s 40 = -7531509075591588241086174728332749884330191931323175857749 := by
    intro hs39
    have hT40 : blockSteps s 40 = 193 := by
      change blockSteps s 39 + s 39 = 193
      rw [hT39, hs39]
    have hS40 : renewalIntSlack s 40 = 5022694395181773286585404118082582947874518957604893168043 := by
      have h1 := hstep39.1
      rw [h1, hT39, hS39, hs39]
      norm_num
    have hC40 : centeredRenewalSlack s 40 = -7531509075591588241086174728332749884330191931323175857749 := by
      have h2 := hstep39.2.1
      rw [h2, hT39, hS39, hs39]
      norm_num
    exact ⟨hT40, hS40, hC40⟩
  have h41_vals :
      s 39 = 5 → s 40 = 4 →
        blockSteps s 41 = 197 ∧
          renewalIntSlack s 41 = 5103734944976067327927210479398568147285287120298137786139 ∧
          centeredRenewalSlack s 41 = -195763520587397717114818051063246757167990087102550966626533 := by
    intro hs39 hs40
    obtain ⟨hT40, hS40, _⟩ := h40_vals hs39
    have hstep40 := subCeiling_step_sandwich_iff s 40
    have hT41 : blockSteps s 41 = 197 := by
      change blockSteps s 40 + s 40 = 197
      rw [hT40, hs40]
    have hS41 : renewalIntSlack s 41 = 5103734944976067327927210479398568147285287120298137786139 := by
      have h1 := hstep40.1
      rw [h1, hT40, hS40, hs40]
      norm_num
    have hC41 : centeredRenewalSlack s 41 = -195763520587397717114818051063246757167990087102550966626533 := by
      have h2 := hstep40.2.1
      rw [h2, hT40, hS40, hs40]
      norm_num
    exact ⟨hT41, hS41, hC41⟩
  refine ⟨hiff39, ?_, ?_, ?_⟩
  · intro hs39
    obtain ⟨hT40, hS40, hC40⟩ := h40_vals hs39
    have hsand40 := (subCeiling_step_sandwich_iff s 40).2.2
    rw [hT40, hS40] at hsand40
    refine ⟨hT40, hS40, hC40, ?_⟩
    exact hsand40.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 5022694395181773286585404118082582947874518957604893168043) (T_N := 193) (s_star := 4)
      (by norm_num) (by norm_num) (s 40)).1
  · intro hs39 hs40
    obtain ⟨hT41, hS41, hC41⟩ := h41_vals hs39 hs40
    have hsand41 := (subCeiling_step_sandwich_iff s 41).2.2
    rw [hT41, hS41] at hsand41
    refine ⟨hT41, hS41, hC41, ?_⟩
    exact hsand41.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 5103734944976067327927210479398568147285287120298137786139) (T_N := 197) (s_star := 11)
      (by norm_num) (by norm_num) (s 41)).1
  · intro hs39 hs40 hs41
    obtain ⟨hT41, hS41, _⟩ := h41_vals hs39 hs40
    have hstep41 := subCeiling_step_sandwich_iff s 41
    have hT42 : blockSteps s 42 = 208 := by
      change blockSteps s 41 + s 41 = 208
      rw [hT41, hs41]
    have hS42 : renewalIntSlack s 42 = 81359055637072377862836963515342899095778824682664282726860921 := by
      have h1 := hstep41.1
      rw [h1, hT41, hS41, hs41]
      norm_num
    have hC42 : centeredRenewalSlack s 42 = -330017083693229132675905332123994727149905141725730683110291335 := by
      have h2 := hstep41.2.1
      rw [h2, hT41, hS41, hs41]
      norm_num
    refine ⟨hT42, hS42, hC42, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 42) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 42 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT42] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 209 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.ShiftSlackAndKneading42
