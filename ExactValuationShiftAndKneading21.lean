import DyadicTriadicRungPartitionAndKneading18

/-!
# Sharpened $2^{T_{K+1}+1}$ Exact Valuation Shift, Mod-512 $(2, 6)$ Corridor Law, Two-Step $(4, 2)$ Window & 21-Block ($T_{21} = 105$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 9 / 20 (Part XXIV, Sections C2.O9.1–C2.O9.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O9.1 (Inner Loop 1 / 5) — First-Block Factoring of `renewalNumerator`
   (`renewalNumerator_succ_split_factor`)**:
   - For any sequence `s : ℕ → ℕ` and horizon `m : ℕ`, setting `s1 t = s (1 + t)` and
     `d_m = blockSteps s1 m`:
     `renewalNumerator s (1 + m) = 2 ^ (s 0) * (3 ^ d_m + renewalNumerator s1 m)`.
   - Whenever `1 ≤ s 0`, `2 ^ (s 0) ∣ renewalNumerator s (1 + m)` and
     `renewalNumerator s (1 + m) % 2 = 0`.

2. **Section C2.O9.2 & C2.O9.3 (Inner Loops 2–3 / 5) — Sharpened $2^{T_{K+1}+1}$ Exact Valuation Shift for $\Sigma_N$ & Mod-512 $(2, 6)$ Corridor Law
   (`renewalIntSlack_sharpened_two_pow_next_step_factor`, `two_six_corridor_mod_512_slack_congruence`)**:
   - For any `K, m : ℕ`, setting `s1 t = s (K + 1 + t)` and `d_m = blockSteps s1 m`:
     `(3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K - renewalIntSlack s (K + 1 + m) =
       (2 : ℤ) ^ (blockSteps s (K + 1) + 1) * ((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ))`,
     where the cofactor `(3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ)` is odd whenever
     `m = 0 ∨ 1 ≤ s (K + 1)`.
   - On any sequence with `s 0 = 2` and `s 1 = 6`, for all `m : ℕ`:
     `(512 : ℤ) ∣ ((3 : ℤ) ^ (blockSteps s (2 + m) - 2) - renewalIntSlack s (2 + m))`.

3. **Section C2.O9.4 (Inner Loop 4 / 5) — Universal Two-Step $(s_N = 4, s_{N+1} = 2)$ Sub-Ceiling Window
   (`subCeiling_two_step_four_two_window`)**:
   - When `s N = 4` and `s (N + 1) = 2`,
     `renewalIntSlack s (N + 2) = 729 * S_N - 416 * (2 : ℤ) ^ T_N`,
     `centeredRenewalSlack s (N + 2) = 729 * S_N - 480 * (2 : ℤ) ^ T_N`, and both steps `N + 1`
     and `N + 2` remain sub-ceiling if and only if
     `416 * (2 : ℤ) ^ T_N < 729 * S_N ∧ 81 * S_N < 48 * (2 : ℤ) ^ T_N`.

4. **Section C2.O9.5 (Inner Loop 5 / 5) — Certification of Blocks 19, 20, and 21 ($s_{18} = 5, s_{19} = 7, s_{20} = 4$, $T_{21} = 105$) & Mod-$2^{106}$ Uniqueness
   (`nineteen_to_twentyone_block_kneading_corridor_and_two_pow_106_uniqueness`)**:
   - Crosses the 100-step binary horizon ($T_{20} = 101, T_{21} = 105$) and proves that any two
     seeds $b_1 < b_2$ sharing this 21-block prefix satisfy $2^{106} \mid (b_2 - b_1)$ and
     $2^{106} \le b_2$.
-/

namespace Mahler.ExactValuationAndKneading21

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

/-! ## 1. Section C2.O9.1: First-Block Factoring of `renewalNumerator` -/

/-- **First-Block Factoring of `renewalNumerator`
(`renewalNumerator_succ_split_factor`, Section C2.O9.1)**:
For any sequence `s : ℕ → ℕ` and horizon `m : ℕ`, setting `s1 t = s (1 + t)` and
`d_m = blockSteps s1 m`:
1. `renewalNumerator s (1 + m) = 2 ^ (s 0) * (3 ^ d_m + renewalNumerator s1 m)`, and
2. Whenever `1 ≤ s 0`, `2 ^ (s 0) ∣ renewalNumerator s (1 + m)` and
   `renewalNumerator s (1 + m) % 2 = 0`. -/
theorem renewalNumerator_succ_split_factor (s : ℕ → ℕ) (m : ℕ) :
    let s1 := fun t => s (1 + t)
    let d_m := blockSteps s1 m
    renewalNumerator s (1 + m) = 2 ^ (s 0) * (3 ^ d_m + renewalNumerator s1 m) ∧
      (1 ≤ s 0 →
        2 ^ (s 0) ∣ renewalNumerator s (1 + m) ∧
          renewalNumerator s (1 + m) % 2 = 0) := by
  intro s1 d_m
  have hcomp := renewalNumerator_cocycle_composition s 1 m
  have hT1 : blockSteps s 1 = s 0 := by simp [blockSteps]
  have hA1 : renewalNumerator s 1 = 2 ^ (s 0) := by simp [renewalNumerator, blockSteps]
  have hid : renewalNumerator s (1 + m) = 2 ^ (s 0) * (3 ^ d_m + renewalNumerator s1 m) := by
    change renewalNumerator s (1 + m) =
      3 ^ d_m * renewalNumerator s 1 + 2 ^ (blockSteps s 1) * renewalNumerator s1 m at hcomp
    rw [hcomp, hT1, hA1]
    ring
  refine ⟨hid, ?_⟩
  intro hs0
  refine ⟨⟨3 ^ d_m + renewalNumerator s1 m, hid⟩, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s 0 = k + 1 := ⟨s 0 - 1, by omega⟩
  have hmul2 :
      2 ^ (s 0) * (3 ^ d_m + renewalNumerator s1 m) =
        2 * (2 ^ k * (3 ^ d_m + renewalNumerator s1 m)) := by
    rw [hk, Nat.pow_succ]
    ring
  rw [hid, hmul2]
  omega

/-! ## 2. Sections C2.O9.2 & C2.O9.3: Sharpened $2^{T_{K+1}+1}$ Exact Valuation Shift & Mod-512 Law -/

/-- **Sharpened $2^{T_{K+1}+1}$ Exact Valuation Shift for $\Sigma_N$
(`renewalIntSlack_sharpened_two_pow_next_step_factor`, Section C2.O9.2)**:
For any sequence `s : ℕ → ℕ` and any `K, m : ℕ`, setting `s1 t = s (K + 1 + t)` and
`d_m = blockSteps s1 m`:
1. `(3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K - renewalIntSlack s (K + 1 + m) =
     (2 : ℤ) ^ (blockSteps s (K + 1) + 1) * ((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ))`,
2. `((2 : ℤ) ^ (blockSteps s (K + 1) + 1)) ∣
     ((3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K - renewalIntSlack s (K + 1 + m))`, and
3. Whenever `m = 0 ∨ 1 ≤ s (K + 1)`,
   `(((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ)) % 2) = 1`. -/
theorem renewalIntSlack_sharpened_two_pow_next_step_factor
    (s : ℕ → ℕ) (K m : ℕ) :
    let s1 := fun t => s (K + 1 + t)
    let d_m := blockSteps s1 m
    (3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K - renewalIntSlack s (K + 1 + m) =
      (2 : ℤ) ^ (blockSteps s (K + 1) + 1) * ((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ)) ∧
      ((2 : ℤ) ^ (blockSteps s (K + 1) + 1)) ∣
        ((3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K - renewalIntSlack s (K + 1 + m)) ∧
      ((m = 0 ∨ 1 ≤ s (K + 1)) →
        (((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ)) % 2) = 1) := by
  intro s1 d_m
  set s0 := fun t => s (K + t)
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 K (1 + m)).2.2
  have hsplit := (renewalNumerator_succ_split_factor s0 m).1
  have hs0_shift : (fun t => s0 (1 + t)) = s1 := by
    funext t
    dsimp [s0, s1]
    rw [Nat.add_assoc]
  have hd_eq : blockSteps s0 (1 + m) = s K + d_m := by
    have hsh := blockSteps_add_shift s0 1 m
    have h1 : blockSteps s0 1 = s K := by simp [blockSteps, s0]
    rw [hsh, h1, hs0_shift]
  have hA_eq : renewalNumerator s0 (1 + m) = 2 ^ (s K) * (3 ^ d_m + renewalNumerator s1 m) := by
    change renewalNumerator s0 (1 + m) =
      2 ^ (s0 0) * (3 ^ (blockSteps (fun t => s0 (1 + t)) m) +
        renewalNumerator (fun t => s0 (1 + t)) m) at hsplit
    rw [hs0_shift] at hsplit
    exact hsplit
  have hTK1 : blockSteps s (K + 1) = blockSteps s K + s K := rfl
  have hid :
      (3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K - renewalIntSlack s (K + 1 + m) =
        (2 : ℤ) ^ (blockSteps s (K + 1) + 1) * ((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ)) := by
    have hassoc : K + (1 + m) = K + 1 + m := by omega
    rw [← hassoc, hcoc]
    change (3 : ℤ) ^ (s K + d_m) * renewalIntSlack s K -
      ((3 : ℤ) ^ (blockSteps s0 (1 + m)) * renewalIntSlack s K -
        (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator s0 (1 + m) : ℤ)) =
      (2 : ℤ) ^ (blockSteps s (K + 1) + 1) * ((3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ))
    rw [hd_eq, hA_eq, hTK1]
    push_cast
    simp only [pow_add, pow_succ]
    ring
  refine ⟨hid, ⟨(3 : ℤ) ^ d_m + (renewalNumerator s1 m : ℤ), hid⟩, ?_⟩
  intro hcond
  have h3_odd : ((3 : ℤ) ^ d_m) % 2 = 1 := int_three_pow_mod_two_eq_one d_m
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · have hA0 : renewalNumerator s1 0 = 0 := rfl
    rw [hA0]
    omega
  · rcases hcond with rfl | hsK1
    · omega
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = 1 + j := ⟨m - 1, by omega⟩
      have h0_s1 : 1 ≤ s1 0 := by
        dsimp [s1]
        exact hsK1
      have heven_nat : renewalNumerator s1 (1 + j) % 2 = 0 :=
        ((renewalNumerator_succ_split_factor s1 j).2 h0_s1).2
      have heven_int : ((renewalNumerator s1 (1 + j) : ℤ) % 2) = 0 := by
        exact_mod_cast heven_nat
      omega

/-- **Universal Mod-512 Law on the $(2, 6)$ Sub-Ceiling Corridor
(`two_six_corridor_mod_512_slack_congruence`, Section C2.O9.3)**:
For any sequence `s : ℕ → ℕ` with `s 0 = 2` and `s 1 = 6`, and any `m : ℕ`:
`(512 : ℤ) ∣ ((3 : ℤ) ^ (blockSteps s (2 + m) - 2) - renewalIntSlack s (2 + m))`. -/
theorem two_six_corridor_mod_512_slack_congruence
    {s : ℕ → ℕ} (hs0 : s 0 = 2) (hs1 : s 1 = 6) (m : ℕ) :
    (512 : ℤ) ∣ ((3 : ℤ) ^ (blockSteps s (2 + m) - 2) - renewalIntSlack s (2 + m)) := by
  have hsharp := (renewalIntSlack_sharpened_two_pow_next_step_factor s 1 m).2.1
  have hT1 : blockSteps s 1 = 2 := by simp [blockSteps, hs0]
  have hT2 : blockSteps s 2 = 8 := by simp [blockSteps, hs0, hs1]
  have hS1 : renewalIntSlack s 1 = 1 := by
    have hstep0 := renewalIntSlack_step_and_cocycle s 0 0 0
    rw [hstep0.2.1, hstep0.1, hT1, hs0]
    norm_num
  have hsh := blockSteps_add_shift s 2 m
  rw [hT2] at hsh
  have hd : s 1 + blockSteps (fun t => s (1 + 1 + t)) m = blockSteps s (2 + m) - 2 := by
    change s 1 + blockSteps (fun t => s (2 + t)) m = blockSteps s (2 + m) - 2
    omega
  change ((2 : ℤ) ^ (blockSteps s 2 + 1)) ∣
    ((3 : ℤ) ^ (s 1 + blockSteps (fun t => s (1 + 1 + t)) m) * renewalIntSlack s 1 -
      renewalIntSlack s (2 + m)) at hsharp
  rw [hT2, hS1, hd, mul_one] at hsharp
  norm_num at hsharp
  exact hsharp

/-! ## 3. Section C2.O9.4: Universal Two-Step $(s_N = 4, s_{N+1} = 2)$ Sub-Ceiling Window -/

/-- **Universal Two-Step $(s_N = 4, s_{N+1} = 2)$ Sub-Ceiling Window
(`subCeiling_two_step_four_two_window`, Section C2.O9.4)**:
For any sequence `s : ℕ → ℕ` and index `N : ℕ`, setting `T_N = blockSteps s N` and
`S_N = renewalIntSlack s N`, whenever `s N = 4` and `s (N + 1) = 2`:
1. `renewalIntSlack s (N + 2) = 729 * S_N - 416 * (2 : ℤ) ^ T_N`,
2. `centeredRenewalSlack s (N + 2) = 729 * S_N - 480 * (2 : ℤ) ^ T_N`, and
3. `(((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ∧
      (0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0)) ↔
     (416 * (2 : ℤ) ^ T_N < 729 * S_N ∧ 81 * S_N < 48 * (2 : ℤ) ^ T_N))`. -/
theorem subCeiling_two_step_four_two_window
    {s : ℕ → ℕ} {N : ℕ} (hs4 : s N = 4) (hs_next : s (N + 1) = 2) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    renewalIntSlack s (N + 2) = 729 * S_N - 416 * (2 : ℤ) ^ T_N ∧
      centeredRenewalSlack s (N + 2) = 729 * S_N - 480 * (2 : ℤ) ^ T_N ∧
      (((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ∧
          (0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0)) ↔
        (416 * (2 : ℤ) ^ T_N < 729 * S_N ∧ 81 * S_N < 48 * (2 : ℤ) ^ T_N)) := by
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
  have hT1 : blockSteps s (N + 1) = T_N + 4 := by simp [blockSteps, T_N, hs4]
  have hS1' : renewalIntSlack s (N + 1) = 81 * S_N - 32 * (2 : ℤ) ^ T_N := by
    rw [hS1, hs4, pow_add]
    ring
  have hC1' : centeredRenewalSlack s (N + 1) = 81 * S_N - 48 * (2 : ℤ) ^ T_N := by
    rw [hC1, hs4, pow_add]
    ring
  have hS2' : renewalIntSlack s (N + 2) = 729 * S_N - 416 * (2 : ℤ) ^ T_N := by
    rw [hS2, hs_next, hT1, hS1', pow_add]
    ring
  have hC2' : centeredRenewalSlack s (N + 2) = 729 * S_N - 480 * (2 : ℤ) ^ T_N := by
    rw [hC2, hs_next, hT1, hS1', pow_add]
    ring
  clear hS1 hC1 hS2 hC2 hT1
  refine ⟨hS2', hC2', ?_⟩
  rw [hS1', hC1', hS2', hC2']
  have hpos : 0 < (2 : ℤ) ^ T_N := by positivity
  constructor <;> intro h <;> omega

/-! ## 4. Section C2.O9.5: Certification of Blocks 19, 20, and 21 ($T_{21} = 105$) & Mod-$2^{106}$ Uniqueness -/

/-- **Certification of the 19th ($s_{18} = 5$), 20th ($s_{19} = 7$), and 21st ($s_{20} = 4$) Kneading Rungs & Mod-$2^{106}$ Uniqueness
(`nineteen_to_twentyone_block_kneading_corridor_and_two_pow_106_uniqueness`, Section C2.O9.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 18-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6)$:
1. `(0 < renewalIntSlack s 19 ∧ centeredRenewalSlack s 19 < 0) ↔ s 18 = 5`,
2. When `s 18 = 5`: `blockSteps s 19 = 94`,
   `renewalIntSlack s 19 = 2877581691087272240083978801`,
   `centeredRenewalSlack s 19 = -16929458937478812158302008783`, and
   `(0 < renewalIntSlack s 20 ∧ centeredRenewalSlack s 20 < 0) ↔ s 19 = 7`,
3. When `s 18 = 5` and `s 19 = 7`: `blockSteps s 20 = 101`,
   `renewalIntSlack s 20 = 1222668757494946783076848816283`,
   `centeredRenewalSlack s 20 = -1312632442961512019916557594469`, and
   `(0 < renewalIntSlack s 21 ∧ centeredRenewalSlack s 21 < 0) ↔ s 20 = 4`,
4. When `s 18 = 5`, `s 19 = 7`, and `s 20 = 4`: `blockSteps s 21 = 105`,
   `renewalIntSlack s 21 = 17906530942484007733435748974859`,
   `centeredRenewalSlack s 21 = -22658288264819333114458753597173`, and any two seeds `b₁ < b₂`
   realizing `ValidBlockChain bᵢ s uᵢ 21` satisfy `2 ^ 106 ∣ (b₂ - b₁)` and `2 ^ 106 ≤ b₂`. -/
theorem nineteen_to_twentyone_block_kneading_corridor_and_two_pow_106_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) :
    ((0 < renewalIntSlack s 19 ∧ centeredRenewalSlack s 19 < 0) ↔ s 18 = 5) ∧
      (s 18 = 5 →
        blockSteps s 19 = 94 ∧
          renewalIntSlack s 19 = 2877581691087272240083978801 ∧
          centeredRenewalSlack s 19 = -16929458937478812158302008783 ∧
          ((0 < renewalIntSlack s 20 ∧ centeredRenewalSlack s 20 < 0) ↔ s 19 = 7)) ∧
      (s 18 = 5 → s 19 = 7 →
        blockSteps s 20 = 101 ∧
          renewalIntSlack s 20 = 1222668757494946783076848816283 ∧
          centeredRenewalSlack s 20 = -1312632442961512019916557594469 ∧
          ((0 < renewalIntSlack s 21 ∧ centeredRenewalSlack s 21 < 0) ↔ s 20 = 4)) ∧
      (s 18 = 5 → s 19 = 7 → s 20 = 4 →
        blockSteps s 21 = 105 ∧
          renewalIntSlack s 21 = 17906530942484007733435748974859 ∧
          centeredRenewalSlack s 21 = -22658288264819333114458753597173 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 21 →
              ValidBlockChain b₂ s u₂ 21 →
                2 ^ 106 ∣ (b₂ - b₁) ∧ 2 ^ 106 ≤ b₂)) := by
  have hprev :=
    (sixteen_to_eighteen_block_kneading_corridor_and_two_pow_90_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14).2.2.2 hs15 hs16 hs17
  have hT18 : blockSteps s 18 = 89 := hprev.1
  have hS18 : renewalIntSlack s 18 = 174862810486499757353316683 := hprev.2.1
  have hstep18 := subCeiling_step_sandwich_iff s 18
  have hiff18 :
      (0 < renewalIntSlack s 19 ∧ centeredRenewalSlack s 19 < 0) ↔ s 18 = 5 := by
    have hsand18 := hstep18.2.2
    rw [hT18, hS18] at hsand18
    exact hsand18.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 174862810486499757353316683) (T_N := 89) (s_star := 5)
      (by norm_num) (by norm_num) (s 18)).1
  have h19_vals :
      s 18 = 5 →
        blockSteps s 19 = 94 ∧
          renewalIntSlack s 19 = 2877581691087272240083978801 ∧
          centeredRenewalSlack s 19 = -16929458937478812158302008783 := by
    intro hs18
    have hT19 : blockSteps s 19 = 94 := by
      change blockSteps s 18 + s 18 = 94
      rw [hT18, hs18]
    have hS19 : renewalIntSlack s 19 = 2877581691087272240083978801 := by
      have h1 := hstep18.1
      rw [h1, hT18, hS18, hs18]
      norm_num
    have hC19 : centeredRenewalSlack s 19 = -16929458937478812158302008783 := by
      have h2 := hstep18.2.1
      rw [h2, hT18, hS18, hs18]
      norm_num
    exact ⟨hT19, hS19, hC19⟩
  have h20_vals :
      s 18 = 5 → s 19 = 7 →
        blockSteps s 20 = 101 ∧
          renewalIntSlack s 20 = 1222668757494946783076848816283 ∧
          centeredRenewalSlack s 20 = -1312632442961512019916557594469 := by
    intro hs18 hs19
    obtain ⟨hT19, hS19, _⟩ := h19_vals hs18
    have hstep19 := subCeiling_step_sandwich_iff s 19
    have hT20 : blockSteps s 20 = 101 := by
      change blockSteps s 19 + s 19 = 101
      rw [hT19, hs19]
    have hS20 : renewalIntSlack s 20 = 1222668757494946783076848816283 := by
      have h1 := hstep19.1
      rw [h1, hT19, hS19, hs19]
      norm_num
    have hC20 : centeredRenewalSlack s 20 = -1312632442961512019916557594469 := by
      have h2 := hstep19.2.1
      rw [h2, hT19, hS19, hs19]
      norm_num
    exact ⟨hT20, hS20, hC20⟩
  refine ⟨hiff18, ?_, ?_, ?_⟩
  · intro hs18
    obtain ⟨hT19, hS19, hC19⟩ := h19_vals hs18
    have hsand19 := (subCeiling_step_sandwich_iff s 19).2.2
    rw [hT19, hS19] at hsand19
    refine ⟨hT19, hS19, hC19, ?_⟩
    exact hsand19.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 2877581691087272240083978801) (T_N := 94) (s_star := 7)
      (by norm_num) (by norm_num) (s 19)).1
  · intro hs18 hs19
    obtain ⟨hT20, hS20, hC20⟩ := h20_vals hs18 hs19
    have hsand20 := (subCeiling_step_sandwich_iff s 20).2.2
    rw [hT20, hS20] at hsand20
    refine ⟨hT20, hS20, hC20, ?_⟩
    exact hsand20.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 1222668757494946783076848816283) (T_N := 101) (s_star := 4)
      (by norm_num) (by norm_num) (s 20)).1
  · intro hs18 hs19 hs20
    obtain ⟨hT20, hS20, _⟩ := h20_vals hs18 hs19
    have hstep20 := subCeiling_step_sandwich_iff s 20
    have hT21 : blockSteps s 21 = 105 := by
      change blockSteps s 20 + s 20 = 105
      rw [hT20, hs20]
    have hS21 : renewalIntSlack s 21 = 17906530942484007733435748974859 := by
      have h1 := hstep20.1
      rw [h1, hT20, hS20, hs20]
      norm_num
    have hC21 : centeredRenewalSlack s 21 = -22658288264819333114458753597173 := by
      have h2 := hstep20.2.1
      rw [h2, hT20, hS20, hs20]
      norm_num
    refine ⟨hT21, hS21, hC21, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 21) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 21 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT21] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 106 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.ExactValuationAndKneading21
