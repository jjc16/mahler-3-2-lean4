import ExtraBitBackwardPropagationAndKneading15

/-!
# Dyadic-Triadic Rung Partition, Two-Step $(3, 2)$ Window, 2-Adic Prefix Congruence & 18-Block ($T_{18} = 89$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 8 / 20 (Part XXIII, Sections C2.O8.1–C2.O8.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O8.1 (Inner Loop 1 / 5) — Dyadic-Triadic Partition Characterization of the Sub-Ceiling Window & Non-Vanishing Boundaries
   (`subCeiling_dyadic_triadic_partition_and_odd_boundary_non_vanishing`)**:
   - For any sequence `s : ℕ → ℕ` and index `N : ℕ` with `1 ≤ s N`, setting `T_N = blockSteps s N`
     and `S_N = renewalIntSlack s N`:
     `(0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
       ((2 : ℤ) ^ (T_N + s N + 1) < (3 : ℤ) ^ (s N) * S_N ∧
         (3 : ℤ) ^ (s N - 1) * S_N < (2 : ℤ) ^ (T_N + s N))`.
   - Whenever `S_N % 2 = 1` and `1 ≤ T_N + m`, the shared boundary between rung `m` and rung `m - 1`
     cannot be hit: `(3 : ℤ) ^ (m - 1) * S_N ≠ (2 : ℤ) ^ (T_N + m)`.

2. **Section C2.O8.2 & C2.O8.3 (Inner Loops 2–3 / 5) — Exact Sub-Ceiling Rung-$2$ Criterion & Two-Step $(s_N = 3, s_{N+1} = 2)$ Window
   (`subCeiling_rung_eq_two_iff_and_two_step_three_two_window`)**:
   - In any sub-ceiling state (`centeredRenewalSlack s N < 0`), choosing `s N = 2` forces
     `centeredRenewalSlack s (N + 1) ≤ -3 * (2 : ℤ) ^ T_N - 9 < 0`, so `s N = 2` is sub-ceiling
     at step `N + 1` if and only if `8 * (2 : ℤ) ^ T_N < 9 * S_N`.
   - When `s N = 3` and `s (N + 1) = 2`,
     `renewalIntSlack s (N + 2) = 243 * S_N - 208 * (2 : ℤ) ^ T_N`,
     `centeredRenewalSlack s (N + 2) = 243 * S_N - 240 * (2 : ℤ) ^ T_N`, and both steps `N + 1`
     and `N + 2` lie in the sub-ceiling corridor if and only if
     `208 * (2 : ℤ) ^ T_N < 243 * S_N ∧ 27 * S_N < 24 * (2 : ℤ) ^ T_N`
     (i.e. $S_N / 2^{T_N} \in (208/243, 216/243)$).

3. **Section C2.O8.4 (Inner Loop 4 / 5) — 2-Adic Prefix Congruence $2^{T_K+1} \mid (3^d \Sigma_K - \Sigma_{K+M})$ and Mod-8 Law
   (`renewalIntSlack_two_adic_prefix_congruence_and_mod_eight`)**:
   - For all `K, M : ℕ` with `d = blockSteps (fun t => s (K + t)) M`,
     `(3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M) =
       (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator (fun t => s (K + t)) M : ℤ)` and
     `((2 : ℤ) ^ (blockSteps s K + 1)) ∣ ((3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M))`.
   - When `s 0 = 2` and `1 ≤ N`, `(8 : ℤ) ∣ ((3 : ℤ) ^ (blockSteps s N - 2) - renewalIntSlack s N)`.

4. **Section C2.O8.5 (Inner Loop 5 / 5) — Certification of Blocks 16, 17, and 18 ($s_{15} = 8, s_{16} = 3, s_{17} = 6$, $T_{18} = 89$) & Mod-$2^{90}$ Uniqueness
   (`sixteen_to_eighteen_block_kneading_corridor_and_two_pow_90_uniqueness`)**:
   - Certifies $s_{15} = 8$ ($T_{16} = 80$), $s_{16} = 3$ ($T_{17} = 83$), and $s_{17} = 6$ ($T_{18} = 89$),
     together with $2^{90} \mid (b_2 - b_1)$ and $2^{90} \le b_2$ for any two seeds sharing the
     18-block prefix.
-/

namespace Mahler.DyadicTriadicAndKneading18

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

/-! ## 1. Section C2.O8.1: Dyadic-Triadic Partition Characterization of the Sub-Ceiling Window -/

/-- Auxiliary oddness lemma: `(3 : ℤ) ^ k % 2 = 1` for every `k : ℕ`. -/
theorem int_three_pow_mod_two_eq_one (k : ℕ) : ((3 : ℤ) ^ k) % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [pow_succ]
      omega

/-- **Dyadic-Triadic Partition Characterization of the Sub-Ceiling Window & Non-Vanishing Boundaries
(`subCeiling_dyadic_triadic_partition_and_odd_boundary_non_vanishing`, Section C2.O8.1)**:
For any sequence `s : ℕ → ℕ` and index `N : ℕ` with `1 ≤ s N`, setting `T_N = blockSteps s N`
and `S_N = renewalIntSlack s N`:
1. `(0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
    ((2 : ℤ) ^ (T_N + s N + 1) < (3 : ℤ) ^ (s N) * S_N ∧
      (3 : ℤ) ^ (s N - 1) * S_N < (2 : ℤ) ^ (T_N + s N))`, and
2. Whenever `S_N % 2 = 1` and `1 ≤ T_N + m`, `(3 : ℤ) ^ (m - 1) * S_N ≠ (2 : ℤ) ^ (T_N + m)`. -/
theorem subCeiling_dyadic_triadic_partition_and_odd_boundary_non_vanishing
    {s : ℕ → ℕ} {N : ℕ} (hs : 1 ≤ s N) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    ((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
      ((2 : ℤ) ^ (T_N + s N + 1) < (3 : ℤ) ^ (s N) * S_N ∧
        (3 : ℤ) ^ (s N - 1) * S_N < (2 : ℤ) ^ (T_N + s N))) ∧
      (∀ m : ℕ, S_N % 2 = 1 → 1 ≤ T_N + m →
        (3 : ℤ) ^ (m - 1) * S_N ≠ (2 : ℤ) ^ (T_N + m)) := by
  intro T_N S_N
  have hsand := (subCeiling_step_sandwich_iff s N).2.2
  change (0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
    (2 * (2 : ℤ) ^ (T_N + s N) < (3 : ℤ) ^ (s N) * S_N ∧
      (3 : ℤ) ^ (s N) * S_N < 3 * (2 : ℤ) ^ (T_N + s N)) at hsand
  have hpow2 : (2 : ℤ) ^ (T_N + s N + 1) = 2 * (2 : ℤ) ^ (T_N + s N) := by
    rw [pow_succ']
  have hpow3 : (3 : ℤ) ^ (s N) * S_N = 3 * ((3 : ℤ) ^ (s N - 1) * S_N) := by
    have h3 : (3 : ℤ) ^ (s N) = 3 * (3 : ℤ) ^ (s N - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hs]
    rw [h3, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hsand, hpow2]
    refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
    · have h2 := h.2
      rw [hpow3] at h2
      omega
    · have h2 := h.2
      rw [hpow3]
      omega
  · intro m hodd hm heq
    have h3 : ((3 : ℤ) ^ (m - 1)) % 2 = 1 := int_three_pow_mod_two_eq_one (m - 1)
    have hmul_mod : (((3 : ℤ) ^ (m - 1) * S_N) % 2) = 1 := by
      rw [Int.mul_emod, h3, hodd]
      decide
    have h2_mod : (((2 : ℤ) ^ (T_N + m)) % 2) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, T_N + m = k + 1 := ⟨(T_N + m) - 1, by omega⟩
      rw [hk, pow_succ]
      omega
    rw [heq] at hmul_mod
    omega

/-! ## 2. Sections C2.O8.2 & C2.O8.3: Rung-$2$ Threshold & Two-Step $(3, 2)$ Sub-Ceiling Window -/

/-- **Exact Sub-Ceiling Rung-$2$ Criterion & Two-Step $(s_N = 3, s_{N+1} = 2)$ Window
(`subCeiling_rung_eq_two_iff_and_two_step_three_two_window`, Sections C2.O8.2–C2.O8.3)**:
For any sequence `s : ℕ → ℕ` and index `N : ℕ`, setting `T_N = blockSteps s N` and
`S_N = renewalIntSlack s N`:
1. If `centeredRenewalSlack s N < 0` and `s N = 2`, then
   `centeredRenewalSlack s (N + 1) ≤ -3 * (2 : ℤ) ^ T_N - 9` and
   `((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔ 8 * (2 : ℤ) ^ T_N < 9 * S_N)`.
2. If `s N = 3` and `s (N + 1) = 2`, then
   `renewalIntSlack s (N + 2) = 243 * S_N - 208 * (2 : ℤ) ^ T_N`,
   `centeredRenewalSlack s (N + 2) = 243 * S_N - 240 * (2 : ℤ) ^ T_N`, and
   `((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ∧
     (0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0)) ↔
     (208 * (2 : ℤ) ^ T_N < 243 * S_N ∧ 27 * S_N < 24 * (2 : ℤ) ^ T_N)`. -/
theorem subCeiling_rung_eq_two_iff_and_two_step_three_two_window
    (s : ℕ → ℕ) (N : ℕ) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    (centeredRenewalSlack s N < 0 → s N = 2 →
      centeredRenewalSlack s (N + 1) ≤ -3 * (2 : ℤ) ^ T_N - 9 ∧
        ((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
          8 * (2 : ℤ) ^ T_N < 9 * S_N)) ∧
      (s N = 3 → s (N + 1) = 2 →
        renewalIntSlack s (N + 2) = 243 * S_N - 208 * (2 : ℤ) ^ T_N ∧
          centeredRenewalSlack s (N + 2) = 243 * S_N - 240 * (2 : ℤ) ^ T_N ∧
          (((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ∧
              (0 < renewalIntSlack s (N + 2) ∧ centeredRenewalSlack s (N + 2) < 0)) ↔
            (208 * (2 : ℤ) ^ T_N < 243 * S_N ∧ 27 * S_N < 24 * (2 : ℤ) ^ T_N))) := by
  intro T_N S_N
  have hstep1 := subCeiling_step_sandwich_iff s N
  have hS1 : renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 2 * (2 : ℤ) ^ (T_N + s N) := hstep1.1
  have hC1 : centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 3 * (2 : ℤ) ^ (T_N + s N) := hstep1.2.1
  clear hstep1
  refine ⟨?_, ?_⟩
  · intro hC_lt hs2
    have hC_def : centeredRenewalSlack s N = S_N - (2 : ℤ) ^ T_N := rfl
    have hS1' : renewalIntSlack s (N + 1) = 9 * S_N - 8 * (2 : ℤ) ^ T_N := by
      rw [hS1, hs2, pow_add]
      ring
    have hC1' : centeredRenewalSlack s (N + 1) = 9 * S_N - 12 * (2 : ℤ) ^ T_N := by
      rw [hC1, hs2, pow_add]
      ring
    clear hS1 hC1
    rw [hC_def] at hC_lt
    rw [hS1', hC1']
    refine ⟨by omega, ?_⟩
    constructor <;> intro h <;> omega
  · intro hs3 hs_next
    have hstep2 := subCeiling_step_sandwich_iff s (N + 1)
    have hS2 : renewalIntSlack s (N + 2) =
        (3 : ℤ) ^ (s (N + 1)) * renewalIntSlack s (N + 1) - 2 * (2 : ℤ) ^ (blockSteps s (N + 1) + s (N + 1)) := hstep2.1
    have hC2 : centeredRenewalSlack s (N + 2) =
        (3 : ℤ) ^ (s (N + 1)) * renewalIntSlack s (N + 1) - 3 * (2 : ℤ) ^ (blockSteps s (N + 1) + s (N + 1)) := hstep2.2.1
    clear hstep2
    have hT1 : blockSteps s (N + 1) = T_N + 3 := by
      simp [blockSteps, T_N, hs3]
    have hS1' : renewalIntSlack s (N + 1) = 27 * S_N - 16 * (2 : ℤ) ^ T_N := by
      rw [hS1, hs3, pow_add]
      ring
    have hC1' : centeredRenewalSlack s (N + 1) = 27 * S_N - 24 * (2 : ℤ) ^ T_N := by
      rw [hC1, hs3, pow_add]
      ring
    have hS2' : renewalIntSlack s (N + 2) = 243 * S_N - 208 * (2 : ℤ) ^ T_N := by
      rw [hS2, hs_next, hT1, hS1', pow_add]
      ring
    have hC2' : centeredRenewalSlack s (N + 2) = 243 * S_N - 240 * (2 : ℤ) ^ T_N := by
      rw [hC2, hs_next, hT1, hS1', pow_add]
      ring
    clear hS1 hC1 hS2 hC2 hT1
    refine ⟨hS2', hC2', ?_⟩
    rw [hS1', hC1', hS2', hC2']
    have hpos : 0 < (2 : ℤ) ^ T_N := by positivity
    constructor <;> intro h <;> omega

/-! ## 3. Section C2.O8.4: 2-Adic Prefix Congruence $2^{T_K+1} \mid (3^d \Sigma_K - \Sigma_{K+M})$ and Mod-8 Law -/

/-- **2-Adic Prefix Congruence $2^{T_K+1} \mid (3^d \Sigma_K - \Sigma_{K+M})$ and Mod-8 Law
(`renewalIntSlack_two_adic_prefix_congruence_and_mod_eight`, Section C2.O8.4)**:
1. For any sequence `s : ℕ → ℕ` and any `K, M : ℕ`, setting `d = blockSteps (fun t => s (K + t)) M`:
   `(3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M) =
     (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator (fun t => s (K + t)) M : ℤ)` and
   `((2 : ℤ) ^ (blockSteps s K + 1)) ∣ ((3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M))`.
2. Whenever `s 0 = 2` and `1 ≤ N`,
   `(8 : ℤ) ∣ ((3 : ℤ) ^ (blockSteps s N - 2) - renewalIntSlack s N)`. -/
theorem renewalIntSlack_two_adic_prefix_congruence_and_mod_eight
    (s : ℕ → ℕ) (K M N : ℕ) :
    let d := blockSteps (fun t => s (K + t)) M
    ((3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M) =
      (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator (fun t => s (K + t)) M : ℤ) ∧
      ((2 : ℤ) ^ (blockSteps s K + 1)) ∣
        ((3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M))) ∧
      (s 0 = 2 → 1 ≤ N →
        (8 : ℤ) ∣ ((3 : ℤ) ^ (blockSteps s N - 2) - renewalIntSlack s N)) := by
  intro d
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 K M).2.2
  have hid :
      (3 : ℤ) ^ d * renewalIntSlack s K - renewalIntSlack s (K + M) =
        (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator (fun t => s (K + t)) M : ℤ) := by
    dsimp [d]
    rw [hcoc]
    ring
  refine ⟨⟨hid, ⟨(renewalNumerator (fun t => s (K + t)) M : ℤ), hid⟩⟩, ?_⟩
  intro hs0 hN
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = 1 + m := ⟨N - 1, by omega⟩
  have hcoc1 := (renewalIntSlack_step_and_cocycle s 0 1 m).2.2
  have hT1 : blockSteps s 1 = 2 := by
    simp [blockSteps, hs0]
  have hS1 : renewalIntSlack s 1 = 1 := by
    have hstep0 := (renewalIntSlack_step_and_cocycle s 0 0 0)
    rw [hstep0.2.1, hstep0.1, hT1, hs0]
    norm_num
  have hshift1 := blockSteps_add_shift s 1 m
  rw [hT1] at hshift1
  have hd1 : blockSteps (fun t => s (1 + t)) m = blockSteps s (1 + m) - 2 := by
    omega
  refine ⟨(renewalNumerator (fun t => s (1 + t)) m : ℤ), ?_⟩
  rw [hcoc1, hT1, hS1, hd1]
  ring

/-! ## 4. Section C2.O8.5: Certification of Blocks 16, 17, and 18 ($T_{18} = 89$) & Mod-$2^{90}$ Uniqueness -/

/-- **Certification of the 16th ($s_{15} = 8$), 17th ($s_{16} = 3$), and 18th ($s_{17} = 6$) Kneading Rungs & Mod-$2^{90}$ Uniqueness
(`sixteen_to_eighteen_block_kneading_corridor_and_two_pow_90_uniqueness`, Section C2.O8.5)**:
For any sequence `s : ℕ → ℕ` beginning with $(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3)$:
1. `(0 < renewalIntSlack s 16 ∧ centeredRenewalSlack s 16 < 0) ↔ s 15 = 8`,
2. When `s 15 = 8`: `blockSteps s 16 = 80`,
   `renewalIntSlack s 16 = 788178306648220023676537`,
   `centeredRenewalSlack s 16 = -420747512966409151029639`, and
   `(0 < renewalIntSlack s 17 ∧ centeredRenewalSlack s 17 < 0) ↔ s 16 = 3`,
3. When `s 15 = 8` and `s 16 = 3`: `blockSteps s 17 = 83`,
   `renewalIntSlack s 17 = 1938001165667873843967683`,
   `centeredRenewalSlack s 17 = -7733405391249159553681725`, and
   `(0 < renewalIntSlack s 18 ∧ centeredRenewalSlack s 18 < 0) ↔ s 17 = 6`,
4. When `s 15 = 8`, `s 16 = 3`, and `s 17 = 6`: `blockSteps s 18 = 89`,
   `renewalIntSlack s 18 = 174862810486499757353316683`,
   `centeredRenewalSlack s 18 = -444107209156190380096245429`, and any two seeds `b₁ < b₂`
   realizing `ValidBlockChain bᵢ s uᵢ 18` satisfy `2 ^ 90 ∣ (b₂ - b₁)` and `2 ^ 90 ≤ b₂`. -/
theorem sixteen_to_eighteen_block_kneading_corridor_and_two_pow_90_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) :
    ((0 < renewalIntSlack s 16 ∧ centeredRenewalSlack s 16 < 0) ↔ s 15 = 8) ∧
      (s 15 = 8 →
        blockSteps s 16 = 80 ∧
          renewalIntSlack s 16 = 788178306648220023676537 ∧
          centeredRenewalSlack s 16 = -420747512966409151029639 ∧
          ((0 < renewalIntSlack s 17 ∧ centeredRenewalSlack s 17 < 0) ↔ s 16 = 3)) ∧
      (s 15 = 8 → s 16 = 3 →
        blockSteps s 17 = 83 ∧
          renewalIntSlack s 17 = 1938001165667873843967683 ∧
          centeredRenewalSlack s 17 = -7733405391249159553681725 ∧
          ((0 < renewalIntSlack s 18 ∧ centeredRenewalSlack s 18 < 0) ↔ s 17 = 6)) ∧
      (s 15 = 8 → s 16 = 3 → s 17 = 6 →
        blockSteps s 18 = 89 ∧
          renewalIntSlack s 18 = 174862810486499757353316683 ∧
          centeredRenewalSlack s 18 = -444107209156190380096245429 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 18 →
              ValidBlockChain b₂ s u₂ 18 →
                2 ^ 90 ∣ (b₂ - b₁) ∧ 2 ^ 90 ≤ b₂)) := by
  have hprev :=
    (fourteen_and_fifteen_block_kneading_corridor_and_two_pow_73_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12).2.2 hs13 hs14
  have hT15 : blockSteps s 15 = 72 := hprev.1
  have hS15 : renewalIntSlack s 15 = 488649587849028863449 := hprev.2.1
  have hstep15 := subCeiling_step_sandwich_iff s 15
  have hiff15 :
      (0 < renewalIntSlack s 16 ∧ centeredRenewalSlack s 16 < 0) ↔ s 15 = 8 := by
    have hsand15 := (subCeiling_step_sandwich_iff s 15).2.2
    rw [hT15, hS15] at hsand15
    exact hsand15.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 488649587849028863449) (T_N := 72) (s_star := 8)
      (by norm_num) (by norm_num) (s 15)).1
  have h16_vals :
      s 15 = 8 →
        blockSteps s 16 = 80 ∧
          renewalIntSlack s 16 = 788178306648220023676537 ∧
          centeredRenewalSlack s 16 = -420747512966409151029639 := by
    intro hs15
    have hT16 : blockSteps s 16 = 80 := by
      change blockSteps s 15 + s 15 = 80
      rw [hT15, hs15]
    have hS16 : renewalIntSlack s 16 = 788178306648220023676537 := by
      have h1 := hstep15.1
      rw [h1, hT15, hS15, hs15]
      norm_num
    have hC16 : centeredRenewalSlack s 16 = -420747512966409151029639 := by
      have h2 := hstep15.2.1
      rw [h2, hT15, hS15, hs15]
      norm_num
    exact ⟨hT16, hS16, hC16⟩
  have h17_vals :
      s 15 = 8 → s 16 = 3 →
        blockSteps s 17 = 83 ∧
          renewalIntSlack s 17 = 1938001165667873843967683 ∧
          centeredRenewalSlack s 17 = -7733405391249159553681725 := by
    intro hs15 hs16
    obtain ⟨hT16, hS16, _⟩ := h16_vals hs15
    have hstep16 := subCeiling_step_sandwich_iff s 16
    have hT17 : blockSteps s 17 = 83 := by
      change blockSteps s 16 + s 16 = 83
      rw [hT16, hs16]
    have hS17 : renewalIntSlack s 17 = 1938001165667873843967683 := by
      have h1 := hstep16.1
      rw [h1, hT16, hS16, hs16]
      norm_num
    have hC17 : centeredRenewalSlack s 17 = -7733405391249159553681725 := by
      have h2 := hstep16.2.1
      rw [h2, hT16, hS16, hs16]
      norm_num
    exact ⟨hT17, hS17, hC17⟩
  refine ⟨hiff15, ?_, ?_, ?_⟩
  · intro hs15
    obtain ⟨hT16, hS16, hC16⟩ := h16_vals hs15
    have hsand16 := (subCeiling_step_sandwich_iff s 16).2.2
    rw [hT16, hS16] at hsand16
    refine ⟨hT16, hS16, hC16, ?_⟩
    exact hsand16.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 788178306648220023676537) (T_N := 80) (s_star := 3)
      (by norm_num) (by norm_num) (s 16)).1
  · intro hs15 hs16
    obtain ⟨hT17, hS17, hC17⟩ := h17_vals hs15 hs16
    have hsand17 := (subCeiling_step_sandwich_iff s 17).2.2
    rw [hT17, hS17] at hsand17
    refine ⟨hT17, hS17, hC17, ?_⟩
    exact hsand17.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 1938001165667873843967683) (T_N := 83) (s_star := 6)
      (by norm_num) (by norm_num) (s 17)).1
  · intro hs15 hs16 hs17
    obtain ⟨hT17, hS17, _⟩ := h17_vals hs15 hs16
    have hstep17 := subCeiling_step_sandwich_iff s 17
    have hT18 : blockSteps s 18 = 89 := by
      change blockSteps s 17 + s 17 = 89
      rw [hT17, hs17]
    have hS18 : renewalIntSlack s 18 = 174862810486499757353316683 := by
      have h1 := hstep17.1
      rw [h1, hT17, hS17, hs17]
      norm_num
    have hC18 : centeredRenewalSlack s 18 = -444107209156190380096245429 := by
      have h2 := hstep17.2.1
      rw [h2, hT17, hS17, hs17]
      norm_num
    refine ⟨hT18, hS18, hC18, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 18) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 18 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT18] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 90 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.DyadicTriadicAndKneading18
