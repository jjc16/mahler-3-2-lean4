import ShiftSlackDecompositionAndKneading42

/-!
# The Universal Parry–Kneading Shift Domination Theorem ($w_M \le s_{N+M}$) & 45-Block ($T_{45} = 223$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 17 / 20 (Part XXXII, Sections C2.O17.1–C2.O17.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O17.1 (Inner Loop 1 / 5) — Prefix-Congruence Invariance of `blockSteps`, `renewalNumerator`, $\Sigma_M$, and $\widehat{\Sigma}_M$
   (`prefix_congr_blockSteps_renewalNumerator_slack`)**:
   - Whenever `∀ t < M, s' t = w t`, `blockSteps s' M = blockSteps w M`,
     `renewalNumerator s' M = renewalNumerator w M`, `renewalIntSlack s' M = renewalIntSlack w M`,
     and `centeredRenewalSlack s' M = centeredRenewalSlack w M`.

2. **Section C2.O17.2 (Inner Loop 2 / 5) — Monotone Rung-Death Below a Sub-Ceiling Rung
   (`candidateSlack_nonpos_of_lt_of_candidateCenteredSlack_nonpos`)**:
   - Whenever `candidateCenteredSlack S d m ≤ 0` and `r < m`, `candidateSlack S d r ≤ 0`.

3. **Section C2.O17.3 (Inner Loop 3 / 5) — The Universal Parry–Kneading Shift Domination Theorem ($w_M \le s_{N+M}$)
   (`subCeiling_shift_lexicographic_domination`)**:
   - Suppose `centeredRenewalSlack s N < 0` and the shifted subword starting at `N` matches `w`
     for `M` blocks (`∀ t < M, s (N + t) = w t`), with `d = blockSteps w M`:
     1. If `centeredRenewalSlack w M ≤ 0`, then `centeredRenewalSlack s (N + M) < 0`.
     2. `renewalIntSlack s (N + M + 1) =
          (3 : ℤ) ^ (d + s (N + M)) * centeredRenewalSlack s N +
            (2 : ℤ) ^ (blockSteps s N) * candidateSlack (renewalIntSlack w M) d (s (N + M))`.
     3. If `centeredRenewalSlack w (M + 1) ≤ 0` and `0 < renewalIntSlack s (N + M + 1)`, then
        **`w M ≤ s (N + M)`**!

4. **Sections C2.O17.4 & C2.O17.5 (Inner Loops 4–5 / 5) — Certification of Blocks 43, 44, and 45 ($s_{42} = 6, s_{43} = 6, s_{44} = 3$, $T_{45} = 223$) & Mod-$2^{224}$ Uniqueness
   (`fortythree_to_fortyfive_block_kneading_corridor_and_two_pow_224_uniqueness`)**:
   - Certifies blocks 43–45 ($T_{45} = 223$) and proves $2^{224} \mid (b_2 - b_1)$ and $2^{224} \le b_2$
     for any two seeds sharing the 45-block prefix.
-/

namespace Mahler.ParryKneadingDominationAndKneading45

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

/-! ## 1. Section C2.O17.1: Prefix-Congruence Invariance -/

/-- **Prefix-Congruence Invariance of `blockSteps`, `renewalNumerator`, $\Sigma_M$, and $\widehat{\Sigma}_M$
(`prefix_congr_blockSteps_renewalNumerator_slack`, Section C2.O17.1)**:
Whenever `∀ t < M, s' t = w t`:
1. `blockSteps s' M = blockSteps w M`,
2. `renewalNumerator s' M = renewalNumerator w M`,
3. `renewalIntSlack s' M = renewalIntSlack w M`, and
4. `centeredRenewalSlack s' M = centeredRenewalSlack w M`. -/
theorem prefix_congr_blockSteps_renewalNumerator_slack
    {s' w : ℕ → ℕ} {M : ℕ} (heq : ∀ t < M, s' t = w t) :
    blockSteps s' M = blockSteps w M ∧
      renewalNumerator s' M = renewalNumerator w M ∧
      renewalIntSlack s' M = renewalIntSlack w M ∧
      centeredRenewalSlack s' M = centeredRenewalSlack w M := by
  have hTA : blockSteps s' M = blockSteps w M ∧ renewalNumerator s' M = renewalNumerator w M := by
    induction M with
    | zero => simp [blockSteps, renewalNumerator]
    | succ M ih =>
        rcases ih (fun t ht => heq t (by omega)) with ⟨hT, hA⟩
        have hM := heq M (by omega)
        refine ⟨by simp [blockSteps, hT, hM], by simp [renewalNumerator, blockSteps, hT, hA, hM]⟩
  rcases hTA with ⟨hT, hA⟩
  have hS : renewalIntSlack s' M = renewalIntSlack w M := by
    unfold renewalIntSlack
    rw [hT, hA]
  have hC : centeredRenewalSlack s' M = centeredRenewalSlack w M := by
    unfold centeredRenewalSlack
    rw [hS, hT]
  exact ⟨hT, hA, hS, hC⟩

/-! ## 2. Section C2.O17.2: Monotone Rung-Death Below a Sub-Ceiling Rung -/

/-- **Monotone Rung-Death Below a Sub-Ceiling Rung
(`candidateSlack_nonpos_of_lt_of_candidateCenteredSlack_nonpos`, Section C2.O17.2)**:
For any `S : ℤ` and `d, r, m : ℕ`, if `candidateCenteredSlack S d m ≤ 0` and `r < m`, then
`candidateSlack S d r ≤ 0`. -/
theorem candidateSlack_nonpos_of_lt_of_candidateCenteredSlack_nonpos
    {S : ℤ} {d r m : ℕ}
    (hC_le : candidateCenteredSlack S d m ≤ 0) (hr_lt : r < m) :
    candidateSlack S d r ≤ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = r + k + 1 := ⟨m - r - 1, by omega⟩
  unfold candidateCenteredSlack at hC_le
  unfold candidateSlack
  by_contra hpos
  push_neg at hpos
  have h3_split : (3 : ℤ) ^ (r + k + 1) * S = 3 * (3 : ℤ) ^ k * ((3 : ℤ) ^ r * S) := by
    rw [pow_add, pow_succ]
    ring
  have h2_split : 3 * (2 : ℤ) ^ (d + (r + k + 1)) = 3 * (2 : ℤ) ^ k * (2 * (2 : ℤ) ^ (d + r)) := by
    rw [show d + (r + k + 1) = (d + r) + k + 1 by omega, pow_add, pow_succ]
    ring
  have h2_le_3 : (2 : ℤ) ^ k ≤ (3 : ℤ) ^ k := by
    exact_mod_cast Nat.pow_le_pow_left (by decide) k
  have h2dr_nonneg : 0 ≤ 2 * (2 : ℤ) ^ (d + r) := by positivity
  have h3k_pos : 0 < 3 * (3 : ℤ) ^ k := by positivity
  have hmul1 :
      3 * (2 : ℤ) ^ k * (2 * (2 : ℤ) ^ (d + r)) ≤
        3 * (3 : ℤ) ^ k * (2 * (2 : ℤ) ^ (d + r)) := by
    have hle3 : 3 * (2 : ℤ) ^ k ≤ 3 * (3 : ℤ) ^ k := by omega
    exact mul_le_mul_of_nonneg_right hle3 h2dr_nonneg
  have hmul2 :
      3 * (3 : ℤ) ^ k * (2 * (2 : ℤ) ^ (d + r)) <
        3 * (3 : ℤ) ^ k * ((3 : ℤ) ^ r * S) :=
    mul_lt_mul_of_pos_left (by omega) h3k_pos
  rw [h3_split, h2_split] at hC_le
  omega

/-! ## 3. Section C2.O17.3: The Universal Parry–Kneading Shift Domination Theorem ($w_M \le s_{N+M}$) -/

/-- **The Universal Parry–Kneading Shift Domination Theorem ($w_M \le s_{N+M}$)
(`subCeiling_shift_lexicographic_domination`, Section C2.O17.3)**:
Suppose `centeredRenewalSlack s N < 0` and the shifted subword starting at `N` matches `w`
for `M` blocks (`∀ t < M, s (N + t) = w t`), with `d = blockSteps w M`:
1. If `centeredRenewalSlack w M ≤ 0`, then `centeredRenewalSlack s (N + M) < 0`.
2. `renewalIntSlack s (N + M + 1) =
     (3 : ℤ) ^ (d + s (N + M)) * centeredRenewalSlack s N +
       (2 : ℤ) ^ (blockSteps s N) * candidateSlack (renewalIntSlack w M) d (s (N + M))`.
3. If `centeredRenewalSlack w (M + 1) ≤ 0` and `0 < renewalIntSlack s (N + M + 1)`, then
   **`w M ≤ s (N + M)`**! -/
theorem subCeiling_shift_lexicographic_domination
    {s w : ℕ → ℕ} {N M : ℕ}
    (hsub : centeredRenewalSlack s N < 0)
    (hmatch : ∀ t < M, s (N + t) = w t) :
    let d := blockSteps w M
    (centeredRenewalSlack w M ≤ 0 → centeredRenewalSlack s (N + M) < 0) ∧
      renewalIntSlack s (N + M + 1) =
        (3 : ℤ) ^ (d + s (N + M)) * centeredRenewalSlack s N +
          (2 : ℤ) ^ (blockSteps s N) *
            candidateSlack (renewalIntSlack w M) d (s (N + M)) ∧
      (centeredRenewalSlack w (M + 1) ≤ 0 →
        0 < renewalIntSlack s (N + M + 1) →
          w M ≤ s (N + M)) := by
  intro d
  set s' := fun t => s (N + t)
  rcases prefix_congr_blockSteps_renewalNumerator_slack (s' := s') (w := w) hmatch with
    ⟨hT_eq, _, hS_eq, hC_eq⟩
  have hcoc_C := (centeredRenewalSlack_step_and_cocycle s 0 N M).2.2.2
  change centeredRenewalSlack s (N + M) =
    (3 : ℤ) ^ (blockSteps s' M) * centeredRenewalSlack s N +
      (2 : ℤ) ^ (blockSteps s N) * centeredRenewalSlack s' M at hcoc_C
  rw [hT_eq, hC_eq] at hcoc_C
  have hshift_S := renewalIntSlack_shift_eq_three_pow_centered_add_two_pow_slack s N M
  change renewalIntSlack s (N + M) =
    (3 : ℤ) ^ (blockSteps s' M) * centeredRenewalSlack s N +
      (2 : ℤ) ^ (blockSteps s N) * renewalIntSlack s' M at hshift_S
  rw [hT_eq, hS_eq] at hshift_S
  have hT_NM : blockSteps s (N + M) = blockSteps s N + d := by
    have hsh := blockSteps_add_shift s N M
    change blockSteps s (N + M) = blockSteps s N + blockSteps s' M at hsh
    rw [hsh, hT_eq]
  have hstep_NM := (subCeiling_step_sandwich_iff s (N + M)).1
  change renewalIntSlack s (N + M + 1) =
    (3 : ℤ) ^ (s (N + M)) * renewalIntSlack s (N + M) -
      2 * (2 : ℤ) ^ (blockSteps s (N + M) + s (N + M)) at hstep_NM
  have hS_next_id :
      renewalIntSlack s (N + M + 1) =
        (3 : ℤ) ^ (d + s (N + M)) * centeredRenewalSlack s N +
          (2 : ℤ) ^ (blockSteps s N) *
            candidateSlack (renewalIntSlack w M) d (s (N + M)) := by
    unfold candidateSlack
    rw [hstep_NM, hshift_S, hT_NM,
        show blockSteps s N + d + s (N + M) = blockSteps s N + (d + s (N + M)) by omega]
    simp only [pow_add]
    ring
  have h3d_pos : 0 < (3 : ℤ) ^ d := by positivity
  have h2T_pos : 0 < (2 : ℤ) ^ (blockSteps s N) := by positivity
  refine ⟨?_, hS_next_id, ?_⟩
  · intro hCw_le
    have h1 : (3 : ℤ) ^ (blockSteps w M) * centeredRenewalSlack s N < 0 :=
      mul_neg_of_pos_of_neg h3d_pos hsub
    have h2 : (2 : ℤ) ^ (blockSteps s N) * centeredRenewalSlack w M ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h2T_pos) hCw_le
    rw [hcoc_C]
    exact add_neg_of_neg_of_nonpos h1 h2
  · intro hCw_next_le hS_next_pos
    have hCw_eq :
        centeredRenewalSlack w (M + 1) =
          candidateCenteredSlack (renewalIntSlack w M) d (w M) :=
      (subCeiling_step_sandwich_iff w M).2.1
    rw [hCw_eq] at hCw_next_le
    by_contra hnot_le
    have hlt : s (N + M) < w M := Nat.lt_of_not_ge hnot_le
    have hcand_le :=
      candidateSlack_nonpos_of_lt_of_candidateCenteredSlack_nonpos hCw_next_le hlt
    have h3dr_pos : 0 < (3 : ℤ) ^ (d + s (N + M)) := by positivity
    have hterm1_neg : (3 : ℤ) ^ (d + s (N + M)) * centeredRenewalSlack s N < 0 :=
      mul_neg_of_pos_of_neg h3dr_pos hsub
    have hterm2_nonpos :
        (2 : ℤ) ^ (blockSteps s N) * candidateSlack (renewalIntSlack w M) d (s (N + M)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h2T_pos) hcand_le
    have hsum_neg : renewalIntSlack s (N + M + 1) < 0 := by
      rw [hS_next_id]
      exact add_neg_of_neg_of_nonpos hterm1_neg hterm2_nonpos
    exact absurd hS_next_pos (not_lt_of_gt hsum_neg)

/-! ## 4. Sections C2.O17.4 & C2.O17.5: Certification of Blocks 43, 44, and 45 ($T_{45} = 223$) & Mod-$2^{224}$ Uniqueness -/

/-- **Certification of the 43rd ($s_{42} = 6$), 44th ($s_{43} = 6$), and 45th ($s_{44} = 3$) Kneading Rungs & Mod-$2^{224}$ Uniqueness
(`fortythree_to_fortyfive_block_kneading_corridor_and_two_pow_224_uniqueness`, Sections C2.O17.4–C2.O17.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 42-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4, 6, 6, 3, 3, 3, 3, 5, 4, 11)$:
1. `(0 < renewalIntSlack s 43 ∧ centeredRenewalSlack s 43 < 0) ↔ s 42 = 6`,
2. When `s 42 = 6`: `blockSteps s 43 = 214`,
   `renewalIntSlack s 43 = 6654605725147170113049132560849757281375215493387706480726122641`,
   `centeredRenewalSlack s 43 = -19673467191992126561430374360067850798348558356749571332851621743`, and
   `(0 < renewalIntSlack s 44 ∧ centeredRenewalSlack s 44 < 0) ↔ s 43 = 6`,
3. When `s 42 = 6` and `s 43 = 6`: `blockSteps s 44 = 220`,
   `renewalIntSlack s 44 = 1481214240238457038079440750982019223917889041862066464311392124137`,
   `centeredRenewalSlack s 44 = -203782426458457949087247691956707693184432484546719315757583516439`, and
   `(0 < renewalIntSlack s 45 ∧ centeredRenewalSlack s 45 < 0) ↔ s 44 = 3`,
4. When `s 42 = 6`, `s 43 = 6`, and `s 44 = 3`: `blockSteps s 45 = 223`,
   `renewalIntSlack s 45 = 13032837819287700233477885189494888372145859707735222055303977102483`,
   `centeredRenewalSlack s 45 = -447135514287619663855622354014926964672712503535064185247828022125`,
   and any two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 45` satisfy `2 ^ 224 ∣ (b₂ - b₁)`
   and `2 ^ 224 ≤ b₂`. -/
theorem fortythree_to_fortyfive_block_kneading_corridor_and_two_pow_224_uniqueness
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
    (hs40 : s 40 = 4) (hs41 : s 41 = 11) :
    ((0 < renewalIntSlack s 43 ∧ centeredRenewalSlack s 43 < 0) ↔ s 42 = 6) ∧
      (s 42 = 6 →
        blockSteps s 43 = 214 ∧
          renewalIntSlack s 43 = 6654605725147170113049132560849757281375215493387706480726122641 ∧
          centeredRenewalSlack s 43 = -19673467191992126561430374360067850798348558356749571332851621743 ∧
          ((0 < renewalIntSlack s 44 ∧ centeredRenewalSlack s 44 < 0) ↔ s 43 = 6)) ∧
      (s 42 = 6 → s 43 = 6 →
        blockSteps s 44 = 220 ∧
          renewalIntSlack s 44 = 1481214240238457038079440750982019223917889041862066464311392124137 ∧
          centeredRenewalSlack s 44 = -203782426458457949087247691956707693184432484546719315757583516439 ∧
          ((0 < renewalIntSlack s 45 ∧ centeredRenewalSlack s 45 < 0) ↔ s 44 = 3)) ∧
      (s 42 = 6 → s 43 = 6 → s 44 = 3 →
        blockSteps s 45 = 223 ∧
          renewalIntSlack s 45 = 13032837819287700233477885189494888372145859707735222055303977102483 ∧
          centeredRenewalSlack s 45 = -447135514287619663855622354014926964672712503535064185247828022125 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 45 →
              ValidBlockChain b₂ s u₂ 45 →
                2 ^ 224 ∣ (b₂ - b₁) ∧ 2 ^ 224 ≤ b₂)) := by
  have hprev :=
    (forty_to_fortytwo_block_kneading_corridor_and_two_pow_209_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32 hs33 hs34 hs35 hs36 hs37
      hs38).2.2.2 hs39 hs40 hs41
  have hT42 : blockSteps s 42 = 208 := hprev.1
  have hS42 : renewalIntSlack s 42 = 81359055637072377862836963515342899095778824682664282726860921 := hprev.2.1
  have hstep42 := subCeiling_step_sandwich_iff s 42
  have hiff42 :
      (0 < renewalIntSlack s 43 ∧ centeredRenewalSlack s 43 < 0) ↔ s 42 = 6 := by
    have hsand42 := hstep42.2.2
    rw [hT42, hS42] at hsand42
    exact hsand42.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 81359055637072377862836963515342899095778824682664282726860921) (T_N := 208) (s_star := 6)
      (by norm_num) (by norm_num) (s 42)).1
  have h43_vals :
      s 42 = 6 →
        blockSteps s 43 = 214 ∧
          renewalIntSlack s 43 = 6654605725147170113049132560849757281375215493387706480726122641 ∧
          centeredRenewalSlack s 43 = -19673467191992126561430374360067850798348558356749571332851621743 := by
    intro hs42
    have hT43 : blockSteps s 43 = 214 := by
      change blockSteps s 42 + s 42 = 214
      rw [hT42, hs42]
    have hS43 : renewalIntSlack s 43 = 6654605725147170113049132560849757281375215493387706480726122641 := by
      have h1 := hstep42.1
      rw [h1, hT42, hS42, hs42]
      norm_num
    have hC43 : centeredRenewalSlack s 43 = -19673467191992126561430374360067850798348558356749571332851621743 := by
      have h2 := hstep42.2.1
      rw [h2, hT42, hS42, hs42]
      norm_num
    exact ⟨hT43, hS43, hC43⟩
  have h44_vals :
      s 42 = 6 → s 43 = 6 →
        blockSteps s 44 = 220 ∧
          renewalIntSlack s 44 = 1481214240238457038079440750982019223917889041862066464311392124137 ∧
          centeredRenewalSlack s 44 = -203782426458457949087247691956707693184432484546719315757583516439 := by
    intro hs42 hs43
    obtain ⟨hT43, hS43, _⟩ := h43_vals hs42
    have hstep43 := subCeiling_step_sandwich_iff s 43
    have hT44 : blockSteps s 44 = 220 := by
      change blockSteps s 43 + s 43 = 220
      rw [hT43, hs43]
    have hS44 : renewalIntSlack s 44 = 1481214240238457038079440750982019223917889041862066464311392124137 := by
      have h1 := hstep43.1
      rw [h1, hT43, hS43, hs43]
      norm_num
    have hC44 : centeredRenewalSlack s 44 = -203782426458457949087247691956707693184432484546719315757583516439 := by
      have h2 := hstep43.2.1
      rw [h2, hT43, hS43, hs43]
      norm_num
    exact ⟨hT44, hS44, hC44⟩
  refine ⟨hiff42, ?_, ?_, ?_⟩
  · intro hs42
    obtain ⟨hT43, hS43, hC43⟩ := h43_vals hs42
    have hsand43 := (subCeiling_step_sandwich_iff s 43).2.2
    rw [hT43, hS43] at hsand43
    refine ⟨hT43, hS43, hC43, ?_⟩
    exact hsand43.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 6654605725147170113049132560849757281375215493387706480726122641) (T_N := 214) (s_star := 6)
      (by norm_num) (by norm_num) (s 43)).1
  · intro hs42 hs43
    obtain ⟨hT44, hS44, hC44⟩ := h44_vals hs42 hs43
    have hsand44 := (subCeiling_step_sandwich_iff s 44).2.2
    rw [hT44, hS44] at hsand44
    refine ⟨hT44, hS44, hC44, ?_⟩
    exact hsand44.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 1481214240238457038079440750982019223917889041862066464311392124137) (T_N := 220) (s_star := 3)
      (by norm_num) (by norm_num) (s 44)).1
  · intro hs42 hs43 hs44
    obtain ⟨hT44, hS44, _⟩ := h44_vals hs42 hs43
    have hstep44 := subCeiling_step_sandwich_iff s 44
    have hT45 : blockSteps s 45 = 223 := by
      change blockSteps s 44 + s 44 = 223
      rw [hT44, hs44]
    have hS45 : renewalIntSlack s 45 = 13032837819287700233477885189494888372145859707735222055303977102483 := by
      have h1 := hstep44.1
      rw [h1, hT44, hS44, hs44]
      norm_num
    have hC45 : centeredRenewalSlack s 45 = -447135514287619663855622354014926964672712503535064185247828022125 := by
      have h2 := hstep44.2.1
      rw [h2, hT44, hS44, hs44]
      norm_num
    refine ⟨hT45, hS45, hC45, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 45) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 45 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT45] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 224 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.ParryKneadingDominationAndKneading45
