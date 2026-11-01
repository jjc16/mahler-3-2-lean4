import CenteredRenewalSlackAndUniqueSubCeilingRung

/-!
# The Unique Sub-Ceiling Corridor Theorem for $(2, 6, 3, 3, 2, 10)$

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 3 / 20 (Part XVIII, Sections C2.O3.1–C2.O3.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O3.1 (Inner Loop 1 / 5) — Closed Form $19 \widehat{\Sigma}_{2+j}(2, 6, 3^j) = 27^{j+1} - 768 \cdot 8^j$
   (`two_six_three_run_centeredRenewalSlack_and_j_ge_three_restoration`)**:
   - Along any prefix $(2, 6, \underbrace{3, \dots, 3}_j)$,
     `19 * centeredRenewalSlack s (2 + j) = (27 : ℤ) ^ (j + 1) - 768 * (8 : ℤ) ^ j`.
   - Proves `centeredRenewalSlack s (2 + j) < 0 ↔ j ≤ 2` and `0 < centeredRenewalSlack s (2 + j) ↔ 3 ≤ j`
     (with $\widehat{\Sigma}_5(2, 6, 3, 3, 3) = 7275 > 0$).

2. **Section C2.O3.2 (Inner Loop 2 / 5) — Uniqueness of the $s_2 = 3$ Sub-Ceiling Rung After $(2, 6)$
   (`three_block_two_six_unique_subCeiling_rung_three`)**:
   - Along $(2, 6, s_2)$, `centeredRenewalSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 768 * (2 : ℤ) ^ (s 2)`,
     and `(0 < renewalIntSlack s 3 ∧ centeredRenewalSlack s 3 < 0) ↔ s 2 = 3` ($\widehat{\Sigma}_3 = -285$).

3. **Section C2.O3.3 (Inner Loop 3 / 5) — Uniqueness of the $s_3 = 3$ Sub-Ceiling Rung After $(2, 6, 3)$
   (`four_block_two_six_three_unique_subCeiling_rung_three`)**:
   - Along $(2, 6, 3, s_3)$, `renewalIntSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 4096 * (2 : ℤ) ^ (s 3)` and
     `centeredRenewalSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 6144 * (2 : ℤ) ^ (s 3)`,
     and `(0 < renewalIntSlack s 4 ∧ centeredRenewalSlack s 4 < 0) ↔ s 3 = 3` ($\widehat{\Sigma}_4 = -1551$).

4. **Section C2.O3.4 (Inner Loop 4 / 5) — Uniqueness of the $s_4 = 2$ Sub-Ceiling Rung After $(2, 6, 3, 3)$
   (`five_block_two_six_three_three_unique_subCeiling_rung_two`)**:
   - Along $(2, 6, 3, 3, s_4)$, `renewalIntSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 32768 * (2 : ℤ) ^ (s 4)` and
     `centeredRenewalSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 49152 * (2 : ℤ) ^ (s 4)`,
     and `(0 < renewalIntSlack s 5 ∧ centeredRenewalSlack s 5 < 0) ↔ s 4 = 2` ($\widehat{\Sigma}_5 = -63111$).

5. **Section C2.O3.5 (Inner Loop 5 / 5) — Uniqueness of $s_5 = 10$ & the 6-Block Sub-Ceiling Corridor Theorem
   (`six_block_unique_subCeiling_rung_ten`, `unique_six_block_subCeiling_kneading_corridor`)**:
   - Along $(2, 6, 3, 3, 2, s_5)$, `centeredRenewalSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 196608 * (2 : ℤ) ^ (s 5)`,
     and `(0 < renewalIntSlack s 6 ∧ centeredRenewalSlack s 6 < 0) ↔ s 5 = 10` ($\widehat{\Sigma}_6 = -58132767$).
   - **Capstone (`unique_six_block_subCeiling_kneading_corridor`):** Starting from $s_0 = 2$,
     $(2, 6, 3, 3, 2, 10)$ is the **unique** 6-block sequence keeping $(0 < \Sigma_k \land \widehat{\Sigma}_k < 0)$
     for all $2 \le k \le 6$!
-/

namespace Mahler.UniqueSubCeilingCorridor

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

/-! ## 1. Section C2.O3.1: Closed Form $19 \widehat{\Sigma}_{2+j}(2, 6, 3^j) = 27^{j+1} - 768 \cdot 8^j$ -/

/-- **Closed Form & $j \ge 3$ Ceiling-Restoration Threshold for $(2, 6, 3^j)$
(`two_six_three_run_centeredRenewalSlack_and_j_ge_three_restoration`, Section C2.O3.1)**:
Suppose `s 0 = 2`, `s 1 = 6`, and `∀ t < j, s (2 + t) = 3`. Then:
1. `19 * centeredRenewalSlack s (2 + j) = (27 : ℤ) ^ (j + 1) - 768 * (8 : ℤ) ^ j`,
2. `centeredRenewalSlack s (2 + j) < 0 ↔ j ≤ 2`, and
3. `0 < centeredRenewalSlack s (2 + j) ↔ 3 ≤ j` (with `centeredRenewalSlack s 5 = 7275` at `j = 3`). -/
theorem two_six_three_run_centeredRenewalSlack_and_j_ge_three_restoration
    {s : ℕ → ℕ} {j : ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs3 : ∀ t < j, s (2 + t) = 3) :
    19 * centeredRenewalSlack s (2 + j) = (27 : ℤ) ^ (j + 1) - 768 * (8 : ℤ) ^ j ∧
      (centeredRenewalSlack s (2 + j) < 0 ↔ j ≤ 2) ∧
      (0 < centeredRenewalSlack s (2 + j) ↔ 3 ≤ j) ∧
      (j = 3 → centeredRenewalSlack s (2 + j) = 7275) := by
  rcases two_six_three_run_and_next_two_slack_closed_forms hs0 hs1 hs3 with ⟨hT, h19S, _⟩
  have h2_pow : (2 : ℤ) ^ (8 + 3 * j) = 256 * (8 : ℤ) ^ j := by
    calc
      (2 : ℤ) ^ (8 + 3 * j) = (2 : ℤ) ^ 8 * ((2 : ℤ) ^ 3) ^ j := by
        rw [pow_add, pow_mul]
      _ = 256 * (8 : ℤ) ^ j := by norm_num
  have h19CS : 19 * centeredRenewalSlack s (2 + j) = (27 : ℤ) ^ (j + 1) - 768 * (8 : ℤ) ^ j := by
    unfold centeredRenewalSlack
    rw [hT, h2_pow]
    linarith [h19S]
  have hpow3 : ∀ m : ℕ, 768 * 8 ^ (m + 3) < 27 ^ (m + 3 + 1) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 768 * 8 ^ (m + 1 + 3) = 8 * (768 * 8 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 27 ^ (m + 1 + 3 + 1) = 27 * 27 ^ (m + 3 + 1) := by
          rw [show m + 1 + 3 + 1 = (m + 3 + 1) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow2_le : ∀ n : ℕ, n ≤ 2 → ((27 : ℤ) ^ (n + 1) - 768 * (8 : ℤ) ^ n) < 0 := by
    intro n hn
    rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · omega
  have hpos_iff : 0 < centeredRenewalSlack s (2 + j) ↔ 3 ≤ j := by
    constructor
    · intro hpos
      by_contra hnot
      have hle2 : j ≤ 2 := by omega
      have hlt := hpow2_le j hle2
      linarith [h19CS]
    · intro hge3
      obtain ⟨m, hm⟩ : ∃ m : ℕ, j = m + 3 := ⟨j - 3, by omega⟩
      have hlt : (768 : ℤ) * (8 : ℤ) ^ j < (27 : ℤ) ^ (j + 1) := by
        rw [hm]
        exact_mod_cast hpow3 m
      linarith [h19CS]
  have hneg_iff : centeredRenewalSlack s (2 + j) < 0 ↔ j ≤ 2 := by
    constructor
    · intro hneg
      by_contra hnot
      have hge3 : 3 ≤ j := by omega
      have hp := hpos_iff.mpr hge3
      linarith
    · intro hle2
      have hlt := hpow2_le j hle2
      linarith [h19CS]
  refine ⟨h19CS, hneg_iff, hpos_iff, ?_⟩
  rintro rfl
  omega

/-! ## 2. Section C2.O3.2: Uniqueness of the $s_2 = 3$ Sub-Ceiling Rung After $(2, 6)$ -/

/-- **Uniqueness of the $s_2 = 3$ Sub-Ceiling Rung After $(2, 6)$
(`three_block_two_six_unique_subCeiling_rung_three`, Section C2.O3.2)**:
If `s 0 = 2` and `s 1 = 6`, then:
1. `centeredRenewalSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 768 * (2 : ℤ) ^ (s 2)`,
2. `(0 < renewalIntSlack s 3 ∧ centeredRenewalSlack s 3 < 0) ↔ s 2 = 3`
   (with `centeredRenewalSlack s 3 = -285` at `s 2 = 3`), and
3. `0 < centeredRenewalSlack s 3 ↔ 4 ≤ s 2` (with `centeredRenewalSlack s 3 = 5289` at `s 2 = 4`). -/
theorem three_block_two_six_unique_subCeiling_rung_three
    {s : ℕ → ℕ} (hs0 : s 0 = 2) (hs1 : s 1 = 6) :
    centeredRenewalSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 768 * (2 : ℤ) ^ (s 2) ∧
      ((0 < renewalIntSlack s 3 ∧ centeredRenewalSlack s 3 < 0) ↔ s 2 = 3) ∧
      (0 < centeredRenewalSlack s 3 ↔ 4 ≤ s 2) ∧
      (s 2 = 3 → centeredRenewalSlack s 3 = -285) ∧
      (s 2 = 4 → centeredRenewalSlack s 3 = 5289) := by
  rcases three_block_two_s1_s2_slack_formula hs0 with ⟨hT3, _⟩
  rcases three_block_two_six_s2_escape_iff_s2_le_two hs0 hs1 with ⟨hS3, hesc_iff⟩
  rw [hs1] at hT3
  have hCS3 : centeredRenewalSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 768 * (2 : ℤ) ^ (s 2) := by
    unfold centeredRenewalSlack
    rw [hS3, hT3, show 2 + 6 + s 2 = 8 + s 2 by omega, pow_add (2 : ℤ) 8 (s 2)]
    ring
  have hpow4 : ∀ m : ℕ, 768 * 2 ^ (m + 4) < 217 * 3 ^ (m + 4) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 768 * 2 ^ (m + 1 + 4) = 2 * (768 * 2 ^ (m + 4)) := by
          rw [show m + 1 + 4 = (m + 4) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 217 * 3 ^ (m + 1 + 4) = 3 * (217 * 3 ^ (m + 4)) := by
          rw [show m + 1 + 4 = (m + 4) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow3_le : ∀ n : ℕ, n ≤ 3 → (217 * (3 : ℤ) ^ n - 768 * (2 : ℤ) ^ n) < 0 := by
    intro n hn
    rcases n with _ | _ | _ | _ | n
    · decide
    · decide
    · decide
    · decide
    · omega
  have hslack_nonpos_iff : renewalIntSlack s 3 ≤ 0 ↔ s 2 ≤ 2 := by
    rw [← hesc_iff]
    unfold renewalIntSlack
    have hcast : (3 : ℤ) ^ (blockSteps s 3) = ((3 ^ (blockSteps s 3) : ℕ) : ℤ) := by norm_cast
    rw [hcast]
    omega
  have hpos_iff : 0 < centeredRenewalSlack s 3 ↔ 4 ≤ s 2 := by
    rw [hCS3]
    constructor
    · intro hpos
      by_contra hnot
      have hle3 : s 2 ≤ 3 := by omega
      have hlt := hpow3_le (s 2) hle3
      linarith
    · intro hge4
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 2 = m + 4 := ⟨s 2 - 4, by omega⟩
      have hlt : (768 : ℤ) * (2 : ℤ) ^ (s 2) < 217 * (3 : ℤ) ^ (s 2) := by
        rw [hm]
        exact_mod_cast hpow4 m
      linarith
  have hsub_iff : (0 < renewalIntSlack s 3 ∧ centeredRenewalSlack s 3 < 0) ↔ s 2 = 3 := by
    constructor
    · rintro ⟨hS_pos, hCS_neg⟩
      have hgt2 : ¬ (s 2 ≤ 2) := fun h => by have := hslack_nonpos_iff.mpr h; linarith
      have hlt4 : ¬ (4 ≤ s 2) := fun h => by have := hpos_iff.mpr h; linarith
      omega
    · intro hs2
      exact ⟨by rw [hS3, hs2]; norm_num, by rw [hCS3, hs2]; norm_num⟩
  refine ⟨hCS3, hsub_iff, hpos_iff, ?_, ?_⟩
  · intro hs2; rw [hCS3, hs2]; norm_num
  · intro hs2; rw [hCS3, hs2]; norm_num

/-! ## 3. Section C2.O3.3: Uniqueness of the $s_3 = 3$ Sub-Ceiling Rung After $(2, 6, 3)$ -/

/-- **Uniqueness of the $s_3 = 3$ Sub-Ceiling Rung After $(2, 6, 3)$
(`four_block_two_six_three_unique_subCeiling_rung_three`, Section C2.O3.3)**:
If `s 0 = 2`, `s 1 = 6`, and `s 2 = 3`, then:
1. `renewalIntSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 4096 * (2 : ℤ) ^ (s 3)`,
2. `centeredRenewalSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 6144 * (2 : ℤ) ^ (s 3)`,
3. `renewalIntSlack s 4 ≤ 0 ↔ s 3 ≤ 2`,
4. `(0 < renewalIntSlack s 4 ∧ centeredRenewalSlack s 4 < 0) ↔ s 3 = 3`
   (with `centeredRenewalSlack s 4 = -1551` at `s 3 = 3`), and
5. `0 < centeredRenewalSlack s 4 ↔ 4 ≤ s 3` (with `centeredRenewalSlack s 4 = 44499` at `s 3 = 4`). -/
theorem four_block_two_six_three_unique_subCeiling_rung_three
    {s : ℕ → ℕ} (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) :
    renewalIntSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 4096 * (2 : ℤ) ^ (s 3) ∧
      centeredRenewalSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 6144 * (2 : ℤ) ^ (s 3) ∧
      (renewalIntSlack s 4 ≤ 0 ↔ s 3 ≤ 2) ∧
      ((0 < renewalIntSlack s 4 ∧ centeredRenewalSlack s 4 < 0) ↔ s 3 = 3) ∧
      (0 < centeredRenewalSlack s 4 ↔ 4 ≤ s 3) ∧
      (s 3 = 3 → centeredRenewalSlack s 4 = -1551) := by
  rcases three_block_two_s1_s2_slack_formula hs0 with ⟨hT3, hS3_raw⟩
  rw [hs1, hs2] at hT3 hS3_raw
  have hT3_eq : blockSteps s 3 = 11 := by omega
  have hS3_eq : renewalIntSlack s 3 = 1763 := by rw [hS3_raw]; norm_num
  have hT4 : blockSteps s 4 = 11 + s 3 := by
    change blockSteps s 3 + s 3 = 11 + s 3
    rw [hT3_eq]
  have hstep4 := (renewalIntSlack_step_and_cocycle s 3 0 0).2.1
  rw [hS3_eq, hT4] at hstep4
  have hS4 : renewalIntSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 4096 * (2 : ℤ) ^ (s 3) := by
    rw [hstep4, show 11 + s 3 + 1 = 12 + s 3 by omega, pow_add (2 : ℤ) 12 (s 3)]
    ring
  have hCS4 : centeredRenewalSlack s 4 = 1763 * (3 : ℤ) ^ (s 3) - 6144 * (2 : ℤ) ^ (s 3) := by
    unfold centeredRenewalSlack
    rw [hS4, hT4, pow_add (2 : ℤ) 11 (s 3)]
    ring
  have hpow3_S : ∀ m : ℕ, 4096 * 2 ^ (m + 3) < 1763 * 3 ^ (m + 3) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 4096 * 2 ^ (m + 1 + 3) = 2 * (4096 * 2 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 1763 * 3 ^ (m + 1 + 3) = 3 * (1763 * 3 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow2_S : ∀ n : ℕ, n ≤ 2 → (1763 * (3 : ℤ) ^ n - 4096 * (2 : ℤ) ^ n) ≤ 0 := by
    intro n hn
    rcases n with _ | _ | _ | n <;> try decide
    omega
  have hpow4_CS : ∀ m : ℕ, 6144 * 2 ^ (m + 4) < 1763 * 3 ^ (m + 4) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 6144 * 2 ^ (m + 1 + 4) = 2 * (6144 * 2 ^ (m + 4)) := by
          rw [show m + 1 + 4 = (m + 4) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 1763 * 3 ^ (m + 1 + 4) = 3 * (1763 * 3 ^ (m + 4)) := by
          rw [show m + 1 + 4 = (m + 4) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow3_CS : ∀ n : ℕ, n ≤ 3 → (1763 * (3 : ℤ) ^ n - 6144 * (2 : ℤ) ^ n) < 0 := by
    intro n hn
    rcases n with _ | _ | _ | _ | n <;> try decide
    omega
  have hslack_nonpos_iff : renewalIntSlack s 4 ≤ 0 ↔ s 3 ≤ 2 := by
    rw [hS4]
    constructor
    · intro hle
      by_contra hnot
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 3 = m + 3 := ⟨s 3 - 3, by omega⟩
      have hlt : (4096 : ℤ) * (2 : ℤ) ^ (s 3) < 1763 * (3 : ℤ) ^ (s 3) := by
        rw [hm]; exact_mod_cast hpow3_S m
      linarith
    · exact hpow2_S (s 3)
  have hpos_iff : 0 < centeredRenewalSlack s 4 ↔ 4 ≤ s 3 := by
    rw [hCS4]
    constructor
    · intro hpos
      by_contra hnot
      have hlt := hpow3_CS (s 3) (by omega)
      linarith
    · intro hge4
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 3 = m + 4 := ⟨s 3 - 4, by omega⟩
      have hlt : (6144 : ℤ) * (2 : ℤ) ^ (s 3) < 1763 * (3 : ℤ) ^ (s 3) := by
        rw [hm]; exact_mod_cast hpow4_CS m
      linarith
  have hsub_iff : (0 < renewalIntSlack s 4 ∧ centeredRenewalSlack s 4 < 0) ↔ s 3 = 3 := by
    constructor
    · rintro ⟨hS_pos, hCS_neg⟩
      have hgt2 : ¬ (s 3 ≤ 2) := fun h => by have := hslack_nonpos_iff.mpr h; linarith
      have hlt4 : ¬ (4 ≤ s 3) := fun h => by have := hpos_iff.mpr h; linarith
      omega
    · intro hs3
      exact ⟨by rw [hS4, hs3]; norm_num, by rw [hCS4, hs3]; norm_num⟩
  refine ⟨hS4, hCS4, hslack_nonpos_iff, hsub_iff, hpos_iff, ?_⟩
  intro hs3; rw [hCS4, hs3]; norm_num

/-! ## 4. Section C2.O3.4: Uniqueness of the $s_4 = 2$ Sub-Ceiling Rung After $(2, 6, 3, 3)$ -/

/-- **Uniqueness of the $s_4 = 2$ Sub-Ceiling Rung After $(2, 6, 3, 3)$
(`five_block_two_six_three_three_unique_subCeiling_rung_two`, Section C2.O3.4)**:
If `s 0 = 2`, `s 1 = 6`, `s 2 = 3`, and `s 3 = 3`, then:
1. `renewalIntSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 32768 * (2 : ℤ) ^ (s 4)`,
2. `centeredRenewalSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 49152 * (2 : ℤ) ^ (s 4)`,
3. `renewalIntSlack s 5 ≤ 0 ↔ s 4 ≤ 1`,
4. `(0 < renewalIntSlack s 5 ∧ centeredRenewalSlack s 5 < 0) ↔ s 4 = 2`
   (with `centeredRenewalSlack s 5 = -63111` at `s 4 = 2`), and
5. `0 < centeredRenewalSlack s 5 ↔ 3 ≤ s 4`. -/
theorem five_block_two_six_three_three_unique_subCeiling_rung_two
    {s : ℕ → ℕ} (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3) :
    renewalIntSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 32768 * (2 : ℤ) ^ (s 4) ∧
      centeredRenewalSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 49152 * (2 : ℤ) ^ (s 4) ∧
      (renewalIntSlack s 5 ≤ 0 ↔ s 4 ≤ 1) ∧
      ((0 < renewalIntSlack s 5 ∧ centeredRenewalSlack s 5 < 0) ↔ s 4 = 2) ∧
      (0 < centeredRenewalSlack s 5 ↔ 3 ≤ s 4) ∧
      (s 4 = 2 → centeredRenewalSlack s 5 = -63111) := by
  have hs_run : ∀ t < 2, s (2 + t) = 3 := by
    intro t ht
    rcases t with _ | _ | t
    · exact hs2
    · exact hs3
    · omega
  rcases two_six_three_run_and_next_two_slack_closed_forms hs0 hs1 hs_run with ⟨hT4_raw, h19S4, _⟩
  change blockSteps s 4 = 8 + 3 * 2 at hT4_raw
  change 19 * renewalIntSlack s 4 = (27 : ℤ) ^ (2 + 1) + 4096 * (8 : ℤ) ^ 2 at h19S4
  have hT4_eq : blockSteps s 4 = 14 := by omega
  have hS4_eq : renewalIntSlack s 4 = 14833 := by omega
  have hT5 : blockSteps s 5 = 14 + s 4 := by
    change blockSteps s 4 + s 4 = 14 + s 4
    rw [hT4_eq]
  have hstep5 := (renewalIntSlack_step_and_cocycle s 4 0 0).2.1
  rw [hS4_eq, hT5] at hstep5
  have hS5 : renewalIntSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 32768 * (2 : ℤ) ^ (s 4) := by
    rw [hstep5, show 14 + s 4 + 1 = 15 + s 4 by omega, pow_add (2 : ℤ) 15 (s 4)]
    ring
  have hCS5 : centeredRenewalSlack s 5 = 14833 * (3 : ℤ) ^ (s 4) - 49152 * (2 : ℤ) ^ (s 4) := by
    unfold centeredRenewalSlack
    rw [hS5, hT5, pow_add (2 : ℤ) 14 (s 4)]
    ring
  have hpow2_S : ∀ m : ℕ, 32768 * 2 ^ (m + 2) < 14833 * 3 ^ (m + 2) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 32768 * 2 ^ (m + 1 + 2) = 2 * (32768 * 2 ^ (m + 2)) := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 14833 * 3 ^ (m + 1 + 2) = 3 * (14833 * 3 ^ (m + 2)) := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow1_S : ∀ n : ℕ, n ≤ 1 → (14833 * (3 : ℤ) ^ n - 32768 * (2 : ℤ) ^ n) ≤ 0 := by
    intro n hn
    rcases n with _ | _ | n <;> try decide
    omega
  have hpow3_CS : ∀ m : ℕ, 49152 * 2 ^ (m + 3) < 14833 * 3 ^ (m + 3) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 49152 * 2 ^ (m + 1 + 3) = 2 * (49152 * 2 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 14833 * 3 ^ (m + 1 + 3) = 3 * (14833 * 3 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow2_CS : ∀ n : ℕ, n ≤ 2 → (14833 * (3 : ℤ) ^ n - 49152 * (2 : ℤ) ^ n) < 0 := by
    intro n hn
    rcases n with _ | _ | _ | n <;> try decide
    omega
  have hslack_nonpos_iff : renewalIntSlack s 5 ≤ 0 ↔ s 4 ≤ 1 := by
    rw [hS5]
    constructor
    · intro hle
      by_contra hnot
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 4 = m + 2 := ⟨s 4 - 2, by omega⟩
      have hlt : (32768 : ℤ) * (2 : ℤ) ^ (s 4) < 14833 * (3 : ℤ) ^ (s 4) := by
        rw [hm]; exact_mod_cast hpow2_S m
      linarith
    · exact hpow1_S (s 4)
  have hpos_iff : 0 < centeredRenewalSlack s 5 ↔ 3 ≤ s 4 := by
    rw [hCS5]
    constructor
    · intro hpos
      by_contra hnot
      have hlt := hpow2_CS (s 4) (by omega)
      linarith
    · intro hge3
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 4 = m + 3 := ⟨s 4 - 3, by omega⟩
      have hlt : (49152 : ℤ) * (2 : ℤ) ^ (s 4) < 14833 * (3 : ℤ) ^ (s 4) := by
        rw [hm]; exact_mod_cast hpow3_CS m
      linarith
  have hsub_iff : (0 < renewalIntSlack s 5 ∧ centeredRenewalSlack s 5 < 0) ↔ s 4 = 2 := by
    constructor
    · rintro ⟨hS_pos, hCS_neg⟩
      have hgt1 : ¬ (s 4 ≤ 1) := fun h => by have := hslack_nonpos_iff.mpr h; linarith
      have hlt3 : ¬ (3 ≤ s 4) := fun h => by have := hpos_iff.mpr h; linarith
      omega
    · intro hs4
      exact ⟨by rw [hS5, hs4]; norm_num, by rw [hCS5, hs4]; norm_num⟩
  refine ⟨hS5, hCS5, hslack_nonpos_iff, hsub_iff, hpos_iff, ?_⟩
  intro hs4; rw [hCS5, hs4]; norm_num

/-! ## 5. Section C2.O3.5: Uniqueness of $s_5 = 10$ & the 6-Block Sub-Ceiling Corridor Theorem -/

/-- **Uniqueness of the $s_5 = 10$ Sub-Ceiling Rung After $(2, 6, 3, 3, 2)$
(`six_block_unique_subCeiling_rung_ten`, Section C2.O3.5)**:
If `s 0 = 2`, `s 1 = 6`, `s 2 = 3`, `s 3 = 3`, and `s 4 = 2`, then:
1. `centeredRenewalSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 196608 * (2 : ℤ) ^ (s 5)`,
2. `(0 < renewalIntSlack s 6 ∧ centeredRenewalSlack s 6 < 0) ↔ s 5 = 10`
   (with `centeredRenewalSlack s 6 = -58132767` at `s 5 = 10`), and
3. `0 < centeredRenewalSlack s 6 ↔ 11 ≤ s 5` (with `centeredRenewalSlack s 6 = 26928291` at `s 5 = 11`). -/
theorem six_block_unique_subCeiling_rung_ten
    {s : ℕ → ℕ} (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3)
    (hs3 : s 3 = 3) (hs4 : s 4 = 2) :
    centeredRenewalSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 196608 * (2 : ℤ) ^ (s 5) ∧
      ((0 < renewalIntSlack s 6 ∧ centeredRenewalSlack s 6 < 0) ↔ s 5 = 10) ∧
      (0 < centeredRenewalSlack s 6 ↔ 11 ≤ s 5) ∧
      (s 5 = 10 → centeredRenewalSlack s 6 = -58132767) ∧
      (s 5 = 11 → centeredRenewalSlack s 6 = 26928291) := by
  rcases six_block_kneading_s5_slack_and_escape_iff_le_nine hs0 hs1 hs2 hs3 hs4 with
    ⟨_, _, hT6, hS6, hesc_iff, _⟩
  have hCS6 : centeredRenewalSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 196608 * (2 : ℤ) ^ (s 5) := by
    unfold centeredRenewalSlack
    rw [hS6, hT6, pow_add (2 : ℤ) 16 (s 5)]
    ring
  have hpow11 : ∀ m : ℕ, 196608 * 2 ^ (m + 11) < 2425 * 3 ^ (m + 11) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 196608 * 2 ^ (m + 1 + 11) = 2 * (196608 * 2 ^ (m + 11)) := by
          rw [show m + 1 + 11 = (m + 11) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 2425 * 3 ^ (m + 1 + 11) = 3 * (2425 * 3 ^ (m + 11)) := by
          rw [show m + 1 + 11 = (m + 11) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow10_le : ∀ n : ℕ, n ≤ 10 → (2425 * (3 : ℤ) ^ n - 196608 * (2 : ℤ) ^ n) < 0 := by
    intro n hn
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try decide
    omega
  have hslack_nonpos_iff : renewalIntSlack s 6 ≤ 0 ↔ s 5 ≤ 9 := by
    rw [← hesc_iff]
    unfold renewalIntSlack
    have hcast : (3 : ℤ) ^ (blockSteps s 6) = ((3 ^ (blockSteps s 6) : ℕ) : ℤ) := by norm_cast
    rw [hcast]
    omega
  have hpos_iff : 0 < centeredRenewalSlack s 6 ↔ 11 ≤ s 5 := by
    rw [hCS6]
    constructor
    · intro hpos
      by_contra hnot
      have hlt := hpow10_le (s 5) (by omega)
      linarith
    · intro hge11
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 5 = m + 11 := ⟨s 5 - 11, by omega⟩
      have hlt : (196608 : ℤ) * (2 : ℤ) ^ (s 5) < 2425 * (3 : ℤ) ^ (s 5) := by
        rw [hm]; exact_mod_cast hpow11 m
      linarith
  have hsub_iff : (0 < renewalIntSlack s 6 ∧ centeredRenewalSlack s 6 < 0) ↔ s 5 = 10 := by
    constructor
    · rintro ⟨hS_pos, hCS_neg⟩
      have hgt9 : ¬ (s 5 ≤ 9) := fun h => by have := hslack_nonpos_iff.mpr h; linarith
      have hlt11 : ¬ (11 ≤ s 5) := fun h => by have := hpos_iff.mpr h; linarith
      omega
    · intro hs5
      exact ⟨by rw [hS6, hs5]; norm_num, by rw [hCS6, hs5]; norm_num⟩
  refine ⟨hCS6, hsub_iff, hpos_iff, ?_, ?_⟩
  · intro hs5; rw [hCS6, hs5]; norm_num
  · intro hs5; rw [hCS6, hs5]; norm_num

/-- **The Unique 6-Block Sub-Ceiling Kneading Corridor Theorem
(`unique_six_block_subCeiling_kneading_corridor`, Section C2.O3.5)**:
Starting from `s 0 = 2`, the 5-tuple `(s 1, s 2, s 3, s 4, s 5) = (6, 3, 3, 2, 10)` is the
**unique** choice of block lengths keeping the trajectory inside the strict sub-ceiling survival
corridor `0 < renewalIntSlack s k ∧ centeredRenewalSlack s k < 0` for all `k ∈ {2, 3, 4, 5, 6}`! -/
theorem unique_six_block_subCeiling_kneading_corridor {s : ℕ → ℕ} (hs0 : s 0 = 2) :
    ((∀ k : ℕ, 2 ≤ k → k ≤ 6 →
      0 < renewalIntSlack s k ∧ centeredRenewalSlack s k < 0) ↔
      (s 1 = 6 ∧ s 2 = 3 ∧ s 3 = 3 ∧ s 4 = 2 ∧ s 5 = 10)) := by
  constructor
  · intro hall
    have h2 := hall 2 (by decide) (by decide)
    have hs1 : s 1 = 6 :=
      (two_block_centeredRenewalSlack_and_unique_subCeiling_rung_six hs0).2.2.1.mp h2
    have h3 := hall 3 (by decide) (by decide)
    have hs2 : s 2 = 3 :=
      (three_block_two_six_unique_subCeiling_rung_three hs0 hs1).2.1.mp h3
    have h4 := hall 4 (by decide) (by decide)
    have hs3 : s 3 = 3 :=
      (four_block_two_six_three_unique_subCeiling_rung_three hs0 hs1 hs2).2.2.2.1.mp h4
    have h5 := hall 5 (by decide) (by decide)
    have hs4 : s 4 = 2 :=
      (five_block_two_six_three_three_unique_subCeiling_rung_two hs0 hs1 hs2 hs3).2.2.2.1.mp h5
    have h6 := hall 6 (by decide) (by decide)
    have hs5 : s 5 = 10 :=
      (six_block_unique_subCeiling_rung_ten hs0 hs1 hs2 hs3 hs4).2.1.mp h6
    exact ⟨hs1, hs2, hs3, hs4, hs5⟩
  · rintro ⟨hs1, hs2, hs3, hs4, hs5⟩ k hk2 hk6
    have h2 :=
      (two_block_centeredRenewalSlack_and_unique_subCeiling_rung_six hs0).2.2.1.mpr hs1
    have h3 :=
      (three_block_two_six_unique_subCeiling_rung_three hs0 hs1).2.1.mpr hs2
    have h4 :=
      (four_block_two_six_three_unique_subCeiling_rung_three hs0 hs1 hs2).2.2.2.1.mpr hs3
    have h5 :=
      (five_block_two_six_three_three_unique_subCeiling_rung_two hs0 hs1 hs2 hs3).2.2.2.1.mpr hs4
    have h6 :=
      (six_block_unique_subCeiling_rung_ten hs0 hs1 hs2 hs3 hs4).2.1.mpr hs5
    have hcases : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

end Mahler.UniqueSubCeilingCorridor
