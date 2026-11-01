import UniqueSubCeilingKneadingCorridor

/-!
# Universal Sub-Ceiling Non-Branching Theorem Across All Horizons $K \in \mathbb{N}$ & 8-Block Kneading Certification $(2, 6, 3, 3, 2, 10, 7, 5)$

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 4 / 20 (Part XIX, Sections C2.O4.1–C2.O4.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O4.1 (Inner Loop 1 / 5) — Exact $(2 : 3)$ Multiplicative Sandwich of the Sub-Ceiling Window
   (`subCeiling_step_sandwich_iff`)**:
   - At any step $N$, `0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0`
     holds if and only if
     `2 * (2 : ℤ) ^ (blockSteps s N + s N) < (3 : ℤ) ^ (s N) * renewalIntSlack s N ∧ (3 : ℤ) ^ (s N) * renewalIntSlack s N < 3 * (2 : ℤ) ^ (blockSteps s N + s N)`.

2. **Section C2.O4.2 (Inner Loop 2 / 5) — Universal At-Most-One Sub-Ceiling Rung Theorem
   (`subCeiling_survival_rung_unique_and_trichotomy`)**:
   - Because the ratio of the upper endpoint $3 \cdot 2^{T + s}$ to the lower endpoint $2 \cdot 2^{T + s}$
     is $3/2$, increasing $s$ by $d \ge 1$ multiplies $3^s \Sigma$ by $3^d \ge 3 \cdot 2^{d-1}$,
     jumping completely across the open window $(2 \cdot 2^{T + s'}, 3 \cdot 2^{T + s'})$!
   - Consequently, for **any** $\Sigma \in \mathbb{Z}$ and $T \in \mathbb{N}$, at most **one**
     $s \in \mathbb{N}$ can satisfy $2 \cdot 2^{T + s} < 3^s \Sigma < 3 \cdot 2^{T + s}$!

3. **Section C2.O4.3 (Inner Loop 3 / 5) — One-Line Witness Criterion
   (`subCeiling_rung_iff_eq_of_witness`)**:
   - If a single integer $s_*$ satisfies $2 \cdot 2^{T + s_*} < 3^{s_*} \Sigma < 3 \cdot 2^{T + s_*}$,
     then for every $s \in \mathbb{N}$:
     - $(2 \cdot 2^{T + s} < 3^s \Sigma \land 3^s \Sigma < 3 \cdot 2^{T + s}) \iff s = s_*$,
     - $3^s \Sigma \le 2 \cdot 2^{T + s} \iff s < s_*$, and
     - $3 \cdot 2^{T + s} \le 3^s \Sigma \iff s_* < s$.

4. **Section C2.O4.4 (Inner Loop 4 / 5) — All-Horizon Sub-Ceiling Corridor Non-Branching Theorem
   (`all_horizon_subCeiling_corridor_unique_sequence`)**:
   - For **every** horizon $K \in \mathbb{N}$, any two sequences $s, s' : \mathbb{N} \to \mathbb{N}$
     with $s_0 = s'_0$ that stay inside the sub-ceiling corridor
     `0 < renewalIntSlack · k ∧ centeredRenewalSlack · k < 0` for all $1 \le k \le K$ satisfy
     `∀ k < K, s k = s' k`!

5. **Section C2.O4.5 (Inner Loop 5 / 5) — Certification of the 7th ($s_6 = 7$) & 8th ($s_7 = 5$) Kneading Rungs
   (`seven_and_eight_block_kneading_corridor_certification`)**:
   - Uses `subCeiling_rung_iff_eq_of_witness` to certify in one line of `norm_num` that after
     $(2, 6, 3, 3, 2, 10)$, the unique 7th sub-ceiling rung is $s_6 = 7$
     ($\Sigma_7 = 2{,}450{,}854{,}955$, $\widehat{\Sigma}_7 = -6{,}139{,}079{,}637$) and the unique
     8th sub-ceiling rung is $s_7 = 5$
     ($\Sigma_8 = 45{,}801{,}940{,}177$, $\widehat{\Sigma}_8 = -229{,}075{,}966{,}767$).
-/

namespace Mahler.UniversalSubCeilingNonBranching

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

/-! ## 1. Section C2.O4.1: Exact $(2 : 3)$ Multiplicative Sandwich of the Sub-Ceiling Window -/

/-- **Exact $(2 : 3)$ Multiplicative Sandwich of the Sub-Ceiling Window
(`subCeiling_step_sandwich_iff`, Section C2.O4.1)**:
For any sequence `s : ℕ → ℕ` and index `N : ℕ`, setting `T_N = blockSteps s N` and
`Σ_N = renewalIntSlack s N`:
1. `renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * Σ_N - 2 * (2 : ℤ) ^ (T_N + s N)`,
2. `centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * Σ_N - 3 * (2 : ℤ) ^ (T_N + s N)`, and
3. `(0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
    (2 * (2 : ℤ) ^ (T_N + s N) < (3 : ℤ) ^ (s N) * Σ_N ∧
      (3 : ℤ) ^ (s N) * Σ_N < 3 * (2 : ℤ) ^ (T_N + s N))`. -/
theorem subCeiling_step_sandwich_iff (s : ℕ → ℕ) (N : ℕ) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 2 * (2 : ℤ) ^ (T_N + s N) ∧
      centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 3 * (2 : ℤ) ^ (T_N + s N) ∧
      ((0 < renewalIntSlack s (N + 1) ∧ centeredRenewalSlack s (N + 1) < 0) ↔
        (2 * (2 : ℤ) ^ (T_N + s N) < (3 : ℤ) ^ (s N) * S_N ∧
          (3 : ℤ) ^ (s N) * S_N < 3 * (2 : ℤ) ^ (T_N + s N))) := by
  intro T_N S_N
  have hstep := (renewalIntSlack_step_and_cocycle s N 0 0).2.1
  have hT_succ : blockSteps s (N + 1) = T_N + s N := rfl
  have hS_succ : renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 2 * (2 : ℤ) ^ (T_N + s N) := by
    dsimp [S_N]
    rw [hstep, hT_succ, pow_succ']
  have hCS_succ :
      centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * S_N - 3 * (2 : ℤ) ^ (T_N + s N) := by
    unfold centeredRenewalSlack
    rw [hS_succ, hT_succ]
    ring
  refine ⟨hS_succ, hCS_succ, ?_⟩
  rw [hS_succ, hCS_succ]
  constructor <;> intro h <;> constructor <;> linarith

/-! ## 2. Section C2.O4.2 & C2.O4.3: Universal At-Most-One Sub-Ceiling Rung & Witness Criterion -/

/-- **Universal Sub-Ceiling Rung Trichotomy & Uniqueness
(`subCeiling_survival_rung_unique_and_trichotomy`, Section C2.O4.2)**:
For any integer `S_N : ℤ`, step sum `T_N : ℕ`, and block lengths `s₁, s₂ : ℕ`:
1. If `s₁ < s₂` and `2 * (2 : ℤ) ^ (T_N + s₁) < (3 : ℤ) ^ s₁ * S_N`, then
   `3 * (2 : ℤ) ^ (T_N + s₂) < (3 : ℤ) ^ s₂ * S_N`,
2. If `s₁ < s₂` and `(3 : ℤ) ^ s₂ * S_N < 3 * (2 : ℤ) ^ (T_N + s₂)`, then
   `(3 : ℤ) ^ s₁ * S_N < 2 * (2 : ℤ) ^ (T_N + s₁)`, and
3. If both `s₁` and `s₂` satisfy the sub-ceiling window
   `2 * (2 : ℤ) ^ (T_N + s) < (3 : ℤ) ^ s * S_N ∧ (3 : ℤ) ^ s * S_N < 3 * (2 : ℤ) ^ (T_N + s)`,
   then `s₁ = s₂`! -/
theorem subCeiling_survival_rung_unique_and_trichotomy
    (S_N : ℤ) (T_N s₁ s₂ : ℕ) :
    (s₁ < s₂ → 2 * (2 : ℤ) ^ (T_N + s₁) < (3 : ℤ) ^ s₁ * S_N →
      3 * (2 : ℤ) ^ (T_N + s₂) < (3 : ℤ) ^ s₂ * S_N) ∧
      (s₁ < s₂ → (3 : ℤ) ^ s₂ * S_N < 3 * (2 : ℤ) ^ (T_N + s₂) →
        (3 : ℤ) ^ s₁ * S_N < 2 * (2 : ℤ) ^ (T_N + s₁)) ∧
      ((2 * (2 : ℤ) ^ (T_N + s₁) < (3 : ℤ) ^ s₁ * S_N ∧
        (3 : ℤ) ^ s₁ * S_N < 3 * (2 : ℤ) ^ (T_N + s₁)) →
        (2 * (2 : ℤ) ^ (T_N + s₂) < (3 : ℤ) ^ s₂ * S_N ∧
          (3 : ℤ) ^ s₂ * S_N < 3 * (2 : ℤ) ^ (T_N + s₂)) →
        s₁ = s₂) := by
  have hjump :
      ∀ a b : ℕ, a < b →
        2 * (2 : ℤ) ^ (T_N + a) < (3 : ℤ) ^ a * S_N →
          3 * (2 : ℤ) ^ (T_N + b) < (3 : ℤ) ^ b * S_N := by
    intro a b hab hgt
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, b = a + (m + 1) := ⟨b - a - 1, by omega⟩
    have hpow_m : (2 : ℤ) ^ m ≤ (3 : ℤ) ^ m := by
      exact_mod_cast Nat.pow_le_pow_left (by decide) m
    have h3m_pos : (0 : ℤ) < (3 : ℤ) ^ (m + 1) := pow_pos (by decide) (m + 1)
    have hmul1 :
        (3 : ℤ) ^ (m + 1) * (2 * (2 : ℤ) ^ (T_N + a)) <
          (3 : ℤ) ^ (m + 1) * ((3 : ℤ) ^ a * S_N) :=
      mul_lt_mul_of_pos_left hgt h3m_pos
    have hmul2 :
        3 * (2 : ℤ) ^ (T_N + (a + (m + 1))) ≤
          (3 : ℤ) ^ (m + 1) * (2 * (2 : ℤ) ^ (T_N + a)) := by
      calc
        3 * (2 : ℤ) ^ (T_N + (a + (m + 1))) =
            (2 : ℤ) ^ m * (3 * (2 * (2 : ℤ) ^ (T_N + a))) := by
          rw [show T_N + (a + (m + 1)) = (T_N + a) + m + 1 by omega, pow_add, pow_add]
          ring
        _ ≤ (3 : ℤ) ^ m * (3 * (2 * (2 : ℤ) ^ (T_N + a))) :=
          mul_le_mul_of_nonneg_right hpow_m (by positivity)
        _ = (3 : ℤ) ^ (m + 1) * (2 * (2 : ℤ) ^ (T_N + a)) := by
          rw [pow_succ]
          ring
    have hrhs :
        (3 : ℤ) ^ (m + 1) * ((3 : ℤ) ^ a * S_N) = (3 : ℤ) ^ (a + (m + 1)) * S_N := by
      rw [pow_add]
      ring
    linarith
  refine ⟨hjump s₁ s₂, ?_, ?_⟩
  · intro hlt hlt2
    by_contra hnot
    push_neg at hnot
    have hle_strict : 2 * (2 : ℤ) ^ (T_N + s₁) < (3 : ℤ) ^ s₁ * S_N ∨
        2 * (2 : ℤ) ^ (T_N + s₁) = (3 : ℤ) ^ s₁ * S_N := lt_or_eq_of_le hnot
    rcases hle_strict with hgt1 | heq1
    · have hj := hjump s₁ s₂ hlt hgt1
      linarith
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, s₂ = s₁ + (m + 1) := ⟨s₂ - s₁ - 1, by omega⟩
      have hpow_m : (2 : ℤ) ^ m ≤ (3 : ℤ) ^ m := by
        exact_mod_cast Nat.pow_le_pow_left (by decide) m
      have hge :
          3 * (2 : ℤ) ^ (T_N + (s₁ + (m + 1))) ≤ (3 : ℤ) ^ (s₁ + (m + 1)) * S_N := by
        calc
          3 * (2 : ℤ) ^ (T_N + (s₁ + (m + 1))) =
              (2 : ℤ) ^ m * (3 * (2 * (2 : ℤ) ^ (T_N + s₁))) := by
            rw [show T_N + (s₁ + (m + 1)) = (T_N + s₁) + m + 1 by omega, pow_add, pow_add]
            ring
          _ ≤ (3 : ℤ) ^ m * (3 * (2 * (2 : ℤ) ^ (T_N + s₁))) :=
            mul_le_mul_of_nonneg_right hpow_m (by positivity)
          _ = (3 : ℤ) ^ (m + 1) * ((3 : ℤ) ^ s₁ * S_N) := by
            rw [← heq1, pow_succ]
            ring
          _ = (3 : ℤ) ^ (s₁ + (m + 1)) * S_N := by
            rw [pow_add]
            ring
      linarith
  · rintro ⟨h1_low, h1_high⟩ ⟨h2_low, h2_high⟩
    rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
    · have hj := hjump s₁ s₂ hlt h1_low
      linarith
    · rfl
    · have hj := hjump s₂ s₁ hgt h2_low
      linarith

/-- **One-Line Witness Criterion for the Sub-Ceiling Rung (`subCeiling_rung_iff_eq_of_witness`,
Section C2.O4.3)**:
If a single integer `s_star : ℕ` satisfies
`2 * (2 : ℤ) ^ (T_N + s_star) < (3 : ℤ) ^ s_star * S_N` and
`(3 : ℤ) ^ s_star * S_N < 3 * (2 : ℤ) ^ (T_N + s_star)`, then for every `s : ℕ`:
1. `(2 * (2 : ℤ) ^ (T_N + s) < (3 : ℤ) ^ s * S_N ∧ (3 : ℤ) ^ s * S_N < 3 * (2 : ℤ) ^ (T_N + s)) ↔ s = s_star`,
2. `(3 : ℤ) ^ s * S_N ≤ 2 * (2 : ℤ) ^ (T_N + s) ↔ s < s_star`, and
3. `3 * (2 : ℤ) ^ (T_N + s) ≤ (3 : ℤ) ^ s * S_N ↔ s_star < s`. -/
theorem subCeiling_rung_iff_eq_of_witness
    {S_N : ℤ} {T_N s_star : ℕ}
    (hlow_star : 2 * (2 : ℤ) ^ (T_N + s_star) < (3 : ℤ) ^ s_star * S_N)
    (hhigh_star : (3 : ℤ) ^ s_star * S_N < 3 * (2 : ℤ) ^ (T_N + s_star)) (s : ℕ) :
    ((2 * (2 : ℤ) ^ (T_N + s) < (3 : ℤ) ^ s * S_N ∧
      (3 : ℤ) ^ s * S_N < 3 * (2 : ℤ) ^ (T_N + s)) ↔ s = s_star) ∧
      ((3 : ℤ) ^ s * S_N ≤ 2 * (2 : ℤ) ^ (T_N + s) ↔ s < s_star) ∧
      (3 * (2 : ℤ) ^ (T_N + s) ≤ (3 : ℤ) ^ s * S_N ↔ s_star < s) := by
  have htri1 := subCeiling_survival_rung_unique_and_trichotomy S_N T_N s s_star
  have htri2 := subCeiling_survival_rung_unique_and_trichotomy S_N T_N s_star s
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hs
      exact htri1.2.2 hs ⟨hlow_star, hhigh_star⟩
    · rintro rfl
      exact ⟨hlow_star, hhigh_star⟩
  · constructor
    · intro hle
      rcases lt_trichotomy s s_star with hlt | rfl | hgt
      · exact hlt
      · linarith
      · have hj := htri2.1 hgt hlow_star
        have h2_pos : (0 : ℤ) < (2 : ℤ) ^ (T_N + s) := pow_pos (by decide) _
        linarith
    · intro hlt
      exact le_of_lt (htri1.2.1 hlt hhigh_star)
  · constructor
    · intro hge
      rcases lt_trichotomy s_star s with hlt | rfl | hgt
      · exact hlt
      · linarith
      · have hj := htri1.2.1 hgt hhigh_star
        have h2_pos : (0 : ℤ) < (2 : ℤ) ^ (T_N + s) := pow_pos (by decide) _
        linarith
    · intro hgt
      exact le_of_lt (htri2.1 hgt hlow_star)

/-! ## 3. Section C2.O4.4: All-Horizon Sub-Ceiling Corridor Non-Branching Theorem -/

/-- If two gap sequences agree on `t < k`, their `blockSteps`, `renewalIntSlack`, and
`centeredRenewalSlack` at `k` are equal. -/
theorem blockSteps_and_slacks_congr {s₁ s₂ : ℕ → ℕ} {k : ℕ}
    (hmatch : ∀ t < k, s₁ t = s₂ t) :
    blockSteps s₁ k = blockSteps s₂ k ∧
      renewalIntSlack s₁ k = renewalIntSlack s₂ k ∧
      centeredRenewalSlack s₁ k = centeredRenewalSlack s₂ k := by
  rcases blockSteps_and_renewalNumerator_congr hmatch with ⟨hT, hA⟩
  have hS : renewalIntSlack s₁ k = renewalIntSlack s₂ k := by
    unfold renewalIntSlack
    rw [hT, hA]
  have hCS : centeredRenewalSlack s₁ k = centeredRenewalSlack s₂ k := by
    unfold centeredRenewalSlack
    rw [hS, hT]
  exact ⟨hT, hS, hCS⟩

/-- **All-Horizon Sub-Ceiling Corridor Non-Branching Theorem
(`all_horizon_subCeiling_corridor_unique_sequence`, Section C2.O4.4)**:
For **every** horizon `K : ℕ`, if two gap sequences `s₁, s₂ : ℕ → ℕ` satisfy `s₁ 0 = s₂ 0` and
both remain inside the strict sub-ceiling survival corridor
`0 < renewalIntSlack sᵢ (k + 1) ∧ centeredRenewalSlack sᵢ (k + 1) < 0` for all `1 ≤ k < K`,
then `∀ k < K, s₁ k = s₂ k`! -/
theorem all_horizon_subCeiling_corridor_unique_sequence
    {s₁ s₂ : ℕ → ℕ} {K : ℕ}
    (h0 : s₁ 0 = s₂ 0)
    (hcor₁ : ∀ k : ℕ, 1 ≤ k → k < K →
      0 < renewalIntSlack s₁ (k + 1) ∧ centeredRenewalSlack s₁ (k + 1) < 0)
    (hcor₂ : ∀ k : ℕ, 1 ≤ k → k < K →
      0 < renewalIntSlack s₂ (k + 1) ∧ centeredRenewalSlack s₂ (k + 1) < 0) :
    ∀ k < K, s₁ k = s₂ k := by
  induction K with
  | zero => intro k hk; omega
  | succ K ih =>
      rcases Nat.eq_zero_or_pos K with rfl | hK_pos
      · intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        exact h0
      · have ih' := ih (fun k hk1 hkK => hcor₁ k hk1 (by omega))
          (fun k hk1 hkK => hcor₂ k hk1 (by omega))
        rcases blockSteps_and_slacks_congr ih' with ⟨hTK, hSK, _⟩
        have hc1 := (subCeiling_step_sandwich_iff s₁ K).2.2.mp (hcor₁ K hK_pos (by omega))
        have hc2 := (subCeiling_step_sandwich_iff s₂ K).2.2.mp (hcor₂ K hK_pos (by omega))
        rw [hTK, hSK] at hc1
        have huniq := (subCeiling_survival_rung_unique_and_trichotomy
          (renewalIntSlack s₂ K) (blockSteps s₂ K) (s₁ K) (s₂ K)).2.2 hc1 hc2
        intro k hk
        rcases Nat.eq_or_lt_of_le (by omega : k ≤ K) with rfl | hlt
        · exact huniq
        · exact ih' k hlt

/-! ## 4. Section C2.O4.5: Certification of the 7th ($s_6 = 7$) & 8th ($s_7 = 5$) Kneading Rungs -/

/-- **One-Line Certification of the 7th ($s_6 = 7$) and 8th ($s_7 = 5$) Sub-Ceiling Kneading Rungs
(`seven_and_eight_block_kneading_corridor_certification`, Section C2.O4.5)**:
Suppose `s 0 = 2, s 1 = 6, s 2 = 3, s 3 = 3, s 4 = 2, s 5 = 10`. Then:
1. `(0 < renewalIntSlack s 7 ∧ centeredRenewalSlack s 7 < 0) ↔ s 6 = 7`,
2. When `s 6 = 7`:
   - `blockSteps s 7 = 33`,
   - `renewalIntSlack s 7 = 2450854955`,
   - `centeredRenewalSlack s 7 = -6139079637`, and
   - `(0 < renewalIntSlack s 8 ∧ centeredRenewalSlack s 8 < 0) ↔ s 7 = 5`, and
3. When `s 6 = 7` and `s 7 = 5`:
   - `blockSteps s 8 = 38`,
   - `renewalIntSlack s 8 = 45801940177`, and
   - `centeredRenewalSlack s 8 = -229075966767`. -/
theorem seven_and_eight_block_kneading_corridor_certification
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3)
    (hs3 : s 3 = 3) (hs4 : s 4 = 2) (hs5 : s 5 = 10) :
    ((0 < renewalIntSlack s 7 ∧ centeredRenewalSlack s 7 < 0) ↔ s 6 = 7) ∧
      (s 6 = 7 →
        blockSteps s 7 = 33 ∧
          renewalIntSlack s 7 = 2450854955 ∧
          centeredRenewalSlack s 7 = -6139079637 ∧
          ((0 < renewalIntSlack s 8 ∧ centeredRenewalSlack s 8 < 0) ↔ s 7 = 5)) ∧
      (s 6 = 7 → s 7 = 5 →
        blockSteps s 8 = 38 ∧
          renewalIntSlack s 8 = 45801940177 ∧
          centeredRenewalSlack s 8 = -229075966767) := by
  rcases six_block_kneading_s5_slack_and_escape_iff_le_nine hs0 hs1 hs2 hs3 hs4 with
    ⟨_, _, hT6_raw, _, _, hS6_10⟩
  have hT6 : blockSteps s 6 = 26 := by rw [hT6_raw, hs5]
  have hS6 : renewalIntSlack s 6 = 8976097 := hS6_10 hs5
  have hsand6 := (subCeiling_step_sandwich_iff s 6).2.2
  rw [hT6, hS6] at hsand6
  have hwit7 := (subCeiling_rung_iff_eq_of_witness (S_N := 8976097) (T_N := 26) (s_star := 7)
    (by norm_num) (by norm_num) (s 6)).1
  have hiff7 : (0 < renewalIntSlack s 7 ∧ centeredRenewalSlack s 7 < 0) ↔ s 6 = 7 :=
    hsand6.trans hwit7
  refine ⟨hiff7, ?_, ?_⟩
  · intro hs6
    have hT7 : blockSteps s 7 = 33 := by
      change blockSteps s 6 + s 6 = 33
      rw [hT6, hs6]
    have hS7_eq := (subCeiling_step_sandwich_iff s 6).1
    have hCS7_eq := (subCeiling_step_sandwich_iff s 6).2.1
    rw [hT6, hS6, hs6] at hS7_eq hCS7_eq
    have hS7 : renewalIntSlack s 7 = 2450854955 := by rw [hS7_eq]; norm_num
    have hCS7 : centeredRenewalSlack s 7 = -6139079637 := by rw [hCS7_eq]; norm_num
    have hsand7 := (subCeiling_step_sandwich_iff s 7).2.2
    rw [hT7, hS7] at hsand7
    have hwit8 := (subCeiling_rung_iff_eq_of_witness (S_N := 2450854955) (T_N := 33) (s_star := 5)
      (by norm_num) (by norm_num) (s 7)).1
    exact ⟨hT7, hS7, hCS7, hsand7.trans hwit8⟩
  · intro hs6 hs7
    have hT7 : blockSteps s 7 = 33 := by
      change blockSteps s 6 + s 6 = 33
      rw [hT6, hs6]
    have hS7_eq := (subCeiling_step_sandwich_iff s 6).1
    rw [hT6, hS6, hs6] at hS7_eq
    have hS7 : renewalIntSlack s 7 = 2450854955 := by rw [hS7_eq]; norm_num
    have hT8 : blockSteps s 8 = 38 := by
      change blockSteps s 7 + s 7 = 38
      rw [hT7, hs7]
    have hS8_eq := (subCeiling_step_sandwich_iff s 7).1
    have hCS8_eq := (subCeiling_step_sandwich_iff s 7).2.1
    rw [hT7, hS7, hs7] at hS8_eq hCS8_eq
    exact ⟨hT8, by rw [hS8_eq]; norm_num, by rw [hCS8_eq]; norm_num⟩

end Mahler.UniversalSubCeilingNonBranching
