import UniversalConstantRungRunAndKneading30

/-!
# Explicit Finite Run Bound $m j < 2 T_N + 3 m + 2$, Exclusion of Eventually-Constant Sub-Ceiling Words & 33-Block ($T_{33} = 164$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 13 / 20 (Part XXVIII, Sections C2.O13.1–C2.O13.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O13.1 (Inner Loop 1 / 5) — Two-Parameter Exponential Dominance $2 \cdot 2^{A+B} < 3^B$ ($2 A + 2 \le B$)
   (`two_mul_two_pow_add_lt_three_pow_of_two_mul_add_two_le`)**:
   - For all `A, B : ℕ` with `2 * A + 2 ≤ B`, `2 * (2 : ℤ) ^ (A + B) < (3 : ℤ) ^ B`.

2. **Section C2.O13.2 (Inner Loop 2 / 5) — Finite-Horizon Escape Below $\rho_*(m)$ and Ceiling Restoration Above $\rho_*(m)$
   (`constant_rung_run_escapes_or_restores_ceiling_at_horizon`)**:
   - Whenever `1 ≤ m`, `∀ t < j, s (N + t) = m`, and `2 * blockSteps s N + 3 * m + 2 ≤ m * j`:
     - Below $\rho_*(m)$ (`((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N < (2 : ℤ) ^ (T_N + m + 1)`):
       `renewalIntSlack s (N + j) < 0` (Escape),
     - Above $\rho_*(m)$ (`(2 : ℤ) ^ (T_N + m + 1) < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N`):
       `0 < centeredRenewalSlack s (N + j)` (Full Ceiling Restoration).

3. **Section C2.O13.3 (Inner Loop 3 / 5) — Unconditional Exclusion of Eventually-Constant Sub-Ceiling Words
   (`no_subCeiling_constant_rung_run_exceeds_horizon`)**:
   - Whenever `renewalIntSlack s N % 2 = 1`, `1 ≤ m`, `∀ t < j, s (N + t) = m`, and
     `2 * blockSteps s N + 3 * m + 2 ≤ m * j`:
     `renewalIntSlack s (N + j) < 0 ∨ 0 < centeredRenewalSlack s (N + j)` and
     `¬ (0 < renewalIntSlack s (N + j) ∧ centeredRenewalSlack s (N + j) < 0)`.
   - Consequently, no sequence `s` with `∀ k, 1 ≤ s k` can become eventually constant inside the
     sub-ceiling corridor.

4. **Sections C2.O13.4 & C2.O13.5 (Inner Loops 4–5 / 5) — Certification of Blocks 31, 32, and 33 ($s_{30} = 5, s_{31} = 3, s_{32} = 4$, $T_{33} = 164$) & Mod-$2^{165}$ Uniqueness
   (`thirtyone_to_thirtythree_block_kneading_corridor_and_two_pow_165_uniqueness`)**:
   - Certifies blocks 31–33 ($T_{33} = 164$) and proves $2^{165} \mid (b_2 - b_1)$ and $2^{165} \le b_2$
     for any two seeds sharing the 33-block prefix.
-/

namespace Mahler.ConstantRungBoundAndKneading33

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

/-! ## 1. Section C2.O13.1: Two-Parameter Exponential Dominance $2 \cdot 2^{A+B} < 3^B$ ($2 A + 2 \le B$) -/

/-- **Two-Parameter Exponential Dominance $2 \cdot 2^{A+B} < 3^B$ ($2 A + 2 \le B$)
(`two_mul_two_pow_add_lt_three_pow_of_two_mul_add_two_le`, Section C2.O13.1)**:
For all `A, B : ℕ` with `2 * A + 2 ≤ B`, `2 * (2 : ℤ) ^ (A + B) < (3 : ℤ) ^ B`. -/
theorem two_mul_two_pow_add_lt_three_pow_of_two_mul_add_two_le
    {A B : ℕ} (hAB : 2 * A + 2 ≤ B) :
    2 * (2 : ℤ) ^ (A + B) < (3 : ℤ) ^ B := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, B = (2 * A + 2) + r := ⟨B - (2 * A + 2), by omega⟩
  induction r with
  | zero =>
      have h0 := two_mul_two_pow_three_mul_add_two_lt_three_pow A
      rw [show A + (2 * A + 2 + 0) = 3 * A + 2 by omega,
          show 2 * A + 2 + 0 = 2 * A + 2 by omega]
      exact h0
  | succ r ih =>
      have ih' := ih (by omega)
      have h1 : 2 * (2 : ℤ) ^ (A + (2 * A + 2 + (r + 1))) =
          2 * (2 * (2 : ℤ) ^ (A + (2 * A + 2 + r))) := by
        rw [show A + (2 * A + 2 + (r + 1)) = (A + (2 * A + 2 + r)) + 1 by omega, pow_succ]
        ring
      have h2 : (3 : ℤ) ^ (2 * A + 2 + (r + 1)) = 3 * (3 : ℤ) ^ (2 * A + 2 + r) := by
        rw [show 2 * A + 2 + (r + 1) = (2 * A + 2 + r) + 1 by omega, pow_succ]
        ring
      have hpos : 0 < 2 * (2 : ℤ) ^ (A + (2 * A + 2 + r)) := by positivity
      omega

/-! ## 2. Sections C2.O13.2 & C2.O13.3: Finite-Horizon Escape/Restoration & Exclusion of Eventually-Constant Sub-Ceiling Words -/

/-- Auxiliary inequality: `(2 : ℤ) ^ m < (3 : ℤ) ^ m` for every `1 ≤ m`. -/
theorem two_pow_lt_three_pow_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    (2 : ℤ) ^ m < (3 : ℤ) ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
      have ih' := ih (by omega)
      have h1 : (2 : ℤ) ^ (k + 1 + 1) = 2 * (2 : ℤ) ^ (k + 1) := by rw [pow_succ]; ring
      have h2 : (3 : ℤ) ^ (k + 1 + 1) = 3 * (3 : ℤ) ^ (k + 1) := by rw [pow_succ]; ring
      have hpos : 0 < (2 : ℤ) ^ (k + 1) := by positivity
      omega

/-- **Finite-Horizon Escape Below $\rho_*(m)$ and Ceiling Restoration Above $\rho_*(m)$
(`constant_rung_run_escapes_or_restores_ceiling_at_horizon`, Section C2.O13.2)**:
For any sequence `s : ℕ → ℕ`, step `N : ℕ`, rung `1 ≤ m`, and run length `j : ℕ` with
`∀ t < j, s (N + t) = m` and `2 * blockSteps s N + 3 * m + 2 ≤ m * j`, setting
`T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
1. If `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N < (2 : ℤ) ^ (T_N + m + 1)`, then
   `renewalIntSlack s (N + j) < 0` (Escape!).
2. If `(2 : ℤ) ^ (T_N + m + 1) < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N`, then
   `0 < centeredRenewalSlack s (N + j)` (Full Ceiling Restoration!). -/
theorem constant_rung_run_escapes_or_restores_ceiling_at_horizon
    {s : ℕ → ℕ} {N m j : ℕ} (hm1 : 1 ≤ m)
    (hm : ∀ t < j, s (N + t) = m)
    (hhor : 2 * blockSteps s N + 3 * m + 2 ≤ m * j) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N < (2 : ℤ) ^ (T_N + m + 1) →
      renewalIntSlack s (N + j) < 0) ∧
      ((2 : ℤ) ^ (T_N + m + 1) < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N →
        0 < centeredRenewalSlack s (N + j)) := by
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
  have hlt_m := two_pow_lt_three_pow_of_one_le hm1
  have hMm_pos : 0 < (3 : ℤ) ^ m - (2 : ℤ) ^ m := by omega
  have hdom1 := two_mul_two_pow_add_lt_three_pow_of_two_mul_add_two_le
    (A := T_N + m) (B := m * j) (by omega)
  have hdom1' : (2 : ℤ) ^ (T_N + m + 1 + m * j) < (3 : ℤ) ^ (m * j) := by
    calc
      (2 : ℤ) ^ (T_N + m + 1 + m * j)
          = 2 * (2 : ℤ) ^ ((T_N + m) + m * j) := by
            rw [show T_N + m + 1 + m * j = ((T_N + m) + m * j) + 1 by omega, pow_succ]
            ring
      _ < (3 : ℤ) ^ (m * j) := hdom1
  refine ⟨?_, ?_⟩
  · intro hbelow
    have hle_neg1 : ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1) ≤ -1 := by omega
    have h3mj_nonneg : 0 ≤ (3 : ℤ) ^ (m * j) := by positivity
    have hmul_le :
        (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) ≤
          (3 : ℤ) ^ (m * j) * (-1) :=
      mul_le_mul_of_nonneg_left hle_neg1 h3mj_nonneg
    have hS_mul_neg : ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) < 0 := by omega
    by_contra hge
    push_neg at hge
    have hnonneg : 0 ≤ ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) :=
      mul_nonneg (le_of_lt hMm_pos) hge
    omega
  · intro habove
    have hge1 : 1 ≤ ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1) := by omega
    have h3mj_nonneg : 0 ≤ (3 : ℤ) ^ (m * j) := by positivity
    have hmul_ge :
        (3 : ℤ) ^ (m * j) * 1 ≤
          (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N - (2 : ℤ) ^ (T_N + m + 1)) :=
      mul_le_mul_of_nonneg_left hge1 h3mj_nonneg
    have hj_pos : 1 ≤ j := by
      by_contra hj0
      have hj_eq : j = 0 := by omega
      rw [hj_eq] at hhor
      omega
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = 1 + k := ⟨j - 1, by omega⟩
    have hdom2 := two_mul_two_pow_add_lt_three_pow_of_two_mul_add_two_le
      (A := T_N + m) (B := m * k) (by
        have hmk : m * (1 + k) = m + m * k := by ring
        omega)
    have h2_pos : 0 < (2 : ℤ) ^ (T_N + m * (1 + k)) := by positivity
    have h2m_pos : 0 < (2 : ℤ) ^ m := by positivity
    have h3m_pos : 0 < (3 : ℤ) ^ m := by positivity
    have hcoeff_lt : (3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m < (3 : ℤ) ^ m := by omega
    have hterm_lt1 :
        ((3 : ℤ) ^ m - 3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ (T_N + m * (1 + k)) <
          (3 : ℤ) ^ m * (2 : ℤ) ^ (T_N + m * (1 + k)) :=
      mul_lt_mul_of_pos_right hcoeff_lt h2_pos
    have h2_split : (2 : ℤ) ^ (T_N + m * (1 + k)) = (2 : ℤ) ^ ((T_N + m) + m * k) := by
      rw [show T_N + m * (1 + k) = (T_N + m) + m * k by ring]
    have h2_lt_3mk : (2 : ℤ) ^ (T_N + m * (1 + k)) < (3 : ℤ) ^ (m * k) := by
      have hpos_pow : 0 < (2 : ℤ) ^ ((T_N + m) + m * k) := by positivity
      rw [h2_split]
      omega
    have hterm_lt2 :
        (3 : ℤ) ^ m * (2 : ℤ) ^ (T_N + m * (1 + k)) < (3 : ℤ) ^ (m * (1 + k)) := by
      calc
        (3 : ℤ) ^ m * (2 : ℤ) ^ (T_N + m * (1 + k))
            < (3 : ℤ) ^ m * (3 : ℤ) ^ (m * k) :=
              mul_lt_mul_of_pos_left h2_lt_3mk h3m_pos
        _ = (3 : ℤ) ^ (m * (1 + k)) := by
              rw [show m * (1 + k) = m + m * k by ring, pow_add]
    have hC_mul_pos : 0 < ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * centeredRenewalSlack s (N + (1 + k)) := by
      omega
    exact pos_of_mul_pos_right hC_mul_pos (le_of_lt hMm_pos)

/-- **Unconditional Exclusion of Eventually-Constant Sub-Ceiling Words
(`no_subCeiling_constant_rung_run_exceeds_horizon`, Section C2.O13.3)**:
1. Whenever `renewalIntSlack s N % 2 = 1`, `1 ≤ m`, `∀ t < j, s (N + t) = m`, and
   `2 * blockSteps s N + 3 * m + 2 ≤ m * j`:
   `renewalIntSlack s (N + j) < 0 ∨ 0 < centeredRenewalSlack s (N + j)` and
   `¬ (0 < renewalIntSlack s (N + j) ∧ centeredRenewalSlack s (N + j) < 0)`.
2. For any sequence `s : ℕ → ℕ` with `∀ k, 1 ≤ s k`, it is impossible for `s` to become
   eventually constant while remaining in the sub-ceiling corridor:
   `¬ (∃ N m : ℕ, (∀ t : ℕ, s (N + t) = m) ∧
        ∀ k : ℕ, 0 < renewalIntSlack s (N + k) ∧ centeredRenewalSlack s (N + k) < 0)`. -/
theorem no_subCeiling_constant_rung_run_exceeds_horizon
    {s : ℕ → ℕ} {N m j : ℕ}
    (hodd : renewalIntSlack s N % 2 = 1) (hm1 : 1 ≤ m)
    (hm : ∀ t < j, s (N + t) = m)
    (hhor : 2 * blockSteps s N + 3 * m + 2 ≤ m * j) :
    (renewalIntSlack s (N + j) < 0 ∨ 0 < centeredRenewalSlack s (N + j)) ∧
      ¬ (0 < renewalIntSlack s (N + j) ∧ centeredRenewalSlack s (N + j) < 0) ∧
      (∀ s' : ℕ → ℕ, (∀ k : ℕ, 1 ≤ s' k) →
        ¬ (∃ N' m' : ℕ, (∀ t : ℕ, s' (N' + t) = m') ∧
            ∀ k : ℕ, 0 < renewalIntSlack s' (N' + k) ∧ centeredRenewalSlack s' (N' + k) < 0)) := by
  have hne := (repelling_fixed_point_non_vanishing_for_all_rungs hodd (blockSteps s N) hm1).1
  have hesc := constant_rung_run_escapes_or_restores_ceiling_at_horizon hm1 hm hhor
  have hor : renewalIntSlack s (N + j) < 0 ∨ 0 < centeredRenewalSlack s (N + j) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hesc.1 hlt)
    · exact Or.inr (hesc.2 hgt)
  refine ⟨hor, ?_, ?_⟩
  · rintro ⟨hpos, hneg⟩
    rcases hor with h1 | h2 <;> omega
  · intro s' hs' ⟨N', m', hm', hsub⟩
    have hm'1 : 1 ≤ m' := by
      have h0 := hm' 0
      have hge := hs' (N' + 0)
      omega
    have hodd' : renewalIntSlack s' N' % 2 = 1 :=
      (renewalIntSlack_eq_return_pinch_margin_and_odd (fun k _ => hs' k)).2.1
    set j' := 2 * blockSteps s' N' + 3 * m' + 2
    have hhor' : 2 * blockSteps s' N' + 3 * m' + 2 ≤ m' * j' := by
      have h1 : 1 * j' ≤ m' * j' := Nat.mul_le_mul_right j' hm'1
      omega
    have hesc' := constant_rung_run_escapes_or_restores_ceiling_at_horizon
      hm'1 (fun t _ => hm' t) hhor'
    have hne' := (repelling_fixed_point_non_vanishing_for_all_rungs hodd' (blockSteps s' N') hm'1).1
    have hsub' := hsub j'
    rcases lt_or_gt_of_ne hne' with hlt' | hgt'
    · have h1 := hesc'.1 hlt'
      have h2 := hsub'.1
      omega
    · have h1 := hesc'.2 hgt'
      have h2 := hsub'.2
      omega

/-! ## 3. Sections C2.O13.4 & C2.O13.5: Certification of Blocks 31, 32, and 33 ($T_{33} = 164$) & Mod-$2^{165}$ Uniqueness -/

/-- **Certification of the 31st ($s_{30} = 5$), 32nd ($s_{31} = 3$), and 33rd ($s_{32} = 4$) Kneading Rungs & Mod-$2^{165}$ Uniqueness
(`thirtyone_to_thirtythree_block_kneading_corridor_and_two_pow_165_uniqueness`, Sections C2.O13.4–C2.O13.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 30-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4)$:
1. `(0 < renewalIntSlack s 31 ∧ centeredRenewalSlack s 31 < 0) ↔ s 30 = 5`,
2. When `s 30 = 5`: `blockSteps s 31 = 157`,
   `renewalIntSlack s 31 = 131755214163557023865312124855675151299099699131`,
   `centeredRenewalSlack s 31 = -50932490502805840910148479233860226157891868741`, and
   `(0 < renewalIntSlack s 32 ∧ centeredRenewalSlack s 32 < 0) ↔ s 31 = 3`,
3. When `s 30 = 5` and `s 31 = 3`: `blockSteps s 32 = 160`,
   `renewalIntSlack s 32 = 634387507754233807956057705670663045763826790585`,
   `centeredRenewalSlack s 32 = -827114129576669110247627127045619973892105752391`, and
   `(0 < renewalIntSlack s 33 ∧ centeredRenewalSlack s 33 < 0) ↔ s 32 = 4`,
4. When `s 30 = 5`, `s 31 = 3`, and `s 32 = 4`: `blockSteps s 33 = 164`,
   `renewalIntSlack s 33 = 4617335733504045061922759512402650077880128662153`,
   `centeredRenewalSlack s 33 = -18766690463790401629336197811057878236614792025463`, and any two
   seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 33` satisfy `2 ^ 165 ∣ (b₂ - b₁)` and `2 ^ 165 ≤ b₂`. -/
theorem thirtyone_to_thirtythree_block_kneading_corridor_and_two_pow_165_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3)
    (hs24 : s 24 = 5) (hs25 : s 25 = 8) (hs26 : s 26 = 8) (hs27 : s 27 = 3)
    (hs28 : s 28 = 6) (hs29 : s 29 = 4) :
    ((0 < renewalIntSlack s 31 ∧ centeredRenewalSlack s 31 < 0) ↔ s 30 = 5) ∧
      (s 30 = 5 →
        blockSteps s 31 = 157 ∧
          renewalIntSlack s 31 = 131755214163557023865312124855675151299099699131 ∧
          centeredRenewalSlack s 31 = -50932490502805840910148479233860226157891868741 ∧
          ((0 < renewalIntSlack s 32 ∧ centeredRenewalSlack s 32 < 0) ↔ s 31 = 3)) ∧
      (s 30 = 5 → s 31 = 3 →
        blockSteps s 32 = 160 ∧
          renewalIntSlack s 32 = 634387507754233807956057705670663045763826790585 ∧
          centeredRenewalSlack s 32 = -827114129576669110247627127045619973892105752391 ∧
          ((0 < renewalIntSlack s 33 ∧ centeredRenewalSlack s 33 < 0) ↔ s 32 = 4)) ∧
      (s 30 = 5 → s 31 = 3 → s 32 = 4 →
        blockSteps s 33 = 164 ∧
          renewalIntSlack s 33 = 4617335733504045061922759512402650077880128662153 ∧
          centeredRenewalSlack s 33 = -18766690463790401629336197811057878236614792025463 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 33 →
              ValidBlockChain b₂ s u₂ 33 →
                2 ^ 165 ∣ (b₂ - b₁) ∧ 2 ^ 165 ≤ b₂)) := by
  have hprev :=
    (twentyeight_to_thirty_block_kneading_corridor_and_two_pow_153_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26).2.2.2 hs27 hs28 hs29
  have hT30 : blockSteps s 30 = 152 := hprev.1
  have hS30 : renewalIntSlack s 30 = 2045805034964126557268449930184139531741081625 := hprev.2.1
  have hstep30 := subCeiling_step_sandwich_iff s 30
  have hiff30 :
      (0 < renewalIntSlack s 31 ∧ centeredRenewalSlack s 31 < 0) ↔ s 30 = 5 := by
    have hsand30 := hstep30.2.2
    rw [hT30, hS30] at hsand30
    exact hsand30.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 2045805034964126557268449930184139531741081625) (T_N := 152) (s_star := 5)
      (by norm_num) (by norm_num) (s 30)).1
  have h31_vals :
      s 30 = 5 →
        blockSteps s 31 = 157 ∧
          renewalIntSlack s 31 = 131755214163557023865312124855675151299099699131 ∧
          centeredRenewalSlack s 31 = -50932490502805840910148479233860226157891868741 := by
    intro hs30
    have hT31 : blockSteps s 31 = 157 := by
      change blockSteps s 30 + s 30 = 157
      rw [hT30, hs30]
    have hS31 : renewalIntSlack s 31 = 131755214163557023865312124855675151299099699131 := by
      have h1 := hstep30.1
      rw [h1, hT30, hS30, hs30]
      norm_num
    have hC31 : centeredRenewalSlack s 31 = -50932490502805840910148479233860226157891868741 := by
      have h2 := hstep30.2.1
      rw [h2, hT30, hS30, hs30]
      norm_num
    exact ⟨hT31, hS31, hC31⟩
  have h32_vals :
      s 30 = 5 → s 31 = 3 →
        blockSteps s 32 = 160 ∧
          renewalIntSlack s 32 = 634387507754233807956057705670663045763826790585 ∧
          centeredRenewalSlack s 32 = -827114129576669110247627127045619973892105752391 := by
    intro hs30 hs31
    obtain ⟨hT31, hS31, _⟩ := h31_vals hs30
    have hstep31 := subCeiling_step_sandwich_iff s 31
    have hT32 : blockSteps s 32 = 160 := by
      change blockSteps s 31 + s 31 = 160
      rw [hT31, hs31]
    have hS32 : renewalIntSlack s 32 = 634387507754233807956057705670663045763826790585 := by
      have h1 := hstep31.1
      rw [h1, hT31, hS31, hs31]
      norm_num
    have hC32 : centeredRenewalSlack s 32 = -827114129576669110247627127045619973892105752391 := by
      have h2 := hstep31.2.1
      rw [h2, hT31, hS31, hs31]
      norm_num
    exact ⟨hT32, hS32, hC32⟩
  refine ⟨hiff30, ?_, ?_, ?_⟩
  · intro hs30
    obtain ⟨hT31, hS31, hC31⟩ := h31_vals hs30
    have hsand31 := (subCeiling_step_sandwich_iff s 31).2.2
    rw [hT31, hS31] at hsand31
    refine ⟨hT31, hS31, hC31, ?_⟩
    exact hsand31.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 131755214163557023865312124855675151299099699131) (T_N := 157) (s_star := 3)
      (by norm_num) (by norm_num) (s 31)).1
  · intro hs30 hs31
    obtain ⟨hT32, hS32, hC32⟩ := h32_vals hs30 hs31
    have hsand32 := (subCeiling_step_sandwich_iff s 32).2.2
    rw [hT32, hS32] at hsand32
    refine ⟨hT32, hS32, hC32, ?_⟩
    exact hsand32.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 634387507754233807956057705670663045763826790585) (T_N := 160) (s_star := 4)
      (by norm_num) (by norm_num) (s 32)).1
  · intro hs30 hs31 hs32
    obtain ⟨hT32, hS32, _⟩ := h32_vals hs30 hs31
    have hstep32 := subCeiling_step_sandwich_iff s 32
    have hT33 : blockSteps s 33 = 164 := by
      change blockSteps s 32 + s 32 = 164
      rw [hT32, hs32]
    have hS33 : renewalIntSlack s 33 = 4617335733504045061922759512402650077880128662153 := by
      have h1 := hstep32.1
      rw [h1, hT32, hS32, hs32]
      norm_num
    have hC33 : centeredRenewalSlack s 33 = -18766690463790401629336197811057878236614792025463 := by
      have h2 := hstep32.2.1
      rw [h2, hT32, hS32, hs32]
      norm_num
    refine ⟨hT33, hS33, hC33, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 33) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 33 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT33] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 165 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.ConstantRungBoundAndKneading33
