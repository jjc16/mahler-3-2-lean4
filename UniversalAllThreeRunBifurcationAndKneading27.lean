import UniversalTwoRungWindowAndKneading24

/-!
# Universal All-$3$ Run Closed Form from Arbitrary State, the $\frac{16}{19}$ Repelling Fixed-Point Bifurcation & 27-Block ($T_{27} = 139$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 11 / 20 (Part XXVI, Sections C2.O11.1–C2.O11.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O11.1 (Inner Loop 1 / 5) — Universal Closed Form for a $j$-Run of $3$'s from Arbitrary State $N$
   (`universal_all_three_run_from_step_closed_form`)**:
   - Whenever `∀ t < j, s (N + t) = 3`, setting `T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
     - `blockSteps s (N + j) = T_N + 3 * j`,
     - `19 * renewalIntSlack s (N + j) =
         (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) + 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`, and
     - `19 * centeredRenewalSlack s (N + j) =
         (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) - 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`.

2. **Section C2.O11.2 (Inner Loop 2 / 5) — Non-Vanishing of the Repelling Fixed Point $\rho_*(m) = \frac{2^{m+1}}{3^m - 2^m}$
   (`repelling_fixed_point_non_vanishing_for_all_rungs`)**:
   - For any odd slack `S_N % 2 = 1`, any `T_N : ℕ`, and any `1 ≤ m`:
     `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N ≠ (2 : ℤ) ^ (T_N + m + 1)` and
     `19 * S_N ≠ 16 * (2 : ℤ) ^ T_N`.

3. **Section C2.O11.3 (Inner Loop 3 / 5) — Upward vs. Downward Drift Bifurcation Around $\frac{16}{19}$
   (`all_three_run_fixed_point_bifurcation`)**:
   - Under `∀ t < j, s (N + t) = 3`:
     - Above $\frac{16}{19}$ (`16 * 2 ^ T_N < 19 * S_N`): `0 < renewalIntSlack s (N + j)` for all $j$,
       and `centeredRenewalSlack s (N + j) < 0 ↔ (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) < 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`.
     - Below $\frac{16}{19}$ (`19 * S_N < 16 * 2 ^ T_N`): `centeredRenewalSlack s (N + j) < 0` for all $j$,
       and `0 < renewalIntSlack s (N + j) ↔ (27 : ℤ) ^ j * (16 * (2 : ℤ) ^ T_N - 19 * S_N) < 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`.

4. **Sections C2.O11.4 & C2.O11.5 (Inner Loops 4–5 / 5) — Certification of Blocks 25, 26, and 27 ($s_{24} = 5, s_{25} = 8, s_{26} = 8$, $T_{27} = 139$) & Mod-$2^{140}$ Uniqueness
   (`twentyfive_to_twentyseven_block_kneading_corridor_and_two_pow_140_uniqueness`)**:
   - Crosses the 128-bit horizon ($T_{26} = 131, T_{27} = 139$) and proves $2^{140} \mid (b_2 - b_1)$
     and $2^{140} \le b_2$ for any two seeds sharing the 27-block prefix.
-/

namespace Mahler.UniversalAllThreeRunAndKneading27

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

/-! ## 1. Section C2.O11.1: Universal Closed Form for a $j$-Run of $3$'s from Arbitrary State $N$ -/

/-- **Universal Closed Form for a $j$-Run of $3$'s from Arbitrary State $N$
(`universal_all_three_run_from_step_closed_form`, Section C2.O11.1)**:
For any sequence `s : ℕ → ℕ`, starting index `N : ℕ`, and run length `j : ℕ` such that
`∀ t < j, s (N + t) = 3`, setting `T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
1. `blockSteps s (N + j) = T_N + 3 * j`,
2. `19 * renewalIntSlack s (N + j) =
     (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) + 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`, and
3. `19 * centeredRenewalSlack s (N + j) =
     (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) - 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`. -/
theorem universal_all_three_run_from_step_closed_form
    {s : ℕ → ℕ} {N j : ℕ} (h3 : ∀ t < j, s (N + t) = 3) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    blockSteps s (N + j) = T_N + 3 * j ∧
      19 * renewalIntSlack s (N + j) =
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) + 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j ∧
      19 * centeredRenewalSlack s (N + j) =
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) - 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by
  intro T_N S_N
  set s' := fun t => s (N + t)
  have hall3 := constant_three_run_renewalNumerator_nineteen_law (s' := s') h3
  have hd : blockSteps s' j = 3 * j := hall3.1
  have hAj : 19 * renewalNumerator s' j = 8 * (27 ^ j - 8 ^ j) := hall3.2
  have hsh := blockSteps_add_shift s N j
  have hT_Nj : blockSteps s (N + j) = T_N + 3 * j := by
    change blockSteps s (N + j) = T_N + blockSteps s' j at hsh
    rw [hsh, hd]
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 N j).2.2
  change renewalIntSlack s (N + j) =
    (3 : ℤ) ^ (blockSteps s' j) * S_N - (2 : ℤ) ^ (T_N + 1) * (renewalNumerator s' j : ℤ) at hcoc
  have hpow3 : (3 : ℤ) ^ (3 * j) = (27 : ℤ) ^ j := by
    rw [pow_mul]
    norm_num
  have hpow2 : (2 : ℤ) ^ (T_N + 3 * j) = (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by
    rw [pow_add, pow_mul]
    norm_num
  have h8_le_27 : 8 ^ j ≤ 27 ^ j := Nat.pow_le_pow_left (by decide) j
  have hAj_z : 19 * (renewalNumerator s' j : ℤ) = 8 * ((27 : ℤ) ^ j - (8 : ℤ) ^ j) := by
    zify [h8_le_27] at hAj
    exact_mod_cast hAj
  have hS_Nj :
      19 * renewalIntSlack s (N + j) =
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) + 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by
    calc
      19 * renewalIntSlack s (N + j)
          = 19 * ((3 : ℤ) ^ (3 * j) * S_N) - (2 : ℤ) ^ (T_N + 1) * (19 * (renewalNumerator s' j : ℤ)) := by
            rw [hcoc, hd]
            ring
      _ = 19 * ((27 : ℤ) ^ j * S_N) - (2 : ℤ) ^ (T_N + 1) * (8 * ((27 : ℤ) ^ j - (8 : ℤ) ^ j)) := by
            rw [hpow3, hAj_z]
      _ = (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) + 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by
            rw [pow_succ]
            ring
  have hC_Nj :
      19 * centeredRenewalSlack s (N + j) =
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) - 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by
    have hC_def : centeredRenewalSlack s (N + j) = renewalIntSlack s (N + j) - (2 : ℤ) ^ (blockSteps s (N + j)) := rfl
    rw [hC_def, hT_Nj, hpow2]
    calc
      19 * (renewalIntSlack s (N + j) - (2 : ℤ) ^ T_N * (8 : ℤ) ^ j)
          = 19 * renewalIntSlack s (N + j) - 19 * ((2 : ℤ) ^ T_N * (8 : ℤ) ^ j) := by ring
      _ = (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) - 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by
            rw [hS_Nj]
            ring
  exact ⟨hT_Nj, hS_Nj, hC_Nj⟩

/-! ## 2. Section C2.O11.2: Non-Vanishing of the Repelling Fixed Point $\rho_*(m) = \frac{2^{m+1}}{3^m - 2^m}$ -/

/-- **Non-Vanishing of the Repelling Fixed Point $\rho_*(m) = \frac{2^{m+1}}{3^m - 2^m}$
(`repelling_fixed_point_non_vanishing_for_all_rungs`, Section C2.O11.2)**:
For any odd integer `S_N % 2 = 1`, any `T_N : ℕ`, and any `m : ℕ` with `1 ≤ m`:
1. `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N ≠ (2 : ℤ) ^ (T_N + m + 1)`, and
2. `19 * S_N ≠ 16 * (2 : ℤ) ^ T_N`. -/
theorem repelling_fixed_point_non_vanishing_for_all_rungs
    {S_N : ℤ} (hodd : S_N % 2 = 1) (T_N : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * S_N ≠ (2 : ℤ) ^ (T_N + m + 1) ∧
      19 * S_N ≠ 16 * (2 : ℤ) ^ T_N := by
  have h3_odd : ((3 : ℤ) ^ m) % 2 = 1 := int_three_pow_mod_two_eq_one m
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  have h2_even : ((2 : ℤ) ^ (k + 1)) % 2 = 0 := by
    rw [pow_succ]
    omega
  have hdiff_odd : (((3 : ℤ) ^ (k + 1) - (2 : ℤ) ^ (k + 1)) % 2) = 1 := by
    omega
  have hprod_odd : ((((3 : ℤ) ^ (k + 1) - (2 : ℤ) ^ (k + 1)) * S_N) % 2) = 1 := by
    rw [Int.mul_emod, hdiff_odd, hodd]
    decide
  have hrhs_even : (((2 : ℤ) ^ (T_N + (k + 1) + 1)) % 2) = 0 := by
    rw [pow_succ]
    omega
  refine ⟨?_, ?_⟩
  · intro heq
    rw [heq] at hprod_odd
    omega
  · intro heq19
    have h19_odd : ((19 * S_N) % 2) = 1 := by
      rw [Int.mul_emod, hodd]
      decide
    have h16_even : ((16 * (2 : ℤ) ^ T_N) % 2) = 0 := by
      omega
    rw [heq19] at h19_odd
    omega

/-! ## 3. Section C2.O11.3: Upward vs. Downward Drift Bifurcation Around $\frac{16}{19}$ -/

/-- **Upward vs. Downward Drift Bifurcation Around $\frac{16}{19}$
(`all_three_run_fixed_point_bifurcation`, Section C2.O11.3)**:
Under `∀ t < j, s (N + t) = 3`, setting `T_N = blockSteps s N` and `S_N = renewalIntSlack s N`:
1. If `16 * (2 : ℤ) ^ T_N < 19 * S_N` (above $\frac{16}{19}$), then `0 < renewalIntSlack s (N + j)`
   and
   `centeredRenewalSlack s (N + j) < 0 ↔
     (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) < 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`.
2. If `19 * S_N < 16 * (2 : ℤ) ^ T_N` (below $\frac{16}{19}$), then `centeredRenewalSlack s (N + j) < 0`
   and
   `0 < renewalIntSlack s (N + j) ↔
     (27 : ℤ) ^ j * (16 * (2 : ℤ) ^ T_N - 19 * S_N) < 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j`. -/
theorem all_three_run_fixed_point_bifurcation
    {s : ℕ → ℕ} {N j : ℕ} (h3 : ∀ t < j, s (N + t) = 3) :
    let T_N := blockSteps s N
    let S_N := renewalIntSlack s N
    (16 * (2 : ℤ) ^ T_N < 19 * S_N →
      0 < renewalIntSlack s (N + j) ∧
        (centeredRenewalSlack s (N + j) < 0 ↔
          (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) < 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j)) ∧
      (19 * S_N < 16 * (2 : ℤ) ^ T_N →
        centeredRenewalSlack s (N + j) < 0 ∧
          (0 < renewalIntSlack s (N + j) ↔
            (27 : ℤ) ^ j * (16 * (2 : ℤ) ^ T_N - 19 * S_N) < 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j)) := by
  intro T_N S_N
  have hcf := universal_all_three_run_from_step_closed_form h3
  have hS_Nj :
      19 * renewalIntSlack s (N + j) =
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) + 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := hcf.2.1
  have hC_Nj :
      19 * centeredRenewalSlack s (N + j) =
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) - 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := hcf.2.2
  clear hcf
  have h27_pos : 0 < (27 : ℤ) ^ j := by positivity
  have h16_pos : 0 < 16 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by positivity
  have h3_pos : 0 < 3 * (2 : ℤ) ^ T_N * (8 : ℤ) ^ j := by positivity
  refine ⟨?_, ?_⟩
  · intro habove
    have hdiff_pos : 0 < 19 * S_N - 16 * (2 : ℤ) ^ T_N := by omega
    have hprod_pos : 0 < (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) := mul_pos h27_pos hdiff_pos
    refine ⟨by omega, ?_⟩
    constructor <;> intro h <;> omega
  · intro hbelow
    have hdiff_pos : 0 < 16 * (2 : ℤ) ^ T_N - 19 * S_N := by omega
    have hprod_pos : 0 < (27 : ℤ) ^ j * (16 * (2 : ℤ) ^ T_N - 19 * S_N) := mul_pos h27_pos hdiff_pos
    have hneg_eq :
        (27 : ℤ) ^ j * (19 * S_N - 16 * (2 : ℤ) ^ T_N) =
          -((27 : ℤ) ^ j * (16 * (2 : ℤ) ^ T_N - 19 * S_N)) := by ring
    rw [hneg_eq] at hS_Nj hC_Nj
    refine ⟨by omega, ?_⟩
    constructor <;> intro h <;> omega

/-! ## 4. Sections C2.O11.4 & C2.O11.5: Certification of Blocks 25, 26, and 27 ($T_{27} = 139$) & Mod-$2^{140}$ Uniqueness -/

/-- **Certification of the 25th ($s_{24} = 5$), 26th ($s_{25} = 8$), and 27th ($s_{26} = 8$) Kneading Rungs & Mod-$2^{140}$ Uniqueness
(`twentyfive_to_twentyseven_block_kneading_corridor_and_two_pow_140_uniqueness`, Sections C2.O11.4–C2.O11.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 24-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3)$:
1. `(0 < renewalIntSlack s 25 ∧ centeredRenewalSlack s 25 < 0) ↔ s 24 = 5`,
2. When `s 24 = 5`: `blockSteps s 25 = 123`,
   `renewalIntSlack s 25 = 872841296440661209348790157987972899`,
   `centeredRenewalSlack s 25 = -9760982669838665773881666324254783709`, and
   `(0 < renewalIntSlack s 26 ∧ centeredRenewalSlack s 26 < 0) ↔ s 25 = 8`,
3. When `s 24 = 5` and `s 25 = 8`: `blockSteps s 26 = 131`,
   `renewalIntSlack s 26 = 282193875212162779123418507650798807043`,
   `centeredRenewalSlack s 26 = -2440065060155344928583578351803346884605`, and
   `(0 < renewalIntSlack s 27 ∧ centeredRenewalSlack s 27 < 0) ↔ s 26 = 8`,
4. When `s 24 = 5`, `s 25 = 8`, and `s 26 = 8`: `blockSteps s 27 = 139`,
   `renewalIntSlack s 27 = 457677440358836047482766436656368378885347`,
   `centeredRenewalSlack s 27 = -239220847095245925690224759363892918176541`, and any two seeds
   `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 27` satisfy `2 ^ 140 ∣ (b₂ - b₁)` and `2 ^ 140 ≤ b₂`. -/
theorem twentyfive_to_twentyseven_block_kneading_corridor_and_two_pow_140_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3) :
    ((0 < renewalIntSlack s 25 ∧ centeredRenewalSlack s 25 < 0) ↔ s 24 = 5) ∧
      (s 24 = 5 →
        blockSteps s 25 = 123 ∧
          renewalIntSlack s 25 = 872841296440661209348790157987972899 ∧
          centeredRenewalSlack s 25 = -9760982669838665773881666324254783709 ∧
          ((0 < renewalIntSlack s 26 ∧ centeredRenewalSlack s 26 < 0) ↔ s 25 = 8)) ∧
      (s 24 = 5 → s 25 = 8 →
        blockSteps s 26 = 131 ∧
          renewalIntSlack s 26 = 282193875212162779123418507650798807043 ∧
          centeredRenewalSlack s 26 = -2440065060155344928583578351803346884605 ∧
          ((0 < renewalIntSlack s 27 ∧ centeredRenewalSlack s 27 < 0) ↔ s 26 = 8)) ∧
      (s 24 = 5 → s 25 = 8 → s 26 = 8 →
        blockSteps s 27 = 139 ∧
          renewalIntSlack s 27 = 457677440358836047482766436656368378885347 ∧
          centeredRenewalSlack s 27 = -239220847095245925690224759363892918176541 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 27 →
              ValidBlockChain b₂ s u₂ 27 →
                2 ^ 140 ∣ (b₂ - b₁) ∧ 2 ^ 140 ≤ b₂)) := by
  have hprev :=
    (twentytwo_to_twentyfour_block_kneading_corridor_and_two_pow_119_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hs20).2.2.2
      hs21 hs22 hs23
  have hT24 : blockSteps s 24 = 118 := hprev.1
  have hS24 : renewalIntSlack s 24 = 91113124399174136525965856471084305 := hprev.2.1
  have hstep24 := subCeiling_step_sandwich_iff s 24
  have hiff24 :
      (0 < renewalIntSlack s 25 ∧ centeredRenewalSlack s 25 < 0) ↔ s 24 = 5 := by
    have hsand24 := hstep24.2.2
    rw [hT24, hS24] at hsand24
    exact hsand24.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 91113124399174136525965856471084305) (T_N := 118) (s_star := 5)
      (by norm_num) (by norm_num) (s 24)).1
  have h25_vals :
      s 24 = 5 →
        blockSteps s 25 = 123 ∧
          renewalIntSlack s 25 = 872841296440661209348790157987972899 ∧
          centeredRenewalSlack s 25 = -9760982669838665773881666324254783709 := by
    intro hs24
    have hT25 : blockSteps s 25 = 123 := by
      change blockSteps s 24 + s 24 = 123
      rw [hT24, hs24]
    have hS25 : renewalIntSlack s 25 = 872841296440661209348790157987972899 := by
      have h1 := hstep24.1
      rw [h1, hT24, hS24, hs24]
      norm_num
    have hC25 : centeredRenewalSlack s 25 = -9760982669838665773881666324254783709 := by
      have h2 := hstep24.2.1
      rw [h2, hT24, hS24, hs24]
      norm_num
    exact ⟨hT25, hS25, hC25⟩
  have h26_vals :
      s 24 = 5 → s 25 = 8 →
        blockSteps s 26 = 131 ∧
          renewalIntSlack s 26 = 282193875212162779123418507650798807043 ∧
          centeredRenewalSlack s 26 = -2440065060155344928583578351803346884605 := by
    intro hs24 hs25
    obtain ⟨hT25, hS25, _⟩ := h25_vals hs24
    have hstep25 := subCeiling_step_sandwich_iff s 25
    have hT26 : blockSteps s 26 = 131 := by
      change blockSteps s 25 + s 25 = 131
      rw [hT25, hs25]
    have hS26 : renewalIntSlack s 26 = 282193875212162779123418507650798807043 := by
      have h1 := hstep25.1
      rw [h1, hT25, hS25, hs25]
      norm_num
    have hC26 : centeredRenewalSlack s 26 = -2440065060155344928583578351803346884605 := by
      have h2 := hstep25.2.1
      rw [h2, hT25, hS25, hs25]
      norm_num
    exact ⟨hT26, hS26, hC26⟩
  refine ⟨hiff24, ?_, ?_, ?_⟩
  · intro hs24
    obtain ⟨hT25, hS25, hC25⟩ := h25_vals hs24
    have hsand25 := (subCeiling_step_sandwich_iff s 25).2.2
    rw [hT25, hS25] at hsand25
    refine ⟨hT25, hS25, hC25, ?_⟩
    exact hsand25.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 872841296440661209348790157987972899) (T_N := 123) (s_star := 8)
      (by norm_num) (by norm_num) (s 25)).1
  · intro hs24 hs25
    obtain ⟨hT26, hS26, hC26⟩ := h26_vals hs24 hs25
    have hsand26 := (subCeiling_step_sandwich_iff s 26).2.2
    rw [hT26, hS26] at hsand26
    refine ⟨hT26, hS26, hC26, ?_⟩
    exact hsand26.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 282193875212162779123418507650798807043) (T_N := 131) (s_star := 8)
      (by norm_num) (by norm_num) (s 26)).1
  · intro hs24 hs25 hs26
    obtain ⟨hT26, hS26, _⟩ := h26_vals hs24 hs25
    have hstep26 := subCeiling_step_sandwich_iff s 26
    have hT27 : blockSteps s 27 = 139 := by
      change blockSteps s 26 + s 26 = 139
      rw [hT26, hs26]
    have hS27 : renewalIntSlack s 27 = 457677440358836047482766436656368378885347 := by
      have h1 := hstep26.1
      rw [h1, hT26, hS26, hs26]
      norm_num
    have hC27 : centeredRenewalSlack s 27 = -239220847095245925690224759363892918176541 := by
      have h2 := hstep26.2.1
      rw [h2, hT26, hS26, hs26]
      norm_num
    refine ⟨hT27, hS27, hC27, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 27) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 27 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT27] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 140 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.UniversalAllThreeRunAndKneading27
