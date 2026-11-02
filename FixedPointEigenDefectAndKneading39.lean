import PeriodicTailExclusionAndKneading36

/-!
# Periodic Fixed-Point Eigen-Defect $\Delta^{(q, A_p)}_{N+Rp} = 3^{qR} \Delta^{(q, A_p)}_N$, Upward/Downward $3$-Run Exit Laws & 39-Block ($T_{39} = 188$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 15 / 20 (Part XXX, Sections C2.O15.1–C2.O15.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Sections C2.O15.1 & C2.O15.2 (Inner Loops 1–2 / 5) — Constant-Rung & Periodic Fixed-Point Eigen-Defect Laws
   (`periodicFixedPointDefect`, `constant_rung_and_periodic_fixed_point_eigenDefect_law`)**:
   - Defines $\Delta^{(q, A_p)}_N := ((3 : \mathbb{Z})^q - (2 : \mathbb{Z})^q)\Sigma_N - (2 : \mathbb{Z})^{T_N + 1} A_p$.
   - Across $R$ consecutive $(p, q, A_p)$-windows starting at step $N$:
     `periodicFixedPointDefect s q A_p (N + R * p) = (3 : ℤ) ^ (q * R) * periodicFixedPointDefect s q A_p N`.
   - Specializing to a constant-$m$ run (`p = 1, q = m, A_1 = 2 ^ m`) across $j$ blocks (`∀ t < j, s (N + t) = m`):
     `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) - (2 : ℤ) ^ (blockSteps s (N + j) + m + 1) =
       (3 : ℤ) ^ (m * j) * (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s N - (2 : ℤ) ^ (blockSteps s N + m + 1))`.

2. **Section C2.O15.3 (Inner Loop 3 / 5) — Exact Upward ($s_k = 2$) and Downward ($4 \le s_k$) Exit Laws for $3^j$ Runs
   (`three_run_upward_exit_forces_two_and_downward_exit_forces_ge_four`)**:
   - At any sub-ceiling step `k` (`centeredRenewalSlack s k < 0`):
     - **Upward exit**: if choosing `3` at step `k` would restore ceiling
       (`0 < candidateCenteredSlack (renewalIntSlack s k) (blockSteps s k) 3`), then step `k + 1`
       is sub-ceiling **if and only if `s k = 2`**!
     - **Downward exit**: if choosing `3` at step `k` would escape
       (`candidateSlack (renewalIntSlack s k) (blockSteps s k) 3 ≤ 0`), then whenever step `k + 1`
       is sub-ceiling (`0 < renewalIntSlack s (k + 1)`), **`4 ≤ s k`**!

3. **Sections C2.O15.4 & C2.O15.5 (Inner Loops 4–5 / 5) — Certification of the 4-Fold $3$-Run at Blocks 37, 38, and 39 ($s_{36} = 3, s_{37} = 3, s_{38} = 3$, $T_{39} = 188$) & Mod-$2^{189}$ Uniqueness
   (`thirtyseven_to_thirtynine_block_kneading_corridor_and_two_pow_189_uniqueness`)**:
   - Certifies blocks 37–39 ($T_{39} = 188$) and proves $2^{189} \mid (b_2 - b_1)$ and $2^{189} \le b_2$
     for any two seeds sharing the 39-block prefix.
-/

namespace Mahler.FixedPointEigenDefectAndKneading39

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

/-! ## 1. Sections C2.O15.1 & C2.O15.2: Periodic & Constant-Rung Fixed-Point Eigen-Defect Laws -/

/-- Periodic fixed-point eigen-defect
$\Delta^{(q, A_p)}_N := (3^q - 2^q)\Sigma_N - 2^{T_N + 1} A_p \in \mathbb{Z}$. -/
def periodicFixedPointDefect (s : ℕ → ℕ) (q A_p N : ℕ) : ℤ :=
  ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s N -
    (2 : ℤ) ^ (blockSteps s N + 1) * (A_p : ℤ)

/-- **Constant-Rung & Periodic Fixed-Point Eigen-Defect Laws
(`constant_rung_and_periodic_fixed_point_eigenDefect_law`, Sections C2.O15.1–C2.O15.2)**:
1. For any `p, q, A_p, R : ℕ` such that for all `r < R`,
   `blockSteps (fun t => s (N + (r * p + t))) p = q` and
   `renewalNumerator (fun t => s (N + (r * p + t))) p = A_p`:
   `periodicFixedPointDefect s q A_p (N + R * p) =
     (3 : ℤ) ^ (q * R) * periodicFixedPointDefect s q A_p N`.
2. For any constant-$m$ run (`∀ t < j, s (N + t) = m`):
   `((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) -
      (2 : ℤ) ^ (blockSteps s (N + j) + m + 1) =
     (3 : ℤ) ^ (m * j) *
       (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s N -
         (2 : ℤ) ^ (blockSteps s N + m + 1))`. -/
theorem constant_rung_and_periodic_fixed_point_eigenDefect_law
    {s : ℕ → ℕ} {N p q A_p R m j : ℕ}
    (hq : ∀ r < R, blockSteps (fun t => s (N + (r * p + t))) p = q)
    (hA : ∀ r < R, renewalNumerator (fun t => s (N + (r * p + t))) p = A_p)
    (hm : ∀ t < j, s (N + t) = m) :
    periodicFixedPointDefect s q A_p (N + R * p) =
      (3 : ℤ) ^ (q * R) * periodicFixedPointDefect s q A_p N ∧
      ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) -
          (2 : ℤ) ^ (blockSteps s (N + j) + m + 1) =
        (3 : ℤ) ^ (m * j) *
          (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s N -
            (2 : ℤ) ^ (blockSteps s N + m + 1)) := by
  have hper := universal_periodic_tail_from_step_closed_form hq hA
  have hT_NR : blockSteps s (N + R * p) = blockSteps s N + q * R := hper.1
  have hS_NR := hper.2.1
  change ((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s (N + R * p) =
    (3 : ℤ) ^ (q * R) *
      (((3 : ℤ) ^ q - (2 : ℤ) ^ q) * renewalIntSlack s N -
        (2 : ℤ) ^ (blockSteps s N + 1) * (A_p : ℤ)) +
      (A_p : ℤ) * (2 : ℤ) ^ (blockSteps s N + 1 + q * R) at hS_NR
  have hcon := universal_constant_rung_run_from_step_closed_form hm
  have hT_Nj : blockSteps s (N + j) = blockSteps s N + m * j := hcon.1
  have hS_Nj := hcon.2.1
  change ((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s (N + j) =
    (3 : ℤ) ^ (m * j) *
      (((3 : ℤ) ^ m - (2 : ℤ) ^ m) * renewalIntSlack s N -
        (2 : ℤ) ^ (blockSteps s N + m + 1)) +
      (2 : ℤ) ^ (blockSteps s N + m + 1 + m * j) at hS_Nj
  refine ⟨?_, ?_⟩
  · unfold periodicFixedPointDefect
    rw [hS_NR, hT_NR, show blockSteps s N + q * R + 1 = blockSteps s N + 1 + q * R by omega]
    ring
  · rw [hS_Nj, hT_Nj,
        show blockSteps s N + m * j + m + 1 = blockSteps s N + m + 1 + m * j by omega]
    ring

/-! ## 2. Section C2.O15.3: Exact Upward ($s_k = 2$) and Downward ($4 \le s_k$) Exit Laws for $3^j$ Runs -/

/-- **Exact Upward ($s_k = 2$) and Downward ($4 \le s_k$) Exit Laws for $3^j$ Runs
(`three_run_upward_exit_forces_two_and_downward_exit_forces_ge_four`, Section C2.O15.3)**:
For any sequence `s : ℕ → ℕ` and index `k : ℕ`, setting `T_k = blockSteps s k` and
`S_k = renewalIntSlack s k`:
1. **Upward exit**: if `0 < S_k`, `centeredRenewalSlack s k < 0`, and
   `0 < candidateCenteredSlack S_k T_k 3`, then
   `(0 < renewalIntSlack s (k + 1) ∧ centeredRenewalSlack s (k + 1) < 0) ↔ s k = 2`.
2. **Downward exit**: if `0 < S_k`, `candidateSlack S_k T_k 3 ≤ 0`, and
   `0 < renewalIntSlack s (k + 1)`, then `4 ≤ s k`. -/
theorem three_run_upward_exit_forces_two_and_downward_exit_forces_ge_four
    (s : ℕ → ℕ) (k : ℕ) :
    let T_k := blockSteps s k
    let S_k := renewalIntSlack s k
    (0 < S_k → centeredRenewalSlack s k < 0 → 0 < candidateCenteredSlack S_k T_k 3 →
      ((0 < renewalIntSlack s (k + 1) ∧ centeredRenewalSlack s (k + 1) < 0) ↔ s k = 2)) ∧
      (0 < S_k → candidateSlack S_k T_k 3 ≤ 0 → 0 < renewalIntSlack s (k + 1) →
        4 ≤ s k) := by
  intro T_k S_k
  have hstep := subCeiling_step_sandwich_iff s k
  have hS_next : renewalIntSlack s (k + 1) = (3 : ℤ) ^ (s k) * S_k - 2 * (2 : ℤ) ^ (T_k + s k) := hstep.1
  have hC_next : centeredRenewalSlack s (k + 1) = (3 : ℤ) ^ (s k) * S_k - 3 * (2 : ℤ) ^ (T_k + s k) := hstep.2.1
  clear hstep
  refine ⟨?_, ?_⟩
  · intro hS_pos hC_lt hC3_pos
    have hC3_eq : candidateCenteredSlack S_k T_k 3 = 27 * S_k - 24 * (2 : ℤ) ^ T_k := by
      unfold candidateCenteredSlack
      rw [pow_add]
      ring
    rw [hC3_eq] at hC3_pos
    have h8_lt_9 : 8 * (2 : ℤ) ^ T_k < 9 * S_k := by omega
    have hC_def : centeredRenewalSlack s k = S_k - (2 : ℤ) ^ T_k := rfl
    rw [hC_def] at hC_lt
    constructor
    · rintro ⟨hpos1, hneg1⟩
      by_contra hne2
      rcases Nat.lt_or_gt_of_ne hne2 with hlt2 | hgt2
      · have h01 : s k = 0 ∨ s k = 1 := by omega
        rcases h01 with hs0 | hs1
        · rw [hS_next, hs0] at hpos1
          simp only [pow_zero, add_zero] at hpos1
          omega
        · rw [hS_next, hs1] at hpos1
          rw [pow_one, pow_add, pow_one] at hpos1
          omega
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, s k = d + 3 := ⟨s k - 3, by omega⟩
        rw [hC_next, hd] at hneg1
        have h3_split : (3 : ℤ) ^ (d + 3) * S_k = (3 : ℤ) ^ d * (27 * S_k) := by
          rw [pow_add]
          ring
        have h2_split : 3 * (2 : ℤ) ^ (T_k + (d + 3)) = (2 : ℤ) ^ d * (24 * (2 : ℤ) ^ T_k) := by
          rw [show T_k + (d + 3) = d + T_k + 3 by omega, pow_add, pow_add]
          ring
        rw [h3_split, h2_split] at hneg1
        have h2_le_3 : (2 : ℤ) ^ d ≤ (3 : ℤ) ^ d := by
          exact_mod_cast Nat.pow_le_pow_left (by decide) d
        have h24_pos : 0 ≤ 24 * (2 : ℤ) ^ T_k := by positivity
        have h3d_pos : 0 < (3 : ℤ) ^ d := by positivity
        have hmul1 : (2 : ℤ) ^ d * (24 * (2 : ℤ) ^ T_k) ≤ (3 : ℤ) ^ d * (24 * (2 : ℤ) ^ T_k) :=
          mul_le_mul_of_nonneg_right h2_le_3 h24_pos
        have hmul2 : (3 : ℤ) ^ d * (24 * (2 : ℤ) ^ T_k) < (3 : ℤ) ^ d * (27 * S_k) :=
          mul_lt_mul_of_pos_left (by omega) h3d_pos
        omega
    · intro hs2
      have hC_lt' : centeredRenewalSlack s k < 0 := by rw [hC_def]; exact hC_lt
      exact ((subCeiling_rung_eq_two_iff_and_two_step_three_two_window s k).1 hC_lt' hs2).2.mpr h8_lt_9
  · intro hS_pos hS3_le hpos1
    have hS3_eq : candidateSlack S_k T_k 3 = 27 * S_k - 16 * (2 : ℤ) ^ T_k := by
      unfold candidateSlack
      rw [pow_add]
      ring
    rw [hS3_eq] at hS3_le
    by_contra hlt4
    have hcases : s k = 0 ∨ s k = 1 ∨ s k = 2 ∨ s k = 3 := by omega
    have h2_pos : 0 < (2 : ℤ) ^ T_k := by positivity
    rcases hcases with hs0 | hs1 | hs2 | hs3
    · rw [hS_next, hs0] at hpos1
      simp only [pow_zero, add_zero] at hpos1
      omega
    · rw [hS_next, hs1] at hpos1
      rw [pow_one, pow_add, pow_one] at hpos1
      omega
    · rw [hS_next, hs2] at hpos1
      have h2 : (3 : ℤ) ^ 2 * S_k - 2 * (2 : ℤ) ^ (T_k + 2) = 9 * S_k - 8 * (2 : ℤ) ^ T_k := by
        rw [pow_add]
        ring
      rw [h2] at hpos1
      omega
    · rw [hS_next, hs3] at hpos1
      have h3 : (3 : ℤ) ^ 3 * S_k - 2 * (2 : ℤ) ^ (T_k + 3) = 27 * S_k - 16 * (2 : ℤ) ^ T_k := by
        rw [pow_add]
        ring
      rw [h3] at hpos1
      omega

/-! ## 3. Sections C2.O15.4 & C2.O15.5: Certification of Blocks 37, 38, and 39 ($T_{39} = 188$) & Mod-$2^{189}$ Uniqueness -/

/-- **Certification of the 37th ($s_{36} = 3$), 38th ($s_{37} = 3$), and 39th ($s_{38} = 3$) Kneading Rungs & Mod-$2^{189}$ Uniqueness
(`thirtyseven_to_thirtynine_block_kneading_corridor_and_two_pow_189_uniqueness`, Sections C2.O15.4–C2.O15.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 36-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4, 6, 6, 3)$:
1. `(0 < renewalIntSlack s 37 ∧ centeredRenewalSlack s 37 < 0) ↔ s 36 = 3`,
2. When `s 36 = 3`: `blockSteps s 37 = 182`,
   `renewalIntSlack s 37 = 4878993571106759469387254741143623902406679309965392401`,
   `centeredRenewalSlack s 37 = -1250988592356795964046133367457612832068277178769016303`, and
   `(0 < renewalIntSlack s 38 ∧ centeredRenewalSlack s 38 < 0) ↔ s 37 = 3`,
3. When `s 36 = 3` and `s 37 = 3`: `blockSteps s 38 = 185`,
   `renewalIntSlack s 38 = 33653111804465618738521668273258057613381037549315055563`,
   `centeredRenewalSlack s 38 = -15386745503242824728945436595551836262418614360560214069`, and
   `(0 < renewalIntSlack s 39 ∧ centeredRenewalSlack s 39 < 0) ↔ s 38 = 3`,
4. When `s 36 = 3`, `s 37 = 3`, and `s 38 = 3`: `blockSteps s 39 = 188`,
   `renewalIntSlack s 39 = 123996301797236610460611365477009253548493583273502186089`,
   `centeredRenewalSlack s 39 = -268322556664430937279125473473469897457903632005499970967`, and
   any two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 39` satisfy `2 ^ 189 ∣ (b₂ - b₁)`
   and `2 ^ 189 ≤ b₂`. -/
theorem thirtyseven_to_thirtynine_block_kneading_corridor_and_two_pow_189_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3)
    (hs24 : s 24 = 5) (hs25 : s 25 = 8) (hs26 : s 26 = 8) (hs27 : s 27 = 3)
    (hs28 : s 28 = 6) (hs29 : s 29 = 4) (hs30 : s 30 = 5) (hs31 : s 31 = 3)
    (hs32 : s 32 = 4) (hs33 : s 33 = 6) (hs34 : s 34 = 6) (hs35 : s 35 = 3) :
    ((0 < renewalIntSlack s 37 ∧ centeredRenewalSlack s 37 < 0) ↔ s 36 = 3) ∧
      (s 36 = 3 →
        blockSteps s 37 = 182 ∧
          renewalIntSlack s 37 = 4878993571106759469387254741143623902406679309965392401 ∧
          centeredRenewalSlack s 37 = -1250988592356795964046133367457612832068277178769016303 ∧
          ((0 < renewalIntSlack s 38 ∧ centeredRenewalSlack s 38 < 0) ↔ s 37 = 3)) ∧
      (s 36 = 3 → s 37 = 3 →
        blockSteps s 38 = 185 ∧
          renewalIntSlack s 38 = 33653111804465618738521668273258057613381037549315055563 ∧
          centeredRenewalSlack s 38 = -15386745503242824728945436595551836262418614360560214069 ∧
          ((0 < renewalIntSlack s 39 ∧ centeredRenewalSlack s 39 < 0) ↔ s 38 = 3)) ∧
      (s 36 = 3 → s 37 = 3 → s 38 = 3 →
        blockSteps s 39 = 188 ∧
          renewalIntSlack s 39 = 123996301797236610460611365477009253548493583273502186089 ∧
          centeredRenewalSlack s 39 = -268322556664430937279125473473469897457903632005499970967 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 39 →
              ValidBlockChain b₂ s u₂ 39 →
                2 ^ 189 ∣ (b₂ - b₁) ∧ 2 ^ 189 ≤ b₂)) := by
  have hprev :=
    (thirtyfour_to_thirtysix_block_kneading_corridor_and_two_pow_180_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32).2.2.2 hs33 hs34 hs35
  have hT36 : blockSteps s 36 = 179 := hprev.1
  have hS36 : renewalIntSlack s 36 = 634776218445698901342741887346151754494688603238304067 := hprev.2.1
  have hstep36 := subCeiling_step_sandwich_iff s 36
  have hiff36 :
      (0 < renewalIntSlack s 37 ∧ centeredRenewalSlack s 37 < 0) ↔ s 36 = 3 := by
    have hsand36 := hstep36.2.2
    rw [hT36, hS36] at hsand36
    exact hsand36.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 634776218445698901342741887346151754494688603238304067) (T_N := 179) (s_star := 3)
      (by norm_num) (by norm_num) (s 36)).1
  have h37_vals :
      s 36 = 3 →
        blockSteps s 37 = 182 ∧
          renewalIntSlack s 37 = 4878993571106759469387254741143623902406679309965392401 ∧
          centeredRenewalSlack s 37 = -1250988592356795964046133367457612832068277178769016303 := by
    intro hs36
    have hT37 : blockSteps s 37 = 182 := by
      change blockSteps s 36 + s 36 = 182
      rw [hT36, hs36]
    have hS37 : renewalIntSlack s 37 = 4878993571106759469387254741143623902406679309965392401 := by
      have h1 := hstep36.1
      rw [h1, hT36, hS36, hs36]
      norm_num
    have hC37 : centeredRenewalSlack s 37 = -1250988592356795964046133367457612832068277178769016303 := by
      have h2 := hstep36.2.1
      rw [h2, hT36, hS36, hs36]
      norm_num
    exact ⟨hT37, hS37, hC37⟩
  have h38_vals :
      s 36 = 3 → s 37 = 3 →
        blockSteps s 38 = 185 ∧
          renewalIntSlack s 38 = 33653111804465618738521668273258057613381037549315055563 ∧
          centeredRenewalSlack s 38 = -15386745503242824728945436595551836262418614360560214069 := by
    intro hs36 hs37
    obtain ⟨hT37, hS37, _⟩ := h37_vals hs36
    have hstep37 := subCeiling_step_sandwich_iff s 37
    have hT38 : blockSteps s 38 = 185 := by
      change blockSteps s 37 + s 37 = 185
      rw [hT37, hs37]
    have hS38 : renewalIntSlack s 38 = 33653111804465618738521668273258057613381037549315055563 := by
      have h1 := hstep37.1
      rw [h1, hT37, hS37, hs37]
      norm_num
    have hC38 : centeredRenewalSlack s 38 = -15386745503242824728945436595551836262418614360560214069 := by
      have h2 := hstep37.2.1
      rw [h2, hT37, hS37, hs37]
      norm_num
    exact ⟨hT38, hS38, hC38⟩
  refine ⟨hiff36, ?_, ?_, ?_⟩
  · intro hs36
    obtain ⟨hT37, hS37, hC37⟩ := h37_vals hs36
    have hsand37 := (subCeiling_step_sandwich_iff s 37).2.2
    rw [hT37, hS37] at hsand37
    refine ⟨hT37, hS37, hC37, ?_⟩
    exact hsand37.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 4878993571106759469387254741143623902406679309965392401) (T_N := 182) (s_star := 3)
      (by norm_num) (by norm_num) (s 37)).1
  · intro hs36 hs37
    obtain ⟨hT38, hS38, hC38⟩ := h38_vals hs36 hs37
    have hsand38 := (subCeiling_step_sandwich_iff s 38).2.2
    rw [hT38, hS38] at hsand38
    refine ⟨hT38, hS38, hC38, ?_⟩
    exact hsand38.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 33653111804465618738521668273258057613381037549315055563) (T_N := 185) (s_star := 3)
      (by norm_num) (by norm_num) (s 38)).1
  · intro hs36 hs37 hs38
    obtain ⟨hT38, hS38, _⟩ := h38_vals hs36 hs37
    have hstep38 := subCeiling_step_sandwich_iff s 38
    have hT39 : blockSteps s 39 = 188 := by
      change blockSteps s 38 + s 38 = 188
      rw [hT38, hs38]
    have hS39 : renewalIntSlack s 39 = 123996301797236610460611365477009253548493583273502186089 := by
      have h1 := hstep38.1
      rw [h1, hT38, hS38, hs38]
      norm_num
    have hC39 : centeredRenewalSlack s 39 = -268322556664430937279125473473469897457903632005499970967 := by
      have h2 := hstep38.2.1
      rw [h2, hT38, hS38, hs38]
      norm_num
    refine ⟨hT39, hS39, hC39, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 39) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 39 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT39] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 189 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

end Mahler.FixedPointEigenDefectAndKneading39
