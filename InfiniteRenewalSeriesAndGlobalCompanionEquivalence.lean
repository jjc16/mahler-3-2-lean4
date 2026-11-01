import StrictEndpointResolutionAndSlackGrowth

/-!
# Complete Resolution of Question 5: Supremum Renewal Constant $\mathcal{H}_\infty$, Uniqueness of $\alpha = \mathcal{H}_\infty / 3$, and the Two-Way Infinite-Horizon All-Block Companion Equivalence

This module formalizes **Outer Loop 9 / 10 (Part XIII, Sections O9.1–O9.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`, completely resolving **Question 5 of Section A8.2**:

1. **Section O9.1 (Inner Loop 1 / 3) — Universal Upper Bound $A_{0,N} \le 2(3^{T_N} - 2^{T_N})$ & Supremum Renewal Scale $\mathcal{H}_\infty$
   (`renewalPartialSeq`, `renewalPartialSeq_strictMono_and_two_index_bound`,
   `supRenewalScale`, `supRenewalTail`, `supRenewalTail_bounds_and_recurrence`)**:
   - Specializing `renewalNumerator_bellman_upper_sandwich` to $L = 1$ ($\forall k, 1 \le s_k$) proves
     `renewalNumerator s N ≤ 2 * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N))` unconditionally.
   - Consequently, the partial renewal sequence $\mathcal{L}_N := P_0 + A_{0,N} / 3^{T_N}$ is
     strictly increasing (`StrictMono`) and satisfies
     `0 < renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K ≤ 2 * ((2 / 3) ^ T_K - (2 / 3) ^ T_M)`
     for all $K < M$.
   - Its least upper bound $\mathcal{H}_\infty := \sup_N \mathcal{L}_N$ satisfies
     $P_0 < \mathcal{H}_\infty \le P_0 + 2$, and its normalized boundary tails
     $h_r^\infty := \mathcal{H}_\infty (3/2)^{T_r} - P_r = \operatorname{renewalTail}(b_0, \mathcal{H}_\infty / 3, T_r)$
     satisfy $0 < h_r^\infty \le 2$ and $h_{r+1}^\infty = (3/2)^{s_r} h_r^\infty - 1$ for all $r \in \mathbb{N}$.

2. **Section O9.2 (Inner Loop 2 / 3) — All-Time Coverage & Converse Companion Construction
   (`exists_block_interval_containing_time`, `validCompanionForever_of_forall_supRenewalTail_lt_half`)**:
   - Proves that for every sequence $s$ with $\forall k, 1 \le s_k$ and every time $n \in \mathbb{N}$,
     there exist $r \le n$ and $v \le s_r$ such that $n = \operatorname{blockSteps} s r + v$.
   - Proves the **Converse Direction:** along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`),
     if $\forall r \in \mathbb{N},\, h_r^\infty < 1/2$, then setting $\alpha_\infty := \mathcal{H}_\infty / 3$
     satisfies `ValidCompanionForever b_0 (supRenewalScale b_0 s / 3)` across all ordinary times $n \in \mathbb{N}$!

3. **Section O9.3 (Inner Loop 3 / 3) — Companion Uniqueness $\alpha = \mathcal{H}_\infty / 3$ & Full Two-Way Equivalence
   (`validCompanionForever_imp_eq_supRenewalScale_div_three`,
   `exists_validCompanionForever_iff_forall_supRenewalTail_lt_half`)**:
   - Proves that if `ValidCompanionForever b_0 α` holds, then $\alpha = \mathcal{H}_\infty / 3$ uniquely
     and $h_r^\infty < 1/2$ for all $r \in \mathbb{N}$.
   - Bundles both directions into the **Two-Way Infinite-Horizon All-Block Companion Equivalence**:
     $$\big(\exists \alpha \in \mathbb{R},\; \operatorname{ValidCompanionForever} b_0 \, \alpha\big)
       \;\Longleftrightarrow\;
       \big(\forall r \in \mathbb{N},\; \operatorname{supRenewalTail} b_0 \, s \, r < 1/2\big)
       \;\Longleftrightarrow\;
       \operatorname{ValidCompanionForever} b_0 \, (\operatorname{supRenewalScale} b_0 \, s / 3).$$
-/

namespace Mahler.InfiniteRenewalEquivalence

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

/-! ## 1. Section O9.1: Partial Renewal Sequence $\mathcal{L}_N$, Supremum $\mathcal{H}_\infty$ & Tail Recurrence -/

/-- Partial renewal sequence $\mathcal{L}_N = P_0 + A_{0,N} / 3^{T_N}$. -/
noncomputable def renewalPartialSeq (b_0 : ℕ) (s : ℕ → ℕ) (N : ℕ) : ℝ :=
  (oddReturnP b_0 : ℝ) + (renewalNumerator s N : ℝ) / (3 : ℝ) ^ (blockSteps s N)

/-- Supremum renewal constant $\mathcal{H}_\infty = \sup_N \mathcal{L}_N$. -/
noncomputable def supRenewalScale (b_0 : ℕ) (s : ℕ → ℕ) : ℝ :=
  sSup (Set.range (renewalPartialSeq b_0 s))

/-- Supremum renewal tail $h_r^\infty = \operatorname{renewalTail}(b_0, \mathcal{H}_\infty / 3, T_r)$. -/
noncomputable def supRenewalTail (b_0 : ℕ) (s : ℕ → ℕ) (r : ℕ) : ℝ :=
  renewalTail b_0 (supRenewalScale b_0 s / 3) (blockSteps s r)

/-- **Strict Monotonicity and Two-Index Upper Bound for $\mathcal{L}_N$
(`renewalPartialSeq_strictMono_and_two_index_bound`, Section O9.1)**:
Whenever `∀ k, 1 ≤ s k`:
1. For all `K < M`, setting `T_K = blockSteps s K` and `T_M = blockSteps s M`:
   `0 < renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K` and
   `renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K ≤ 2 * ((2 / 3 : ℝ) ^ T_K - (2 / 3 : ℝ) ^ T_M)`,
2. `StrictMono (renewalPartialSeq b_0 s)`, and
3. For all `N`, `(oddReturnP b_0 : ℝ) ≤ renewalPartialSeq b_0 s N` and
   `renewalPartialSeq b_0 s N ≤ (oddReturnP b_0 : ℝ) + 2`. -/
theorem renewalPartialSeq_strictMono_and_two_index_bound (b_0 : ℕ) {s : ℕ → ℕ}
    (hs : ∀ k : ℕ, 1 ≤ s k) :
    (∀ K M : ℕ, K < M →
      0 < renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K ∧
        renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K ≤
          2 * ((2 / 3 : ℝ) ^ (blockSteps s K) - (2 / 3 : ℝ) ^ (blockSteps s M))) ∧
      StrictMono (renewalPartialSeq b_0 s) ∧
      (∀ N : ℕ,
        (oddReturnP b_0 : ℝ) ≤ renewalPartialSeq b_0 s N ∧
          renewalPartialSeq b_0 s N ≤ (oddReturnP b_0 : ℝ) + 2) := by
  have htwo_idx :
      ∀ K M : ℕ, K < M →
        0 < renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K ∧
          renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K ≤
            2 * ((2 / 3 : ℝ) ^ (blockSteps s K) - (2 / 3 : ℝ) ^ (blockSteps s M)) := by
    intro K M hKM
    have hM_eq : K + (M - K) = M := by omega
    have hMK_pos : 1 ≤ M - K := by omega
    set s' := fun t => s (K + t)
    set d := blockSteps s' (M - K)
    set TK := blockSteps s K
    set TM := blockSteps s M
    have hshift := blockSteps_add_shift s K (M - K)
    rw [hM_eq] at hshift
    change TM = TK + d at hshift
    have hcomp := renewalNumerator_cocycle_composition s K (M - K)
    rw [hM_eq] at hcomp
    change renewalNumerator s M = 3 ^ d * renewalNumerator s K + 2 ^ TK * renewalNumerator s' (M - K) at hcomp
    have h3K_pos : (0 : ℝ) < (3 : ℝ) ^ TK := pow_pos (by norm_num) TK
    have h3d_pos : (0 : ℝ) < (3 : ℝ) ^ d := pow_pos (by norm_num) d
    have h3K_ne : (3 : ℝ) ^ TK ≠ 0 := ne_of_gt h3K_pos
    have h3d_ne : (3 : ℝ) ^ d ≠ 0 := ne_of_gt h3d_pos
    have hdiff_eq :
        renewalPartialSeq b_0 s M - renewalPartialSeq b_0 s K =
          (2 / 3 : ℝ) ^ TK * ((renewalNumerator s' (M - K) : ℝ) / (3 : ℝ) ^ d) := by
      unfold renewalPartialSeq
      change ((oddReturnP b_0 : ℝ) + (renewalNumerator s M : ℝ) / (3 : ℝ) ^ TM) -
        ((oddReturnP b_0 : ℝ) + (renewalNumerator s K : ℝ) / (3 : ℝ) ^ TK) = _
      rw [hshift, hcomp, pow_add, div_pow]
      push_cast
      field_simp [h3K_ne, h3d_ne]
      ring
    rw [hdiff_eq]
    have hqK_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ TK := pow_pos (by norm_num) TK
    have hA_pos_nat := (renewalNumerator_pos_of_pos_horizon s' hMK_pos).2
    have hA_pos : (0 : ℝ) < (renewalNumerator s' (M - K) : ℝ) := by
      exact_mod_cast (by omega : 0 < renewalNumerator s' (M - K))
    have hbell_nat := renewalNumerator_bellman_upper_sandwich (s := s') (N := M - K) (L := 1)
      (fun k _ => hs (K + k))
    change (3 ^ 1 - 2 ^ 1) * renewalNumerator s' (M - K) ≤ 2 ^ 1 * (3 ^ d - 2 ^ d) at hbell_nat
    have hd_le : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
    have hbell_r : (renewalNumerator s' (M - K) : ℝ) ≤ 2 * ((3 : ℝ) ^ d - (2 : ℝ) ^ d) := by
      have h1 : renewalNumerator s' (M - K) ≤ 2 * (3 ^ d - 2 ^ d) := by omega
      zify [hd_le] at h1
      exact_mod_cast h1
    have hdiv_le : (renewalNumerator s' (M - K) : ℝ) / (3 : ℝ) ^ d ≤ 2 * (1 - (2 / 3 : ℝ) ^ d) := by
      rw [div_pow, div_le_iff₀ h3d_pos]
      have hring :
          2 * (1 - (2 : ℝ) ^ d / (3 : ℝ) ^ d) * (3 : ℝ) ^ d =
            2 * ((3 : ℝ) ^ d - (2 : ℝ) ^ d) := by
        calc
          2 * (1 - (2 : ℝ) ^ d / (3 : ℝ) ^ d) * (3 : ℝ) ^ d =
              2 * ((3 : ℝ) ^ d - (2 : ℝ) ^ d / (3 : ℝ) ^ d * (3 : ℝ) ^ d) := by ring
          _ = 2 * ((3 : ℝ) ^ d - (2 : ℝ) ^ d) := by rw [div_mul_cancel₀ _ h3d_ne]
      rw [hring]
      exact hbell_r
    have hmul_le := mul_le_mul_of_nonneg_left hdiv_le (le_of_lt hqK_pos)
    have hq_expand :
        (2 / 3 : ℝ) ^ TK * (2 * (1 - (2 / 3 : ℝ) ^ d)) =
          2 * ((2 / 3 : ℝ) ^ TK - (2 / 3 : ℝ) ^ TM) := by
      rw [hshift, pow_add]
      ring
    refine ⟨mul_pos hqK_pos (div_pos hA_pos h3d_pos), by linarith⟩
  have hmono : StrictMono (renewalPartialSeq b_0 s) := by
    intro K M hKM
    have h := (htwo_idx K M hKM).1
    linarith
  refine ⟨htwo_idx, hmono, ?_⟩
  intro N
  cases N with
  | zero =>
      unfold renewalPartialSeq blockSteps renewalNumerator
      simp only [Nat.cast_zero, pow_zero, div_one, add_zero, le_refl, true_and]
      linarith
  | succ N =>
      have h0 := htwo_idx 0 (N + 1) (by omega)
      have hL0 : renewalPartialSeq b_0 s 0 = (oddReturnP b_0 : ℝ) := by
        unfold renewalPartialSeq blockSteps renewalNumerator
        ring
      have hT0 : (2 / 3 : ℝ) ^ (blockSteps s 0) = 1 := by
        change (2 / 3 : ℝ) ^ 0 = 1
        ring
      have hq_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (blockSteps s (N + 1)) :=
        pow_pos (by norm_num) _
      rw [hL0, hT0] at h0
      constructor <;> linarith

/-- **Bounds and Recurrence of the Supremum Renewal Tail $h_r^\infty$
(`supRenewalTail_bounds_and_recurrence`, Section O9.1)**:
Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`):
1. `IsLUB (Set.range (renewalPartialSeq b_0 s)) (supRenewalScale b_0 s)`,
2. For every `r : ℕ`, `0 < supRenewalTail b_0 s r` and `supRenewalTail b_0 s r ≤ 2`, and
3. For every `r : ℕ`,
   `supRenewalTail b_0 s (r + 1) = (3 / 2 : ℝ) ^ (s r) * supRenewalTail b_0 s r - 1` and
   `supRenewalTail b_0 s r = (2 / 3 : ℝ) ^ (s r) * (1 + supRenewalTail b_0 s (r + 1))`. -/
theorem supRenewalTail_bounds_and_recurrence {b_0 : ℕ} {s u : ℕ → ℕ}
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N) :
    let H := supRenewalScale b_0 s
    IsLUB (Set.range (renewalPartialSeq b_0 s)) H ∧
      (∀ r : ℕ, 0 < supRenewalTail b_0 s r ∧ supRenewalTail b_0 s r ≤ 2) ∧
      (∀ r : ℕ,
        supRenewalTail b_0 s (r + 1) = (3 / 2 : ℝ) ^ (s r) * supRenewalTail b_0 s r - 1 ∧
          supRenewalTail b_0 s r = (2 / 3 : ℝ) ^ (s r) * (1 + supRenewalTail b_0 s (r + 1))) := by
  intro H
  have hs : ∀ k : ℕ, 1 ≤ s k := fun k => (hchain (k + 1) k (by omega)).1
  rcases renewalPartialSeq_strictMono_and_two_index_bound b_0 hs with ⟨htwo_idx, hmono, hbounds⟩
  set LSeq := renewalPartialSeq b_0 s
  have hbdd : BddAbove (Set.range LSeq) := by
    refine ⟨(oddReturnP b_0 : ℝ) + 2, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact (hbounds N).2
  have hLUB : IsLUB (Set.range LSeq) H := Real.isLUB_sSup (Set.range_nonempty LSeq) hbdd
  have hle_H : ∀ K : ℕ, LSeq K ≤ H := fun K => hLUB.1 ⟨K, rfl⟩
  have hH_le : ∀ K : ℕ, H ≤ LSeq K + 2 * (2 / 3 : ℝ) ^ (blockSteps s K) := by
    intro K
    refine hLUB.2 ?_
    rintro _ ⟨M, rfl⟩
    rcases lt_trichotomy M K with hMK | rfl | hKM
    · have hlt : LSeq M < LSeq K := hmono hMK
      have hq_nonneg : (0 : ℝ) ≤ 2 * (2 / 3 : ℝ) ^ (blockSteps s K) := by positivity
      linarith
    · have hq_nonneg : (0 : ℝ) ≤ 2 * (2 / 3 : ℝ) ^ (blockSteps s M) := by positivity
      linarith
    · have h2 := (htwo_idx K M hKM).2
      have hqM_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (blockSteps s M) := pow_pos (by norm_num) _
      linarith
  have htail_eq :
      ∀ r : ℕ,
        supRenewalTail b_0 s r =
          (3 / 2 : ℝ) ^ (blockSteps s r) * (H - LSeq r) := by
    intro r
    unfold supRenewalTail renewalTail fracPart
    have hnorm := renewal_normalized_prefix_identity (hchain r)
    dsimp only at hnorm
    set Tr := blockSteps s r
    have hP_def : (oddReturnP (orbit b_0 Tr) : ℝ) = 3 * (orbit b_0 Tr : ℝ) + 1 := by
      unfold oddReturnP
      push_cast
      ring
    have hL_def : LSeq r = (oddReturnP b_0 : ℝ) + (renewalNumerator s r : ℝ) / (3 : ℝ) ^ Tr := rfl
    rw [← hL_def] at hnorm
    have hcancel : (3 / 2 : ℝ) ^ Tr * (2 / 3 : ℝ) ^ Tr = 1 := by
      rw [← mul_pow]
      norm_num
    have hPr_eq : (oddReturnP (orbit b_0 Tr) : ℝ) = (3 / 2 : ℝ) ^ Tr * LSeq r := by
      calc
        (oddReturnP (orbit b_0 Tr) : ℝ) =
            ((3 / 2 : ℝ) ^ Tr * (2 / 3 : ℝ) ^ Tr) * (oddReturnP (orbit b_0 Tr) : ℝ) := by
          rw [hcancel, one_mul]
        _ = (3 / 2 : ℝ) ^ Tr * ((2 / 3 : ℝ) ^ Tr * (oddReturnP (orbit b_0 Tr) : ℝ)) := by ring
        _ = (3 / 2 : ℝ) ^ Tr * LSeq r := by rw [hnorm]
    linarith [hP_def, hPr_eq]
  refine ⟨hLUB, ?_, ?_⟩
  · intro r
    rw [htail_eq r]
    set Tr := blockSteps s r
    have hstep_pos := (htwo_idx r (r + 1) (by omega)).1
    have hle_r1 : LSeq (r + 1) ≤ H := hle_H (r + 1)
    have hH_gt : 0 < H - LSeq r := by linarith
    have hH_diff_le : H - LSeq r ≤ 2 * (2 / 3 : ℝ) ^ Tr := by
      have h := hH_le r
      linarith
    have h32_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ Tr := pow_pos (by norm_num) Tr
    have hcancel2 : (3 / 2 : ℝ) ^ Tr * (2 * (2 / 3 : ℝ) ^ Tr) = 2 := by
      have hc : (3 / 2 : ℝ) ^ Tr * (2 / 3 : ℝ) ^ Tr = 1 := by
        rw [← mul_pow]; norm_num
      calc
        (3 / 2 : ℝ) ^ Tr * (2 * (2 / 3 : ℝ) ^ Tr) =
            2 * ((3 / 2 : ℝ) ^ Tr * (2 / 3 : ℝ) ^ Tr) := by ring
        _ = 2 := by rw [hc, mul_one]
    refine ⟨mul_pos h32_pos hH_gt, ?_⟩
    calc
      (3 / 2 : ℝ) ^ Tr * (H - LSeq r) ≤ (3 / 2 : ℝ) ^ Tr * (2 * (2 / 3 : ℝ) ^ Tr) :=
        mul_le_mul_of_nonneg_left hH_diff_le (le_of_lt h32_pos)
      _ = 2 := hcancel2
  · intro r
    rcases hchain (r + 1) r (by omega) with ⟨hsr, _, hdecomp⟩
    set Tr := blockSteps s r
    set br := orbit b_0 Tr
    set αr := (H / 3) * (3 / 2 : ℝ) ^ Tr
    have hrec_br := (renewalTail_recurrence_and_block_companion_iff hsr hdecomp αr).1
    have h0_eq : renewalTail br αr 0 = supRenewalTail b_0 s r := by
      dsimp [br, αr, Tr, H]
      unfold supRenewalTail renewalTail fracPart
      simp only [orbit, pow_zero, mul_one]
    have h1_eq : renewalTail br αr (s r) = supRenewalTail b_0 s (r + 1) := by
      dsimp [br, αr, Tr, H]
      unfold supRenewalTail renewalTail fracPart
      have hT_succ : blockSteps s (r + 1) = blockSteps s r + s r := rfl
      rw [hT_succ, orbit_add, pow_add, ← mul_assoc]
    rw [← h0_eq, ← h1_eq]
    exact hrec_br

/-! ## 2. Section O9.2: All-Time Coverage & Converse Companion Construction -/

/-- **All-Time Block Coverage Lemma (`exists_block_interval_containing_time`, Section O9.2)**:
For every sequence `s : ℕ → ℕ` with `∀ k, 1 ≤ s k` and every time `n : ℕ`, there exist
`r ≤ n` and `v ≤ s r` such that `n = blockSteps s r + v`. -/
theorem exists_block_interval_containing_time {s : ℕ → ℕ}
    (hs : ∀ k : ℕ, 1 ≤ s k) (n : ℕ) :
    ∃ r ≤ n, ∃ v ≤ s r, n = blockSteps s r + v := by
  induction n with
  | zero =>
      exact ⟨0, le_refl 0, 0, by omega, by simp [blockSteps]⟩
  | succ n ih =>
      rcases ih with ⟨r, hrn, v, hvs, hneq⟩
      rcases lt_or_eq_of_le hvs with hlt | rfl
      · exact ⟨r, by omega, v + 1, by omega, by omega⟩
      · refine ⟨r + 1, by omega, 1, hs (r + 1), ?_⟩
        simp only [blockSteps]
        omega

/-- **Converse Companion Construction (`validCompanionForever_of_forall_supRenewalTail_lt_half`,
Section O9.2)**:
Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`), if
`∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2`, then `ValidCompanionForever b_0 (supRenewalScale b_0 s / 3)`
holds across **all ordinary times $n \in \mathbb{N}$**! -/
theorem validCompanionForever_of_forall_supRenewalTail_lt_half {b_0 : ℕ} {s u : ℕ → ℕ}
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N)
    (htail_lt : ∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2) :
    ValidCompanionForever b_0 (supRenewalScale b_0 s / 3) := by
  have hs : ∀ k : ℕ, 1 ≤ s k := fun k => (hchain (k + 1) k (by omega)).1
  have hmain := supRenewalTail_bounds_and_recurrence hchain
  set α := supRenewalScale b_0 s / 3
  intro n
  rcases exists_block_interval_containing_time hs n with ⟨r, _, v, hvs, rfl⟩
  rcases hchain (r + 1) r (by omega) with ⟨hsr, _, hdecomp⟩
  set Tr := blockSteps s r
  set br := orbit b_0 Tr
  set αr := α * (3 / 2 : ℝ) ^ Tr
  have h0_eq : renewalTail br αr 0 = supRenewalTail b_0 s r := by
    dsimp [br, αr, Tr, α]
    unfold supRenewalTail renewalTail fracPart
    simp only [orbit, pow_zero, mul_one]
  have h1_eq : renewalTail br αr (s r) = supRenewalTail b_0 s (r + 1) := by
    dsimp [br, αr, Tr, α]
    unfold supRenewalTail renewalTail fracPart
    have hT_succ : blockSteps s (r + 1) = blockSteps s r + s r := rfl
    rw [hT_succ, orbit_add, pow_add, ← mul_assoc]
  have hh1_pos : 0 < renewalTail br αr (s r) := by
    rw [h1_eq]
    exact (hmain.2.1 (r + 1)).1
  have hh1_lt : renewalTail br αr (s r) < 1 / 2 := by
    rw [h1_eq]
    exact htail_lt (r + 1)
  have hh0_lt : renewalTail br αr 0 < 1 / 2 := by
    rw [h0_eq]
    exact htail_lt r
  have hblock :=
    (renewalTail_recurrence_and_block_companion_iff hsr hdecomp αr).2.2 hh1_pos hh1_lt hh0_lt
  have hv_comp : ValidCompanionAt br αr v := hblock.2 v hvs
  unfold ValidCompanionAt at hv_comp ⊢
  rw [orbit_add, pow_add, ← mul_assoc]
  exact hv_comp

/-! ## 3. Section O9.3: Uniqueness $\alpha = \mathcal{H}_\infty / 3$ & Full Two-Way Equivalence -/

/-- **Uniqueness of the Companion Scale $\alpha = \mathcal{H}_\infty / 3$
(`validCompanionForever_imp_eq_supRenewalScale_div_three`, Section O9.3)**:
Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`), if
`ValidCompanionForever b_0 α` holds, then `α = supRenewalScale b_0 s / 3` and
`∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2`. -/
theorem validCompanionForever_imp_eq_supRenewalScale_div_three
    {b_0 : ℕ} {s u : ℕ → ℕ} {α : ℝ}
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N)
    (hforever : ValidCompanionForever b_0 α) :
    α = supRenewalScale b_0 s / 3 ∧
      ∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2 := by
  have hLUB := (supRenewalTail_bounds_and_recurrence hchain).1
  set H := supRenewalScale b_0 s
  set LSeq := renewalPartialSeq b_0 s
  have hLN_le_3a : ∀ N : ℕ, LSeq N ≤ 3 * α := by
    intro N
    have h0 : ValidCompanionAt b_0 α 0 := hforever 0
    have hf0 := (validCompanionAt_iff_fracPart b_0 α 0).mp h0
    have h3a_eq : 3 * α = (oddReturnP b_0 : ℝ) + renewalTail b_0 α 0 := by
      unfold oddReturnP renewalTail fracPart
      simp only [orbit, pow_zero, mul_one]
      push_cast
      ring
    rcases Nat.eq_zero_or_pos N with rfl | hN_pos
    · unfold LSeq renewalPartialSeq blockSteps renewalNumerator
      simp only [Nat.cast_zero, pow_zero, div_one, add_zero]
      have hsurv1 : ValidCompanionUpTo b_0 α (blockSteps s 1 + 1) :=
        (validCompanionForever_iff_forall_upTo b_0 α).mp hforever (blockSteps s 1 + 1)
      have hb1 := validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound
        (by decide : 1 ≤ 1) (hchain 1) hsurv1
      have hA1_pos : (0 : ℝ) ≤ (renewalNumerator s 1 : ℝ) / (3 : ℝ) ^ (blockSteps s 1) := by
        positivity
      linarith [hb1.2.2.2.2, h3a_eq]
    · have hsurvN : ValidCompanionUpTo b_0 α (blockSteps s N + 1) :=
        (validCompanionForever_iff_forall_upTo b_0 α).mp hforever (blockSteps s N + 1)
      have hbN := validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound hN_pos (hchain N) hsurvN
      unfold LSeq renewalPartialSeq
      linarith [hbN.2.2.2.2, h3a_eq]
  have hH_le_3a : H ≤ 3 * α := by
    refine hLUB.2 ?_
    rintro _ ⟨N, rfl⟩
    exact hLN_le_3a N
  have h3a_le_H : 3 * α ≤ H := by
    by_contra hlt
    push_neg at hlt
    set δ := 3 * α - H
    have hδ_pos : 0 < δ := sub_pos.mpr hlt
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (2 / δ) < (K : ℝ) := exists_nat_gt (2 / δ)
    have hN : 1 ≤ K + 1 := by omega
    set TN := blockSteps s (K + 1)
    have hTN_ge : K + 1 ≤ TN :=
      id_le_blockSteps (fun k hk => (hchain (K + 1) k hk).1)
    have htail_id := (multi_block_renewalTail_and_slack_identity (hchain (K + 1)) α).1
    change (2 : ℝ) ^ TN * renewalTail b_0 α TN =
      (3 : ℝ) ^ TN * renewalTail b_0 α 0 - (renewalNumerator s (K + 1) : ℝ) at htail_id
    have h3a_eq : 3 * α = (oddReturnP b_0 : ℝ) + renewalTail b_0 α 0 := by
      unfold oddReturnP renewalTail fracPart
      simp only [orbit, pow_zero, mul_one]
      push_cast
      ring
    have h3TN_pos : (0 : ℝ) < (3 : ℝ) ^ TN := pow_pos (by norm_num) TN
    have h3TN_ne : (3 : ℝ) ^ TN ≠ 0 := ne_of_gt h3TN_pos
    have hdiff_LN :
        3 * α - LSeq (K + 1) = (2 / 3 : ℝ) ^ TN * renewalTail b_0 α TN := by
      unfold LSeq renewalPartialSeq
      dsimp only [TN] at htail_id h3TN_ne ⊢
      rw [h3a_eq, div_pow]
      field_simp [h3TN_ne]
      linarith [htail_id]
    have hfTN := (validCompanionAt_iff_fracPart b_0 α TN).mp (hforever TN)
    have hhTN_lt : renewalTail b_0 α TN < 1 / 2 := by
      unfold renewalTail
      linarith [hfTN.2]
    have hLE_H : LSeq (K + 1) ≤ H := hLUB.1 ⟨K + 1, rfl⟩
    have hδ_le_diff : δ ≤ 3 * α - LSeq (K + 1) := sub_le_sub_left hLE_H (3 * α)
    have hq_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ TN := pow_pos (by norm_num) TN
    have hδ_lt_q : δ < (2 / 3 : ℝ) ^ TN := by
      have hm := mul_lt_mul_of_pos_left hhTN_lt hq_pos
      linarith [hdiff_LN, hδ_le_diff]
    have hpow_gt : ∀ n : ℕ, 1 + (n : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
          push_cast
          rw [pow_succ]
          have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          linarith
    have h32_TN : (K : ℝ) / 2 < (3 / 2 : ℝ) ^ TN := by
      have h1 : (K : ℝ) / 2 < 1 + (TN : ℝ) / 2 := by
        have hnat : (K : ℝ) ≤ (TN : ℝ) := by exact_mod_cast (by omega : K ≤ TN)
        linarith
      have h2 : 1 + (TN : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ TN := hpow_gt TN
      linarith
    have hcancel : (3 / 2 : ℝ) ^ TN * (2 / 3 : ℝ) ^ TN = 1 := by
      rw [← mul_pow]; norm_num
    have h32_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ TN := pow_pos (by norm_num) TN
    have hmul1 : (3 / 2 : ℝ) ^ TN * δ < 1 := by
      have hm := mul_lt_mul_of_pos_left hδ_lt_q h32_pos
      linarith [hcancel]
    have hmul2 : 2 < (K : ℝ) * δ := (div_lt_iff₀ hδ_pos).mp hK
    have hmul3 : ((K : ℝ) / 2) * δ < (3 / 2 : ℝ) ^ TN * δ :=
      mul_lt_mul_of_pos_right h32_TN hδ_pos
    have h1_lt : (1 : ℝ) < ((K : ℝ) / 2) * δ := by
      have hdiv2 : ((K : ℝ) / 2) * δ = ((K : ℝ) * δ) / 2 := by ring
      rw [hdiv2, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith [hmul2]
    exact lt_irrefl (1 : ℝ) (lt_trans h1_lt (lt_trans hmul3 hmul1))
  have hα_eq : α = H / 3 := by linarith
  refine ⟨hα_eq, ?_⟩
  intro r
  unfold supRenewalTail
  change renewalTail b_0 (H / 3) (blockSteps s r) < 1 / 2
  rw [← hα_eq]
  have hfr := (validCompanionAt_iff_fracPart b_0 α (blockSteps s r)).mp (hforever (blockSteps s r))
  unfold renewalTail
  linarith [hfr.2]

/-- **Two-Way Infinite-Horizon All-Block Companion Equivalence
(`exists_validCompanionForever_iff_forall_supRenewalTail_lt_half`, Section O9.3 & Question 5)**:
Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`):
1. `(∃ α : ℝ, ValidCompanionForever b_0 α) ↔ (∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2)`, and
2. `(∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2) ↔ ValidCompanionForever b_0 (supRenewalScale b_0 s / 3)`. -/
theorem exists_validCompanionForever_iff_forall_supRenewalTail_lt_half
    {b_0 : ℕ} {s u : ℕ → ℕ}
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N) :
    ((∃ α : ℝ, ValidCompanionForever b_0 α) ↔
      (∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2)) ∧
      ((∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2) ↔
        ValidCompanionForever b_0 (supRenewalScale b_0 s / 3)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨α, hforever⟩
    exact (validCompanionForever_imp_eq_supRenewalScale_div_three hchain hforever).2
  · intro htail
    exact ⟨supRenewalScale b_0 s / 3, validCompanionForever_of_forall_supRenewalTail_lt_half hchain htail⟩
  · intro htail
    exact validCompanionForever_of_forall_supRenewalTail_lt_half hchain htail
  · intro hforever
    exact (validCompanionForever_imp_eq_supRenewalScale_div_three hchain hforever).2

end Mahler.InfiniteRenewalEquivalence
