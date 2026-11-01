import AllBlockRepeatedWindowAndAnagramSyzygy
import SparseDefectCocycleAndValuationLock

/-!
# Exact Signed-Cocycle–Renewal Identity, the $s_k \ge 3$ Certificate Barrier, 4-Way Valuation Dictionary & the $\Sigma_2(2, s_1) = 3^{s_1} - 8 \cdot 2^{s_1}$ Law

This module formalizes **Outer Loop 3 / 10 (Part VII, Sections O3.1–O3.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O3.1 (Inner Loop 1 / 3) — Universal Identity $\operatorname{defectCocycleSum}(s, N) = 9 A_{0,N} - 8 K_N$
   and the $s_k \ge 3$ Finite-Certificate Barrier (`defectCocycleSum_eq_nine_mul_renewal_sub_eight_mul_kernel`,
   `nineteen_mul_renewal_and_slack_signed_cocycle_identities`,
   `no_finite_renewal_escape_of_all_blocks_ge_three`)**:
   - Proves the assumption-free identity across all sequences $s : \mathbb{N} \to \mathbb{N}$ and $N \in \mathbb{N}$:
     `defectCocycleSum s N = 9 * (renewalNumerator s N : ℤ) - 8 * (blockKernel s N : ℤ)`.
   - Combining with $3 K_N = (3^{T_N} - 2^{T_N}) + A_{0,N}$ ($\forall k < N, 1 \le s_k$) yields:
     `19 * (renewalNumerator s N : ℤ) = 8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N) + 3 * defectCocycleSum s N`
     and
     `19 * renewalIntSlack s N = 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N - 6 * defectCocycleSum s N`.
   - Consequently, whenever $\forall k < N,\, 3 \le s_k$, we have $\operatorname{defectCocycleSum}(s, N) \le 0$,
     so $19 \Sigma_N \ge 3 \cdot 3^{T_N} + 16 \cdot 2^{T_N} > 0$ and $2 A_{0,N} < 3^{T_N}$, proving that
     **every finite escape certificate $2 A_{0,N} \ge 3^{T_N}$ requires at least one short block $s_k \le 2$**!

2. **Section O3.2 (Inner Loop 2 / 3) — Exact 4-Way Valuation Dictionary Between $P(b) = 2^s u$ and $I(b) = 19 b + 9$
   (`three_mul_affInv_eq_nineteen_mul_oddReturnP_add_eight`,
   `odd_block_affInv_two_adic_valuation_four_way_dictionary`)**:
   - Proves $3(19 b + 9) = 19(3 b + 1) + 8$ and the exact 4-way divisibility dictionary for
     $3 b + 1 = 2^s u$ ($u$ odd):
     - $s = 1 \implies 2 \mid (19 b + 9) \land \neg(4 \mid (19 b + 9))$,
     - $s = 2 \implies 4 \mid (19 b + 9) \land \neg(8 \mid (19 b + 9))$,
     - $s \ge 4 \implies 8 \mid (19 b + 9) \land \neg(16 \mid (19 b + 9))$, and
     - $s = 3 \implies 16 \mid (19 b + 9)$.

3. **Section O3.3 (Inner Loop 3 / 3) — Closed Form $\Sigma_2(2, s_1) = 3^{s_1} - 8 \cdot 2^{s_1}$ & Unclipped Cap Identity
   (`two_block_two_s1_renewalNumerator_and_slack`,
   `two_block_two_s1_escape_iff_s1_le_five`,
   `unclipped_recoveryCap_eq_renewalIntSlack_div_two_pow`)**:
   - For any 2-block sequence with $s_0 = 2$ and $s_1 \ge 1$:
     `renewalNumerator s 2 = 4 * 3 ^ s₁ + 4 * 2 ^ s₁` and
     `renewalIntSlack s 2 = (3 : ℤ) ^ s₁ - 8 * (2 : ℤ) ^ s₁`.
   - Proves $2 A_{0,2} \ge 3^{2 + s_1} \iff s_1 \le 5$, while at $s_1 = 6$, $\Sigma_2 = 217$ and
     $\Sigma_2 / 2^{2 + 6 + 1} = 217 / 512 = B_2$.
   - Proves that along any prefix where the rational cap does not clip at $1/2$,
     `B_N = (renewalIntSlack s N : ℚ) / (2 : ℚ) ^ (blockSteps s N + 1)`.
-/

namespace Mahler.SignedCocycleRenewalBridge

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

/-! ## 1. Section O3.1: Exact Identity Between `defectCocycleSum`, `renewalNumerator`, and `renewalIntSlack` -/

/-- **Universal Identity $\operatorname{defectCocycleSum}(s, N) = 9 A_{0,N} - 8 K_N$
(`defectCocycleSum_eq_nine_mul_renewal_sub_eight_mul_kernel`, Section O3.1)**:
For every sequence `s : ℕ → ℕ` and horizon `N : ℕ`:
`defectCocycleSum s N = 9 * (renewalNumerator s N : ℤ) - 8 * (blockKernel s N : ℤ)`. -/
theorem defectCocycleSum_eq_nine_mul_renewal_sub_eight_mul_kernel (s : ℕ → ℕ) (N : ℕ) :
    defectCocycleSum s N =
      9 * (renewalNumerator s N : ℤ) - 8 * (blockKernel s N : ℤ) := by
  induction N with
  | zero => simp [defectCocycleSum, renewalNumerator, blockKernel]
  | succ N ih =>
      simp only [defectCocycleSum, renewalNumerator, blockKernel, defectTerm, blockSteps,
        pow_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ih]
      ring

/-- **Exact $19 A_{0,N}$ and $19 \Sigma_N$ Signed-Cocycle Identities
(`nineteen_mul_renewal_and_slack_signed_cocycle_identities`, Section O3.1)**:
For any valid block sequence (`∀ k < N, 1 ≤ s k`), setting `T_N = blockSteps s N`:
1. `19 * (renewalNumerator s N : ℤ) = 8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N) + 3 * defectCocycleSum s N`,
2. `19 * renewalIntSlack s N = 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N - 6 * defectCocycleSum s N`, and
3. `2 * renewalNumerator s N ≥ 3 ^ T_N ↔ 6 * defectCocycleSum s N ≥ 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N`. -/
theorem nineteen_mul_renewal_and_slack_signed_cocycle_identities {s : ℕ → ℕ} {N : ℕ}
    (hs : ∀ k < N, 1 ≤ s k) :
    let T_N := blockSteps s N
    19 * (renewalNumerator s N : ℤ) =
      8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N) + 3 * defectCocycleSum s N ∧
      19 * renewalIntSlack s N =
        3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N - 6 * defectCocycleSum s N ∧
      (2 * renewalNumerator s N ≥ 3 ^ T_N ↔
        6 * defectCocycleSum s N ≥ 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N) := by
  intro T_N
  have hdef := defectCocycleSum_eq_nine_mul_renewal_sub_eight_mul_kernel s N
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator hs
  change 3 * blockKernel s N = (3 ^ T_N - 2 ^ T_N) + renewalNumerator s N at hbridge
  have hle : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  have hbridge_z :
      3 * (blockKernel s N : ℤ) =
        (3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N + (renewalNumerator s N : ℤ) := by
    zify [hle] at hbridge
    exact_mod_cast hbridge
  have hid1 :
      19 * (renewalNumerator s N : ℤ) =
        8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N) + 3 * defectCocycleSum s N := by
    linarith [hdef, hbridge_z]
  have hid2 :
      19 * renewalIntSlack s N =
        3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N - 6 * defectCocycleSum s N := by
    unfold renewalIntSlack
    change 19 * ((3 : ℤ) ^ T_N - 2 * (renewalNumerator s N : ℤ)) = _
    linarith [hid1]
  have hcast : (3 : ℤ) ^ T_N = ((3 ^ T_N : ℕ) : ℤ) := by norm_cast
  have hiff :
      2 * renewalNumerator s N ≥ 3 ^ T_N ↔
        6 * defectCocycleSum s N ≥ 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N := by
    have hslack_nonpos :
        2 * renewalNumerator s N ≥ 3 ^ T_N ↔ renewalIntSlack s N ≤ 0 := by
      unfold renewalIntSlack
      change 2 * renewalNumerator s N ≥ 3 ^ T_N ↔
        (3 : ℤ) ^ T_N - 2 * (renewalNumerator s N : ℤ) ≤ 0
      rw [hcast]
      omega
    rw [hslack_nonpos]
    omega
  exact ⟨hid1, hid2, hiff⟩

/-- **The $s_k \ge 3$ Finite-Certificate Barrier (`no_finite_renewal_escape_of_all_blocks_ge_three`,
Section O3.1)**:
Whenever `∀ k < N, 3 ≤ s k`:
1. `defectCocycleSum s N ≤ 0`,
2. `19 * (renewalNumerator s N : ℤ) ≤ 8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N)`,
3. `19 * renewalIntSlack s N ≥ 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N > 0`, and
4. `2 * renewalNumerator s N < 3 ^ (blockSteps s N)`. -/
theorem no_finite_renewal_escape_of_all_blocks_ge_three {s : ℕ → ℕ} {N : ℕ}
    (hs3 : ∀ k < N, 3 ≤ s k) :
    let T_N := blockSteps s N
    defectCocycleSum s N ≤ 0 ∧
      19 * (renewalNumerator s N : ℤ) ≤ 8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N) ∧
      19 * renewalIntSlack s N ≥ 3 * (3 : ℤ) ^ T_N + 16 * (2 : ℤ) ^ T_N ∧
      2 * renewalNumerator s N < 3 ^ T_N := by
  have hcoc_nonpos : defectCocycleSum s N ≤ 0 := by
    induction N with
    | zero => simp [defectCocycleSum]
    | succ N ih =>
        have ih' := ih (fun k hk => hs3 k (by omega))
        have hsN : 3 ≤ s N := hs3 N (by omega)
        have hterm_nonpos : defectTerm (s N) ≤ 0 := by
          obtain ⟨k, hk⟩ : ∃ k : ℕ, s N = k + 3 := ⟨s N - 3, by omega⟩
          rw [hk]
          unfold defectTerm
          have hsub : k + 3 - 1 = k + 2 := by omega
          rw [hsub, pow_add (2 : ℤ) k 3, pow_add (3 : ℤ) k 2]
          have hpow : (2 : ℤ) ^ k ≤ (3 : ℤ) ^ k := by
            exact_mod_cast Nat.pow_le_pow_left (by decide) k
          linarith
        simp only [defectCocycleSum]
        have h3_nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ (s N) := pow_nonneg (by decide) (s N)
        have h2_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (blockSteps s N) := pow_nonneg (by decide) _
        have hm1 : (3 : ℤ) ^ (s N) * defectCocycleSum s N ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h3_nonneg ih'
        have hm2 : (2 : ℤ) ^ (blockSteps s N) * defectTerm (s N) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h2_nonneg hterm_nonpos
        linarith
  intro T_N
  have hs1 : ∀ k < N, 1 ≤ s k := fun k hk => by have := hs3 k hk; omega
  have hids := nineteen_mul_renewal_and_slack_signed_cocycle_identities hs1
  change 19 * (renewalNumerator s N : ℤ) =
    8 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N) + 3 * defectCocycleSum s N ∧ _ at hids
  have h3_pos : (0 : ℤ) < (3 : ℤ) ^ T_N := pow_pos (by decide) T_N
  have h2_pos : (0 : ℤ) < (2 : ℤ) ^ T_N := pow_pos (by decide) T_N
  have hslack_pos : 0 < renewalIntSlack s N := by linarith [hids.2.1]
  have hlt := (renewalIntSlack_eq_return_pinch_margin_and_odd hs1).2.2.mp hslack_pos
  exact ⟨hcoc_nonpos, by linarith [hids.1], by linarith [hids.2.1], hlt⟩

/-! ## 2. Section O3.2: Exact 4-Way Valuation Dictionary Between $P(b) = 2^s u$ and $I(b) = 19 b + 9$ -/

/-- Universal affine bridge `3 * (19 * b + 9) = 19 * oddReturnP b + 8`. -/
theorem three_mul_affInv_eq_nineteen_mul_oddReturnP_add_eight (b : ℕ) :
    3 * (19 * b + 9) = 19 * oddReturnP b + 8 := by
  unfold oddReturnP
  ring

/-- **Exact 4-Way Valuation Dictionary Between $P(b) = 2^s u$ and $I(b) = 19 b + 9$
(`odd_block_affInv_two_adic_valuation_four_way_dictionary`, Section O3.2)**:
Suppose `3 * b + 1 = 2 ^ s * u` with `u % 2 = 1`:
1. If `s = 1`, then `2 ∣ (19 * b + 9) ∧ ¬ (4 ∣ (19 * b + 9))`,
2. If `s = 2`, then `4 ∣ (19 * b + 9) ∧ ¬ (8 ∣ (19 * b + 9))`,
3. If `4 ≤ s`, then `8 ∣ (19 * b + 9) ∧ ¬ (16 ∣ (19 * b + 9))`, and
4. If `s = 3`, then `16 ∣ (19 * b + 9)`. -/
theorem odd_block_affInv_two_adic_valuation_four_way_dictionary
    {b s u : ℕ} (hu : u % 2 = 1) (hdecomp : 3 * b + 1 = 2 ^ s * u) :
    (s = 1 → 2 ∣ (19 * b + 9) ∧ ¬ (4 ∣ (19 * b + 9))) ∧
      (s = 2 → 4 ∣ (19 * b + 9) ∧ ¬ (8 ∣ (19 * b + 9))) ∧
      (4 ≤ s → 8 ∣ (19 * b + 9) ∧ ¬ (16 ∣ (19 * b + 9))) ∧
      (s = 3 → 16 ∣ (19 * b + 9)) := by
  have hrel : 3 * (19 * b + 9) = 19 * (2 ^ s * u) + 8 := by
    have h := three_mul_affInv_eq_nineteen_mul_oddReturnP_add_eight b
    unfold oddReturnP at h
    rw [hdecomp] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    simp only [Nat.pow_one] at hrel
    omega
  · rintro rfl
    change 3 * (19 * b + 9) = 19 * (4 * u) + 8 at hrel
    omega
  · intro hs4
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k + 4 := ⟨s - 4, by omega⟩
    have hpow : 2 ^ (k + 4) * u = 16 * (2 ^ k * u) := by
      rw [Nat.pow_add]
      ring
    rw [hpow] at hrel
    omega
  · rintro rfl
    change 3 * (19 * b + 9) = 19 * (8 * u) + 8 at hrel
    omega

/-! ## 3. Section O3.3: Closed Form $\Sigma_2(2, s_1) = 3^{s_1} - 8 \cdot 2^{s_1}$ & Unclipped Cap Identity -/

/-- **Two-Block $(2, s_1)$ Renewal Numerator & Slack Formula (`two_block_two_s1_renewalNumerator_and_slack`,
Section O3.3)**:
For any gap sequence `s` with `s 0 = 2`:
1. `blockSteps s 2 = 2 + s 1`,
2. `renewalNumerator s 2 = 4 * 3 ^ (s 1) + 4 * 2 ^ (s 1)`, and
3. `renewalIntSlack s 2 = (3 : ℤ) ^ (s 1) - 8 * (2 : ℤ) ^ (s 1)`. -/
theorem two_block_two_s1_renewalNumerator_and_slack {s : ℕ → ℕ} (hs0 : s 0 = 2) :
    blockSteps s 2 = 2 + s 1 ∧
      renewalNumerator s 2 = 4 * 3 ^ (s 1) + 4 * 2 ^ (s 1) ∧
      renewalIntSlack s 2 = (3 : ℤ) ^ (s 1) - 8 * (2 : ℤ) ^ (s 1) := by
  have hT1 : blockSteps s 1 = 2 := by
    simp [blockSteps, hs0]
  have hT2 : blockSteps s 2 = 2 + s 1 := by
    simp [blockSteps, hs0]
  have hA1 : renewalNumerator s 1 = 4 := by
    simp [renewalNumerator, hT1]
  have hA2 : renewalNumerator s 2 = 4 * 3 ^ (s 1) + 4 * 2 ^ (s 1) := by
    change 3 ^ (s 1) * renewalNumerator s 1 + 2 ^ (blockSteps s 2) = _
    rw [hA1, hT2, Nat.pow_add]
    ring
  have hS2 : renewalIntSlack s 2 = (3 : ℤ) ^ (s 1) - 8 * (2 : ℤ) ^ (s 1) := by
    unfold renewalIntSlack
    rw [hT2, hA2, pow_add]
    push_cast
    ring
  exact ⟨hT2, hA2, hS2⟩

/-- **Exact Escape Threshold for $(2, s_1)$ Pairs (`two_block_two_s1_escape_iff_s1_le_five`,
Section O3.3)**:
For any gap sequence `s` with `s 0 = 2`:
1. `2 * renewalNumerator s 2 ≥ 3 ^ (blockSteps s 2) ↔ s 1 ≤ 5`, and
2. At `s 1 = 6`, `renewalIntSlack s 2 = 217` and
   `(renewalIntSlack s 2 : ℚ) / (2 : ℚ) ^ (blockSteps s 2 + 1) = 217 / 512`. -/
theorem two_block_two_s1_escape_iff_s1_le_five {s : ℕ → ℕ} (hs0 : s 0 = 2) :
    (2 * renewalNumerator s 2 ≥ 3 ^ (blockSteps s 2) ↔ s 1 ≤ 5) ∧
      (s 1 = 6 →
        renewalIntSlack s 2 = 217 ∧
          (renewalIntSlack s 2 : ℚ) / (2 : ℚ) ^ (blockSteps s 2 + 1) = 217 / 512) := by
  rcases two_block_two_s1_renewalNumerator_and_slack hs0 with ⟨hT2, hA2, hS2⟩
  have hpow_ge : ∀ m : ℕ, 8 * 2 ^ (m + 6) < 3 ^ (m + 6) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 8 * 2 ^ (m + 1 + 6) = 2 * (8 * 2 ^ (m + 6)) := by
          rw [show m + 1 + 6 = (m + 6) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 3 ^ (m + 1 + 6) = 3 * 3 ^ (m + 6) := by
          rw [show m + 1 + 6 = (m + 6) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hiff : 2 * renewalNumerator s 2 ≥ 3 ^ (blockSteps s 2) ↔ s 1 ≤ 5 := by
    rw [hT2, hA2, Nat.pow_add]
    change 2 * (4 * 3 ^ (s 1) + 4 * 2 ^ (s 1)) ≥ 9 * 3 ^ (s 1) ↔ s 1 ≤ 5
    constructor
    · intro hge
      by_contra hgt
      push_neg at hgt
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 1 = m + 6 := ⟨s 1 - 6, by omega⟩
      have hlt := hpow_ge m
      rw [← hm] at hlt
      omega
    · intro hle
      have hpow_le : ∀ n : ℕ, n ≤ 5 → 2 * (4 * 3 ^ n + 4 * 2 ^ n) ≥ 9 * 3 ^ n := by
        intro n hn
        rcases n with _ | _ | _ | _ | _ | _ | n
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · omega
      exact hpow_le (s 1) hle
  refine ⟨hiff, ?_⟩
  intro hs1
  rw [hS2, hT2, hs1]
  refine ⟨by norm_num, by norm_num⟩

/-- Unclipped rational cap step $(3/2)^s B - 1$ preserves the closed form
$B_N = \Sigma_N / 2^{T_N + 1}$ (`unclipped_recoveryCap_eq_renewalIntSlack_div_two_pow`, Section O3.3). -/
theorem unclipped_recoveryCap_eq_renewalIntSlack_div_two_pow (s : ℕ → ℕ) (N : ℕ) :
    let B := fun k => (renewalIntSlack s k : ℚ) / (2 : ℚ) ^ (blockSteps s k + 1)
    B 0 = 1 / 2 ∧
      B (N + 1) = (3 / 2 : ℚ) ^ (s N) * B N - 1 := by
  intro B
  have hrec := (renewalIntSlack_step_and_cocycle s N 0 0).2.1
  refine ⟨?_, ?_⟩
  · dsimp [B, renewalIntSlack, blockSteps, renewalNumerator]
    norm_num
  · dsimp [B]
    rw [hrec]
    simp only [blockSteps, pow_add, pow_succ, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat]
    have h2_ne : (2 : ℚ) ^ (blockSteps s N) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2s_ne : (2 : ℚ) ^ (s N) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [div_pow]
    field_simp [h2_ne, h2s_ne]
    ring

end Mahler.SignedCocycleRenewalBridge
