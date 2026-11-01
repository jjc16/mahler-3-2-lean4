import AllBlockConstantOfMotionAndBackwardRecovery

/-!
# Centered Renewal Slack $\widehat{\Sigma}_N = \Sigma_N - 2^{T_N}$, Mod-6 Non-Vanishing Law & Uniqueness of the $s_1 = 6$ Sub-Ceiling Rung

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 2 / 20 (Part XVII, Sections C2.O2.1–C2.O2.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O2.1 (Inner Loop 1 / 5) — Equal-Step-Sum Second-Difference Identity for $P_r$
   (`allBlock_equal_stepSum_second_difference_identity`)**:
   - Across two consecutive block segments $[0, K]$ and $[K, K+M]$ with equal step sums
     $T_K = d = T_{K+M} - T_K$:
     `(2 ^ d * P (K + M) + 3 ^ d * P 0) + renewalNumerator s K = 2 ^ d * P K + 3 ^ d * P K + renewalNumerator s' M`.

2. **Section C2.O2.2 (Inner Loop 2 / 5) — Centered Renewal Slack $\widehat{\Sigma}_N = \Sigma_N - 2^{T_N}$ & Homogeneous Cocycle Law
   (`centeredRenewalSlack`, `centeredRenewalSlack_step_and_cocycle`)**:
   - Defines $\widehat{\Sigma}_N := \Sigma_N - 2^{T_N} = 3^{T_N} - 2^{T_N} - 2 A_{0,N} \in \mathbb{Z}$.
   - Proves the one-step recurrence (for $1 \le s_N$)
     `centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * centeredRenewalSlack s N + 3 * (2 : ℤ) ^ (blockSteps s N) * ((3 : ℤ) ^ (s N - 1) - (2 : ℤ) ^ (s N))`
     and the homogeneous multi-step cocycle law
     `centeredRenewalSlack s (K + M) = (3 : ℤ) ^ d * centeredRenewalSlack s K + (2 : ℤ) ^ (blockSteps s K) * centeredRenewalSlack s' M`.

3. **Section C2.O2.3 (Inner Loop 3 / 5) — Sign of $\widehat{\Sigma}_N$ on $s_k \ge 3$ vs. $1 \le s_k \le 2$ Segments
   (`centeredRenewalSlack_nonneg_of_three_le_and_nonpos_of_le_two`)**:
   - Whenever $\forall k < N,\, 3 \le s_k$, `0 ≤ centeredRenewalSlack s N` (`2 ^ T_N ≤ renewalIntSlack s N`).
   - Whenever $\forall k < N,\, 1 \le s_k \le 2$, `centeredRenewalSlack s N ≤ 0` (`renewalIntSlack s N ≤ 2 ^ T_N`).

4. **Section C2.O2.4 (Inner Loop 4 / 5) — Kernel Identity $\widehat{\Sigma}_N = 3(3^{T_N} - 2^{T_N} - 2 K_N)$ & Mod-6 Non-Vanishing Law
   (`centeredRenewalSlack_eq_three_mul_and_mod_six_eq_three`)**:
   - For any valid block sequence (`∀ k < N, 1 ≤ s k`):
     `centeredRenewalSlack s N = 3 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N - 2 * (blockKernel s N : ℤ))`,
   - For `1 ≤ N`, `centeredRenewalSlack s N % 6 = 3` and `centeredRenewalSlack s N ≠ 0`
     (`renewalIntSlack s N ≠ 2 ^ T_N`).

5. **Section C2.O2.5 (Inner Loop 5 / 5) — Closed Form $\widehat{\Sigma}_2(2, s_1) = 3^{s_1} - 12 \cdot 2^{s_1}$ & Uniqueness of $s_1 = 6$
   (`two_block_centeredRenewalSlack_and_unique_subCeiling_rung_six`)**:
   - For $s_0 = 2$, `centeredRenewalSlack s 2 = (3 : ℤ) ^ (s 1) - 12 * (2 : ℤ) ^ (s 1)`.
   - Proves the exact trichotomy:
     - `renewalIntSlack s 2 ≤ 0 ↔ s 1 ≤ 5` (Escape),
     - `(0 < renewalIntSlack s 2 ∧ centeredRenewalSlack s 2 < 0) ↔ s 1 = 6`
       (**Unique Sub-Ceiling Recovery Rung**, with $\widehat{\Sigma}_2(2, 6) = -39$), and
     - `0 < centeredRenewalSlack s 2 ↔ 7 ≤ s 1` (Full Ceiling Restoration in one block, with
       $\widehat{\Sigma}_2(2, 7) = 651$).
-/

namespace Mahler.CenteredRenewalSlack

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

/-! ## 1. Section C2.O2.1: Equal-Step-Sum Second-Difference Identity for $P_r$ -/

/-- **Equal-Step-Sum Second-Difference Identity for $P_r$
(`allBlock_equal_stepSum_second_difference_identity`, Section C2.O2.1)**:
Suppose `ValidBlockChain b_0 s u (K + M)` holds and the two consecutive segments $[0, K]$ and
$[K, K+M]$ have equal step sum `blockSteps s K = d = blockSteps (fun t => s (K + t)) M`.
Setting `P r = oddReturnP (orbit b_0 (blockSteps s r))` and `s' t = s (K + t)`:
`2 ^ d * P (K + M) + 3 ^ d * P 0 + renewalNumerator s K = (2 ^ d + 3 ^ d) * P K + renewalNumerator s' M`. -/
theorem allBlock_equal_stepSum_second_difference_identity
    {b_0 K M d : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + M))
    (hd1 : blockSteps s K = d)
    (hd2 : blockSteps (fun t => s (K + t)) M = d) :
    let P := fun r => oddReturnP (orbit b_0 (blockSteps s r))
    let s' := fun t => s (K + t)
    2 ^ d * P (K + M) + 3 ^ d * P 0 + renewalNumerator s K =
      (2 ^ d + 3 ^ d) * P K + renewalNumerator s' M := by
  intro P s'
  have hch1 : ValidBlockChain b_0 s u K := fun k hk => hchain k (by omega)
  have hch2 := validBlockChain_shift (r := K) (L := M) (le_refl (K + M)) hchain
  have hm1 := renewal_prefix_master_identity hch1
  have hm2 := renewal_prefix_master_identity hch2
  dsimp only at hm1 hm2
  have hshift := blockSteps_add_shift s K M
  rw [← orbit_add, ← hshift] at hm2
  change 2 ^ (blockSteps s K) * P K = 3 ^ (blockSteps s K) * P 0 + renewalNumerator s K at hm1
  change 2 ^ (blockSteps s' M) * P (K + M) = 3 ^ (blockSteps s' M) * P K + renewalNumerator s' M at hm2
  rw [hd1] at hm1
  rw [hd2] at hm2
  have hdist : (2 ^ d + 3 ^ d) * P K = 2 ^ d * P K + 3 ^ d * P K := by ring
  omega

/-! ## 2. Section C2.O2.2: Centered Renewal Slack $\widehat{\Sigma}_N = \Sigma_N - 2^{T_N}$ & Homogeneous Cocycle Law -/

/-- Centered renewal slack $\widehat{\Sigma}_N := \Sigma_N - 2^{T_N} = 3^{T_N} - 2^{T_N} - 2 A_{0,N} \in \mathbb{Z}$. -/
def centeredRenewalSlack (s : ℕ → ℕ) (N : ℕ) : ℤ :=
  renewalIntSlack s N - (2 : ℤ) ^ (blockSteps s N)

/-- **One-Step Recurrence & Homogeneous Multi-Step Cocycle Law for $\widehat{\Sigma}_N$
(`centeredRenewalSlack_step_and_cocycle`, Section C2.O2.2)**:
1. `centeredRenewalSlack s 0 = 0`,
2. `centeredRenewalSlack s N = (3 : ℤ) ^ (blockSteps s N) - (2 : ℤ) ^ (blockSteps s N) - 2 * (renewalNumerator s N : ℤ)`,
3. When `1 ≤ s N`,
   `centeredRenewalSlack s (N + 1) = (3 : ℤ) ^ (s N) * centeredRenewalSlack s N + 3 * (2 : ℤ) ^ (blockSteps s N) * ((3 : ℤ) ^ (s N - 1) - (2 : ℤ) ^ (s N))`, and
4. For all `K, M : ℕ`, setting `s' t = s (K + t)` and `d = blockSteps s' M`:
   `centeredRenewalSlack s (K + M) = (3 : ℤ) ^ d * centeredRenewalSlack s K + (2 : ℤ) ^ (blockSteps s K) * centeredRenewalSlack s' M`. -/
theorem centeredRenewalSlack_step_and_cocycle (s : ℕ → ℕ) (N K M : ℕ) :
    centeredRenewalSlack s 0 = 0 ∧
      centeredRenewalSlack s N =
        (3 : ℤ) ^ (blockSteps s N) - (2 : ℤ) ^ (blockSteps s N) -
          2 * (renewalNumerator s N : ℤ) ∧
      (1 ≤ s N →
        centeredRenewalSlack s (N + 1) =
          (3 : ℤ) ^ (s N) * centeredRenewalSlack s N +
            3 * (2 : ℤ) ^ (blockSteps s N) * ((3 : ℤ) ^ (s N - 1) - (2 : ℤ) ^ (s N))) ∧
      centeredRenewalSlack s (K + M) =
        (3 : ℤ) ^ (blockSteps (fun t => s (K + t)) M) * centeredRenewalSlack s K +
          (2 : ℤ) ^ (blockSteps s K) * centeredRenewalSlack (fun t => s (K + t)) M := by
  have hdef : ∀ m : ℕ,
      centeredRenewalSlack s m =
        (3 : ℤ) ^ (blockSteps s m) - (2 : ℤ) ^ (blockSteps s m) -
          2 * (renewalNumerator s m : ℤ) := by
    intro m
    unfold centeredRenewalSlack renewalIntSlack
    ring
  refine ⟨by simp [centeredRenewalSlack, renewalIntSlack, blockSteps, renewalNumerator], hdef N, ?_, ?_⟩
  · intro hsN
    rw [hdef (N + 1), hdef N]
    simp only [blockSteps, renewalNumerator, pow_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    have h3s : (3 : ℤ) ^ (s N) = 3 * (3 : ℤ) ^ (s N - 1) := by
      have hsub : s N = (s N - 1) + 1 := by omega
      conv_lhs => rw [hsub, pow_succ']
    rw [h3s]
    ring
  · have hcomp := renewalNumerator_cocycle_composition s K M
    have hshift := blockSteps_add_shift s K M
    unfold centeredRenewalSlack renewalIntSlack
    rw [hshift, hcomp]
    simp only [pow_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring

/-! ## 3. Section C2.O2.3: Sign of $\widehat{\Sigma}_N$ on $s_k \ge 3$ vs. $1 \le s_k \le 2$ Segments -/

/-- **Sign of $\widehat{\Sigma}_N$ on $s_k \ge 3$ vs. $1 \le s_k \le 2$ Segments
(`centeredRenewalSlack_nonneg_of_three_le_and_nonpos_of_le_two`, Section C2.O2.3)**:
1. If `∀ k < N, 3 ≤ s k`, then `0 ≤ centeredRenewalSlack s N` (`(2 : ℤ) ^ (blockSteps s N) ≤ renewalIntSlack s N`), and
2. If `∀ k < N, 1 ≤ s k ∧ s k ≤ 2`, then `centeredRenewalSlack s N ≤ 0` (`renewalIntSlack s N ≤ (2 : ℤ) ^ (blockSteps s N)`). -/
theorem centeredRenewalSlack_nonneg_of_three_le_and_nonpos_of_le_two (s : ℕ → ℕ) (N : ℕ) :
    ((∀ k < N, 3 ≤ s k) → 0 ≤ centeredRenewalSlack s N) ∧
      ((∀ k < N, 1 ≤ s k ∧ s k ≤ 2) → centeredRenewalSlack s N ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro hs3
    induction N with
    | zero => simp [centeredRenewalSlack, renewalIntSlack, blockSteps, renewalNumerator]
    | succ N ih =>
        have ih' := ih (fun k hk => hs3 k (by omega))
        have hsN : 3 ≤ s N := hs3 N (by omega)
        have hstep := (centeredRenewalSlack_step_and_cocycle s N 0 0).2.2.1 (by omega)
        have hloc_pos : (0 : ℤ) ≤ (3 : ℤ) ^ (s N - 1) - (2 : ℤ) ^ (s N) := by
          obtain ⟨m, hm⟩ : ∃ m : ℕ, s N = m + 3 := ⟨s N - 3, by omega⟩
          rw [hm]
          have hsub : m + 3 - 1 = m + 2 := by omega
          rw [hsub, pow_add (3 : ℤ) m 2, pow_add (2 : ℤ) m 3]
          have hpow : (2 : ℤ) ^ m ≤ (3 : ℤ) ^ m := by
            exact_mod_cast Nat.pow_le_pow_left (by decide) m
          have hpow_pos : (0 : ℤ) ≤ (2 : ℤ) ^ m := pow_nonneg (by decide) m
          omega
        have h3_nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ (s N) := pow_nonneg (by decide) _
        have h2_nonneg : (0 : ℤ) ≤ 3 * (2 : ℤ) ^ (blockSteps s N) := by positivity
        rw [hstep]
        exact add_nonneg (mul_nonneg h3_nonneg ih') (mul_nonneg h2_nonneg hloc_pos)
  · intro hs12
    induction N with
    | zero => simp [centeredRenewalSlack, renewalIntSlack, blockSteps, renewalNumerator]
    | succ N ih =>
        have ih' := ih (fun k hk => hs12 k (by omega))
        rcases hs12 N (by omega) with ⟨hs1, hs2⟩
        have hstep := (centeredRenewalSlack_step_and_cocycle s N 0 0).2.2.1 hs1
        have hloc_neg : (3 : ℤ) ^ (s N - 1) - (2 : ℤ) ^ (s N) ≤ 0 := by
          have hcases : s N = 1 ∨ s N = 2 := by omega
          rcases hcases with h | h <;> rw [h] <;> decide
        have h3_nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ (s N) := pow_nonneg (by decide) _
        have h2_nonneg : (0 : ℤ) ≤ 3 * (2 : ℤ) ^ (blockSteps s N) := by positivity
        rw [hstep]
        exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos h3_nonneg ih')
          (mul_nonpos_of_nonneg_of_nonpos h2_nonneg hloc_neg)

/-! ## 4. Section C2.O2.4: Kernel Identity $\widehat{\Sigma}_N = 3(3^{T_N} - 2^{T_N} - 2 K_N)$ & Mod-6 Non-Vanishing -/

/-- **Kernel Identity & Mod-6 Non-Vanishing Law for $\widehat{\Sigma}_N$
(`centeredRenewalSlack_eq_three_mul_and_mod_six_eq_three`, Section C2.O2.4)**:
For any valid block sequence (`∀ k < N, 1 ≤ s k`), setting `T_N = blockSteps s N`:
1. `centeredRenewalSlack s N = 3 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N - 2 * (blockKernel s N : ℤ))`, and
2. If `1 ≤ N`, then `centeredRenewalSlack s N % 6 = 3` and `centeredRenewalSlack s N ≠ 0`
   (`renewalIntSlack s N ≠ (2 : ℤ) ^ T_N`). -/
theorem centeredRenewalSlack_eq_three_mul_and_mod_six_eq_three {s : ℕ → ℕ} {N : ℕ}
    (hs : ∀ k < N, 1 ≤ s k) :
    let T_N := blockSteps s N
    centeredRenewalSlack s N =
      3 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N - 2 * (blockKernel s N : ℤ)) ∧
      (1 ≤ N →
        centeredRenewalSlack s N % 6 = 3 ∧
          centeredRenewalSlack s N ≠ 0 ∧
          renewalIntSlack s N ≠ (2 : ℤ) ^ T_N) := by
  intro T_N
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator hs
  change 3 * blockKernel s N = (3 ^ T_N - 2 ^ T_N) + renewalNumerator s N at hbridge
  have hle : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  have hbridge_z :
      3 * (blockKernel s N : ℤ) =
        (3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N + (renewalNumerator s N : ℤ) := by
    zify [hle] at hbridge
    exact_mod_cast hbridge
  have hdef := (centeredRenewalSlack_step_and_cocycle s N 0 0).2.1
  change centeredRenewalSlack s N =
    (3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N - 2 * (renewalNumerator s N : ℤ) at hdef
  have hid :
      centeredRenewalSlack s N =
        3 * ((3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N - 2 * (blockKernel s N : ℤ)) := by
    linarith [hdef, hbridge_z]
  refine ⟨hid, ?_⟩
  intro hN
  have hTN_pos : 1 ≤ T_N := blockSteps_pos hN hs
  have hodd3 : ∀ m : ℕ, 3 ^ m % 2 = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have h3_odd_z : ((3 : ℤ) ^ T_N) % 2 = 1 := by
    have hn : 3 ^ T_N % 2 = 1 := hodd3 T_N
    exact_mod_cast hn
  have h2_even_z : ((2 : ℤ) ^ T_N) % 2 = 0 := by
    have hsub : T_N = (T_N - 1) + 1 := by omega
    rw [hsub, pow_succ]
    omega
  have hmod6 : centeredRenewalSlack s N % 6 = 3 := by
    rw [hid]
    omega
  refine ⟨hmod6, by omega, ?_⟩
  unfold centeredRenewalSlack at hmod6
  change (renewalIntSlack s N - (2 : ℤ) ^ T_N) % 6 = 3 at hmod6
  omega

/-! ## 5. Section C2.O2.5: Closed Form $\widehat{\Sigma}_2(2, s_1) = 3^{s_1} - 12 \cdot 2^{s_1}$ & Uniqueness of $s_1 = 6$ -/

/-- **Closed Form $\widehat{\Sigma}_2(2, s_1) = 3^{s_1} - 12 \cdot 2^{s_1}$ & Uniqueness of the $s_1 = 6$ Sub-Ceiling Rung
(`two_block_centeredRenewalSlack_and_unique_subCeiling_rung_six`, Section C2.O2.5)**:
For any gap sequence `s` with `s 0 = 2`:
1. `centeredRenewalSlack s 2 = (3 : ℤ) ^ (s 1) - 12 * (2 : ℤ) ^ (s 1)`,
2. `renewalIntSlack s 2 ≤ 0 ↔ s 1 ≤ 5`,
3. `(0 < renewalIntSlack s 2 ∧ centeredRenewalSlack s 2 < 0) ↔ s 1 = 6`
   (with `centeredRenewalSlack s 2 = -39` at `s 1 = 6`), and
4. `0 < centeredRenewalSlack s 2 ↔ 7 ≤ s 1` (with `centeredRenewalSlack s 2 = 651` at `s 1 = 7`). -/
theorem two_block_centeredRenewalSlack_and_unique_subCeiling_rung_six
    {s : ℕ → ℕ} (hs0 : s 0 = 2) :
    centeredRenewalSlack s 2 = (3 : ℤ) ^ (s 1) - 12 * (2 : ℤ) ^ (s 1) ∧
      (renewalIntSlack s 2 ≤ 0 ↔ s 1 ≤ 5) ∧
      ((0 < renewalIntSlack s 2 ∧ centeredRenewalSlack s 2 < 0) ↔ s 1 = 6) ∧
      (0 < centeredRenewalSlack s 2 ↔ 7 ≤ s 1) ∧
      (s 1 = 6 → centeredRenewalSlack s 2 = -39) ∧
      (s 1 = 7 → centeredRenewalSlack s 2 = 651) := by
  rcases two_block_two_s1_renewalNumerator_and_slack hs0 with ⟨hT2, _, hS2⟩
  have hCS2 : centeredRenewalSlack s 2 = (3 : ℤ) ^ (s 1) - 12 * (2 : ℤ) ^ (s 1) := by
    unfold centeredRenewalSlack
    rw [hS2, hT2, pow_add (2 : ℤ) 2 (s 1)]
    ring
  have hpow7 : ∀ m : ℕ, 12 * 2 ^ (m + 7) < 3 ^ (m + 7) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 12 * 2 ^ (m + 1 + 7) = 2 * (12 * 2 ^ (m + 7)) := by
          rw [show m + 1 + 7 = (m + 7) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 3 ^ (m + 1 + 7) = 3 * 3 ^ (m + 7) := by
          rw [show m + 1 + 7 = (m + 7) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow6_le : ∀ n : ℕ, n ≤ 6 → ((3 : ℤ) ^ n - 12 * (2 : ℤ) ^ n) < 0 := by
    intro n hn
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · omega
  have hesc_iff := (two_block_two_s1_escape_iff_s1_le_five hs0).1
  have hslack_nonpos_iff :
      renewalIntSlack s 2 ≤ 0 ↔ s 1 ≤ 5 := by
    rw [← hesc_iff]
    unfold renewalIntSlack
    have hcast : (3 : ℤ) ^ (blockSteps s 2) = ((3 ^ (blockSteps s 2) : ℕ) : ℤ) := by norm_cast
    rw [hcast]
    omega
  have hpos_iff_ge7 : 0 < centeredRenewalSlack s 2 ↔ 7 ≤ s 1 := by
    rw [hCS2]
    constructor
    · intro hpos
      by_contra hnot
      have hle6 : s 1 ≤ 6 := by omega
      have hlt := hpow6_le (s 1) hle6
      linarith
    · intro hge7
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 1 = m + 7 := ⟨s 1 - 7, by omega⟩
      have hlt : (12 : ℤ) * (2 : ℤ) ^ (s 1) < (3 : ℤ) ^ (s 1) := by
        rw [hm]
        exact_mod_cast hpow7 m
      linarith
  have hsub_iff_eq6 :
      (0 < renewalIntSlack s 2 ∧ centeredRenewalSlack s 2 < 0) ↔ s 1 = 6 := by
    constructor
    · rintro ⟨hS_pos, hCS_neg⟩
      have hgt5 : ¬ (s 1 ≤ 5) := by
        intro hle5
        have hnp := hslack_nonpos_iff.mpr hle5
        linarith
      have hlt7 : ¬ (7 ≤ s 1) := by
        intro hge7
        have hp := hpos_iff_ge7.mpr hge7
        linarith
      omega
    · intro hs6
      have hS_pos : 0 < renewalIntSlack s 2 := by
        rw [hS2, hs6]
        norm_num
      have hCS_neg : centeredRenewalSlack s 2 < 0 := by
        rw [hCS2, hs6]
        norm_num
      exact ⟨hS_pos, hCS_neg⟩
  refine ⟨hCS2, hslack_nonpos_iff, hsub_iff_eq6, hpos_iff_ge7, ?_, ?_⟩
  · intro hs6; rw [hCS2, hs6]; norm_num
  · intro hs7; rw [hCS2, hs7]; norm_num

end Mahler.CenteredRenewalSlack
