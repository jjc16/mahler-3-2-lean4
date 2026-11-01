import SixBlockKneadingEscapeAndFiftyMillionBound

/-!
# Resolution of the Strict Endpoint Question ($h_0 = 1/2$), the Exact Identity $\Sigma_{0,N} = 3^{T_N}(1 - 2 h_0) + 2^{T_N+1} h_N$, and Bounded-Slack Exclusion

This module formalizes **Outer Loop 8 / 10 (Part XII, Sections O8.1–O8.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`, resolving **Question 6 of Section A8.2**:

1. **Section O8.1 (Inner Loop 1 / 3) — Multi-Block Renewal-Tail Identity & Slack Decomposition
   (`multi_block_renewalTail_and_slack_identity`)**:
   - Across any valid `N`-block chain (`ValidBlockChain b_0 s u N`) with $T_N = \operatorname{blockSteps} s N$:
     - `(2 : ℝ) ^ T_N * renewalTail b_0 α T_N = (3 : ℝ) ^ T_N * renewalTail b_0 α 0 - (renewalNumerator s N : ℝ)`,
     - `(renewalIntSlack s N : ℝ) = (3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) + (2 : ℝ) ^ (T_N + 1) * renewalTail b_0 α T_N`, and
     - When `renewalTail b_0 α 0 = 1 / 2`, `renewalTail b_0 α T_N = (renewalIntSlack s N : ℝ) / (2 : ℝ) ^ (T_N + 1)`.

2. **Section O8.2 (Inner Loop 2 / 3) — Complete Resolution of Question 6: Asymptotic Endpoint $\lim A_{0,N}/3^{T_N} = 1/2$
   (`validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound`,
   `asymptotic_endpoint_slack_ratio_zero_excludes_companion_forever`)**:
   - Whenever `ValidCompanionUpTo b_0 α (T_N + 1)` holds along a valid `N`-block chain (`N ≥ 1`),
     the terminal odd boundary `orbit b_0 T_N` is odd, so survival through step `T_N + 1` forces
     `0 ≤ renewalTail b_0 α T_N` while `renewalTail b_0 α 0 < 1 / 2` ($\delta_0 := 1 - 2 h_0(\alpha) > 0$).
   - Consequently, for every $N \ge 1$:
     `(3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) ≤ (renewalIntSlack s N : ℝ)` and
     `(renewalNumerator s N : ℝ) / (3 : ℝ) ^ T_N ≤ renewalTail b_0 α 0 < 1 / 2`.
   - **Resolution of Question 6:** If for every $\varepsilon > 0$ there exists $N \ge 1$ with
     `ValidBlockChain b_0 s u N` and `(renewalIntSlack s N : ℝ) < ε * (3 : ℝ) ^ T_N`
     (i.e. $\inf_N \Sigma_{0,N} / 3^{T_N} \le 0$, which includes the limiting endpoint case
     $\lim_{N\to\infty} A_{0,N} / 3^{T_N} = 1/2$ where all finite partial sums stay $< 1/2$),
     then **no real $\alpha$ can satisfy `ValidCompanionForever b_0 α`**!

3. **Section O8.3 (Inner Loop 3 / 3) — Unconditional Exclusion of Bounded Renewal Slack $\Sigma_{0,N} \le M$
   (`no_bounded_renewalIntSlack_for_validCompanionForever`)**:
   - Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`), if `ValidCompanionForever b_0 α`
     holds, then $(1 - 2 h_0(\alpha)) \cdot 3^N \le \Sigma_{0,N}$ for all $N \ge 1$, so $\Sigma_{0,N}$
     cannot remain bounded above by any constant $M \in \mathbb{Z}$.
-/

namespace Mahler.StrictEndpointAndSlackGrowth

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

/-! ## 1. Section O8.1: Multi-Block Renewal-Tail Identity & Slack Decomposition -/

/-- **Multi-Block Renewal-Tail Identity & Slack Decomposition
(`multi_block_renewalTail_and_slack_identity`, Section O8.1)**:
Across any valid `N`-block chain (`ValidBlockChain b_0 s u N`) and any real `α : ℝ`, setting
`T_N = blockSteps s N`:
1. `(2 : ℝ) ^ T_N * renewalTail b_0 α T_N = (3 : ℝ) ^ T_N * renewalTail b_0 α 0 - (renewalNumerator s N : ℝ)`,
2. `(renewalIntSlack s N : ℝ) = (3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) + (2 : ℝ) ^ (T_N + 1) * renewalTail b_0 α T_N`, and
3. If `renewalTail b_0 α 0 = 1 / 2`, then
   `renewalTail b_0 α T_N = (renewalIntSlack s N : ℝ) / (2 : ℝ) ^ (T_N + 1)`. -/
theorem multi_block_renewalTail_and_slack_identity
    {b_0 N : ℕ} {s u : ℕ → ℕ} (hchain : ValidBlockChain b_0 s u N) (α : ℝ) :
    let T_N := blockSteps s N
    (2 : ℝ) ^ T_N * renewalTail b_0 α T_N =
      (3 : ℝ) ^ T_N * renewalTail b_0 α 0 - (renewalNumerator s N : ℝ) ∧
      (renewalIntSlack s N : ℝ) =
        (3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) +
          (2 : ℝ) ^ (T_N + 1) * renewalTail b_0 α T_N ∧
      (renewalTail b_0 α 0 = 1 / 2 →
        renewalTail b_0 α T_N = (renewalIntSlack s N : ℝ) / (2 : ℝ) ^ (T_N + 1)) := by
  intro T_N
  have hf_id := mixed_block_fracPart_identity hchain α
  change (2 : ℝ) ^ T_N * fracPart b_0 α T_N =
    (3 : ℝ) ^ T_N * fracPart b_0 α 0 - (blockKernel s N : ℝ) at hf_id
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator
    (fun k hk => (hchain k hk).1)
  change 3 * blockKernel s N = (3 ^ T_N - 2 ^ T_N) + renewalNumerator s N at hbridge
  have hle : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  have hbridge_r :
      3 * (blockKernel s N : ℝ) =
        (3 : ℝ) ^ T_N - (2 : ℝ) ^ T_N + (renewalNumerator s N : ℝ) := by
    zify [hle] at hbridge
    exact_mod_cast hbridge
  have htail_id :
      (2 : ℝ) ^ T_N * renewalTail b_0 α T_N =
        (3 : ℝ) ^ T_N * renewalTail b_0 α 0 - (renewalNumerator s N : ℝ) := by
    unfold renewalTail
    linarith [hf_id, hbridge_r]
  have hslack_id :
      (renewalIntSlack s N : ℝ) =
        (3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) +
          (2 : ℝ) ^ (T_N + 1) * renewalTail b_0 α T_N := by
    unfold renewalIntSlack
    dsimp only [T_N] at htail_id ⊢
    push_cast
    rw [pow_succ]
    linarith [htail_id]
  refine ⟨htail_id, hslack_id, ?_⟩
  intro hh0
  have h2_ne : (2 : ℝ) ^ (T_N + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hslack_id, hh0, eq_div_iff h2_ne]
  ring

/-! ## 2. Section O8.2: Resolution of Question 6 (Asymptotic Endpoint $\lim A_{0,N}/3^{T_N} = 1/2$) -/

/-- **Exponential Lower Bound on $\Sigma_{0,N}$ Along Valid Companions
(`validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound`, Section O8.2)**:
Whenever `1 ≤ N`, `ValidBlockChain b_0 s u N`, and `ValidCompanionUpTo b_0 α (blockSteps s N + 1)`:
1. `renewalTail b_0 α 0 < 1 / 2` (so `0 < 1 - 2 * renewalTail b_0 α 0`),
2. `0 ≤ renewalTail b_0 α (blockSteps s N)`,
3. `(3 : ℝ) ^ (blockSteps s N) * (1 - 2 * renewalTail b_0 α 0) ≤ (renewalIntSlack s N : ℝ)`, and
4. `(renewalNumerator s N : ℝ) / (3 : ℝ) ^ (blockSteps s N) ≤ renewalTail b_0 α 0`. -/
theorem validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound
    {b_0 N : ℕ} {s u : ℕ → ℕ} {α : ℝ}
    (hN : 1 ≤ N) (hchain : ValidBlockChain b_0 s u N)
    (hsurv : ValidCompanionUpTo b_0 α (blockSteps s N + 1)) :
    let T_N := blockSteps s N
    renewalTail b_0 α 0 < 1 / 2 ∧
      0 < 1 - 2 * renewalTail b_0 α 0 ∧
      0 ≤ renewalTail b_0 α T_N ∧
      (3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) ≤ (renewalIntSlack s N : ℝ) ∧
      (renewalNumerator s N : ℝ) / (3 : ℝ) ^ T_N ≤ renewalTail b_0 α 0 := by
  intro T_N
  have h0 : ValidCompanionAt b_0 α 0 := hsurv 0 (by omega)
  have hTN : ValidCompanionAt b_0 α T_N := hsurv T_N (by omega)
  have hTN1 : ValidCompanionAt b_0 α (T_N + 1) := hsurv (T_N + 1) (by omega)
  have hf0 := (validCompanionAt_iff_fracPart b_0 α 0).mp h0
  have hfTN1 := (validCompanionAt_iff_fracPart b_0 α (T_N + 1)).mp hTN1
  have hodd_TN : orbit b_0 T_N % 2 = 1 := mixed_block_return_odd hN hchain
  have hsucc_TN := fracPart_succ b_0 α T_N
  rw [hodd_TN] at hsucc_TN
  simp only [Nat.cast_one] at hsucc_TN
  have hh0_lt : renewalTail b_0 α 0 < 1 / 2 := by
    unfold renewalTail
    linarith [hf0.2]
  have hhTN_nonneg : 0 ≤ renewalTail b_0 α T_N := by
    unfold renewalTail
    linarith [hfTN1.1, hsucc_TN]
  rcases multi_block_renewalTail_and_slack_identity hchain α with ⟨htail_id, hslack_id, _⟩
  change (2 : ℝ) ^ T_N * renewalTail b_0 α T_N =
    (3 : ℝ) ^ T_N * renewalTail b_0 α 0 - (renewalNumerator s N : ℝ) at htail_id
  change (renewalIntSlack s N : ℝ) =
    (3 : ℝ) ^ T_N * (1 - 2 * renewalTail b_0 α 0) +
      (2 : ℝ) ^ (T_N + 1) * renewalTail b_0 α T_N at hslack_id
  have h2_pos : (0 : ℝ) ≤ (2 : ℝ) ^ (T_N + 1) := pow_nonneg (by norm_num) _
  have h2T_pos : (0 : ℝ) ≤ (2 : ℝ) ^ T_N := pow_nonneg (by norm_num) _
  have hprod_nonneg : 0 ≤ (2 : ℝ) ^ (T_N + 1) * renewalTail b_0 α T_N :=
    mul_nonneg h2_pos hhTN_nonneg
  have hprodT_nonneg : 0 ≤ (2 : ℝ) ^ T_N * renewalTail b_0 α T_N :=
    mul_nonneg h2T_pos hhTN_nonneg
  have h3_pos : (0 : ℝ) < (3 : ℝ) ^ T_N := pow_pos (by norm_num) T_N
  have hdiv_le : (renewalNumerator s N : ℝ) / (3 : ℝ) ^ T_N ≤ renewalTail b_0 α 0 := by
    rw [div_le_iff₀ h3_pos]
    linarith [htail_id, hprodT_nonneg]
  exact ⟨hh0_lt, by linarith, hhTN_nonneg, by linarith [hslack_id, hprod_nonneg], hdiv_le⟩

/-- **Complete Resolution of Section A8.2 Question 6 (`asymptotic_endpoint_slack_ratio_zero_excludes_companion_forever`,
Section O8.2)**:
If a block trajectory (`∀ N, ValidBlockChain b_0 s u N`) satisfies
`∀ ε > 0, ∃ N ≥ 1, (renewalIntSlack s N : ℝ) < ε * (3 : ℝ) ^ (blockSteps s N)`
(which holds whenever $\lim_{N\to\infty} A_{0,N} / 3^{T_N} = 1/2$, even if $2 A_{0,N} < 3^{T_N}$
for every finite $N$), then **no real $\alpha$ can satisfy `ValidCompanionForever b_0 α`**! -/
theorem asymptotic_endpoint_slack_ratio_zero_excludes_companion_forever
    {b_0 : ℕ} {s u : ℕ → ℕ}
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N)
    (hlim : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ (renewalIntSlack s N : ℝ) < ε * (3 : ℝ) ^ (blockSteps s N)) :
    ∀ α : ℝ, ¬ ValidCompanionForever b_0 α := by
  intro α hforever
  have hsurv1 : ValidCompanionUpTo b_0 α (blockSteps s 1 + 1) :=
    (validCompanionForever_iff_forall_upTo b_0 α).mp hforever (blockSteps s 1 + 1)
  have hpos_delta :=
    (validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound
      (by decide : 1 ≤ 1) (hchain 1) hsurv1).2.1
  rcases hlim (1 - 2 * renewalTail b_0 α 0) hpos_delta with ⟨N, hN, hlt⟩
  have hsurvN : ValidCompanionUpTo b_0 α (blockSteps s N + 1) :=
    (validCompanionForever_iff_forall_upTo b_0 α).mp hforever (blockSteps s N + 1)
  have hge :=
    (validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound hN (hchain N) hsurvN).2.2.2.1
  change (3 : ℝ) ^ (blockSteps s N) * (1 - 2 * renewalTail b_0 α 0) ≤
    (renewalIntSlack s N : ℝ) at hge
  linarith

/-! ## 3. Section O8.3: Unconditional Exclusion of Bounded Renewal Slack $\Sigma_{0,N} \le M$ -/

/-- For any valid block chain (`∀ k < N, 1 ≤ s k`), `N ≤ blockSteps s N`. -/
theorem id_le_blockSteps {s : ℕ → ℕ} {N : ℕ} (hs : ∀ k < N, 1 ≤ s k) :
    N ≤ blockSteps s N := by
  induction N with
  | zero => simp [blockSteps]
  | succ N ih =>
      have ih' := ih (fun k hk => hs k (by omega))
      have hsN := hs N (by omega)
      simp only [blockSteps]
      omega

/-- **Unconditional Exclusion of Bounded Integer Renewal Slack
(`no_bounded_renewalIntSlack_for_validCompanionForever`, Section O8.3)**:
Along any infinite valid block chain (`∀ N, ValidBlockChain b_0 s u N`), if `ValidCompanionForever b_0 α`
holds, then `renewalIntSlack s N` grows exponentially and cannot satisfy `renewalIntSlack s N ≤ M`
for all `N : ℕ`. -/
theorem no_bounded_renewalIntSlack_for_validCompanionForever
    {b_0 : ℕ} {s u : ℕ → ℕ} {α : ℝ} (M : ℤ)
    (hchain : ∀ N : ℕ, ValidBlockChain b_0 s u N)
    (hforever : ValidCompanionForever b_0 α) :
    ¬ (∀ N : ℕ, renewalIntSlack s N ≤ M) := by
  intro hbounded
  apply asymptotic_endpoint_slack_ratio_zero_excludes_companion_forever hchain _ α hforever
  intro ε hε
  have hsurv1 : ValidCompanionUpTo b_0 α (blockSteps s 1 + 1) :=
    (validCompanionForever_iff_forall_upTo b_0 α).mp hforever (blockSteps s 1 + 1)
  have h1_pos : (0 : ℝ) < (renewalIntSlack s 1 : ℝ) := by
    have hb := validCompanionUpTo_imp_renewalIntSlack_exponential_lower_bound
      (by decide : 1 ≤ 1) (hchain 1) hsurv1
    have h3_pos : (0 : ℝ) < (3 : ℝ) ^ (blockSteps s 1) := pow_pos (by norm_num) _
    have hmul_pos : 0 < (3 : ℝ) ^ (blockSteps s 1) * (1 - 2 * renewalTail b_0 α 0) :=
      mul_pos h3_pos hb.2.1
    linarith [hb.2.2.2.1]
  have hM_pos : (0 : ℝ) < (M : ℝ) := by
    have hle1 : (renewalIntSlack s 1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hbounded 1
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ((M : ℝ) / ε) < (K : ℝ) := exists_nat_gt ((M : ℝ) / ε)
  refine ⟨K + 1, by omega, ?_⟩
  have hN_le_T : K + 1 ≤ blockSteps s (K + 1) :=
    id_le_blockSteps (fun k hk => (hchain (K + 1) k hk).1)
  have hpow_gt : ∀ n : ℕ, (n : ℝ) < (3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        push_cast
        rw [pow_succ]
        have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        linarith
  have hK_lt_pow : (K : ℝ) < (3 : ℝ) ^ (blockSteps s (K + 1)) := by
    have h1 : (K : ℝ) < ((K + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : ((K + 1 : ℕ) : ℝ) < (3 : ℝ) ^ (K + 1) := hpow_gt (K + 1)
    have h3 : (3 : ℝ) ^ (K + 1) ≤ (3 : ℝ) ^ (blockSteps s (K + 1)) :=
      pow_le_pow_right₀ (by norm_num) hN_le_T
    linarith
  have hM_lt : (M : ℝ) < ε * (3 : ℝ) ^ (blockSteps s (K + 1)) := by
    have hm1 := (div_lt_iff₀ hε).mp hK
    have hm2 := mul_lt_mul_of_pos_left hK_lt_pow hε
    linarith
  have hle_M : (renewalIntSlack s (K + 1) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hbounded (K + 1)
  linarith

end Mahler.StrictEndpointAndSlackGrowth
