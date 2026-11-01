import AllRungConstantOfMotionAndDualRemainder

/-!
# Archimedean Constant of Motion $L$, Exact Companion Bridge, All-Block Renewal System & Finite Escape Certificates

This module formalizes **Part II Sections F2 & F3** and **Part III Sections A0.3, A1.3, A2, A3, and A4**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Sections F2 & A1.3 — Normalized Boundary Sequence, Real Constant of Motion $L$, and Strict $1/27$ Pinning
   (`normalizedBoundarySeq_strictAnti_and_lower_bound`, `exists_archimedean_constant_of_motion`,
   `pinning_ceil_identity`, `fract_pinning_gt_twentySix_twentySevenths`, `fract_pinning_ge`,
   `boundary_val2_mod_three_zero`, `archimedean_two_adic_coincidence`, `coupling_val_determined_by_L`)**:
   - The real sequence $g_K = (2/3)^{S_K} W_K$ is strictly decreasing (`StrictAnti`) and bounded below
     by $W_0 - 1/27$.
   - Its greatest lower bound $L = \inf_K g_K \in [W_0 - 1/27, W_0)$ satisfies the **strict $1/27$
     pinning law** for every $K \ge 0$:
     $$0 < W_K - L\,(3/2)^{S_K} < \frac{1}{27} < \frac{3}{65},$$
     forcing $\lceil L(3/2)^{S_K}\rceil = W_K$, $\{L(3/2)^{S_K}\} > 26/27 > 62/65$, and
     $v_2(W_K) = 3 j_K \equiv 0 \pmod 3$.

2. **Sections A2 & A0.3 — Exact Companion Bridge $L = \frac{19}{72}\alpha(3/2)^{t_0}$ & Scale-24 Static Countermodel
   (`pinning_error_eq_boundary_fraction_affine`, `sharp_pinning_iff_boundary_fraction_window`,
   `normalized_boundary_limit_eq_scaled_companion`, `static_pinning_and_valuation_do_not_supply_orbit_clock`)**:
   - Proves that when $19 b_r + 9 = 72 W_r$ and $f_r = \alpha(3/2)^{t_0 + S_r} - b_r$, setting
     $L = \frac{19}{72}\alpha(3/2)^{t_0}$ gives $W_r - L(3/2)^{S_r} = \frac{9 - 19 f_r}{72}$, so
     $0 < W_r - L(3/2)^{S_r} < 1/27 \iff 1/3 < f_r < 9/19$.
   - Formalizes the scale-24 countermodel showing that static pinning + valuation + mod-19 boundary
     integrality do not supply the actual first-return orbit clock ($b_0 = 117$ has $s_0 = 5 \ne 24$).

3. **Section A3 — All-Block Renewal System $P_r = 3 b_r + 1$, Two-Prime Transport & Companion Equivalence
   (`oddReturnP_recurrence`, `oddReturnP_strictMono`, `oddReturnP_three_adic_transport`,
   `three_mul_blockKernel_eq_pow_diff_add_renewalNumerator`, `renewal_normalized_prefix_identity`,
   `renewalTail_recurrence`, `renewalTail_lt_half_iff_validCompanion_on_block`,
   `even_seed_reaches_odd_boundary`, `minimum_gap_three_real_feasibility_and_ghost`)**:
   - At every odd boundary $b_r$ ($s_r \ge 1$, including short $s_r = 2$ recovery blocks),
     $P_r = 3 b_r + 1$ satisfies $2^{s_r} P_{r+1} = 3^{s_r} P_r + 2^{s_r}$, with exact 2-to-3 transport
     $v_3(P_{r+1} - 1) = s_r = v_2(P_r)$ and $(P_{r+1} - 1)/3^{s_r} = P_r / 2^{s_r} = Q_r$.
   - Proves the fundamental kernel-renewal bridge
     `3 * blockKernel s N = (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) + renewalNumerator s N`.
   - Proves both directions of the renewal-tail companion characterization across every odd block
     (including all intermediate even steps $1 \le v \le s_r$), plus the initial even-run shift bridge
     and the $s_r = 3$ rational ghost control ($P_* = -8/19, b_* = -9/19, h_* = 8/19 < 1/2$).

4. **Section A4 — Finite Renewal Escape Certificate $2 A_{0,N} \ge 3^{T_N}$, Rational Cap Engine & Extra-Bit Lock
   (`finite_renewal_escape_certificate`, `seed_137_two_five_escape_certificate`,
   `recoveryCap_two_six_three_three_two_cascade`, `extra_bit_prefix_compatibility_and_counterexample`)**:
   - Proves that $2 A_{0,N} \ge 3^{T_N}$ (in fact $2 A_{0,N} > 3^{T_N}$ by parity) is equivalent to
     violating `mixed_block_return_pinch`, hence unconditionally excludes `ValidCompanionUpTo b_0 α (T_N + 1)`
     and `ValidCompanionForever b_0 α`.
   - Certifies the genuine seed-137 $(2, 5)$ escape ($2 A = 2200 > 2187 = 3^7$), the exact rational
     recovery-cap cascade for $(2, 6, 3, 3, 2)$, and the extra-bit prefix compatibility criterion
     $3^{T_N} P_0 + A_{0,N} \equiv 0 \pmod{2^{T_N + 1}}$ with the $P_0 = 4, s = 1$ counterexample.
-/

namespace Mahler.ArchimedeanPinningAndRenewal

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection
open Mahler.BetaShiftDictionary
open Mahler.GeneralizedDefectAllRung
open Mahler.BoundedOddPartAndSieve
open Mahler.AllRungConstantOfMotion

/-! ## 1. Sections F2 & A1.3: Normalized Boundary Sequence, Real Limit $L$ & Strict $1/27$ Pinning -/

/-- Normalized real boundary sequence $g_K = (2/3)^{S_K} W_K$. -/
noncomputable def normalizedBoundarySeq (W j s : ℕ → ℕ) (K : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ (allRungStepSum j s K) * (W K : ℝ)

/-- Exact single-step decrease of `normalizedBoundarySeq` and cumulative identity
`g 0 - g K = allRungDefectAcc j s K / 3 ^ S_K`. -/
theorem normalizedBoundarySeq_step_and_prefix {W j s : ℕ → ℕ}
    (hrec : ∀ r : ℕ,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    (∀ K : ℕ,
      let S_K : ℕ := allRungStepSum j s K
      let a_K : ℕ := 3 * j K + s K
      let u_K : ℕ := 2 ^ (3 * j K) * (3 ^ (s K - 3) - 2 ^ (s K - 3))
      normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s (K + 1) =
        (2 / 3 : ℝ) ^ S_K * ((u_K : ℝ) / (3 : ℝ) ^ a_K)) ∧
      (∀ K : ℕ,
        let S_K := allRungStepSum j s K
        (W 0 : ℝ) - normalizedBoundarySeq W j s K =
          (allRungDefectAcc j s K : ℝ) / (3 : ℝ) ^ S_K) := by
  refine ⟨?_, ?_⟩
  · intro K S_K a_K u_K
    have hstep :
        (2 : ℝ) ^ a_K * (W (K + 1) : ℝ) + (u_K : ℝ) = (3 : ℝ) ^ a_K * (W K : ℝ) := by
      have hnat : 2 ^ a_K * W (K + 1) + u_K = 3 ^ a_K * W K := hrec K
      exact_mod_cast hnat
    have h3_ne : (3 : ℝ) ^ a_K ≠ 0 := pow_ne_zero a_K (by norm_num)
    have hdiv :
        (W K : ℝ) - (2 / 3 : ℝ) ^ a_K * (W (K + 1) : ℝ) = (u_K : ℝ) / (3 : ℝ) ^ a_K := by
      rw [div_pow, eq_div_iff h3_ne]
      have hring :
          ((W K : ℝ) - (2 : ℝ) ^ a_K / (3 : ℝ) ^ a_K * (W (K + 1) : ℝ)) * (3 : ℝ) ^ a_K =
            (3 : ℝ) ^ a_K * (W K : ℝ) - (2 : ℝ) ^ a_K / (3 : ℝ) ^ a_K * (3 : ℝ) ^ a_K * (W (K + 1) : ℝ) := by
        ring
      rw [hring, div_mul_cancel₀ _ h3_ne]
      linarith
    unfold normalizedBoundarySeq
    have hS : allRungStepSum j s (K + 1) = S_K + a_K := rfl
    rw [hS, pow_add]
    calc
      (2 / 3 : ℝ) ^ S_K * (W K : ℝ) -
          (2 / 3 : ℝ) ^ S_K * (2 / 3 : ℝ) ^ a_K * (W (K + 1) : ℝ)
        = (2 / 3 : ℝ) ^ S_K * ((W K : ℝ) - (2 / 3 : ℝ) ^ a_K * (W (K + 1) : ℝ)) := by ring
      _ = (2 / 3 : ℝ) ^ S_K * ((u_K : ℝ) / (3 : ℝ) ^ a_K) := by rw [hdiv]
  · intro K S_K
    have hm :
        (2 : ℝ) ^ S_K * (W K : ℝ) + (allRungDefectAcc j s K : ℝ) =
          (3 : ℝ) ^ S_K * (W 0 : ℝ) := by
      have hnat : 2 ^ S_K * W K + allRungDefectAcc j s K = 3 ^ S_K * W 0 :=
        allRung_single_exponent_master_identity (K := K) (fun r _ => hrec r)
      exact_mod_cast hnat
    have h3_ne : (3 : ℝ) ^ S_K ≠ 0 := pow_ne_zero S_K (by norm_num)
    unfold normalizedBoundarySeq
    change (W 0 : ℝ) - (2 / 3 : ℝ) ^ S_K * (W K : ℝ) =
      (allRungDefectAcc j s K : ℝ) / (3 : ℝ) ^ S_K
    rw [div_pow, eq_div_iff h3_ne]
    have hring :
        ((W 0 : ℝ) - (2 : ℝ) ^ S_K / (3 : ℝ) ^ S_K * (W K : ℝ)) * (3 : ℝ) ^ S_K =
          (3 : ℝ) ^ S_K * (W 0 : ℝ) - (2 : ℝ) ^ S_K / (3 : ℝ) ^ S_K * (3 : ℝ) ^ S_K * (W K : ℝ) := by
      ring
    rw [hring, div_mul_cancel₀ _ h3_ne]
    linarith

/-- **Strict Antitonicity and Uniform Two-Index Real Squeeze (`normalizedBoundarySeq_strictAnti_and_lower_bound`,
Sections F2.1 & A1.3)**:
Whenever `∀ r, 4 ≤ s r` and `W` satisfies the single-exponent recurrence:
1. `StrictAnti (normalizedBoundarySeq W j s)`,
2. For all `K < M`, setting `S_K = allRungStepSum j s K` and `S_M = allRungStepSum j s M`:
   `0 < normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M` and
   `normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M < (1 / 27 : ℝ) * ((2 / 3 : ℝ) ^ S_K - (2 / 3 : ℝ) ^ S_M)`, and
3. For all `K`, `(W 0 : ℝ) - 1 / 27 < normalizedBoundarySeq W j s K` and
   `normalizedBoundarySeq W j s K ≤ (W 0 : ℝ)`. -/
theorem normalizedBoundarySeq_strictAnti_and_lower_bound {W j s : ℕ → ℕ}
    (hs : ∀ r : ℕ, 4 ≤ s r)
    (hrec : ∀ r : ℕ,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    StrictAnti (normalizedBoundarySeq W j s) ∧
      (∀ K M : ℕ, K < M →
        let S_K := allRungStepSum j s K
        let S_M := allRungStepSum j s M
        0 < normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M ∧
          normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M <
            (1 / 27 : ℝ) * ((2 / 3 : ℝ) ^ S_K - (2 / 3 : ℝ) ^ S_M)) ∧
      (∀ K : ℕ,
        (W 0 : ℝ) - 1 / 27 < normalizedBoundarySeq W j s K ∧
          normalizedBoundarySeq W j s K ≤ (W 0 : ℝ)) := by
  have htwo_idx :
      ∀ K M : ℕ, K < M →
        0 < normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M ∧
          normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M <
            (1 / 27 : ℝ) *
              ((2 / 3 : ℝ) ^ (allRungStepSum j s K) - (2 / 3 : ℝ) ^ (allRungStepSum j s M)) := by
    intro K M hKM
    set S_K := allRungStepSum j s K
    set S_M := allRungStepSum j s M
    have hgap := allRung_tailGap_twentySeven_strict_bound hKM (fun r _ => hs r) (fun r _ => hrec r)
    set j' := fun t => j (K + t)
    set s' := fun t => s (K + t)
    set d := S_M - S_K
    set G := allRungDefectAcc j' s' (M - K)
    change 2 ^ d * W M + G = 3 ^ d * W K ∧ _ at hgap
    have hM_eq : K + (M - K) = M := by omega
    have hshift := allRungStepSum_add_shift j s K (M - K)
    rw [hM_eq] at hshift
    have hd_add : S_K + d = S_M := by
      change S_K + (S_M - S_K) = S_M
      have hle : S_K ≤ S_M := by
        change allRungStepSum j s K ≤ allRungStepSum j s M
        rw [hshift]
        omega
      omega
    have hm_real : (2 : ℝ) ^ d * (W M : ℝ) + (G : ℝ) = (3 : ℝ) ^ d * (W K : ℝ) := by
      exact_mod_cast hgap.1
    have hG_pos : (0 : ℝ) < (G : ℝ) := by
      have : 1 ≤ G := hgap.2.2.1
      exact_mod_cast (by omega : 0 < G)
    have h27G : 27 * (G : ℝ) < (3 : ℝ) ^ d - (2 : ℝ) ^ d := by
      have hle_pow : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
      have hnat : 27 * G < 3 ^ d - 2 ^ d := hgap.2.2.2.1
      zify [hle_pow] at hnat
      exact_mod_cast hnat
    have h3d_pos : (0 : ℝ) < (3 : ℝ) ^ d := pow_pos (by norm_num) d
    have h3d_ne : (3 : ℝ) ^ d ≠ 0 := ne_of_gt h3d_pos
    have hqK_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ S_K := pow_pos (by norm_num) S_K
    have hdiff_eq :
        normalizedBoundarySeq W j s K - normalizedBoundarySeq W j s M =
          (2 / 3 : ℝ) ^ S_K * ((G : ℝ) / (3 : ℝ) ^ d) := by
      unfold normalizedBoundarySeq
      change (2 / 3 : ℝ) ^ S_K * (W K : ℝ) - (2 / 3 : ℝ) ^ S_M * (W M : ℝ) = _
      rw [← hd_add, pow_add]
      have h1 : (W K : ℝ) - (2 / 3 : ℝ) ^ d * (W M : ℝ) = (G : ℝ) / (3 : ℝ) ^ d := by
        rw [div_pow, eq_div_iff h3d_ne]
        have hring :
            ((W K : ℝ) - (2 : ℝ) ^ d / (3 : ℝ) ^ d * (W M : ℝ)) * (3 : ℝ) ^ d =
              (3 : ℝ) ^ d * (W K : ℝ) - (2 : ℝ) ^ d / (3 : ℝ) ^ d * (3 : ℝ) ^ d * (W M : ℝ) := by
          ring
        rw [hring, div_mul_cancel₀ _ h3d_ne]
        linarith
      calc
        (2 / 3 : ℝ) ^ S_K * (W K : ℝ) - (2 / 3 : ℝ) ^ S_K * (2 / 3 : ℝ) ^ d * (W M : ℝ) =
            (2 / 3 : ℝ) ^ S_K * ((W K : ℝ) - (2 / 3 : ℝ) ^ d * (W M : ℝ)) := by ring
        _ = (2 / 3 : ℝ) ^ S_K * ((G : ℝ) / (3 : ℝ) ^ d) := by rw [h1]
    rw [hdiff_eq]
    refine ⟨mul_pos hqK_pos (div_pos hG_pos h3d_pos), ?_⟩
    have hdiv_lt : (G : ℝ) / (3 : ℝ) ^ d < (1 / 27 : ℝ) * (1 - (2 / 3 : ℝ) ^ d) := by
      rw [div_pow, div_lt_iff₀ h3d_pos]
      have hring :
          (1 / 27 : ℝ) * (1 - (2 : ℝ) ^ d / (3 : ℝ) ^ d) * (3 : ℝ) ^ d =
            (1 / 27 : ℝ) * ((3 : ℝ) ^ d - (2 : ℝ) ^ d) := by
        calc
          (1 / 27 : ℝ) * (1 - (2 : ℝ) ^ d / (3 : ℝ) ^ d) * (3 : ℝ) ^ d =
              (1 / 27 : ℝ) * ((3 : ℝ) ^ d - (2 : ℝ) ^ d / (3 : ℝ) ^ d * (3 : ℝ) ^ d) := by ring
          _ = (1 / 27 : ℝ) * ((3 : ℝ) ^ d - (2 : ℝ) ^ d) := by rw [div_mul_cancel₀ _ h3d_ne]
      rw [hring]
      linarith
    have hmul_lt := mul_lt_mul_of_pos_left hdiv_lt hqK_pos
    have hq_expand :
        (2 / 3 : ℝ) ^ S_K * ((1 / 27 : ℝ) * (1 - (2 / 3 : ℝ) ^ d)) =
          (1 / 27 : ℝ) * ((2 / 3 : ℝ) ^ S_K - (2 / 3 : ℝ) ^ S_M) := by
      rw [← hd_add, pow_add]
      ring
    linarith
  have hanti : StrictAnti (normalizedBoundarySeq W j s) := by
    intro K M hKM
    have h := (htwo_idx K M hKM).1
    linarith
  refine ⟨hanti, fun K M hKM => htwo_idx K M hKM, ?_⟩
  intro K
  cases K with
  | zero =>
      unfold normalizedBoundarySeq allRungStepSum
      simp only [pow_zero, one_mul, le_refl, and_true]
      linarith
  | succ K =>
      have h0 := htwo_idx 0 (K + 1) (by omega)
      have hg0 : normalizedBoundarySeq W j s 0 = (W 0 : ℝ) := by
        unfold normalizedBoundarySeq allRungStepSum
        ring
      have hS0 : (2 / 3 : ℝ) ^ (allRungStepSum j s 0) = 1 := by
        change (2 / 3 : ℝ) ^ 0 = 1
        ring
      have hq_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (allRungStepSum j s (K + 1)) :=
        pow_pos (by norm_num) _
      rw [hg0, hS0] at h0
      constructor <;> linarith

/-- **Existence of the Archimedean Constant of Motion $L$ with Strict $1/27$ Pinning
(`exists_archimedean_constant_of_motion`, Sections F2.2, F2.5 & A1.3)**:
For any infinite all-long chain (`∀ r, 4 ≤ s r`) satisfying the single-exponent recurrence,
there exists a real constant $L \in \mathbb{R}$ (explicitly $L = \inf_K (2/3)^{S_K} W_K$) such that:
1. `(W 0 : ℝ) - 1 / 27 < L` and `L < (W 0 : ℝ)` (and `(W 0 : ℝ) - 1 ≤ L`), and
2. For every `K : ℕ`:
   `0 < (W K : ℝ) - L * (3 / 2 : ℝ) ^ (allRungStepSum j s K)`,
   `(W K : ℝ) - L * (3 / 2 : ℝ) ^ (allRungStepSum j s K) < 1 / 27`, and
   `(W K : ℝ) - L * (3 / 2 : ℝ) ^ (allRungStepSum j s K) ≤ 3 / 65`. -/
theorem exists_archimedean_constant_of_motion {W j s : ℕ → ℕ}
    (hs : ∀ r : ℕ, 4 ≤ s r)
    (hrec : ∀ r : ℕ,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    ∃ L : ℝ,
      ((W 0 : ℝ) - 1 ≤ L ∧ (W 0 : ℝ) - 1 / 27 < L ∧ L < (W 0 : ℝ)) ∧
        ∀ K : ℕ,
          let S_K := allRungStepSum j s K
          0 < (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K ∧
            (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K < 1 / 27 ∧
            (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K ≤ 3 / 65 := by
  have hmain := normalizedBoundarySeq_strictAnti_and_lower_bound hs hrec
  rcases hmain with ⟨hanti, htwo_idx, hbounds0⟩
  set g := normalizedBoundarySeq W j s
  set L := sInf (Set.range g)
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨(W 0 : ℝ) - 1 / 27, ?_⟩
    rintro _ ⟨K, rfl⟩
    exact le_of_lt (hbounds0 K).1
  have hGLB : IsGLB (Set.range g) L := Real.isGLB_sInf (Set.range_nonempty g) hbdd
  have hL_le : ∀ K : ℕ, L ≤ g K := fun K => hGLB.1 ⟨K, rfl⟩
  have h_weak : ∀ K : ℕ, g K - (1 / 27 : ℝ) * (2 / 3 : ℝ) ^ (allRungStepSum j s K) ≤ L := by
    intro K
    refine hGLB.2 ?_
    rintro _ ⟨M, rfl⟩
    rcases lt_trichotomy M K with hMK | rfl | hKM
    · have hle : g K ≤ g M := le_of_lt (hanti hMK)
      have hq_pos : (0 : ℝ) ≤ (1 / 27 : ℝ) * (2 / 3 : ℝ) ^ (allRungStepSum j s K) := by
        positivity
      linarith
    · have hq_pos : (0 : ℝ) ≤ (1 / 27 : ℝ) * (2 / 3 : ℝ) ^ (allRungStepSum j s M) := by
        positivity
      linarith
    · have hlt := (htwo_idx K M hKM).2
      have hqM_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (allRungStepSum j s M) :=
        pow_pos (by norm_num) _
      linarith
  have h_strict_g :
      ∀ K : ℕ,
        0 < g K - L ∧
          g K - L < (1 / 27 : ℝ) * (2 / 3 : ℝ) ^ (allRungStepSum j s K) := by
    intro K
    have hstep_lt := htwo_idx K (K + 1) (by omega)
    dsimp only at hstep_lt
    have hL_K1 : L ≤ g (K + 1) := hL_le (K + 1)
    have hweak_K1 := h_weak (K + 1)
    constructor <;> linarith
  refine ⟨L, ?_, ?_⟩
  · have h0 := h_strict_g 0
    have hg0 : g 0 = (W 0 : ℝ) := by
      change (2 / 3 : ℝ) ^ 0 * (W 0 : ℝ) = (W 0 : ℝ)
      ring
    have hS0 : allRungStepSum j s 0 = 0 := rfl
    rw [hg0, hS0, pow_zero] at h0
    refine ⟨by linarith, by linarith, by linarith⟩
  · intro K S_K
    have hK := h_strict_g K
    have h32_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ S_K := pow_pos (by norm_num) S_K
    have hmul_id :
        ((W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K) = (3 / 2 : ℝ) ^ S_K * (g K - L) := by
      change (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K =
        (3 / 2 : ℝ) ^ S_K * ((2 / 3 : ℝ) ^ S_K * (W K : ℝ) - L)
      have hcancel : (3 / 2 : ℝ) ^ S_K * (2 / 3 : ℝ) ^ S_K = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K =
            ((3 / 2 : ℝ) ^ S_K * (2 / 3 : ℝ) ^ S_K) * (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K := by
          rw [hcancel, one_mul]
        _ = (3 / 2 : ℝ) ^ S_K * ((2 / 3 : ℝ) ^ S_K * (W K : ℝ) - L) := by ring
    have hcancel2 :
        (3 / 2 : ℝ) ^ S_K * ((1 / 27 : ℝ) * (2 / 3 : ℝ) ^ S_K) = 1 / 27 := by
      have hc : (3 / 2 : ℝ) ^ S_K * (2 / 3 : ℝ) ^ S_K = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (3 / 2 : ℝ) ^ S_K * ((1 / 27 : ℝ) * (2 / 3 : ℝ) ^ S_K) =
            (1 / 27 : ℝ) * ((3 / 2 : ℝ) ^ S_K * (2 / 3 : ℝ) ^ S_K) := by ring
        _ = 1 / 27 := by rw [hc, mul_one]
    rw [hmul_id]
    have hpos : 0 < (3 / 2 : ℝ) ^ S_K * (g K - L) := mul_pos h32_pos hK.1
    have hlt27 : (3 / 2 : ℝ) ^ S_K * (g K - L) < 1 / 27 := by
      have hm := mul_lt_mul_of_pos_left hK.2 h32_pos
      linarith
    exact ⟨hpos, hlt27, by linarith⟩

/-- **Ceiling Identity, Fractional-Part Pinning & 2-Adic Valuation Coupling
(`pinning_ceil_and_fract_and_val2_coincidence`, Sections F2.4, F2.5 & A1.3)**:
Whenever `0 < (W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K` and `(W K : ℝ) - L * (3 / 2 : ℝ) ^ S_K < 1 / 27`:
1. `⌈L * (3 / 2 : ℝ) ^ S_K⌉ = (W K : ℤ)` (`pinning_ceil_identity`),
2. `⌊L * (3 / 2 : ℝ) ^ S_K⌋ = (W K : ℤ) - 1`,
3. `26 / 27 < Int.fract (L * (3 / 2 : ℝ) ^ S_K)` and `62 / 65 ≤ Int.fract (L * (3 / 2 : ℝ) ^ S_K)`
   (`fract_pinning_ge`), and
4. if `W K = 2 ^ (3 * j K) * V K` with `V K % 2 = 1`, then `(W K).factorization 2 = 3 * j K` and
   `(W K).factorization 2 % 3 = 0` (`boundary_val2_mod_three_zero`). -/
theorem pinning_ceil_and_fract_and_val2_coincidence {W S_K j_K V_K : ℕ} {L : ℝ}
    (hpos : 0 < (W : ℝ) - L * (3 / 2 : ℝ) ^ S_K)
    (hlt : (W : ℝ) - L * (3 / 2 : ℝ) ^ S_K < 1 / 27) :
    let x := L * (3 / 2 : ℝ) ^ S_K
    ⌈x⌉ = (W : ℤ) ∧
      ⌊x⌋ = (W : ℤ) - 1 ∧
      (26 / 27 : ℝ) < Int.fract x ∧
      (62 / 65 : ℝ) ≤ Int.fract x ∧
      (W = 2 ^ (3 * j_K) * V_K → V_K % 2 = 1 →
        W.factorization 2 = 3 * j_K ∧ W.factorization 2 % 3 = 0) := by
  intro x
  change 0 < (W : ℝ) - x at hpos
  change (W : ℝ) - x < 1 / 27 at hlt
  have hceil : ⌈x⌉ = (W : ℤ) := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith
  have hfloor : ⌊x⌋ = (W : ℤ) - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hfract_eq : Int.fract x = x - ((W : ℝ) - 1) := by
    rw [Int.fract, hfloor]
    push_cast
    ring
  refine ⟨hceil, hfloor, by linarith, by linarith, ?_⟩
  intro hW_eq hV_odd
  have hV_ne : V_K ≠ 0 := by omega
  have h2_ne : (2 : ℕ) ^ (3 * j_K) ≠ 0 := pow_ne_zero (3 * j_K) (by decide)
  have hnot_dvd : ¬ (2 ∣ V_K) := by omega
  have hfact : W.factorization 2 = 3 * j_K := by
    rw [hW_eq, Nat.factorization_mul h2_ne hV_ne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hnot_dvd, Nat.add_zero]
  exact ⟨hfact, by rw [hfact]; omega⟩

/-- **Valuation Coupling Determined by $L$ (`coupling_val_determined_by_L`, Section F3)**:
Whenever `⌈L * (3 / 2 : ℝ) ^ S_r⌉ = (W_r : ℤ)`, `W_r = 2 ^ (3 * j_r) * V_r`, and
`2 ^ (ν_next + s_r - 3) * V_next = 3 ^ (3 * j_r + s_r) * V_r - (3 ^ (s_r - 3) - 2 ^ (s_r - 3))`
with `1 ≤ V_next` and `V_next % 2 = 1`, the 2-adic valuation of the transition term
`X_r = 3 ^ (3 * j_r + s_r) * (⌈L * (3 / 2 : ℝ) ^ S_r⌉.toNat / 2 ^ (3 * j_r)) - (3 ^ (s_r - 3) - 2 ^ (s_r - 3))`
is identically `ν_next + s_r - 3`. -/
theorem coupling_val_determined_by_L {W_r j_r V_r s_r S_r ν_next V_next : ℕ} {L : ℝ}
    (hceil : ⌈L * (3 / 2 : ℝ) ^ S_r⌉ = (W_r : ℤ))
    (hW : W_r = 2 ^ (3 * j_r) * V_r)
    (hX : 2 ^ (ν_next + s_r - 3) * V_next =
      3 ^ (3 * j_r + s_r) * V_r - (3 ^ (s_r - 3) - 2 ^ (s_r - 3)))
    (hV_next_odd : V_next % 2 = 1) :
    let X_r :=
      3 ^ (3 * j_r + s_r) * (⌈L * (3 / 2 : ℝ) ^ S_r⌉.toNat / 2 ^ (3 * j_r)) -
        (3 ^ (s_r - 3) - 2 ^ (s_r - 3))
    X_r = 2 ^ (ν_next + s_r - 3) * V_next ∧
      X_r.factorization 2 = ν_next + s_r - 3 := by
  intro X_r
  have htoNat : ⌈L * (3 / 2 : ℝ) ^ S_r⌉.toNat = W_r := by
    rw [hceil, Int.toNat_natCast]
  have hdiv : W_r / 2 ^ (3 * j_r) = V_r := by
    rw [hW, Nat.mul_div_right V_r (Nat.pow_pos (by decide))]
  have hX_eq : X_r = 2 ^ (ν_next + s_r - 3) * V_next := by
    dsimp [X_r]
    rw [htoNat, hdiv, ← hX]
  have h2_ne : (2 : ℕ) ^ (ν_next + s_r - 3) ≠ 0 := pow_ne_zero _ (by decide)
  have hV_ne : V_next ≠ 0 := by omega
  have hnot_dvd : ¬ (2 ∣ V_next) := by omega
  refine ⟨hX_eq, ?_⟩
  rw [hX_eq, Nat.factorization_mul h2_ne hV_ne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hnot_dvd, Nat.add_zero]

/-! ## 2. Sections A2 & A0.3: Exact Companion Bridge $L = \frac{19}{72}\alpha(3/2)^{t_0}$ & Scale-24 Static Countermodel -/

/-- **Exact Affine Pinning-Error Conversion (`pinning_error_eq_boundary_fraction_affine`, Section A2)**:
If `19 * (b_r : ℝ) + 9 = 72 * (W_r : ℝ)`, `f_r = α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ)`, and
`L = (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0`, then:
`(W_r : ℝ) - L * (3 / 2 : ℝ) ^ S_r = (9 - 19 * f_r) / 72`. -/
theorem pinning_error_eq_boundary_fraction_affine {b_r W_r t_0 S_r : ℕ} {α : ℝ}
    (haff : 19 * (b_r : ℝ) + 9 = 72 * (W_r : ℝ)) :
    let f_r := α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ)
    let L := (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0
    (W_r : ℝ) - L * (3 / 2 : ℝ) ^ S_r = (9 - 19 * f_r) / 72 := by
  intro f_r L
  dsimp [f_r, L]
  rw [pow_add]
  linarith

/-- **Equivalence Between Sharp $1/27$ Pinning and $1/3 < f_r < 9/19$
(`sharp_pinning_iff_boundary_fraction_window`, Section A2)**:
Under `19 * (b_r : ℝ) + 9 = 72 * (W_r : ℝ)`, the sharp pinning window
`0 < (W_r : ℝ) - L * (3 / 2 : ℝ) ^ S_r < 1 / 27` holds if and only if
`1 / 3 < f_r ∧ f_r < 9 / 19`. -/
theorem sharp_pinning_iff_boundary_fraction_window {b_r W_r t_0 S_r : ℕ} {α : ℝ}
    (haff : 19 * (b_r : ℝ) + 9 = 72 * (W_r : ℝ)) :
    let f_r := α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ)
    let L := (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0
    let ε_r := (W_r : ℝ) - L * (3 / 2 : ℝ) ^ S_r
    (0 < ε_r ∧ ε_r < 1 / 27) ↔ (1 / 3 < f_r ∧ f_r < 9 / 19) := by
  intro f_r L ε_r
  have hid := pinning_error_eq_boundary_fraction_affine (t_0 := t_0) (S_r := S_r) (α := α) haff
  change ε_r = (9 - 19 * f_r) / 72 at hid
  rw [hid]
  constructor <;> intro h <;> constructor <;> linarith

/-- **Quantitative Convergence of $(2/3)^{S_r} W_r$ to $\frac{19}{72}\alpha(3/2)^{t_0}$
(`normalized_boundary_limit_eq_scaled_companion`, Section A2)**:
Whenever `19 * (b_r : ℝ) + 9 = 72 * (W_r : ℝ)` and `0 ≤ f_r ∧ f_r < 1 / 2`:
`|(2 / 3 : ℝ) ^ S_r * (W_r : ℝ) - (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0| ≤ (1 / 8 : ℝ) * (2 / 3 : ℝ) ^ S_r`. -/
theorem normalized_boundary_limit_eq_scaled_companion {b_r W_r t_0 S_r : ℕ} {α : ℝ}
    (haff : 19 * (b_r : ℝ) + 9 = 72 * (W_r : ℝ))
    (hf0 : 0 ≤ α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ))
    (hf1 : α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ) < 1 / 2) :
    |(2 / 3 : ℝ) ^ S_r * (W_r : ℝ) - (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0| ≤
      (1 / 8 : ℝ) * (2 / 3 : ℝ) ^ S_r := by
  have hid :
      (W_r : ℝ) - ((19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0) * (3 / 2 : ℝ) ^ S_r =
        (9 - 19 * (α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ))) / 72 :=
    pinning_error_eq_boundary_fraction_affine (t_0 := t_0) (S_r := S_r) (α := α) haff
  have hcancel : (2 / 3 : ℝ) ^ S_r * (3 / 2 : ℝ) ^ S_r = 1 := by
    rw [← mul_pow]
    norm_num
  have hdiff :
      (2 / 3 : ℝ) ^ S_r * (W_r : ℝ) - (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0 =
        (2 / 3 : ℝ) ^ S_r * ((9 - 19 * (α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ))) / 72) := by
    calc
      (2 / 3 : ℝ) ^ S_r * (W_r : ℝ) - (19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0 =
          (2 / 3 : ℝ) ^ S_r * (W_r : ℝ) -
            ((19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0) * ((2 / 3 : ℝ) ^ S_r * (3 / 2 : ℝ) ^ S_r) := by
        rw [hcancel, mul_one]
      _ = (2 / 3 : ℝ) ^ S_r *
            ((W_r : ℝ) - ((19 / 72 : ℝ) * α * (3 / 2 : ℝ) ^ t_0) * (3 / 2 : ℝ) ^ S_r) := by
        ring
      _ = (2 / 3 : ℝ) ^ S_r * ((9 - 19 * (α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ))) / 72) := by
        rw [hid]
  have hq_nonneg : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ S_r := pow_nonneg (by norm_num) S_r
  have habs_bound :
      |(9 - 19 * (α * (3 / 2 : ℝ) ^ (t_0 + S_r) - (b_r : ℝ))) / 72| ≤ 1 / 8 := by
    rw [abs_le]
    constructor <;> linarith
  rw [hdiff, abs_mul, abs_of_nonneg hq_nonneg, mul_comm (1 / 8 : ℝ)]
  exact mul_le_mul_of_nonneg_left habs_bound hq_nonneg

/-- **Scale-24 Countermodel to Static Pinning Without the First-Return Clock
(`static_pinning_and_valuation_do_not_supply_orbit_clock`, Section A0.3)**:
1. The scale-24 interval length $\ell = 1/125$ expands by $(3/2)^{24} \ell > 114 + \ell$, so every
   parent interval $114 m_r + [a, b]$ ($a = 30 + 26/27 + 1/125$, $b = a + 1/125$) has image
   containing a full child interval $114 m_{r+1} + [a, b]$.
2. Every integer $W_r = 114 m_r + 31$ satisfies $W_r \bmod 2 = 1$ ($v_2(W_r) = 0 \equiv 0 \pmod 3$),
   $W_r \bmod 3 = 1$, $W_r \bmod 19 = 12$, and $19(432 m_r + 117) + 9 = 72(114 m_r + 31)$.
3. However, at the initial state $m_0 = 0$ ($W_0 = 31$, $b_0 = 117$), $3 \cdot 117 + 1 = 352 = 2^5 \cdot 11$,
   so the genuine first odd-return length is $s_0 = 5 \ne 24$. -/
theorem static_pinning_and_valuation_do_not_supply_orbit_clock (m : ℕ) :
    ((3 / 2 : ℚ) ^ 24 * (1 / 125) > 114 + 1 / 125 ∧
      (30 + 26 / 27 : ℚ) < 30 + 26 / 27 + 1 / 125 ∧
      (30 + 26 / 27 + 1 / 125 + 1 / 125 : ℚ) < 31) ∧
      ((114 * m + 31) % 2 = 1 ∧
        (114 * m + 31) % 3 = 1 ∧
        (114 * m + 31) % 19 = 12 ∧
        19 * (432 * m + 117) + 9 = 72 * (114 * m + 31)) ∧
      (3 * 117 + 1 = 2 ^ 5 * 11 ∧ (3 * 117 + 1).factorization 2 = 5 ∧ 5 ≠ 24) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by omega, by omega, by omega, by ring⟩, ?_⟩
  refine ⟨by decide, ?_, by decide⟩
  have h352 : 3 * 117 + 1 = 2 ^ 5 * 11 := by decide
  rw [h352, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide), Nat.add_zero]

/-! ## 3. Section A3: All-Block Renewal System $P_r = 3 b_r + 1$, Two-Prime Transport & Companion Equivalence -/

/-- All-block return coordinate $P(b) = 3 b + 1$. -/
def oddReturnP (b : ℕ) : ℕ :=
  3 * b + 1

/-- Finite renewal numerator $A_{0,N} = \sum_{i=1}^N 2^{T_i} 3^{T_N - T_i}$ defined recursively. -/
def renewalNumerator (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 3 ^ (s N) * renewalNumerator s N + 2 ^ (blockSteps s (N + 1))

/-- **All-Block Integer Recurrence & Strict Growth of $P_r = 3 b_r + 1$
(`oddReturnP_recurrence`, `oddReturnP_strictMono`, Section A3.1)**:
Across any odd-to-odd block of length `1 ≤ s` with `3 * b + 1 = 2 ^ s * u` (`b' = orbit b s`):
1. `oddReturnP b' = 3 ^ s * u + 1`,
2. `2 ^ s * oddReturnP b' = 3 ^ s * oddReturnP b + 2 ^ s`, and
3. `oddReturnP b < oddReturnP b'`. -/
theorem oddReturnP_recurrence_and_strictMono {b s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * b + 1 = 2 ^ s * u) :
    let b' := orbit b s
    oddReturnP b' = 3 ^ s * u + 1 ∧
      2 ^ s * oddReturnP b' = 3 ^ s * oddReturnP b + 2 ^ s ∧
      oddReturnP b < oddReturnP b' := by
  intro b'
  have hret : b' = 3 ^ (s - 1) * u := orbit_odd_block_return hs hdecomp
  have h3s : 3 * 3 ^ (s - 1) = 3 ^ s := by
    have hsub : s = (s - 1) + 1 := by omega
    conv_rhs => rw [hsub, Nat.pow_succ']
  have hP' : oddReturnP b' = 3 ^ s * u + 1 := by
    unfold oddReturnP
    rw [hret, ← mul_assoc, h3s]
  have hlin : 2 ^ s * oddReturnP b' = 3 ^ s * oddReturnP b + 2 ^ s := by
    rw [hP']
    unfold oddReturnP
    calc
      2 ^ s * (3 ^ s * u + 1) = 3 ^ s * (2 ^ s * u) + 2 ^ s := by ring
      _ = 3 ^ s * (3 * b + 1) + 2 ^ s := by rw [← hdecomp]
  have hu_pos : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · omega
    · exact hpos
  have hlt : oddReturnP b < oddReturnP b' := by
    rw [hP']
    unfold oddReturnP
    rw [hdecomp]
    have hpow : 2 ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by decide) s
    have hmul : 2 ^ s * u ≤ 3 ^ s * u := Nat.mul_le_mul_right u hpow
    omega
  exact ⟨hP', hlin, hlt⟩

/-- **Exact Two-Prime Transport Identity (`oddReturnP_three_adic_transport`, Section A3.5)**:
Across any odd-to-odd block `3 * b + 1 = 2 ^ s * u` (`1 ≤ s`, `u % 2 = 1`, `b' = orbit b s`):
1. `oddReturnP b' - 1 = 3 ^ s * u`,
2. `3 ^ s ∣ (oddReturnP b' - 1)` and `¬ (3 ^ (s + 1) ∣ (oddReturnP b' - 1))`,
3. `(oddReturnP b' - 1) / 3 ^ s = oddReturnP b / 2 ^ s = u`, and
4. `oddReturnP b = 2 ^ s * ((oddReturnP b' - 1) / 3 ^ s)`. -/
theorem oddReturnP_three_adic_transport {b s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * b + 1 = 2 ^ s * u) :
    let b' := orbit b s
    oddReturnP b' - 1 = 3 ^ s * u ∧
      (3 ^ s ∣ (oddReturnP b' - 1)) ∧
      ¬ (3 ^ (s + 1) ∣ (oddReturnP b' - 1)) ∧
      (oddReturnP b' - 1) / 3 ^ s = u ∧
      oddReturnP b / 2 ^ s = u ∧
      oddReturnP b = 2 ^ s * ((oddReturnP b' - 1) / 3 ^ s) := by
  intro b'
  have hP := (oddReturnP_recurrence_and_strictMono hs hdecomp).1
  change oddReturnP b' = 3 ^ s * u + 1 at hP
  have hsub : oddReturnP b' - 1 = 3 ^ s * u := by omega
  have hnot3 : ¬ (3 ∣ u) := not_three_dvd_odd_part hdecomp
  have hdvd : 3 ^ s ∣ (oddReturnP b' - 1) := ⟨u, hsub⟩
  have hndvd : ¬ (3 ^ (s + 1) ∣ (oddReturnP b' - 1)) := by
    rw [hsub]
    rintro ⟨q, hq⟩
    have hpow : 3 ^ (s + 1) * q = 3 ^ s * (3 * q) := by
      rw [Nat.pow_succ]
      ring
    rw [hpow] at hq
    have hu_eq : u = 3 * q := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hq
    exact hnot3 ⟨q, hu_eq⟩
  have hdiv3 : (oddReturnP b' - 1) / 3 ^ s = u := by
    rw [hsub, Nat.mul_div_right u (Nat.pow_pos (by decide))]
  have hdiv2 : oddReturnP b / 2 ^ s = u := by
    unfold oddReturnP
    rw [hdecomp, Nat.mul_div_right u (Nat.pow_pos (by decide))]
  refine ⟨hsub, hdvd, hndvd, hdiv3, hdiv2, ?_⟩
  rw [hdiv3]
  exact hdecomp

/-- **Fundamental Kernel–Renewal Bridge (`three_mul_blockKernel_eq_pow_diff_add_renewalNumerator`,
Sections A3.2 & A4.1)**:
For every block-length sequence `s : ℕ → ℕ` and horizon `N : ℕ` with `∀ k < N, 1 ≤ s k`:
`3 * blockKernel s N = (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) + renewalNumerator s N`. -/
theorem three_mul_blockKernel_eq_pow_diff_add_renewalNumerator {s : ℕ → ℕ} {N : ℕ}
    (hs : ∀ k < N, 1 ≤ s k) :
    3 * blockKernel s N =
      (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) + renewalNumerator s N := by
  induction N with
  | zero => simp [blockKernel, blockSteps, renewalNumerator]
  | succ N ih =>
      have ih' := ih (fun k hk => hs k (by omega))
      have hsN : 1 ≤ s N := hs N (by omega)
      set T := blockSteps s N
      set K := blockKernel s N
      set A := renewalNumerator s N
      have h3_split : 3 * 3 ^ (s N - 1) = 3 ^ (s N) := by
        have hsub : s N = (s N - 1) + 1 := by omega
        conv_rhs => rw [hsub, Nat.pow_succ']
      have hK_step : 3 * blockKernel s (N + 1) = 3 ^ (s N) * (3 * K) + 2 ^ T * 3 ^ (s N) := by
        simp only [blockKernel, T, K]
        calc
          3 * (3 ^ (s N) * K + 2 ^ T * 3 ^ (s N - 1)) =
              3 ^ (s N) * (3 * K) + 2 ^ T * (3 * 3 ^ (s N - 1)) := by ring
          _ = 3 ^ (s N) * (3 * K) + 2 ^ T * 3 ^ (s N) := by rw [h3_split]
      have hA_step : renewalNumerator s (N + 1) = 3 ^ (s N) * A + 2 ^ T * 2 ^ (s N) := by
        simp only [renewalNumerator, blockSteps, T, A, Nat.pow_add]
      have hT_le : 2 ^ T ≤ 3 ^ T := Nat.pow_le_pow_left (by decide) T
      have hTs_le : 2 ^ (T + s N) ≤ 3 ^ (T + s N) := Nat.pow_le_pow_left (by decide) (T + s N)
      rw [hK_step, ih', hA_step]
      change 3 ^ (s N) * (3 ^ T - 2 ^ T + A) + 2 ^ T * 3 ^ (s N) =
        (3 ^ (T + s N) - 2 ^ (T + s N)) + (3 ^ (s N) * A + 2 ^ T * 2 ^ (s N))
      zify [hT_le, hTs_le]
      simp only [pow_add]
      ring

/-- **Multi-Block Renewal Integer Master Identity (`renewal_prefix_master_identity`, Sections A3.2 & A4.1)**:
Across any valid `N`-block chain from `b_0`, setting `T_N = blockSteps s N`:
`2 ^ T_N * oddReturnP (orbit b_0 T_N) = 3 ^ T_N * oddReturnP b_0 + renewalNumerator s N`. -/
theorem renewal_prefix_master_identity {b_0 : ℕ} {s u : ℕ → ℕ} {N : ℕ}
    (hchain : ValidBlockChain b_0 s u N) :
    let T_N := blockSteps s N
    2 ^ T_N * oddReturnP (orbit b_0 T_N) =
      3 ^ T_N * oddReturnP b_0 + renewalNumerator s N := by
  intro T_N
  have hid := mixed_block_integer_identity hchain
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator
    (fun k hk => (hchain k hk).1)
  change 2 ^ T_N * orbit b_0 T_N = 3 ^ T_N * b_0 + blockKernel s N at hid
  change 3 * blockKernel s N = (3 ^ T_N - 2 ^ T_N) + renewalNumerator s N at hbridge
  have hT_le : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  unfold oddReturnP
  change 2 ^ T_N * (3 * orbit b_0 T_N + 1) = 3 ^ T_N * (3 * b_0 + 1) + renewalNumerator s N
  have hdist1 : 2 ^ T_N * (3 * orbit b_0 T_N + 1) = 3 * (2 ^ T_N * orbit b_0 T_N) + 2 ^ T_N := by ring
  have hdist2 : 3 ^ T_N * (3 * b_0 + 1) = 3 * (3 ^ T_N * b_0) + 3 ^ T_N := by ring
  have hmul3 : 3 * (2 ^ T_N * orbit b_0 T_N) = 3 * (3 ^ T_N * b_0) + 3 * blockKernel s N := by
    rw [hid]
    ring
  rw [hbridge] at hmul3
  omega

/-- Normalized prefix identity in $\mathbb{R}$ (`renewal_normalized_prefix_identity`, Section A3.2):
`(2 / 3 : ℝ) ^ T_N * oddReturnP (orbit b_0 T_N) = oddReturnP b_0 + renewalNumerator s N / 3 ^ T_N`. -/
theorem renewal_normalized_prefix_identity {b_0 : ℕ} {s u : ℕ → ℕ} {N : ℕ}
    (hchain : ValidBlockChain b_0 s u N) :
    let T_N := blockSteps s N
    (2 / 3 : ℝ) ^ T_N * (oddReturnP (orbit b_0 T_N) : ℝ) =
      (oddReturnP b_0 : ℝ) + (renewalNumerator s N : ℝ) / (3 : ℝ) ^ T_N := by
  intro T_N
  have hm :
      (2 : ℝ) ^ T_N * (oddReturnP (orbit b_0 T_N) : ℝ) =
        (3 : ℝ) ^ T_N * (oddReturnP b_0 : ℝ) + (renewalNumerator s N : ℝ) := by
    have hnat : 2 ^ T_N * oddReturnP (orbit b_0 T_N) = 3 ^ T_N * oddReturnP b_0 + renewalNumerator s N :=
      renewal_prefix_master_identity hchain
    exact_mod_cast hnat
  have h3_ne : (3 : ℝ) ^ T_N ≠ 0 := pow_ne_zero T_N (by norm_num)
  rw [div_pow, add_div', eq_div_iff h3_ne]
  · have hring :
        (2 : ℝ) ^ T_N / (3 : ℝ) ^ T_N * (oddReturnP (orbit b_0 T_N) : ℝ) * (3 : ℝ) ^ T_N =
          (2 : ℝ) ^ T_N / (3 : ℝ) ^ T_N * (3 : ℝ) ^ T_N * (oddReturnP (orbit b_0 T_N) : ℝ) := by
      ring
    rw [hring, div_mul_cancel₀ _ h3_ne]
    linarith
  · exact h3_ne

/-- Renewal tail $h(b, \alpha, n) := 3 \operatorname{fracPart}(b, \alpha, n) - 1 = 3 \alpha (3/2)^n - (3 \operatorname{orbit}(b, n) + 1)$. -/
noncomputable def renewalTail (b : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  3 * fracPart b α n - 1

/-- **Renewal Tail Recurrence & Companion Equivalence Across a Single Odd Block
(`renewalTail_recurrence_and_block_companion_iff`, Sections A3.2 & A3.3)**:
Suppose `3 * b + 1 = 2 ^ s * u` (`1 ≤ s`, `u % 2 = 1`). Set `h_0 = renewalTail b α 0` and
`h_1 = renewalTail b α s`. Then:
1. `h_1 = (3 / 2 : ℝ) ^ s * h_0 - 1` and `h_0 = (2 / 3 : ℝ) ^ s * (1 + h_1)`,
2. For every intermediate step `1 ≤ v ≤ s`,
   `fracPart b α v = (2 / 3 : ℝ) ^ (s - v) * ((1 + h_1) / 3)`, and
3. `(∀ v ≤ s, ValidCompanionAt b α v) ∧ 0 ≤ h_1` holds **if and only if**
   `0 ≤ h_0 ∧ h_0 < 1 / 2 ∧ 0 ≤ h_1 ∧ h_1 < 1 / 2`
   (and when `0 < h_1 < 1 / 2` and `h_0 < 1 / 2`, `0 < h_0` is automatic and every step `v ≤ s`
   satisfies `ValidCompanionAt b α v`). -/
theorem renewalTail_recurrence_and_block_companion_iff {b s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * b + 1 = 2 ^ s * u) (α : ℝ) :
    let h_0 := renewalTail b α 0
    let h_1 := renewalTail b α s
    (h_1 = (3 / 2 : ℝ) ^ s * h_0 - 1 ∧ h_0 = (2 / 3 : ℝ) ^ s * (1 + h_1)) ∧
      (∀ v : ℕ, 1 ≤ v → v ≤ s →
        fracPart b α v = (2 / 3 : ℝ) ^ (s - v) * ((1 + h_1) / 3)) ∧
      (0 < h_1 → h_1 < 1 / 2 → h_0 < 1 / 2 →
        0 < h_0 ∧ ∀ v ≤ s, ValidCompanionAt b α v) := by
  intro h_0 h_1
  have hf_block := fracPart_odd_block hs hdecomp α
  have hrec1 : h_1 = (3 / 2 : ℝ) ^ s * h_0 - 1 := by
    dsimp [h_0, h_1, renewalTail]
    rw [hf_block]
    ring
  have hcancel : (2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have hrec0 : h_0 = (2 / 3 : ℝ) ^ s * (1 + h_1) := by
    rw [hrec1]
    calc
      h_0 = ((2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s) * h_0 := by rw [hcancel, one_mul]
      _ = (2 / 3 : ℝ) ^ s * (1 + ((3 / 2 : ℝ) ^ s * h_0 - 1)) := by ring
  have hint :
      ∀ v : ℕ, 1 ≤ v → v ≤ s →
        fracPart b α v = (2 / 3 : ℝ) ^ (s - v) * ((1 + h_1) / 3) := by
    intro v hv1 hvs
    have hstep1 : fracPart b α 1 = (3 / 2 : ℝ) * fracPart b α 0 - 1 / 2 := by
      have h := fracPart_succ b α 0
      have hodd0 : orbit b 0 % 2 = 1 := by
        simp only [orbit]
        have h2s : 2 ∣ 2 ^ s * u := by
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k + 1 := ⟨s - 1, by omega⟩
          rw [Nat.pow_succ']
          exact ⟨2 ^ k * u, by ring⟩
        omega
      rw [hodd0] at h
      simpa using h
    have heven_iter :
        ∀ m : ℕ, m ≤ s - 1 →
          fracPart b α (1 + m) = (3 / 2 : ℝ) ^ m * fracPart b α 1 := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
          have ihm := ih (by omega)
          have hsucc := fracPart_succ b α (1 + m)
          have hev : orbit b (1 + m) % 2 = 0 :=
            orbit_odd_block_even_interior (by omega) (by omega) hdecomp
          rw [hev] at hsucc
          simp only [Nat.cast_zero, zero_div, sub_zero] at hsucc
          rw [show 1 + (m + 1) = (1 + m) + 1 by omega, hsucc, ihm, pow_succ]
          ring
    have hv_eq : v = 1 + (v - 1) := by omega
    have hfv : fracPart b α v = (3 / 2 : ℝ) ^ v * (fracPart b α 0 - 1 / 3) := by
      conv_lhs => rw [hv_eq]
      rw [heven_iter (v - 1) (by omega), hstep1]
      have hs_v : (3 / 2 : ℝ) ^ v = (3 / 2 : ℝ) ^ (v - 1) * (3 / 2 : ℝ) := by
        conv_lhs => rw [hv_eq, pow_add, pow_one]
        ring
      rw [hs_v]
      ring
    have hfs : (1 + h_1) / 3 = fracPart b α s := by
      dsimp [h_1, renewalTail]
      ring
    have hsub : s = (s - v) + v := by omega
    have h32_s : (3 / 2 : ℝ) ^ s = (3 / 2 : ℝ) ^ (s - v) * (3 / 2 : ℝ) ^ v := by
      conv_lhs => rw [hsub, pow_add]
    have hc_v : (2 / 3 : ℝ) ^ (s - v) * (3 / 2 : ℝ) ^ (s - v) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hfs, hf_block, hfv, h32_s]
    calc
      (3 / 2 : ℝ) ^ v * (fracPart b α 0 - 1 / 3) =
          ((2 / 3 : ℝ) ^ (s - v) * (3 / 2 : ℝ) ^ (s - v)) *
            ((3 / 2 : ℝ) ^ v * (fracPart b α 0 - 1 / 3)) := by
        rw [hc_v, one_mul]
      _ = (2 / 3 : ℝ) ^ (s - v) *
            (((3 / 2 : ℝ) ^ (s - v) * (3 / 2 : ℝ) ^ v) * (fracPart b α 0 - 1 / 3)) := by ring
  refine ⟨⟨hrec1, hrec0⟩, hint, ?_⟩
  intro hh1_pos hh1_lt hh0_lt
  have hq_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ s := pow_pos (by norm_num) s
  have hh0_pos : 0 < h_0 := by
    rw [hrec0]
    exact mul_pos hq_pos (by linarith)
  refine ⟨hh0_pos, ?_⟩
  intro v hvs
  rw [validCompanionAt_iff_fracPart]
  rcases Nat.eq_zero_or_pos v with rfl | hv_pos
  · have hf0 : fracPart b α 0 = (1 + h_0) / 3 := by dsimp [h_0, renewalTail]; ring
    rw [hf0]
    constructor <;> linarith
  · rw [hint v hv_pos hvs]
    have hqv_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ (s - v) := pow_pos (by norm_num) (s - v)
    have hqv_le : (2 / 3 : ℝ) ^ (s - v) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h1_bounds : 0 < (1 + h_1) / 3 ∧ (1 + h_1) / 3 < 1 / 2 := by
      constructor <;> linarith
    refine ⟨le_of_lt (mul_pos hqv_pos h1_bounds.1), ?_⟩
    calc
      (2 / 3 : ℝ) ^ (s - v) * ((1 + h_1) / 3) ≤ 1 * ((1 + h_1) / 3) :=
        mul_le_mul_of_nonneg_right hqv_le (le_of_lt h1_bounds.1)
      _ < 1 / 2 := by linarith

/-- **Initial Even-Run Shift Bridge (`even_seed_reaches_odd_boundary`, Section A3.3)**:
If `a_0 = 2 ^ k * b_0` with `b_0 % 2 = 1`, then `orbit a_0 k = 3 ^ k * b_0` is odd, and
`ValidCompanionForever a_0 α` implies `ValidCompanionForever (3 ^ k * b_0) (α * (3 / 2 : ℝ) ^ k)`. -/
theorem even_seed_reaches_odd_boundary {a_0 k b_0 : ℕ} {α : ℝ}
    (ha0 : a_0 = 2 ^ k * b_0) (hb0_odd : b_0 % 2 = 1) :
    orbit a_0 k = 3 ^ k * b_0 ∧
      (3 ^ k * b_0) % 2 = 1 ∧
      (ValidCompanionForever a_0 α →
        ValidCompanionForever (3 ^ k * b_0) (α * (3 / 2 : ℝ) ^ k)) := by
  have horb : orbit a_0 k = 3 ^ k * b_0 := by
    rw [ha0, orbit_even_tail b_0 k k (le_refl k), Nat.sub_self, Nat.pow_zero, Nat.mul_one]
  have hodd3 : ∀ m : ℕ, 3 ^ m % 2 = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hodd : (3 ^ k * b_0) % 2 = 1 := by
    rw [Nat.mul_mod, hodd3 k, hb0_odd]
  refine ⟨horb, hodd, ?_⟩
  intro hsurv n
  have hn := hsurv (k + n)
  have horb_add : orbit a_0 (k + n) = orbit (3 ^ k * b_0) n := by
    rw [orbit_add, horb]
  unfold ValidCompanionAt at hn ⊢
  rw [horb_add, pow_add, ← mul_assoc] at hn
  exact hn

/-- **Section A3.4 Negative/Limitative Theorem: Real Feasibility of $s_r \ge 3$ & the $s = 3$ Rational Ghost
(`minimum_gap_three_real_feasibility_and_ghost`, Section A3.4)**:
1. Whenever a step length $s \ge 3$ and next tail $0 < h' \le 8/19$ are given, the backward renewal
   map $h = (2/3)^s (1 + h')$ satisfies $0 < h \le 8/19 < 1/2$.
2. For the stationary schedule $s = 3$, $h_* = 8/19 < 1/2$ is the exact fixed point of
   $h = (8/27)(1 + h)$, while its unique stationary $P_*$ and $b_*$ are the negative rationals
   $P_* = -8/19$ and $b_* = -9/19$ ($19 b_* + 9 = 0$), proving that real renewal feasibility alone
   cannot exclude all-$\ge 3$ schedules without positive natural-seed arithmetic. -/
theorem minimum_gap_three_real_feasibility_and_ghost {s : ℕ} {h' : ℝ}
    (hs : 3 ≤ s) (hh'_pos : 0 < h') (hh'_le : h' ≤ 8 / 19) :
    (0 < (2 / 3 : ℝ) ^ s * (1 + h') ∧
      (2 / 3 : ℝ) ^ s * (1 + h') ≤ 8 / 19 ∧
      (8 / 19 : ℝ) < 1 / 2) ∧
      ((8 / 27 : ℚ) * (1 + 8 / 19) = 8 / 19 ∧
        (27 / 8 : ℚ) * (-8 / 19) + 1 = -8 / 19 ∧
        3 * (-9 / 19 : ℚ) + 1 = -8 / 19 ∧
        19 * (-9 / 19 : ℚ) + 9 = 0) := by
  have hq_pos : (0 : ℝ) < (2 / 3 : ℝ) ^ s := pow_pos (by norm_num) s
  have hq_le : (2 / 3 : ℝ) ^ s ≤ (2 / 3 : ℝ) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hprod_le : (2 / 3 : ℝ) ^ s * (1 + h') ≤ 8 / 19 := by
    calc
      (2 / 3 : ℝ) ^ s * (1 + h') ≤ (2 / 3 : ℝ) ^ 3 * (1 + 8 / 19) :=
        mul_le_mul hq_le (by linarith) (by linarith) (by norm_num)
      _ = 8 / 19 := by norm_num
  refine ⟨⟨mul_pos hq_pos (by linarith), hprod_le, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-! ## 4. Section A4: Finite Renewal Escape Certificate, Rational Cap Engine & Extra-Bit Compatibility -/

/-- **Finite Renewal Escape Certificate (`finite_renewal_escape_certificate`, Section A4.1)**:
For any valid `N`-block chain (`N ≥ 1`) starting at `b_0` with total length `T_N = blockSteps s N`:
1. `2 * renewalNumerator s N ≠ 3 ^ T_N` (since the left side is even and the right side is odd),
2. `2 * renewalNumerator s N ≥ 3 ^ T_N ↔ 6 * blockKernel s N + 2 ^ (T_N + 1) ≥ 3 ^ (T_N + 1)`, and
3. Whenever `2 * renewalNumerator s N ≥ 3 ^ T_N`, **no real $\alpha$** can satisfy
   `ValidCompanionUpTo b_0 α (T_N + 1)` (nor `ValidCompanionForever b_0 α`). -/
theorem finite_renewal_escape_certificate {b_0 : ℕ} {s u : ℕ → ℕ} {N : ℕ}
    (hN : 1 ≤ N) (hchain : ValidBlockChain b_0 s u N) :
    let T_N := blockSteps s N
    2 * renewalNumerator s N ≠ 3 ^ T_N ∧
      (2 * renewalNumerator s N ≥ 3 ^ T_N ↔
        6 * blockKernel s N + 2 ^ (T_N + 1) ≥ 3 ^ (T_N + 1)) ∧
      (2 * renewalNumerator s N ≥ 3 ^ T_N →
        (∀ α : ℝ, ¬ ValidCompanionUpTo b_0 α (T_N + 1)) ∧
          (∀ α : ℝ, ¬ ValidCompanionForever b_0 α)) := by
  intro T_N
  have hodd3 : ∀ m : ℕ, 3 ^ m % 2 = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hne : 2 * renewalNumerator s N ≠ 3 ^ T_N := by
    intro heq
    have h3 : 3 ^ T_N % 2 = 1 := hodd3 T_N
    omega
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator
    (fun k hk => (hchain k hk).1)
  change 3 * blockKernel s N = (3 ^ T_N - 2 ^ T_N) + renewalNumerator s N at hbridge
  have hT_le : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  have h2_T1 : 2 ^ (T_N + 1) = 2 * 2 ^ T_N := by rw [Nat.pow_succ']
  have h3_T1 : 3 ^ (T_N + 1) = 3 * 3 ^ T_N := by rw [Nat.pow_succ']
  have h6K : 6 * blockKernel s N = 2 * (3 * blockKernel s N) := by ring
  have hiff :
      2 * renewalNumerator s N ≥ 3 ^ T_N ↔
        6 * blockKernel s N + 2 ^ (T_N + 1) ≥ 3 ^ (T_N + 1) := by
    rw [h6K, hbridge, h2_T1, h3_T1]
    omega
  refine ⟨hne, hiff, ?_⟩
  intro hescape
  refine ⟨?_, ?_⟩
  · intro α hsurv
    have hpinch := mixed_block_return_pinch hN hchain hsurv
    change 6 * blockKernel s N + 2 ^ (T_N + 1) < 3 ^ (T_N + 1) at hpinch
    have hge := hiff.mp hescape
    omega
  · intro α hforever
    have hsurv : ValidCompanionUpTo b_0 α (T_N + 1) :=
      (validCompanionForever_iff_forall_upTo b_0 α).mp hforever (T_N + 1)
    have hpinch := mixed_block_return_pinch hN hchain hsurv
    change 6 * blockKernel s N + 2 ^ (T_N + 1) < 3 ^ (T_N + 1) at hpinch
    have hge := hiff.mp hescape
    omega

/-- **Seed-137 $(2, 5)$ Finite Escape Witness (`seed_137_two_five_escape_certificate`, Section A4.1)**:
The genuine odd seed `137` executes the two odd blocks `137 →(s=2) 309 →(s=5) 2349` (`d = 7`),
where `A_{0,2} = 1100` and `2 * 1100 = 2200 > 2187 = 3^7`. -/
theorem seed_137_two_five_escape_certificate :
    3 * 137 + 1 = 2 ^ 2 * 103 ∧
      orbit 137 2 = 309 ∧
      3 * 309 + 1 = 2 ^ 5 * 29 ∧
      orbit 309 5 = 2349 ∧
      2 ^ 2 * 3 ^ 5 + 2 ^ 7 = 1100 ∧
      2 * 1100 > 3 ^ 7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Rational feasibility cap update $B_{r+1} = \min(1/2, (3/2)^s B_r - 1)$. -/
def recoveryCapStep (s : ℕ) (B : ℚ) : ℚ :=
  min (1 / 2) ((3 / 2 : ℚ) ^ s * B - 1)

/-- **Rational Recovery-Cap Cascade for $(2, 6, 3, 3, 2)$ (`recoveryCap_two_six_three_three_two_cascade`,
Section A4.2)**:
Starting from $B_0 = 1/2$, applying `recoveryCapStep` along $(2, 6, 3, 3, 2)$ produces the exact
rational caps $1/8 \to 217/512 \to 1763/4096 \to 14833/32768 \to 2425/131072$, after which $s = 9$
is infeasible ($< 0$) and $s \ge 10$ is required. -/
theorem recoveryCap_two_six_three_three_two_cascade :
    let B1 := recoveryCapStep 2 (1 / 2)
    let B2 := recoveryCapStep 6 B1
    let B3 := recoveryCapStep 3 B2
    let B4 := recoveryCapStep 3 B3
    let B5 := recoveryCapStep 2 B4
    B1 = 1 / 8 ∧
      (3 / 2 : ℚ) ^ 5 * B1 - 1 < 0 ∧
      B2 = 217 / 512 ∧
      B3 = 1763 / 4096 ∧
      B4 = 14833 / 32768 ∧
      B5 = 2425 / 131072 ∧
      (3 / 2 : ℚ) ^ 9 * B5 - 1 < 0 ∧
      0 < (3 / 2 : ℚ) ^ 10 * B5 - 1 := by
  dsimp [recoveryCapStep]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **Extra-Bit Prefix Compatibility & the $P_0 = 4, s = 1$ Counterexample
(`extra_bit_prefix_compatibility_and_counterexample`, Section A4.3)**:
1. Across any valid `N`-block chain from `b_0`, the terminal state `orbit b_0 T_N` has
   `oddReturnP (orbit b_0 T_N)` even, so `2 ^ (T_N + 1) ∣ (3 ^ T_N * oddReturnP b_0 + renewalNumerator s N)`.
2. At $P_0 = 4$ ($b_0 = 1$) with the falsely requested gap $s = 1$, $2 \mid (3^1 \cdot 4 + 2^1 = 14)$,
   yet $2^2 = 4 \nmid 14$ because $(3^1 \cdot 4 + 2^1) / 2^1 = 7$ is odd (the true gap is $v_2(4) = 2$). -/
theorem extra_bit_prefix_compatibility_and_counterexample {b_0 : ℕ} {s u : ℕ → ℕ} {N : ℕ}
    (hN : 1 ≤ N) (hchain : ValidBlockChain b_0 s u N) :
    let T_N := blockSteps s N
    (2 ^ (T_N + 1) ∣ (3 ^ T_N * oddReturnP b_0 + renewalNumerator s N)) ∧
      ((3 ^ 1 * 4 + 2 ^ 1) % 2 ^ 1 = 0 ∧
        (3 ^ 1 * 4 + 2 ^ 1) % 2 ^ 2 = 2 ∧
        ((3 ^ 1 * 4 + 2 ^ 1) / 2 ^ 1) % 2 = 1) := by
  intro T_N
  have hm := renewal_prefix_master_identity hchain
  have hodd_ret : orbit b_0 T_N % 2 = 1 := mixed_block_return_odd hN hchain
  have heven_P : 2 ∣ oddReturnP (orbit b_0 T_N) := by
    unfold oddReturnP
    omega
  rcases heven_P with ⟨k, hk⟩
  refine ⟨⟨k, ?_⟩, ⟨by decide, by decide, by decide⟩⟩
  rw [← hm, hk, Nat.pow_succ]
  ring

end Mahler.ArchimedeanPinningAndRenewal
