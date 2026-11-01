import ModThreeDeathClassOctadicSieve

/-!
# Renewal Cocycle Composition, Escape Persistence, Two-Sided Bellman Gap Sandwiches & Odd Integer Renewal Slack

This module formalizes **Outer Loop 1 / 10 (Part V, Sections O1.1–O1.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O1.1 (Inner Loop 1 / 3) — Renewal Cocycle Composition & Escape Persistence
   (`blockSteps_add_shift`, `renewalNumerator_cocycle_composition`,
   `renewalNumerator_pos_of_pos_horizon`, `renewal_escape_persists_forever`)**:
   - Across any two consecutive block segments $[0, K]$ and $[K, K+M]$ with shifted gap sequence
     $s'(t) = s(K + t)$ and shifted step sum $d = \operatorname{blockSteps} s' M$,
     `blockSteps s (K + M) = blockSteps s K + d` and
     `renewalNumerator s (K + M) = 3 ^ d * renewalNumerator s K + 2 ^ (blockSteps s K) * renewalNumerator s' M`.
   - Consequently, once $2 A_{0,K} \ge 3^{T_K}$ holds at horizon $K$, **every** subsequent horizon
     $K + M$ ($M \ge 1$) satisfies $2 A_{0,K+M} > 3^{T_{K+M}}$ strictly, regardless of how long the
     subsequent recovery blocks $s_K, \dots, s_{K+M-1}$ are!

2. **Section O1.2 (Inner Loop 2 / 3) — Two-Sided Integer Bellman Gap Sandwiches & Sub-Ceiling Escape
   (`renewalNumerator_bellman_lower_sandwich`, `renewalNumerator_bellman_upper_sandwich`,
   `short_block_segment_escape_of_stepSum_ge_three`)**:
   - Because $s \mapsto 2^s / (3^s - 2^s)$ is antitone:
     - Whenever $\forall k < N,\, s_k \le H$,
       `2 ^ H * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) ≤ (3 ^ H - 2 ^ H) * renewalNumerator s N`.
     - Whenever $\forall k < N,\, L \le s_k$,
       `(3 ^ L - 2 ^ L) * renewalNumerator s N ≤ 2 ^ L * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N))`.
   - At $H = 2$ ($s_k \le 2$), $5 A_{0,N} \ge 4(3^{T_N} - 2^{T_N})$, which forces $2 A_{0,N} > 3^{T_N}$
     for every segment with total step sum $T_N \ge 3$.

3. **Section O1.3 (Inner Loop 3 / 3) — Odd Integer Renewal Slack $\Sigma_N = 3^{T_N} - 2 A_{0,N}$
   (`renewalIntSlack`, `renewalIntSlack_step_and_cocycle`,
   `renewalIntSlack_eq_return_pinch_margin_and_odd`)**:
   - Defines the signed integer renewal slack $\Sigma_N := 3^{T_N} - 2 A_{0,N} \in \mathbb{Z}$.
   - Proves the one-step recurrence $\Sigma_{N+1} = 3^{s_N} \Sigma_N - 2^{T_{N+1} + 1}$, the multi-step
     cocycle law $\Sigma_{K+M} = 3^d \Sigma_K - 2^{T_K + 1} A_{K,K+M}$, the exact identity with the
     return-pinch margin $3^{T_N + 1} - (6 K_N + 2^{T_N + 1}) = \Sigma_N$, and oddness $\Sigma_N \bmod 2 = 1$.
-/

namespace Mahler.RenewalCocycleAndSandwich

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
open Mahler.ArchimedeanPinningAndRenewal
open Mahler.ConsecutiveGCDAndPillai
open Mahler.OctadicDeathAnatomy

/-! ## 1. Section O1.1: Renewal Cocycle Composition & Escape Persistence -/

/-- Shift additivity of `blockSteps`:
`blockSteps s (K + M) = blockSteps s K + blockSteps (fun t => s (K + t)) M`. -/
theorem blockSteps_add_shift (s : ℕ → ℕ) (K M : ℕ) :
    blockSteps s (K + M) = blockSteps s K + blockSteps (fun t => s (K + t)) M := by
  induction M with
  | zero => simp [blockSteps]
  | succ M ih =>
      rw [← Nat.add_assoc, blockSteps, ih]
      simp only [blockSteps]
      omega

/-- **Renewal Cocycle Composition Law (`renewalNumerator_cocycle_composition`, Section O1.1)**:
For any gap sequence `s : ℕ → ℕ` and horizons `K, M : ℕ`, setting `s' t = s (K + t)` and
`d = blockSteps s' M`:
`renewalNumerator s (K + M) = 3 ^ d * renewalNumerator s K + 2 ^ (blockSteps s K) * renewalNumerator s' M`. -/
theorem renewalNumerator_cocycle_composition (s : ℕ → ℕ) (K M : ℕ) :
    let s' := fun t => s (K + t)
    let d := blockSteps s' M
    renewalNumerator s (K + M) =
      3 ^ d * renewalNumerator s K + 2 ^ (blockSteps s K) * renewalNumerator s' M := by
  intro s' d
  induction M with
  | zero =>
      dsimp [s', d]
      simp [blockSteps, renewalNumerator]
  | succ M ih =>
      have hshift := blockSteps_add_shift s K M
      rw [← Nat.add_assoc, renewalNumerator, ih]
      simp only [renewalNumerator, blockSteps, s', d]
      rw [hshift]
      simp only [Nat.pow_add]
      ring

/-- Positivity of `renewalNumerator s M` for `1 ≤ M`: `2 ^ (blockSteps s M) ≤ renewalNumerator s M`
and `1 ≤ renewalNumerator s M`. -/
theorem renewalNumerator_pos_of_pos_horizon (s : ℕ → ℕ) {M : ℕ} (hM : 1 ≤ M) :
    2 ^ (blockSteps s M) ≤ renewalNumerator s M ∧ 1 ≤ renewalNumerator s M := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = m + 1 := ⟨M - 1, by omega⟩
  simp only [renewalNumerator]
  have hpos : 1 ≤ 2 ^ (blockSteps s (m + 1)) := Nat.one_le_pow _ 2 (by decide)
  exact ⟨by omega, by omega⟩

/-- **Unconditional Persistence of Finite Renewal Escape (`renewal_escape_persists_forever`,
Section O1.1)**:
If `2 * renewalNumerator s K ≥ 3 ^ (blockSteps s K)` holds at horizon `K`, then for **every**
future horizon `K + M` (`M : ℕ`), `2 * renewalNumerator s (K + M) ≥ 3 ^ (blockSteps s (K + M))`,
and for `1 ≤ M`, the strict inequality `2 * renewalNumerator s (K + M) > 3 ^ (blockSteps s (K + M))`
holds regardless of the subsequent block lengths $s_K, \dots, s_{K+M-1}$. -/
theorem renewal_escape_persists_forever {s : ℕ → ℕ} {K M : ℕ}
    (hesc : 2 * renewalNumerator s K ≥ 3 ^ (blockSteps s K)) :
    2 * renewalNumerator s (K + M) ≥ 3 ^ (blockSteps s (K + M)) ∧
      (1 ≤ M → 2 * renewalNumerator s (K + M) > 3 ^ (blockSteps s (K + M))) := by
  have hcomp := renewalNumerator_cocycle_composition s K M
  have hshift := blockSteps_add_shift s K M
  set s' := fun t => s (K + t)
  set d := blockSteps s' M
  set TK := blockSteps s K
  change renewalNumerator s (K + M) = 3 ^ d * renewalNumerator s K + 2 ^ TK * renewalNumerator s' M at hcomp
  have hpow3 : 3 ^ (blockSteps s (K + M)) = 3 ^ d * 3 ^ TK := by
    rw [hshift, Nat.pow_add, Nat.mul_comm]
  have hmul : 3 ^ d * 3 ^ TK ≤ 2 * (3 ^ d * renewalNumerator s K) := by
    have hm := Nat.mul_le_mul_left (3 ^ d) hesc
    linarith
  rw [hcomp, hpow3]
  refine ⟨by omega, ?_⟩
  intro hM
  have hposM := (renewalNumerator_pos_of_pos_horizon s' hM).2
  have hpos2 : 1 ≤ 2 ^ TK := Nat.one_le_pow TK 2 (by decide)
  have hprod : 1 ≤ 2 ^ TK * renewalNumerator s' M := Nat.mul_le_mul hpos2 hposM
  omega

/-! ## 2. Section O1.2: Two-Sided Integer Bellman Gap Sandwiches & Sub-Ceiling Escape -/

/-- Local step inequality: for `a ≤ b`, `(3 ^ a - 2 ^ a) * 2 ^ b ≤ 2 ^ a * (3 ^ b - 2 ^ b)`. -/
theorem pow_diff_mul_two_pow_mono {a b : ℕ} (hab : a ≤ b) :
    (3 ^ a - 2 ^ a) * 2 ^ b ≤ 2 ^ a * (3 ^ b - 2 ^ b) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, b = a + d := ⟨b - a, by omega⟩
  have hle_a : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) a
  have hle_ad : 2 ^ (a + d) ≤ 3 ^ (a + d) := Nat.pow_le_pow_left (by decide) (a + d)
  have hle_d : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
  have hid :
      2 ^ a * (3 ^ (a + d) - 2 ^ (a + d)) =
        (3 ^ a - 2 ^ a) * 2 ^ (a + d) + 2 ^ a * 3 ^ a * (3 ^ d - 2 ^ d) := by
    zify [hle_a, hle_ad, hle_d]
    simp only [pow_add]
    ring
  omega

/-- **Bellman Lower Sandwich for Bounded Block Lengths (`renewalNumerator_bellman_lower_sandwich`,
Section O1.2)**:
Whenever `∀ k < N, s k ≤ H`,
`2 ^ H * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) ≤ (3 ^ H - 2 ^ H) * renewalNumerator s N`. -/
theorem renewalNumerator_bellman_lower_sandwich {s : ℕ → ℕ} {N H : ℕ}
    (hs : ∀ k < N, s k ≤ H) :
    2 ^ H * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) ≤
      (3 ^ H - 2 ^ H) * renewalNumerator s N := by
  induction N with
  | zero => simp [blockSteps, renewalNumerator]
  | succ N ih =>
      have ih' := ih (fun k hk => hs k (by omega))
      have hloc := pow_diff_mul_two_pow_mono (hs N (by omega))
      set T := blockSteps s N
      set A := renewalNumerator s N
      set MH := 3 ^ H - 2 ^ H
      have hmul1 : 3 ^ (s N) * (2 ^ H * (3 ^ T - 2 ^ T)) ≤ 3 ^ (s N) * (MH * A) :=
        Nat.mul_le_mul_left (3 ^ (s N)) ih'
      have hloc_comm : 2 ^ H * (3 ^ (s N) - 2 ^ (s N)) ≤ MH * 2 ^ (s N) := by
        calc
          2 ^ H * (3 ^ (s N) - 2 ^ (s N)) = (3 ^ (s N) - 2 ^ (s N)) * 2 ^ H := Nat.mul_comm _ _
          _ ≤ 2 ^ (s N) * MH := hloc
          _ = MH * 2 ^ (s N) := Nat.mul_comm _ _
      have hmul2 : 2 ^ T * (2 ^ H * (3 ^ (s N) - 2 ^ (s N))) ≤ 2 ^ T * (MH * 2 ^ (s N)) :=
        Nat.mul_le_mul_left (2 ^ T) hloc_comm
      have hT_le : 2 ^ T ≤ 3 ^ T := Nat.pow_le_pow_left (by decide) T
      have hs_le : 2 ^ (s N) ≤ 3 ^ (s N) := Nat.pow_le_pow_left (by decide) (s N)
      have hTs_le : 2 ^ (T + s N) ≤ 3 ^ (T + s N) := Nat.pow_le_pow_left (by decide) (T + s N)
      have htelescope :
          3 ^ (s N) * (2 ^ H * (3 ^ T - 2 ^ T)) + 2 ^ T * (2 ^ H * (3 ^ (s N) - 2 ^ (s N))) =
            2 ^ H * (3 ^ (T + s N) - 2 ^ (T + s N)) := by
        zify [hT_le, hs_le, hTs_le]
        simp only [pow_add]
        ring
      have hstep_A :
          MH * renewalNumerator s (N + 1) = 3 ^ (s N) * (MH * A) + 2 ^ T * (MH * 2 ^ (s N)) := by
        simp only [renewalNumerator, blockSteps, T, A, Nat.pow_add]
        ring
      have hstep_T : blockSteps s (N + 1) = T + s N := rfl
      rw [hstep_T, hstep_A]
      omega

/-- **Bellman Upper Sandwich for Lower-Bounded Block Lengths (`renewalNumerator_bellman_upper_sandwich`,
Section O1.2)**:
Whenever `∀ k < N, L ≤ s k`,
`(3 ^ L - 2 ^ L) * renewalNumerator s N ≤ 2 ^ L * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N))`. -/
theorem renewalNumerator_bellman_upper_sandwich {s : ℕ → ℕ} {N L : ℕ}
    (hs : ∀ k < N, L ≤ s k) :
    (3 ^ L - 2 ^ L) * renewalNumerator s N ≤
      2 ^ L * (3 ^ (blockSteps s N) - 2 ^ (blockSteps s N)) := by
  induction N with
  | zero => simp [blockSteps, renewalNumerator]
  | succ N ih =>
      have ih' := ih (fun k hk => hs k (by omega))
      have hloc := pow_diff_mul_two_pow_mono (hs N (by omega))
      set T := blockSteps s N
      set A := renewalNumerator s N
      set ML := 3 ^ L - 2 ^ L
      have hmul1 : 3 ^ (s N) * (ML * A) ≤ 3 ^ (s N) * (2 ^ L * (3 ^ T - 2 ^ T)) :=
        Nat.mul_le_mul_left (3 ^ (s N)) ih'
      have hmul2 : 2 ^ T * (ML * 2 ^ (s N)) ≤ 2 ^ T * (2 ^ L * (3 ^ (s N) - 2 ^ (s N))) :=
        Nat.mul_le_mul_left (2 ^ T) hloc
      have hT_le : 2 ^ T ≤ 3 ^ T := Nat.pow_le_pow_left (by decide) T
      have hs_le : 2 ^ (s N) ≤ 3 ^ (s N) := Nat.pow_le_pow_left (by decide) (s N)
      have hTs_le : 2 ^ (T + s N) ≤ 3 ^ (T + s N) := Nat.pow_le_pow_left (by decide) (T + s N)
      have htelescope :
          3 ^ (s N) * (2 ^ L * (3 ^ T - 2 ^ T)) + 2 ^ T * (2 ^ L * (3 ^ (s N) - 2 ^ (s N))) =
            2 ^ L * (3 ^ (T + s N) - 2 ^ (T + s N)) := by
        zify [hT_le, hs_le, hTs_le]
        simp only [pow_add]
        ring
      have hstep_A :
          ML * renewalNumerator s (N + 1) = 3 ^ (s N) * (ML * A) + 2 ^ T * (ML * 2 ^ (s N)) := by
        simp only [renewalNumerator, blockSteps, T, A, Nat.pow_add]
        ring
      have hstep_T : blockSteps s (N + 1) = T + s N := rfl
      rw [hstep_T, hstep_A]
      omega

/-- **Unconditional Escape of Short-Block Segments (`short_block_segment_escape_of_stepSum_ge_three`,
Section O1.2)**:
If `∀ k < N, s k ≤ 2` and `3 ≤ blockSteps s N`, then `4 * (3 ^ T_N - 2 ^ T_N) ≤ 5 * renewalNumerator s N`
and `2 * renewalNumerator s N > 3 ^ (blockSteps s N)`. -/
theorem short_block_segment_escape_of_stepSum_ge_three {s : ℕ → ℕ} {N : ℕ}
    (hs : ∀ k < N, s k ≤ 2) (hT : 3 ≤ blockSteps s N) :
    let T_N := blockSteps s N
    4 * (3 ^ T_N - 2 ^ T_N) ≤ 5 * renewalNumerator s N ∧
      2 * renewalNumerator s N > 3 ^ T_N := by
  intro T_N
  have hsand := renewalNumerator_bellman_lower_sandwich (H := 2) hs
  change (2 ^ 2) * (3 ^ T_N - 2 ^ T_N) ≤ (3 ^ 2 - 2 ^ 2) * renewalNumerator s N at hsand
  have h8_le_3 : ∀ m : ℕ, 8 * 2 ^ (m + 3) < 3 * 3 ^ (m + 3) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 8 * 2 ^ (m + 1 + 3) = 2 * (8 * 2 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]
          ring
        have h2 : 3 * 3 ^ (m + 1 + 3) = 3 * (3 * 3 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]
          ring
        omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, T_N = m + 3 := ⟨T_N - 3, by omega⟩
  have hpow : 8 * 2 ^ T_N < 3 * 3 ^ T_N := by
    rw [hm]
    exact h8_le_3 m
  have hle_T : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  exact ⟨by omega, by omega⟩

/-! ## 3. Section O1.3: Odd Integer Renewal Slack $\Sigma_N = 3^{T_N} - 2 A_{0,N}$ -/

/-- Signed integer renewal slack $\Sigma_N := 3^{T_N} - 2 A_{0,N} \in \mathbb{Z}$. -/
def renewalIntSlack (s : ℕ → ℕ) (N : ℕ) : ℤ :=
  (3 : ℤ) ^ (blockSteps s N) - 2 * (renewalNumerator s N : ℤ)

/-- **One-Step Recurrence & Multi-Step Cocycle Law for $\Sigma_N$
(`renewalIntSlack_step_and_cocycle`, Section O1.3)**:
1. `renewalIntSlack s 0 = 1`,
2. `renewalIntSlack s (N + 1) = (3 : ℤ) ^ (s N) * renewalIntSlack s N - (2 : ℤ) ^ (blockSteps s (N + 1) + 1)`, and
3. `renewalIntSlack s (K + M) = (3 : ℤ) ^ (blockSteps (fun t => s (K + t)) M) * renewalIntSlack s K - (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator (fun t => s (K + t)) M : ℤ)`. -/
theorem renewalIntSlack_step_and_cocycle (s : ℕ → ℕ) (N K M : ℕ) :
    renewalIntSlack s 0 = 1 ∧
      renewalIntSlack s (N + 1) =
        (3 : ℤ) ^ (s N) * renewalIntSlack s N - (2 : ℤ) ^ (blockSteps s (N + 1) + 1) ∧
      renewalIntSlack s (K + M) =
        (3 : ℤ) ^ (blockSteps (fun t => s (K + t)) M) * renewalIntSlack s K -
          (2 : ℤ) ^ (blockSteps s K + 1) * (renewalNumerator (fun t => s (K + t)) M : ℤ) := by
  refine ⟨by simp [renewalIntSlack, blockSteps, renewalNumerator], ?_, ?_⟩
  · unfold renewalIntSlack
    simp only [blockSteps, renewalNumerator, pow_add, pow_succ, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    ring
  · have hcomp := renewalNumerator_cocycle_composition s K M
    have hshift := blockSteps_add_shift s K M
    unfold renewalIntSlack
    rw [hshift, hcomp]
    simp only [pow_add, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring

/-- **Exact Identity Between Renewal Slack and Return-Pinch Margin & Oddness Law
(`renewalIntSlack_eq_return_pinch_margin_and_odd`, Section O1.3)**:
For any valid block sequence (`∀ k < N, 1 ≤ s k`):
1. `(3 : ℤ) ^ (blockSteps s N + 1) - (6 * (blockKernel s N : ℤ) + (2 : ℤ) ^ (blockSteps s N + 1)) = renewalIntSlack s N`,
2. `renewalIntSlack s N % 2 = 1`, and
3. `renewalIntSlack s N > 0 ↔ 2 * renewalNumerator s N < 3 ^ (blockSteps s N)`. -/
theorem renewalIntSlack_eq_return_pinch_margin_and_odd {s : ℕ → ℕ} {N : ℕ}
    (hs : ∀ k < N, 1 ≤ s k) :
    let T_N := blockSteps s N
    (3 : ℤ) ^ (T_N + 1) - (6 * (blockKernel s N : ℤ) + (2 : ℤ) ^ (T_N + 1)) =
      renewalIntSlack s N ∧
      renewalIntSlack s N % 2 = 1 ∧
      (0 < renewalIntSlack s N ↔ 2 * renewalNumerator s N < 3 ^ T_N) := by
  intro T_N
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator hs
  change 3 * blockKernel s N = (3 ^ T_N - 2 ^ T_N) + renewalNumerator s N at hbridge
  have hle : 2 ^ T_N ≤ 3 ^ T_N := Nat.pow_le_pow_left (by decide) T_N
  have hbridge_z :
      3 * (blockKernel s N : ℤ) =
        (3 : ℤ) ^ T_N - (2 : ℤ) ^ T_N + (renewalNumerator s N : ℤ) := by
    zify [hle] at hbridge
    exact_mod_cast hbridge
  have hid :
      (3 : ℤ) ^ (T_N + 1) - (6 * (blockKernel s N : ℤ) + (2 : ℤ) ^ (T_N + 1)) =
        renewalIntSlack s N := by
    unfold renewalIntSlack
    change (3 : ℤ) ^ (T_N + 1) - (6 * (blockKernel s N : ℤ) + (2 : ℤ) ^ (T_N + 1)) =
      (3 : ℤ) ^ T_N - 2 * (renewalNumerator s N : ℤ)
    have h6K : 6 * (blockKernel s N : ℤ) = 2 * (3 * (blockKernel s N : ℤ)) := by ring
    rw [h6K, hbridge_z, pow_succ, pow_succ]
    ring
  have hodd3 : ∀ m : ℕ, 3 ^ m % 2 = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hodd_z : renewalIntSlack s N % 2 = 1 := by
    unfold renewalIntSlack
    change ((3 : ℤ) ^ T_N - 2 * (renewalNumerator s N : ℤ)) % 2 = 1
    have h3m : ((3 : ℤ) ^ T_N) % 2 = 1 := by
      have hn : 3 ^ T_N % 2 = 1 := hodd3 T_N
      exact_mod_cast hn
    omega
  have hpos_iff : 0 < renewalIntSlack s N ↔ 2 * renewalNumerator s N < 3 ^ T_N := by
    unfold renewalIntSlack
    change 0 < (3 : ℤ) ^ T_N - 2 * (renewalNumerator s N : ℤ) ↔
      2 * renewalNumerator s N < 3 ^ T_N
    have hcast : (3 : ℤ) ^ T_N = ((3 ^ T_N : ℕ) : ℤ) := by norm_cast
    rw [hcast]
    omega
  exact ⟨hid, hodd_z, hpos_iff⟩

end Mahler.RenewalCocycleAndSandwich
