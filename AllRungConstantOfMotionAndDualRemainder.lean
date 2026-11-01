import BoundedOddPartAndThreeAdicSieve

/-!
# Universal All-Rung Constant of Motion, Sharp $1/27$ Telescoping Slack, Bounded-Rung Bellman Constants & Seed-149 Counterexample

This module formalizes **Part I Track 1**, **Part II Section F2 (Integer Core)**, and
**Part III Sections A0.2 & A1** of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Step-Sum Cancellation & Single-Exponent Master Identity (`allRungTwoExp_add_three_mul_eq`,
   `allRung_W_recurrence`, `allRung_single_exponent_master_identity`)**:
   - Even when the long exit lengths $s_r \ge 4$ vary arbitrarily across epochs, the cumulative
     2-adic exponent $E_K = \sum_{r<K}(3 j_{r+1} + s_r)$ and 3-adic exponent
     $S_K = \sum_{r<K}(3 j_r + s_r)$ satisfy the exact telescoping identity
     `E_K + 3 * j 0 = S_K + 3 * j K`.
   - In the affine boundary coordinate $W_r = 2^{3 j_r} V_r$, the per-epoch recurrence collapses
     to the single-exponent law $2^{a_r} W_{r+1} + 2^{3 j_r} D_{s_r} = 3^{a_r} W_r$
     ($a_r = 3 j_r + s_r$, $D_s = 3^{s-3} - 2^{s-3}$), yielding the $K$-step master identity
     `2 ^ S_K * W K + allRungDefectAcc j s K = 3 ^ S_K * W 0`.

2. **Section A1.1 — Sharp $1/27$ Local & Accumulated Telescoping Slack
   (`allRung_local_twentySeven_slack_identity`, `allRungDefectAcc_twentySeven_strict_bound`)**:
   - Preserving the correlation between the step increment $u = 2^{3 j}(3^{s-3} - 2^{s-3})$ and
     step length $a = 3 j + s$ ($s \ge 4$) gives the exact positive slack decomposition:
     `27 * u + 3 ^ s * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (a - 3) = 3 ^ a - 2 ^ a`.
   - Inducting over any non-empty epoch prefix $K \ge 1$ yields the strict integer bound
     `0 < allRungDefectAcc j s K` and `27 * allRungDefectAcc j s K < 3 ^ S_K - 2 ^ S_K`
     (improving Fable's $3/65$ geometric bound to $1/27$ without real analysis).

3. **Section A1.2 — Constant of Motion, Two-Index Tail-Gap & Strict Modular Pinning
   (`all_rung_constant_of_motion_and_dual_remainder`, `allRung_tailGap_twentySeven_strict_bound`,
   `allRung_pinning_mod_strict_lower`, `allRung_W_strictMono`)**:
   - For every $K \ge 1$ and $W_0 \ge 1$:
     `(2 ^ S_K * W K) / 3 ^ S_K = W 0 - 1` and
     `(2 ^ S_K * W K) % 3 ^ S_K = 3 ^ S_K - allRungDefectAcc j s K`.
   - For every $K < M$ ($d = S_M - S_K$):
     `0 < 3 ^ d * W K - 2 ^ d * W M`, `27 * (3 ^ d * W K - 2 ^ d * W M) < 3 ^ d - 2 ^ d`,
     `27 * ((2 ^ d * W M) % 3 ^ d) > 26 * 3 ^ d + 2 ^ d`, and
     `65 * ((2 ^ d * W M) % 3 ^ d) ≥ 62 * 3 ^ d`.
   - Every positive integer trajectory $W_r$ ($W_0 \ge 1$) is strictly increasing: `W r < W (r + 1)`.

4. **Section A1.4 — Optimal Bounded-Rung Bellman Constants $C_H = (3^{H-3} - 2^{H-3})/(3^H - 2^H)$
   (`bounded_rung_bellman_constant_optimality`, `bounded_rung_accumulated_defect_bound`)**:
   - Whenever $4 \le s_r \le H$, cross-multiplied integer optimality holds at every step and
     accumulates to `(3 ^ H - 2 ^ H) * allRungDefectAcc j s K ≤ (3 ^ (H - 3) - 2 ^ (H - 3)) * (3 ^ S_K - 2 ^ S_K)`,
     with exact rational specializations $C_4 = 1/65$, $C_5 = 5/211$, $C_6 = 1/35$.

5. **Track 1.6 & Section A0.2 — Repeated Epoch-Window $(p, q)$ Cutoff & Genuine Seed-149 Counterexample
   (`all_rung_repeated_epoch_window_pq_cutoff`,
   `seed_149_window_1701_base_two_quotient_counterexample`,
   `diagonal_M_eq_K_mod_pinning_counterexample`)**:
   - Proves the corrected repeated-window $(p, q)$ cutoff (`1 ≤ q`, local window length $d$).
   - Certifies the genuine post-defect orbit window starting at `149` (`1701 → 8613 → 43605 → 1117557`),
     refuting the unguarded claim that $W_0 < 2^{S_K}$ forces $W_K = \lfloor 3^{S_K} W_0 / 2^{S_K} \rfloor$.
-/

namespace Mahler.AllRungConstantOfMotion

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

/-! ## 1. Cumulative Exponents, Step-Sum Cancellation & Single-Exponent Master Identity -/

/-- Cumulative 3-adic step sum $S_K = \sum_{r=0}^{K-1} (3 j_r + s_r)$ across $K$ long-exit epochs. -/
def allRungStepSum (j s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => allRungStepSum j s K + (3 * j K + s K)

/-- Cumulative 2-adic step sum $E_K = \sum_{r=0}^{K-1} (3 j_{r+1} + s_r)$ across $K$ long-exit epochs. -/
def allRungTwoExp (j s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => allRungTwoExp j s K + (3 * j (K + 1) + s K)

/-- Cumulative all-rung defect $\widetilde{\Delta}_K$ in the single-exponent $W_r = 2^{3 j_r} V_r$ coordinate. -/
def allRungDefectAcc (j s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 =>
      3 ^ (3 * j K + s K) * allRungDefectAcc j s K +
        2 ^ (allRungStepSum j s K + 3 * j K) * (3 ^ (s K - 3) - 2 ^ (s K - 3))

/-- **Exact Exponent Cancellation Identity (`allRungTwoExp_add_three_mul_eq`, Track 1.1)**:
For arbitrary sequences `j, s : ℕ → ℕ` and every horizon `K : ℕ`,
`allRungTwoExp j s K + 3 * j 0 = allRungStepSum j s K + 3 * j K`. -/
theorem allRungTwoExp_add_three_mul_eq (j s : ℕ → ℕ) (K : ℕ) :
    allRungTwoExp j s K + 3 * j 0 = allRungStepSum j s K + 3 * j K := by
  induction K with
  | zero => simp [allRungTwoExp, allRungStepSum]
  | succ K ih =>
      simp only [allRungTwoExp, allRungStepSum]
      omega

/-- **Single-Exponent $W$-Recurrence (`allRung_W_recurrence`, Track 1.1 & F1)**:
If `2^(3 * j (r + 1) + s r) * V (r + 1) + (3^(s r - 3) - 2^(s r - 3)) = 3^(3 * j r + s r) * V r`,
then setting `W k = 2^(3 * j k) * V k` satisfies the single-exponent recurrence
`2^(3 * j r + s r) * W (r + 1) + 2^(3 * j r) * (3^(s r - 3) - 2^(s r - 3)) = 3^(3 * j r + s r) * W r`. -/
theorem allRung_W_recurrence {V j s : ℕ → ℕ} {r : ℕ}
    (hrec : 2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
      3 ^ (3 * j r + s r) * V r) :
    let W := fun k => 2 ^ (3 * j k) * V k
    2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
      3 ^ (3 * j r + s r) * W r := by
  intro W
  dsimp [W]
  have hmul := congrArg (fun x => 2 ^ (3 * j r) * x) hrec
  dsimp at hmul
  calc
    2 ^ (3 * j r + s r) * (2 ^ (3 * j (r + 1)) * V (r + 1)) +
        2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3))
      = 2 ^ (3 * j r) *
          (2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3))) := by
        simp only [Nat.pow_add]
        ring
    _ = 2 ^ (3 * j r) * (3 ^ (3 * j r + s r) * V r) := hmul
    _ = 3 ^ (3 * j r + s r) * (2 ^ (3 * j r) * V r) := by ring

/-- **Single-Exponent All-Rung Master Identity (`allRung_single_exponent_master_identity`, Track 1.2)**:
Whenever `W` satisfies the single-exponent recurrence for all `r < K`,
`2 ^ (allRungStepSum j s K) * W K + allRungDefectAcc j s K = 3 ^ (allRungStepSum j s K) * W 0`. -/
theorem allRung_single_exponent_master_identity {W j s : ℕ → ℕ} {K : ℕ}
    (hrec : ∀ r < K,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    2 ^ (allRungStepSum j s K) * W K + allRungDefectAcc j s K =
      3 ^ (allRungStepSum j s K) * W 0 := by
  induction K with
  | zero => simp [allRungStepSum, allRungDefectAcc]
  | succ K ih =>
      have ih' := ih (fun r hr => hrec r (by omega))
      have hstep := hrec K (by omega)
      simp only [allRungStepSum, allRungDefectAcc]
      calc
        2 ^ (allRungStepSum j s K + (3 * j K + s K)) * W (K + 1) +
            (3 ^ (3 * j K + s K) * allRungDefectAcc j s K +
              2 ^ (allRungStepSum j s K + 3 * j K) * (3 ^ (s K - 3) - 2 ^ (s K - 3)))
          = 2 ^ (allRungStepSum j s K) *
              (2 ^ (3 * j K + s K) * W (K + 1) +
                2 ^ (3 * j K) * (3 ^ (s K - 3) - 2 ^ (s K - 3))) +
              3 ^ (3 * j K + s K) * allRungDefectAcc j s K := by
            simp only [Nat.pow_add]
            ring
        _ = 2 ^ (allRungStepSum j s K) * (3 ^ (3 * j K + s K) * W K) +
              3 ^ (3 * j K + s K) * allRungDefectAcc j s K := by
            rw [hstep]
        _ = 3 ^ (3 * j K + s K) *
              (2 ^ (allRungStepSum j s K) * W K + allRungDefectAcc j s K) := by
            ring
        _ = 3 ^ (3 * j K + s K) * (3 ^ (allRungStepSum j s K) * W 0) := by
            rw [ih']
        _ = 3 ^ (allRungStepSum j s K + (3 * j K + s K)) * W 0 := by
            simp only [Nat.pow_add]
            ring

/-- Master identity specialized directly to `W r = 2^(3 * j r) * V r`. -/
theorem allRung_single_exponent_master_identity_from_V {V j s : ℕ → ℕ} {K : ℕ}
    (hrec : ∀ r < K,
      2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * V r) :
    let W := fun r => 2 ^ (3 * j r) * V r
    2 ^ (allRungStepSum j s K) * W K + allRungDefectAcc j s K =
      3 ^ (allRungStepSum j s K) * W 0 := by
  intro W
  exact allRung_single_exponent_master_identity (fun r hr => allRung_W_recurrence (hrec r hr))

/-! ## 2. Section A1.1: Sharp $1/27$ Local and Accumulated Telescoping Slack -/

/-- Elementary power inequality `27 * 2^a ≤ 26 * 3^a` for all `1 ≤ a`. -/
theorem twenty_seven_mul_two_pow_le_twenty_six_mul_three_pow {a : ℕ} (ha : 1 ≤ a) :
    27 * 2 ^ a ≤ 26 * 3 ^ a := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k + 1 := ⟨a - 1, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
      have h1 : 27 * 2 ^ (k + 2) = 2 * (27 * 2 ^ (k + 1)) := by
        rw [Nat.pow_succ]
        ring
      have h2 : 26 * 3 ^ (k + 2) = 3 * (26 * 3 ^ (k + 1)) := by
        rw [Nat.pow_succ]
        ring
      omega

/-- **Exact Local $27$-Slack Decomposition (`allRung_local_twentySeven_slack_identity`, Section A1.1)**:
For every `j : ℕ` and `4 ≤ s`, setting `a = 3 * j + s` and `u = 2^(3 * j) * (3^(s - 3) - 2^(s - 3))`:
1. `27 * u + 3 ^ s * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (a - 3) = 3 ^ a - 2 ^ a`,
2. `1 ≤ u`,
3. `0 < 3 ^ s * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (a - 3)`, and
4. `27 * u < 3 ^ a - 2 ^ a` (and `u < 3 ^ a - 2 ^ a`). -/
theorem allRung_local_twentySeven_slack_identity (j : ℕ) {s : ℕ} (hs : 4 ≤ s) :
    let a := 3 * j + s
    let u := 2 ^ (3 * j) * (3 ^ (s - 3) - 2 ^ (s - 3))
    27 * u + 3 ^ s * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (a - 3) = 3 ^ a - 2 ^ a ∧
      1 ≤ u ∧
      0 < 3 ^ s * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (a - 3) ∧
      27 * u < 3 ^ a - 2 ^ a := by
  intro a u
  dsimp [a, u]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k + 4 := ⟨s - 4, by omega⟩
  have hsub1 : k + 4 - 3 = k + 1 := by omega
  have hsub2 : 3 * j + (k + 4) - 3 = 3 * j + (k + 1) := by omega
  rw [hsub1, hsub2]
  have hle_k : 2 ^ (k + 1) ≤ 3 ^ (k + 1) := Nat.pow_le_pow_left (by decide) (k + 1)
  have hlt_k : 2 ^ (k + 1) < 3 ^ (k + 1) := Nat.pow_lt_pow_left (by decide) (by omega)
  have hle_j : 2 ^ (3 * j) ≤ 3 ^ (3 * j) := Nat.pow_le_pow_left (by decide) (3 * j)
  have hle_a : 2 ^ (3 * j + (k + 4)) ≤ 3 ^ (3 * j + (k + 4)) :=
    Nat.pow_le_pow_left (by decide) (3 * j + (k + 4))
  have hid :
      27 * (2 ^ (3 * j) * (3 ^ (k + 1) - 2 ^ (k + 1))) +
          3 ^ (k + 4) * (3 ^ (3 * j) - 2 ^ (3 * j)) +
          19 * 2 ^ (3 * j + (k + 1)) =
        3 ^ (3 * j + (k + 4)) - 2 ^ (3 * j + (k + 4)) := by
    zify [hle_k, hle_j, hle_a]
    simp only [pow_add]
    ring
  have hu_pos : 1 ≤ 2 ^ (3 * j) * (3 ^ (k + 1) - 2 ^ (k + 1)) := by
    have h1 : 1 ≤ 2 ^ (3 * j) := Nat.one_le_pow (3 * j) 2 (by decide)
    have h2 : 1 ≤ 3 ^ (k + 1) - 2 ^ (k + 1) := by omega
    exact Nat.mul_le_mul h1 h2
  have hslack_pos : 0 < 3 ^ (k + 4) * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (3 * j + (k + 1)) := by
    have hpow2 : 0 < 2 ^ (3 * j + (k + 1)) := Nat.pow_pos (by decide)
    omega
  refine ⟨hid, hu_pos, hslack_pos, ?_⟩
  omega

/-- **Strict Accumulated $27$-Slack Inequality (`allRungDefectAcc_twentySeven_strict_bound`, Section A1.1)**:
For every `1 ≤ K` and any sequences `j, s : ℕ → ℕ` with `∀ r < K, 4 ≤ s r`:
1. `1 ≤ allRungDefectAcc j s K`,
2. `27 * allRungDefectAcc j s K < 3 ^ (allRungStepSum j s K) - 2 ^ (allRungStepSum j s K)`, and
3. `allRungDefectAcc j s K ≤ 3 ^ (allRungStepSum j s K) - 2 ^ (allRungStepSum j s K)`. -/
theorem allRungDefectAcc_twentySeven_strict_bound (j : ℕ → ℕ) {s : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hs : ∀ r < K, 4 ≤ s r) :
    1 ≤ allRungDefectAcc j s K ∧
      27 * allRungDefectAcc j s K <
        3 ^ (allRungStepSum j s K) - 2 ^ (allRungStepSum j s K) ∧
      allRungDefectAcc j s K ≤
        3 ^ (allRungStepSum j s K) - 2 ^ (allRungStepSum j s K) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, K = m + 1 := ⟨K - 1, by omega⟩
  induction m with
  | zero =>
      have hloc := allRung_local_twentySeven_slack_identity (j 0) (hs 0 (by omega))
      simp only [allRungDefectAcc, allRungStepSum, Nat.zero_add, Nat.pow_zero, Nat.mul_zero]
      refine ⟨hloc.2.1, hloc.2.2.2, by omega⟩
  | succ m ih =>
      have ihm := ih (by omega) (fun r hr => hs r (by omega))
      have hloc := allRung_local_twentySeven_slack_identity (j (m + 1)) (hs (m + 1) (by omega))
      set S := allRungStepSum j s (m + 1)
      set a := 3 * j (m + 1) + s (m + 1)
      set Δ := allRungDefectAcc j s (m + 1)
      set u := 2 ^ (3 * j (m + 1)) * (3 ^ (s (m + 1) - 3) - 2 ^ (s (m + 1) - 3))
      have hS_le : 2 ^ S ≤ 3 ^ S := Nat.pow_le_pow_left (by decide) S
      have ha_le : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) a
      have h3a_pos : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
      have h2S_pos : 1 ≤ 2 ^ S := Nat.one_le_pow S 2 (by decide)
      have hmul1 : 3 ^ a * (27 * Δ) + 3 ^ a ≤ 3 ^ a * (3 ^ S - 2 ^ S) := by
        have hlt : 27 * Δ + 1 ≤ 3 ^ S - 2 ^ S := ihm.2.1
        have hm := Nat.mul_le_mul_left (3 ^ a) hlt
        linarith
      have hmul2 : 2 ^ S * (27 * u) + 2 ^ S ≤ 2 ^ S * (3 ^ a - 2 ^ a) := by
        have hlt : 27 * u + 1 ≤ 3 ^ a - 2 ^ a := hloc.2.2.2
        have hm := Nat.mul_le_mul_left (2 ^ S) hlt
        linarith
      have htelescope :
          3 ^ a * (3 ^ S - 2 ^ S) + 2 ^ S * (3 ^ a - 2 ^ a) =
            3 ^ (S + a) - 2 ^ (S + a) := by
        have hSa_le : 2 ^ (S + a) ≤ 3 ^ (S + a) := Nat.pow_le_pow_left (by decide) (S + a)
        zify [hS_le, ha_le, hSa_le]
        simp only [pow_add]
        ring
      have hstep_Δ : allRungDefectAcc j s (m + 2) = 3 ^ a * Δ + 2 ^ S * u := by
        simp only [allRungDefectAcc, S, a, Δ, u, Nat.pow_add]
        ring
      have hstep_S : allRungStepSum j s (m + 2) = S + a := rfl
      rw [hstep_Δ, hstep_S]
      have hpos : 1 ≤ 3 ^ a * Δ + 2 ^ S * u := by
        have h1 : 1 ≤ 2 ^ S * u := Nat.mul_le_mul h2S_pos hloc.2.1
        omega
      have hstrict : 27 * (3 ^ a * Δ + 2 ^ S * u) < 3 ^ (S + a) - 2 ^ (S + a) := by
        have h27 : 27 * (3 ^ a * Δ + 2 ^ S * u) = 3 ^ a * (27 * Δ) + 2 ^ S * (27 * u) := by ring
        omega
      exact ⟨hpos, hstrict, by omega⟩

/-- Compatibility wrapper for Track 1 deliverable 4 (`allRungDefectAcc_pos_and_le_three_pow_sub_two_pow`). -/
theorem allRungDefectAcc_pos_and_le_three_pow_sub_two_pow (j : ℕ → ℕ) {s : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hs : ∀ r < K, 4 ≤ s r) :
    1 ≤ allRungDefectAcc j s K ∧
      allRungDefectAcc j s K ≤ 3 ^ (allRungStepSum j s K) - 2 ^ (allRungStepSum j s K) := by
  have h := allRungDefectAcc_twentySeven_strict_bound j hK hs
  exact ⟨h.1, h.2.2⟩

/-! ## 3. Section A1.2: Universal Constant of Motion, Two-Index Tail Gap & Strict Modular Pinning -/

/-- **Universal All-Rung Constant of Motion & Dual Remainder Law
(`all_rung_constant_of_motion_and_dual_remainder`, Track 1.5 & Section A1.2)**:
For `1 ≤ K`, `1 ≤ W 0`, and `∀ r < K, 4 ≤ s r`, setting `S_K = allRungStepSum j s K` and
`Δ_K = allRungDefectAcc j s K`:
1. `(2 ^ S_K * W K) / 3 ^ S_K = W 0 - 1`,
2. `(2 ^ S_K * W K) % 3 ^ S_K = 3 ^ S_K - Δ_K`,
3. `2 ^ S_K * W K < 3 ^ S_K * W 0`,
4. `27 * ((2 ^ S_K * W K) % 3 ^ S_K) > 26 * 3 ^ S_K + 2 ^ S_K` (and `65 * (...) ≥ 62 * 3 ^ S_K`), and
5. `(3 ^ S_K * W 0) / 2 ^ S_K = W K + Δ_K / 2 ^ S_K` and `(3 ^ S_K * W 0) % 2 ^ S_K = Δ_K % 2 ^ S_K`. -/
theorem all_rung_constant_of_motion_and_dual_remainder {W j s : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hW0 : 1 ≤ W 0) (hs : ∀ r < K, 4 ≤ s r)
    (hrec : ∀ r < K,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    let S_K := allRungStepSum j s K
    let Δ_K := allRungDefectAcc j s K
    (2 ^ S_K * W K) / 3 ^ S_K = W 0 - 1 ∧
      (2 ^ S_K * W K) % 3 ^ S_K = 3 ^ S_K - Δ_K ∧
      2 ^ S_K * W K < 3 ^ S_K * W 0 ∧
      27 * ((2 ^ S_K * W K) % 3 ^ S_K) > 26 * 3 ^ S_K + 2 ^ S_K ∧
      65 * ((2 ^ S_K * W K) % 3 ^ S_K) ≥ 62 * 3 ^ S_K ∧
      (3 ^ S_K * W 0) / 2 ^ S_K = W K + Δ_K / 2 ^ S_K ∧
      (3 ^ S_K * W 0) % 2 ^ S_K = Δ_K % 2 ^ S_K := by
  intro S_K Δ_K
  have hmaster : 2 ^ S_K * W K + Δ_K = 3 ^ S_K * W 0 :=
    allRung_single_exponent_master_identity hrec
  have hbounds := allRungDefectAcc_twentySeven_strict_bound j hK hs
  change 1 ≤ Δ_K ∧ 27 * Δ_K < 3 ^ S_K - 2 ^ S_K ∧ Δ_K ≤ 3 ^ S_K - 2 ^ S_K at hbounds
  have h2_pos : 0 < 2 ^ S_K := Nat.pow_pos (by decide)
  have h3_pos : 0 < 3 ^ S_K := Nat.pow_pos (by decide)
  have hle_pow : 2 ^ S_K ≤ 3 ^ S_K := Nat.pow_le_pow_left (by decide) S_K
  have hΔ_lt : Δ_K < 3 ^ S_K := by omega
  have hW0_split : 3 ^ S_K * W 0 = 3 ^ S_K * (W 0 - 1) + 3 ^ S_K := by
    have h1 : W 0 = (W 0 - 1) + 1 := by omega
    conv_lhs => rw [h1]
    ring
  have hdecomp : 2 ^ S_K * W K = (3 ^ S_K - Δ_K) + 3 ^ S_K * (W 0 - 1) := by
    omega
  have hrem_lt : 3 ^ S_K - Δ_K < 3 ^ S_K := by omega
  have hdiv3 : (2 ^ S_K * W K) / 3 ^ S_K = W 0 - 1 := by
    rw [hdecomp, Nat.add_mul_div_left _ _ h3_pos, Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
  have hmod3 : (2 ^ S_K * W K) % 3 ^ S_K = 3 ^ S_K - Δ_K := by
    rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
  have hdiv2 : (3 ^ S_K * W 0) / 2 ^ S_K = W K + Δ_K / 2 ^ S_K := by
    rw [← hmaster, Nat.add_comm (2 ^ S_K * W K) Δ_K, Nat.add_mul_div_left _ _ h2_pos, Nat.add_comm]
  have hmod2 : (3 ^ S_K * W 0) % 2 ^ S_K = Δ_K % 2 ^ S_K := by
    rw [← hmaster, Nat.add_comm (2 ^ S_K * W K) Δ_K, Nat.add_mul_mod_self_left]
  refine ⟨hdiv3, hmod3, by omega, ?_, ?_, hdiv2, hmod2⟩
  · rw [hmod3]
    omega
  · rw [hmod3]
    omega

/-- Shift additivity of `allRungStepSum`:
`allRungStepSum j s (K + D) = allRungStepSum j s K + allRungStepSum (fun t => j (K + t)) (fun t => s (K + t)) D`. -/
theorem allRungStepSum_add_shift (j s : ℕ → ℕ) (K D : ℕ) :
    allRungStepSum j s (K + D) =
      allRungStepSum j s K + allRungStepSum (fun t => j (K + t)) (fun t => s (K + t)) D := by
  induction D with
  | zero => simp [allRungStepSum]
  | succ D ih =>
      rw [← Nat.add_assoc, allRungStepSum, ih]
      simp only [allRungStepSum]
      omega

/-- **Two-Index Tail-Gap Identity & Strict $27$-Slack Pinning (`allRung_tailGap_twentySeven_strict_bound`,
Section A1.2 & F2.3)**:
For any `K < M` and `∀ r < M, 4 ≤ s r`, let `d = allRungStepSum j s M - allRungStepSum j s K` and
`G = allRungDefectAcc (fun t => j (K + t)) (fun t => s (K + t)) (M - K)`. Then:
1. `2 ^ d * W M + G = 3 ^ d * W K` (so `3 ^ d * W K - 2 ^ d * W M = G`),
2. `1 ≤ G` and `27 * G < 3 ^ d - 2 ^ d` (hence `65 * G ≤ 3 ^ (d + 1)`), and
3. if `1 ≤ W K`, then
   `(2 ^ d * W M) / 3 ^ d = W K - 1`,
   `(2 ^ d * W M) % 3 ^ d = 3 ^ d - G`,
   `27 * ((2 ^ d * W M) % 3 ^ d) > 26 * 3 ^ d + 2 ^ d`, and
   `65 * ((2 ^ d * W M) % 3 ^ d) ≥ 62 * 3 ^ d`. -/
theorem allRung_tailGap_twentySeven_strict_bound {W j s : ℕ → ℕ} {K M : ℕ}
    (hKM : K < M) (hs : ∀ r < M, 4 ≤ s r)
    (hrec : ∀ r < M,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    let j' := fun t => j (K + t)
    let s' := fun t => s (K + t)
    let d := allRungStepSum j s M - allRungStepSum j s K
    let G := allRungDefectAcc j' s' (M - K)
    2 ^ d * W M + G = 3 ^ d * W K ∧
      3 ^ d * W K - 2 ^ d * W M = G ∧
      1 ≤ G ∧
      27 * G < 3 ^ d - 2 ^ d ∧
      65 * G ≤ 3 ^ (d + 1) ∧
      (1 ≤ W K →
        (2 ^ d * W M) / 3 ^ d = W K - 1 ∧
        (2 ^ d * W M) % 3 ^ d = 3 ^ d - G ∧
        27 * ((2 ^ d * W M) % 3 ^ d) > 26 * 3 ^ d + 2 ^ d ∧
        65 * ((2 ^ d * W M) % 3 ^ d) ≥ 62 * 3 ^ d) := by
  intro j' s' d G
  set W' := fun t => W (K + t)
  have hMK_pos : 1 ≤ M - K := by omega
  have hM_eq : K + (M - K) = M := by omega
  have hd_eq : d = allRungStepSum j' s' (M - K) := by
    have hshift := allRungStepSum_add_shift j s K (M - K)
    rw [hM_eq] at hshift
    dsimp [d, j', s']
    rw [hshift]
    omega
  have hs' : ∀ t < M - K, 4 ≤ s' t := fun t ht => hs (K + t) (by omega)
  have hrec' : ∀ t < M - K,
      2 ^ (3 * j' t + s' t) * W' (t + 1) + 2 ^ (3 * j' t) * (3 ^ (s' t - 3) - 2 ^ (s' t - 3)) =
        3 ^ (3 * j' t + s' t) * W' t := by
    intro t ht
    have h := hrec (K + t) (by omega)
    simpa [j', s', W', Nat.add_assoc] using h
  have hmaster' := allRung_single_exponent_master_identity hrec'
  have hWM : W' (M - K) = W M := by dsimp [W']; rw [hM_eq]
  have hWK : W' 0 = W K := rfl
  rw [← hd_eq, hWM, hWK] at hmaster'
  have hbounds := allRungDefectAcc_twentySeven_strict_bound j' hMK_pos hs'
  rw [← hd_eq] at hbounds
  change 1 ≤ G ∧ 27 * G < 3 ^ d - 2 ^ d ∧ G ≤ 3 ^ d - 2 ^ d at hbounds
  have h2d_pos : 0 < 2 ^ d := Nat.pow_pos (by decide)
  have hle_pow : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
  have h3d1 : 3 ^ (d + 1) = 3 * 3 ^ d := by rw [Nat.pow_succ]; ring
  refine ⟨hmaster', by omega, hbounds.1, hbounds.2.1, by rw [h3d1]; omega, ?_⟩
  intro hWK_pos
  have hcom := all_rung_constant_of_motion_and_dual_remainder hMK_pos
    (by simpa [hWK] using hWK_pos) hs' hrec'
  rw [← hd_eq, hWM, hWK] at hcom
  exact ⟨hcom.1, hcom.2.1, hcom.2.2.2.1, hcom.2.2.2.2.1⟩

/-- Direct modular lower-bound wrapper (`allRung_pinning_mod_strict_lower`, Section A1.2 & F2.5). -/
theorem allRung_pinning_mod_strict_lower {W j s : ℕ → ℕ} {K M : ℕ}
    (hKM : K < M) (hWK : 1 ≤ W K) (hs : ∀ r < M, 4 ≤ s r)
    (hrec : ∀ r < M,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    let d := allRungStepSum j s M - allRungStepSum j s K
    27 * ((2 ^ d * W M) % 3 ^ d) > 26 * 3 ^ d + 2 ^ d ∧
      65 * ((2 ^ d * W M) % 3 ^ d) ≥ 62 * 3 ^ d := by
  intro d
  have h := (allRung_tailGap_twentySeven_strict_bound hKM hs hrec).2.2.2.2.2 hWK
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- **Strict Growth of $W_r$ Along Positive All-Long Chains (`allRung_W_strictMono`, Section A1.2)**:
Whenever `1 ≤ W 0`, `4 ≤ s r`, and `W` satisfies the single-exponent recurrence for all `r < K`,
`1 ≤ W r` for all `r ≤ K` and `W r < W (r + 1)` for all `r < K`. -/
theorem allRung_W_strictMono {W j s : ℕ → ℕ} {K : ℕ}
    (hW0 : 1 ≤ W 0) (hs : ∀ r < K, 4 ≤ s r)
    (hrec : ∀ r < K,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r) :
    (∀ r ≤ K, 1 ≤ W r) ∧ (∀ r < K, W r < W (r + 1)) := by
  have hstep_lt : ∀ r < K, 1 ≤ W r → W r < W (r + 1) := by
    intro r hr hWr
    have hloc := allRung_local_twentySeven_slack_identity (j r) (hs r hr)
    set a := 3 * j r + s r
    set u := 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3))
    have hstep := hrec r hr
    change 2 ^ a * W (r + 1) + u = 3 ^ a * W r at hstep
    have hu_lt : u < 3 ^ a - 2 ^ a := by
      have h27 : 27 * u < 3 ^ a - 2 ^ a := hloc.2.2.2
      omega
    have ha_le : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) a
    have hmul : (3 ^ a - 2 ^ a) * 1 ≤ (3 ^ a - 2 ^ a) * W r :=
      Nat.mul_le_mul_left (3 ^ a - 2 ^ a) hWr
    have hdist : (3 ^ a - 2 ^ a) * W r + 2 ^ a * W r = 3 ^ a * W r := by
      rw [← Nat.add_mul, Nat.sub_add_cancel ha_le]
    have h2a_lt : 2 ^ a * W r < 2 ^ a * W (r + 1) := by omega
    exact (Nat.mul_lt_mul_left (Nat.pow_pos (by decide))).mp h2a_lt
  have hpos : ∀ r ≤ K, 1 ≤ W r := by
    intro r hr
    induction r with
    | zero => exact hW0
    | succ r ih =>
        have hlt := hstep_lt r (by omega) (ih (by omega))
        omega
  exact ⟨hpos, fun r hr => hstep_lt r hr (hpos r (by omega))⟩

/-! ## 4. Section A1.4: Optimal Bounded-Rung Bellman Constants $C_H$ -/

/-- **Optimal Bounded-Rung Local Bellman Inequality (`bounded_rung_bellman_constant_optimality`,
Section A1.4)**:
Whenever `4 ≤ s ≤ H`, setting `a = 3 * j + s` and `u = 2^(3 * j) * (3^(s - 3) - 2^(s - 3))`:
1. `(3 ^ H - 2 ^ H) * u ≤ (3 ^ (H - 3) - 2 ^ (H - 3)) * (3 ^ a - 2 ^ a)`, and
2. at `j = 0, s = H`, equality holds:
   `(3 ^ H - 2 ^ H) * (3 ^ (H - 3) - 2 ^ (H - 3)) = (3 ^ (H - 3) - 2 ^ (H - 3)) * (3 ^ H - 2 ^ H)`. -/
theorem bounded_rung_bellman_constant_optimality (j : ℕ) {s H : ℕ}
    (hs : 4 ≤ s) (hsH : s ≤ H) :
    let a := 3 * j + s
    let u := 2 ^ (3 * j) * (3 ^ (s - 3) - 2 ^ (s - 3))
    (3 ^ H - 2 ^ H) * u ≤ (3 ^ (H - 3) - 2 ^ (H - 3)) * (3 ^ a - 2 ^ a) := by
  intro a u
  dsimp [a, u]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k + 4 := ⟨s - 4, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, H = (k + 4) + d := ⟨H - (k + 4), by omega⟩
  have hsub1 : k + 4 - 3 = k + 1 := by omega
  have hsub2 : k + 4 + d - 3 = (k + 1) + d := by omega
  rw [hsub1, hsub2]
  have hle_k : 2 ^ (k + 1) ≤ 3 ^ (k + 1) := Nat.pow_le_pow_left (by decide) (k + 1)
  have hle_kd : 2 ^ ((k + 1) + d) ≤ 3 ^ ((k + 1) + d) :=
    Nat.pow_le_pow_left (by decide) ((k + 1) + d)
  have hle_H : 2 ^ (k + 4 + d) ≤ 3 ^ (k + 4 + d) :=
    Nat.pow_le_pow_left (by decide) (k + 4 + d)
  have hle_a : 2 ^ (3 * j + (k + 4)) ≤ 3 ^ (3 * j + (k + 4)) :=
    Nat.pow_le_pow_left (by decide) (3 * j + (k + 4))
  have hle_d : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
  have hle_j : 2 ^ (3 * j) ≤ 3 ^ (3 * j) := Nat.pow_le_pow_left (by decide) (3 * j)
  have hdiff :
      (3 ^ ((k + 1) + d) - 2 ^ ((k + 1) + d)) * (3 ^ (3 * j + (k + 4)) - 2 ^ (3 * j + (k + 4))) =
        (3 ^ (k + 4 + d) - 2 ^ (k + 4 + d)) * (2 ^ (3 * j) * (3 ^ (k + 1) - 2 ^ (k + 1))) +
          27 * 3 ^ (k + 1) * (3 ^ ((k + 1) + d) - 2 ^ ((k + 1) + d)) * (3 ^ (3 * j) - 2 ^ (3 * j)) +
          19 * 2 ^ (3 * j) * 2 ^ (k + 1) * 3 ^ (k + 1) * (3 ^ d - 2 ^ d) := by
    zify [hle_k, hle_kd, hle_H, hle_a, hle_d, hle_j]
    simp only [pow_add]
    ring
  omega

/-- **Accumulated Bounded-Rung Defect Inequality (`bounded_rung_accumulated_defect_bound`, Section A1.4)**:
Whenever `4 ≤ s r ≤ H` for all `r < K`,
`(3 ^ H - 2 ^ H) * allRungDefectAcc j s K ≤ (3 ^ (H - 3) - 2 ^ (H - 3)) * (3 ^ S_K - 2 ^ S_K)`. -/
theorem bounded_rung_accumulated_defect_bound {j s : ℕ → ℕ} {K H : ℕ}
    (hs : ∀ r < K, 4 ≤ s r ∧ s r ≤ H) :
    (3 ^ H - 2 ^ H) * allRungDefectAcc j s K ≤
      (3 ^ (H - 3) - 2 ^ (H - 3)) *
        (3 ^ (allRungStepSum j s K) - 2 ^ (allRungStepSum j s K)) := by
  induction K with
  | zero => simp [allRungDefectAcc, allRungStepSum]
  | succ K ih =>
      have ih' := ih (fun r hr => hs r (by omega))
      rcases hs K (by omega) with ⟨hs4, hsH⟩
      have hloc := bounded_rung_bellman_constant_optimality (j K) hs4 hsH
      set S := allRungStepSum j s K
      set a := 3 * j K + s K
      set Δ := allRungDefectAcc j s K
      set u := 2 ^ (3 * j K) * (3 ^ (s K - 3) - 2 ^ (s K - 3))
      set DH := 3 ^ (H - 3) - 2 ^ (H - 3)
      set MH := 3 ^ H - 2 ^ H
      have hmul1 : 3 ^ a * (MH * Δ) ≤ 3 ^ a * (DH * (3 ^ S - 2 ^ S)) :=
        Nat.mul_le_mul_left (3 ^ a) ih'
      have hmul2 : 2 ^ S * (MH * u) ≤ 2 ^ S * (DH * (3 ^ a - 2 ^ a)) :=
        Nat.mul_le_mul_left (2 ^ S) hloc
      have hS_le : 2 ^ S ≤ 3 ^ S := Nat.pow_le_pow_left (by decide) S
      have ha_le : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) a
      have hSa_le : 2 ^ (S + a) ≤ 3 ^ (S + a) := Nat.pow_le_pow_left (by decide) (S + a)
      have htelescope :
          3 ^ a * (DH * (3 ^ S - 2 ^ S)) + 2 ^ S * (DH * (3 ^ a - 2 ^ a)) =
            DH * (3 ^ (S + a) - 2 ^ (S + a)) := by
        zify [hS_le, ha_le, hSa_le]
        simp only [pow_add]
        ring
      have hstep_Δ :
          MH * allRungDefectAcc j s (K + 1) = 3 ^ a * (MH * Δ) + 2 ^ S * (MH * u) := by
        simp only [allRungDefectAcc, S, a, Δ, u, Nat.pow_add]
        ring
      have hstep_S : allRungStepSum j s (K + 1) = S + a := rfl
      rw [hstep_Δ, hstep_S]
      omega

/-- Exact rational values of the bounded-rung Bellman constants $C_4 = 1/65, C_5 = 5/211, C_6 = 1/35$. -/
theorem bounded_rung_bellman_constants_four_five_six :
    ((3 : ℚ) ^ (4 - 3) - 2 ^ (4 - 3)) / (3 ^ 4 - 2 ^ 4) = 1 / 65 ∧
      ((3 : ℚ) ^ (5 - 3) - 2 ^ (5 - 3)) / (3 ^ 5 - 2 ^ 5) = 5 / 211 ∧
      ((3 : ℚ) ^ (6 - 3) - 2 ^ (6 - 3)) / (3 ^ 6 - 2 ^ 6) = 1 / 35 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## 5. Track 1.6: Corrected All-Rung Repeated Epoch-Window $(p, q)$ Cutoff -/

/-- **All-Rung Repeated Epoch-Window $(p, q)$ Cutoff (`all_rung_repeated_epoch_window_pq_cutoff`,
Track 1.6 & Section A0.1)**:
Suppose an $L$-epoch window of parameters `(j, s)` repeats at `r₁` and `r₂`
(`∀ t < L, j (r₁ + t) = j (r₂ + t) ∧ s (r₁ + t) = s (r₂ + t)`), with local window step sum
`d = allRungStepSum (fun t => j (r₁ + t)) (fun t => s (r₁ + t)) L`.
If `W r₁ ≤ W r₂`, then:
1. `2 ^ d * (W (r₂ + L) - W (r₁ + L)) = 3 ^ d * (W r₂ - W r₁)`,
2. `2 ^ d ∣ (W r₂ - W r₁)` and `3 ^ d ∣ (W (r₂ + L) - W (r₁ + L))`, and
3. if `W r₁ < W r₂`, `W 0 < 2 ^ B`, `1 ≤ q`, `3 ^ q ≤ 2 ^ (p + q)`, and the recurrence holds
   up to `r₂ + L`, then `q * d < p * allRungStepSum j s r₂ + q * B`. -/
theorem all_rung_repeated_epoch_window_pq_cutoff {W j s : ℕ → ℕ} {r₁ r₂ L p q B : ℕ}
    (hmatch : ∀ t < L, j (r₁ + t) = j (r₂ + t) ∧ s (r₁ + t) = s (r₂ + t))
    (hrec : ∀ r < max (r₁ + L) (r₂ + L),
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r)
    (hle : W r₁ ≤ W r₂) :
    let d := allRungStepSum (fun t => j (r₁ + t)) (fun t => s (r₁ + t)) L
    2 ^ d * (W (r₂ + L) - W (r₁ + L)) = 3 ^ d * (W r₂ - W r₁) ∧
      (2 ^ d ∣ (W r₂ - W r₁)) ∧
      (3 ^ d ∣ (W (r₂ + L) - W (r₁ + L))) ∧
      (W r₁ < W r₂ → W 0 < 2 ^ B → 1 ≤ q → 3 ^ q ≤ 2 ^ (p + q) →
        q * d < p * allRungStepSum j s r₂ + q * B) := by
  intro d
  set j₁ := fun t => j (r₁ + t)
  set s₁ := fun t => s (r₁ + t)
  set j₂ := fun t => j (r₂ + t)
  set s₂ := fun t => s (r₂ + t)
  have hrec1 : ∀ t < L,
      2 ^ (3 * j₁ t + s₁ t) * W (r₁ + (t + 1)) + 2 ^ (3 * j₁ t) * (3 ^ (s₁ t - 3) - 2 ^ (s₁ t - 3)) =
        3 ^ (3 * j₁ t + s₁ t) * W (r₁ + t) := by
    intro t ht
    simpa [j₁, s₁, Nat.add_assoc] using hrec (r₁ + t) (by omega)
  have hrec2 : ∀ t < L,
      2 ^ (3 * j₁ t + s₁ t) * W (r₂ + (t + 1)) + 2 ^ (3 * j₁ t) * (3 ^ (s₁ t - 3) - 2 ^ (s₁ t - 3)) =
        3 ^ (3 * j₁ t + s₁ t) * W (r₂ + t) := by
    intro t ht
    rcases hmatch t ht with ⟨hj, hs⟩
    have h := hrec (r₂ + t) (by omega)
    rw [← hj, ← hs] at h
    simpa [j₁, s₁, Nat.add_assoc] using h
  have hm1 := allRung_single_exponent_master_identity (W := fun t => W (r₁ + t)) hrec1
  have hm2 := allRung_single_exponent_master_identity (W := fun t => W (r₂ + t)) hrec2
  simp only [Nat.add_zero] at hm1 hm2
  change 2 ^ d * W (r₁ + L) + allRungDefectAcc j₁ s₁ L = 3 ^ d * W r₁ at hm1
  change 2 ^ d * W (r₂ + L) + allRungDefectAcc j₁ s₁ L = 3 ^ d * W r₂ at hm2
  have hle_L : W (r₁ + L) ≤ W (r₂ + L) := by
    have hmul_le : 2 ^ d * W (r₁ + L) ≤ 2 ^ d * W (r₂ + L) := by
      have h3 : 3 ^ d * W r₁ ≤ 3 ^ d * W r₂ := Nat.mul_le_mul_left (3 ^ d) hle
      omega
    exact Nat.le_of_mul_le_mul_left hmul_le (Nat.pow_pos (by decide))
  have hdiff : 2 ^ d * (W (r₂ + L) - W (r₁ + L)) = 3 ^ d * (W r₂ - W r₁) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  have hcop : Nat.Coprime (2 ^ d) (3 ^ d) :=
    (Nat.Coprime.pow_left d (by decide)).pow_right d
  have hdvd2 : 2 ^ d ∣ (W r₂ - W r₁) := by
    refine hcop.dvd_of_dvd_mul_left ?_
    exact ⟨W (r₂ + L) - W (r₁ + L), hdiff.symm⟩
  have hdvd3 : 3 ^ d ∣ (W (r₂ + L) - W (r₁ + L)) := by
    refine hcop.symm.dvd_of_dvd_mul_left ?_
    exact ⟨W r₂ - W r₁, hdiff⟩
  refine ⟨hdiff, hdvd2, hdvd3, ?_⟩
  intro hlt hW0_lt hq hpq
  have hdiff_pos : 0 < W r₂ - W r₁ := by omega
  have h2d_le : 2 ^ d ≤ W r₂ - W r₁ := Nat.le_of_dvd hdiff_pos hdvd2
  have h2d_le_Wr2 : 2 ^ d ≤ W r₂ := by omega
  have hm_r2 := allRung_single_exponent_master_identity (K := r₂) (fun r hr => hrec r (by omega))
  set S₂ := allRungStepSum j s r₂
  have h2S2_Wr2 : 2 ^ S₂ * W r₂ ≤ 3 ^ S₂ * W 0 := by omega
  have h2_comb : 2 ^ (S₂ + d) ≤ 3 ^ S₂ * W 0 := by
    calc
      2 ^ (S₂ + d) = 2 ^ S₂ * 2 ^ d := by rw [Nat.pow_add]
      _ ≤ 2 ^ S₂ * W r₂ := Nat.mul_le_mul_left (2 ^ S₂) h2d_le_Wr2
      _ ≤ 3 ^ S₂ * W 0 := h2S2_Wr2
  have h3S2_lt : 3 ^ S₂ * W 0 < 3 ^ S₂ * 2 ^ B :=
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide))).mpr hW0_lt
  have h2_lt : 2 ^ (S₂ + d) < 3 ^ S₂ * 2 ^ B := lt_of_le_of_lt h2_comb h3S2_lt
  have hpow_q : (2 ^ (S₂ + d)) ^ q < (3 ^ S₂ * 2 ^ B) ^ q :=
    Nat.pow_lt_pow_left h2_lt (by omega)
  have hlhs : (2 ^ (S₂ + d)) ^ q = 2 ^ (q * (S₂ + d)) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have hrhs_le : (3 ^ S₂ * 2 ^ B) ^ q ≤ 2 ^ ((p + q) * S₂ + q * B) := by
    calc
      (3 ^ S₂ * 2 ^ B) ^ q = (3 ^ q) ^ S₂ * 2 ^ (q * B) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm S₂ q, Nat.mul_comm B q,
          Nat.pow_mul]
      _ ≤ (2 ^ (p + q)) ^ S₂ * 2 ^ (q * B) :=
        Nat.mul_le_mul_right (2 ^ (q * B)) (Nat.pow_le_pow_left hpq S₂)
      _ = 2 ^ ((p + q) * S₂ + q * B) := by
        rw [← Nat.pow_mul, ← Nat.pow_add]
  have hpow2_lt : 2 ^ (q * (S₂ + d)) < 2 ^ ((p + q) * S₂ + q * B) := by
    rw [← hlhs]
    exact lt_of_lt_of_le hpow_q hrhs_le
  have hexp_lt : q * (S₂ + d) < (p + q) * S₂ + q * B :=
    (Nat.pow_lt_pow_iff_right (by decide)).mp hpow2_lt
  have hring1 : q * (S₂ + d) = q * S₂ + q * d := by ring
  have hring2 : (p + q) * S₂ + q * B = p * S₂ + q * S₂ + q * B := by ring
  omega

/-! ## 6. Section A0.2: Genuine Seed-149 / 1701 Counterexample & Diagonal $M = K$ Counterexample -/

/-- **Genuine Post-Defect Orbit Counterexample to the Deleted Base-Two Quotient Claim
(`seed_149_window_1701_base_two_quotient_counterexample`, Section A0.2)**:
Starting at odd seed `149`, its first odd block of length `6` lands at `1701`, followed by the
three genuine odd-to-odd long blocks `1701 →(s=4) 8613 →(s=4) 43605 →(s=8) 1117557`.
Along this 3-epoch window (`W = ![449, 2273, 11507, 294911]`, `j = 0`, `s = ![4, 4, 8]`, `S_3 = 16`,
`Δ_3 = 690433`), even though `W 0 = 449 < 2^9 ≤ 2^16`:
- `(3^16 * 449) / 2^16 = 294921 ≠ 294911 = W 3`, and
- `(3^16 * 449) % 2^16 = 35073 ≠ 690433 = Δ_3`,
while the corrected formula `(3^16 * 449) / 2^16 = W 3 + Δ_3 / 2^16` (`294921 = 294911 + 10`) holds. -/
theorem seed_149_window_1701_base_two_quotient_counterexample :
    orbit 149 6 = 1701 ∧
      orbit 1701 4 = 8613 ∧
      orbit 8613 4 = 43605 ∧
      orbit 43605 8 = 1117557 ∧
      19 * 1701 + 9 = 72 * 449 ∧
      19 * 8613 + 9 = 72 * 2273 ∧
      19 * 43605 + 9 = 72 * 11507 ∧
      19 * 1117557 + 9 = 72 * 294911 ∧
      2 ^ 16 * 294911 + 690433 = 3 ^ 16 * 449 ∧
      449 < 2 ^ 9 ∧ 2 ^ 9 ≤ 2 ^ 16 ∧
      (3 ^ 16 * 449) / 2 ^ 16 = 294921 ∧
      294921 ≠ 294911 ∧
      (3 ^ 16 * 449) % 2 ^ 16 = 35073 ∧
      35073 ≠ 690433 ∧
      (3 ^ 16 * 449) / 2 ^ 16 = 294911 + 690433 / 2 ^ 16 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- **Diagonal $M = K$ Modular Pinning Counterexample (`diagonal_M_eq_K_mod_pinning_counterexample`,
Section A0.2 & F2.3)**:
At `M = K` (`d = 0`), `(2^0 * W_K) % 3^0 = 0`, refuting `65 * ((2^d * W_M) % 3^d) ≥ 62 * 3^d`
when `M = K` is permitted instead of `K < M`. -/
theorem diagonal_M_eq_K_mod_pinning_counterexample (W_K : ℕ) :
    (2 ^ 0 * W_K) % 3 ^ 0 = 0 ∧ ¬ (65 * ((2 ^ 0 * W_K) % 3 ^ 0) ≥ 62 * 3 ^ 0) := by
  simp
  omega

end Mahler.AllRungConstantOfMotion
