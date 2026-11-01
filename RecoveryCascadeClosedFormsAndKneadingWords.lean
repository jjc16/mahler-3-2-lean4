import MultiStepQuotientMasterAndFermatGCD

/-!
# Closed-Form Recovery Cascades, $\Sigma_3(2, s_1, s_2)$, and the $19 \Sigma(2, 6, 3^j, 2) = 9 \cdot 27^{j+1} - 2048 \cdot 8^j$ Law

This module formalizes **Outer Loop 5 / 10 (Part IX, Sections O5.1–O5.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O5.1 (Inner Loop 1 / 3) — Pure $s = 3$ Run Formula & Closed Forms for $(2, 6, 3^j)$ and $(2, 6, 3^j, 2)$
   (`constant_three_run_renewalNumerator_nineteen_law`,
   `two_six_three_run_and_next_two_slack_closed_forms`)**:
   - Across any $j$-block run of $s = 3$, `blockSteps (fun _ => 3) j = 3 * j` and
     `19 * renewalNumerator (fun _ => 3) j = 8 * (27 ^ j - 8 ^ j)`.
   - Because $19 \cdot 3^6 - 216 \cdot 2^6 = 27$, across any prefix $(2, 6, \underbrace{3, \dots, 3}_j)$:
     `19 * renewalIntSlack s (2 + j) = 27 ^ (j + 1) + 4096 * 8 ^ j`
     (recovering $\Sigma_2 = 217$, $\Sigma_3 = 1763$, $\Sigma_4 = 14833$ at $j = 0, 1, 2$).
   - If the next block $s(2 + j) = 2$, then:
     `19 * renewalIntSlack s (3 + j) = 9 * 27 ^ (j + 1) - 2048 * 8 ^ j`
     (recovering $\Sigma_5 = 2425$ at $j = 2$).

2. **Section O5.2 (Inner Loop 2 / 3) — Three-Block $(2, s_1, s_2)$ Slack Formula & $(2, 6, s_2)$ Escape Dichotomy
   (`three_block_two_s1_s2_slack_formula`, `three_block_two_six_s2_escape_iff_s2_le_two`)**:
   - Across any 3-block prefix with $s_0 = 2$:
     `renewalIntSlack s 3 = (3 : ℤ) ^ (s 1 + s 2) - 8 * (2 : ℤ) ^ (s 1) * (3 : ℤ) ^ (s 2) - 8 * (2 : ℤ) ^ (s 1 + s 2)`.
   - At $s_1 = 6$, `renewalIntSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 512 * (2 : ℤ) ^ (s 2)` and
     `2 * renewalNumerator s 3 ≥ 3 ^ (blockSteps s 3) ↔ s 2 ≤ 2`.

3. **Section O5.3 (Inner Loop 3 / 3) — Mandatory $j \ge 2$ Neutral Waiting Time in $(2, 6, 3^j, 2)$
   (`two_six_three_pow_two_escape_iff_j_le_one`)**:
   - Along any prefix $(2, 6, \underbrace{3, \dots, 3}_j, 2)$,
     `2 * renewalNumerator s (3 + j) ≥ 3 ^ (blockSteps s (3 + j)) ↔ j ≤ 1`,
     proving unconditionally that $(2, 6, 2)$ ($j = 0$, $19 \Sigma_3 = -1805$) and $(2, 6, 3, 2)$
     ($j = 1$, $19 \Sigma_4 = -9823$) trigger the finite renewal escape certificate, whereas $j \ge 2$
     keeps $\Sigma_{3+j} > 0$.
-/

namespace Mahler.RecoveryCascadeClosedForms

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

/-! ## 1. Section O5.1: Pure $s = 3$ Run Formula & Closed Forms for $(2, 6, 3^j)$ and $(2, 6, 3^j, 2)$ -/

/-- **Pure $s = 3$ Run Renewal Numerator Law (`constant_three_run_renewalNumerator_nineteen_law`,
Section O5.1)**:
For any sequence `s'` with `∀ t < j, s' t = 3`:
1. `blockSteps s' j = 3 * j`, and
2. `19 * renewalNumerator s' j = 8 * (27 ^ j - 8 ^ j)`. -/
theorem constant_three_run_renewalNumerator_nineteen_law {s' : ℕ → ℕ} {j : ℕ}
    (hs' : ∀ t < j, s' t = 3) :
    blockSteps s' j = 3 * j ∧
      19 * renewalNumerator s' j = 8 * (27 ^ j - 8 ^ j) := by
  induction j with
  | zero => simp [blockSteps, renewalNumerator]
  | succ j ih =>
      rcases ih (fun t ht => hs' t (by omega)) with ⟨hT, hA⟩
      have hj : s' j = 3 := hs' j (by omega)
      have hT_succ : blockSteps s' (j + 1) = 3 * (j + 1) := by
        simp only [blockSteps, hT, hj]
        omega
      refine ⟨hT_succ, ?_⟩
      have hA_succ : renewalNumerator s' (j + 1) = 27 * renewalNumerator s' j + 8 * 8 ^ j := by
        simp only [renewalNumerator, hT_succ, hj]
        have hpow8 : 2 ^ (3 * (j + 1)) = 8 * 8 ^ j := by
          calc
            2 ^ (3 * (j + 1)) = (2 ^ 3) ^ j * 2 ^ 3 := by
              rw [show 3 * (j + 1) = 3 * j + 3 by omega, Nat.pow_add, Nat.pow_mul]
            _ = 8 * 8 ^ j := by ring
        rw [hpow8]
        ring
      have hle_j : 8 ^ j ≤ 27 ^ j := Nat.pow_le_pow_left (by decide) j
      have hle_j1 : 8 ^ (j + 1) ≤ 27 ^ (j + 1) := Nat.pow_le_pow_left (by decide) (j + 1)
      have hmul : 19 * renewalNumerator s' (j + 1) = 27 * (19 * renewalNumerator s' j) + 152 * 8 ^ j := by
        rw [hA_succ]
        ring
      rw [hmul, hA]
      zify [hle_j, hle_j1]
      simp only [pow_succ]
      ring

/-- **Closed Forms for $(2, 6, 3^j)$ and $(2, 6, 3^j, 2)$ Renewal Slack
(`two_six_three_run_and_next_two_slack_closed_forms`, Section O5.1)**:
Suppose `s 0 = 2`, `s 1 = 6`, and `∀ t < j, s (2 + t) = 3`. Then:
1. `blockSteps s (2 + j) = 8 + 3 * j`,
2. `19 * renewalIntSlack s (2 + j) = 27 ^ (j + 1) + 4096 * 8 ^ j`, and
3. if `s (2 + j) = 2`, then `blockSteps s (2 + j + 1) = 10 + 3 * j` and
   `19 * renewalIntSlack s (2 + j + 1) = 9 * 27 ^ (j + 1) - 2048 * 8 ^ j`. -/
theorem two_six_three_run_and_next_two_slack_closed_forms {s : ℕ → ℕ} {j : ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs3 : ∀ t < j, s (2 + t) = 3) :
    blockSteps s (2 + j) = 8 + 3 * j ∧
      19 * renewalIntSlack s (2 + j) = (27 : ℤ) ^ (j + 1) + 4096 * (8 : ℤ) ^ j ∧
      (s (2 + j) = 2 →
        blockSteps s (2 + j + 1) = 10 + 3 * j ∧
          19 * renewalIntSlack s (2 + j + 1) = 9 * (27 : ℤ) ^ (j + 1) - 2048 * (8 : ℤ) ^ j) := by
  have h2 := two_block_two_s1_renewalNumerator_and_slack hs0
  have hT2 : blockSteps s 2 = 8 := by rw [h2.1, hs1]
  have hS2 : renewalIntSlack s 2 = 217 := by
    rw [h2.2.2, hs1]
    norm_num
  set s' := fun t => s (2 + t)
  rcases constant_three_run_renewalNumerator_nineteen_law hs3 with ⟨hT_run, hA_run⟩
  have hshift := blockSteps_add_shift s 2 j
  rw [hT2, hT_run] at hshift
  have hcoc := (renewalIntSlack_step_and_cocycle s 0 2 j).2.2
  rw [hT2, hS2, hT_run] at hcoc
  have hle_j : 8 ^ j ≤ 27 ^ j := Nat.pow_le_pow_left (by decide) j
  have hA_run_z : 19 * (renewalNumerator s' j : ℤ) = 8 * ((27 : ℤ) ^ j - (8 : ℤ) ^ j) := by
    zify [hle_j] at hA_run
    exact_mod_cast hA_run
  have h3_3j : (3 : ℤ) ^ (3 * j) = (27 : ℤ) ^ j := by
    rw [pow_mul]
    norm_num
  have h19_S2j : 19 * renewalIntSlack s (2 + j) = (27 : ℤ) ^ (j + 1) + 4096 * (8 : ℤ) ^ j := by
    rw [hcoc, h3_3j]
    have hmul :
        19 * ((27 : ℤ) ^ j * 217 - (2 : ℤ) ^ (8 + 1) * (renewalNumerator s' j : ℤ)) =
          217 * 19 * (27 : ℤ) ^ j - 512 * (19 * (renewalNumerator s' j : ℤ)) := by ring
    rw [hmul, hA_run_z, pow_succ]
    ring
  refine ⟨hshift, h19_S2j, ?_⟩
  intro hs_next
  have hT_next : blockSteps s (2 + j + 1) = 10 + 3 * j := by
    simp only [blockSteps, hshift, hs_next]
    omega
  have hstep_next := (renewalIntSlack_step_and_cocycle s (2 + j) 0 0).2.1
  rw [hs_next, hT_next] at hstep_next
  have h2_pow : (2 : ℤ) ^ (10 + 3 * j + 1) = 2048 * (8 : ℤ) ^ j := by
    calc
      (2 : ℤ) ^ (10 + 3 * j + 1) = (2 : ℤ) ^ 11 * ((2 : ℤ) ^ 3) ^ j := by
        rw [show 10 + 3 * j + 1 = 11 + 3 * j by omega, pow_add, pow_mul]
      _ = 2048 * (8 : ℤ) ^ j := by norm_num
  refine ⟨hT_next, ?_⟩
  have hmul_next :
      19 * renewalIntSlack s (2 + j + 1) =
        9 * (19 * renewalIntSlack s (2 + j)) - 19 * (2 : ℤ) ^ (10 + 3 * j + 1) := by
    rw [hstep_next]
    ring
  rw [hmul_next, h19_S2j, h2_pow]
  ring

/-! ## 2. Section O5.2: Three-Block $(2, s_1, s_2)$ Slack Formula & $(2, 6, s_2)$ Escape Dichotomy -/

/-- **Three-Block $(2, s_1, s_2)$ Renewal Slack Formula (`three_block_two_s1_s2_slack_formula`,
Section O5.2)**:
For any gap sequence `s` with `s 0 = 2`:
1. `blockSteps s 3 = 2 + s 1 + s 2`, and
2. `renewalIntSlack s 3 = (3 : ℤ) ^ (s 1 + s 2) - 8 * (2 : ℤ) ^ (s 1) * (3 : ℤ) ^ (s 2) - 8 * (2 : ℤ) ^ (s 1 + s 2)`. -/
theorem three_block_two_s1_s2_slack_formula {s : ℕ → ℕ} (hs0 : s 0 = 2) :
    blockSteps s 3 = 2 + s 1 + s 2 ∧
      renewalIntSlack s 3 =
        (3 : ℤ) ^ (s 1 + s 2) - 8 * (2 : ℤ) ^ (s 1) * (3 : ℤ) ^ (s 2) -
          8 * (2 : ℤ) ^ (s 1 + s 2) := by
  rcases two_block_two_s1_renewalNumerator_and_slack hs0 with ⟨hT2, _, hS2⟩
  have hT3 : blockSteps s 3 = 2 + s 1 + s 2 := by
    change blockSteps s 2 + s 2 = _
    rw [hT2]
  have hstep3 := (renewalIntSlack_step_and_cocycle s 2 0 0).2.1
  rw [hS2, hT3] at hstep3
  refine ⟨hT3, ?_⟩
  rw [hstep3]
  have h3_add : (3 : ℤ) ^ (s 1 + s 2) = (3 : ℤ) ^ (s 2) * (3 : ℤ) ^ (s 1) := by
    rw [pow_add, mul_comm]
  have h2_add : (2 : ℤ) ^ (2 + s 1 + s 2 + 1) = 8 * (2 : ℤ) ^ (s 1 + s 2) := by
    rw [show 2 + s 1 + s 2 + 1 = 3 + (s 1 + s 2) by omega, pow_add]
    ring
  rw [h3_add, h2_add]
  ring

/-- **Exact Escape Threshold for $(2, 6, s_2)$ Triples (`three_block_two_six_s2_escape_iff_s2_le_two`,
Section O5.2)**:
If `s 0 = 2` and `s 1 = 6`, then:
1. `renewalIntSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 512 * (2 : ℤ) ^ (s 2)`, and
2. `2 * renewalNumerator s 3 ≥ 3 ^ (blockSteps s 3) ↔ s 2 ≤ 2`. -/
theorem three_block_two_six_s2_escape_iff_s2_le_two {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) :
    renewalIntSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 512 * (2 : ℤ) ^ (s 2) ∧
      (2 * renewalNumerator s 3 ≥ 3 ^ (blockSteps s 3) ↔ s 2 ≤ 2) := by
  rcases three_block_two_s1_s2_slack_formula hs0 with ⟨hT3, hS3⟩
  rw [hs1] at hT3 hS3
  have hS3_simp : renewalIntSlack s 3 = 217 * (3 : ℤ) ^ (s 2) - 512 * (2 : ℤ) ^ (s 2) := by
    rw [hS3, pow_add (3 : ℤ) 6 (s 2), pow_add (2 : ℤ) 6 (s 2)]
    ring
  have hpow_gt : ∀ m : ℕ, 512 * 2 ^ (m + 3) < 217 * 3 ^ (m + 3) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 512 * 2 ^ (m + 1 + 3) = 2 * (512 * 2 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 217 * 3 ^ (m + 1 + 3) = 3 * (217 * 3 ^ (m + 3)) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow_le : ∀ n : ℕ, n ≤ 2 → (217 * (3 : ℤ) ^ n - 512 * (2 : ℤ) ^ n) ≤ 0 := by
    intro n hn
    rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · omega
  have hslack_iff :
      2 * renewalNumerator s 3 ≥ 3 ^ (blockSteps s 3) ↔ renewalIntSlack s 3 ≤ 0 := by
    unfold renewalIntSlack
    have hcast : (3 : ℤ) ^ (blockSteps s 3) = ((3 ^ (blockSteps s 3) : ℕ) : ℤ) := by norm_cast
    rw [hcast]
    omega
  refine ⟨hS3_simp, ?_⟩
  rw [hslack_iff, hS3_simp]
  constructor
  · intro hle
    by_contra hgt
    push_neg at hgt
    obtain ⟨m, hm⟩ : ∃ m : ℕ, s 2 = m + 3 := ⟨s 2 - 3, by omega⟩
    have hlt : (512 : ℤ) * (2 : ℤ) ^ (s 2) < 217 * (3 : ℤ) ^ (s 2) := by
      rw [hm]
      exact_mod_cast hpow_gt m
    linarith
  · exact hpow_le (s 2)

/-! ## 3. Section O5.3: Mandatory $j \ge 2$ Neutral Waiting Time in $(2, 6, 3^j, 2)$ -/

/-- **Mandatory $j \ge 2$ Neutral Waiting Time in $(2, 6, 3^j, 2)$
(`two_six_three_pow_two_escape_iff_j_le_one`, Section O5.3)**:
Suppose `s 0 = 2`, `s 1 = 6`, `∀ t < j, s (2 + t) = 3`, and `s (2 + j) = 2`. Then:
1. `2 * renewalNumerator s (2 + j + 1) ≥ 3 ^ (blockSteps s (2 + j + 1)) ↔ j ≤ 1`, and
2. For `2 ≤ j`, `0 < renewalIntSlack s (2 + j + 1)` (with `renewalIntSlack s 5 = 2425` at `j = 2`). -/
theorem two_six_three_pow_two_escape_iff_j_le_one {s : ℕ → ℕ} {j : ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs3 : ∀ t < j, s (2 + t) = 3)
    (hs_next : s (2 + j) = 2) :
    (2 * renewalNumerator s (2 + j + 1) ≥ 3 ^ (blockSteps s (2 + j + 1)) ↔ j ≤ 1) ∧
      (2 ≤ j → 0 < renewalIntSlack s (2 + j + 1)) ∧
      (j = 2 → renewalIntSlack s (2 + j + 1) = 2425) := by
  have hclosed := (two_six_three_run_and_next_two_slack_closed_forms hs0 hs1 hs3).2.2 hs_next
  rcases hclosed with ⟨_, h19S⟩
  have hpow_gt : ∀ m : ℕ, 2048 * 8 ^ (m + 2) < 9 * 27 ^ (m + 2 + 1) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 2048 * 8 ^ (m + 1 + 2) = 8 * (2048 * 8 ^ (m + 2)) := by
          rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 9 * 27 ^ (m + 1 + 2 + 1) = 27 * (9 * 27 ^ (m + 2 + 1)) := by
          rw [show m + 1 + 2 + 1 = (m + 2 + 1) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow_le : ∀ n : ℕ, n ≤ 1 → (9 * (27 : ℤ) ^ (n + 1) - 2048 * (8 : ℤ) ^ n) ≤ 0 := by
    intro n hn
    rcases n with _ | _ | n
    · decide
    · decide
    · omega
  have hslack_iff :
      2 * renewalNumerator s (2 + j + 1) ≥ 3 ^ (blockSteps s (2 + j + 1)) ↔
        19 * renewalIntSlack s (2 + j + 1) ≤ 0 := by
    unfold renewalIntSlack
    have hcast :
        (3 : ℤ) ^ (blockSteps s (2 + j + 1)) = ((3 ^ (blockSteps s (2 + j + 1)) : ℕ) : ℤ) := by
      norm_cast
    rw [hcast]
    omega
  have hj2_pos : 2 ≤ j → 0 < renewalIntSlack s (2 + j + 1) := by
    intro hj2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, j = m + 2 := ⟨j - 2, by omega⟩
    have hlt : (2048 : ℤ) * (8 : ℤ) ^ j < 9 * (27 : ℤ) ^ (j + 1) := by
      rw [hm]
      exact_mod_cast hpow_gt m
    linarith [h19S]
  refine ⟨?_, hj2_pos, ?_⟩
  · rw [hslack_iff, h19S]
    constructor
    · intro hle
      by_contra hgt
      push_neg at hgt
      have hpos := hj2_pos (by omega)
      linarith [h19S]
    · exact hpow_le j
  · rintro rfl
    omega

end Mahler.RecoveryCascadeClosedForms
