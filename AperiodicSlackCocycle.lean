import SharpenedSqueezes

/-!
# The Universal Aperiodic Slack Cocycle, Global Width-`3^T` Corridor & Multi-Block Escalation

This module formalizes the four non-resetting attack vectors across arbitrary
(aperiodic) block-length sequences `s : ℕ → ℕ`:

1. **Attack Vector 1 — The Universal Aperiodic Slack Cocycle & Depletion Identity
   (`integerSlack_cocycle_eq`, `integerSlack_add_coprimeRemainder_eq`,
   `prefix_weighted_tail_budget`, `next_block_threshold_of_integerSlack_pos`)**:
   For **every** sequence `s : ℕ → ℕ`, prefix length `r`, and lookahead `m`:
   - `integerSlack s (r + m) + 2^(blockSteps s r) * (3^(blockSteps (shiftSeq s r) m) - integerSlack (shiftSeq s r) m) = 3^(blockSteps (shiftSeq s r) m) * integerSlack s r`
   - `integerSlack s (r + m) + 2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) m = 3^(blockSteps (shiftSeq s r) m) * integerSlack s r`
   - Whenever `0 < integerSlack s (r + m)`,
     `2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) m < 3^(blockSteps (shiftSeq s r) m) * integerSlack s r`.
   - At `m = 1`, `0 < integerSlack s (r + 1)` forces the next block `s r` to satisfy
     `2^(blockSteps s r + 1) * 2^(s r) < 3^(s r) * integerSlack s r`.
2. **Permanent `4×` Tail Lock After Any `s j = 2` & Multi-Step Escalation
   (`post_two_slack_identity`, `post_two_four_mul_slack_gt`,
   `post_two_tail_budget_lock`, `ten_le_after_subword_2_6_3_3_2`)**:
   - Whenever `s j = 2`, for **all** `m ≥ 0` in the future tail:
     `4 * integerSlack (shiftSeq s (j + 1)) m = 3^(blockSteps (shiftSeq s (j + 1)) m + 1) + integerSlack (shiftSeq s j) (1 + m)`.
   - Surviving through block `j + 1 + m` permanently locks
     `3^(blockSteps (shiftSeq s (j + 1)) m + 1) < 4 * integerSlack (shiftSeq s (j + 1)) m`
     and `2^(s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) m < 3^(blockSteps (shiftSeq s (j + 1)) m)`.
   - Whereas a single `s = 2` only forces the next block to be `≥ 6`, after the
     5-block prefix `(2, 6, 3, 3, 2)` the accumulated slack drops to `2425` against
     `2^17 = 131072`, universally forcing **`10 ≤ s (j + 5)`**.
3. **Attack Vector 2 — The Global Width-`3^T(m)` Coprime Corridor & Div/Mod Lock
   (`global_coprime_addition_identity`, `global_coprime_width_corridor`,
   `global_coprime_div_mod_lock`)**:
   - Exact subtraction-free identity:
     `2^(blockSteps s (m + 1) + 1) * u m = 3^(blockSteps s m) * (6 * a_0 + 2) + 2^(s 0 + 1) * coprimeRemainder s m`.
   - Along any surviving orbit (`1 ≤ m < K`, `0 < integerSlack s m`), `2^(blockSteps s (m + 1) + 1) * u m`
     is trapped in an interval of width `3^(blockSteps s m)`:
     `3^(blockSteps s m) * (6 * a_0 + 2) < 2^(blockSteps s (m + 1) + 1) * u m < 3^(blockSteps s m) * (6 * a_0 + 3)`,
     uniquely locking quotient `6 * a_0 + 2` and remainder `2^(s 0 + 1) * coprimeRemainder s m`.
4. **Attack Vectors 3 & 4 — Coasting Single-Block Ceiling & Cross-Block `a_0`-Elimination
   (`coasting_single_block_bound`, `cross_block_coprime_squeeze`)**:
   - In the coasting regime (`a_0 < 2^W`, `W ≤ blockSteps s m`), every individual block
     length `s m` satisfies `2^(blockSteps s m + s m - W) < 3^(blockSteps s m + 1)`.
   - Between any two blocks `j` and `m`, eliminating `a_0` yields:
     `3^(blockSteps s j) * (2^(blockSteps s (m + 1) + 1) * u m) < 3^(blockSteps s m) * (2^(blockSteps s (j + 1) + 1) * u j + 3^(blockSteps s j))`.
-/

namespace Mahler.AperiodicCocycle

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB
open Mahler.JumpValuation
open Mahler.EscapeBranchCap
open Mahler.PhaseLock
open Mahler.MasterReduction
open Mahler.ModEightClassifier
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.KernelDuality
open Mahler.Coasting
open Mahler.TwoSidedSqueeze
open Mahler.SharpenedSqueezes

/-! ## 1. Attack Vector 1: The Universal Aperiodic Slack Cocycle & Depletion Identity -/

/-- **Universal Aperiodic Slack Cocycle Identity (`integerSlack_cocycle_eq`)**:
For **every** sequence `s : ℕ → ℕ`, prefix length `r`, and lookahead `m`,
`integerSlack s (r + m) + 2^(blockSteps s r) * (3^(blockSteps (shiftSeq s r) m) - integerSlack (shiftSeq s r) m) =
  3^(blockSteps (shiftSeq s r) m) * integerSlack s r`. -/
theorem integerSlack_cocycle_eq (s : ℕ → ℕ) (r m : ℕ) :
    integerSlack s (r + m) +
        (2 : ℤ) ^ (blockSteps s r) *
          ((3 : ℤ) ^ (blockSteps (shiftSeq s r) m) -
            integerSlack (shiftSeq s r) m) =
      (3 : ℤ) ^ (blockSteps (shiftSeq s r) m) * integerSlack s r := by
  induction m with
  | zero =>
      simp [ integerSlack, blockSteps, coprimeRemainder ]
  | succ m ih =>
      have hsucc_global :
          integerSlack s (r + (m + 1)) =
            (3 : ℤ) ^ (s (r + m)) * integerSlack s (r + m) -
              (2 : ℤ) ^ (blockSteps s (r + m + 1) + 1) := by
        rw [← Nat.add_assoc]
        exact integerSlack_succ s (r + m)
      have hsucc_shift :
          integerSlack (shiftSeq s r) (m + 1) =
            (3 : ℤ) ^ (s (r + m)) * integerSlack (shiftSeq s r) m -
              (2 : ℤ) ^ (blockSteps (shiftSeq s r) (m + 1) + 1) := by
        simpa [shiftSeq] using integerSlack_succ (shiftSeq s r) m
      have hsteps :
          blockSteps s (r + m + 1) + 1 =
            blockSteps s r + (blockSteps (shiftSeq s r) (m + 1) + 1) := by
        have h1 : r + m + 1 = r + (m + 1) := by omega
        rw [h1, blockSteps_add]
        omega
      have hpow2 :
          (2 : ℤ) ^ (blockSteps s (r + m + 1) + 1) =
            (2 : ℤ) ^ (blockSteps s r) *
              (2 : ℤ) ^ (blockSteps (shiftSeq s r) (m + 1) + 1) := by
        rw [hsteps, pow_add]
      have hpow3 :
          (3 : ℤ) ^ (blockSteps (shiftSeq s r) (m + 1)) =
            (3 : ℤ) ^ (s (r + m)) *
              (3 : ℤ) ^ (blockSteps (shiftSeq s r) m) := by
        simp only [blockSteps, shiftSeq, pow_add]
        ring
      rw [hsucc_global, hsucc_shift, hpow2, hpow3]
      calc
        (3 : ℤ) ^ s (r + m) * integerSlack s (r + m) -
            (2 : ℤ) ^ blockSteps s r * (2 : ℤ) ^ (blockSteps (shiftSeq s r) (m + 1) + 1) +
            (2 : ℤ) ^ blockSteps s r *
              ((3 : ℤ) ^ s (r + m) * (3 : ℤ) ^ blockSteps (shiftSeq s r) m -
                ((3 : ℤ) ^ s (r + m) * integerSlack (shiftSeq s r) m -
                  (2 : ℤ) ^ (blockSteps (shiftSeq s r) (m + 1) + 1))) =
          (3 : ℤ) ^ s (r + m) *
            (integerSlack s (r + m) +
              (2 : ℤ) ^ blockSteps s r *
                ((3 : ℤ) ^ blockSteps (shiftSeq s r) m - integerSlack (shiftSeq s r) m)) := by
          ring
        _ = (3 : ℤ) ^ s (r + m) *
              ((3 : ℤ) ^ blockSteps (shiftSeq s r) m * integerSlack s r) := by
          rw [ih]
        _ = (3 : ℤ) ^ s (r + m) * (3 : ℤ) ^ blockSteps (shiftSeq s r) m *
              integerSlack s r := by
          ring

/-- **Universal Aperiodic Slack Depletion Identity (`integerSlack_add_coprimeRemainder_eq`)**:
For **every** sequence `s : ℕ → ℕ`, prefix length `r`, and lookahead `m`,
`integerSlack s (r + m) + 2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) m =
  3^(blockSteps (shiftSeq s r) m) * integerSlack s r`. -/
theorem integerSlack_add_coprimeRemainder_eq (s : ℕ → ℕ) (r m : ℕ) :
    integerSlack s (r + m) +
        (2 : ℤ) ^ (blockSteps s r + s r + 1) *
          (coprimeRemainder (shiftSeq s r) m : ℤ) =
      (3 : ℤ) ^ (blockSteps (shiftSeq s r) m) * integerSlack s r := by
  have hcocycle := integerSlack_cocycle_eq s r m
  have hdiff :
      (3 : ℤ) ^ (blockSteps (shiftSeq s r) m) -
          integerSlack (shiftSeq s r) m =
        (2 : ℤ) ^ (s r + 1) * (coprimeRemainder (shiftSeq s r) m : ℤ) := by
    unfold integerSlack
    simp only [shiftSeq_zero]
    ring
  rw [hdiff] at hcocycle
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s r) *
          ((2 : ℤ) ^ (s r + 1) * (coprimeRemainder (shiftSeq s r) m : ℤ)) =
        (2 : ℤ) ^ (blockSteps s r + s r + 1) *
          (coprimeRemainder (shiftSeq s r) m : ℤ) := by
    rw [show blockSteps s r + s r + 1 = blockSteps s r + (s r + 1) by omega, pow_add]
    ring
  linarith

/-- **Prefix-Weighted Tail Budget Inequality (`prefix_weighted_tail_budget`)**:
Whenever `0 < integerSlack s (r + m)`,
`2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) m <
  3^(blockSteps (shiftSeq s r) m) * integerSlack s r`. -/
theorem prefix_weighted_tail_budget (s : ℕ → ℕ) (r m : ℕ)
    (hpos : 0 < integerSlack s (r + m)) :
    (2 : ℤ) ^ (blockSteps s r + s r + 1) *
        (coprimeRemainder (shiftSeq s r) m : ℤ) <
      (3 : ℤ) ^ (blockSteps (shiftSeq s r) m) * integerSlack s r := by
  have hid := integerSlack_add_coprimeRemainder_eq s r m
  linarith

/-- **Dynamic Next-Block Threshold (`next_block_threshold_of_integerSlack_pos`)**:
Surviving step `r + 1` (`0 < integerSlack s (r + 1)`) forces the block length
`s r` to satisfy `2^(blockSteps s r + 1) * 2^(s r) < 3^(s r) * integerSlack s r`. -/
theorem next_block_threshold_of_integerSlack_pos (s : ℕ → ℕ) (r : ℕ)
    (hpos : 0 < integerSlack s (r + 1)) :
    (2 : ℤ) ^ (blockSteps s r + 1) * (2 : ℤ) ^ (s r) <
      (3 : ℤ) ^ (s r) * integerSlack s r := by
  rw [integerSlack_succ] at hpos
  have hpow :
      (2 : ℤ) ^ (blockSteps s (r + 1) + 1) =
        (2 : ℤ) ^ (blockSteps s r + 1) * (2 : ℤ) ^ (s r) := by
    simp only [blockSteps]
    rw [show blockSteps s r + s r + 1 = (blockSteps s r + 1) + s r by omega, pow_add]
  linarith

/-! ## 2. Permanent `4×` Tail Lock After Any `s j = 2` & Multi-Step Escalation -/

theorem shiftSeq_add {α : Type*} (f : ℕ → α) (j r : ℕ) :
    shiftSeq (shiftSeq f j) r = shiftSeq f (j + r) := by
  funext k
  simp [shiftSeq, Nat.add_assoc]

/-- **Exact Post-`s j = 2` Slack Identity (`post_two_slack_identity`)**:
Whenever `s j = 2`, for **every** future horizon `m ≥ 0`:
`4 * integerSlack (shiftSeq s (j + 1)) m =
  3^(blockSteps (shiftSeq s (j + 1)) m + 1) + integerSlack (shiftSeq s j) (1 + m)`. -/
theorem post_two_slack_identity (s : ℕ → ℕ) {j : ℕ} (hsj : s j = 2) (m : ℕ) :
    4 * integerSlack (shiftSeq s (j + 1)) m =
      (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) m + 1) +
        integerSlack (shiftSeq s j) (1 + m) := by
  have hcocycle := integerSlack_cocycle_eq (shiftSeq s j) 1 m
  rw [shiftSeq_add] at hcocycle
  have hb1 : blockSteps (shiftSeq s j) 1 = 2 := by
    simp [blockSteps, shiftSeq, hsj]
  have hd1 : integerSlack (shiftSeq s j) 1 = 1 := by
    rw [integerSlack_one]
    simp [shiftSeq, hsj]
  rw [hb1, hd1] at hcocycle
  have hpow3 :
      (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) m + 1) =
        3 * (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) m) := by
    rw [pow_succ]
    ring
  linarith

/-- **Permanent `3/4` Relative Slack Floor After `s j = 2` (`post_two_four_mul_slack_gt`)**:
If `s j = 2` and the orbit survives through block `j + 1 + m` (`j + 1 + m < K`),
then `3^(blockSteps (shiftSeq s (j + 1)) m + 1) < 4 * integerSlack (shiftSeq s (j + 1)) m`. -/
theorem post_two_four_mul_slack_gt {a_0 : ℕ} {s u : ℕ → ℕ} {K j m : ℕ}
    (hjm : j + (1 + m) < K) (hchain : ValidBlockChain a_0 s u K)
    (hsj : s j = 2) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + (1 + m) + 1))) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s (j + 1)) m + 1) <
      4 * integerSlack (shiftSeq s (j + 1)) m := by
  have hpos := shift_invariant_integerSlack_pos hjm hchain hsurv
  have hid := post_two_slack_identity s hsj m
  linarith

/-- **Permanent `4×` Tail-Budget Lock After `s j = 2` (`post_two_tail_budget_lock`)**:
If `s j = 2` and the orbit survives through block `j + 1 + m` (`j + (1 + m) < K`),
then `2^(s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) m < 3^(blockSteps (shiftSeq s (j + 1)) m)`. -/
theorem post_two_tail_budget_lock {a_0 : ℕ} {s u : ℕ → ℕ} {K j m : ℕ}
    (hjm : j + (1 + m) < K) (hchain : ValidBlockChain a_0 s u K)
    (hsj : s j = 2) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + (1 + m) + 1))) :
    2 ^ (s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) m <
      3 ^ (blockSteps (shiftSeq s (j + 1)) m) := by
  have hpos := shift_invariant_integerSlack_pos hjm hchain hsurv
  have hid := integerSlack_add_coprimeRemainder_eq (shiftSeq s j) 1 m
  rw [shiftSeq_add] at hid
  have hb1 : blockSteps (shiftSeq s j) 1 = 2 := by
    simp [blockSteps, shiftSeq, hsj]
  have hd1 : integerSlack (shiftSeq s j) 1 = 1 := by
    rw [integerSlack_one]
    simp [shiftSeq, hsj]
  have hshift1 : shiftSeq s j 1 = s (j + 1) := rfl
  rw [hb1, hd1, hshift1] at hid
  have hlt :
      ((2 ^ (s (j + 1) + 3) * coprimeRemainder (shiftSeq s (j + 1)) m : ℕ) : ℤ) <
        ((3 ^ (blockSteps (shiftSeq s (j + 1)) m) : ℕ) : ℤ) := by
    push_cast
    have hexp : 2 + s (j + 1) + 1 = s (j + 1) + 3 := by omega
    rw [hexp] at hid
    linarith
  exact_mod_cast hlt

/-- Exact evaluation of `integerSlack` along any 5-block prefix `(2, 6, 3, 3, 2)`. -/
theorem integerSlack_of_prefix_2_6_3_3_2 {t : ℕ → ℕ}
    (h0 : t 0 = 2) (h1 : t 1 = 6) (h2 : t 2 = 3) (h3 : t 3 = 3) (h4 : t 4 = 2) :
    integerSlack t 1 = 1 ∧
    integerSlack t 2 = 217 ∧
    integerSlack t 3 = 1763 ∧
    integerSlack t 4 = 14833 ∧
    integerSlack t 5 = 2425 := by
  have hs1 := integerSlack_one t
  have hs2 := integerSlack_succ t 1
  have hs3 := integerSlack_succ t 2
  have hs4 := integerSlack_succ t 3
  have hs5 := integerSlack_succ t 4
  have hb2 : blockSteps t 2 = 8 := by simp [blockSteps, h0, h1]
  have hb3 : blockSteps t 3 = 11 := by simp [blockSteps, h0, h1, h2]
  have hb4 : blockSteps t 4 = 14 := by simp [blockSteps, h0, h1, h2, h3]
  have hb5 : blockSteps t 5 = 16 := by simp [blockSteps, h0, h1, h2, h3, h4]
  rw [h0] at hs1
  rw [h1, hb2, hs1] at hs2
  rw [h2, hb3, hs2] at hs3
  rw [h3, hb4, hs3] at hs4
  rw [h4, hb5, hs4] at hs5
  norm_num at hs1 hs2 hs3 hs4 hs5
  exact ⟨hs1, hs2, hs3, hs4, hs5⟩

/-- **Multi-Step Escalation Theorem (`ten_le_after_subword_2_6_3_3_2`)**:
Whereas a single block `s = 2` only forces the next block to be `≥ 6`,
if `(s j, s (j + 1), s (j + 2), s (j + 3), s (j + 4)) = (2, 6, 3, 3, 2)` occurs at
any block index `j` (`j + 6 < K`) along a surviving orbit, the accumulated slack
depletion (`integerSlack = 2425` against `2^17 = 131072`) universally forces
**`10 ≤ s (j + 5)`**. -/
theorem ten_le_after_subword_2_6_3_3_2 {a_0 : ℕ} {s u : ℕ → ℕ} {K j : ℕ}
    (hj : j + 6 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs0 : s j = 2) (hs1 : s (j + 1) = 6) (hs2 : s (j + 2) = 3)
    (hs3 : s (j + 3) = 3) (hs4 : s (j + 4) = 2)
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + 6 + 1))) :
    10 ≤ s (j + 5) := by
  have hpos6 := shift_invariant_integerSlack_pos (j := j) (m := 6) hj hchain hsurv
  have hthresh := next_block_threshold_of_integerSlack_pos (shiftSeq s j) 5 hpos6
  have hd5 := (integerSlack_of_prefix_2_6_3_3_2 (t := shiftSeq s j)
    (by simp [shiftSeq, hs0])
    (by simp [shiftSeq, hs1])
    (by simp [shiftSeq, hs2])
    (by simp [shiftSeq, hs3])
    (by simp [shiftSeq, hs4])).2.2.2.2
  have hb5 : blockSteps (shiftSeq s j) 5 = 16 := by
    simp [blockSteps, shiftSeq, hs0, hs1, hs2, hs3, hs4]
  have hs5_eq : shiftSeq s j 5 = s (j + 5) := rfl
  rw [hb5, hd5, hs5_eq] at hthresh
  by_contra hlt
  have hcases :
      s (j + 5) = 0 ∨ s (j + 5) = 1 ∨ s (j + 5) = 2 ∨ s (j + 5) = 3 ∨
      s (j + 5) = 4 ∨ s (j + 5) = 5 ∨ s (j + 5) = 6 ∨ s (j + 5) = 7 ∨
      s (j + 5) = 8 ∨ s (j + 5) = 9 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;>
    { rw [h] at hthresh; norm_num at hthresh }

/-! ## 3. Attack Vector 2: Global Width-`3^T(m)` Coprime Corridor & Div/Mod Lock -/

/-- **Global Subtraction-Free Coprime Quotient Identity (`global_coprime_addition_identity`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`),
`2^(blockSteps s (m + 1) + 1) * u m =
  3^(blockSteps s m) * (6 * a_0 + 2) + 2^(s 0 + 1) * coprimeRemainder s m`. -/
theorem global_coprime_addition_identity {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (blockSteps s (m + 1) + 1) * u m =
      3 ^ (blockSteps s m) * (6 * a_0 + 2) +
        2 ^ (s 0 + 1) * coprimeRemainder s m := by
  have hid := archimedean_slack_addition_identity hmK hchain
  have hpow3 :
      3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) =
        3 ^ (blockSteps s m) * (6 * a_0 + 2) + 3 ^ (blockSteps s m) := by
    rw [Nat.pow_succ]
    ring
  rw [hpow3] at hid
  omega

/-- For `m ≥ 1`, `0 < coprimeRemainder s m`. -/
theorem coprimeRemainder_pos (s : ℕ → ℕ) {m : ℕ} (hm : 1 ≤ m) :
    0 < coprimeRemainder s m := by
  cases m with
  | zero => omega
  | succ n =>
      simp only [coprimeRemainder]
      have hpos : 0 < 2 ^ (tailSteps s n) := Nat.pow_pos (by decide)
      omega

/-- **Global Width-`3^T(m)` Coprime Corridor (`global_coprime_width_corridor`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` with `1 ≤ m < K` and
`0 < integerSlack s m`, the scaled coprime quotient `2^(blockSteps s (m + 1) + 1) * u m`
is trapped in an interval of width `3^(blockSteps s m)`:
`3^(blockSteps s m) * (6 * a_0 + 2) < 2^(blockSteps s (m + 1) + 1) * u m <
  3^(blockSteps s m) * (6 * a_0 + 3)`. -/
theorem global_coprime_width_corridor {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    3 ^ (blockSteps s m) * (6 * a_0 + 2) <
        2 ^ (blockSteps s (m + 1) + 1) * u m ∧
      2 ^ (blockSteps s (m + 1) + 1) * u m <
        3 ^ (blockSteps s m) * (6 * a_0 + 3) := by
  have hid := global_coprime_addition_identity hmK hchain
  have hbudget := (integerSlack_pos_iff_tail_budget s m).mp hslack
  have hRpos := coprimeRemainder_pos s hm1
  have h2pos : 0 < 2 ^ (s 0 + 1) := Nat.pow_pos (by decide)
  have hprod_pos : 0 < 2 ^ (s 0 + 1) * coprimeRemainder s m :=
    Nat.mul_pos h2pos hRpos
  constructor
  · omega
  · have h63 :
        3 ^ (blockSteps s m) * (6 * a_0 + 3) =
          3 ^ (blockSteps s m) * (6 * a_0 + 2) + 3 ^ (blockSteps s m) := by
      ring
    omega

/-- **Global Quotient & Remainder Lock (`global_coprime_div_mod_lock`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` with `m < K` and
`0 < integerSlack s m`, dividing `2^(blockSteps s (m + 1) + 1) * u m` by
`3^(blockSteps s m)` yields exact quotient `6 * a_0 + 2` and exact remainder
`2^(s 0 + 1) * coprimeRemainder s m`. -/
theorem global_coprime_div_mod_lock {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    (2 ^ (blockSteps s (m + 1) + 1) * u m) / 3 ^ (blockSteps s m) = 6 * a_0 + 2 ∧
      (2 ^ (blockSteps s (m + 1) + 1) * u m) % 3 ^ (blockSteps s m) =
        2 ^ (s 0 + 1) * coprimeRemainder s m := by
  have hid := global_coprime_addition_identity hmK hchain
  have hbudget := (integerSlack_pos_iff_tail_budget s m).mp hslack
  have hpos : 0 < 3 ^ (blockSteps s m) := Nat.pow_pos (by decide)
  have hdiv :
      (2 ^ (blockSteps s (m + 1) + 1) * u m) / 3 ^ (blockSteps s m) =
        6 * a_0 + 2 := by
    apply Nat.le_antisymm
    · have hhi :
          2 ^ (blockSteps s (m + 1) + 1) * u m <
            (6 * a_0 + 2 + 1) * 3 ^ (blockSteps s m) := by
        rw [hid]
        have : (6 * a_0 + 2 + 1) * 3 ^ (blockSteps s m) =
            3 ^ (blockSteps s m) * (6 * a_0 + 2) + 3 ^ (blockSteps s m) := by ring
        omega
      exact (Nat.div_lt_iff_lt_mul hpos).mpr hhi |> Nat.le_of_lt_succ
    · have hlo :
          (6 * a_0 + 2) * 3 ^ (blockSteps s m) ≤
            2 ^ (blockSteps s (m + 1) + 1) * u m := by
        rw [hid]
        have : (6 * a_0 + 2) * 3 ^ (blockSteps s m) =
            3 ^ (blockSteps s m) * (6 * a_0 + 2) := by ring
        omega
      exact (Nat.le_div_iff_mul_le hpos).mpr hlo
  have hdm := Nat.div_add_mod (2 ^ (blockSteps s (m + 1) + 1) * u m) (3 ^ (blockSteps s m))
  rw [hdiv] at hdm
  exact ⟨hdiv, by omega⟩

/-! ## 4. Attack Vectors 3 & 4: Coasting Single-Block Ceiling & Cross-Block `a_0`-Elimination -/

/-- **Explicit Single-Block Ceiling in the Coasting Regime (`coasting_single_block_bound`)**:
In the coasting regime (`a_0 < 2^W` and `W ≤ blockSteps s m`), every individual
block length `s m` is bounded independently of `a_0` and `u m`:
`2^(blockSteps s m + s m - W) < 3^(blockSteps s m + 1)`. -/
theorem coasting_single_block_bound {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm : m < K) (hchain : ValidBlockChain a_0 s u K)
    (ha0 : a_0 < 2 ^ W) (hWT : W ≤ blockSteps s m) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + s m)) :
    2 ^ (blockSteps s m + s m - W) < 3 ^ (blockSteps s m + 1) := by
  have hWT1 : W ≤ blockSteps s (m + 1) := by
    simp only [blockSteps]
    omega
  have hbound := coasting_coprime_quotient_bound hm hchain ha0 hWT1 hsurv
  rcases hchain m hm with ⟨_, hum_odd, _⟩
  have hum_pos : 1 ≤ u m := by omega
  have hle :
      2 ^ (blockSteps s (m + 1) - W) * 1 ≤
        2 ^ (blockSteps s (m + 1) - W) * u m :=
    Nat.mul_le_mul_left _ hum_pos
  simp only [blockSteps, Nat.mul_one] at hle hbound ⊢
  omega

/-- **Cross-Block `a_0`-Elimination Squeeze (`cross_block_coprime_squeeze`)**:
For any two block indices `j < K` and `m < K` along a valid block chain where the
orbit survives through block `m` (`0 < integerSlack s m`), eliminating `a_0`
between the lower bound at `j` and the upper bound at `m` yields:
`3^(blockSteps s j) * (2^(blockSteps s (m + 1) + 1) * u m) <
  3^(blockSteps s m) * (2^(blockSteps s (j + 1) + 1) * u j + 3^(blockSteps s j))`. -/
theorem cross_block_coprime_squeeze {a_0 : ℕ} {s u : ℕ → ℕ} {K j m : ℕ}
    (hjK : j < K) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack_m : 0 < integerSlack s m) :
    3 ^ (blockSteps s j) * (2 ^ (blockSteps s (m + 1) + 1) * u m) <
      3 ^ (blockSteps s m) *
        (2 ^ (blockSteps s (j + 1) + 1) * u j + 3 ^ (blockSteps s j)) := by
  have hid_j := archimedean_slack_addition_identity hjK hchain
  have hlo_j :
      3 ^ (blockSteps s j + 1) * (2 * a_0 + 1) ≤
        2 ^ (blockSteps s (j + 1) + 1) * u j + 3 ^ (blockSteps s j) := by
    omega
  have hid_m := archimedean_slack_addition_identity hmK hchain
  have hbudget_m := (integerSlack_pos_iff_tail_budget s m).mp hslack_m
  have hhi_m :
      2 ^ (blockSteps s (m + 1) + 1) * u m <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
    omega
  have hpos_j : 0 < 3 ^ (blockSteps s j) := Nat.pow_pos (by decide)
  have hmul1 :
      3 ^ (blockSteps s j) * (2 ^ (blockSteps s (m + 1) + 1) * u m) <
        3 ^ (blockSteps s j) * (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) :=
    Nat.mul_lt_mul_of_pos_left hhi_m hpos_j
  have hswap :
      3 ^ (blockSteps s j) * (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) =
        3 ^ (blockSteps s m) * (3 ^ (blockSteps s j + 1) * (2 * a_0 + 1)) := by
    rw [Nat.pow_succ (3 : ℕ) (blockSteps s m), Nat.pow_succ (3 : ℕ) (blockSteps s j)]
    ring
  have hmul2 :
      3 ^ (blockSteps s m) * (3 ^ (blockSteps s j + 1) * (2 * a_0 + 1)) ≤
        3 ^ (blockSteps s m) *
          (2 ^ (blockSteps s (j + 1) + 1) * u j + 3 ^ (blockSteps s j)) :=
    Nat.mul_le_mul_left (3 ^ (blockSteps s m)) hlo_j
  omega

end Mahler.AperiodicCocycle
