import CoprimeRemainderSlack

/-!
# The Integer Slack Recurrence & Shift-Invariant Multi-Origin Subword Exclusions

This module formalizes the self-contained 1-step recurrence for the integer
slack `Δ_m` and upgrades the `j = 0` tail budget into a **shift-invariant
multi-origin obstruction** holding at every intermediate block `j`:

1. **The Integer Slack Sequence `integerSlack s m` (`integerSlack_one`,
   `integerSlack_succ`, `integerSlack_eq_orbit_slack`)**:
   Define `integerSlack s m : ℤ := 3^(blockSteps s m) - 2^(s 0 + 1) * coprimeRemainder s m`.
   - At `m = 1`, `integerSlack s 1 = 3^(s 0) - 2^(s 0 + 1)` (`= 1` when `s 0 = 2`).
   - Across each step `m → m + 1`, `integerSlack` satisfies the self-contained
     recurrence:
     `integerSlack s (m + 1) = 3^(s m) * integerSlack s m - 2^(blockSteps s (m + 1) + 1)`.
   - Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`),
     `integerSlack s m = 3^(blockSteps s m + 1) * (2 * a_0 + 1) - 2^(blockSteps s (m + 1) + 1) * u m`.
2. **Shift-Invariance of Block Chains and Mahler Companions (`validBlockChain_shift`,
   `validCompanionUpTo_shift`)**:
   Shifting a valid `(j + K)`-block chain to start at the `j`-th odd return
   `orbit a_0 (blockSteps s j)` yields a valid `K`-block chain for the shifted
   sequences `shiftSeq s j` and `shiftSeq u j`.
3. **Shift-Invariant Multi-Origin Slack Positivity (`shift_invariant_tail_budget`,
   `shift_invariant_integerSlack_pos`)**:
   For **every** starting block index `j` and offset `m` (`j + m < K`), surviving
   through step `blockSteps s (j + m + 1)` forces
   `0 < integerSlack (shiftSeq s j) m`.
4. **Universal Shift-Invariant Forbidden Block Subwords (`no_companion_of_subword_2_6_2`,
   `no_companion_of_subword_2_6_3_2`)**:
   At **any** block index `j` along an orbit:
   - `(s j, s (j + 1), s (j + 2)) = (2, 6, 2)` has relative slack `-95 < 0` at
     `m = 3` and is universally impossible.
   - `(s j, s (j + 1), s (j + 2), s (j + 3)) = (2, 6, 3, 2)` has relative slack
     `-517 < 0` at `m = 4` and is universally impossible.
-/

namespace Mahler.ShiftSlack

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

/-! ## 1. The Integer Slack Sequence `integerSlack` and Its 1-Step Recurrence -/

/-- The integer slack `Δ_m = 3^(blockSteps s m) - 2^(s 0 + 1) * coprimeRemainder s m`. -/
def integerSlack (s : ℕ → ℕ) (m : ℕ) : ℤ :=
  (3 : ℤ) ^ (blockSteps s m) - (2 : ℤ) ^ (s 0 + 1) * (coprimeRemainder s m : ℤ)

theorem integerSlack_one (s : ℕ → ℕ) :
    integerSlack s 1 = (3 : ℤ) ^ (s 0) - (2 : ℤ) ^ (s 0 + 1) := by
  unfold integerSlack
  simp [blockSteps, coprimeRemainder, tailSteps]

/-- **Self-Contained 1-Step Recurrence for `integerSlack` (`integerSlack_succ`)**:
`integerSlack s (m + 1) = 3^(s m) * integerSlack s m - 2^(blockSteps s (m + 1) + 1)`. -/
theorem integerSlack_succ (s : ℕ → ℕ) (m : ℕ) :
    integerSlack s (m + 1) =
      (3 : ℤ) ^ (s m) * integerSlack s m -
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by
  unfold integerSlack
  have hsteps : (s 0 + 1) + tailSteps s m = blockSteps s (m + 1) + 1 := by
    have h := add_tailSteps_eq_blockSteps_succ s m
    omega
  have hpow2 :
      (2 : ℤ) ^ (s 0 + 1) * (2 : ℤ) ^ (tailSteps s m) =
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by
    rw [← pow_add, hsteps]
  have hpow3 :
      (3 : ℤ) ^ (blockSteps s (m + 1)) =
        (3 : ℤ) ^ (s m) * (3 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, pow_add]
    ring
  simp only [coprimeRemainder, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [hpow3]
  calc
    (3 : ℤ) ^ (s m) * (3 : ℤ) ^ (blockSteps s m) -
        (2 : ℤ) ^ (s 0 + 1) *
          ((3 : ℤ) ^ (s m) * (coprimeRemainder s m : ℤ) + (2 : ℤ) ^ (tailSteps s m)) =
      (3 : ℤ) ^ (s m) *
        ((3 : ℤ) ^ (blockSteps s m) - (2 : ℤ) ^ (s 0 + 1) * (coprimeRemainder s m : ℤ)) -
        (2 : ℤ) ^ (s 0 + 1) * (2 : ℤ) ^ (tailSteps s m) := by ring
    _ = (3 : ℤ) ^ (s m) *
        ((3 : ℤ) ^ (blockSteps s m) - (2 : ℤ) ^ (s 0 + 1) * (coprimeRemainder s m : ℤ)) -
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) := by rw [hpow2]

/-- Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`),
`integerSlack s m = 3^(blockSteps s m + 1) * (2 * a_0 + 1) - 2^(blockSteps s (m + 1) + 1) * u m`. -/
theorem integerSlack_eq_orbit_slack {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    integerSlack s m =
      (3 : ℤ) ^ (blockSteps s m + 1) * (2 * (a_0 : ℤ) + 1) -
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) * (u m : ℤ) := by
  unfold integerSlack
  have hadd :
      ((2 ^ (blockSteps s (m + 1) + 1) * u m + 3 ^ (blockSteps s m) : ℕ) : ℤ) =
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) +
          2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) := by
    exact_mod_cast archimedean_slack_addition_identity hmK hchain
  push_cast at hadd
  linarith

theorem integerSlack_pos_iff_tail_budget (s : ℕ → ℕ) (m : ℕ) :
    0 < integerSlack s m ↔
      2 ^ (s 0 + 1) * coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  unfold integerSlack
  constructor <;> intro h
  · have hlt :
        ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) <
          ((3 ^ (blockSteps s m) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hlt
  · have hlt :
        ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) <
          ((3 ^ (blockSteps s m) : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at hlt
    linarith

theorem integerSlack_pos_of_validCompanionUpTo {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + s m)) :
    0 < integerSlack s m :=
  (integerSlack_pos_iff_tail_budget s m).mpr
    (tail_budget_of_validCompanionUpTo hmK hchain hsurv)

/-! ## 2. Shift-Invariance of Block Chains and Multi-Origin Slack Positivity -/

/-- Shift a sequence `f : ℕ → α` to start at index `j`. -/
def shiftSeq {α : Type*} (f : ℕ → α) (j k : ℕ) : α :=
  f (j + k)

@[simp] theorem shiftSeq_zero {α : Type*} (f : ℕ → α) (j : ℕ) :
    shiftSeq f j 0 = f j := by
  simp [shiftSeq]

theorem blockSteps_add (s : ℕ → ℕ) (j k : ℕ) :
    blockSteps s (j + k) =
      blockSteps s j + blockSteps (shiftSeq s j) k := by
  induction k with
  | zero => simp [blockSteps]
  | succ k ih =>
      change blockSteps s ((j + k) + 1) =
        blockSteps s j + (blockSteps (shiftSeq s j) k + shiftSeq s j k)
      simp only [blockSteps, shiftSeq]
      omega

/-- Shifting a valid `(j + K)`-block chain to start at the `j`-th return integer
`orbit a_0 (blockSteps s j)` yields a valid `K`-block chain. -/
theorem validBlockChain_shift {a_0 : ℕ} {s u : ℕ → ℕ} {j K : ℕ}
    (hchain : ValidBlockChain a_0 s u (j + K)) :
    ValidBlockChain (orbit a_0 (blockSteps s j))
      (shiftSeq s j) (shiftSeq u j) K := by
  intro k hk
  rcases hchain (j + k) (by omega) with ⟨hsk, huk, hdecomp⟩
  refine ⟨hsk, huk, ?_⟩
  rw [← orbit_add, ← blockSteps_add]
  exact hdecomp

/-- Shifting `ValidCompanionUpTo a_0 ξ (T + N)` by `T` steps. -/
theorem validCompanionUpTo_shift {a_0 : ℕ} {ξ : ℝ} (T N : ℕ)
    (hsurv : ValidCompanionUpTo a_0 ξ (T + N)) :
    ValidCompanionUpTo (orbit a_0 T) (ξ * (3 / 2 : ℝ) ^ T) N := by
  intro n hn
  exact validCompanionAt_shift T n (hsurv (T + n) (by omega))

/-- **Shift-Invariant Multi-Origin Tail Budget (`shift_invariant_tail_budget`)**:
For **every** starting block index `j` and offset `m` (`j + m < K`), surviving
through step `blockSteps s (j + m + 1)` forces the relative tail budget
`2^(s j + 1) * coprimeRemainder (shiftSeq s j) m < 3^(blockSteps (shiftSeq s j) m)`. -/
theorem shift_invariant_tail_budget {a_0 : ℕ} {s u : ℕ → ℕ} {K j m : ℕ}
    (hjm : j + m < K) (hchain : ValidBlockChain a_0 s u K) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + m + 1))) :
    2 ^ (s j + 1) * coprimeRemainder (shiftSeq s j) m <
      3 ^ (blockSteps (shiftSeq s j) m) := by
  have hchain_sub : ValidBlockChain a_0 s u (j + (m + 1)) :=
    fun k hk => hchain k (by omega)
  have hchain_shift := validBlockChain_shift hchain_sub
  have hsteps :
      blockSteps s (j + m + 1) =
        blockSteps s j +
          (blockSteps (shiftSeq s j) m + shiftSeq s j m) := by
    have h1 : j + m + 1 = j + (m + 1) := by omega
    rw [h1, blockSteps_add]
    rfl
  rw [hsteps] at hsurv
  have hsurv_shift :=
    validCompanionUpTo_shift (blockSteps s j)
      (blockSteps (shiftSeq s j) m + shiftSeq s j m) hsurv
  have hbudget :=
    tail_budget_of_validCompanionUpTo (Nat.lt_succ_self m) hchain_shift hsurv_shift
  simpa [shiftSeq] using hbudget

/-- **Shift-Invariant Multi-Origin Slack Positivity (`shift_invariant_integerSlack_pos`)**:
For every starting block `j` and offset `m` (`j + m < K`), surviving through
step `blockSteps s (j + m + 1)` forces `0 < integerSlack (shiftSeq s j) m`. -/
theorem shift_invariant_integerSlack_pos {a_0 : ℕ} {s u : ℕ → ℕ} {K j m : ℕ}
    (hjm : j + m < K) (hchain : ValidBlockChain a_0 s u K) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + m + 1))) :
    0 < integerSlack (shiftSeq s j) m := by
  rw [integerSlack_pos_iff_tail_budget, shiftSeq_zero]
  exact shift_invariant_tail_budget hjm hchain hsurv

/-! ## 3. Universal Shift-Invariant Exclusions of `(2, 6, 2)` and `(2, 6, 3, 2)` -/

/-- Exact evaluation of `integerSlack` for any sequence starting with `(2, 6, 2)`. -/
theorem integerSlack_of_prefix_2_6_2 {t : ℕ → ℕ}
    (h0 : t 0 = 2) (h1 : t 1 = 6) (h2 : t 2 = 2) :
    integerSlack t 1 = 1 ∧
    integerSlack t 2 = 217 ∧
    integerSlack t 3 = -95 := by
  have hs1 := integerSlack_one t
  have hs2 := integerSlack_succ t 1
  have hs3 := integerSlack_succ t 2
  have hb1 : blockSteps t 1 = 2 := by simp [blockSteps, h0]
  have hb2 : blockSteps t 2 = 8 := by simp [blockSteps, h0, h1]
  have hb3 : blockSteps t 3 = 10 := by simp [blockSteps, h0, h1, h2]
  rw [h0] at hs1
  rw [h1, hb2, hs1] at hs2
  rw [h2, hb3, hs2] at hs3
  norm_num at hs1 hs2 hs3
  exact ⟨hs1, hs2, hs3⟩

/-- **Universal Shift-Invariant Exclusion of `(2, 6, 2)` (`no_companion_of_subword_2_6_2`)**:
If `(s j, s (j + 1), s (j + 2)) = (2, 6, 2)` occurs at **any** block index `j`
(`j + 3 < K`) along `ValidBlockChain a_0 s u K`, then no real companion `ξ` can
survive through step `blockSteps s (j + 4)`. -/
theorem no_companion_of_subword_2_6_2 {a_0 : ℕ} {s u : ℕ → ℕ} {K j : ℕ}
    (hj : j + 3 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs0 : s j = 2) (hs1 : s (j + 1) = 6) (hs2 : s (j + 2) = 2) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s (j + 4)) := by
  rintro ⟨ξ, hξ⟩
  have hpos := shift_invariant_integerSlack_pos (j := j) (m := 3) hj hchain
    (by simpa [Nat.add_assoc] using hξ)
  have hval := (integerSlack_of_prefix_2_6_2 (t := shiftSeq s j)
    (by simp [shiftSeq, hs0])
    (by simp [shiftSeq, hs1])
    (by simp [shiftSeq, hs2])).2.2
  linarith

/-- Exact evaluation of `integerSlack` for any sequence starting with `(2, 6, 3, 2)`. -/
theorem integerSlack_of_prefix_2_6_3_2 {t : ℕ → ℕ}
    (h0 : t 0 = 2) (h1 : t 1 = 6) (h2 : t 2 = 3) (h3 : t 3 = 2) :
    integerSlack t 1 = 1 ∧
    integerSlack t 2 = 217 ∧
    integerSlack t 3 = 1763 ∧
    integerSlack t 4 = -517 := by
  have hs1 := integerSlack_one t
  have hs2 := integerSlack_succ t 1
  have hs3 := integerSlack_succ t 2
  have hs4 := integerSlack_succ t 3
  have hb2 : blockSteps t 2 = 8 := by simp [blockSteps, h0, h1]
  have hb3 : blockSteps t 3 = 11 := by simp [blockSteps, h0, h1, h2]
  have hb4 : blockSteps t 4 = 13 := by simp [blockSteps, h0, h1, h2, h3]
  rw [h0] at hs1
  rw [h1, hb2, hs1] at hs2
  rw [h2, hb3, hs2] at hs3
  rw [h3, hb4, hs3] at hs4
  norm_num at hs1 hs2 hs3 hs4
  exact ⟨hs1, hs2, hs3, hs4⟩

/-- **Universal Shift-Invariant Exclusion of `(2, 6, 3, 2)` (`no_companion_of_subword_2_6_3_2`)**:
If `(s j, s (j + 1), s (j + 2), s (j + 3)) = (2, 6, 3, 2)` occurs at **any**
block index `j` (`j + 4 < K`) along `ValidBlockChain a_0 s u K`, then no real
companion `ξ` can survive through step `blockSteps s (j + 5)`. -/
theorem no_companion_of_subword_2_6_3_2 {a_0 : ℕ} {s u : ℕ → ℕ} {K j : ℕ}
    (hj : j + 4 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs0 : s j = 2) (hs1 : s (j + 1) = 6)
    (hs2 : s (j + 2) = 3) (hs3 : s (j + 3) = 2) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s (j + 5)) := by
  rintro ⟨ξ, hξ⟩
  have hpos := shift_invariant_integerSlack_pos (j := j) (m := 4) hj hchain
    (by simpa [Nat.add_assoc] using hξ)
  have hval := (integerSlack_of_prefix_2_6_3_2 (t := shiftSeq s j)
    (by simp [shiftSeq, hs0])
    (by simp [shiftSeq, hs1])
    (by simp [shiftSeq, hs2])
    (by simp [shiftSeq, hs3])).2.2.2
  linarith

end Mahler.ShiftSlack
