import InfiniteEncoding
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Infinite fractional trajectories

`fractionalTail s n` is the real infinite weighted sum of the bits of s
starting at position n. Summability is proved before using this sum.
For every encoded stream, all tails lie in [0, 9/19], and consecutive
tails satisfy the exact Mahler fractional recurrence.
-/

namespace Mahler.Adversarial

noncomputable def tailTerm (s : ℕ → Bool) (n j : ℕ) : ℝ :=
  (if s (n + j) then 1 else 0) * (1 / 3) * (2 / 3 : ℝ) ^ j

noncomputable def fractionalTail (s : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑' j, tailTerm s n j

theorem tailTerm_nonneg (s : ℕ → Bool) (n j : ℕ) : 0 ≤ tailTerm s n j := by
  unfold tailTerm
  positivity

theorem tailTerm_summable (s : ℕ → Bool) (n : ℕ) :
    Summable (tailTerm s n) := by
  apply Summable.of_nonneg_of_le (tailTerm_nonneg s n)
    (f := fun j => (1 / 3 : ℝ) * (2 / 3 : ℝ) ^ j)
  · intro j
    unfold tailTerm
    split_ifs
    · simp
    · simp only [zero_mul]
      positivity
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) < 1)).mul_left _

theorem fractionalTail_hasSum (s : ℕ → Bool) (n : ℕ) :
    HasSum (tailTerm s n) (fractionalTail s n) :=
  (tailTerm_summable s n).hasSum

theorem fractionalTail_nonneg (s : ℕ → Bool) (n : ℕ) :
    0 ≤ fractionalTail s n :=
  tsum_nonneg (tailTerm_nonneg s n)

theorem fractionalTail_head (s : ℕ → Bool) (n : ℕ) :
    fractionalTail s n =
      (if s n then (1 / 3 : ℝ) else 0) + (2 / 3 : ℝ) * fractionalTail s (n + 1) := by
  have hshift (j : ℕ) :
      tailTerm s n (j + 1) = (2 / 3 : ℝ) * tailTerm s (n + 1) j := by
    simp only [tailTerm, Nat.add_right_comm n j 1, pow_succ]
    ring_nf
  rw [fractionalTail, (tailTerm_summable s n).tsum_eq_zero_add]
  simp_rw [hshift]
  rw [tsum_mul_left]
  simp [tailTerm, fractionalTail]

theorem fractionalTail_recurrence (s : ℕ → Bool) (n : ℕ) :
    fractionalTail s (n + 1) =
      (3 / 2 : ℝ) * fractionalTail s n - (if s n then (1 / 2 : ℝ) else 0) := by
  have h := fractionalTail_head s n
  split_ifs at h ⊢ <;> linarith

private theorem aligned_tail_bound (s : ℕ → Bool) (k : ℕ) :
    fractionalTail (encodeStream s) (3 * k) ≤ (9 / 19 : ℝ) := by
  have hinj : Function.Injective (fun j : ℕ => 3 * j) := by
    intro a b h
    dsimp only at h
    omega
  have hsupport : Function.support (tailTerm (encodeStream s) (3 * k)) ⊆
      Set.range (fun j : ℕ => 3 * j) := by
    intro j hj
    by_cases hz : j % 3 = 0
    · exact ⟨j / 3, by dsimp only; omega⟩
    · simp [Function.mem_support, tailTerm, encodeStream, Nat.add_mod, hz] at hj
  have hsum := hinj.tsum_eq hsupport
  have hs := (tailTerm_summable (encodeStream s) (3 * k)).comp_injective hinj
  have hg : Summable (fun j : ℕ => (1 / 3 : ℝ) * (8 / 27 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 8 / 27)
      (by norm_num : (8 / 27 : ℝ) < 1)).mul_left _
  have hterm (j : ℕ) :
      tailTerm (encodeStream s) (3 * k) (3 * j) ≤
        (1 / 3 : ℝ) * (8 / 27 : ℝ) ^ j := by
    have hp : (2 / 3 : ℝ) ^ (3 * j) = (8 / 27 : ℝ) ^ j := by
      rw [pow_mul]
      norm_num
    unfold tailTerm
    rw [hp]
    split_ifs
    · simp
    · simp only [zero_mul]
      positivity
  calc
    fractionalTail (encodeStream s) (3 * k) =
        ∑' j, tailTerm (encodeStream s) (3 * k) (3 * j) := hsum.symm
    _ ≤ ∑' j : ℕ, (1 / 3 : ℝ) * (8 / 27 : ℝ) ^ j :=
        Summable.tsum_le_tsum hterm hs hg
    _ = 9 / 19 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 8 / 27) (by norm_num : (8 / 27 : ℝ) < 1)]
      norm_num

theorem encoded_fractionalTail_bound (s : ℕ → Bool) (n : ℕ) :
    fractionalTail (encodeStream s) n ≤ (9 / 19 : ℝ) := by
  have hphase (k : ℕ) :
      fractionalTail (encodeStream s) (3 * k + 1) ≤ (9 / 19 : ℝ) ∧
      fractionalTail (encodeStream s) (3 * k + 2) ≤ (9 / 19 : ℝ) := by
    have h1 := fractionalTail_head (encodeStream s) (3 * k + 1)
    have h2 := fractionalTail_head (encodeStream s) (3 * k + 2)
    have hnext := aligned_tail_bound s (k + 1)
    have heq1 : 3 * k + 1 + 1 = 3 * k + 2 := by omega
    have heq2 : 3 * k + 2 + 1 = 3 * (k + 1) := by omega
    simp only [encodeStream_three_mul_add_one, encodeStream_three_mul_add_two,
      Bool.false_eq_true, if_false, zero_add, heq1, heq2] at h1 h2
    constructor <;> linarith
  have hr : n = 3 * (n / 3) ∨ n = 3 * (n / 3) + 1 ∨ n = 3 * (n / 3) + 2 := by
    omega
  rcases hr with h | h | h
  · conv_lhs => rw [h]
    exact aligned_tail_bound s (n / 3)
  · conv_lhs => rw [h]
    exact (hphase (n / 3)).1
  · conv_lhs => rw [h]
    exact (hphase (n / 3)).2

theorem encoded_fractionalTail_admissible (s : ℕ → Bool) (n : ℕ) :
    0 ≤ fractionalTail (encodeStream s) n ∧
      fractionalTail (encodeStream s) n < (1 / 2 : ℝ) := by
  constructor
  · exact fractionalTail_nonneg _ _
  · have h := encoded_fractionalTail_bound s n
    linarith

theorem encoded_fractionalTail_margin (s : ℕ → Bool) (n : ℕ) :
    (1 / 38 : ℝ) ≤ 1 / 2 - fractionalTail (encodeStream s) n := by
  have h := encoded_fractionalTail_bound s n
  linarith

end Mahler.Adversarial
