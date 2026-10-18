import InfiniteSeries
import InfiniteComplexity

/-!
# A single infinite, fractionally admissible, high-complexity witness

This theorem combines the actual convergent real series and the cardinality
of contiguous blocks in ONE infinite stream. It refutes a fractional-only
linear-complexity claim; it does not construct a Z-number or assert that the
stream is the parity sequence of any positive integer Mahler orbit.

Run `lake build` using Lean and Mathlib v4.19.0, pinned by the toolchain and
Lake manifest. The earlier finite proofs remain standard-library-only;
these infinite proofs additionally use Mathlib.
-/

namespace Mahler.Adversarial

theorem infinite_adversarial_witness :
    ∃ s : ℕ → Bool,
      (∀ n, HasSum (tailTerm s n) (fractionalTail s n)) ∧
      (∀ n, 0 ≤ fractionalTail s n ∧ fractionalTail s n ≤ (9 / 19 : ℝ) ∧
        fractionalTail s n < (1 / 2 : ℝ)) ∧
      (∀ n, fractionalTail s (n + 1) =
        (3 / 2 : ℝ) * fractionalTail s n - (if s n then (1 / 2 : ℝ) else 0)) ∧
      (∀ L, 2 ^ (L / 3) ≤ blockComplexity s L) := by
  refine ⟨encodeStream universalStream, ?_, ?_, ?_, ?_⟩
  · exact fractionalTail_hasSum _
  · intro n
    exact ⟨fractionalTail_nonneg _ _, encoded_fractionalTail_bound _ _,
      (encoded_fractionalTail_admissible _ _).2⟩
  · exact fractionalTail_recurrence _
  · exact encoded_complexity_lower_bound

end Mahler.Adversarial
