import InfiniteEncoding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# Complexity of one universal encoded stream

Every finite binary word receives an injective natural-number index `c` at
least its length. Place the word in the interval starting at `c * c`; these
intervals are disjoint. Extending the resulting assignment by `false` gives
one infinite stream containing every finite word, not a family of streams.

For any length `L`, an occurrence of each word of length `L / 3` yields an
aligned length-`L` block in the encoded stream. Sampling positions `3 * i`
recovers the word, so these occurring blocks are distinct, including the
single empty word when `L = 0`.
-/

namespace Mahler.Adversarial

/-- A word occurs if it agrees with a contiguous block at some start index. -/
def blockOccurs (s : ℕ → Bool) {L : ℕ} (w : Fin L → Bool) : Prop :=
  ∃ start : ℕ, ∀ i : Fin L, s (start + i.val) = w i

/-- The number of distinct occurring words, rather than the number of occurrences. -/
noncomputable def blockComplexity (s : ℕ → Bool) (L : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin L → Bool // blockOccurs s w}

private abbrev BinaryWord := Σ L : ℕ, Fin L → Bool

private noncomputable def wordIndex (w : BinaryWord) : ℕ :=
  Nat.pair w.1 ((Fintype.equivFin (Fin w.1 → Bool)) w.2).val

private theorem wordIndex_length_le (w : BinaryWord) : w.1 ≤ wordIndex w :=
  Nat.left_le_pair _ _

private theorem wordIndex_injective : Function.Injective wordIndex := by
  rintro ⟨n, u⟩ ⟨m, v⟩ h
  have hp := Nat.pair_eq_pair.mp h
  rcases hp with ⟨hn, hc⟩
  dsimp at hn
  subst m
  have hw : u = v :=
    (Fintype.equivFin (Fin n → Bool)).injective (Fin.ext hc)
  subst v
  rfl

private noncomputable def wordPosition (x : Σ w : BinaryWord, Fin w.1) : ℕ :=
  wordIndex x.1 * wordIndex x.1 + x.2.val

private theorem wordInterval_before {a b i j : ℕ} (hab : a < b) (hi : i < a) :
    a * a + i < b * b + j := by
  calc
    a * a + i < a * a + a := Nat.add_lt_add_left hi _
    _ = a * (a + 1) := (Nat.mul_succ a a).symm
    _ ≤ a * b := Nat.mul_le_mul_left a hab
    _ ≤ b * b := Nat.mul_le_mul_right b (Nat.le_of_lt hab)
    _ ≤ b * b + j := Nat.le_add_right _ _

private theorem wordPosition_injective : Function.Injective wordPosition := by
  rintro ⟨w, i⟩ ⟨v, j⟩ h
  have hi : i.val < wordIndex w := lt_of_lt_of_le i.isLt (wordIndex_length_le w)
  have hj : j.val < wordIndex v := lt_of_lt_of_le j.isLt (wordIndex_length_le v)
  have hc : wordIndex w = wordIndex v := by
    rcases lt_trichotomy (wordIndex w) (wordIndex v) with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (wordInterval_before hlt hi)) h)
    · exact heq
    · exact False.elim ((ne_of_lt (wordInterval_before hgt hj)) h.symm)
  have hw := wordIndex_injective hc
  subst v
  have hij : i = j := Fin.ext (by simpa [wordPosition] using h)
  subst j
  rfl

/-- One infinite binary stream containing every finite binary word. Its bits
outside the disjoint word intervals are `false`. -/
noncomputable def universalStream : ℕ → Bool :=
  Function.extend wordPosition (fun x => x.1.2 x.2) (fun _ => false)

/-- Universality follows from the disjoint interval construction. -/
theorem universalStream_contains {L : ℕ} (w : Fin L → Bool) :
    blockOccurs universalStream w := by
  refine ⟨wordIndex ⟨L, w⟩ * wordIndex ⟨L, w⟩, ?_⟩
  intro i
  exact wordPosition_injective.extend_apply _ _ ⟨⟨L, w⟩, i⟩

/-- The encoded single stream has at least `2^(L/3)` distinct length-`L`
contiguous blocks. There is no positivity assumption on `L`. -/
theorem encoded_complexity_lower_bound (L : ℕ) :
    2 ^ (L / 3) ≤ blockComplexity (encodeStream universalStream) L := by
  classical
  let start : (Fin (L / 3) → Bool) → ℕ :=
    fun w => Classical.choose (universalStream_contains w)
  have hstart (w : Fin (L / 3) → Bool) (i : Fin (L / 3)) :
      universalStream (start w + i.val) = w i :=
    Classical.choose_spec (universalStream_contains w) i
  let blocks : (Fin (L / 3) → Bool) →
      {w : Fin L → Bool // blockOccurs (encodeStream universalStream) w} :=
    fun w => ⟨fun i => encodeStream universalStream (3 * start w + i.val),
      ⟨3 * start w, fun _ => rfl⟩⟩
  have hinj : Function.Injective blocks := by
    intro u v huv
    funext i
    have hi : 3 * i.val < L := by
      have := i.isLt
      omega
    have heq := congrArg (fun b => b.val ⟨3 * i.val, hi⟩) huv
    change encodeStream universalStream (3 * start u + 3 * i.val) =
      encodeStream universalStream (3 * start v + 3 * i.val) at heq
    rw [← Nat.mul_add, ← Nat.mul_add, encodeStream_three_mul,
      encodeStream_three_mul] at heq
    exact (hstart u i).symm.trans (heq.trans (hstart v i))
  simpa [blockComplexity, Fintype.card_fun] using
    Fintype.card_le_of_injective blocks hinj

end Mahler.Adversarial
