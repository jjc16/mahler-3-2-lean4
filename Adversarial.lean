import Std

/-!
# Adversarial test of fractional-only Demand B

Encode each arbitrary input bit by `000` or `100`. The encoding is injective
and triples word length. Its normalized weight is bounded by 9/19, even
after prepending zeros (as happens when starting inside an encoded block).

For a word w, `numerator w / 3^w.length` represents the finite sum
`sum_j w[j] * 2^j / 3^(j+1)`. All inequalities below clear denominators.

The mathematical infinite extension uses the convergent geometric series:
any tail has at most one 1 in each consecutive group of three positions, so
its weight is at most `(1/3)/(1-(2/3)^3) = 9/19 < 1/2`. An infinite input
containing every finite binary word yields at least `2^n` distinct encoded
blocks of length `3*n`, in a SINGLE infinite output sequence.

Lean verifies the finite weight bounds, zero-prefix bounds, length formula,
and injectivity here. The infinite-series and infinite-word complexity
arguments are formalized in InfiniteSeries.lean and InfiniteComplexity.lean,
and combined into one witness in InfiniteAdversarial.lean.
Nothing here establishes compatibility with a positive integer Mahler orbit.
-/

namespace Mahler.Adversarial

def encode : List Bool → List Bool
  | [] => []
  | b :: bs => b :: false :: false :: encode bs

def numerator : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 3 ^ bs.length else 0) + 2 * numerator bs

theorem encode_length (w : List Bool) : (encode w).length = 3 * w.length := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
      simp only [encode, List.length_cons, ih]
      omega

theorem encode_injective {u v : List Bool} (h : encode u = encode v) : u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons b bs => simp [encode] at h
  | cons a as ih =>
      cases v with
      | nil => simp [encode] at h
      | cons b bs =>
          have hab : a = b := (List.cons.inj h).1
          have ht : encode as = encode bs :=
            (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2
          subst b
          exact congrArg (List.cons a) (ih ht)

theorem encoded_weight_bound (w : List Bool) :
    19 * numerator (encode w) ≤ 9 * 3 ^ (encode w).length := by
  induction w with
  | nil => decide
  | cons b bs ih =>
      cases b <;>
        simp only [encode, numerator, Bool.false_eq_true, if_false, if_true,
          List.length_cons, Nat.pow_succ] <;>
        omega

theorem zero_prefix_weight_bound (zeros : Nat) (w : List Bool) :
    19 * numerator (List.replicate zeros false ++ encode w) ≤
      9 * 3 ^ (List.replicate zeros false ++ encode w).length := by
  induction zeros with
  | zero => simpa using encoded_weight_bound w
  | succ zeros ih =>
      simp only [List.replicate_succ, List.cons_append, numerator,
        Bool.false_eq_true, if_false, List.length_cons, Nat.pow_succ]
      omega

theorem zero_prefix_strict_half (zeros : Nat) (w : List Bool) :
    2 * numerator (List.replicate zeros false ++ encode w) <
      3 ^ (List.replicate zeros false ++ encode w).length := by
  have h := zero_prefix_weight_bound zeros w
  have hp : 0 < 3 ^ (List.replicate zeros false ++ encode w).length :=
    Nat.pow_pos (by decide)
  omega

end Mahler.Adversarial
