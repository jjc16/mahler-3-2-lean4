import MahlerDemandA
import InfiniteAdversarial
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Disjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Formalization of All Identified Dead Ends

This module machine-checks every dead end encountered during the investigation
of the Google AI brainstorm and subsequent combinatorial/symbolic approaches:

1. **Rule 30 Nonlinear-to-Linear Collapse & Shift Direction Fallacies**:
   A horizontal white run at depth `t = 0` does not persist to `t = 1` and does
   not linearize vertical column traces; furthermore, the down-shift matrix is
   not the time-advance operator.
2. **F₂ Fibonacci Polynomial Power-of-Two Collapse Fallacy**:
   The recurrence `P_0 = 1, P_1 = x, P_{k+2} = x P_{k+1} + P_k (mod 2)` does not
   collapse to `x^(2^m) + 1` at powers of two (`P_4 = x^4 + x^2 + 1`,
   `P_8 = x^8 + x^6 + x^4 + 1`).
3. **Infinite Rank / Measure-Zero Implies Emptiness or Zero Entropy Fallacy**:
   An infinite system of full-rank linear prefix constraints has a nonempty
   intersection over all `L`, and its unique solution can have maximum
   exponential block complexity `2^L`.
4. **Lemma 4 Rightward Inversion & Single-Bit-Flip Entropy Fallacies**:
   Rule 30 is not rightward-invertible when the center bit is `true`, and
   flipping a single bit in the zero-entropy all-false stream keeps its block
   complexity bounded by `2` for every `L`.
5. **Well-Quasi-Ordering (Higman Subsequence vs. Contiguous Infix) Dilemma**:
   Subsequence embedding (`List.Sublist`) fails to preserve forbiddenness in
   both Rule 30 (`11` vs. `101`) and Mahler (`OO` vs. `OEO`), while contiguous
   subword containment (`List.IsInfix`) admits an infinite antichain `1 0^(n+1) 1`.
6. **Constraint-Set Containment & Non-Sofic β = 3/2 Obstructions**:
   The parity classes `E^n O` are pairwise disjoint, consecutive macro-step
   fractional intervals are disjoint, and `3/2` cannot satisfy any monic integer
   polynomial (blocking a sofic Parry β-shift presentation).
7. **Backward-Past Fallacy & Arbitrary Finite Survival (`a_0 = 2^N`)**:
   Integers `≡ 1 (mod 3)` have no predecessor under `step`, backward real steps
   from `[1, 3/2)` land in `[2/3, 1)`, and `a_0 = 2^N` survives `N` even steps
   before its first odd step `3^N`.
8. **Fractional-Only Demand B Fallacy**:
   Re-exported from `InfiniteAdversarial.infinite_adversarial_witness`.
-/

namespace Mahler.DeadEnds

open Mahler
open Mahler.Adversarial

/-! ## Dead End 1: Rule 30 Nonlinear-to-Linear Collapse & Shift Fallacies -/

/-- Standard Rule 30 local update `l ⊕ (c ∨ r)`. -/
def rule30Cell (l c r : Bool) : Bool :=
  xor l (c || r)

/-- Exact sideways left-inversion identity at a single cell. -/
theorem rule30_left_inv (l c r : Bool) :
    l = xor (rule30Cell l c r) (c || r) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- When `c = false` at one cell, left-inversion is locally linear at that cell. -/
theorem rule30_left_inv_at_zero (l r : Bool) :
    l = xor (rule30Cell l false r) r := by
  cases l <;> cases r <;> rfl

/-- One synchronous forward step of Rule 30 on a bi-infinite row. -/
def rule30Step (row : Int → Bool) (i : Int) : Bool :=
  rule30Cell (row (i - 1)) (row i) (row (i + 1))

/-- Space-time grid of Rule 30 from an initial row. -/
def rule30Grid (init : Int → Bool) : Nat → Int → Bool
  | 0, i => init i
  | t + 1, i => rule30Step (rule30Grid init t) i

/-- The single black cell at the origin at `t = 0`. -/
def singleSeed (i : Int) : Bool :=
  decide (i = 0)

/-- Although cells `-2` and `-1` are white (`false`) at `t = 0`, the nonlinear
term creates a black cell at `(i = -1, t = 1)` and `(i = -1, t = 2)` while
`(i = 0, t = 2)` is white, causing the claimed vertical linear trace equation
`x(i-1, t) = x(i, t+1) ⊕ x(i+1, t)` to fail at `(i = -1, t = 2)`. -/
theorem rule30_vertical_linearization_counterexample :
    rule30Grid singleSeed 0 (-2) = false ∧
    rule30Grid singleSeed 0 (-1) = false ∧
    rule30Grid singleSeed 1 (-1) = true ∧
    rule30Grid singleSeed 2 (-2) ≠
      xor (rule30Grid singleSeed 3 (-1)) (rule30Grid singleSeed 2 0) := by
  decide

/-- The brainstorm's displayed matrix `S` is a down-shift (prepending `false`),
whereas extracting `c_{i, d+1}` requires the up-shift (time-advance) operator. -/
def downShift (v : Nat → Bool) (t : Nat) : Bool :=
  match t with
  | 0 => false
  | t + 1 => v t

def upShift (v : Nat → Bool) (t : Nat) : Bool :=
  v (t + 1)

theorem downShift_ne_upShift :
    downShift (fun t => decide (t % 2 = 1)) ≠
      upShift (fun t => decide (t % 2 = 1)) := by
  intro h
  have h0 :
      downShift (fun t => decide (t % 2 = 1)) 0 =
        upShift (fun t => decide (t % 2 = 1)) 0 :=
    congrFun h 0
  revert h0
  decide

/-! ## Dead End 2: F₂ Fibonacci Polynomial Power-of-Two Collapse Fallacy -/

/-- Addition of coefficient lists over `F₂` (little-endian: index `i` is `x^i`). -/
def f2PolyAdd : List Bool → List Bool → List Bool
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => xor x y :: f2PolyAdd xs ys

/-- Multiplication by `x` over `F₂` (shifts coefficients up by one degree). -/
def f2MulX (p : List Bool) : List Bool :=
  false :: p

/-- Fibonacci polynomials over `F₂`:
`P_0(x) = 1`, `P_1(x) = x`, `P_{k+2}(x) = x P_{k+1}(x) + P_k(x) (mod 2)`. -/
def f2FibPoly : Nat → List Bool
  | 0 => [true]
  | 1 => [false, true]
  | k + 2 => f2PolyAdd (f2MulX (f2FibPoly (k + 1))) (f2FibPoly k)

/-- Monomial `x^n + 1` in little-endian coefficient form. -/
def xPowPlusOne (n : Nat) : List Bool :=
  match n with
  | 0 => [false]
  | k + 1 => true :: (List.replicate k false ++ [true])

/-- `P_2(x) = x^2 + 1` holds, but `P_4(x) = x^4 + x^2 + 1 ≠ x^4 + 1` and
`P_8(x) = x^8 + x^6 + x^4 + 1 ≠ x^8 + 1`, refuting the brainstorm's
"Freshman's Dream Collapse" `P_{2^m}(x) = x^{2^m} + 1`. -/
theorem f2FibPoly_power_of_two_counterexample :
    f2FibPoly 2 = xPowPlusOne 2 ∧
    f2FibPoly 4 = [true, false, true, false, true] ∧
    f2FibPoly 4 ≠ xPowPlusOne 4 ∧
    f2FibPoly 8 = [true, false, false, false, true, false, true, false, true] ∧
    f2FibPoly 8 ≠ xPowPlusOne 8 := by
  decide

theorem not_all_power_of_two_collapse :
    ¬ ∀ m : Nat, 1 ≤ m → f2FibPoly (2 ^ m) = xPowPlusOne (2 ^ m) := by
  intro h
  have h2 := h 2 (by decide)
  revert h2
  decide

/-! ## Dead End 3: Infinite Rank / Measure-Zero Implies Emptiness or Zero Entropy -/

/-- Full-rank `L × ∞` prefix extraction operator. -/
def prefixConstraint (L : Nat) (x : Nat → Bool) : Fin L → Bool :=
  fun i => x i.val

/-- Every target vector `b : Fin L → Bool` is hit, so the rank of the `L`-th
constraint system is `L` (surjective onto `{0,1}^L`). -/
theorem prefixConstraint_surjective (L : Nat) :
    Function.Surjective (prefixConstraint L) := by
  intro b
  refine ⟨fun n => if h : n < L then b ⟨n, h⟩ else false, ?_⟩
  funext i
  simp [prefixConstraint, i.isLt]

/-- Yet the infinite intersection of all `L` constraint systems around
`universalStream` is nonempty and its unique solution has maximum exponential
block complexity `2^L` for every `L`. -/
theorem infinite_rank_has_maximal_complexity_solution :
    ∃ x : Nat → Bool,
      (∀ L : Nat, prefixConstraint L x = prefixConstraint L universalStream) ∧
      (∀ L : Nat, blockComplexity x L = 2 ^ L) := by
  refine ⟨universalStream, fun _ => rfl, ?_⟩
  intro L
  classical
  apply Nat.le_antisymm
  · simpa [blockComplexity, Fintype.card_fun] using
      (Fintype.card_subtype_le fun w : Fin L → Bool => blockOccurs universalStream w)
  · have hall : ∀ w : Fin L → Bool, blockOccurs universalStream w :=
      fun w => universalStream_contains w
    have hcard :
        Fintype.card {w : Fin L → Bool // blockOccurs universalStream w} =
          Fintype.card (Fin L → Bool) :=
      Fintype.card_congr
        { toFun := fun x => x.val
          invFun := fun w => ⟨w, hall w⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun _ => rfl }
    simpa [blockComplexity, Fintype.card_fun] using hcard.ge

/-! ## Dead End 4: Lemma 4 Rightward Inversion & Single-Bit-Flip Entropy Fallacies -/

/-- When the middle cell is `true`, Rule 30's output is independent of the right
neighbor, so no function `Ψ` can recover the right neighbor. -/
theorem rule30_right_neighbor_unrecoverable :
    ¬ ∃ Ψ : Bool → Bool → Bool → Bool,
      ∀ l c r : Bool, Ψ l c (rule30Cell l c r) = r := by
  rintro ⟨Ψ, hΨ⟩
  have h0 := hΨ false true false
  have h1 := hΨ false true true
  have heq : rule30Cell false true false = rule30Cell false true true := rfl
  rw [heq] at h0
  have : false = true := h0.symm.trans h1
  cases this

/-- Flipping the initial bit of the all-false stream. -/
def singleBitFlipStream (n : Nat) : Bool :=
  decide (n = 0)

/-- A single bit flip on the zero-entropy all-false stream does not create
exponential word growth: every occurring length-`L` block is either all-false
or starts at index `0`, so at most `2` blocks of length `L` exist. -/
theorem singleBitFlip_blockComplexity_le_two (L : Nat) :
    blockComplexity singleBitFlipStream L ≤ 2 := by
  classical
  let zeroBlock : Fin L → Bool := fun _ => false
  let headBlock : Fin L → Bool := fun i => singleBitFlipStream i.val
  let toBool : {w : Fin L → Bool // blockOccurs singleBitFlipStream w} → Bool :=
    fun w => decide (w.val = headBlock)
  have hinj : Function.Injective toBool := by
    intro u v huv
    have hcase (w : {w : Fin L → Bool // blockOccurs singleBitFlipStream w}) :
        w.val = headBlock ∨ w.val = zeroBlock := by
      rcases w.property with ⟨start, hstart⟩
      by_cases hs : start = 0
      · left
        funext i
        simpa [headBlock, hs] using (hstart i).symm
      · right
        funext i
        have hne : start + i.val ≠ 0 := by omega
        have hfalse : singleBitFlipStream (start + i.val) = false :=
          decide_eq_false hne
        simpa [zeroBlock, hfalse] using (hstart i).symm
    rcases hcase u with hu | hu <;> rcases hcase v with hv | hv
    · exact Subtype.ext (hu.trans hv.symm)
    · have : toBool u = true := by simp [toBool, hu]
      have : toBool v = true := huv ▸ this
      have hvh : v.val = headBlock := of_decide_eq_true this
      exact Subtype.ext (hu.trans hvh.symm)
    · have : toBool v = true := by simp [toBool, hv]
      have : toBool u = true := huv.symm ▸ this
      have huh : u.val = headBlock := of_decide_eq_true this
      exact Subtype.ext (huh.trans hv.symm)
    · exact Subtype.ext (hu.trans hv.symm)
  simpa [blockComplexity] using Fintype.card_le_of_injective toBool hinj

/-! ## Dead End 5: WQO Subsequence vs. Contiguous Infix Dilemma -/

/-- Three even-time visible samples `(c_0, c_2, c_4)` in column 1 beside the
alternating center wall `x(0, t) = decide (t % 2 = 1)` from a width-5 right-hand
initial state `(r_1, r_2, r_3, r_4, r_5)`. -/
def visible3 (r1 r2 r3 r4 r5 : Bool) : List Bool :=
  let t1_1 := rule30Cell false r1 r2
  let t1_2 := rule30Cell r1 r2 r3
  let t1_3 := rule30Cell r2 r3 r4
  let t1_4 := rule30Cell r3 r4 r5
  let t2_1 := rule30Cell true t1_1 t1_2
  let t2_2 := rule30Cell t1_1 t1_2 t1_3
  let t2_3 := rule30Cell t1_2 t1_3 t1_4
  let t3_1 := rule30Cell false t2_1 t2_2
  let t3_2 := rule30Cell t2_1 t2_2 t2_3
  let t4_1 := rule30Cell true t3_1 t3_2
  [r1, t2_1, t4_1]

/-- Higman's subsequence order does not preserve Rule 30 forbiddenness:
`[true, true]` (`11`) is a subsequence of `[true, false, true]` (`101`),
`11` is never a prefix of any real visible word, yet `101` is realized. -/
theorem rule30_subsequence_dead_end :
    List.Sublist [true, true] [true, false, true] ∧
    (∀ r1 r2 r3 r4 r5 : Bool,
      (visible3 r1 r2 r3 r4 r5).take 2 ≠ [true, true]) ∧
    (∃ r1 r2 r3 r4 r5 : Bool,
      visible3 r1 r2 r3 r4 r5 = [true, false, true]) := by
  refine ⟨by decide, by decide, ⟨true, false, false, true, true, by decide⟩⟩

/-- Exact rational fractional-part admissibility for finite Mahler parity words. -/
def mahlerWordAdmissible : ℚ → List Bool → Prop
  | r, [] => 0 ≤ r ∧ r < 1 / 2
  | r, false :: bs => 0 ≤ r ∧ r < 1 / 3 ∧ mahlerWordAdmissible ((3 / 2) * r) bs
  | r, true :: bs =>
      1 / 3 ≤ r ∧ r < 1 / 2 ∧ mahlerWordAdmissible ((3 / 2) * r - 1 / 2) bs

/-- Higman's subsequence order does not preserve Mahler forbiddenness:
`[true, true]` (`OO`) is a subsequence of `[true, false, true]` (`OEO`),
`OO` has no valid starting fractional part, yet `OEO` is valid at `r = 53/108`. -/
theorem mahler_subsequence_dead_end :
    List.Sublist [true, true] [true, false, true] ∧
    (∀ r : ℚ, ¬ mahlerWordAdmissible r [true, true]) ∧
    mahlerWordAdmissible (53 / 108 : ℚ) [true, false, true] := by
  refine ⟨by decide, ?_, ?_⟩
  · intro r h
    rcases h with ⟨h1, h2, h3, _⟩
    linarith
  · simp only [mahlerWordAdmissible]
    norm_num

/-- Candidate antichain words `1 0^(n+1) 1` for contiguous subword containment. -/
def zeroGapWord (n : Nat) : List Bool :=
  true :: (List.replicate (n + 1) false ++ [true])

private theorem count_true_replicate_false (n : Nat) :
    (List.replicate n false).count true = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem replicate_append_true_ne {a b : Nat} (hab : a < b) (t : List Bool) :
    List.replicate a false ++ (true :: t) ≠ List.replicate b false ++ [true] := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => omega
      | succ b => simp [List.replicate_succ]
  | succ a ih =>
      cases b with
      | zero => omega
      | succ b =>
          simp only [List.replicate_succ, List.cons_append, ne_eq, List.cons.injEq, true_and]
          exact ih (by omega)

/-- Contiguous subword containment (`<:+:`) is not a well-quasi-order:
for all `i < j`, `zeroGapWord i` is never an infix of `zeroGapWord j`. -/
theorem zeroGapWord_not_infix {i j : Nat} (hij : i < j) :
    ¬ (zeroGapWord i <:+: zeroGapWord j) := by
  rintro ⟨s, t, hst⟩
  cases s with
  | nil =>
      simp only [zeroGapWord, List.nil_append, List.cons_append, List.cons.injEq,
        true_and, List.append_assoc] at hst
      exact replicate_append_true_ne (Nat.succ_lt_succ hij) t hst
  | cons b bs =>
      simp only [zeroGapWord, List.cons_append, List.cons.injEq] at hst
      have htrues := congrArg (fun w : List Bool => w.count true) hst.2
      simp [List.count_append, count_true_replicate_false] at htrues
      omega

/-! ## Dead End 6: Constraint Containment & Non-Sofic β = 3/2 Obstructions -/

/-- Starting integers whose parity sequence begins with `n` evens followed by an odd. -/
def evenRunOddClass (n : Nat) : Set Nat :=
  {m : Nat | (∀ k < n, orbit m k % 2 = 0) ∧ orbit m n % 2 = 1}

/-- The classes `E^n O` are pairwise disjoint for `i ≠ j`, forming an infinite
incomparable family under constraint-set inclusion. -/
theorem evenRunOddClass_disjoint {i j : Nat} (hij : i ≠ j) :
    Disjoint (evenRunOddClass i) (evenRunOddClass j) := by
  rw [Set.disjoint_iff]
  rintro m ⟨⟨hi0, hi1⟩, ⟨hj0, hj1⟩⟩
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have := hj0 i hlt
    omega
  · have := hi0 j hgt
    omega

/-- The admissible fractional intervals for the odd-to-odd macro blocks `OE`
(`[13/27, 1/2)`) and `OEE` (`[35/81, 13/27)`) are disjoint. -/
theorem oddMacroIntervals_disjoint :
    Disjoint {r : ℝ | (13 / 27 : ℝ) ≤ r ∧ r < 1 / 2}
      {r : ℝ | (35 / 81 : ℝ) ≤ r ∧ r < 13 / 27} := by
  rw [Set.disjoint_iff]
  rintro r ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
  linarith

/-- `β = 3/2` cannot satisfy any monic integer polynomial of positive degree:
cleared of denominators, `3^(d+1)` is odd while `2 * K` is even. This blocks
any eventually periodic Parry β-expansion of `1` (and hence a sofic β-shift). -/
theorem three_halves_not_monic_int_root (d : Nat) (K : Int) :
    (3 : Int) ^ (d + 1) + 2 * K ≠ 0 := by
  have hmod : (3 : Int) ^ (d + 1) % 2 = 1 := by
    induction d with
    | zero => decide
    | succ d ih =>
        rw [ pow_succ, Int.mul_emod, ih ]
        decide
  intro h
  have h0 : ((3 : Int) ^ (d + 1) + 2 * K) % 2 = 0 := by rw [h]; rfl
  omega

/-! ## Dead End 7: Backward-Past Fallacy & Arbitrary Finite Survival (`a_0 = 2^N`) -/

/-- No integer `b ≡ 1 (mod 3)` has an integer predecessor under `step`. -/
theorem step_mod_three_ne_one (a : Nat) :
    step a % 3 ≠ 1 := by
  unfold step
  omega

/-- Any real `ξ ∈ [1, 3/2)` has immediate predecessor `(2/3) * ξ ∈ [2/3, 1)`,
whose fractional part exceeds `1/2`. -/
theorem backward_step_enters_forbidden_half {ξ : ℝ}
    (hlo : 1 ≤ ξ) (hhi : ξ < 3 / 2) :
    (1 / 2 : ℝ) < (2 / 3 : ℝ) * ξ ∧ (2 / 3 : ℝ) * ξ < 1 := by
  constructor <;> linarith

/-- Exact closed form for the first `N` steps starting from `a_0 = 2^N`. -/
theorem orbit_two_pow (N k : Nat) (hk : k ≤ N) :
    orbit (2 ^ N) k = 3 ^ k * 2 ^ (N - k) := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
      have hk' : k ≤ N := by omega
      have hsub : N - k = (N - (k + 1)) + 1 := by omega
      have hmul :
          3 ^ k * 2 ^ (N - k) = 2 * (3 ^ k * 2 ^ (N - (k + 1))) := by
        rw [hsub, Nat.pow_succ]
        ring
      have hstep :
          step (3 ^ k * 2 ^ (N - k)) = 3 ^ (k + 1) * 2 ^ (N - (k + 1)) := by
        rw [hmul, Nat.pow_succ]
        have hdiv : ∀ m : Nat, step (2 * m) = 3 * m := by
          intro m
          unfold step
          omega
        rw [hdiv]
        ring
      simpa [orbit, ih hk'] using hstep

/-- Starting at `a_0 = 2^N` produces `N` consecutive even integers before
landing on the odd integer `3^N` at step `N`. -/
theorem orbit_two_pow_even_before (N k : Nat) (hk : k < N) :
    orbit (2 ^ N) k % 2 = 0 := by
  rw [orbit_two_pow N k (by omega)]
  have hsub : N - k = (N - k - 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  have hmul :
      3 ^ k * (2 ^ (N - k - 1) * 2) = 2 * (3 ^ k * 2 ^ (N - k - 1)) := by
    ring
  rw [hmul]
  omega

theorem orbit_two_pow_odd_at_horizon (N : Nat) :
    orbit (2 ^ N) N % 2 = 1 := by
  rw [orbit_two_pow N N (Nat.le_refl N), Nat.sub_self, Nat.pow_zero, Nat.mul_one]
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-! ## Master Certification of All Dead Ends -/

theorem all_dead_ends_certified :
    (rule30Grid singleSeed 2 (-2) ≠
      xor (rule30Grid singleSeed 3 (-1)) (rule30Grid singleSeed 2 0)) ∧
    (¬ ∀ m : Nat, 1 ≤ m → f2FibPoly (2 ^ m) = xPowPlusOne (2 ^ m)) ∧
    (∃ x : Nat → Bool,
      (∀ L : Nat, prefixConstraint L x = prefixConstraint L universalStream) ∧
      (∀ L : Nat, blockComplexity x L = 2 ^ L)) ∧
    (¬ ∃ Ψ : Bool → Bool → Bool → Bool,
      ∀ l c r : Bool, Ψ l c (rule30Cell l c r) = r) ∧
    (∀ L : Nat, blockComplexity singleBitFlipStream L ≤ 2) ∧
    (∀ i j : Nat, i < j → ¬ (zeroGapWord i <:+: zeroGapWord j)) ∧
    (∀ i j : Nat, i ≠ j → Disjoint (evenRunOddClass i) (evenRunOddClass j)) ∧
    (∀ d : Nat, ∀ K : Int, (3 : Int) ^ (d + 1) + 2 * K ≠ 0) ∧
    (∀ a : Nat, step a % 3 ≠ 1) ∧
    (∀ N k : Nat, k < N → orbit (2 ^ N) k % 2 = 0) ∧
    (∃ s : ℕ → Bool,
      (∀ n, HasSum (tailTerm s n) (fractionalTail s n)) ∧
      (∀ n, 0 ≤ fractionalTail s n ∧ fractionalTail s n ≤ (9 / 19 : ℝ) ∧
        fractionalTail s n < (1 / 2 : ℝ)) ∧
      (∀ n, fractionalTail s (n + 1) =
        (3 / 2 : ℝ) * fractionalTail s n - (if s n then (1 / 2 : ℝ) else 0)) ∧
      (∀ L, 2 ^ (L / 3) ≤ blockComplexity s L)) :=
  ⟨rule30_vertical_linearization_counterexample.2.2.2,
   not_all_power_of_two_collapse,
   infinite_rank_has_maximal_complexity_solution,
   rule30_right_neighbor_unrecoverable,
   singleBitFlip_blockComplexity_le_two,
   fun _ _ hij => zeroGapWord_not_infix hij,
   fun _ _ hij => evenRunOddClass_disjoint hij,
   three_halves_not_monic_int_root,
   step_mod_three_ne_one,
   orbit_two_pow_even_before,
   infinite_adversarial_witness⟩

end Mahler.DeadEnds
