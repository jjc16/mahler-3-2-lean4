import ParitySplitPinch
import Mathlib.Data.Real.Archimedean

/-!
# Approach 4: The Time-Homogeneous Coupled Product Graph `G_{K, B}`

Whereas the exact `β = 3/2` shift is non-sofic (`DeadEnds.three_halves_not_monic_int_root`),
we obtain a rigorous, finite, time-homogeneous outer-approximating automaton
by coupling:
- the `K`-bit 2-adic residue `res = orbit m n % 2^K` in `{0, ..., 2^K - 1}`, and
- the uniform rational fractional bin `b = ⌊2 * B * fracPart m ξ n⌋₊` in `{0, ..., B - 1}`.

1. **Exact Two-Lift Residue Transition Law (`step_mod_two_pow_dichotomy`)**:
   For any `K ≥ 1` and `a`, `step a % 2^K` equals either `step (a % 2^K) % 2^K`
   or `(step (a % 2^K) + 2^(K - 1)) % 2^K`.
2. **Exact Rational-Bin Overlap Law (`validBinStep_of_validCompanion`)**:
   Across one step `n → n + 1`, the bin indices `b_n = ⌊2 B r_n⌋₊` and
   `b_{n+1} = ⌊2 B r_{n+1}⌋₊` must satisfy
   `3 * b_n < 2 * b_{n+1} + 2 + 2 * B * ε_n` and
   `2 * b_{n+1} + 2 * B * ε_n < 3 * (b_n + 1)`.
3. **Trajectory Projection & Pruning Soundness (`residueSurvives_of_validCompanionUpTo`,
   `no_validCompanionUpTo_of_residueSurvives_false`)**:
   Every valid trajectory of length `T` projects to a valid `T`-step walk in the
   finite directed graph `G_{K, B}`. Consequently, if iterative dead-end pruning
   eliminates all bins over residue `m % 2^K` at depth `T`, no real companion
   `ξ` can survive `T` steps from `m`.
4. **Certified Finite-Graph Pruning (`g3_6_pruned_residues`, `mod_eight_2_3_7_excluded`)**:
   Even on the 48-state graph `G_{3, 6}` (`K = 3, B = 6`), 3 rounds of dead-end
   pruning eliminate residues `2, 3, 7 (mod 8)`.
-/

namespace Mahler.ProductGraph

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch

/-! ## 1. Exact Two-Lift Residue Transition Law on `ℤ / 2^K ℤ` -/

/-- For any `K ≥ 1` and `a : ℕ`, the next residue `step a % 2^K` is one of at
most two lifts determined by `a % 2^K`. -/
theorem step_mod_two_pow_dichotomy {K : ℕ} (hK : 1 ≤ K) (a : ℕ) :
    step a % 2 ^ K = step (a % 2 ^ K) % 2 ^ K ∨
      step a % 2 ^ K = (step (a % 2 ^ K) + 2 ^ (K - 1)) % 2 ^ K := by
  let q := a / 2 ^ K
  let r := a % 2 ^ K
  have ha : a = 2 ^ K * q + r := (Nat.div_add_mod a (2 ^ K)).symm
  have hK_eq : K = (K - 1) + 1 := by omega
  have hstep_a : step a = 3 * 2 ^ (K - 1) * q + step r := by
    have hmul : 2 ^ K * q = 2 * (2 ^ (K - 1) * q) := by
      conv_lhs => rw [hK_eq, Nat.pow_succ]
      ring
    conv_lhs => rw [ha, hmul]
    rw [step_two_mul_add]
    ring
  let q' := q / 2
  let bit := q % 2
  have hq : q = 2 * q' + bit := (Nat.div_add_mod q 2).symm
  have h2K : 2 ^ K = 2 ^ (K - 1) * 2 := by
    conv_lhs => rw [hK_eq, Nat.pow_succ]
  have hbit : bit = 0 ∨ bit = 1 := by omega
  rcases hbit with hb0 | hb1
  · left
    have hmult :
        3 * 2 ^ (K - 1) * q + step r = step r + 2 ^ K * (3 * q') := by
      rw [hq, hb0, h2K]
      ring
    rw [hstep_a, hmult, Nat.add_mul_mod_self_left]
  · right
    have hmult :
        3 * 2 ^ (K - 1) * q + step r =
          (step r + 2 ^ (K - 1)) + 2 ^ K * (3 * q' + 1) := by
      rw [hq, hb1, h2K]
      ring
    rw [hstep_a, hmult, Nat.add_mul_mod_self_left]

theorem mod_two_of_mod_two_pow {K : ℕ} (hK : 1 ≤ K) (a : ℕ) :
    (a % 2 ^ K) % 2 = a % 2 := by
  have hdvd : 2 ∣ 2 ^ K := by
    have hK_eq : K = (K - 1) + 1 := by omega
    rw [hK_eq, Nat.pow_succ]
    exact ⟨2 ^ (K - 1), by ring⟩
  exact Nat.mod_mod_of_dvd a hdvd

/-! ## 2. Exact Rational-Bin Discretization of `[0, 1/2)` -/

/-- Map a fractional part `r ∈ [0, 1/2)` to its uniform bin `⌊2 B r⌋₊ ∈ {0, ..., B - 1}`. -/
noncomputable def binIndex (B : ℕ) (r : ℝ) : ℕ :=
  ⌊2 * (B : ℝ) * r⌋₊

theorem binIndex_bounds {B : ℕ} (hB : 1 ≤ B) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1 / 2) :
    binIndex B r < B ∧
    (binIndex B r : ℝ) ≤ 2 * (B : ℝ) * r ∧
    2 * (B : ℝ) * r < (binIndex B r : ℝ) + 1 := by
  unfold binIndex
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hnonneg : 0 ≤ 2 * (B : ℝ) * r := by positivity
  have hle : (⌊2 * (B : ℝ) * r⌋₊ : ℝ) ≤ 2 * (B : ℝ) * r := Nat.floor_le hnonneg
  have hlt1 : 2 * (B : ℝ) * r < (⌊2 * (B : ℝ) * r⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one (2 * (B : ℝ) * r)
  have hltB_real : (⌊2 * (B : ℝ) * r⌋₊ : ℝ) < (B : ℝ) := by nlinarith
  have hltB : ⌊2 * (B : ℝ) * r⌋₊ < B := by exact_mod_cast hltB_real
  exact ⟨hltB, hle, hlt1⟩

/-- Decidable rational-bin overlap condition for a step with parity `ε ∈ {0, 1}`. -/
def validBinStep (B ε b b' : ℕ) : Bool :=
  decide (b < B ∧ b' < B ∧
    3 * b < 2 * b' + 2 + 2 * B * ε ∧
    2 * b' + 2 * B * ε < 3 * (b + 1))

theorem validBinStep_of_validCompanion {B : ℕ} (hB : 1 ≤ B)
    (m : ℕ) (ξ : ℝ) (n : ℕ)
    (hn : ValidCompanionAt m ξ n) (hn1 : ValidCompanionAt m ξ (n + 1)) :
    validBinStep B (orbit m n % 2)
      (binIndex B (fracPart m ξ n))
      (binIndex B (fracPart m ξ (n + 1))) = true := by
  unfold validBinStep
  rw [decide_eq_true_iff]
  have hr0 := (validCompanionAt_iff_fracPart m ξ n).mp hn
  have hr1 := (validCompanionAt_iff_fracPart m ξ (n + 1)).mp hn1
  have hb0 := binIndex_bounds hB hr0.1 hr0.2
  have hb1 := binIndex_bounds hB hr1.1 hr1.2
  have hsucc := fracPart_succ m ξ n
  set b := binIndex B (fracPart m ξ n)
  set b' := binIndex B (fracPart m ξ (n + 1))
  set ε := orbit m n % 2
  have hrel :
      2 * (2 * (B : ℝ) * fracPart m ξ (n + 1)) + 2 * (B : ℝ) * (ε : ℝ) =
        3 * (2 * (B : ℝ) * fracPart m ξ n) := by
    rw [hsucc]
    ring
  have hineq1_real :
      3 * (b : ℝ) < 2 * (b' : ℝ) + 2 + 2 * (B : ℝ) * (ε : ℝ) := by
    linarith [hb0.2.1, hb1.2.2, hrel]
  have hineq2_real :
      2 * (b' : ℝ) + 2 * (B : ℝ) * (ε : ℝ) < 3 * ((b : ℝ) + 1) := by
    linarith [hb0.2.2, hb1.2.1, hrel]
  have hineq1 : 3 * b < 2 * b' + 2 + 2 * B * ε := by
    exact_mod_cast hineq1_real
  have hineq2 : 2 * b' + 2 * B * ε < 3 * (b + 1) := by
    exact_mod_cast hineq2_real
  exact ⟨hb0.1, hb1.1, hineq1, hineq2⟩

/-! ## 3. The Coupled Product Graph `G_{K, B}` and Dead-End Pruning Soundness -/

/-- Directed edge relation of the finite coupled product graph `G_{K, B}`. -/
def coupledEdge (K B res b res' b' : ℕ) : Bool :=
  decide (res < 2 ^ K ∧ res' < 2 ^ K ∧
    (res' = step res % 2 ^ K ∨ res' = (step res + 2 ^ (K - 1)) % 2 ^ K)) &&
  validBinStep B (res % 2) b b'

theorem coupledEdge_of_validCompanion_step {K B : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ B)
    (m : ℕ) (ξ : ℝ) (n : ℕ)
    (hn : ValidCompanionAt m ξ n) (hn1 : ValidCompanionAt m ξ (n + 1)) :
    coupledEdge K B
      (orbit m n % 2 ^ K) (binIndex B (fracPart m ξ n))
      (orbit m (n + 1) % 2 ^ K) (binIndex B (fracPart m ξ (n + 1))) = true := by
  unfold coupledEdge
  rw [Bool.and_eq_true, decide_eq_true_iff]
  have hpos : 0 < 2 ^ K := Nat.pow_pos (by decide)
  have hres_lt : orbit m n % 2 ^ K < 2 ^ K := Nat.mod_lt _ hpos
  have hres'_lt : orbit m (n + 1) % 2 ^ K < 2 ^ K := Nat.mod_lt _ hpos
  have hdich := step_mod_two_pow_dichotomy hK (orbit m n)
  have hmod2 := mod_two_of_mod_two_pow hK (orbit m n)
  refine ⟨⟨hres_lt, hres'_lt, by simpa [orbit] using hdich⟩, ?_⟩
  rw [hmod2]
  exact validBinStep_of_validCompanion hB m ξ n hn hn1

/-- Recursive `t`-step survival of a state `(res, b)` in `G_{K, B}`. -/
def stateSurvives (K B : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, res, b => decide (res < 2 ^ K ∧ b < B)
  | t + 1, res, b =>
      (List.range (2 ^ K)).any fun res' =>
        (List.range B).any fun b' =>
          coupledEdge K B res b res' b' && stateSurvives K B t res' b'

/-- Whether any fractional bin over residue `res` survives `t` steps in `G_{K, B}`. -/
def residueSurvives (K B t res : ℕ) : Bool :=
  (List.range B).any fun b => stateSurvives K B t res b

/-- Every real trajectory valid on `[n, n + t]` projects to a surviving state
at depth `t` in the finite graph `G_{K, B}`. -/
theorem stateSurvives_of_validCompanion_window {K B : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ B)
    (m : ℕ) (ξ : ℝ) (n t : ℕ)
    (hw : ∀ k ≤ t, ValidCompanionAt m ξ (n + k)) :
    stateSurvives K B t
      (orbit m n % 2 ^ K) (binIndex B (fracPart m ξ n)) = true := by
  induction t generalizing n with
  | zero =>
      unfold stateSurvives
      rw [decide_eq_true_iff]
      have h0 := (validCompanionAt_iff_fracPart m ξ n).mp (hw 0 (Nat.le_refl 0))
      exact ⟨Nat.mod_lt _ (Nat.pow_pos (by decide)), (binIndex_bounds hB h0.1 h0.2).1⟩
  | succ t ih =>
      unfold stateSurvives
      rw [List.any_eq_true]
      refine ⟨orbit m (n + 1) % 2 ^ K, List.mem_range.mpr (Nat.mod_lt _ (Nat.pow_pos (by decide))), ?_⟩
      rw [List.any_eq_true]
      have h1_valid : ValidCompanionAt m ξ (n + 1) := hw 1 (by omega)
      have h1_frac := (validCompanionAt_iff_fracPart m ξ (n + 1)).mp h1_valid
      refine ⟨binIndex B (fracPart m ξ (n + 1)),
        List.mem_range.mpr (binIndex_bounds hB h1_frac.1 h1_frac.2).1, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨coupledEdge_of_validCompanion_step hK hB m ξ n (hw 0 (by omega)) h1_valid, ?_⟩
      exact ih (n + 1) (fun k hk => by
        have hadd : n + 1 + k = n + (k + 1) := by omega
        rw [hadd]
        exact hw (k + 1) (by omega))

/-- If `m` has a valid real Mahler companion up to step `T`, then its residue
`m % 2^K` survives `T` steps in `G_{K, B}`. -/
theorem residueSurvives_of_validCompanionUpTo {K B : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ B)
    {m T : ℕ} {ξ : ℝ} (h : ValidCompanionUpTo m ξ T) :
    residueSurvives K B T (m % 2 ^ K) = true := by
  unfold residueSurvives
  rw [List.any_eq_true]
  have h0_frac := (validCompanionAt_iff_fracPart m ξ 0).mp (h 0 (Nat.zero_le T))
  refine ⟨binIndex B (fracPart m ξ 0),
    List.mem_range.mpr (binIndex_bounds hB h0_frac.1 h0_frac.2).1, ?_⟩
  have hst := stateSurvives_of_validCompanion_window hK hB m ξ 0 T (fun k hk => by
    simpa using h k hk)
  simpa [orbit] using hst

/-- **Universal Pruning Soundness Theorem**:
If `residueSurvives K B T (m % 2^K) = false`, then no real companion `ξ`
survives `T` steps from starting integer `m`. -/
theorem no_validCompanionUpTo_of_residueSurvives_false {K B m T : ℕ}
    (hK : 1 ≤ K) (hB : 1 ≤ B)
    (hpruned : residueSurvives K B T (m % 2 ^ K) = false) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo m ξ T := by
  rintro ⟨ξ, hξ⟩
  have htrue := residueSurvives_of_validCompanionUpTo hK hB hξ
  rw [hpruned] at htrue
  cases htrue

/-! ## 4. Certified Finite-Graph Exclusion on `G_{3, 6}` -/

/-- On the 48-state product graph `G_{3, 6}` (`K = 3, B = 6`), 3 rounds of
dead-end pruning eliminate residue classes `2, 3, 7 (mod 8)`. -/
theorem g3_6_pruned_residues :
    residueSurvives 3 6 3 2 = false ∧
    residueSurvives 3 6 3 3 = false ∧
    residueSurvives 3 6 3 7 = false := by
  decide

/-- Consequently, no integer `m` with `m % 8 ∈ {2, 3, 7}` has a valid real
Mahler companion through step `3`. -/
theorem mod_eight_2_3_7_excluded (m : ℕ)
    (hm : m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 7) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo m ξ 3 := by
  have hK : 1 ≤ 3 := by decide
  have hB : 1 ≤ 6 := by decide
  have hpow : (2 ^ 3 : ℕ) = 8 := by decide
  rcases hm with h2 | h3 | h7
  · exact no_validCompanionUpTo_of_residueSurvives_false hK hB
      (by rw [hpow, h2]; exact g3_6_pruned_residues.1)
  · exact no_validCompanionUpTo_of_residueSurvives_false hK hB
      (by rw [hpow, h3]; exact g3_6_pruned_residues.2.1)
  · exact no_validCompanionUpTo_of_residueSurvives_false hK hB
      (by rw [hpow, h7]; exact g3_6_pruned_residues.2.2)

end Mahler.ProductGraph
