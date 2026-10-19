import ExactSeedResidueTreeAndStabilization
import InfiniteSeries

/-!
# Nonperiodic Thue–Morse Encoding, Closed Mahler Functional Equations & 2-Adic Seed Bridge

This module implements **Stage 3** of `RESEARCH_OUTLINE_NEXT_STAGE.md`:

1. **The Thue–Morse Binary Sequence & Pair-Complementarity
   (`tmBool`, `tmBit`, `tmBool_two_mul`, `tmBool_two_mul_add_one`,
   `tmBit_two_mul`, `tmBit_two_mul_add_one`, `tmBit_pair_sum_eq_one`)**:
   Defines the canonical Thue–Morse sequence `tmBool : ℕ → Bool` (`tmBit : ℕ → ℕ`)
   and proves its exact 2-automatic recurrence:
   - `tmBit 0 = 0`, `tmBit (2 * k) = tmBit k`, `tmBit (2 * k + 1) = 1 - tmBit k`,
   - `tmBit (2 * k) + tmBit (2 * k + 1) = 1` for every `k : ℕ`.

2. **The 3-Step Encoded Thue–Morse Mahler Stream & Real Admissibility
   (`tmEncodedStream`, `tmEncodedParity`,
   `tmEncodedStream_fractionalTail_admissible`,
   `tmEncodedParity_six_step_pair_balance`)**:
   Inserts two zeros after every Thue–Morse symbol (`ε_{3n} = t_n`, `ε_{3n+1} = ε_{3n+2} = 0`),
   proves that every real fractional tail lies strictly in `[0, 9/19] ⊂ [0, 1/2)`,
   and proves that every aligned 6-step window `6 * k .. 6 * k + 5` contains
   **exactly one odd step**.

3. **Closed Finite & Infinite Mahler Functional Equations (`tmPartialSum`,
   `tmPartialSum_two_mul_eq`, `tmPartialSum_mahler_functional_identity`,
   `tmSeries`, `tmSeries_summable`, `tmSeries_mahler_functional_equation`,
   `tmSeries_eight_twenty_sevenths_functional_equation`)**:
   - Proves for every `z : ℝ` and `M : ℕ`:
     `tmPartialSum z (2 * M) = (1 - z) * tmPartialSum (z^2) M + z * ∑ k ∈ Finset.range M, (z^2)^k`,
     and `(1 - z^2) * tmPartialSum z (2 * M) = (1 - z) * (1 - z^2) * tmPartialSum (z^2) M + z * (1 - (z^2)^M)`.
   - Proves that `tmSeries z = ∑' n : ℕ, (tmBit n : ℝ) * z^n` converges for `0 ≤ z < 1`
     and satisfies the **exact closed Mahler functional equation**:
     `tmSeries z = (1 - z) * tmSeries (z^2) + z / (1 - z^2)`
     (and at `z = 8 / 27`, `tmSeries (8 / 27) = (19 / 27) * tmSeries (64 / 729) + 216 / 665`).

4. **Exact 2-Adic / Integer Carry Mahler Functional Recurrence & Seed Bridge
   (`tmIntCarry`, `wordCarry_tmEncodedParity_three_mul`,
   `tmIntCarry_two_mul_functional_equation`,
   `tm_six_mul_seed_mahler_bridge`)**:
   Proves that `wordCarry tmEncodedParity (3 * N) = 9 * tmIntCarry 8 27 N` and that
   `tmIntCarry p q (2 * M)` satisfies the exact two-scale Mahler functional identity
   linking scale `(p, q) = (8, 27)` to scale `(p^2, q^2) = (64, 729)`, yielding the
   exact 2-adic seed divisibility bridge at horizon `6 * M`.

5. **Elementary All-Scale Repetition & Unconditional Exclusion of Integer Realization
   (`tmBit_base_four_repeat`, `tmBit_scaled_window_repeat`,
   `tmEncodedParity_scaled_window_repeat`, `scalable_early_repetition_cutoff`,
   `tmEncodedParity_finite_seed_cutoff`,
   `tmEncodedParity_mismatch_lt_sixty_mul_bit_length`,
   `no_nonneg_seed_realizes_tmEncodedParity`,
   `tmEncodedParity_seedResidue_never_stabilizes`,
   `tmEncodedStream_aperiodic_fractional_survivor_not_integer_realizable`,
   `tmEncodedParity_shifted_finite_seed_cutoff`)**:
   Proves by induction on `k` that the base Thue–Morse repetition `t[0, 4) = 0110 = t[6, 10)`
   inflates at every scale `R = 2^k` to `tmBit i = tmBit (6 * 2^k + i)` for `i < 4 * 2^k`,
   and transfers through the 3-step zero encoding to `tmEncodedParity i = tmEncodedParity (18 * 2^k + i)`
   for `i < 12 * 2^k`. Combining this with `3^18 < 2^29` and `early_window_no_repeat`
   proves without any transcendence hypothesis that:
   - No positive seed `a_0 < 2^W` (`W ≤ 2^k`) can match `tmEncodedParity` up to step `30 * 2^k`
     (and for `1 ≤ W`, mismatch occurs strictly before step `60 * W`),
   - No nonnegative integer seed `a_0 : ℕ` realizes `tmEncodedParity`,
   - The least seed residues `seedResidue tmEncodedParity N` never stabilize, and
   - Fixed shifts `tmEncodedParity (h + n)` and orbit preperiods are similarly excluded.
-/

namespace Mahler.ThueMorseMahler

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.CeilingSynthesis
open Mahler.MinSlackSystem
open Mahler.SharpenedSqueezes
open Mahler.Adversarial
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree

/-! ## 1. The Thue–Morse Sequence & 2-Automatic Pair-Complementarity -/

/-- The canonical Thue–Morse sequence `tmBool : ℕ → Bool`. -/
def tmBool : ℕ → Bool
  | 0 => false
  | n + 1 =>
      if (n + 1) % 2 = 0 then tmBool ((n + 1) / 2)
      else !tmBool ((n + 1) / 2)
decreasing_by all_goals omega

/-- The `{0, 1}`-valued Thue–Morse sequence `tmBit n = if tmBool n then 1 else 0`. -/
def tmBit (n : ℕ) : ℕ :=
  if tmBool n then 1 else 0

@[simp] theorem tmBool_zero : tmBool 0 = false := by
  unfold tmBool
  rfl

@[simp] theorem tmBool_two_mul (k : ℕ) : tmBool (2 * k) = tmBool k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hsucc : 2 * k = (2 * k - 1) + 1 := by omega
    conv_lhs => rw [hsucc, tmBool]
    have hmod : ((2 * k - 1) + 1) % 2 = 0 := by omega
    have hdiv : ((2 * k - 1) + 1) / 2 = k := by omega
    simp [hmod, hdiv]

@[simp] theorem tmBool_two_mul_add_one (k : ℕ) : tmBool (2 * k + 1) = !tmBool k := by
  conv_lhs => rw [tmBool]
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [hmod, hdiv]

@[simp] theorem tmBit_zero : tmBit 0 = 0 := by
  simp [tmBit]

theorem tmBit_le_one (n : ℕ) : tmBit n ≤ 1 := by
  unfold tmBit
  split_ifs <;> omega

@[simp] theorem tmBit_two_mul (k : ℕ) : tmBit (2 * k) = tmBit k := by
  simp [tmBit]

@[simp] theorem tmBit_two_mul_add_one (k : ℕ) : tmBit (2 * k + 1) = 1 - tmBit k := by
  unfold tmBit
  rw [tmBool_two_mul_add_one]
  cases tmBool k <;> rfl

/-- **Exact Pair-Complementarity of Thue–Morse (`tmBit_pair_sum_eq_one`)**:
For every `k : ℕ`, `tmBit (2 * k) + tmBit (2 * k + 1) = 1`. -/
theorem tmBit_pair_sum_eq_one (k : ℕ) :
    tmBit (2 * k) + tmBit (2 * k + 1) = 1 := by
  rw [tmBit_two_mul, tmBit_two_mul_add_one]
  have hle := tmBit_le_one k
  omega

/-- Initial prefix of `tmBit`: `0, 1, 1, 0, 1, 0, 0, 1`. -/
theorem tmBit_initial_eight :
    tmBit 0 = 0 ∧ tmBit 1 = 1 ∧ tmBit 2 = 1 ∧ tmBit 3 = 0 ∧
      tmBit 4 = 1 ∧ tmBit 5 = 0 ∧ tmBit 6 = 0 ∧ tmBit 7 = 1 := by
  have h1 : tmBit 1 = 1 := by simpa using tmBit_two_mul_add_one 0
  have h2 : tmBit 2 = 1 := by simpa [h1] using tmBit_two_mul 1
  have h3 : tmBit 3 = 0 := by simpa [h1] using tmBit_two_mul_add_one 1
  have h4 : tmBit 4 = 1 := by simpa [h2] using tmBit_two_mul 2
  have h5 : tmBit 5 = 0 := by simpa [h2] using tmBit_two_mul_add_one 2
  have h6 : tmBit 6 = 0 := by simpa [h3] using tmBit_two_mul 3
  have h7 : tmBit 7 = 1 := by simpa [h3] using tmBit_two_mul_add_one 3
  exact ⟨tmBit_zero, h1, h2, h3, h4, h5, h6, h7⟩

/-! ## 2. The 3-Step Encoded Thue–Morse Stream & Real Fractional Admissibility -/

/-- The 3-step encoded Thue–Morse Boolean stream (`ε_{3n} = tmBool n`, `ε_{3n+1} = ε_{3n+2} = false`). -/
def tmEncodedStream : ℕ → Bool :=
  encodeStream tmBool

/-- The `{0, 1}`-valued 3-step encoded Thue–Morse parity stream. -/
def tmEncodedParity (n : ℕ) : ℕ :=
  if tmEncodedStream n then 1 else 0

@[simp] theorem tmEncodedParity_three_mul (k : ℕ) :
    tmEncodedParity (3 * k) = tmBit k := by
  simp [tmEncodedParity, tmEncodedStream, tmBit]

@[simp] theorem tmEncodedParity_three_mul_add_one (k : ℕ) :
    tmEncodedParity (3 * k + 1) = 0 := by
  simp [tmEncodedParity, tmEncodedStream]

@[simp] theorem tmEncodedParity_three_mul_add_two (k : ℕ) :
    tmEncodedParity (3 * k + 2) = 0 := by
  simp [tmEncodedParity, tmEncodedStream]

/-- **Real Fractional Admissibility of `tmEncodedStream` (`tmEncodedStream_fractionalTail_admissible`)**:
At every step `n : ℕ`, the real fractional tail of `tmEncodedStream` satisfies
`0 ≤ fractionalTail tmEncodedStream n ≤ 9 / 19 < 1 / 2` and obeys the exact
stepwise Mahler fractional recurrence. -/
theorem tmEncodedStream_fractionalTail_admissible (n : ℕ) :
    0 ≤ fractionalTail tmEncodedStream n ∧
      fractionalTail tmEncodedStream n ≤ (9 / 19 : ℝ) ∧
      fractionalTail tmEncodedStream n < (1 / 2 : ℝ) ∧
      fractionalTail tmEncodedStream (n + 1) =
        (3 / 2 : ℝ) * fractionalTail tmEncodedStream n -
          (if tmEncodedStream n then (1 / 2 : ℝ) else 0) := by
  refine ⟨fractionalTail_nonneg tmEncodedStream n,
    encoded_fractionalTail_bound tmBool n,
    (encoded_fractionalTail_admissible tmBool n).2,
    fractionalTail_recurrence tmEncodedStream n⟩

/-- **Exact 6-Step Pair Balance of `tmEncodedParity` (`tmEncodedParity_six_step_pair_balance`)**:
Every aligned 6-step window `6 * k, ..., 6 * k + 5` of `tmEncodedParity` contains
**exactly one odd step** (`∑ i ∈ Finset.range 6, tmEncodedParity (6 * k + i) = 1`). -/
theorem tmEncodedParity_six_step_pair_balance (k : ℕ) :
    (∑ i ∈ Finset.range 6, tmEncodedParity (6 * k + i)) = 1 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, Finset.sum_range_succ]
  rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ]
  rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_range_succ]
  rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ]
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ]
  rw [Finset.sum_range_one]
  have h0 : 6 * k + 0 = 3 * (2 * k) := by omega
  have h1 : 6 * k + 1 = 3 * (2 * k) + 1 := by omega
  have h2 : 6 * k + 2 = 3 * (2 * k) + 2 := by omega
  have h3 : 6 * k + 3 = 3 * (2 * k + 1) := by omega
  have h4 : 6 * k + 4 = 3 * (2 * k + 1) + 1 := by omega
  have h5 : 6 * k + 5 = 3 * (2 * k + 1) + 2 := by omega
  rw [h0, h1, h2, h3, h4, h5]
  simp only [tmEncodedParity_three_mul, tmEncodedParity_three_mul_add_one,
    tmEncodedParity_three_mul_add_two, Nat.add_zero]
  exact tmBit_pair_sum_eq_one k

/-! ## 3. Closed Finite & Infinite Mahler Functional Equations -/

/-- The finite Thue–Morse generating partial sum `∑_{n < m} tmBit n * z^n`. -/
def tmPartialSum (z : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, (tmBit n : ℝ) * z ^ n

/-- **Exact Finite Mahler Functional Equation (`tmPartialSum_two_mul_eq`)**:
For every `z : ℝ` and `M : ℕ`,
`tmPartialSum z (2 * M) = (1 - z) * tmPartialSum (z^2) M + z * ∑ k ∈ Finset.range M, (z^2)^k`. -/
theorem tmPartialSum_two_mul_eq (z : ℝ) (M : ℕ) :
    tmPartialSum z (2 * M) =
      (1 - z) * tmPartialSum (z ^ 2) M +
        z * ∑ k ∈ Finset.range M, (z ^ 2) ^ k := by
  induction M with
  | zero => simp [tmPartialSum]
  | succ M ih =>
      have h2M : 2 * (M + 1) = (2 * M + 1) + 1 := by omega
      unfold tmPartialSum at ih ⊢
      rw [h2M, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have hbit0 : (tmBit (2 * M) : ℝ) = (tmBit M : ℝ) := by
        exact_mod_cast tmBit_two_mul M
      have hbit1 : (tmBit (2 * M + 1) : ℝ) = 1 - (tmBit M : ℝ) := by
        have h := tmBit_two_mul_add_one M
        have hle := tmBit_le_one M
        zify [hle] at h
        exact_mod_cast h
      have hpow0 : z ^ (2 * M) = (z ^ 2) ^ M := by rw [pow_mul]
      have hpow1 : z ^ (2 * M + 1) = z * (z ^ 2) ^ M := by
        rw [pow_succ, pow_mul]
        ring
      rw [hbit0, hbit1, hpow0, hpow1]
      ring

private theorem one_sub_mul_geom_sum (x : ℝ) (M : ℕ) :
    (1 - x) * (∑ k ∈ Finset.range M, x ^ k) = 1 - x ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- **Polynomial Mahler Functional Identity (`tmPartialSum_mahler_functional_identity`)**:
For every `z : ℝ` and `M : ℕ`,
`(1 - z^2) * tmPartialSum z (2 * M) =
  (1 - z) * (1 - z^2) * tmPartialSum (z^2) M + z * (1 - (z^2)^M)`. -/
theorem tmPartialSum_mahler_functional_identity (z : ℝ) (M : ℕ) :
    (1 - z ^ 2) * tmPartialSum z (2 * M) =
      (1 - z) * (1 - z ^ 2) * tmPartialSum (z ^ 2) M +
        z * (1 - (z ^ 2) ^ M) := by
  have h1 := congrArg (fun y : ℝ => (1 - z ^ 2) * y) (tmPartialSum_two_mul_eq z M)
  dsimp at h1
  have hgeom := one_sub_mul_geom_sum (z ^ 2) M
  calc
    (1 - z ^ 2) * tmPartialSum z (2 * M) =
        (1 - z) * (1 - z ^ 2) * tmPartialSum (z ^ 2) M +
          z * ((1 - z ^ 2) * ∑ k ∈ Finset.range M, (z ^ 2) ^ k) := by
      linarith [h1]
    _ = (1 - z) * (1 - z ^ 2) * tmPartialSum (z ^ 2) M +
          z * (1 - (z ^ 2) ^ M) := by
      rw [hgeom]

/-- The infinite Thue–Morse Mahler generating function `F(z) = ∑'_{n=0}^∞ tmBit n * z^n`. -/
noncomputable def tmSeries (z : ℝ) : ℝ :=
  ∑' n : ℕ, (tmBit n : ℝ) * z ^ n

/-- For `0 ≤ z < 1`, the Thue–Morse power series `fun n => (tmBit n : ℝ) * z^n` is summable. -/
theorem tmSeries_summable {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun n : ℕ => (tmBit n : ℝ) * z ^ n) := by
  apply Summable.of_nonneg_of_le
  · intro n
    have hbit : (0 : ℝ) ≤ (tmBit n : ℝ) := Nat.cast_nonneg (tmBit n)
    positivity
  · intro n
    have hbit : (tmBit n : ℝ) ≤ 1 := by exact_mod_cast tmBit_le_one n
    have hz_pow : 0 ≤ z ^ n := pow_nonneg hz0 n
    nlinarith
  · exact summable_geometric_of_lt_one hz0 hz1

/-- **Closed Infinite Mahler Functional Equation (`tmSeries_mahler_functional_equation`)**:
For every real `z ∈ [0, 1)`, the Thue–Morse generating function `tmSeries z`
satisfies the closed Mahler functional equation:
`tmSeries z = (1 - z) * tmSeries (z^2) + z / (1 - z^2)`. -/
theorem tmSeries_mahler_functional_equation {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    tmSeries z = (1 - z) * tmSeries (z ^ 2) + z / (1 - z ^ 2) := by
  have hz2_0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hz2_1 : z ^ 2 < 1 := by nlinarith
  have hs1 : HasSum (fun n : ℕ => (tmBit n : ℝ) * z ^ n) (tmSeries z) :=
    (tmSeries_summable hz0 hz1).hasSum
  have hs2 : HasSum (fun n : ℕ => (tmBit n : ℝ) * (z ^ 2) ^ n) (tmSeries (z ^ 2)) :=
    (tmSeries_summable hz2_0 hz2_1).hasSum
  have hs_geom : HasSum (fun k : ℕ => (z ^ 2) ^ k) ((1 - z ^ 2)⁻¹) :=
    hasSum_geometric_of_lt_one hz2_0 hz2_1
  have ht1 : Filter.Tendsto (tmPartialSum z) Filter.atTop (nhds (tmSeries z)) :=
    hs1.tendsto_sum_nat
  have ht_even :
      Filter.Tendsto (fun M : ℕ => tmPartialSum z (2 * M))
        Filter.atTop (nhds (tmSeries z)) := by
    apply ht1.comp
    exact Filter.tendsto_atTop_mono (fun M => by omega : ∀ M : ℕ, M ≤ 2 * M) Filter.tendsto_id
  have ht2 :
      Filter.Tendsto (tmPartialSum (z ^ 2)) Filter.atTop (nhds (tmSeries (z ^ 2))) :=
    hs2.tendsto_sum_nat
  have ht_geom :
      Filter.Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, (z ^ 2) ^ k)
        Filter.atTop (nhds ((1 - z ^ 2)⁻¹)) :=
    hs_geom.tendsto_sum_nat
  have ht_rhs :
      Filter.Tendsto
        (fun M : ℕ =>
          (1 - z) * tmPartialSum (z ^ 2) M + z * ∑ k ∈ Finset.range M, (z ^ 2) ^ k)
        Filter.atTop
        (nhds ((1 - z) * tmSeries (z ^ 2) + z * (1 - z ^ 2)⁻¹)) :=
    (ht2.const_mul (1 - z)).add (ht_geom.const_mul z)
  have hfun :
      (fun M : ℕ => tmPartialSum z (2 * M)) =
        (fun M : ℕ =>
          (1 - z) * tmPartialSum (z ^ 2) M + z * ∑ k ∈ Finset.range M, (z ^ 2) ^ k) := by
    funext M
    exact tmPartialSum_two_mul_eq z M
  rw [hfun] at ht_even
  have heq := tendsto_nhds_unique ht_even ht_rhs
  rw [heq, div_eq_mul_inv]

/-- **Evaluation of the Mahler Functional Equation at $z = 8 / 27$
(`tmSeries_eight_twenty_sevenths_functional_equation`)**:
At the Mahler 3-step specialization point `z = 8 / 27`,
`tmSeries (8 / 27) = (19 / 27) * tmSeries (64 / 729) + 216 / 665`. -/
theorem tmSeries_eight_twenty_sevenths_functional_equation :
    tmSeries (8 / 27 : ℝ) =
      (19 / 27 : ℝ) * tmSeries (64 / 729 : ℝ) + (216 / 665 : ℝ) := by
  have h := tmSeries_mahler_functional_equation
    (z := (8 / 27 : ℝ)) (by norm_num) (by norm_num)
  have hsq : (8 / 27 : ℝ) ^ 2 = (64 / 729 : ℝ) := by norm_num
  rw [hsq] at h
  linarith

/-! ## 4. Exact Integer / 2-Adic Carry Mahler Recurrence & Seed Bridge -/

/-- Two-parameter integer Mahler carry polynomial
`tmIntCarry p q M = ∑_{n < M} tmBit n * p^n * q^(M - 1 - n)`. -/
def tmIntCarry (p q : ℕ) : ℕ → ℕ
  | 0 => 0
  | M + 1 => q * tmIntCarry p q M + p ^ M * tmBit M

/-- Geometric two-parameter carry sum `geomIntCarry p q M = ∑_{k < M} p^k * q^(M - 1 - k)`. -/
def geomIntCarry (p q : ℕ) : ℕ → ℕ
  | 0 => 0
  | M + 1 => q * geomIntCarry p q M + p ^ M

/-- Closed form of `geomIntCarry`: when `p ≤ q`,
`(q - p) * geomIntCarry p q M = q^M - p^M`. -/
theorem geomIntCarry_closed_form {p q : ℕ} (hpq : p ≤ q) (M : ℕ) :
    (q - p) * geomIntCarry p q M = q ^ M - p ^ M := by
  induction M with
  | zero => simp [geomIntCarry]
  | succ M ih =>
      simp only [geomIntCarry]
      have hle_M : p ^ M ≤ q ^ M := Nat.pow_le_pow_left hpq M
      have hle_M1 : p ^ (M + 1) ≤ q ^ (M + 1) := Nat.pow_le_pow_left hpq (M + 1)
      zify [hpq, hle_M, hle_M1] at ih ⊢
      rw [pow_succ (q : ℤ) M, pow_succ (p : ℤ) M]
      linear_combination (q : ℤ) * ih

/-- **Exact Bridge Between `wordCarry tmEncodedParity (3 * N)` and `tmIntCarry 8 27 N`
(`wordCarry_tmEncodedParity_three_mul`)**:
For every `N : ℕ`, `wordCarry tmEncodedParity (3 * N) = 9 * tmIntCarry 8 27 N`. -/
theorem wordCarry_tmEncodedParity_three_mul (N : ℕ) :
    wordCarry tmEncodedParity (3 * N) = 9 * tmIntCarry 8 27 N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hlt : tmBit N < 2 := by
        have hle := tmBit_le_one N
        omega
      have hc1 :
          wordCarry tmEncodedParity (3 * N + 1) =
            3 * wordCarry tmEncodedParity (3 * N) + 2 ^ (3 * N) * tmBit N := by
        simp [wordCarry, Nat.mod_eq_of_lt hlt]
      have hc2 :
          wordCarry tmEncodedParity (3 * N + 2) =
            3 * wordCarry tmEncodedParity (3 * N + 1) := by
        simp [wordCarry]
      have hc3 :
          wordCarry tmEncodedParity (3 * (N + 1)) =
            3 * wordCarry tmEncodedParity (3 * N + 2) := by
        have h3 : 3 * (N + 1) = (3 * N + 2) + 1 := by omega
        rw [h3]
        simp [wordCarry]
      have hpow2 : 2 ^ (3 * N) = 8 ^ N := by rw [Nat.pow_mul]
      simp only [tmIntCarry]
      rw [hc3, hc2, hc1, ih, hpow2]
      ring

/-- **Exact Integer Mahler Functional Equation for `tmIntCarry`
(`tmIntCarry_two_mul_functional_equation`)**:
For any parameters `p, q : ℕ` and any `M : ℕ`,
`tmIntCarry p q (2 * M) + p * tmIntCarry (p^2) (q^2) M =
  q * tmIntCarry (p^2) (q^2) M + p * geomIntCarry (p^2) (q^2) M`. -/
theorem tmIntCarry_two_mul_functional_equation (p q M : ℕ) :
    tmIntCarry p q (2 * M) + p * tmIntCarry (p ^ 2) (q ^ 2) M =
      q * tmIntCarry (p ^ 2) (q ^ 2) M + p * geomIntCarry (p ^ 2) (q ^ 2) M := by
  induction M with
  | zero => simp [tmIntCarry, geomIntCarry]
  | succ M ih =>
      have h2M : 2 * (M + 1) = (2 * M + 1) + 1 := by omega
      rw [h2M]
      simp only [tmIntCarry, geomIntCarry, tmBit_two_mul, tmBit_two_mul_add_one]
      have hp2M : p ^ (2 * M) = (p ^ 2) ^ M := by rw [Nat.pow_mul]
      have hp2M1 : p ^ (2 * M + 1) = p * (p ^ 2) ^ M := by
        rw [Nat.pow_succ, Nat.pow_mul]
        ring
      rw [hp2M, hp2M1]
      have hle := tmBit_le_one M
      zify [hle] at ih ⊢
      linear_combination (q : ℤ) ^ 2 * ih

/-- **Exact 2-Adic Seed Mahler Bridge at Horizon $6 M$ (`tm_six_mul_seed_mahler_bridge`)**:
If an integer seed `a_0 : ℕ` matches the encoded Thue–Morse parity stream up to
step `6 * M`, then:
`64^M * orbit a_0 (6 * M) + 72 * tmIntCarry 64 729 M =
  729^M * a_0 + 243 * tmIntCarry 64 729 M + 72 * geomIntCarry 64 729 M`,
and multiplying by `665 = 729 - 64` gives:
`665 * 64^M * orbit a_0 (6 * M) + 64 * (72 * 665 * tmIntCarry 64 729 M + 72 * 64^M) =
  729^M * (665 * a_0 + 72) + 171 * 665 * tmIntCarry 64 729 M`,
so **`64^M ∣ (729^M * (665 * a_0 + 72) + 113715 * tmIntCarry 64 729 M)`**. -/
theorem tm_six_mul_seed_mahler_bridge {a_0 M : ℕ}
    (hmatch : ∀ n < 6 * M, orbit a_0 n % 2 = tmEncodedParity n % 2) :
    64 ^ M * orbit a_0 (6 * M) + 72 * tmIntCarry 64 729 M =
        729 ^ M * a_0 + 243 * tmIntCarry 64 729 M + 72 * geomIntCarry 64 729 M ∧
      64 ^ M ∣
        (729 ^ M * (665 * a_0 + 72) + 113715 * tmIntCarry 64 729 M) := by
  have hid := (wordCarry_eq_carry_of_parity_match hmatch).2
  have h6M : 6 * M = 3 * (2 * M) := by omega
  have hpow2 : 2 ^ (6 * M) = 64 ^ M := by rw [Nat.pow_mul]
  have hpow3 : 3 ^ (6 * M) = 729 ^ M := by rw [Nat.pow_mul]
  have hcarry3 := wordCarry_tmEncodedParity_three_mul (2 * M)
  have hfunc := tmIntCarry_two_mul_functional_equation 8 27 M
  norm_num at hfunc
  rw [hpow2, hpow3, h6M, hcarry3] at hid
  have heq1 :
      64 ^ M * orbit a_0 (6 * M) + 72 * tmIntCarry 64 729 M =
        729 ^ M * a_0 + 243 * tmIntCarry 64 729 M + 72 * geomIntCarry 64 729 M := by
    rw [← h6M] at hid
    omega
  refine ⟨heq1, ?_⟩
  have hgeom := geomIntCarry_closed_form (p := 64) (q := 729) (by decide) M
  norm_num at hgeom
  have hle_pow : 64 ^ M ≤ 729 ^ M := Nat.pow_le_pow_left (by decide) M
  have hcomb :
      729 ^ M * (665 * a_0 + 72) + 113715 * tmIntCarry 64 729 M =
        64 ^ M * (665 * orbit a_0 (6 * M) + 72) := by
    zify [hle_pow] at heq1 hgeom ⊢
    linear_combination -665 * heq1 - 72 * hgeom
  exact ⟨665 * orbit a_0 (6 * M) + 72, hcomb⟩

/-! ## 5. Elementary All-Scale Repetition & Unconditional Exclusion of Integer Realization -/

/-- Values `tmBit 8 = 1` and `tmBit 9 = 0`, completing the base window `t[6, 10) = 0110`. -/
theorem tmBit_eight_and_nine :
    tmBit 8 = 1 ∧ tmBit 9 = 0 := by
  have h4 := tmBit_initial_eight.2.2.2.2.1
  have h8 : tmBit 8 = 1 := by simpa [h4] using tmBit_two_mul 4
  have h9 : tmBit 9 = 0 := by simpa [h4] using tmBit_two_mul_add_one 4
  exact ⟨h8, h9⟩

/-- **Base Thue–Morse 4-Symbol Repetition (`tmBit_base_four_repeat`)**:
For every `i < 4`, `tmBit i = tmBit (6 + i)` (`t[0, 4) = 0110 = t[6, 10)`). -/
theorem tmBit_base_four_repeat {i : ℕ} (hi : i < 4) :
    tmBit i = tmBit (6 + i) := by
  rcases tmBit_initial_eight with ⟨h0, h1, h2, h3, _, _, h6, h7⟩
  rcases tmBit_eight_and_nine with ⟨h8, h9⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simp [h0, h6]
  · simp [h1, h7]
  · simp [h2, h8]
  · simp [h3, h9]

/-- **All-Scale Thue–Morse Window Inflation (`tmBit_scaled_window_repeat`)**:
For every scale `k : ℕ` (`R = 2^k`) and every `i < 4 * 2^k`,
`tmBit i = tmBit (6 * 2^k + i)`. -/
theorem tmBit_scaled_window_repeat (k : ℕ) :
    ∀ {i : ℕ}, i < 4 * 2 ^ k → tmBit i = tmBit (6 * 2 ^ k + i) := by
  induction k with
  | zero =>
      intro i hi
      simpa using tmBit_base_four_repeat (by simpa using hi)
  | succ k ih =>
      intro i hi
      have hj : i / 2 < 4 * 2 ^ k := by
        rw [Nat.pow_succ] at hi
        omega
      have ihj := ih hj
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hmod0 | hmod1
      · have hi_eq : i = 2 * (i / 2) := by omega
        have hrhs_eq : 6 * 2 ^ (k + 1) + i = 2 * (6 * 2 ^ k + i / 2) := by
          rw [Nat.pow_succ]
          omega
        conv_lhs => rw [hi_eq]
        rw [hrhs_eq, tmBit_two_mul, tmBit_two_mul, ihj]
      · have hi_eq : i = 2 * (i / 2) + 1 := by omega
        have hrhs_eq : 6 * 2 ^ (k + 1) + i = 2 * (6 * 2 ^ k + i / 2) + 1 := by
          rw [Nat.pow_succ]
          omega
        conv_lhs => rw [hi_eq]
        rw [hrhs_eq, tmBit_two_mul_add_one, tmBit_two_mul_add_one, ihj]

/-- Boolean form of all-scale Thue–Morse window inflation (`tmBool_scaled_window_repeat`). -/
theorem tmBool_scaled_window_repeat (k : ℕ) {i : ℕ} (hi : i < 4 * 2 ^ k) :
    tmBool i = tmBool (6 * 2 ^ k + i) := by
  have h := tmBit_scaled_window_repeat k hi
  unfold tmBit at h
  rcases h1 : tmBool i <;> rcases h2 : tmBool (6 * 2 ^ k + i) <;> simp [h1, h2] at h ⊢

/-- Every `tmEncodedParity n` lies in `{0, 1}`, so `tmEncodedParity n % 2 = tmEncodedParity n`. -/
theorem tmEncodedParity_le_one (n : ℕ) : tmEncodedParity n ≤ 1 := by
  unfold tmEncodedParity
  split_ifs <;> omega

@[simp] theorem tmEncodedParity_mod_two (n : ℕ) :
    tmEncodedParity n % 2 = tmEncodedParity n := by
  have h := tmEncodedParity_le_one n
  omega

/-- **All-Scale Encoded Thue–Morse Window Inflation (`tmEncodedParity_scaled_window_repeat`)**:
For every scale `k : ℕ` (`R = 2^k`) and every `i < 12 * 2^k`,
`tmEncodedParity i = tmEncodedParity (18 * 2^k + i)`. -/
theorem tmEncodedParity_scaled_window_repeat (k : ℕ) {i : ℕ} (hi : i < 12 * 2 ^ k) :
    tmEncodedParity i = tmEncodedParity (18 * 2 ^ k + i) := by
  have hq : i / 3 < 4 * 2 ^ k := by omega
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hr0 | hr1 | hr2
  · have hi_eq : i = 3 * (i / 3) := by omega
    have hrhs_eq : 18 * 2 ^ k + i = 3 * (6 * 2 ^ k + i / 3) := by omega
    conv_lhs => rw [hi_eq]
    rw [hrhs_eq, tmEncodedParity_three_mul, tmEncodedParity_three_mul]
    exact tmBit_scaled_window_repeat k hq
  · have hi_eq : i = 3 * (i / 3) + 1 := by omega
    have hrhs_eq : 18 * 2 ^ k + i = 3 * (6 * 2 ^ k + i / 3) + 1 := by omega
    rw [hrhs_eq, hi_eq, tmEncodedParity_three_mul_add_one, tmEncodedParity_three_mul_add_one]
  · have hi_eq : i = 3 * (i / 3) + 2 := by omega
    have hrhs_eq : 18 * 2 ^ k + i = 3 * (6 * 2 ^ k + i / 3) + 2 := by omega
    rw [hrhs_eq, hi_eq, tmEncodedParity_three_mul_add_two, tmEncodedParity_three_mul_add_two]

/-- **General Scalable-Early-Repetition Cutoff Criterion (`scalable_early_repetition_cutoff`)**:
If a parity stream `ε : ℕ → ℕ` has a repeated window of length `L` at origins `i < j ≤ H`
(`∀ t < L, ε (i + t) % 2 = ε (j + t) % 2`), and a positive integer seed `0 < a_0`
satisfies `(a_0 + 1) * 3^H < 2^(L + H)`, then `orbit a_0` cannot match `ε` up to
horizon `H + L`. -/
theorem scalable_early_repetition_cutoff
    {ε : ℕ → ℕ} {a_0 L H i j : ℕ}
    (ha0 : 0 < a_0) (hij : i < j) (hj : j ≤ H)
    (hbound : (a_0 + 1) * 3 ^ H < 2 ^ (L + H))
    (hrep : ∀ t < L, ε (i + t) % 2 = ε (j + t) % 2) :
    ¬ (∀ n < H + L, orbit a_0 n % 2 = ε n % 2) := by
  intro hmatch
  apply early_window_no_repeat ha0 hij hj hbound
  intro t ht
  have hi_lt : i + t < H + L := by omega
  have hj_lt : j + t < H + L := by omega
  rw [hmatch (i + t) hi_lt, hmatch (j + t) hj_lt, hrep t ht]

private theorem pow_strict_mono_left_tm {a b n : ℕ} (hn : 1 ≤ n) (hlt : a < b) :
    a ^ n < b ^ n := by
  have hb_pos : 0 < b := by omega
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · rw [Nat.zero_pow (by omega : 0 < n)]
    exact Nat.pow_pos hb_pos
  · induction n with
    | zero => omega
    | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simpa using hlt
        · have ihn := ih hpos
          rw [Nat.pow_succ, Nat.pow_succ]
          have h1 : a ^ n * a < b ^ n * a := Nat.mul_lt_mul_of_pos_right ihn ha_pos
          have h2 : b ^ n * a ≤ b ^ n * b := Nat.mul_le_mul_left (b ^ n) (by omega)
          exact lt_of_lt_of_le h1 h2

/-- Exact exponential comparison `3^(18 * R) < 2^(29 * R)` for every `R ≥ 1`
(since `3^18 = 387420489 < 536870912 = 2^29`). -/
theorem three_pow_eighteen_mul_lt_two_pow_twenty_nine_mul {R : ℕ} (hR : 1 ≤ R) :
    3 ^ (18 * R) < 2 ^ (29 * R) := by
  rw [Nat.pow_mul 3 18 R, Nat.pow_mul 2 29 R]
  exact pow_strict_mono_left_tm hR (by decide : 3 ^ 18 < 2 ^ 29)

/-- Key growth inequality for Thue–Morse early repetition:
if `a_0 < 2^W`, `W + h ≤ R`, and `1 ≤ R`, then
`(a_0 + 1) * 3^(18 * R) < 2^((12 * R - h) + 18 * R)`. -/
theorem tm_seed_growth_lt_two_pow {a_0 W h R : ℕ}
    (hR : 1 ≤ R) (ha0 : a_0 < 2 ^ W) (hhR : W + h ≤ R) :
    (a_0 + 1) * 3 ^ (18 * R) < 2 ^ ((12 * R - h) + 18 * R) := by
  have ha0_le : a_0 + 1 ≤ 2 ^ W := by omega
  have h3_lt := three_pow_eighteen_mul_lt_two_pow_twenty_nine_mul hR
  have h3_pos : 0 < 3 ^ (18 * R) := Nat.pow_pos (by decide)
  have h1 : (a_0 + 1) * 3 ^ (18 * R) ≤ 2 ^ W * 3 ^ (18 * R) :=
    Nat.mul_le_mul_right _ ha0_le
  have h2 : 2 ^ W * 3 ^ (18 * R) < 2 ^ W * 2 ^ (29 * R) :=
    Nat.mul_lt_mul_of_pos_left h3_lt (Nat.pow_pos (by decide))
  have h3 : 2 ^ W * 2 ^ (29 * R) = 2 ^ (W + 29 * R) := by
    rw [← Nat.pow_add]
  have hexp_le : W + 29 * R ≤ (12 * R - h) + 18 * R := by omega
  have h4 : 2 ^ (W + 29 * R) ≤ 2 ^ ((12 * R - h) + 18 * R) :=
    Nat.pow_le_pow_right (by decide) hexp_le
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le (by rwa [h3] at h2) h4)

/-- **Explicit Finite-Horizon Seed Cutoff for `tmEncodedParity` (`tmEncodedParity_finite_seed_cutoff`)**:
For any positive integer seed `0 < a_0 < 2^W` and scale `k : ℕ` with `W ≤ 2^k`,
`orbit a_0` cannot match `tmEncodedParity` across the finite horizon `0 ≤ n < 30 * 2^k`. -/
theorem tmEncodedParity_finite_seed_cutoff {a_0 W k : ℕ}
    (ha0 : 0 < a_0) (hW : a_0 < 2 ^ W) (hk : W ≤ 2 ^ k) :
    ¬ (∀ n < 30 * 2 ^ k, orbit a_0 n % 2 = tmEncodedParity n) := by
  intro hmatch
  set R := 2 ^ k
  have hR : 1 ≤ R := Nat.pow_pos (by decide)
  have hbound := tm_seed_growth_lt_two_pow (h := 0) hR hW (by omega)
  simp only [Nat.sub_zero] at hbound
  apply scalable_early_repetition_cutoff (ε := tmEncodedParity)
    (L := 12 * R) (H := 18 * R) (i := 0) (j := 18 * R)
    ha0 (by omega) le_rfl hbound
  · intro t ht
    simp only [Nat.zero_add, tmEncodedParity_mod_two]
    exact tmEncodedParity_scaled_window_repeat k ht
  · intro n hn
    have hn30 : n < 30 * 2 ^ k := by omega
    rw [hmatch n hn30, tmEncodedParity_mod_two]

/-- Every `W ≥ 1` lies in `[2^(k-1)+1, 2^k]` for some `k : ℕ`, giving `W ≤ 2^k` and `2^k < 2 * W`. -/
theorem exists_two_pow_sandwich {W : ℕ} (hW : 1 ≤ W) :
    ∃ k : ℕ, W ≤ 2 ^ k ∧ 2 ^ k < 2 * W := by
  induction W with
  | zero => omega
  | succ W ih =>
      rcases Nat.eq_zero_or_pos W with rfl | hW_pos
      · exact ⟨0, by decide, by decide⟩
      · obtain ⟨k, hk_lo, hk_hi⟩ := ih hW_pos
        by_cases hlt : W + 1 ≤ 2 ^ k
        · exact ⟨k, hlt, by omega⟩
        · have heq : 2 ^ k = W := by omega
          refine ⟨k + 1, ?_, ?_⟩
          · rw [Nat.pow_succ, heq]
            omega
          · rw [Nat.pow_succ, heq]
            omega

/-- **Sub-`60 W` Explicit Parity Mismatch Bound (`tmEncodedParity_mismatch_lt_sixty_mul_bit_length`)**:
For every `W ≥ 1` and every positive seed `0 < a_0 < 2^W`, there exists an index
`n < 60 * W` where `orbit a_0 n % 2 ≠ tmEncodedParity n`. -/
theorem tmEncodedParity_mismatch_lt_sixty_mul_bit_length {a_0 W : ℕ}
    (ha0 : 0 < a_0) (hW1 : 1 ≤ W) (hW : a_0 < 2 ^ W) :
    ∃ n < 60 * W, orbit a_0 n % 2 ≠ tmEncodedParity n := by
  obtain ⟨k, hk_lo, hk_hi⟩ := exists_two_pow_sandwich hW1
  have hcut := tmEncodedParity_finite_seed_cutoff ha0 hW hk_lo
  by_contra hno
  apply hcut
  intro n hn
  have hn60 : n < 60 * W := by omega
  by_contra hne
  exact hno ⟨n, hn60, hne⟩

private theorem n_lt_two_pow_tm (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- **Unconditional Non-Realizability of `tmEncodedParity` by Any Nonnegative Integer Seed
(`no_nonneg_seed_realizes_tmEncodedParity`)**:
For **every** nonnegative integer `a_0 : ℕ` (including `a_0 = 0`), there exists
`n : ℕ` with `orbit a_0 n % 2 ≠ tmEncodedParity n`. -/
theorem no_nonneg_seed_realizes_tmEncodedParity (a_0 : ℕ) :
    (∃ n : ℕ, orbit a_0 n % 2 ≠ tmEncodedParity n) ∧
      ¬ (∀ n : ℕ, orbit a_0 n % 2 = tmEncodedParity n % 2) := by
  have hex : ∃ n : ℕ, orbit a_0 n % 2 ≠ tmEncodedParity n := by
    rcases Nat.eq_zero_or_pos a_0 with rfl | ha0_pos
    · refine ⟨3, ?_⟩
      have horb0 : orbit 0 3 = 0 := zero_seed_all_zero_exception.1 3
      have htm3 : tmEncodedParity 3 = 1 := by
        have h : tmEncodedParity (3 * 1) = tmBit 1 := tmEncodedParity_three_mul 1
        simpa [tmBit_initial_eight.2.1] using h
      rw [horb0, htm3]
      decide
    · have hW : a_0 < 2 ^ a_0 := n_lt_two_pow_tm a_0
      obtain ⟨n, _, hne⟩ :=
        tmEncodedParity_mismatch_lt_sixty_mul_bit_length ha0_pos ha0_pos hW
      exact ⟨n, hne⟩
  refine ⟨hex, ?_⟩
  intro hall
  rcases hex with ⟨n, hne⟩
  have h := hall n
  rw [tmEncodedParity_mod_two] at h
  exact hne h

/-- **Seed-Residue Non-Stabilization for `tmEncodedParity`
(`tmEncodedParity_seedResidue_never_stabilizes`)**:
The constructive least-residue sequence `seedResidue tmEncodedParity N` never
stabilizes at any nonnegative integer `a_0 : ℕ`, and therefore takes infinitely
many strict upward jumps `seedResidue tmEncodedParity N < seedResidue tmEncodedParity (N + 1)`. -/
theorem tmEncodedParity_seedResidue_never_stabilizes :
    (∀ a_0 : ℕ, ¬ (∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue tmEncodedParity N = a_0)) ∧
      (∀ N_0 : ℕ, ∃ N ≥ N_0,
        seedResidue tmEncodedParity N < seedResidue tmEncodedParity (N + 1)) := by
  have hno_stab :
      ∀ a_0 : ℕ, ¬ (∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue tmEncodedParity N = a_0) := by
    intro a_0 hstab
    have hall := (exists_nonneg_seed_iff_seedResidue_stabilizes tmEncodedParity a_0).mpr hstab
    exact (no_nonneg_seed_realizes_tmEncodedParity a_0).2 hall
  refine ⟨hno_stab, ?_⟩
  intro N_0
  by_contra hno_jump
  apply hno_stab (seedResidue tmEncodedParity N_0)
  refine ⟨N_0, ?_⟩
  intro N hN
  induction N with
  | zero =>
      have hN0 : N_0 = 0 := by omega
      subst hN0
      rfl
  | succ N ih =>
      rcases Nat.eq_or_lt_of_le hN with heq | hlt
      · subst heq
        rfl
      · have ihN := ih (by omega)
        have hle := seedResidue_le_succ tmEncodedParity N
        have hnot_lt :
            ¬ (seedResidue tmEncodedParity N < seedResidue tmEncodedParity (N + 1)) :=
          fun h => hno_jump ⟨N, by omega, h⟩
        omega

/-- **Concrete Structured Aperiodic Fractional Survivor Excluded from All Ordinary Integer Seeds
(`tmEncodedStream_aperiodic_fractional_survivor_not_integer_realizable`)**:
Combines real fractional-tail admissibility (`0 ≤ fractionalTail tmEncodedStream n ≤ 9/19 < 1/2`),
sub-`60 W` finite parity mismatch for positive seeds, unconditional non-realizability
for all nonnegative integer seeds, and non-stabilization of `seedResidue tmEncodedParity`. -/
theorem tmEncodedStream_aperiodic_fractional_survivor_not_integer_realizable :
    (∀ n : ℕ, 0 ≤ fractionalTail tmEncodedStream n ∧
      fractionalTail tmEncodedStream n ≤ (9 / 19 : ℝ) ∧
      fractionalTail tmEncodedStream n < (1 / 2 : ℝ)) ∧
    (∀ {a_0 W : ℕ}, 0 < a_0 → 1 ≤ W → a_0 < 2 ^ W →
      ∃ n < 60 * W, orbit a_0 n % 2 ≠ tmEncodedParity n) ∧
    (∀ a_0 : ℕ, ∃ n : ℕ, orbit a_0 n % 2 ≠ tmEncodedParity n) ∧
    (∀ a_0 : ℕ, ¬ (∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue tmEncodedParity N = a_0)) := by
  refine ⟨fun n => ⟨(tmEncodedStream_fractionalTail_admissible n).1,
      (tmEncodedStream_fractionalTail_admissible n).2.1,
      (tmEncodedStream_fractionalTail_admissible n).2.2.1⟩,
    fun ha0 hW1 hW => tmEncodedParity_mismatch_lt_sixty_mul_bit_length ha0 hW1 hW,
    fun a_0 => (no_nonneg_seed_realizes_tmEncodedParity a_0).1,
    tmEncodedParity_seedResidue_never_stabilizes.1⟩

/-- **Fixed-Shift & Orbit-Preperiod Extension (`tmEncodedParity_shifted_finite_seed_cutoff`)**:
For any fixed shift `h : ℕ` of the encoded Thue–Morse stream and any positive seed
`0 < a_0 < 2^W` with `W + h ≤ 2^k`, `orbit a_0` cannot match `fun n => tmEncodedParity (h + n)`
across `0 ≤ n < 30 * 2^k - h` (and similarly after any orbit preperiod `p_0` with
`orbit a_0 p_0 < 2^W`). -/
theorem tmEncodedParity_shifted_finite_seed_cutoff {a_0 W h k : ℕ}
    (ha0 : 0 < a_0) (hW : a_0 < 2 ^ W) (hhk : W + h ≤ 2 ^ k) :
    ¬ (∀ n < 30 * 2 ^ k - h, orbit a_0 n % 2 = tmEncodedParity (h + n)) := by
  intro hmatch
  set R := 2 ^ k
  have hR : 1 ≤ R := Nat.pow_pos (by decide)
  have hbound := tm_seed_growth_lt_two_pow hR hW hhk
  apply scalable_early_repetition_cutoff (ε := fun n => tmEncodedParity (h + n))
    (L := 12 * R - h) (H := 18 * R) (i := 0) (j := 18 * R)
    ha0 (by omega) le_rfl hbound
  · intro t ht
    simp only [Nat.zero_add, tmEncodedParity_mod_two]
    have hht : h + t < 12 * 2 ^ k := by omega
    have hrep := tmEncodedParity_scaled_window_repeat k hht
    have hidx : 18 * 2 ^ k + (h + t) = h + (18 * R + t) := by omega
    rwa [hidx] at hrep
  · intro n hn
    have hn_lt : n < 30 * 2 ^ k - h := by omega
    rw [hmatch n hn_lt, tmEncodedParity_mod_two]

/-- Orbit-preperiod version: if `0 < a_0` and `orbit a_0 p_0 < 2^W` with `W + h ≤ 2^k`,
then `orbit a_0 (p_0 + n)` cannot match `tmEncodedParity (h + n)` for all `n < 30 * 2^k - h`. -/
theorem tmEncodedParity_orbit_preperiod_cutoff {a_0 p_0 W h k : ℕ}
    (ha0 : 0 < a_0) (horb : orbit a_0 p_0 < 2 ^ W) (hhk : W + h ≤ 2 ^ k) :
    ¬ (∀ n < 30 * 2 ^ k - h, orbit a_0 (p_0 + n) % 2 = tmEncodedParity (h + n)) := by
  intro hmatch
  have hp0_pos : 0 < orbit a_0 p_0 := by
    have hle : a_0 ≤ orbit a_0 p_0 := orbit_le_of_le a_0 (Nat.zero_le p_0)
    omega
  apply tmEncodedParity_shifted_finite_seed_cutoff hp0_pos horb hhk
  intro n hn
  rw [← orbit_add a_0 p_0 n]
  exact hmatch n hn

/-- The bitwise-complemented 3-step encoded Thue–Morse parity stream
(`ε'_{3n} = 1 - tmBit n`, `ε'_{3n+1} = ε'_{3n+2} = 0`). -/
def tmComplementEncodedParity (n : ℕ) : ℕ :=
  if n % 3 = 0 then 1 - tmBit (n / 3) else 0

theorem tmComplementEncodedParity_le_one (n : ℕ) :
    tmComplementEncodedParity n ≤ 1 := by
  unfold tmComplementEncodedParity
  split_ifs <;> omega

@[simp] theorem tmComplementEncodedParity_mod_two (n : ℕ) :
    tmComplementEncodedParity n % 2 = tmComplementEncodedParity n := by
  have h := tmComplementEncodedParity_le_one n
  omega

/-- All-scale window inflation for the complemented Thue–Morse encoding `tmComplementEncodedParity`. -/
theorem tmComplementEncodedParity_scaled_window_repeat (k : ℕ) {i : ℕ} (hi : i < 12 * 2 ^ k) :
    tmComplementEncodedParity i = tmComplementEncodedParity (18 * 2 ^ k + i) := by
  have hq : i / 3 < 4 * 2 ^ k := by omega
  unfold tmComplementEncodedParity
  have hmod : (18 * 2 ^ k + i) % 3 = i % 3 := by omega
  rw [hmod]
  split_ifs with hr0
  · have hdiv : (18 * 2 ^ k + i) / 3 = 6 * 2 ^ k + i / 3 := by omega
    rw [hdiv, tmBit_scaled_window_repeat k hq]
  · rfl

/-- **Explicit Finite-Horizon Seed Cutoff for Complemented Thue–Morse (`tmComplementEncodedParity_finite_seed_cutoff`)**:
For any `0 < a_0 < 2^W` and `W + h ≤ 2^k`, `orbit a_0` cannot match
`fun n => tmComplementEncodedParity (h + n)` across `0 ≤ n < 30 * 2^k - h`. -/
theorem tmComplementEncodedParity_finite_seed_cutoff {a_0 W h k : ℕ}
    (ha0 : 0 < a_0) (hW : a_0 < 2 ^ W) (hhk : W + h ≤ 2 ^ k) :
    ¬ (∀ n < 30 * 2 ^ k - h, orbit a_0 n % 2 = tmComplementEncodedParity (h + n)) := by
  intro hmatch
  set R := 2 ^ k
  have hR : 1 ≤ R := Nat.pow_pos (by decide)
  have hbound := tm_seed_growth_lt_two_pow hR hW hhk
  apply scalable_early_repetition_cutoff (ε := fun n => tmComplementEncodedParity (h + n))
    (L := 12 * R - h) (H := 18 * R) (i := 0) (j := 18 * R)
    ha0 (by omega) le_rfl hbound
  · intro t ht
    simp only [Nat.zero_add, tmComplementEncodedParity_mod_two]
    have hht : h + t < 12 * 2 ^ k := by omega
    have hrep := tmComplementEncodedParity_scaled_window_repeat k hht
    have hidx : 18 * 2 ^ k + (h + t) = h + (18 * R + t) := by omega
    rwa [hidx] at hrep
  · intro n hn
    have hn_lt : n < 30 * 2 ^ k - h := by omega
    rw [hmatch n hn_lt, tmComplementEncodedParity_mod_two]

private theorem tmBit_not_odd_eventually_periodic (q N_0 : ℕ) :
    ¬ (∀ n ≥ N_0, tmBit (n + (2 * q + 1)) = tmBit n) := by
  intro hper
  have hflip : ∀ m ≥ N_0, tmBit m = 1 - tmBit (m + q) := by
    intro m hm
    have h2m : 2 * m ≥ N_0 := by omega
    have hp := hper (2 * m) h2m
    have hidx : 2 * m + (2 * q + 1) = 2 * (m + q) + 1 := by omega
    rw [hidx, tmBit_two_mul_add_one, tmBit_two_mul] at hp
    exact hp.symm
  have h1 := hflip N_0 le_rfl
  have h2 := hflip (2 * N_0) (by omega)
  have h3 := hflip (2 * N_0 + q) (by omega)
  have hev1 : tmBit (2 * N_0) = tmBit N_0 := tmBit_two_mul N_0
  have hev2 : tmBit (2 * N_0 + q + q) = tmBit (N_0 + q) := by
    have hidx : 2 * N_0 + q + q = 2 * (N_0 + q) := by omega
    rw [hidx, tmBit_two_mul]
  rw [hev1] at h2
  rw [hev2] at h3
  have hle1 := tmBit_le_one N_0
  have hle2 := tmBit_le_one (N_0 + q)
  have hle3 := tmBit_le_one (2 * N_0 + q)
  omega

/-- **Unconditional Non-Eventual-Periodicity of Thue–Morse (`tmBit_not_eventually_periodic`)**:
For every period `p ≥ 1` and threshold `N_0 : ℕ`, there exists `n ≥ N_0` such that
`tmBit (n + p) ≠ tmBit n`. -/
theorem tmBit_not_eventually_periodic {p : ℕ} (hp : 1 ≤ p) (N_0 : ℕ) :
    ∃ n ≥ N_0, tmBit (n + p) ≠ tmBit n := by
  by_contra hno
  have hper : ∀ n ≥ N_0, tmBit (n + p) = tmBit n := by
    intro n hn
    by_contra hne
    exact hno ⟨n, hn, hne⟩
  clear hno
  revert hp hper
  induction p using Nat.strong_induction_on with
  | h p ih =>
      intro hp hper
      rcases (by omega : p % 2 = 1 ∨ p % 2 = 0) with hodd | heven
      · have hp_eq : p = 2 * (p / 2) + 1 := by omega
        rw [hp_eq] at hper
        exact tmBit_not_odd_eventually_periodic (p / 2) N_0 hper
      · have hlt : p / 2 < p := by omega
        have hpos : 1 ≤ p / 2 := by omega
        apply ih (p / 2) hlt hpos
        intro n hn
        have h2n : 2 * n ≥ N_0 := by omega
        have hp2n := hper (2 * n) h2n
        have hidx : 2 * n + p = 2 * (n + p / 2) := by omega
        rw [hidx, tmBit_two_mul, tmBit_two_mul] at hp2n
        exact hp2n

/-- **Unconditional Non-Eventual-Periodicity of `tmEncodedParity`
(`tmEncodedParity_not_eventually_periodic`)**:
For every period `p ≥ 1` and threshold `N_0 : ℕ`, there exists `n ≥ N_0` such that
`tmEncodedParity (n + p) ≠ tmEncodedParity n`. -/
theorem tmEncodedParity_not_eventually_periodic {p : ℕ} (hp : 1 ≤ p) (N_0 : ℕ) :
    ∃ n ≥ N_0, tmEncodedParity (n + p) ≠ tmEncodedParity n := by
  by_contra hno
  have hper : ∀ n ≥ N_0, tmEncodedParity (n + p) = tmEncodedParity n := by
    intro n hn
    by_contra hne
    exact hno ⟨n, hn, hne⟩
  obtain ⟨m, hm, hne⟩ := tmBit_not_eventually_periodic hp N_0
  apply hne
  have h1 := hper (3 * m) (by omega)
  have h2 := hper (3 * m + p) (by omega)
  have h3 := hper (3 * m + 2 * p) (by omega)
  have hidx1 : 3 * m + 2 * p + p = 3 * (m + p) := by omega
  have hidx2 : 3 * m + p + p = 3 * m + 2 * p := by omega
  rw [hidx1, tmEncodedParity_three_mul] at h3
  rw [hidx2] at h2
  rw [tmEncodedParity_three_mul] at h1
  omega

/-! ## 6. Quantitative Thue–Morse Seed-Bit Forcing (`seedResidue ≥ 2^R` & `< 60 N_0` Jump Window) -/

/-- For every horizon `N ≥ 4`, `0 < seedResidue tmEncodedParity N` because `tmEncodedParity 3 = 1`. -/
theorem seedResidue_tmEncodedParity_pos {N : ℕ} (hN : 4 ≤ N) :
    0 < seedResidue tmEncodedParity N := by
  by_contra hle
  have hzero : seedResidue tmEncodedParity N = 0 := by omega
  have h3 := orbit_seedResidue_mod_two tmEncodedParity N 3 (by omega)
  have horb0 : orbit 0 3 = 0 := zero_seed_all_zero_exception.1 3
  have htm3 : tmEncodedParity 3 = 1 := by
    have h : tmEncodedParity (3 * 1) = tmBit 1 := tmEncodedParity_three_mul 1
    simpa [tmBit_initial_eight.2.1] using h
  rw [hzero, horb0, htm3] at h3
  omega

/-- **Quantitative Dyadic Growth of `seedResidue tmEncodedParity` (`seedResidue_tmEncodedParity_ge_two_pow`)**:
For every scale `k : ℕ` (`R = 2^k`), the least seed residue realizing `tmEncodedParity`
at horizon `30 * 2^k` satisfies:
`2 ^ (2 ^ k) ≤ seedResidue tmEncodedParity (30 * 2 ^ k)`. -/
theorem seedResidue_tmEncodedParity_ge_two_pow (k : ℕ) :
    2 ^ (2 ^ k) ≤ seedResidue tmEncodedParity (30 * 2 ^ k) := by
  set R := 2 ^ k
  have hR : 1 ≤ R := Nat.pow_pos (by decide)
  have hpos : 0 < seedResidue tmEncodedParity (30 * R) :=
    seedResidue_tmEncodedParity_pos (by omega)
  by_contra hlt
  have hlt' : seedResidue tmEncodedParity (30 * R) < 2 ^ R := by omega
  apply tmEncodedParity_finite_seed_cutoff (W := R) (k := k) hpos hlt' le_rfl
  intro n hn
  have hmod := orbit_seedResidue_mod_two tmEncodedParity (30 * R) n hn
  rwa [tmEncodedParity_mod_two] at hmod

/-- **Bounded Waiting Window for Forced Nonzero Extension Bits (`tmEncodedParity_forced_seedBit_in_sixty_mul_window`)**:
For every starting horizon `1 ≤ N_0`, there exists `N` in `[N_0, 60 * N_0)` such that
`seedResidue tmEncodedParity N < seedResidue tmEncodedParity (N + 1)` and
`seedBit tmEncodedParity (seedResidue tmEncodedParity N) N = 1`. -/
theorem tmEncodedParity_forced_seedBit_in_sixty_mul_window {N_0 : ℕ} (hN0 : 1 ≤ N_0) :
    ∃ N : ℕ, N_0 ≤ N ∧ N < 60 * N_0 ∧
      seedResidue tmEncodedParity N < seedResidue tmEncodedParity (N + 1) ∧
      seedBit tmEncodedParity (seedResidue tmEncodedParity N) N = 1 := by
  obtain ⟨k, hk_lo, hk_hi⟩ := exists_two_pow_sandwich hN0
  set R := 2 ^ k
  have hlt_N0 : seedResidue tmEncodedParity N_0 < 2 ^ N_0 :=
    seedResidue_lt_two_pow tmEncodedParity N_0
  have hpow_le : 2 ^ N_0 ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) hk_lo
  have hge_30R : 2 ^ R ≤ seedResidue tmEncodedParity (30 * R) :=
    seedResidue_tmEncodedParity_ge_two_pow k
  have hstrict : seedResidue tmEncodedParity N_0 < seedResidue tmEncodedParity (30 * R) :=
    lt_of_lt_of_le (lt_of_lt_of_le hlt_N0 hpow_le) hge_30R
  have hex_jump :
      ∃ N : ℕ, N_0 ≤ N ∧ N < 30 * R ∧
        seedResidue tmEncodedParity N < seedResidue tmEncodedParity (N + 1) := by
    by_contra hno
    have hconst : ∀ M : ℕ, N_0 ≤ M → M ≤ 30 * R →
        seedResidue tmEncodedParity M = seedResidue tmEncodedParity N_0 := by
      intro M hM_lo hM_hi
      induction M with
      | zero => omega
      | succ M ih =>
          rcases Nat.eq_or_lt_of_le hM_lo with heq | hlt
          · subst heq; rfl
          · have ihM := ih (by omega) (by omega)
            have hle := seedResidue_le_succ tmEncodedParity M
            have hnot_lt :
                ¬ (seedResidue tmEncodedParity M < seedResidue tmEncodedParity (M + 1)) :=
              fun h => hno ⟨M, by omega, by omega, h⟩
            omega
    have heq := hconst (30 * R) (by omega) le_rfl
    omega
  rcases hex_jump with ⟨N, hN_lo, hN_hi, hjump⟩
  have hbit1 : seedBit tmEncodedParity (seedResidue tmEncodedParity N) N = 1 := by
    have hsucc :
        seedResidue tmEncodedParity (N + 1) =
          seedResidue tmEncodedParity N +
            seedBit tmEncodedParity (seedResidue tmEncodedParity N) N * 2 ^ N := rfl
    have hbit_le := seedBit_le_one tmEncodedParity (seedResidue tmEncodedParity N) N
    rcases (by omega : seedBit tmEncodedParity (seedResidue tmEncodedParity N) N = 0 ∨
        seedBit tmEncodedParity (seedResidue tmEncodedParity N) N = 1) with hb0 | hb1
    · rw [hb0, Nat.zero_mul, Nat.add_zero] at hsucc
      omega
    · exact hb1
  exact ⟨N, hN_lo, by omega, hjump, hbit1⟩

/-! ## 7. Reusable Dyadic-Inflation Cutoff, Thue–Morse Block-Length Coding & Period-Doubling Exclusion -/

/-- **General Reusable Dyadic-Inflation Parity Cutoff (`dyadic_inflated_repetition_cutoff`)**:
If a parity stream `ε : ℕ → ℕ` has base window length `1 ≤ L_0` and origin shift `1 ≤ H_0`
satisfying:
1. `3 ^ H_0 < 2 ^ (L_0 + H_0 - 1)`, and
2. `∀ k i, i < L_0 * 2^k → ε i % 2 = ε (H_0 * 2^k + i) % 2`,
then:
- For every `k : ℕ`, `W ≤ 2^k`, and `0 < a_0 < 2^W`, `orbit a_0` cannot match `ε`
  across `0 ≤ n < (H_0 + L_0) * 2^k`.
- For every `1 ≤ W` and `0 < a_0 < 2^W`, there exists `n < 2 * (H_0 + L_0) * W`
  with `orbit a_0 n % 2 ≠ ε n % 2`. -/
theorem dyadic_inflated_repetition_cutoff
    {ε : ℕ → ℕ} {L_0 H_0 : ℕ}
    (hL0 : 1 ≤ L_0) (hH0 : 1 ≤ H_0)
    (hpow : 3 ^ H_0 < 2 ^ (L_0 + H_0 - 1))
    (hrep : ∀ (k i : ℕ), i < L_0 * 2 ^ k → ε i % 2 = ε (H_0 * 2 ^ k + i) % 2) :
    (∀ {a_0 W k : ℕ}, 0 < a_0 → a_0 < 2 ^ W → W ≤ 2 ^ k →
      ¬ (∀ n < (H_0 + L_0) * 2 ^ k, orbit a_0 n % 2 = ε n % 2)) ∧
    (∀ {a_0 W : ℕ}, 0 < a_0 → 1 ≤ W → a_0 < 2 ^ W →
      ∃ n < 2 * (H_0 + L_0) * W, orbit a_0 n % 2 ≠ ε n % 2) := by
  have hcut :
      ∀ {a_0 W k : ℕ}, 0 < a_0 → a_0 < 2 ^ W → W ≤ 2 ^ k →
        ¬ (∀ n < (H_0 + L_0) * 2 ^ k, orbit a_0 n % 2 = ε n % 2) := by
    intro a_0 W k ha0 hW hk hmatch
    set R := 2 ^ k
    have hR : 1 ≤ R := Nat.pow_pos (by decide)
    have h3R : 3 ^ (H_0 * R) < 2 ^ ((L_0 + H_0 - 1) * R) := by
      rw [Nat.pow_mul 3 H_0 R, Nat.pow_mul 2 (L_0 + H_0 - 1) R]
      exact pow_strict_mono_left_tm hR hpow
    have ha0_le : a_0 + 1 ≤ 2 ^ W := by omega
    have h1 : (a_0 + 1) * 3 ^ (H_0 * R) ≤ 2 ^ W * 3 ^ (H_0 * R) :=
      Nat.mul_le_mul_right _ ha0_le
    have h2 : 2 ^ W * 3 ^ (H_0 * R) < 2 ^ W * 2 ^ ((L_0 + H_0 - 1) * R) :=
      Nat.mul_lt_mul_of_pos_left h3R (Nat.pow_pos (by decide))
    have h3 : 2 ^ W * 2 ^ ((L_0 + H_0 - 1) * R) = 2 ^ (W + (L_0 + H_0 - 1) * R) := by
      rw [← Nat.pow_add]
    have hexp_le : W + (L_0 + H_0 - 1) * R ≤ L_0 * R + H_0 * R := by
      have hsub : (L_0 + H_0 - 1) * R + R = (L_0 + H_0) * R := by
        have h : L_0 + H_0 - 1 + 1 = L_0 + H_0 := by omega
        calc
          (L_0 + H_0 - 1) * R + R = (L_0 + H_0 - 1 + 1) * R := by ring
          _ = (L_0 + H_0) * R := by rw [h]
      have hadd : (L_0 + H_0) * R = L_0 * R + H_0 * R := by ring
      omega
    have h4 : 2 ^ (W + (L_0 + H_0 - 1) * R) ≤ 2 ^ (L_0 * R + H_0 * R) :=
      Nat.pow_le_pow_right (by decide) hexp_le
    have hbound : (a_0 + 1) * 3 ^ (H_0 * R) < 2 ^ (L_0 * R + H_0 * R) :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le (by rwa [h3] at h2) h4)
    have hHR_pos : 0 < H_0 * R := Nat.mul_pos hH0 hR
    apply scalable_early_repetition_cutoff (ε := ε)
      (L := L_0 * R) (H := H_0 * R) (i := 0) (j := H_0 * R)
      ha0 hHR_pos le_rfl hbound
    · intro t ht
      simp only [Nat.zero_add]
      exact hrep k t ht
    · intro n hn
      have hn' : n < (H_0 + L_0) * R := by
        have hring : (H_0 + L_0) * R = H_0 * R + L_0 * R := by ring
        omega
      exact hmatch n hn'
  refine ⟨hcut, ?_⟩
  intro a_0 W ha0 hW1 hW
  obtain ⟨k, hk_lo, hk_hi⟩ := exists_two_pow_sandwich hW1
  have hc := hcut ha0 hW hk_lo
  by_contra hno
  apply hc
  intro n hn
  have hn2 : n < 2 * (H_0 + L_0) * W := by
    have hmul : (H_0 + L_0) * 2 ^ k < (H_0 + L_0) * (2 * W) :=
      Nat.mul_lt_mul_of_pos_left hk_hi (by omega)
    have hring : (H_0 + L_0) * (2 * W) = 2 * (H_0 + L_0) * W := by ring
    omega
  by_contra hne
  exact hno ⟨n, hn2, hne⟩

/-- Two-letter Thue–Morse block-length sequence `s(n) = a + (b - a) * tmBit n`. -/
def tmBlockSeq (a b n : ℕ) : ℕ :=
  a + (b - a) * tmBit n

/-- Every entry of `tmBlockSeq a b` (`a ≤ b`) satisfies `a ≤ tmBlockSeq a b n ≤ b`. -/
theorem tmBlockSeq_bounds {a b : ℕ} (hab : a ≤ b) (n : ℕ) :
    a ≤ tmBlockSeq a b n ∧ tmBlockSeq a b n ≤ b := by
  unfold tmBlockSeq
  have h := tmBit_le_one n
  have hmul : (b - a) * tmBit n ≤ (b - a) * 1 := Nat.mul_le_mul_left (b - a) h
  omega

/-- Exact pair-balance of `tmBlockSeq`: `tmBlockSeq a b (2 * j) + tmBlockSeq a b (2 * j + 1) = a + b`. -/
theorem tmBlockSeq_pair_sum {a b : ℕ} (hab : a ≤ b) (j : ℕ) :
    tmBlockSeq a b (2 * j) + tmBlockSeq a b (2 * j + 1) = a + b := by
  unfold tmBlockSeq
  have hpair := tmBit_pair_sum_eq_one j
  have hdist :
      (a + (b - a) * tmBit (2 * j)) + (a + (b - a) * tmBit (2 * j + 1)) =
        2 * a + (b - a) * (tmBit (2 * j) + tmBit (2 * j + 1)) := by ring
  rw [hdist, hpair]
  omega

/-- Exact cumulative steps at even block horizons:
`blockSteps (tmBlockSeq a b) (2 * m) = m * (a + b)`. -/
theorem blockSteps_tmBlockSeq_two_mul {a b : ℕ} (hab : a ≤ b) (m : ℕ) :
    blockSteps (tmBlockSeq a b) (2 * m) = m * (a + b) := by
  induction m with
  | zero => simp [blockSteps]
  | succ m ih =>
      have hidx : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [hidx]
      simp only [blockSteps]
      rw [ih]
      have hpair := tmBlockSeq_pair_sum hab m
      linarith

/-- All-scale window repetition for `tmBlockSeq a b`:
for every `k : ℕ` and `i < 4 * 2^k`, `tmBlockSeq a b i = tmBlockSeq a b (6 * 2^k + i)`. -/
theorem tmBlockSeq_scaled_window_repeat (a b k : ℕ) {i : ℕ} (hi : i < 4 * 2 ^ k) :
    tmBlockSeq a b i = tmBlockSeq a b (6 * 2 ^ k + i) := by
  unfold tmBlockSeq
  rw [tmBit_scaled_window_repeat k hi]

/-- **Explicit Finite-Seed Cutoff for Thue–Morse Block-Length Codings (`tmBlockSeq_finite_seed_cutoff`)**:
For any `3 ≤ a ≤ b`, scale `k : ℕ` (`R = 2^k`), `10 * 2^k ≤ K`, and `a_0 < 2^W`,
along any `ValidBlockChain a_0 (tmBlockSeq a b) u K`:
`2 ^ k * (a + b) ≤ 5 * W + 2`. -/
theorem tmBlockSeq_finite_seed_cutoff
    {a b a_0 W k K : ℕ} {u : ℕ → ℕ}
    (ha3 : 3 ≤ a) (hab : a ≤ b) (hK : 10 * 2 ^ k ≤ K) (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 (tmBlockSeq a b) u K) :
    2 ^ k * (a + b) ≤ 5 * W + 2 := by
  set R := 2 ^ k
  have hR : 1 ≤ R := Nat.pow_pos (by decide)
  have h3_all : ∀ j < 6 * R, 3 ≤ tmBlockSeq a b j := by
    intro j _
    have hb := (tmBlockSeq_bounds hab j).1
    omega
  have hshift0 : shiftSeq (tmBlockSeq a b) 0 = tmBlockSeq a b := by
    funext n
    simp [shiftSeq]
  have hslack : 0 < integerSlack (tmBlockSeq a b) (6 * R) := by
    have h := (all_shifted_slacks_pos_of_three_le (tmBlockSeq a b) (6 * R) h3_all).2 0 (Nat.zero_le _)
    rw [hshift0, Nat.sub_zero] at h
    exact h
  have hcut :=
    parameterized_pq_repeated_subword_cutoff
      (p := 3) (q := 5) (r1 := 0) (r2 := 6 * R) (L := 4 * R)
      (by decide : 1 ≤ 5) (by decide : 3 ^ 5 < 2 ^ (3 + 5))
      (by omega : 1 ≤ 4 * R) (by omega : 0 < 6 * R) (by omega : 6 * R + (4 * R - 1) < K)
      ha0 hchain hslack
      (fun i hi => by simpa using tmBlockSeq_scaled_window_repeat a b k hi)
  have hS : blockSteps (tmBlockSeq a b) (4 * R) = 2 * R * (a + b) := by
    have h4 : 4 * R = 2 * (2 * R) := by ring
    rw [h4, blockSteps_tmBlockSeq_two_mul hab (2 * R)]
  have hT : blockSteps (tmBlockSeq a b) (6 * R) = 3 * R * (a + b) := by
    have h6 : 6 * R = 2 * (3 * R) := by ring
    rw [h6, blockSteps_tmBlockSeq_two_mul hab (3 * R)]
  rw [hshift0, hS, hT] at hcut
  linarith

/-- **Unconditional Exclusion of Infinite Thue–Morse Block-Length Chains
(`no_infinite_tmBlockSeq_block_chain`)**:
For any `3 ≤ a ≤ b` and any integer seed `a_0 : ℕ`, there is **no** infinite valid
integer block chain `∀ K : ℕ, ValidBlockChain a_0 (tmBlockSeq a b) u K`. -/
theorem no_infinite_tmBlockSeq_block_chain {a b a_0 : ℕ} (ha3 : 3 ≤ a) (hab : a ≤ b) :
    ¬ (∃ u : ℕ → ℕ, ∀ K : ℕ, ValidBlockChain a_0 (tmBlockSeq a b) u K) := by
  rintro ⟨u, hchain⟩
  have ha0 : a_0 < 2 ^ a_0 := n_lt_two_pow_tm a_0
  set k := 5 * a_0 + 3
  have hk_lt : k < 2 ^ k := n_lt_two_pow_tm k
  have hcut :=
    tmBlockSeq_finite_seed_cutoff (k := k) (K := 10 * 2 ^ k)
      ha3 hab le_rfl ha0 (hchain (10 * 2 ^ k))
  have hab6 : 6 ≤ a + b := by omega
  have hmul : 2 ^ k * 6 ≤ 2 ^ k * (a + b) := Nat.mul_le_mul_left (2 ^ k) hab6
  omega

/-- The canonical Period-Doubling Boolean sequence `pdBool : ℕ → Bool`
(`0 ↦ 01, 1 ↦ 00`, satisfying `d(2n) = 0, d(2n+1) = 1 - d(n)`). -/
def pdBool : ℕ → Bool
  | 0 => false
  | n + 1 =>
      if (n + 1) % 2 = 0 then false
      else !pdBool ((n + 1) / 2)
decreasing_by all_goals omega

/-- The `{0, 1}`-valued Period-Doubling sequence `pdBit n = if pdBool n then 1 else 0`. -/
def pdBit (n : ℕ) : ℕ :=
  if pdBool n then 1 else 0

@[simp] theorem pdBool_zero : pdBool 0 = false := by
  unfold pdBool
  rfl

@[simp] theorem pdBool_two_mul (k : ℕ) : pdBool (2 * k) = false := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hsucc : 2 * k = (2 * k - 1) + 1 := by omega
    conv_lhs => rw [hsucc, pdBool]
    have hmod : ((2 * k - 1) + 1) % 2 = 0 := by omega
    simp [hmod]

@[simp] theorem pdBool_two_mul_add_one (k : ℕ) : pdBool (2 * k + 1) = !pdBool k := by
  conv_lhs => rw [pdBool]
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [hmod, hdiv]

theorem pdBit_le_one (n : ℕ) : pdBit n ≤ 1 := by
  unfold pdBit
  split_ifs <;> omega

@[simp] theorem pdBit_two_mul (k : ℕ) : pdBit (2 * k) = 0 := by
  simp [pdBit]

@[simp] theorem pdBit_two_mul_add_one (k : ℕ) : pdBit (2 * k + 1) = 1 - pdBit k := by
  unfold pdBit
  rw [pdBool_two_mul_add_one]
  cases pdBool k <;> rfl

/-- `pdBit` is distinct from `tmBit` (`pdBit 2 = 0 ≠ 1 = tmBit 2`). -/
theorem pdBit_ne_tmBit : pdBit 2 = 0 ∧ tmBit 2 = 1 ∧ pdBit ≠ tmBit := by
  have hp2 : pdBit 2 = 0 := by simpa using pdBit_two_mul 1
  have ht2 : tmBit 2 = 1 := tmBit_initial_eight.2.2.1
  refine ⟨hp2, ht2, ?_⟩
  intro heq
  have h := congrFun heq 2
  omega

/-- Base 3-symbol repetition of `pdBit`: for `i < 3`, `pdBit i = pdBit (4 + i)` (`010`). -/
theorem pdBit_base_three_repeat {i : ℕ} (hi : i < 3) :
    pdBit i = pdBit (4 + i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · have h0 : pdBit (2 * 0) = 0 := pdBit_two_mul 0
    have h4 : pdBit (2 * 2) = 0 := pdBit_two_mul 2
    simpa using h0.trans h4.symm
  · have h0 : pdBit 0 = 0 := by simpa using pdBit_two_mul 0
    have h2 : pdBit 2 = 0 := by simpa using pdBit_two_mul 1
    have h1 : pdBit 1 = 1 := by simpa [h0] using pdBit_two_mul_add_one 0
    have h5 : pdBit 5 = 1 := by simpa [h2] using pdBit_two_mul_add_one 2
    simpa [h1] using h5.symm
  · have h2 : pdBit (2 * 1) = 0 := pdBit_two_mul 1
    have h6 : pdBit (2 * 3) = 0 := pdBit_two_mul 3
    simpa using h2.trans h6.symm

/-- **All-Scale Period-Doubling Window Inflation (`pdBit_scaled_window_repeat`)**:
For every scale `k : ℕ` (`R = 2^k`) and every `i < 3 * 2^k`,
`pdBit i = pdBit (4 * 2^k + i)`. -/
theorem pdBit_scaled_window_repeat (k : ℕ) :
    ∀ {i : ℕ}, i < 3 * 2 ^ k → pdBit i = pdBit (4 * 2 ^ k + i) := by
  induction k with
  | zero =>
      intro i hi
      simpa using pdBit_base_three_repeat (by simpa using hi)
  | succ k ih =>
      intro i hi
      rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hmod0 | hmod1
      · have hi_eq : i = 2 * (i / 2) := by omega
        have hrhs_eq : 4 * 2 ^ (k + 1) + i = 2 * (4 * 2 ^ k + i / 2) := by
          rw [Nat.pow_succ]
          omega
        conv_lhs => rw [hi_eq]
        rw [hrhs_eq, pdBit_two_mul, pdBit_two_mul]
      · have hj : i / 2 < 3 * 2 ^ k := by
          rw [Nat.pow_succ] at hi
          omega
        have ihj := ih hj
        have hi_eq : i = 2 * (i / 2) + 1 := by omega
        have hrhs_eq : 4 * 2 ^ (k + 1) + i = 2 * (4 * 2 ^ k + i / 2) + 1 := by
          rw [Nat.pow_succ]
          omega
        conv_lhs => rw [hi_eq]
        rw [hrhs_eq, pdBit_two_mul_add_one, pdBit_two_mul_add_one, ihj]

/-- The 3-step zero-encoded Period-Doubling parity stream
(`pdEncodedParity (3 * n) = pdBit n`, `pdEncodedParity (3 * n + 1) = pdEncodedParity (3 * n + 2) = 0`). -/
def pdEncodedParity (n : ℕ) : ℕ :=
  if n % 3 = 0 then pdBit (n / 3) else 0

theorem pdEncodedParity_le_one (n : ℕ) : pdEncodedParity n ≤ 1 := by
  unfold pdEncodedParity
  split_ifs
  · exact pdBit_le_one (n / 3)
  · omega

@[simp] theorem pdEncodedParity_mod_two (n : ℕ) :
    pdEncodedParity n % 2 = pdEncodedParity n := by
  have h := pdEncodedParity_le_one n
  omega

/-- All-scale window inflation for `pdEncodedParity`:
for every `k : ℕ` and `i < 9 * 2^k`, `pdEncodedParity i = pdEncodedParity (12 * 2^k + i)`. -/
theorem pdEncodedParity_scaled_window_repeat (k : ℕ) {i : ℕ} (hi : i < 9 * 2 ^ k) :
    pdEncodedParity i = pdEncodedParity (12 * 2 ^ k + i) := by
  have hq : i / 3 < 3 * 2 ^ k := by omega
  unfold pdEncodedParity
  have hmod : (12 * 2 ^ k + i) % 3 = i % 3 := by omega
  rw [hmod]
  split_ifs with hr0
  · have hdiv : (12 * 2 ^ k + i) / 3 = 4 * 2 ^ k + i / 3 := by omega
    rw [hdiv, pdBit_scaled_window_repeat k hq]
  · rfl

/-- **Period-Doubling Finite Seed Cutoff, `< 42 W` Mismatch Bound & Non-Realizability
(`pdEncodedParity_cutoff_and_exclusion`)**:
Applies `dyadic_inflated_repetition_cutoff` with `L_0 = 9`, `H_0 = 12` (`3^12 < 2^20`):
1. For any `0 < a_0 < 2^W` and `W ≤ 2^k`, `orbit a_0` cannot match `pdEncodedParity`
   across `0 ≤ n < 21 * 2^k`.
2. For any `1 ≤ W` and `0 < a_0 < 2^W`, there exists `n < 42 * W` with
   `orbit a_0 n % 2 ≠ pdEncodedParity n`.
3. For every nonnegative integer `a_0 : ℕ`, there exists `n : ℕ` with
   `orbit a_0 n % 2 ≠ pdEncodedParity n`, and `seedResidue pdEncodedParity` never stabilizes. -/
theorem pdEncodedParity_cutoff_and_exclusion :
    (∀ {a_0 W k : ℕ}, 0 < a_0 → a_0 < 2 ^ W → W ≤ 2 ^ k →
      ¬ (∀ n < 21 * 2 ^ k, orbit a_0 n % 2 = pdEncodedParity n)) ∧
    (∀ {a_0 W : ℕ}, 0 < a_0 → 1 ≤ W → a_0 < 2 ^ W →
      ∃ n < 42 * W, orbit a_0 n % 2 ≠ pdEncodedParity n) ∧
    (∀ a_0 : ℕ, ∃ n : ℕ, orbit a_0 n % 2 ≠ pdEncodedParity n) ∧
    (∀ a_0 : ℕ, ¬ (∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue pdEncodedParity N = a_0)) := by
  have hgen :=
    dyadic_inflated_repetition_cutoff (ε := pdEncodedParity) (L_0 := 9) (H_0 := 12)
      (by decide) (by decide) (by decide : 3 ^ 12 < 2 ^ (9 + 12 - 1))
      (fun k i hi => by
        simp only [pdEncodedParity_mod_two]
        exact pdEncodedParity_scaled_window_repeat k hi)
  have h1 :
      ∀ {a_0 W k : ℕ}, 0 < a_0 → a_0 < 2 ^ W → W ≤ 2 ^ k →
        ¬ (∀ n < 21 * 2 ^ k, orbit a_0 n % 2 = pdEncodedParity n) := by
    intro a_0 W k ha0 hW hk hmatch
    apply hgen.1 ha0 hW hk
    intro n hn
    have hn21 : n < 21 * 2 ^ k := by omega
    rw [hmatch n hn21, pdEncodedParity_mod_two]
  have h2 :
      ∀ {a_0 W : ℕ}, 0 < a_0 → 1 ≤ W → a_0 < 2 ^ W →
        ∃ n < 42 * W, orbit a_0 n % 2 ≠ pdEncodedParity n := by
    intro a_0 W ha0 hW1 hW
    obtain ⟨n, hn, hne⟩ := hgen.2 ha0 hW1 hW
    rw [pdEncodedParity_mod_two] at hne
    exact ⟨n, by omega, hne⟩
  have h3 : ∀ a_0 : ℕ, ∃ n : ℕ, orbit a_0 n % 2 ≠ pdEncodedParity n := by
    intro a_0
    rcases Nat.eq_zero_or_pos a_0 with rfl | ha0_pos
    · refine ⟨3, ?_⟩
      have horb0 : orbit 0 3 = 0 := zero_seed_all_zero_exception.1 3
      have hpd3 : pdEncodedParity 3 = 1 := by
        unfold pdEncodedParity
        have h0 : pdBit 0 = 0 := by simpa using pdBit_two_mul 0
        have h1 : pdBit 1 = 1 := by simpa [h0] using pdBit_two_mul_add_one 0
        simpa using h1
      rw [horb0, hpd3]
      decide
    · have hW : a_0 < 2 ^ a_0 := n_lt_two_pow_tm a_0
      obtain ⟨n, _, hne⟩ := h2 ha0_pos ha0_pos hW
      exact ⟨n, hne⟩
  refine ⟨h1, h2, h3, ?_⟩
  intro a_0 hstab
  have hall := (exists_nonneg_seed_iff_seedResidue_stabilizes pdEncodedParity a_0).mpr hstab
  rcases h3 a_0 with ⟨n, hne⟩
  have hn := hall n
  rw [pdEncodedParity_mod_two] at hn
  exact hne hn

private theorem pdBit_not_odd_eventually_periodic (q N_0 : ℕ) :
    ¬ (∀ n ≥ N_0, pdBit (n + (2 * q + 1)) = pdBit n) := by
  intro hper
  set m := N_0 + q
  have h2m : 2 * m ≥ N_0 := by omega
  have hp := hper (2 * m) h2m
  have hidx : 2 * m + (2 * q + 1) = 2 * (m + q) + 1 := by omega
  rw [hidx, pdBit_two_mul_add_one, pdBit_two_mul] at hp
  have hmq_even : m + q = 2 * (N_0 / 2 + q) ∨ m + q = 2 * (N_0 / 2 + q) + 1 := by omega
  rcases hmq_even with hev | _
  · rw [hev, pdBit_two_mul] at hp
    omega
  · set m' := N_0 + q + 1
    have h2m' : 2 * m' ≥ N_0 := by omega
    have hp' := hper (2 * m') h2m'
    have hidx' : 2 * m' + (2 * q + 1) = 2 * (m' + q) + 1 := by omega
    have hev' : m' + q = 2 * (N_0 / 2 + q + 1) := by omega
    rw [hidx', pdBit_two_mul_add_one, pdBit_two_mul, hev', pdBit_two_mul] at hp'
    omega

/-- **Unconditional Non-Eventual-Periodicity of Period-Doubling (`pdBit_not_eventually_periodic`)**:
For every period `p ≥ 1` and threshold `N_0 : ℕ`, there exists `n ≥ N_0` such that
`pdBit (n + p) ≠ pdBit n`. -/
theorem pdBit_not_eventually_periodic {p : ℕ} (hp : 1 ≤ p) (N_0 : ℕ) :
    ∃ n ≥ N_0, pdBit (n + p) ≠ pdBit n := by
  by_contra hno
  have hper : ∀ n ≥ N_0, pdBit (n + p) = pdBit n := by
    intro n hn
    by_contra hne
    exact hno ⟨n, hn, hne⟩
  clear hno
  revert hp hper
  induction p using Nat.strong_induction_on with
  | h p ih =>
      intro hp hper
      rcases (by omega : p % 2 = 1 ∨ p % 2 = 0) with hodd | heven
      · have hp_eq : p = 2 * (p / 2) + 1 := by omega
        rw [hp_eq] at hper
        exact pdBit_not_odd_eventually_periodic (p / 2) N_0 hper
      · have hlt : p / 2 < p := by omega
        have hpos : 1 ≤ p / 2 := by omega
        apply ih (p / 2) hlt hpos
        intro n hn
        have h2n1 : 2 * n + 1 ≥ N_0 := by omega
        have hp2n1 := hper (2 * n + 1) h2n1
        have hidx : 2 * n + 1 + p = 2 * (n + p / 2) + 1 := by omega
        rw [hidx, pdBit_two_mul_add_one, pdBit_two_mul_add_one] at hp2n1
        have hle1 := pdBit_le_one (n + p / 2)
        have hle2 := pdBit_le_one n
        omega

/-- **Unconditional Non-Eventual-Periodicity of `pdEncodedParity`
(`pdEncodedParity_not_eventually_periodic`)**:
For every period `p ≥ 1` and threshold `N_0 : ℕ`, there exists `n ≥ N_0` such that
`pdEncodedParity (n + p) ≠ pdEncodedParity n`. -/
theorem pdEncodedParity_not_eventually_periodic {p : ℕ} (hp : 1 ≤ p) (N_0 : ℕ) :
    ∃ n ≥ N_0, pdEncodedParity (n + p) ≠ pdEncodedParity n := by
  by_contra hno
  have hper : ∀ n ≥ N_0, pdEncodedParity (n + p) = pdEncodedParity n := by
    intro n hn
    by_contra hne
    exact hno ⟨n, hn, hne⟩
  obtain ⟨m, hm, hne⟩ := pdBit_not_eventually_periodic hp N_0
  apply hne
  have h1 := hper (3 * m) (by omega)
  have h2 := hper (3 * m + p) (by omega)
  have h3 := hper (3 * m + 2 * p) (by omega)
  have hm1 : pdEncodedParity (3 * m) = pdBit m := by
    unfold pdEncodedParity
    have hmod : (3 * m) % 3 = 0 := by omega
    have hdiv : (3 * m) / 3 = m := by omega
    simp [hmod, hdiv]
  have hm2 : pdEncodedParity (3 * (m + p)) = pdBit (m + p) := by
    unfold pdEncodedParity
    have hmod : (3 * (m + p)) % 3 = 0 := by omega
    have hdiv : (3 * (m + p)) / 3 = m + p := by omega
    simp [hmod, hdiv]
  have hidx1 : 3 * m + 2 * p + p = 3 * (m + p) := by omega
  have hidx2 : 3 * m + p + p = 3 * m + 2 * p := by omega
  rw [hidx1, hm2] at h3
  rw [hidx2] at h2
  rw [hm1] at h1
  omega

/-- Quantitative dyadic lower bound `2^(2^k) ≤ seedResidue pdEncodedParity (21 * 2^k)`
for the Period-Doubling encoded parity stream. -/
theorem seedResidue_pdEncodedParity_ge_two_pow (k : ℕ) :
    2 ^ (2 ^ k) ≤ seedResidue pdEncodedParity (21 * 2 ^ k) := by
  set R := 2 ^ k
  have hR : 1 ≤ R := Nat.pow_pos (by decide)
  have hpos : 0 < seedResidue pdEncodedParity (21 * R) := by
    by_contra hle
    have hzero : seedResidue pdEncodedParity (21 * R) = 0 := by omega
    have h3 := orbit_seedResidue_mod_two pdEncodedParity (21 * R) 3 (by omega)
    have horb0 : orbit 0 3 = 0 := zero_seed_all_zero_exception.1 3
    have hpd3 : pdEncodedParity 3 = 1 := by
      unfold pdEncodedParity
      have h0 : pdBit 0 = 0 := by simpa using pdBit_two_mul 0
      have h1 : pdBit 1 = 1 := by simpa [h0] using pdBit_two_mul_add_one 0
      simpa using h1
    rw [hzero, horb0, hpd3] at h3
    omega
  by_contra hlt
  have hlt' : seedResidue pdEncodedParity (21 * R) < 2 ^ R := by omega
  apply pdEncodedParity_cutoff_and_exclusion.1 (W := R) (k := k) hpos hlt' le_rfl
  intro n hn
  have hmod := orbit_seedResidue_mod_two pdEncodedParity (21 * R) n hn
  rwa [pdEncodedParity_mod_two] at hmod

end Mahler.ThueMorseMahler
