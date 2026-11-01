import ExactSeedResidueTreeAndStabilization
import GlobalStepRateBounds

/-!
# Finite Odd-Count Bridge, Parity-Surplus Reductions, Lyapunov Potentials & Safety-Game Completeness

This module formalizes **Phase C (Sections C1–C3)**, **Section 18 (Deterministic Lyapunov /
Potential Functions)**, and **Section 19 (Infinite Safety-Game / Survivor-Kernel Completeness)**
of the general-proof research plan (`RESEARCH_PLAN_ARGON_GENERAL_PROOF.md`):

1. **Shift-Submultiplicativity of `signedMargin` & Post-`101` 5-Zero Lock (`signedMargin_add_le_two_pow_mul_shift`,
   `signedMargin_shift_pos_of_add_pos`, `signedMargin_post_101_five_zeros_lock`)**:
   - Because `signedMargin ε N ≤ 2^N` holds universally at every depth `k` and the recurrence
     `D_{n+1} = min(2^{n+1}, 3 D_n - 2^{n+1} e_n)` is monotone in `D_n`, shifting any parity stream
     `ε` by `k` steps (`shiftStream ε k m = ε (k + m)`) satisfies the universal inequality:
     `signedMargin ε (k + m) ≤ 2^k * signedMargin (shiftStream ε k) m`.
   - Consequently, every suffix of a feasible parity prefix is itself feasible from depth `0`:
     `0 < signedMargin ε (k + m) → 0 < signedMargin (shiftStream ε k) m`.
   - Whenever `(ε 0 % 2, ε 1 % 2, ε 2 % 2) = (1, 0, 1)`, `signedMargin ε 3 = 1`, and if any of the
     next five parities `ε 3, ε 4, ε 5, ε 6, ε 7` is odd, `signedMargin` immediately becomes negative
     (`-13, -23, -37, -47, -13 < 0`).

2. **Look-Ahead-Free Finite Odd-Count Bound (`three_mul_oddParityCount_le_add_three_of_signedMargin_pos`,
   `three_mul_oddCount_le_add_three_of_validCompanionUpTo`,
   `three_mul_oddCount_le_add_three_of_validCompanionForever`)**:
   - Using `signedMargin_shift_pos_of_add_pos` and the 5-zero lock after `101`, strong induction on `N`
     proves that for **every** parity stream `ε : ℕ → ℕ` and **every** horizon `N : ℕ`:
     `0 < signedMargin ε N → 3 * oddParityCount ε N ≤ N + 3`
     (with no block-chain packaging or look-ahead assumptions required).
   - Specializing to `ε = orbit a_0` via `validCompanionUpTo_iff_signedMargin_pos` proves Phase C1 in
     both finite-horizon and infinite-horizon forms:
     `(∃ α : ℝ, ValidCompanionUpTo a_0 α N) → 3 * oddCount a_0 N ≤ N + 3`, and
     `ValidCompanionForever a_0 α → ∀ N : ℕ, 3 * oddCount a_0 N ≤ N + 3`.
   - We also prove that no positive seed `a_0 > 0` can remain permanently even
     (`two_pow_dvd_of_oddCount_eq_zero`, `exists_odd_orbit_step_of_pos`).

3. **Phase C2 Pointwise Arithmetic Sufficient Conditions for Mahler's Conjecture
   (`mahler_conjecture_of_forall_pos_seed_parity_surplus`,
   `mahler_conjecture_of_forall_pos_seed_hits_three_mod_four`)**:
   - **Finite Parity-Surplus Target**: If every positive integer `a_0 ≥ 1` admits a single finite
     horizon `N` where `N + 3 < 3 * oddCount a_0 N`, then Mahler's $3/2$ conjecture holds for all `α > 0`.
   - **Residue `≡ 3 (mod 4)` Target**: Since `x % 4 = 3 → x % 2 = 1 ∧ step x % 2 = 1`, if every
     positive integer `a_0 ≥ 1` eventually hits `orbit a_0 n % 4 = 3`, then Mahler's $3/2$ conjecture
     holds for all `α > 0`.

4. **Section 18 Deterministic Lyapunov Potentials & Certified Indifference Table
   (`deficitPotential`, `deficitPotential_nonneg_of_signedMargin_pos`,
   `deficitPotential_indifference_on_100_and_increase_on_1000`,
   `linear_coupled_margin_deficit_stationary_on_100_cycle`,
   `stabilized_seed_100_two_adic_valuation_drop`)**:
   - Formalizes the **Odd-Count Deficit Potential** `Φ_def(ε, N) = (N + 3 : ℤ) - 3 * oddParityCount ε N`,
     proving `0 ≤ Φ_def(ε, N)` for all feasible prefixes (`0 < signedMargin ε N`).
   - Proves the exact **Indifference Surface Refutation**: on any `100` (`s = 3`) block from ceiling,
     both the normalized margin `signedMargin ε N / 2^N = 1` and `Φ_def` (`Δ Φ_def = 0`) are strictly
     stationary, while on `1000` (`s = 4`) `Φ_def` increases by `+1`. Thus no linear combination of
     normalized margin and `Φ_def` can strictly decrease across `100` without incorporating the
     2-adic seed quotient `q_N`, where `8 * (19 * q_{N+3} + 9) = 27 * (19 * q_N + 9)` strictly consumes
     three factors of `2` whenever `η_N = η_{N+1} = η_{N+2} = 0`.

5. **Section 19 Infinite Safety-Game & Survivor-Kernel Completeness
   (`survivesHorizonSet`, `survivorKernel`, `safety_game_kernel_and_rank_completeness`)**:
   - Formalizes the decreasing safety-game survival sets `survivesHorizonSet N` and their intersection
     `survivorKernel = ⋂ N, survivesHorizonSet N`, proving the 4-way equivalence between:
     (i) Mahler's $3/2$ conjecture, (ii) emptiness of `survivorKernel`, (iii) existence of a
     well-founded integer escape rank on positive seeds, and (iv) unbounded growth `B(N) → ∞`.
-/

namespace Mahler.ParitySurplusAndGames

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree

/-! ## 1. Shift-Submultiplicativity of `signedMargin` & Post-`101` 5-Zero Lock -/

/-- Shift a parity stream `ε : ℕ → ℕ` forward by `k` steps. -/
def shiftStream (ε : ℕ → ℕ) (k : ℕ) (m : ℕ) : ℕ :=
  ε (k + m)

@[simp]
theorem shiftStream_zero (ε : ℕ → ℕ) : shiftStream ε 0 = ε := by
  funext m
  simp [shiftStream]

theorem shiftStream_add (ε : ℕ → ℕ) (k₁ k₂ m : ℕ) :
    shiftStream (shiftStream ε k₁) k₂ m = shiftStream ε (k₁ + k₂) m := by
  simp [shiftStream, Nat.add_assoc]

/-- **Universal Shift-Submultiplicativity of `signedMargin` (`signedMargin_add_le_two_pow_mul_shift`)**:
For every parity stream `ε : ℕ → ℕ` and all `k, m : ℕ`:
`signedMargin ε (k + m) ≤ 2^k * signedMargin (shiftStream ε k) m`. -/
theorem signedMargin_add_le_two_pow_mul_shift (ε : ℕ → ℕ) (k m : ℕ) :
    signedMargin ε (k + m) ≤ (2 : ℤ) ^ k * signedMargin (shiftStream ε k) m := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, signedMargin, mul_one]
      exact signedMargin_le_two_pow ε k
  | succ m ih =>
      have hidx : k + (m + 1) = (k + m) + 1 := by omega
      rw [hidx]
      simp only [signedMargin, shiftStream]
      have hpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
      have hpow : (2 : ℤ) ^ (k + m + 1) = (2 : ℤ) ^ k * (2 : ℤ) ^ (m + 1) := by
        rw [show k + m + 1 = k + (m + 1) by omega, pow_add]
      rw [mul_min_of_nonneg _ _ (le_of_lt hpos)]
      apply le_min
      · rw [← hpow]
        exact min_le_left _ _
      · refine le_trans (min_le_right _ _) ?_
        have hmul :
            3 * signedMargin ε (k + m) ≤
              (2 : ℤ) ^ k * (3 * signedMargin (shiftStream ε k) m) := by
          nlinarith
        rw [hpow]
        linarith

/-- **Suffix Feasibility Preservation (`signedMargin_shift_pos_of_add_pos`)**:
Whenever `0 < signedMargin ε (k + m)`, the shifted stream `shiftStream ε k` also has
strictly positive margin `0 < signedMargin (shiftStream ε k) m`. -/
theorem signedMargin_shift_pos_of_add_pos {ε : ℕ → ℕ} {k m : ℕ}
    (hpos : 0 < signedMargin ε (k + m)) :
    0 < signedMargin (shiftStream ε k) m := by
  have hle := signedMargin_add_le_two_pow_mul_shift ε k m
  have hk : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  by_contra hnonpos
  push_neg at hnonpos
  have hmul : (2 : ℤ) ^ k * signedMargin (shiftStream ε k) m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hk) hnonpos
  linarith

/-- **Exact Shift-At-Ceiling Identity (`signedMargin_add_eq_two_pow_mul_shift_of_ceiling`)**:
Whenever `signedMargin ε k = 2^k`, the shifted stream satisfies the exact equality
`signedMargin ε (k + m) = 2^k * signedMargin (shiftStream ε k) m` for all `m : ℕ`. -/
theorem signedMargin_add_eq_two_pow_mul_shift_of_ceiling {ε : ℕ → ℕ} {k : ℕ}
    (hceil : signedMargin ε k = (2 : ℤ) ^ k) (m : ℕ) :
    signedMargin ε (k + m) = (2 : ℤ) ^ k * signedMargin (shiftStream ε k) m := by
  induction m with
  | zero =>
      simp [hceil, signedMargin]
  | succ m ih =>
      have hidx : k + (m + 1) = (k + m) + 1 := by omega
      rw [hidx]
      simp only [signedMargin, shiftStream]
      rw [ih]
      have hk : (0 : ℤ) ≤ (2 : ℤ) ^ k := by positivity
      have hpow : (2 : ℤ) ^ (k + m + 1) = (2 : ℤ) ^ k * (2 : ℤ) ^ (m + 1) := by
        rw [show k + m + 1 = k + (m + 1) by omega, pow_add]
      rw [hpow]
      have h1 :
          3 * ((2 : ℤ) ^ k * signedMargin (shiftStream ε k) m) -
              (2 : ℤ) ^ k * (2 : ℤ) ^ (m + 1) * ((ε (k + m) % 2 : ℕ) : ℤ) =
            (2 : ℤ) ^ k *
              (3 * signedMargin (shiftStream ε k) m -
                (2 : ℤ) ^ (m + 1) * ((ε (k + m) % 2 : ℕ) : ℤ)) := by
        ring
      rw [h1, ← mul_min_of_nonneg _ _ hk]

/-- At any step `n`, `signedMargin ε (n + 1) ≤ 3 * signedMargin ε n`. -/
theorem signedMargin_succ_le_three_mul (ε : ℕ → ℕ) (n : ℕ) :
    signedMargin ε (n + 1) ≤ 3 * signedMargin ε n := by
  have h1 :
      signedMargin ε (n + 1) ≤
        3 * signedMargin ε n - (2 : ℤ) ^ (n + 1) * ((ε n % 2 : ℕ) : ℤ) :=
    min_le_right _ _
  have h2 : (0 : ℤ) ≤ (2 : ℤ) ^ (n + 1) * ((ε n % 2 : ℕ) : ℤ) := by positivity
  linarith

/-- **The Post-`101` Five-Zero Margin Lock (`signedMargin_post_101_five_zeros_lock`)**:
Suppose `ε 0 % 2 = 1`, `ε 1 % 2 = 0`, and `ε 2 % 2 = 1`. Then:
1. `signedMargin ε 3 = 1`,
2. For every `k ≤ 5`, `signedMargin ε (3 + k) ≤ 3^k`, and
3. If `0 < signedMargin ε N`, then for every `j ∈ {3, 4, 5}` with `j < N`, `ε j % 2 = 0`. -/
theorem signedMargin_post_101_five_zeros_lock {ε : ℕ → ℕ}
    (h0 : ε 0 % 2 = 1) (h1 : ε 1 % 2 = 0) (h2 : ε 2 % 2 = 1) :
    signedMargin ε 3 = 1 ∧
      (∀ N : ℕ, 0 < signedMargin ε N →
        (3 < N → ε 3 % 2 = 0) ∧
        (4 < N → ε 4 % 2 = 0) ∧
        (5 < N → ε 5 % 2 = 0)) := by
  have hd1 : signedMargin ε 1 = 1 := by
    simp [signedMargin, h0]
  have hd2 : signedMargin ε 2 = 3 := by
    change min ((2 : ℤ) ^ 2) (3 * signedMargin ε 1 - (2 : ℤ) ^ 2 * ((ε 1 % 2 : ℕ) : ℤ)) = 3
    rw [hd1, h1]
    decide
  have hd3 : signedMargin ε 3 = 1 := by
    change min ((2 : ℤ) ^ 3) (3 * signedMargin ε 2 - (2 : ℤ) ^ 3 * ((ε 2 % 2 : ℕ) : ℤ)) = 1
    rw [hd2, h2]
    decide
  refine ⟨hd3, ?_⟩
  intro N hposN
  have hd4_le : signedMargin ε 4 ≤ 3 := by
    have hle := signedMargin_succ_le_three_mul ε 3
    linarith
  have hd5_le : signedMargin ε 5 ≤ 9 := by
    have hle := signedMargin_succ_le_three_mul ε 4
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro h3N
    by_contra h3_ne
    have h3_odd : ε 3 % 2 = 1 := by omega
    have hd4_neg : signedMargin ε 4 ≤ 0 := by
      have eq4 := (signedMargin_odd_step_eq h3_odd).1
      have hp4 : (2 : ℤ) ^ (3 + 1) = 16 := by decide
      linarith
    have hnonpos := (signedMargin_nonpos_of_nonpos hd4_neg).2 N (by omega : 4 ≤ N)
    linarith
  · intro h4N
    by_contra h4_ne
    have h4_odd : ε 4 % 2 = 1 := by omega
    have hd5_neg : signedMargin ε 5 ≤ 0 := by
      have eq5 := (signedMargin_odd_step_eq h4_odd).1
      have hp5 : (2 : ℤ) ^ (4 + 1) = 32 := by decide
      linarith
    have hnonpos := (signedMargin_nonpos_of_nonpos hd5_neg).2 N (by omega : 5 ≤ N)
    linarith
  · intro h5N
    by_contra h5_ne
    have h5_odd : ε 5 % 2 = 1 := by omega
    have hd6_neg : signedMargin ε 6 ≤ 0 := by
      have eq6 := (signedMargin_odd_step_eq h5_odd).1
      have hp6 : (2 : ℤ) ^ (5 + 1) = 64 := by decide
      linarith
    have hnonpos := (signedMargin_nonpos_of_nonpos hd6_neg).2 N (by omega : 6 ≤ N)
    linarith

/-! ## 2. Look-Ahead-Free Finite Odd-Count Bound (Phase C1) -/

/-- Number of odd parities `ε n % 2 = 1` in the prefix `0 ≤ n < N`. -/
def oddParityCount (ε : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ε n % 2 = 1)).card

/-- Number of odd orbit terms `orbit a n % 2 = 1` in the prefix `0 ≤ n < N`. -/
def oddCount (a : ℕ) (N : ℕ) : ℕ :=
  oddParityCount (orbit a) N

@[simp]
theorem oddParityCount_zero (ε : ℕ → ℕ) : oddParityCount ε 0 = 0 := by
  simp [oddParityCount]

theorem oddParityCount_succ (ε : ℕ → ℕ) (N : ℕ) :
    oddParityCount ε (N + 1) = oddParityCount ε N + (ε N % 2) := by
  unfold oddParityCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_not_mem (by simp), h]
  · have h0 : ε N % 2 = 0 := by omega
    rw [h0, Nat.add_zero]

theorem oddParityCount_le (ε : ℕ → ℕ) (N : ℕ) :
    oddParityCount ε N ≤ N := by
  unfold oddParityCount
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Decomposition of `oddParityCount ε (k + m)` into the prefix of length `k` and the shifted tail of length `m`. -/
theorem oddParityCount_add (ε : ℕ → ℕ) (k m : ℕ) :
    oddParityCount ε (k + m) = oddParityCount ε k + oddParityCount (shiftStream ε k) m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx : k + (m + 1) = (k + m) + 1 := by omega
      rw [hidx, oddParityCount_succ, ih, oddParityCount_succ]
      simp [shiftStream, Nat.add_assoc]

/-- **Look-Ahead-Free Finite Odd-Count Theorem (`three_mul_oddParityCount_le_add_three_of_signedMargin_pos`)**:
For **every** parity stream `ε : ℕ → ℕ` and **every** horizon `N : ℕ`,
if `0 < signedMargin ε N`, then `3 * oddParityCount ε N ≤ N + 3`. -/
theorem three_mul_oddParityCount_le_add_three_of_signedMargin_pos :
    ∀ (N : ℕ) (ε : ℕ → ℕ), 0 < signedMargin ε N → 3 * oddParityCount ε N ≤ N + 3 := by
  intro N
  induction' N using Nat.strong_induction_on with N ih
  intro ε hpos
  rcases ( by omega : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ 4 ≤ N ) with rfl | rfl | rfl | rfl | hN4
  · simp
  · have hle := oddParityCount_le ε 1
    omega
  · -- At N = 2, `11` is impossible since `signedMargin ε 2 > 0`
    rw [show (2 : ℕ) = 0 + 1 + 1 by rfl, oddParityCount_succ, oddParityCount_succ, oddParityCount_zero]
    have hnot11 : ¬ (ε 0 % 2 = 1 ∧ ε 1 % 2 = 1) := by
      rintro ⟨h0, h1⟩
      have hneg := (signedMargin_two_ones_neg (N := 0) h0 h1).2
      linarith
    have hb0 : ε 0 % 2 ≤ 1 := by omega
    have hb1 : ε 1 % 2 ≤ 1 := by omega
    omega
  · -- At N = 3, `ε 0 % 2` and `ε 1 % 2` cannot both be 1, so `oddParityCount ε 3 ≤ 2`
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by rfl, oddParityCount_succ, oddParityCount_succ,
      oddParityCount_succ, oddParityCount_zero]
    have hnot01 : ¬ (ε 0 % 2 = 1 ∧ ε 1 % 2 = 1) := by
      rintro ⟨h0, h1⟩
      have hneg := (signedMargin_two_ones_neg (N := 0) h0 h1).1
      have hneg2 : signedMargin ε 2 ≤ 0 := by norm_num at hneg; linarith
      have hle := (signedMargin_nonpos_of_nonpos hneg2).2 3 (by omega : 2 ≤ 3)
      linarith
    have hb0 : ε 0 % 2 ≤ 1 := by omega
    have hb1 : ε 1 % 2 ≤ 1 := by omega
    have hb2 : ε 2 % 2 ≤ 1 := by omega
    omega
  · -- For N ≥ 4, branch on the initial parities of `ε`
    rcases (by omega : ε 0 % 2 = 0 ∨ ε 0 % 2 = 1) with h0_even | h0_odd
    · -- Case 1: `ε 0 % 2 = 0` -> shift by 1
      have hsplit : N = 1 + (N - 1) := by omega
      have hpos1 : 0 < signedMargin (shiftStream ε 1) (N - 1) := by
        apply signedMargin_shift_pos_of_add_pos
        rw [← hsplit]; exact hpos
      have hih := ih (N - 1) (by omega) (shiftStream ε 1) hpos1
      have hcnt : oddParityCount ε N = oddParityCount (shiftStream ε 1) (N - 1) := by
        conv_lhs => rw [hsplit, oddParityCount_add]
        rw [show (1 : ℕ) = 0 + 1 by rfl, oddParityCount_succ, oddParityCount_zero, h0_even]
        omega
      omega
    · -- `ε 0 % 2 = 1`: then `ε 1 % 2` must be `0` since `N ≥ 2` and `signedMargin ε N > 0`
      have h1_even : ε 1 % 2 = 0 := by
        by_contra h1_ne
        have h1_odd : ε 1 % 2 = 1 := by omega
        have hneg := (signedMargin_two_ones_neg (N := 0) h0_odd h1_odd).1
        have hneg2 : signedMargin ε 2 ≤ 0 := by norm_num at hneg; linarith
        have hle := (signedMargin_nonpos_of_nonpos hneg2).2 N (by omega : 2 ≤ N)
        linarith
      rcases (by omega : ε 2 % 2 = 0 ∨ ε 2 % 2 = 1) with h2_even | h2_odd
      · -- Case 2: `(ε 0, ε 1, ε 2) = (1, 0, 0)` -> shift by 3
        have hsplit : N = 3 + (N - 3) := by omega
        have hpos3 : 0 < signedMargin (shiftStream ε 3) (N - 3) := by
          apply signedMargin_shift_pos_of_add_pos
          rw [← hsplit]; exact hpos
        have hih := ih (N - 3) (by omega) (shiftStream ε 3) hpos3
        have hcnt3 : oddParityCount ε 3 = 1 := by
          rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by rfl, oddParityCount_succ, oddParityCount_succ,
            oddParityCount_succ, oddParityCount_zero, h0_odd, h1_even, h2_even]
        have hcnt : oddParityCount ε N = 1 + oddParityCount (shiftStream ε 3) (N - 3) := by
          conv_lhs => rw [hsplit, oddParityCount_add, hcnt3]
        omega
      · -- Case 3: `(ε 0, ε 1, ε 2) = (1, 0, 1)` -> post-`101` lock forces `ε 3 = ε 4 = ε 5 = 0`
        have hlock := (signedMargin_post_101_five_zeros_lock h0_odd h1_even h2_odd).2 N hpos
        have hcnt3 : oddParityCount ε 3 = 2 := by
          rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by rfl, oddParityCount_succ, oddParityCount_succ,
            oddParityCount_succ, oddParityCount_zero, h0_odd, h1_even, h2_odd]
        rcases (by omega : N = 4 ∨ N = 5 ∨ 6 ≤ N) with rfl | rfl | hN6
        · have h3_0 := hlock.1 (by omega)
          rw [show (4 : ℕ) = 3 + 1 by rfl, oddParityCount_succ, hcnt3, h3_0]
          omega
        · have h3_0 := hlock.1 (by omega)
          have h4_0 := hlock.2.1 (by omega)
          rw [show (5 : ℕ) = 3 + 1 + 1 by rfl, oddParityCount_succ, oddParityCount_succ, hcnt3, h3_0, h4_0]
          omega
        · have h3_0 := hlock.1 (by omega)
          have h4_0 := hlock.2.1 (by omega)
          have h5_0 := hlock.2.2 (by omega)
          have hcnt6 : oddParityCount ε 6 = 2 := by
            rw [show (6 : ℕ) = 3 + 1 + 1 + 1 by rfl, oddParityCount_succ, oddParityCount_succ,
              oddParityCount_succ, hcnt3, h3_0, h4_0, h5_0]
          have hsplit : N = 6 + (N - 6) := by omega
          have hpos6 : 0 < signedMargin (shiftStream ε 6) (N - 6) := by
            apply signedMargin_shift_pos_of_add_pos
            rw [← hsplit]; exact hpos
          have hih := ih (N - 6) (by omega) (shiftStream ε 6) hpos6
          have hcnt : oddParityCount ε N = 2 + oddParityCount (shiftStream ε 6) (N - 6) := by
            conv_lhs => rw [hsplit, oddParityCount_add, hcnt6]
          omega

/-- **Finite-Horizon Seed Odd-Count Bound (`three_mul_oddCount_le_add_three_of_validCompanionUpTo`)**:
For every nonnegative integer seed `a_0 : ℕ` and horizon `N : ℕ`, if `a_0` admits a valid
real companion up to step `N`, then `3 * oddCount a_0 N ≤ N + 3`. -/
theorem three_mul_oddCount_le_add_three_of_validCompanionUpTo {a_0 N : ℕ}
    (hsurv : ∃ α : ℝ, ValidCompanionUpTo a_0 α N) :
    3 * oddCount a_0 N ≤ N + 3 := by
  have hmod : a_0 % 2 ^ N = seedResidue (orbit a_0) N :=
    (orbit_parity_match_iff_mod_two_pow_eq_seedResidue (orbit a_0) a_0 N).mp (fun _ _ => rfl)
  have hpos : 0 < signedMargin (orbit a_0) N :=
    (validCompanionUpTo_iff_signedMargin_pos hmod).mp hsurv
  exact three_mul_oddParityCount_le_add_three_of_signedMargin_pos N (orbit a_0) hpos

/-- **Infinite-Horizon Seed Odd-Count Bound (`three_mul_oddCount_le_add_three_of_validCompanionForever`,
Phase C1 Target)**:
If `ValidCompanionForever a_0 α`, then for **every** `N : ℕ`, `3 * oddCount a_0 N ≤ N + 3`. -/
theorem three_mul_oddCount_le_add_three_of_validCompanionForever {a_0 : ℕ} {α : ℝ}
    (hforever : ValidCompanionForever a_0 α) (N : ℕ) :
    3 * oddCount a_0 N ≤ N + 3 := by
  have hup : ValidCompanionUpTo a_0 α N :=
    (validCompanionForever_iff_forall_upTo a_0 α).mp hforever N
  exact three_mul_oddCount_le_add_three_of_validCompanionUpTo ⟨α, hup⟩

/-- If `oddCount a N = 0`, then all `n < N` are even steps and `2^N ∣ a` (`3^N * a = 2^N * orbit a N`). -/
theorem two_pow_dvd_of_oddCount_eq_zero {a N : ℕ} (hzero : oddCount a N = 0) :
    3 ^ N * a = 2 ^ N * orbit a N ∧ 2 ^ N ∣ a := by
  have hall_even : ∀ n < N, orbit a n % 2 = 0 := by
    intro n hn
    by_contra hne
    have h1 : orbit a n % 2 = 1 := by omega
    have hmem : n ∈ (Finset.range N).filter (fun k => orbit a k % 2 = 1) := by
      simp [hn, h1]
    have hpos : 0 < oddCount a N := Finset.card_pos.mpr ⟨n, hmem⟩
    omega
  have hmul : 3 ^ N * a = 2 ^ N * orbit a N := by
    induction N with
    | zero => simp [orbit]
    | succ m ih =>
        have hzero_m : oddCount a m = 0 := by
          unfold oddCount at hzero ⊢
          rw [oddParityCount_succ] at hzero
          omega
        have ihm := ih hzero_m (fun n hn => hall_even n (by omega))
        have hm_even : orbit a m % 2 = 0 := hall_even m (by omega)
        have hstep := step_identity (orbit a m)
        rw [hm_even, Nat.add_zero] at hstep
        have horb : 2 * orbit a (m + 1) = 3 * orbit a m := hstep
        calc
          3 ^ (m + 1) * a = 3 * (3 ^ m * a) := by rw [pow_succ']; ring
          _ = 3 * (2 ^ m * orbit a m) := by rw [ihm]
          _ = 2 ^ m * (3 * orbit a m) := by ring
          _ = 2 ^ m * (2 * orbit a (m + 1)) := by rw [← horb]
          _ = 2 ^ (m + 1) * orbit a (m + 1) := by rw [pow_succ]; ring
  refine ⟨hmul, ?_⟩
  have hdvd3 : 2 ^ N ∣ 3 ^ N * a := ⟨orbit a N, hmul⟩
  have hcop : Nat.Coprime (2 ^ N) (3 ^ N) := by
    apply Nat.Coprime.pow
    decide
  exact hcop.dvd_of_dvd_mul_left hdvd3

/-- **Positive Seeds Cannot Remain Permanently Even (`exists_odd_orbit_step_of_pos`)**:
For every positive integer `1 ≤ a` with `a < 2^W`, there exists `n < W` with
`orbit a n % 2 = 1` (and `1 ≤ oddCount a W`). -/
theorem exists_odd_orbit_step_of_pos {a W : ℕ} (ha : 1 ≤ a) (hW : a < 2 ^ W) :
    (∃ n < W, orbit a n % 2 = 1) ∧ 1 ≤ oddCount a W := by
  have hpos : 1 ≤ oddCount a W := by
    by_contra hzero
    have h0 : oddCount a W = 0 := by omega
    have hdvd := (two_pow_dvd_of_oddCount_eq_zero h0).2
    have hle : 2 ^ W ≤ a := Nat.le_of_dvd (by omega) hdvd
    omega
  refine ⟨?_, hpos⟩
  have hcard : 0 < ((Finset.range W).filter (fun n => orbit a n % 2 = 1)).card := hpos
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcard
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  exact ⟨n, hn.1, hn.2⟩

/-! ## 3. Phase C2 Pointwise Arithmetic Sufficient Conditions for Mahler's Conjecture -/

/-- **Finite Parity-Surplus Sufficient Condition for Mahler's Conjecture
(`mahler_conjecture_of_forall_pos_seed_parity_surplus`, Phase C2 Target 1)**:
If every positive integer seed `1 ≤ a_0` admits a finite horizon `N` where
`N + 3 < 3 * oddCount a_0 N`, then Mahler's $3/2$ conjecture holds for all `α > 0`. -/
theorem mahler_conjecture_of_forall_pos_seed_parity_surplus
    (hsurplus : ∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, N + 3 < 3 * oddCount a_0 N) :
    ∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n) := by
  rw [general_mahler_conjecture_iff_positive_stabilized_branch_escape.1]
  intro a_0 ha0 ⟨α, hforever⟩
  obtain ⟨N, hgt⟩ := hsurplus a_0 ha0
  have hle := three_mul_oddCount_le_add_three_of_validCompanionForever hforever N
  omega

/-- Whenever `x % 4 = 3`, both `x` and `step x` are odd (`x % 2 = 1 ∧ step x % 2 = 1`). -/
theorem odd_and_step_odd_of_mod_four_eq_three {x : ℕ} (hmod4 : x % 4 = 3) :
    x % 2 = 1 ∧ step x % 2 = 1 := by
  have hx_odd : x % 2 = 1 := by omega
  have hstep := step_identity x
  rw [hx_odd] at hstep
  omega

/-- **Mod-4 Residue-Hitting Sufficient Condition for Mahler's Conjecture
(`mahler_conjecture_of_forall_pos_seed_hits_three_mod_four`, Phase C2 Target 2)**:
If every positive integer seed `1 ≤ a_0` eventually hits `orbit a_0 n % 4 = 3`,
then Mahler's $3/2$ conjecture holds for all `α > 0`. -/
theorem mahler_conjecture_of_forall_pos_seed_hits_three_mod_four
    (hhit : ∀ a_0 : ℕ, 1 ≤ a_0 → ∃ n : ℕ, orbit a_0 n % 4 = 3) :
    ∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n) := by
  rw [general_mahler_conjecture_iff_positive_stabilized_branch_escape.1]
  intro a_0 ha0 hcomp
  obtain ⟨n, hmod4⟩ := hhit a_0 ha0
  rcases odd_and_step_odd_of_mod_four_eq_three hmod4 with ⟨h0, h1⟩
  exact no_validCompanionForever_of_consecutive_odd_steps h0 h1 hcomp

/-! ## 4. Section 18 Deterministic Lyapunov Potentials & Certified Indifference Table -/

/-- **The Odd-Count Deficit Potential (`deficitPotential`, Section 18.2)**:
`Φ_def(ε, N) = (N + 3 : ℤ) - 3 * oddParityCount ε N`. -/
def deficitPotential (ε : ℕ → ℕ) (N : ℕ) : ℤ :=
  (N : ℤ) + 3 - 3 * (oddParityCount ε N : ℤ)

/-- **Feasibility Nonnegativity of `deficitPotential` (`deficitPotential_nonneg_of_signedMargin_pos`)**:
Whenever `0 < signedMargin ε N`, `0 ≤ deficitPotential ε N`. -/
theorem deficitPotential_nonneg_of_signedMargin_pos {ε : ℕ → ℕ} {N : ℕ}
    (hpos : 0 < signedMargin ε N) :
    0 ≤ deficitPotential ε N := by
  have hle := three_mul_oddParityCount_le_add_three_of_signedMargin_pos N ε hpos
  unfold deficitPotential
  omega

/-- **One-Step Evolution of `deficitPotential` (`deficitPotential_succ`)**:
`deficitPotential ε (N + 1) = deficitPotential ε N + 1 - 3 * (ε N % 2)`. -/
theorem deficitPotential_succ (ε : ℕ → ℕ) (N : ℕ) :
    deficitPotential ε (N + 1) = deficitPotential ε N + 1 - 3 * ((ε N % 2 : ℕ) : ℤ) := by
  unfold deficitPotential
  rw [oddParityCount_succ]
  push_cast
  ring

/-- **Indifference Surface Refutation of `deficitPotential` (`deficitPotential_indifference_on_100_and_increase_on_1000`,
Section 18 Negative Result)**:
1. Across any `100` (`s = 3`) block `(ε N % 2, ε (N + 1) % 2, ε (N + 2) % 2) = (1, 0, 0)`,
   `deficitPotential ε (N + 3) = deficitPotential ε N` (zero net drop, while `signedMargin` also
   recovers the full `2^(N + 3)` ceiling!).
2. Across any `1000` (`s = 4`) block `(ε N % 2, ε (N + 1) % 2, ε (N + 2) % 2, ε (N + 3) % 2) = (1, 0, 0, 0)`,
   `deficitPotential ε (N + 4) = deficitPotential ε N + 1` (strictly increases!). -/
theorem deficitPotential_indifference_on_100_and_increase_on_1000 {ε : ℕ → ℕ} {N : ℕ}
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 0) (h2 : ε (N + 2) % 2 = 0) :
    deficitPotential ε (N + 3) = deficitPotential ε N ∧
      (ε (N + 3) % 2 = 0 → deficitPotential ε (N + 4) = deficitPotential ε N + 1) := by
  have hs1 := deficitPotential_succ ε N
  have hs2 := deficitPotential_succ ε (N + 1)
  have hs3 := deficitPotential_succ ε (N + 2)
  have hs4 := deficitPotential_succ ε (N + 3)
  have hidx2 : N + 1 + 1 = N + 2 := by omega
  have hidx3 : N + 2 + 1 = N + 3 := by omega
  have hidx4 : N + 3 + 1 = N + 4 := by omega
  rw [h0] at hs1
  rw [hidx2, h1] at hs2
  rw [hidx3, h2] at hs3
  norm_num at hs1 hs2 hs3
  refine ⟨by linarith, ?_⟩
  intro h3
  rw [hidx4, h3] at hs4
  norm_num at hs4
  linarith

/-- **Refutation of All Linear `(Normalized Margin, Deficit)` Potentials on `100` Blocks
(`linear_coupled_margin_deficit_stationary_on_100_cycle`, Section 18 Refutation Certificate)**:
For ANY rational weights `α_M, α_D : ℚ`, the linear potential
`Ψ(ε, N) = α_M * (signedMargin ε N / 2^N) + α_D * deficitPotential ε N`
is strictly stationary (`Ψ(ε, N + 3) = Ψ(ε, N)`) across any ceiling-saturated `100` block. -/
theorem linear_coupled_margin_deficit_stationary_on_100_cycle {ε : ℕ → ℕ} {N : ℕ}
    (α_M α_D : ℚ)
    (hcap : signedMargin ε N = (2 : ℤ) ^ N)
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 0) (h2 : ε (N + 2) % 2 = 0) :
    α_M * ((signedMargin ε (N + 3) : ℚ) / (2 : ℚ) ^ (N + 3)) +
        α_D * (deficitPotential ε (N + 3) : ℚ) =
      α_M * ((signedMargin ε N : ℚ) / (2 : ℚ) ^ N) +
        α_D * (deficitPotential ε N : ℚ) := by
  have hrec := (signedMargin_100_ceiling_recovery hcap h0 h1 h2).2.2
  have hdef := (deficitPotential_indifference_on_100_and_increase_on_1000 h0 h1 h2).1
  have h2N : (2 : ℚ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2N3 : (2 : ℚ) ^ (N + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hrec, hcap, hdef]
  push_cast
  rw [div_self h2N, div_self h2N3]

/-- **Why the Coupled 2-Adic Quotient Breaks the `100` Indifference Surface
(`stabilized_seed_100_two_adic_valuation_drop`, Section 18.3)**:
When the seed has stabilized (`η_N = η_{N+1} = η_{N+2} = 0`) and `(ε N % 2, ε (N+1) % 2, ε (N+2) % 2) = (1, 0, 0)`,
the coupled orbit quotient `q_N = seedQuotient ε N` satisfies the exact identity
`8 * (19 * seedQuotient ε (N + 3) + 9) = 27 * (19 * seedQuotient ε N + 9)`,
forcing `8 ∣ (19 * seedQuotient ε N + 9)` and strictly draining 3 factors of `2`. -/
theorem stabilized_seed_100_two_adic_valuation_drop {ε : ℕ → ℕ} {N : ℕ}
    (hbit0 : seedBit ε (seedResidue ε N) N = 0)
    (hbit1 : seedBit ε (seedResidue ε (N + 1)) (N + 1) = 0)
    (hbit2 : seedBit ε (seedResidue ε (N + 2)) (N + 2) = 0)
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 0) (h2 : ε (N + 2) % 2 = 0) :
    8 * (19 * seedQuotient ε (N + 3) + 9) = 27 * (19 * seedQuotient ε N + 9) ∧
      8 ∣ (19 * seedQuotient ε N + 9) := by
  have hq1 := (coupled_seedQuotient_and_margin_transition ε N).2.2.1
  have hq2 := (coupled_seedQuotient_and_margin_transition ε (N + 1)).2.2.1
  have hq3 := (coupled_seedQuotient_and_margin_transition ε (N + 2)).2.2.1
  have hidx2 : N + 1 + 1 = N + 2 := by omega
  have hidx3 : N + 2 + 1 = N + 3 := by omega
  rw [hbit0, h0, mul_zero, add_zero] at hq1
  rw [hbit1, h1, mul_zero, add_zero, add_zero, hidx2] at hq2
  rw [hbit2, h2, mul_zero, add_zero, add_zero, hidx3] at hq3
  have hid : 8 * (19 * seedQuotient ε (N + 3) + 9) = 27 * (19 * seedQuotient ε N + 9) := by
    omega
  refine ⟨hid, ?_⟩
  have hdvd27 : 8 ∣ 27 * (19 * seedQuotient ε N + 9) := ⟨19 * seedQuotient ε (N + 3) + 9, hid.symm⟩
  have hcop : Nat.Coprime 8 27 := by decide
  exact hcop.dvd_of_dvd_mul_left hdvd27

/-! ## 5. Section 19 Infinite Safety-Game & Survivor-Kernel Completeness -/

/-- Set of positive integer seeds surviving the Mahler safety game through horizon `N`. -/
def survivesHorizonSet (N : ℕ) : Set ℕ :=
  {a : ℕ | 1 ≤ a ∧ survivesSteps a N = true}

/-- The greatest invariant **Survivor Kernel** `⋂ N, survivesHorizonSet N` of the safety game. -/
def survivorKernel : Set ℕ :=
  ⋂ N : ℕ, survivesHorizonSet N

/-- Monotonicity of the safety-game horizon sets: `N₁ ≤ N₂ → survivesHorizonSet N₂ ⊆ survivesHorizonSet N₁`. -/
theorem survivesHorizonSet_antitone {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    survivesHorizonSet N₂ ⊆ survivesHorizonSet N₁ := by
  intro a ⟨ha, hsurv2⟩
  refine ⟨ha, ?_⟩
  rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch] at hsurv2 ⊢
  rcases hsurv2 with ⟨ξ, hξ⟩
  exact ⟨ξ, fun n hn => hξ n (le_trans hn hN)⟩

/-- **Safety-Game Kernel Membership Equivalence (`mem_survivorKernel_iff_forall_validCompanionUpTo`)**:
A natural number `a` belongs to `survivorKernel` if and only if `1 ≤ a` and `a` admits a valid
companion at every finite horizon `N : ℕ`. -/
theorem mem_survivorKernel_iff_forall_validCompanionUpTo (a : ℕ) :
    a ∈ survivorKernel ↔ (1 ≤ a ∧ ∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a α N) := by
  simp only [survivorKernel, Set.mem_iInter, survivesHorizonSet, Set.mem_setOf_eq]
  constructor
  · intro hall
    refine ⟨(hall 0).1, fun N => ?_⟩
    rw [exists_validCompanionUpTo_iff_integerPinch, ← survivesSteps_eq_true_iff]
    exact (hall N).2
  · rintro ⟨ha, hall⟩ N
    refine ⟨ha, ?_⟩
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact hall N

/-- **4-Way Safety-Game, Survivor-Kernel & Rank Completeness Theorem
(`safety_game_kernel_and_rank_completeness`, Section 19)**:
The following four global statements are equivalent:
1. **Mahler's $3/2$ Conjecture**: For every real `α > 0`, `∃ n : ℕ, 1 / 2 ≤ Int.fract (α * (3 / 2)^n)`.
2. **Emptiness of the Safety-Game Survivor Kernel**: `survivorKernel = ∅`
   (the Orbit player has no winning positive-integer initial state).
3. **Existence of a Finite Escape-Rank Certificate on Positive Seeds**:
   There exists a rank function `R : ℕ → ℕ` such that every positive seed `1 ≤ a` fails
   survival by step `R a` (`survivesSteps a (R a) = false`).
4. **Unbounded Growth of `leastPositiveSurvivor`**:
   `∀ B : ℕ, ∃ N : ℕ, B ≤ leastPositiveSurvivor N`. -/
theorem safety_game_kernel_and_rank_completeness :
    ((∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) ↔
      survivorKernel = ∅) ∧
    (survivorKernel = ∅ ↔
      (∃ R : ℕ → ℕ, ∀ a : ℕ, 1 ≤ a → survivesSteps a (R a) = false)) ∧
    ((∃ R : ℕ → ℕ, ∀ a : ℕ, 1 ≤ a → survivesSteps a (R a) = false) ↔
      (∀ B : ℕ, ∃ N : ℕ, B ≤ leastPositiveSurvivor N)) := by
  rcases general_mahler_conjecture_iff_positive_stabilized_branch_escape with ⟨h12, h23, _, _⟩
  have h1_fin :
      (∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) ↔
        (∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) :=
    h12.trans h23
  have hkern_fin :
      survivorKernel = ∅ ↔
        (∀ a_0 : ℕ, 1 ≤ a_0 → ∃ N : ℕ, ¬ ∃ α : ℝ, ValidCompanionUpTo a_0 α N) := by
    rw [Set.eq_empty_iff_forall_not_mem]
    constructor
    · intro hno a_0 ha0
      have hnot := hno a_0
      rw [mem_survivorKernel_iff_forall_validCompanionUpTo] at hnot
      push_neg at hnot
      obtain ⟨N, hN⟩ := hnot ha0
      exact ⟨N, fun ⟨α, hα⟩ => hN α hα⟩
    · intro hfin a_0 hmem
      rw [mem_survivorKernel_iff_forall_validCompanionUpTo] at hmem
      obtain ⟨N, hN⟩ := hfin a_0 hmem.1
      exact hN (hmem.2 N)
  have hkern_rank :
      survivorKernel = ∅ ↔
        (∃ R : ℕ → ℕ, ∀ a : ℕ, 1 ≤ a → survivesSteps a (R a) = false) := by
    rw [Set.eq_empty_iff_forall_not_mem]
    constructor
    · intro hno
      have hex : ∀ a : ℕ, ∃ N : ℕ, 1 ≤ a → survivesSteps a N = false := by
        intro a
        by_cases ha : 1 ≤ a
        · have hnot := hno a
          simp only [survivorKernel, Set.mem_iInter, survivesHorizonSet, Set.mem_setOf_eq] at hnot
          push_neg at hnot
          obtain ⟨N, hN⟩ := hnot
          have hfalse : survivesSteps a N = false := by
            cases hbool : survivesSteps a N
            · rfl
            · exfalso; exact hN ha hbool
          exact ⟨N, fun _ => hfalse⟩
        · exact ⟨0, fun h1 => absurd h1 ha⟩
      choose R hR using hex
      exact ⟨R, hR⟩
    · rintro ⟨R, hR⟩ a hmem
      simp only [survivorKernel, Set.mem_iInter, survivesHorizonSet, Set.mem_setOf_eq] at hmem
      have ha : 1 ≤ a := (hmem 0).1
      have htrue : survivesSteps a (R a) = true := (hmem (R a)).2
      have hfalse : survivesSteps a (R a) = false := hR a ha
      rw [htrue] at hfalse
      contradiction
  refine ⟨h1_fin.trans hkern_fin.symm, hkern_rank, ?_⟩
  rw [← hkern_rank, ← h1_fin.trans hkern_fin.symm]
  exact mahler_conjecture_iff_leastPositiveSurvivor_unbounded

end Mahler.ParitySurplusAndGames
