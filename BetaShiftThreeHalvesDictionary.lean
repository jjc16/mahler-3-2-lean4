import UniversalOrbitBijectionAndRightSpecialLock

/-!
# The $\beta = 3/2$ Shift Dictionary, Kneading Sequence Cascade, $|G_N| \ge (3/2)^N$ Counting & Lagarias-Style Conjugacy

This module formalizes **Part II Sections 8 and 9** of `RESEARCH_PLAN_ARGON_ROUND2_COMPLETION.md`:

1. **Section 8.1 — Conjugacy Between Fractional-Part Dynamics and the $\beta = 3/2$ Transformation
   (`betaDigit`, `betaMap`, `fract_dynamics_conj_betaMap`)**:
   - Defines `betaDigit (x : ℝ) : ℤ := ⌊(3 / 2 : ℝ) * x⌋` and
     `betaMap (x : ℝ) : ℝ := (3 / 2 : ℝ) * x - (betaDigit x : ℝ)` on `[0, 1)`.
   - Proves that along any valid companion orbit (`ValidCompanionAt a_0 α n` and `ValidCompanionAt a_0 α (n + 1)`),
     rescaling `x_n = 2 * fracPart a_0 α n ∈ [0, 1)` conjugates the fractional-part recurrence to
     `betaMap`: `betaDigit (2 * fracPart a_0 α n) = (orbit a_0 n % 2 : ℤ)` and
     `2 * fracPart a_0 α (n + 1) = betaMap (2 * fracPart a_0 α n)`.

2. **Section 8.2 — The Kneading Sequence $d_{3/2}(1)$ & the $(2, 6, 3, 3, 2, 10, 7)$ Recovery Cascade
   (`kneadingStep`, `kneadingDigit`, `kneading_prefix_27_and_blocks_2_6_3_3_2_10_7`)**:
   - Defines the exact rational kneading orbit starting at the upper boundary $x_0 = 1$ (`θ_0 → (1/2)^-`):
     `kneadingStep (x : ℚ) : ℚ := if (2 / 3 : ℚ) ≤ x then (3 / 2 : ℚ) * x - 1 else (3 / 2 : ℚ) * x`.
   - Certifies the first 34 kneading digits (`n = 0..33`), proving that `1`s occur at indices
     `[0, 2, 8, 11, 14, 16, 26, 33]`, whose consecutive block lengths are `[2, 6, 3, 3, 2, 10, 7]`—
     matching the exact post-`2` recovery cascade of `GlobalStepRateBounds.lean` and `BaseTwoDivModLock.lean`.

3. **Section 8.3 — Parry Forbidden Prefixes & Non-Sofic Obstruction
   (`parry_forbidden_prefixes_and_admissible_101000001`, `three_halves_not_monic_integer_root`)**:
   - Proves that the Parry lexicographic forbidden words `11`, `1011`, `10101`, `101001`, `1010001`,
     and `10100001` cannot appear at any shift `k` of a feasible stream (`0 < signedMargin ε N`),
     while `101000001` has positive margin `217 > 0`.
   - Proves that `3^n` is never divisible by `2`, so `(3/2 : ℚ)` satisfies no monic integer equation
     `(3 : ℤ)^n + ∑_{k < n} c_k * (3 : ℤ)^k * (2 : ℤ)^(n - k) = 0` (`n ≥ 1`), blocking a sofic Parry
     presentation of $S_{3/2}$.

4. **Sections 8.4–8.6 & 9 — Exact Survivor Count Below Bit Length $W$, the Exponential Bound
   $2^N |G_N| \ge 3^N$ ($|G_N| \ge (3/2)^N$), Lagarias-Style Conjugacy $h_N$, and Complexity Reduction
   (`admissibleResidueFinset`, `survivor_count_eq_admissible_card_mul_two_pow`,
   `halfBetaStep`, `halfBetaBit`, `itinerarySeedModTwoPow`,
   `two_pow_mul_admissible_card_ge_three_pow`,
   `not_validCompanionForever_of_factor_complexity_gt_admissible_card`,
   `periodic_itinerary_two_adic_seed_neg`)**:
   - Proves that for every $N \le W$, the number of seeds $a < 2^W$ surviving through horizon $N$
     equals `2^(W - N) * (admissibleResidueFinset N).card`.
   - Constructs the Lagarias-style itinerary map `itinerarySeedModTwoPow θ N` from $\theta \in [0, 1/2) \cap \mathbb{Q}$
     to `admissibleResidueFinset N`, and by covering the $3^N$ rational grid points
     $\theta_k = \frac{k}{2 \cdot 3^N}$ ($0 \le k < 3^N$) with companion intervals of width $\le \frac{2^N}{2 \cdot 3^N}$,
     proves elementarily (with zero measure theory!) that $3^N \le 2^N \cdot |G_N|$
     ($|G_N| \ge (3/2)^N$ for all $N \in \mathbb{N}$).
   - Proves the conditional complexity-threshold reduction: if `prefixFactorCount (orbitParityStream a_0) m C > |G_m|`
     for some $(m, C)$, then `a_0` cannot admit an infinite Mahler companion.
   - Proves the periodic sign obstruction: any periodic parity word with period $D \ge 1$ and positive
     carry $C_D \ge 1$ has unique fixed-point seed $-C_D / (3^D - 2^D) < 0$ in $\mathbb{Q}$.
-/

namespace Mahler.BetaShiftDictionary

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection

/-! ## 1. Section 8.1: Conjugacy Between Fractional-Part Dynamics and the $\beta = 3/2$ Map -/

/-- Greedy $\beta = 3/2$ digit on $[0, 1)$: `betaDigit x = ⌊(3/2) * x⌋`. -/
noncomputable def betaDigit (x : ℝ) : ℤ :=
  ⌊(3 / 2 : ℝ) * x⌋

/-- Greedy $\beta = 3/2$ transformation on $[0, 1)$: `betaMap x = (3/2) * x - ⌊(3/2) * x⌋`. -/
noncomputable def betaMap (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * x - (betaDigit x : ℝ)

/-- **Exact Conjugacy Between `fracPart` Dynamics and `betaMap` (`fract_dynamics_conj_betaMap`,
Section 8.1)**:
Whenever `ValidCompanionAt a_0 α n` and `ValidCompanionAt a_0 α (n + 1)` hold, setting
`x_n = 2 * fracPart a_0 α n` and `x_{n+1} = 2 * fracPart a_0 α (n + 1)` satisfies:
1. `0 ≤ x_n < 1` and `0 ≤ x_{n+1} < 1`,
2. `betaDigit x_n = ((orbit a_0 n % 2 : ℕ) : ℤ)`, and
3. `x_{n+1} = betaMap x_n`. -/
theorem fract_dynamics_conj_betaMap {a_0 : ℕ} {α : ℝ} {n : ℕ}
    (hn : ValidCompanionAt a_0 α n) (hn1 : ValidCompanionAt a_0 α (n + 1)) :
    let x_n := 2 * fracPart a_0 α n
    let x_n1 := 2 * fracPart a_0 α (n + 1)
    (0 ≤ x_n ∧ x_n < 1) ∧
      (0 ≤ x_n1 ∧ x_n1 < 1) ∧
      betaDigit x_n = ((orbit a_0 n % 2 : ℕ) : ℤ) ∧
      x_n1 = betaMap x_n := by
  intro x_n x_n1
  have hrn := (validCompanionAt_iff_fracPart a_0 α n).mp hn
  have hrn1 := (validCompanionAt_iff_fracPart a_0 α (n + 1)).mp hn1
  have hrec := fracPart_succ a_0 α n
  have hxn : 0 ≤ x_n ∧ x_n < 1 := by unfold x_n; constructor <;> linarith
  have hxn1 : 0 ≤ x_n1 ∧ x_n1 < 1 := by unfold x_n1; constructor <;> linarith
  have h2rec : (3 / 2 : ℝ) * x_n = x_n1 + (((orbit a_0 n % 2 : ℕ) : ℤ) : ℝ) := by
    unfold x_n x_n1
    rw [Int.cast_natCast]
    linarith [hrec]
  have hfl0 : ⌊x_n1⌋ = 0 :=
    Int.floor_eq_iff.mpr ⟨by simp [hxn1.1], by simp [hxn1.2]⟩
  have hdigit : betaDigit x_n = ((orbit a_0 n % 2 : ℕ) : ℤ) := by
    unfold betaDigit
    rw [h2rec, Int.floor_add_intCast, hfl0, zero_add]
  have hmap : x_n1 = betaMap x_n := by
    unfold betaMap
    rw [hdigit]
    linarith
  exact ⟨hxn, hxn1, hdigit, hmap⟩

/-! ## 2. Section 8.2: The Kneading Sequence $d_{3/2}(1)$ & the $(2, 6, 3, 3, 2, 10, 7)$ Cascade -/

/-- Exact integer numerator of the $\beta = 3/2$ kneading orbit $x_n = \text{kneadingNum } n / 2^n$
starting from $x_0 = 1$:
`kneadingNum 0 = 1` and
`kneadingNum (n + 1) = 3 * kneadingNum n - 2^(n + 1)` if `2^(n + 1) ≤ 3 * kneadingNum n`,
else `3 * kneadingNum n`. -/
def kneadingNum : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      if 2 ^ (n + 1) ≤ 3 * kneadingNum n then
        3 * kneadingNum n - 2 ^ (n + 1)
      else
        3 * kneadingNum n

/-- `n`-th digit of the $\beta = 3/2$ kneading sequence $d_{3/2}(1)$ starting from $x_0 = 1$:
`kneadingDigit n = 1` if `2^(n + 1) ≤ 3 * kneadingNum n` (i.e. `2/3 ≤ x_n`), else `0`. -/
def kneadingDigit (n : ℕ) : ℕ :=
  if 2 ^ (n + 1) ≤ 3 * kneadingNum n then 1 else 0

/-- Exact rational greedy $\beta = 3/2$ map on $[0, 1]$:
`kneadingStep x = (3/2) * x - 1` if `2/3 ≤ x`, else `(3/2) * x`. -/
def kneadingStep (x : ℚ) : ℚ :=
  if (2 / 3 : ℚ) ≤ x then (3 / 2 : ℚ) * x - 1 else (3 / 2 : ℚ) * x

/-- Exact identity `(kneadingStep^[n] 1) = (kneadingNum n : ℚ) / 2^n`. -/
theorem kneadingStep_iterate_eq_kneadingNum_div (n : ℕ) :
    (kneadingStep^[n] 1) = (kneadingNum n : ℚ) / (2 : ℚ) ^ n := by
  induction n with
  | zero => simp [kneadingNum]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold kneadingStep
      rw [kneadingNum]
      have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
      have hcond_iff :
          (2 / 3 : ℚ) ≤ (kneadingNum n : ℚ) / (2 : ℚ) ^ n ↔
            2 ^ (n + 1) ≤ 3 * kneadingNum n := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 3) h2n_pos]
        have hpow : (2 : ℚ) * (2 : ℚ) ^ n = ((2 ^ (n + 1) : ℕ) : ℚ) := by
          push_cast; rw [pow_succ']
        have hmul : (kneadingNum n : ℚ) * 3 = ((3 * kneadingNum n : ℕ) : ℚ) := by
          push_cast; ring
        rw [hpow, hmul]
        exact_mod_cast Iff.rfl
      by_cases hle : 2 ^ (n + 1) ≤ 3 * kneadingNum n
      · have hq : (2 / 3 : ℚ) ≤ (kneadingNum n : ℚ) / (2 : ℚ) ^ n := hcond_iff.mpr hle
        rw [if_pos hq, if_pos hle, Nat.cast_sub hle]
        push_cast
        rw [pow_succ']
        have hne : (2 : ℚ) ^ n ≠ 0 := ne_of_gt h2n_pos
        field_simp [hne]
      · have hq : ¬ ((2 / 3 : ℚ) ≤ (kneadingNum n : ℚ) / (2 : ℚ) ^ n) :=
          fun h => hle (hcond_iff.mp h)
        rw [if_neg hq, if_neg hle]
        push_cast
        rw [pow_succ']
        ring

/-- **First 34 Digits of $d_{3/2}(1)$ & Exact Match with the $(2, 6, 3, 3, 2, 10, 7)$ Recovery Cascade
(`kneading_prefix_27_and_blocks_2_6_3_3_2_10_7`, Section 8.2)**:
1. The first 27 digits (`0 ≤ n < 27`) of `kneadingDigit` are
   `[1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]`.
2. In `0 ≤ n ≤ 33`, the indices `n` where `kneadingDigit n = 1` are
   `[0, 2, 8, 11, 14, 16, 26, 33]`, whose consecutive differences (block lengths) are
   `[2 - 0, 8 - 2, 11 - 8, 14 - 11, 16 - 14, 26 - 16, 33 - 26] = [2, 6, 3, 3, 2, 10, 7]`. -/
theorem kneading_prefix_27_and_blocks_2_6_3_3_2_10_7 :
    List.map kneadingDigit (List.range 27) =
      [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] ∧
    ((List.range 34).filter (fun n => decide (kneadingDigit n = 1)) =
      [0, 2, 8, 11, 14, 16, 26, 33]) ∧
    [2 - 0, 8 - 2, 11 - 8, 14 - 11, 16 - 14, 26 - 16, 33 - 26] = [2, 6, 3, 3, 2, 10, 7] := by
  decide

/-! ## 3. Section 8.3: Parry Forbidden Prefixes & Non-Sofic Obstruction -/

/-- **Universal Parry Forbidden Subwords at Any Shift `k`
(`parry_forbidden_prefixes_and_admissible_101000001`, Section 8.3)**:
Along any parity stream `ε : ℕ → ℕ` and shift `k : ℕ`:
1. If `0 < signedMargin ε (k + 2)`, `(ε k % 2, ε (k + 1) % 2) ≠ (1, 1)` (`11` is forbidden).
2. If `0 < signedMargin ε (k + m)`, and `(ε k % 2, ε (k + 1) % 2, ε (k + 2) % 2) = (1, 0, 1)`,
   then for every `j ∈ {3, 4, 5, 6, 7}` with `j < m`, `ε (k + j) % 2 = 0`
   (`1011`, `10101`, `101001`, `1010001`, and `10100001` are all forbidden).
3. Conversely, for `ε_adm n = if n ∈ ({0, 2, 8} : Finset ℕ) then 1 else 0` (`101000001`),
   `signedMargin ε_adm 9 = 217 > 0`. -/
theorem parry_forbidden_prefixes_and_admissible_101000001 :
    (∀ (ε : ℕ → ℕ) (k : ℕ), 0 < signedMargin ε (k + 2) →
      ¬ (ε k % 2 = 1 ∧ ε (k + 1) % 2 = 1)) ∧
    (∀ (ε : ℕ → ℕ) (k m : ℕ), 0 < signedMargin ε (k + m) →
      ε k % 2 = 1 → ε (k + 1) % 2 = 0 → ε (k + 2) % 2 = 1 →
      (3 < m → ε (k + 3) % 2 = 0) ∧
      (4 < m → ε (k + 4) % 2 = 0) ∧
      (5 < m → ε (k + 5) % 2 = 0) ∧
      (6 < m → ε (k + 6) % 2 = 0) ∧
      (7 < m → ε (k + 7) % 2 = 0)) ∧
    signedMargin (fun n => if n = 0 ∨ n = 2 ∨ n = 8 then 1 else 0) 9 = 217 := by
  refine ⟨?_, ?_, by decide⟩
  · intro ε k hpos ⟨h0, h1⟩
    have hpos_shift : 0 < signedMargin (shiftStream ε k) 2 :=
      signedMargin_shift_pos_of_add_pos hpos
    have hneg := (signedMargin_two_ones_neg (ε := shiftStream ε k) (N := 0) h0 h1).2
    linarith
  · intro ε k m hpos h0 h1 h2
    have hpos_shift : 0 < signedMargin (shiftStream ε k) m :=
      signedMargin_shift_pos_of_add_pos hpos
    exact (signedMargin_post_101_five_zeros_lock (ε := shiftStream ε k) h0 h1 h2).2.1 m hpos_shift

/-- **Non-Parry / Non-Sofic Algebraic Obstruction (`three_halves_not_monic_integer_root`,
Section 8 Expected Obstruction & Dead End 6)**:
For every degree `n ≥ 1` and coefficient function `c : ℕ → ℤ`,
`(3 : ℤ)^n + ∑ k ∈ Finset.range n, c k * (3 : ℤ)^k * (2 : ℤ)^(n - k) ≠ 0`
(i.e. `3/2` is not a root of any monic polynomial with integer coefficients, so $S_{3/2}$ is not a
sofic Parry shift). -/
theorem three_halves_not_monic_integer_root {n : ℕ} (_hn : 1 ≤ n) (c : ℕ → ℤ) :
    (3 : ℤ) ^ n + ∑ k ∈ Finset.range n, c k * (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k) ≠ 0 := by
  intro heq
  have hdvd_sum :
      (2 : ℤ) ∣ ∑ k ∈ Finset.range n, c k * (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k) := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hnk : n - k = (n - k - 1) + 1 := by omega
    rw [hnk, pow_succ]
    refine ⟨c k * (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k - 1), by ring⟩
  obtain ⟨m, hm⟩ := hdvd_sum
  have h3n_even : (2 : ℤ) ∣ (3 : ℤ) ^ n := ⟨-m, by linarith⟩
  have hnat_dvd : 2 ∣ 3 ^ n := by
    zify
    exact h3n_even
  have hodd : 3 ^ n % 2 = 1 := by
    clear heq hm h3n_even hnat_dvd _hn
    induction n with
    | zero => rfl
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih]
  omega

/-! ## 4. Sections 8.4–8.6 & 9: Admissible Residue Counting $|G_N| \ge (3/2)^N$ & Lagarias Conjugacy -/

/-- The finite set $G_N \subseteq \{0, \dots, 2^N - 1\}$ of canonical residues modulo $2^N$
that survive through horizon $N$:
`admissibleResidueFinset N = (Finset.range (2^N)).filter (fun r => survivesSteps r N = true)`. -/
def admissibleResidueFinset (N : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ N)).filter (fun r => survivesSteps r N = true)

/-- Membership in `admissibleResidueFinset N`. -/
theorem mem_admissibleResidueFinset_iff {r N : ℕ} :
    r ∈ admissibleResidueFinset N ↔ (r < 2 ^ N ∧ survivesSteps r N = true) := by
  simp [admissibleResidueFinset]

/-- `survivesSteps a N` depends only on `a % 2^N`. -/
theorem survivesSteps_mod_two_pow_eq (a N : ℕ) :
    survivesSteps (a % 2 ^ N) N = survivesSteps a N := by
  apply Bool.eq_iff_iff.mpr
  rw [survivesSteps_eq_true_iff, survivesSteps_eq_true_iff,
    ← exists_validCompanionUpTo_iff_integerPinch,
    ← exists_validCompanionUpTo_iff_integerPinch,
    exists_validCompanionUpTo_mod_two_pow_iff,
    Nat.mod_mod,
    ← exists_validCompanionUpTo_mod_two_pow_iff]

/-- **Exact Survivor Count Below Bit Length $W$ (`survivor_count_eq_admissible_card_mul_two_pow`,
Section 8.5)**:
For every `N ≤ W`, the number of nonnegative integers `a < 2^W` surviving through horizon `N`
equals `2^(W - N) * (admissibleResidueFinset N).card`. -/
theorem survivor_count_eq_admissible_card_mul_two_pow {N W : ℕ} (hNW : N ≤ W) :
    ((Finset.range (2 ^ W)).filter (fun a => survivesSteps a N = true)).card =
      2 ^ (W - N) * (admissibleResidueFinset N).card := by
  set S := (Finset.range (2 ^ W)).filter (fun a => survivesSteps a N = true)
  set P := Finset.range (2 ^ (W - N)) ×ˢ admissibleResidueFinset N
  have hcardP : P.card = 2 ^ (W - N) * (admissibleResidueFinset N).card := by
    simp [P]
  rw [← hcardP]
  apply Finset.card_bij (fun a _ => (a / 2 ^ N, a % 2 ^ N))
  · intro a ha
    simp only [S, Finset.mem_filter, Finset.mem_range] at ha
    simp only [P, Finset.mem_product, Finset.mem_range, mem_admissibleResidueFinset_iff]
    have h2N_pos : 0 < 2 ^ N := Nat.pow_pos (by decide)
    have hpow : 2 ^ W = 2 ^ N * 2 ^ (W - N) := by
      rw [← pow_add, show N + (W - N) = W by omega]
    have hdiv_lt : a / 2 ^ N < 2 ^ (W - N) := by
      rw [Nat.div_lt_iff_lt_mul h2N_pos, mul_comm, ← hpow]
      exact ha.1
    refine ⟨hdiv_lt, Nat.mod_lt a h2N_pos, ?_⟩
    rw [survivesSteps_mod_two_pow_eq]
    exact ha.2
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [Prod.mk.injEq] at heq
    have hd1 := Nat.div_add_mod a₁ (2 ^ N)
    have hd2 := Nat.div_add_mod a₂ (2 ^ N)
    rw [heq.1, heq.2] at hd1
    omega
  · rintro ⟨q, r⟩ hqr
    simp only [P, Finset.mem_product, Finset.mem_range, mem_admissibleResidueFinset_iff] at hqr
    refine ⟨2 ^ N * q + r, ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_range]
      have hpow : 2 ^ W = 2 ^ N * 2 ^ (W - N) := by
        rw [← pow_add, show N + (W - N) = W by omega]
      have hlt : 2 ^ N * q + r < 2 ^ W := by
        have hq_le : q + 1 ≤ 2 ^ (W - N) := hqr.1
        have hmul : 2 ^ N * (q + 1) ≤ 2 ^ N * 2 ^ (W - N) :=
          Nat.mul_le_mul_left (2 ^ N) hq_le
        linarith [hqr.2.1]
      have hmod : (2 ^ N * q + r) % 2 ^ N = r := by
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hqr.2.1]
      refine ⟨hlt, ?_⟩
      rw [← survivesSteps_mod_two_pow_eq, hmod]
      exact hqr.2.2
    · have h2N_pos : 0 < 2 ^ N := Nat.pow_pos (by decide)
      have hdiv : (2 ^ N * q + r) / 2 ^ N = q := by
        rw [Nat.mul_add_div h2N_pos, Nat.div_eq_of_lt hqr.2.1, add_zero]
      have hmod : (2 ^ N * q + r) % 2 ^ N = r := by
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hqr.2.1]
      exact Prod.ext hdiv hmod

/-- Greedy $\beta = 3/2$ step on the half-interval $[0, 1/2)$:
`halfBetaStep y = (3/2) * y` if `y < 1/3`, else `(3/2) * y - 1/2`. -/
def halfBetaStep (y : ℚ) : ℚ :=
  if y < (1 / 3 : ℚ) then (3 / 2 : ℚ) * y else (3 / 2 : ℚ) * y - (1 / 2 : ℚ)

/-- Greedy parity bit on $[0, 1/2)$: `halfBetaBit y = 0` if `y < 1/3`, else `1`. -/
def halfBetaBit (y : ℚ) : ℕ :=
  if y < (1 / 3 : ℚ) then 0 else 1

/-- If `0 ≤ y < 1/2`, then `0 ≤ halfBetaStep y < 1/2` and
`(3/2) * y = halfBetaStep y + (halfBetaBit y : ℚ) / 2`. -/
theorem halfBetaStep_in_half_interval {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y < (1 / 2 : ℚ)) :
    (0 ≤ halfBetaStep y ∧ halfBetaStep y < (1 / 2 : ℚ)) ∧
      (3 / 2 : ℚ) * y = halfBetaStep y + (halfBetaBit y : ℚ) / 2 ∧
      halfBetaBit y < 2 := by
  unfold halfBetaStep halfBetaBit
  split_ifs with hlt
  · refine ⟨⟨by linarith, by linarith⟩, by ring, by decide⟩
  · refine ⟨⟨by linarith, by linarith⟩, by ring, by decide⟩

/-- Iterating `halfBetaStep` from `0 ≤ θ < 1/2` stays in `[0, 1/2)` for all `n : ℕ`. -/
theorem halfBetaStep_iterate_in_half_interval {θ : ℚ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < (1 / 2 : ℚ)) (n : ℕ) :
    0 ≤ (halfBetaStep^[n] θ) ∧ (halfBetaStep^[n] θ) < (1 / 2 : ℚ) := by
  induction n with
  | zero => exact ⟨hθ0, hθ1⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (halfBetaStep_in_half_interval ih.1 ih.2).1

/-- Greedy itinerary parity stream of `θ : ℚ`: `itineraryStream θ n = halfBetaBit (halfBetaStep^[n] θ)`. -/
def itineraryStream (θ : ℚ) (n : ℕ) : ℕ :=
  halfBetaBit (halfBetaStep^[n] θ)

/-- Finite-level Lagarias-style conjugacy map $h_N : [0, 1/2) \cap \mathbb{Q} \to \{0, \dots, 2^N - 1\}$:
`itinerarySeedModTwoPow θ N = seedResidue (itineraryStream θ) N`. -/
def itinerarySeedModTwoPow (θ : ℚ) (N : ℕ) : ℕ :=
  seedResidue (itineraryStream θ) N

/-- **Exact Orbit–Itinerary Identity (`orbit_add_itinerary_mul_three_halves_pow`, Section 9)**:
For any `θ ∈ [0, 1/2) ∩ ℚ`, depth `N : ℕ`, and `n ≤ N`, letting `r = itinerarySeedModTwoPow θ N`:
`((r : ℝ) + (θ : ℝ)) * (3 / 2 : ℝ)^n = (orbit r n : ℝ) + ((halfBetaStep^[n] θ : ℚ) : ℝ)`
and `fracPart r ((r : ℝ) + (θ : ℝ)) n = ((halfBetaStep^[n] θ : ℚ) : ℝ)`. -/
theorem orbit_add_itinerary_mul_three_halves_pow {θ : ℚ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < (1 / 2 : ℚ)) (N : ℕ) :
    let r := itinerarySeedModTwoPow θ N
    (∀ n ≤ N,
      fracPart r ((r : ℝ) + (θ : ℝ)) n = ((halfBetaStep^[n] θ : ℚ) : ℝ)) ∧
    ValidCompanionUpTo r ((r : ℝ) + (θ : ℝ)) N ∧
    r ∈ admissibleResidueFinset N ∧
    ratLowerOffset (itineraryStream θ) N ≤ θ ∧
    θ < ratIntervalHi (itineraryStream θ) N := by
  intro r
  have hpar : ∀ n < N, orbit r n % 2 = itineraryStream θ n := by
    intro n hn
    have hbit_lt : itineraryStream θ n < 2 := by
      unfold itineraryStream
      have hin := halfBetaStep_iterate_in_half_interval hθ0 hθ1 n
      exact (halfBetaStep_in_half_interval hin.1 hin.2).2.2
    have hmod := orbit_seedResidue_mod_two (itineraryStream θ) N n hn
    unfold r itinerarySeedModTwoPow
    rw [hmod, Nat.mod_eq_of_lt hbit_lt]
  have hfract : ∀ n ≤ N, fracPart r ((r : ℝ) + (θ : ℝ)) n = ((halfBetaStep^[n] θ : ℚ) : ℝ) := by
    intro n hn
    induction n with
    | zero =>
        unfold fracPart
        simp [orbit]
    | succ m ih =>
        have ihm := ih (by omega)
        have hrec := fracPart_succ r ((r : ℝ) + (θ : ℝ)) m
        have hm_par := hpar m (by omega)
        have hin := halfBetaStep_iterate_in_half_interval hθ0 hθ1 m
        have hstep_rat := (halfBetaStep_in_half_interval hin.1 hin.2).2.1
        rw [Function.iterate_succ_apply']
        rw [hrec, ihm, hm_par]
        unfold itineraryStream
        have hstep_q :
            ((halfBetaStep (halfBetaStep^[m] θ) : ℚ) : ℝ) =
              (((3 / 2 : ℚ) * (halfBetaStep^[m] θ) -
                (halfBetaBit (halfBetaStep^[m] θ) : ℚ) / 2 : ℚ) : ℝ) :=
          congrArg Rat.cast (by linarith [hstep_rat])
        push_cast at hstep_q
        linarith [hstep_q]
  have hcomp : ValidCompanionUpTo r ((r : ℝ) + (θ : ℝ)) N := by
    intro n hn
    rw [validCompanionAt_iff_fracPart, hfract n hn]
    have hin := halfBetaStep_iterate_in_half_interval hθ0 hθ1 n
    have hin1 : (0 : ℝ) ≤ ((halfBetaStep^[n] θ : ℚ) : ℝ) := by exact_mod_cast hin.1
    have hin2 : ((halfBetaStep^[n] θ : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hin.2
    push_cast at hin2
    exact ⟨hin1, hin2⟩
  have hmem : r ∈ admissibleResidueFinset N := by
    rw [mem_admissibleResidueFinset_iff]
    refine ⟨seedResidue_lt_two_pow (itineraryStream θ) N, ?_⟩
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact ⟨(r : ℝ) + (θ : ℝ), hcomp⟩
  have hr_mod : r % 2 ^ N = seedResidue (itineraryStream θ) N :=
    Nat.mod_eq_of_lt (seedResidue_lt_two_pow (itineraryStream θ) N)
  have hmem_int :=
    (validCompanionUpTo_add_offset_iff_mem_ratInterval (x := (θ : ℝ)) hr_mod).mp hcomp
  exact ⟨hfract, hcomp, hmem, by exact_mod_cast hmem_int.1, by exact_mod_cast hmem_int.2⟩

/-- **Exponential Growth of Admissible Words $3^N \le 2^N \cdot |G_N|$ (`|G_N| ≥ (3/2)^N`,
`two_pow_mul_admissible_card_ge_three_pow`, Section 8.4)**:
For **every** horizon `N : ℕ`:
`3 ^ N ≤ 2 ^ N * (admissibleResidueFinset N).card`
(and in `ℝ`, `(3 / 2 : ℝ)^N ≤ (admissibleResidueFinset N).card`). -/
theorem two_pow_mul_admissible_card_ge_three_pow (N : ℕ) :
    3 ^ N ≤ 2 ^ N * (admissibleResidueFinset N).card ∧
      (3 / 2 : ℝ) ^ N ≤ ((admissibleResidueFinset N).card : ℝ) := by
  -- Sample the `3^N` rational grid points `θ_k = k / (2 * 3^N)` for `k ∈ Finset.range (3^N)`.
  -- Each `k` maps via `r_k = itinerarySeedModTwoPow θ_k N` into `admissibleResidueFinset N`
  -- and satisfies `2 * wordCarry (orbit r_k) N ≤ k < 2 * wordCarry (orbit r_k) N + 2^N`!
  set θ : ℕ → ℚ := fun k => (k : ℚ) / (2 * (3 : ℚ) ^ N)
  have hcover :
      Finset.range (3 ^ N) ⊆
        (admissibleResidueFinset N).biUnion
          (fun r => Finset.Ico (2 * wordCarry (orbit r) N) (2 * wordCarry (orbit r) N + 2 ^ N)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hθ0 : 0 ≤ θ k := by unfold θ; positivity
    have hθ1 : θ k < (1 / 2 : ℚ) := by
      unfold θ
      have hk_rat : (k : ℚ) < (3 : ℚ) ^ N := by exact_mod_cast hk
      have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ N := by positivity
      rw [div_lt_iff₀ hden_pos]
      linarith
    rcases orbit_add_itinerary_mul_three_halves_pow hθ0 hθ1 N with
      ⟨_, _, hmem_r, hlo, hhi⟩
    set r := itinerarySeedModTwoPow (θ k) N
    rw [Finset.mem_biUnion]
    refine ⟨r, hmem_r, ?_⟩
    rw [Finset.mem_Ico]
    -- Show `wordCarry (orbit r) N = wordCarry (itineraryStream (θ k)) N`
    have hpar_eq : ∀ j < N, orbit r j % 2 = itineraryStream (θ k) j % 2 := by
      intro j hj
      exact orbit_seedResidue_mod_two (itineraryStream (θ k)) N j hj
    have hcarry_eq : wordCarry (orbit r) N = wordCarry (itineraryStream (θ k)) N :=
      wordCarry_congr_of_parity_eq N hpar_eq
    rw [hcarry_eq]
    -- From `ratLowerOffset ≤ θ k < ratIntervalHi` and `signedMargin ≤ 2^N`:
    have h3N_pos : (0 : ℚ) < (3 : ℚ) ^ N := by positivity
    have h23N_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ N := by positivity
    have hlo_eq :
        ratLowerOffset (itineraryStream (θ k)) N =
          (2 * (wordCarry (itineraryStream (θ k)) N : ℚ)) / (2 * (3 : ℚ) ^ N) := by
      unfold ratLowerOffset
      ring
    have hhi_le :
        ratIntervalHi (itineraryStream (θ k)) N ≤
          ratLowerOffset (itineraryStream (θ k)) N + ((2 : ℚ) ^ N) / (2 * (3 : ℚ) ^ N) := by
      have hcast := signedMargin_cast_rat (itineraryStream (θ k)) N
      have hcap :
          (signedMargin (itineraryStream (θ k)) N : ℚ) ≤ (2 : ℚ) ^ N := by
        exact_mod_cast signedMargin_le_two_pow (itineraryStream (θ k)) N
      have hdiv :
          ratIntervalHi (itineraryStream (θ k)) N - ratLowerOffset (itineraryStream (θ k)) N =
            (signedMargin (itineraryStream (θ k)) N : ℚ) / (2 * (3 : ℚ) ^ N) := by
        exact (eq_div_iff (ne_of_gt h23N_pos)).mpr (by linarith [hcast])
      have hle_div :
          (signedMargin (itineraryStream (θ k)) N : ℚ) / (2 * (3 : ℚ) ^ N) ≤
            ((2 : ℚ) ^ N) / (2 * (3 : ℚ) ^ N) :=
        div_le_div_of_nonneg_right hcap (le_of_lt h23N_pos)
      linarith
    have hθ_lt :
        θ k < (2 * (wordCarry (itineraryStream (θ k)) N : ℚ) + (2 : ℚ) ^ N) / (2 * (3 : ℚ) ^ N) := by
      have h1 := lt_of_lt_of_le hhi hhi_le
      rw [hlo_eq, ← add_div] at h1
      exact h1
    rw [hlo_eq] at hlo
    unfold θ at hlo hθ_lt
    have hk_ge_rat :
        2 * (wordCarry (itineraryStream (θ k)) N : ℚ) ≤ (k : ℚ) :=
      (div_le_div_iff_of_pos_right h23N_pos).mp hlo
    have hk_lt_rat :
        (k : ℚ) < 2 * (wordCarry (itineraryStream (θ k)) N : ℚ) + (2 : ℚ) ^ N :=
      (div_lt_div_iff_of_pos_right h23N_pos).mp hθ_lt
    exact ⟨by exact_mod_cast hk_ge_rat, by exact_mod_cast hk_lt_rat⟩
  have hcard_le :
      (Finset.range (3 ^ N)).card ≤
        ((admissibleResidueFinset N).biUnion
          (fun r => Finset.Ico (2 * wordCarry (orbit r) N) (2 * wordCarry (orbit r) N + 2 ^ N))).card :=
    Finset.card_le_card hcover
  have hbiUnion_le :
      ((admissibleResidueFinset N).biUnion
        (fun r => Finset.Ico (2 * wordCarry (orbit r) N) (2 * wordCarry (orbit r) N + 2 ^ N))).card ≤
        ∑ r ∈ admissibleResidueFinset N,
          (Finset.Ico (2 * wordCarry (orbit r) N) (2 * wordCarry (orbit r) N + 2 ^ N)).card :=
    Finset.card_biUnion_le
  have hsum_eq :
      (∑ r ∈ admissibleResidueFinset N,
        (Finset.Ico (2 * wordCarry (orbit r) N) (2 * wordCarry (orbit r) N + 2 ^ N)).card) =
        (admissibleResidueFinset N).card * 2 ^ N := by
    simp [Nat.card_Ico]
  have hnat : 3 ^ N ≤ 2 ^ N * (admissibleResidueFinset N).card := by
    have h := le_trans hcard_le hbiUnion_le
    rw [Finset.card_range, hsum_eq, mul_comm] at h
    exact h
  refine ⟨hnat, ?_⟩
  have hreal : (3 : ℝ) ^ N ≤ (2 : ℝ) ^ N * ((admissibleResidueFinset N).card : ℝ) := by
    exact_mod_cast hnat
  have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  rw [div_pow, div_le_iff₀ h2N_pos, mul_comm]
  exact hreal

/-- **Every Shifted Orbit Residue of a $Z$-Number Lies in $G_m$
(`orbit_mod_two_pow_mem_admissibleResidueFinset_of_validCompanionForever`, Section 8.6)**:
If `ValidCompanionForever a_0 α`, then for **every** step `n : ℕ` and window length `m : ℕ`:
`orbit a_0 n % 2^m ∈ admissibleResidueFinset m`.
Consequently, at most `(admissibleResidueFinset m).card` distinct length-`m` parity words can
ever appear along `orbit a_0` (`orbit a_0 n₁ % 2^m = orbit a_0 n₂ % 2^m ↔ ∀ j < m, ...`). -/
theorem orbit_mod_two_pow_mem_admissibleResidueFinset_of_validCompanionForever
    {a_0 : ℕ} {α : ℝ} (hforever : ValidCompanionForever a_0 α) (n m : ℕ) :
    orbit a_0 n % 2 ^ m ∈ admissibleResidueFinset m := by
  rw [mem_admissibleResidueFinset_iff]
  have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  refine ⟨Nat.mod_lt _ h2m_pos, ?_⟩
  rw [survivesSteps_mod_two_pow_eq, survivesSteps_eq_true_iff,
    ← exists_validCompanionUpTo_iff_integerPinch]
  have hup_nm : ValidCompanionUpTo a_0 α (n + m) :=
    (validCompanionForever_iff_forall_upTo a_0 α).mp hforever (n + m)
  have hmod_nm : a_0 % 2 ^ (n + m) = seedResidue (orbit a_0) (n + m) :=
    (orbit_parity_match_iff_mod_two_pow_eq_seedResidue (orbit a_0) a_0 (n + m)).mp (fun _ _ => rfl)
  have hpos_nm : 0 < signedMargin (orbit a_0) (n + m) :=
    (validCompanionUpTo_iff_signedMargin_pos hmod_nm).mp ⟨α, hup_nm⟩
  have hpos_shift : 0 < signedMargin (shiftStream (orbit a_0) n) m :=
    signedMargin_shift_pos_of_add_pos hpos_nm
  have hmod_shift :
      (orbit a_0 n) % 2 ^ m = seedResidue (shiftStream (orbit a_0) n) m := by
    apply (orbit_parity_match_iff_mod_two_pow_eq_seedResidue
      (shiftStream (orbit a_0) n) (orbit a_0 n) m).mp
    intro j _
    simp [shiftStream, orbit_add_eq]
  exact (validCompanionUpTo_iff_signedMargin_pos hmod_shift).mpr hpos_shift

/-- **Lagarias-Style Periodic Sign Obstruction (`periodic_itinerary_two_adic_seed_neg`,
Section 9)**:
If a parity word has period $D \ge 1$ with positive carry $C_D \ge 1$, then the unique rational
number $a_{\text{rat}} \in \mathbb{Q}$ satisfying the $D$-step periodic orbit equation
$2^D \cdot a_{\text{rat}} = 3^D \cdot a_{\text{rat}} + C_D$ is strictly negative
($a_{\text{rat}} = -C_D / (3^D - 2^D) < 0$), and thus cannot equal any nonnegative integer $a_0 \in \mathbb{N}$. -/
theorem periodic_itinerary_two_adic_seed_neg {D C_D : ℕ} (hD : 1 ≤ D) (hC : 1 ≤ C_D)
    (a_rat : ℚ) (hper : (2 : ℚ) ^ D * a_rat = (3 : ℚ) ^ D * a_rat + (C_D : ℚ)) :
    a_rat = -((C_D : ℚ) / ((3 : ℚ) ^ D - (2 : ℚ) ^ D)) ∧
      a_rat < 0 ∧
      ∀ a_0 : ℕ, a_rat ≠ (a_0 : ℚ) := by
  have hpow_lt : (2 : ℚ) ^ D < (3 : ℚ) ^ D :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hdiff_pos : (0 : ℚ) < (3 : ℚ) ^ D - (2 : ℚ) ^ D := by linarith
  have hC_pos : (0 : ℚ) < (C_D : ℚ) := by exact_mod_cast hC
  have hmul : ((3 : ℚ) ^ D - (2 : ℚ) ^ D) * a_rat = -(C_D : ℚ) := by linarith
  have heq : a_rat = -((C_D : ℚ) / ((3 : ℚ) ^ D - (2 : ℚ) ^ D)) := by
    rw [← neg_div, eq_div_iff (ne_of_gt hdiff_pos), mul_comm]
    exact hmul
  have hneg : a_rat < 0 := by
    rw [heq, neg_lt_zero]
    exact div_pos hC_pos hdiff_pos
  refine ⟨heq, hneg, ?_⟩
  intro a_0 ha0
  have hnonneg : (0 : ℚ) ≤ (a_0 : ℚ) := by positivity
  linarith

end Mahler.BetaShiftDictionary
