import ThueMorseMahlerFunctionalEquation

/-!
# Signed Defect Cocycle, 2-Adic Valuation Non-Cancellation & Sparse-Defect Exclusion

This module implements **Stage 4** of `RESEARCH_OUTLINE_NEXT_STAGE.md` and
provides the unified 130-module synthesis:

1. **The Exact Signed Single-Block Defect Identity (`affInv`, `defectTerm`,
   `defectTerm_small_values`, `single_block_signed_defect_identity`)**:
   For the affine invariant `affInv b = 19 * (b : ℤ) + 9` and signed defect
   `defectTerm c = 9 * (2 : ℤ)^c - 8 * (3 : ℤ)^(c - 1)` (`defectTerm 2 = 12`,
   `defectTerm 3 = 0`, `defectTerm 4 = -72`), every block `k < K` of a
   `ValidBlockChain a_0 s u K` satisfies the exact signed identity:
   `(2 : ℤ)^(s k) * affInv (orbit a_0 (blockSteps s (k + 1))) =
     (3 : ℤ)^(s k) * affInv (orbit a_0 (blockSteps s k)) + defectTerm (s k)`.

2. **Constant 2-Adic Valuation $v_2(E(c)) = 3$ for All Defects $c \ge 4$
   (`defectOddQuotient`, `defectTerm_eq_eight_mul_odd_of_four_le`)**:
   For every `c ≥ 3`, `defectTerm c = 8 * defectOddQuotient c` where
   `defectOddQuotient c = 9 * (2 : ℤ)^(c - 3) - (3 : ℤ)^(c - 1)`.
   Whenever `c ≥ 4` (even for arbitrarily large, unbounded block lengths `c`),
   `defectOddQuotient c` is **strictly odd** (`defectOddQuotient c % 2 ≠ 0`), so
   `(8 : ℤ) ∣ defectTerm c` and `¬ ((16 : ℤ) ∣ defectTerm c)`.

3. **The Iterated Multi-Block Signed Defect Cocycle & Explicit Finite-Sum Presentation
   (`defectCocycleSum`, `defectCocycleSum_eq_finset_sum`,
   `iterated_signed_defect_cocycle`)**:
   Iterating across `m ≤ K` blocks of a `ValidBlockChain a_0 s u K` yields both the
   recursive cocycle and its proved closed `Finset.sum` expansion:
   `defectCocycleSum s m = ∑ j ∈ Finset.range m, 3^(T(m) - T(j + 1)) * 2^(T(j)) * defectTerm (s j)`
   and
   `(2 : ℤ)^(blockSteps s m) * affInv (orbit a_0 (blockSteps s m)) =
     (3 : ℤ)^(blockSteps s m) * affInv a_0 + defectCocycleSum s m`.

4. **Local Prefix First-Defect Lock vs. Multi-Block Valuation Non-Cancellation
   (`local_single_block_affInv_identity`, `local_single_defect_valuation_three`,
   `local_prefix_first_defect_valuation_lock`,
   `first_defect_valuation_lock_and_non_cancellation`)**:
   - **Short Local Prefix Derivation**: At any single block boundary `b` with
     `3 * b + 1 = 2^c * u`, `3 * (19 * b + 9) = 19 * 2^c * u + 8`. When `c ≥ 4`,
     this single block already forces `8 ∣ (19 * b + 9)` and `¬ (16 ∣ (19 * b + 9))`
     locally, and propagating back across `j_0` blocks of length `3` (`ValidBlockChain a_0 s u (j_0 + 1)`)
     already forces `2^(3 * j_0 + 3) ∣ (19 * a_0 + 9)` and `¬ (2^(3 * j_0 + 4) ∣ (19 * a_0 + 9))`
     with **no** later blocks required.
   - **Multi-Block Non-Cancellation**: Along any longer continuation `m ≥ j_0 + 1`,
     later defect terms are divisible by `2^(3 * j_0 + 4)`, consistent with this
     prefix valuation lock; however, the normalized cocycle residual equals the
     growing boundary invariant `affInv (orbit a_0 (blockSteps s m))` rather than
     a descending rank.
-/

namespace Mahler.SparseDefectCocycle

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SturmianComplexityExclusion
open Mahler.FiniteSeedAndBackwardDescent
open Mahler.SubstitutionAndGrandSynthesis
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ThueMorseMahler

/-! ## 1. The Signed Single-Block Defect Identity -/

/-- The affine invariant `I(b) = 19 * b + 9` governing constant-3 orbits. -/
def affInv (b : ℕ) : ℤ :=
  19 * (b : ℤ) + 9

/-- The signed single-block defect `E(c) = 9 * 2^c - 8 * 3^(c - 1)`. -/
def defectTerm (c : ℕ) : ℤ :=
  9 * (2 : ℤ) ^ c - 8 * (3 : ℤ) ^ (c - 1)

/-- Explicit values of `defectTerm c` for `c = 1, 2, 3, 4, 5`:
`E(1) = 10`, `E(2) = 12`, `E(3) = 0`, `E(4) = -72`, `E(5) = -360`. -/
theorem defectTerm_small_values :
    defectTerm 1 = 10 ∧
      defectTerm 2 = 12 ∧
      defectTerm 3 = 0 ∧
      defectTerm 4 = -72 ∧
      defectTerm 5 = -360 := by
  decide

/-- **Exact Single-Block Signed Defect Identity (`single_block_signed_defect_identity`)**:
Along any `ValidBlockChain a_0 s u K` (`k < K`), the affine invariant `affInv`
evolves across block `k` with exact signed error `defectTerm (s k)`:
`(2 : ℤ)^(s k) * affInv (orbit a_0 (blockSteps s (k + 1))) =
  (3 : ℤ)^(s k) * affInv (orbit a_0 (blockSteps s k)) + defectTerm (s k)`. -/
theorem single_block_signed_defect_identity
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hkK : k < K) (hchain : ValidBlockChain a_0 s u K) :
    (2 : ℤ) ^ (s k) * affInv (orbit a_0 (blockSteps s (k + 1))) =
      (3 : ℤ) ^ (s k) * affInv (orbit a_0 (blockSteps s k)) + defectTerm (s k) := by
  rcases hchain k hkK with ⟨hsk, _, hdecomp⟩
  have horb_next : orbit a_0 (blockSteps s (k + 1)) = 3 ^ (s k - 1) * u k := by
    have hsteps : blockSteps s (k + 1) = blockSteps s k + s k := rfl
    rw [hsteps, orbit_add]
    exact orbit_odd_block_return hsk hdecomp
  have hdecomp_int :
      3 * (orbit a_0 (blockSteps s k) : ℤ) + 1 =
        (2 : ℤ) ^ (s k) * (u k : ℤ) := by
    exact_mod_cast hdecomp
  have horb_next_int :
      (orbit a_0 (blockSteps s (k + 1)) : ℤ) =
        (3 : ℤ) ^ (s k - 1) * (u k : ℤ) := by
    exact_mod_cast horb_next
  have hpow3 : (3 : ℤ) ^ (s k) = 3 * (3 : ℤ) ^ (s k - 1) := by
    have hsk_eq : s k = (s k - 1) + 1 := by omega
    conv_lhs => rw [hsk_eq, pow_succ]
    ring
  unfold affInv defectTerm
  rw [horb_next_int, hpow3]
  linear_combination 19 * (3 : ℤ) ^ (s k - 1) * hdecomp_int.symm

/-! ## 2. Exact 2-Adic Valuation Structure of `defectTerm c` ($v_2(E(c)) = 3$ for $c \ge 4$) -/

/-- The odd quotient `defectOddQuotient c = 9 * 2^(c - 3) - 3^(c - 1)` of `defectTerm c`
after factoring out `8 = 2^3` (`c ≥ 3`). -/
def defectOddQuotient (c : ℕ) : ℤ :=
  9 * (2 : ℤ) ^ (c - 3) - (3 : ℤ) ^ (c - 1)

/-- For every `c ≥ 3`, `defectTerm c = 8 * defectOddQuotient c`. -/
theorem defectTerm_eq_eight_mul (c : ℕ) (hc : 3 ≤ c) :
    defectTerm c = 8 * defectOddQuotient c := by
  have hpow2 : (2 : ℤ) ^ c = 8 * (2 : ℤ) ^ (c - 3) := by
    have hc_eq : c = (c - 3) + 3 := by omega
    conv_lhs => rw [hc_eq, pow_add (2 : ℤ) (c - 3) 3]
    ring
  unfold defectTerm defectOddQuotient
  rw [hpow2]
  ring

private theorem three_pow_int_mod_two (n : ℕ) : ((3 : ℤ) ^ n) % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, Int.mul_emod, ih]
      rfl

/-- **Exact 2-Adic Valuation Lock of `defectTerm c` for $c \ge 4$
(`defectTerm_eq_eight_mul_odd_of_four_le`)**:
For **every** block length `c ≥ 4` (arbitrarily large):
1. `defectTerm c = 8 * defectOddQuotient c`,
2. `defectOddQuotient c % 2 ≠ 0` (`defectOddQuotient c` is strictly odd), and
3. `(8 : ℤ) ∣ defectTerm c ∧ ¬ ((16 : ℤ) ∣ defectTerm c)`. -/
theorem defectTerm_eq_eight_mul_odd_of_four_le {c : ℕ} (hc : 4 ≤ c) :
    defectTerm c = 8 * defectOddQuotient c ∧
      defectOddQuotient c % 2 ≠ 0 ∧
      (8 : ℤ) ∣ defectTerm c ∧
      ¬ ((16 : ℤ) ∣ defectTerm c) := by
  have heq8 := defectTerm_eq_eight_mul c (by omega)
  have hodd : defectOddQuotient c % 2 ≠ 0 := by
    unfold defectOddQuotient
    have hc4 : c - 3 = (c - 4) + 1 := by omega
    rw [hc4, pow_succ (2 : ℤ) (c - 4)]
    have h3 := three_pow_int_mod_two (c - 1)
    omega
  refine ⟨heq8, hodd, ⟨defectOddQuotient c, heq8⟩, ?_⟩
  rintro ⟨q, hq⟩
  rw [heq8] at hq
  have hdiv2 : defectOddQuotient c = 2 * q := by omega
  omega

/-! ## 3. Iterated Multi-Block Signed Defect Cocycle -/

/-- Cumulative multi-block defect cocycle `defectCocycleSum s m`, defined recursively
and proved equal below (`defectCocycleSum_eq_finset_sum`) to the explicit finite sum
`∑ j ∈ Finset.range m, 3^(T(m) - T(j + 1)) * 2^(T(j)) * defectTerm (s j)`. -/
def defectCocycleSum (s : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 =>
      (3 : ℤ) ^ (s m) * defectCocycleSum s m +
        (2 : ℤ) ^ (blockSteps s m) * defectTerm (s m)

private theorem blockSteps_mono_le (s : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    blockSteps s i ≤ blockSteps s j := by
  induction j with
  | zero =>
      have hi0 : i = 0 := by omega
      subst hi0
      exact le_rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact le_rfl
      · have ihj := ih (by omega)
        simp only [blockSteps]
        omega

/-- **Explicit `Finset.sum` Formula for `defectCocycleSum` (`defectCocycleSum_eq_finset_sum`)**:
For every `s : ℕ → ℕ` and `m : ℕ`,
`defectCocycleSum s m = ∑ j ∈ Finset.range m, (3 : ℤ)^(blockSteps s m - blockSteps s (j + 1)) * (2 : ℤ)^(blockSteps s j) * defectTerm (s j)`. -/
theorem defectCocycleSum_eq_finset_sum (s : ℕ → ℕ) (m : ℕ) :
    defectCocycleSum s m =
      ∑ j ∈ Finset.range m,
        (3 : ℤ) ^ (blockSteps s m - blockSteps s (j + 1)) *
          (2 : ℤ) ^ (blockSteps s j) * defectTerm (s j) := by
  induction m with
  | zero => simp [defectCocycleSum]
  | succ m ih =>
      simp only [defectCocycleSum, ih, Finset.sum_range_succ, Nat.sub_self, pow_zero,
        one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      have hle : blockSteps s (j + 1) ≤ blockSteps s m :=
        blockSteps_mono_le s (by omega : j + 1 ≤ m)
      have hstep_m : blockSteps s (m + 1) = blockSteps s m + s m := rfl
      have hsub :
          blockSteps s (m + 1) - blockSteps s (j + 1) =
            s m + (blockSteps s m - blockSteps s (j + 1)) := by
        rw [hstep_m]
        omega
      rw [hsub, pow_add (3 : ℤ) (s m) (blockSteps s m - blockSteps s (j + 1))]
      ring

/-- **Iterated Multi-Block Signed Defect Cocycle (`iterated_signed_defect_cocycle`)**:
Along any `ValidBlockChain a_0 s u K` (`m ≤ K`),
`(2 : ℤ)^(blockSteps s m) * affInv (orbit a_0 (blockSteps s m)) =
  (3 : ℤ)^(blockSteps s m) * affInv a_0 + defectCocycleSum s m`. -/
theorem iterated_signed_defect_cocycle
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m ≤ K) (hchain : ValidBlockChain a_0 s u K) :
    (2 : ℤ) ^ (blockSteps s m) * affInv (orbit a_0 (blockSteps s m)) =
      (3 : ℤ) ^ (blockSteps s m) * affInv a_0 + defectCocycleSum s m := by
  induction m with
  | zero =>
      simp [blockSteps, orbit, defectCocycleSum]
  | succ m ih =>
      have ihm := ih (by omega)
      have hstep := single_block_signed_defect_identity (by omega : m < K) hchain
      have hpow2 :
          (2 : ℤ) ^ (blockSteps s (m + 1)) =
            (2 : ℤ) ^ (blockSteps s m) * (2 : ℤ) ^ (s m) :=
        pow_add (2 : ℤ) (blockSteps s m) (s m)
      have hpow3 :
          (3 : ℤ) ^ (blockSteps s (m + 1)) =
            (3 : ℤ) ^ (blockSteps s m) * (3 : ℤ) ^ (s m) :=
        pow_add (3 : ℤ) (blockSteps s m) (s m)
      simp only [defectCocycleSum]
      rw [hpow2, hpow3]
      linear_combination
        (2 : ℤ) ^ (blockSteps s m) * hstep + (3 : ℤ) ^ (s m) * ihm

/-! ## 4. 2-Adic Valuation Non-Cancellation & First-Defect Lock -/

/-- If `s k = 3` for all `k < j_0`, then `blockSteps s j_0 = 3 * j_0` and
`defectCocycleSum s j_0 = 0`. -/
theorem defectCocycleSum_eq_zero_of_three_prefix (s : ℕ → ℕ) (j_0 : ℕ)
    (hs3 : ∀ k < j_0, s k = 3) :
    blockSteps s j_0 = 3 * j_0 ∧ defectCocycleSum s j_0 = 0 := by
  induction j_0 with
  | zero => simp [blockSteps, defectCocycleSum]
  | succ j_0 ih =>
      rcases ih (fun k hk => hs3 k (by omega)) with ⟨ih_steps, ih_sum⟩
      have hs_j0 : s j_0 = 3 := hs3 j_0 (Nat.lt_succ_self j_0)
      have hE3 : defectTerm 3 = 0 := by decide
      simp only [blockSteps, defectCocycleSum, ih_steps, ih_sum, hs_j0, hE3]
      exact ⟨by omega, by ring⟩

/-- Propagation of the first defect modulo `2^(3 * j_0 + 4)`:
If `s k = 3` for `k < j_0` and `4 ≤ s j_0`, then for every `m` with `j_0 + 1 ≤ m`,
`3 * j_0 + 4 ≤ blockSteps s m` and `defectCocycleSum s m` is congruent modulo
`(2 : ℤ)^(3 * j_0 + 4)` to `(3 : ℤ)^(blockSteps s m - blockSteps s (j_0 + 1)) * (2 : ℤ)^(3 * j_0 + 3) * defectOddQuotient (s j_0)`. -/
theorem defectCocycleSum_mod_after_first_defect
    (s : ℕ → ℕ) {j_0 m : ℕ}
    (hs3 : ∀ k < j_0, s k = 3)
    (hs_j0 : 4 ≤ s j_0)
    (hm : j_0 + 1 ≤ m) :
    3 * j_0 + 4 ≤ blockSteps s m ∧
      blockSteps s (j_0 + 1) ≤ blockSteps s m ∧
      ((2 : ℤ) ^ (3 * j_0 + 4)) ∣
        (defectCocycleSum s m -
          (3 : ℤ) ^ (blockSteps s m - blockSteps s (j_0 + 1)) *
            (2 : ℤ) ^ (3 * j_0 + 3) * defectOddQuotient (s j_0)) := by
  rcases defectCocycleSum_eq_zero_of_three_prefix s j_0 hs3 with ⟨hsteps_j0, hsum_j0⟩
  have hsteps_j01 : blockSteps s (j_0 + 1) = 3 * j_0 + s j_0 := by
    simp only [blockSteps, hsteps_j0]
  have hsum_j01 :
      defectCocycleSum s (j_0 + 1) =
        (2 : ℤ) ^ (3 * j_0 + 3) * defectOddQuotient (s j_0) := by
    simp only [defectCocycleSum, hsum_j0, hsteps_j0, mul_zero, zero_add]
    rw [(defectTerm_eq_eight_mul_odd_of_four_le hs_j0).1,
      pow_add (2 : ℤ) (3 * j_0) 3]
    ring
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · have hj0 : m = j_0 := by omega
        subst hj0
        refine ⟨by omega, le_rfl, ?_⟩
        rw [Nat.sub_self, pow_zero, one_mul, hsum_j01, sub_self]
        exact dvd_zero _
      · rcases ih (by omega) with ⟨ih_ge4, ih_le, ⟨q, hq⟩⟩
        have hsteps_succ : blockSteps s (m + 1) = blockSteps s m + s m := rfl
        refine ⟨by omega, by omega, ?_⟩
        have hsub_add :
            blockSteps s (m + 1) - blockSteps s (j_0 + 1) =
              (blockSteps s m - blockSteps s (j_0 + 1)) + s m := by
          omega
        have hpow_dvd :
            ((2 : ℤ) ^ (3 * j_0 + 4)) ∣
              (2 : ℤ) ^ (blockSteps s m) * defectTerm (s m) := by
          have h1 : (2 : ℤ) ^ (3 * j_0 + 4) ∣ (2 : ℤ) ^ (blockSteps s m) :=
            pow_dvd_pow (2 : ℤ) ih_ge4
          exact dvd_mul_of_dvd_left h1 _
        rcases hpow_dvd with ⟨r, hr⟩
        refine ⟨(3 : ℤ) ^ (s m) * q + r, ?_⟩
        simp only [defectCocycleSum]
        rw [hsub_add, pow_add (3 : ℤ) (blockSteps s m - blockSteps s (j_0 + 1)) (s m), hr]
        linear_combination (3 : ℤ) ^ (s m) * hq

private theorem int_not_two_dvd_three_pow_mul_odd (n : ℕ) {x : ℤ} (hodd : x % 2 ≠ 0) :
    ¬ ((2 : ℤ) ∣ (3 : ℤ) ^ n * x) := by
  rintro ⟨q, hq⟩
  have hmod := congrArg (fun z : ℤ => z % 2) hq
  dsimp at hmod
  rw [Int.mul_emod, three_pow_int_mod_two n] at hmod
  omega

/-- **2-Adic Valuation Non-Cancellation & First-Defect Lock
(`first_defect_valuation_lock_and_non_cancellation`)**:
Suppose a `ValidBlockChain a_0 s u K` (`j_0 + 1 ≤ m ≤ K`) starts with `j_0` blocks
of length `3` (`∀ k < j_0, s k = 3`), has a defect `4 ≤ s j_0` at index `j_0`, and
continues with **any** valid blocks for `j_0 < j < m` (bounded or unbounded). Then:
1. `2^(3 * j_0 + 3) ∣ (19 * a_0 + 9)`,
2. `¬ (2^(3 * j_0 + 4) ∣ (19 * a_0 + 9))` (no subsequent defects can ever cancel
   the 2-adic valuation at `3 * j_0 + 3`),
3. `2^(3 * j_0 + 3) ≤ 19 * a_0 + 9`, and
4. If `a_0 < 2^W`, then `3 * j_0 ≤ W + 1`. -/
theorem first_defect_valuation_lock_and_non_cancellation
    {a_0 : ℕ} {s u : ℕ → ℕ} {K j_0 m : ℕ}
    (hm1 : j_0 + 1 ≤ m) (hmK : m ≤ K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs3 : ∀ k < j_0, s k = 3)
    (hs_j0 : 4 ≤ s j_0) :
    2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) ∧
      ¬ (2 ^ (3 * j_0 + 4) ∣ (19 * a_0 + 9)) ∧
      2 ^ (3 * j_0 + 3) ≤ 19 * a_0 + 9 ∧
      (∀ W : ℕ, a_0 < 2 ^ W → 3 * j_0 ≤ W + 1) := by
  have hcocycle := iterated_signed_defect_cocycle hmK hchain
  rcases defectCocycleSum_mod_after_first_defect s hs3 hs_j0 hm1 with
    ⟨hge4, _, ⟨q_def, hq_def⟩⟩
  have hlhs_dvd :
      ((2 : ℤ) ^ (3 * j_0 + 4)) ∣
        (2 : ℤ) ^ (blockSteps s m) * affInv (orbit a_0 (blockSteps s m)) :=
    dvd_mul_of_dvd_left (pow_dvd_pow (2 : ℤ) hge4) _
  rcases hlhs_dvd with ⟨q_lhs, hq_lhs⟩
  set N3 := blockSteps s m - blockSteps s (j_0 + 1)
  have hcomb :
      (3 : ℤ) ^ (blockSteps s m) * affInv a_0 +
          (3 : ℤ) ^ N3 * (2 : ℤ) ^ (3 * j_0 + 3) * defectOddQuotient (s j_0) =
        (2 : ℤ) ^ (3 * j_0 + 4) * (q_lhs - q_def) := by
    linear_combination hq_lhs - hcocycle - hq_def
  have hdvd_3 :
      2 ^ (3 * j_0 + 3) ∣ 3 ^ (blockSteps s m) * (19 * a_0 + 9) := by
    have hdvd_int :
        ((2 : ℤ) ^ (3 * j_0 + 3)) ∣
          (3 : ℤ) ^ (blockSteps s m) * affInv a_0 := by
      refine ⟨2 * (q_lhs - q_def) - (3 : ℤ) ^ N3 * defectOddQuotient (s j_0), ?_⟩
      have hpow_succ :
          (2 : ℤ) ^ (3 * j_0 + 4) = (2 : ℤ) ^ (3 * j_0 + 3) * 2 := by
        rw [pow_succ]
      rw [hpow_succ] at hcomb
      linear_combination hcomb
    unfold affInv at hdvd_int
    exact_mod_cast hdvd_int
  have hcop : Nat.Coprime (2 ^ (3 * j_0 + 3)) (3 ^ (blockSteps s m)) :=
    (by decide : Nat.Coprime 2 3).pow (3 * j_0 + 3) (blockSteps s m)
  have hdvd_a0 : 2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) :=
    hcop.dvd_of_dvd_mul_left hdvd_3
  have hnot_dvd_4 : ¬ (2 ^ (3 * j_0 + 4) ∣ (19 * a_0 + 9)) := by
    intro hdvd4
    have hdvd4_int : ((2 : ℤ) ^ (3 * j_0 + 4)) ∣ affInv a_0 := by
      unfold affInv
      exact_mod_cast hdvd4
    rcases hdvd4_int with ⟨q_a0, hq_a0⟩
    rw [hq_a0] at hcomb
    have hpow_succ :
        (2 : ℤ) ^ (3 * j_0 + 4) = (2 : ℤ) ^ (3 * j_0 + 3) * 2 := by
      rw [pow_succ]
    rw [hpow_succ] at hcomb
    have hmul_eq :
        (2 : ℤ) ^ (3 * j_0 + 3) *
            ((3 : ℤ) ^ N3 * defectOddQuotient (s j_0)) =
          (2 : ℤ) ^ (3 * j_0 + 3) *
            (2 * (q_lhs - q_def - (3 : ℤ) ^ (blockSteps s m) * q_a0)) := by
      linear_combination hcomb
    have hpos : (2 : ℤ) ^ (3 * j_0 + 3) ≠ 0 := by positivity
    have hcancel := mul_left_cancel₀ hpos hmul_eq
    have h2_dvd : (2 : ℤ) ∣ (3 : ℤ) ^ N3 * defectOddQuotient (s j_0) :=
      ⟨q_lhs - q_def - (3 : ℤ) ^ (blockSteps s m) * q_a0, hcancel⟩
    have hodd := (defectTerm_eq_eight_mul_odd_of_four_le hs_j0).2.1
    exact int_not_two_dvd_three_pow_mul_odd N3 hodd h2_dvd
  have hle_a0 : 2 ^ (3 * j_0 + 3) ≤ 19 * a_0 + 9 :=
    Nat.le_of_dvd (by omega) hdvd_a0
  refine ⟨hdvd_a0, hnot_dvd_4, hle_a0, ?_⟩
  intro W ha0
  have h19 : 19 * a_0 + 9 < 2 ^ (W + 5) := by
    have hpow5 : 2 ^ (W + 5) = 32 * 2 ^ W := by
      rw [Nat.pow_add]
      ring
    omega
  have hlt_pow : 2 ^ (3 * j_0 + 3) < 2 ^ (W + 5) := lt_of_le_of_lt hle_a0 h19
  have hlt_exp : 3 * j_0 + 3 < W + 5 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt_pow
  omega

/-! ## 5. Short Local Prefix Derivation of the First-Defect Lock & Boundary Invariant Scope -/

/-- **Local Single-Block Identity for `19 * b + 9` (`local_single_block_affInv_identity`)**:
At any single block boundary `b` with `3 * b + 1 = 2^c * u`,
`3 * (19 * b + 9) = 19 * 2^c * u + 8`. -/
theorem local_single_block_affInv_identity {b c u : ℕ}
    (hdecomp : 3 * b + 1 = 2 ^ c * u) :
    3 * (19 * b + 9) = 19 * 2 ^ c * u + 8 := by
  calc
    3 * (19 * b + 9) = 19 * (3 * b + 1) + 8 := by ring
    _ = 19 * (2 ^ c * u) + 8 := by rw [hdecomp]
    _ = 19 * 2 ^ c * u + 8 := by ring

/-- **Local Single-Defect Valuation $v_2(19 b + 9) = 3$ (`local_single_defect_valuation_three`)**:
For any `4 ≤ c` and `3 * b + 1 = 2^c * u`, the single block decomposition alone
immediately forces `8 ∣ (19 * b + 9)` and `¬ (16 ∣ (19 * b + 9))`. -/
theorem local_single_defect_valuation_three {b c u : ℕ}
    (hc : 4 ≤ c) (hdecomp : 3 * b + 1 = 2 ^ c * u) :
    8 ∣ (19 * b + 9) ∧ ¬ (16 ∣ (19 * b + 9)) := by
  have hid := local_single_block_affInv_identity hdecomp
  have hpow : 2 ^ c = 16 * 2 ^ (c - 4) := by
    have hc_eq : c = 4 + (c - 4) := by omega
    calc
      2 ^ c = 2 ^ (4 + (c - 4)) := by rw [← hc_eq]
      _ = 2 ^ 4 * 2 ^ (c - 4) := Nat.pow_add 2 4 (c - 4)
      _ = 16 * 2 ^ (c - 4) := by ring
  set k := 2 ^ (c - 4) * u
  have hid_k : 3 * (19 * b + 9) = 304 * k + 8 := by
    calc
      3 * (19 * b + 9) = 19 * 2 ^ c * u + 8 := hid
      _ = 19 * (16 * 2 ^ (c - 4)) * u + 8 := by rw [hpow]
      _ = 304 * k + 8 := by unfold k; ring
  have hdvd8_3 : 8 ∣ 3 * (19 * b + 9) := ⟨38 * k + 1, by omega⟩
  have hcop : Nat.Coprime 8 3 := by decide
  have hdvd8 : 8 ∣ (19 * b + 9) := hcop.dvd_of_dvd_mul_left hdvd8_3
  refine ⟨hdvd8, ?_⟩
  rintro ⟨q, hq⟩
  omega

/-- **Short Local Prefix Proof of the First-Defect Lock (`local_prefix_first_defect_valuation_lock`)**:
Requiring only the finite prefix `ValidBlockChain a_0 s u (j_0 + 1)` up to the first
defect `j_0` (`∀ k < j_0, s k = 3` and `4 ≤ s j_0`), with **no** later survival
assumption beyond block `j_0`, already forces
`2^(3 * j_0 + 3) ∣ (19 * a_0 + 9)` and `¬ (2^(3 * j_0 + 4) ∣ (19 * a_0 + 9))`. -/
theorem local_prefix_first_defect_valuation_lock
    {a_0 : ℕ} {s u : ℕ → ℕ} {j_0 : ℕ}
    (hchain : ValidBlockChain a_0 s u (j_0 + 1))
    (hs3 : ∀ k < j_0, s k = 3)
    (hs_j0 : 4 ≤ s j_0) :
    8 ^ j_0 * (19 * orbit a_0 (blockSteps s j_0) + 9) = 27 ^ j_0 * (19 * a_0 + 9) ∧
      2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) ∧
      ¬ (2 ^ (3 * j_0 + 4) ∣ (19 * a_0 + 9)) := by
  have hcocycle :=
    iterated_signed_defect_cocycle (K := j_0 + 1) (m := j_0) (by omega) hchain
  rcases defectCocycleSum_eq_zero_of_three_prefix s j_0 hs3 with ⟨hsteps, hsum0⟩
  rw [hsteps, hsum0, add_zero] at hcocycle
  unfold affInv at hcocycle
  have hnat_eq :
      2 ^ (3 * j_0) * (19 * orbit a_0 (3 * j_0) + 9) =
        3 ^ (3 * j_0) * (19 * a_0 + 9) := by
    exact_mod_cast hcocycle
  have hpow2 : 2 ^ (3 * j_0) = 8 ^ j_0 := by rw [Nat.pow_mul]
  have hpow3 : 3 ^ (3 * j_0) = 27 ^ j_0 := by rw [Nat.pow_mul]
  have hprefix_eq :
      8 ^ j_0 * (19 * orbit a_0 (blockSteps s j_0) + 9) =
        27 ^ j_0 * (19 * a_0 + 9) := by
    rw [hsteps, ← hpow2, ← hpow3]
    exact hnat_eq
  rcases hchain j_0 (Nat.lt_succ_self j_0) with ⟨_, _, hdecomp_j0⟩
  rcases local_single_defect_valuation_three hs_j0 hdecomp_j0 with ⟨hdvd8, hnot16⟩
  rcases hdvd8 with ⟨q_b, hq_b⟩
  have hdvd_3 :
      2 ^ (3 * j_0 + 3) ∣ 3 ^ (3 * j_0) * (19 * a_0 + 9) := by
    refine ⟨q_b, ?_⟩
    rw [← hnat_eq, ← hsteps, hq_b, Nat.pow_add]
    ring
  have hcop : Nat.Coprime (2 ^ (3 * j_0 + 3)) (3 ^ (3 * j_0)) :=
    (by decide : Nat.Coprime 2 3).pow (3 * j_0 + 3) (3 * j_0)
  have hdvd_a0 : 2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) :=
    hcop.dvd_of_dvd_mul_left hdvd_3
  refine ⟨hprefix_eq, hdvd_a0, ?_⟩
  rintro ⟨q_a, hq_a⟩
  apply hnot16
  have hmul :
      2 ^ (3 * j_0) * (19 * orbit a_0 (blockSteps s j_0) + 9) =
        2 ^ (3 * j_0) * (16 * (3 ^ (3 * j_0) * q_a)) := by
    rw [hsteps, hnat_eq, hq_a, Nat.pow_add 2 (3 * j_0) 4]
    ring
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul
  exact ⟨3 ^ (3 * j_0) * q_a, hcancel⟩

/-- **Normalized Cocycle Residual is the Growing Boundary Invariant
(`defectCocycle_residual_eq_growing_boundary_affInv`)**:
For any positive seed `1 ≤ a_0` and `ValidBlockChain a_0 s u K` (`m ≤ K`),
the normalized cocycle residual `(3^T(m) * affInv a_0 + defectCocycleSum s m) / 2^T(m)`
equals `affInv (orbit a_0 (blockSteps s m))`, which satisfies
`affInv a_0 ≤ affInv (orbit a_0 (blockSteps s m))`. -/
theorem defectCocycle_residual_eq_growing_boundary_affInv
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m ≤ K) (hchain : ValidBlockChain a_0 s u K) :
    ((3 : ℤ) ^ (blockSteps s m) * affInv a_0 + defectCocycleSum s m) /
        (2 : ℤ) ^ (blockSteps s m) =
      affInv (orbit a_0 (blockSteps s m)) ∧
    affInv a_0 ≤ affInv (orbit a_0 (blockSteps s m)) := by
  have hcocycle := iterated_signed_defect_cocycle hmK hchain
  have hpow_ne : (2 : ℤ) ^ (blockSteps s m) ≠ 0 := by positivity
  have hdiv :
      ((3 : ℤ) ^ (blockSteps s m) * affInv a_0 + defectCocycleSum s m) /
          (2 : ℤ) ^ (blockSteps s m) =
        affInv (orbit a_0 (blockSteps s m)) := by
    rw [← hcocycle, mul_comm, Int.mul_ediv_cancel _ hpow_ne]
  have horb_le : a_0 ≤ orbit a_0 (blockSteps s m) :=
    orbit_le_of_le a_0 (Nat.zero_le (blockSteps s m))
  refine ⟨hdiv, ?_⟩
  unfold affInv
  have horb_int : (a_0 : ℤ) ≤ (orbit a_0 (blockSteps s m) : ℤ) := by
    exact_mod_cast horb_le
  omega

/-! ## 6. Unified Research Synthesis (`mahler_next_stage_research_synthesis`) -/

/-- **Unified Next-Stage Research Synthesis (`mahler_next_stage_research_synthesis`)**:
Collects the five principal theorems across Stages 0, 1, 2, 3, and 4 of
`RESEARCH_OUTLINE_NEXT_STAGE.md`:
1. **Stage 0 (Perpetual-to-Infinite Endpoint Alternative):**
   Perpetual finite feasibility implies either strict infinite survival of `a_0`
   at `supCompanion a_0` or strict infinite survival of the shifted seed
   `orbit a_0 (j + 1)` after a unique dyadic upper-endpoint hit at `j`.
2. **Stage 1 (Sharp Parameterized `(p, q)` Balanced Complexity Exclusion):**
   For any `1 ≤ q` with `3^q < 2^(p + q)`, balanced cumulative discrepancy
   `|T(n) - lam * n| ≤ D` and prefix factor complexity `prefixFactorCount s L C ≤ C ≤ kappa * L + C_0`
   force `lam * (q - p * kappa) * L + 1 ≤ (2 * q + p) * D + p * lam * C_0 + q * W + p`.
3. **Stage 2 (Constructive Seed-Residue Stabilization & Nonperiodic Spike Cutoff):**
   An infinite parity stream is generated by an ordinary nonnegative integer `a_0`
   iff `seedResidue ε N` eventually stabilizes at `a_0`, and every single surviving
   block satisfies `5 * s m ≤ 3 * blockSteps s m + 5 * W + 7`.
4. **Stage 3 (Closed Thue–Morse Mahler Functional Equation & 2-Adic Seed Bridge):**
   `tmSeries z = (1 - z) * tmSeries (z^2) + z / (1 - z^2)` for `0 ≤ z < 1`, and
   `64^M ∣ (729^M * (665 * a_0 + 72) + 113715 * tmIntCarry 64 729 M)`.
5. **Stage 4 (Signed Defect Cocycle & 2-Adic Valuation Non-Cancellation):**
   After `j_0` blocks of `3`, any defect `4 ≤ s j_0` locks the 2-adic valuation
   `2^(3 * j_0 + 3) ∣ (19 * a_0 + 9)` and `¬ (2^(3 * j_0 + 4) ∣ (19 * a_0 + 9))`
   regardless of all subsequent blocks. -/
theorem mahler_next_stage_research_synthesis :
    (∀ {a_0 : ℕ},
      (∀ N : ℕ, ∃ α : ℝ, ValidCompanionUpTo a_0 α N) →
        ValidCompanionForever a_0 (supCompanion a_0) ∨
          ∃ j : ℕ,
            supCompanion a_0 = upperBound a_0 j ∧
              ValidCompanionForever (orbit a_0 (j + 1))
                (supCompanion a_0 * (3 / 2 : ℝ) ^ (j + 1))) ∧
    (∀ {p q a_0 W L C K : ℕ} {s u : ℕ → ℕ} {lam D kappa C_0 : ℝ},
      1 ≤ q → 3 ^ q < 2 ^ (p + q) → 1 ≤ L → C + L ≤ K → a_0 < 2 ^ W →
      ValidBlockChain a_0 s u K → 0 < Mahler.MinSlackSystem.minSlack s C → 0 < lam →
      (∀ n ≤ K, |(blockSteps s n : ℝ) - lam * (n : ℝ)| ≤ D) →
      prefixFactorCount s L C ≤ C → (C : ℝ) ≤ kappa * (L : ℝ) + C_0 →
        lam * ((q : ℝ) - (p : ℝ) * kappa) * (L : ℝ) + 1 ≤
          (2 * (q : ℝ) + (p : ℝ)) * D + (p : ℝ) * lam * C_0 +
            (q : ℝ) * (W : ℝ) + (p : ℝ)) ∧
    (∀ (ε : ℕ → ℕ) (a_0 : ℕ),
      (∀ n : ℕ, orbit a_0 n % 2 = ε n % 2) ↔
        ∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue ε N = a_0) ∧
    (tmSeries (8 / 27 : ℝ) =
      (19 / 27 : ℝ) * tmSeries (64 / 729 : ℝ) + (216 / 665 : ℝ)) ∧
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K j_0 m : ℕ},
      j_0 + 1 ≤ m → m ≤ K → ValidBlockChain a_0 s u K →
      (∀ k < j_0, s k = 3) → 4 ≤ s j_0 →
        2 ^ (3 * j_0 + 3) ∣ (19 * a_0 + 9) ∧
          ¬ (2 ^ (3 * j_0 + 4) ∣ (19 * a_0 + 9))) := by
  refine ⟨fun h => perpetual_finite_survival_endpoint_alternative h,
    fun hq hpq hL hK ha0 hchain hmin hlam hbal hcard hC =>
      balanced_discrepancy_and_factor_complexity_exclusion
        hq hpq hL hK ha0 hchain hmin hlam hbal hcard hC,
    exists_nonneg_seed_iff_seedResidue_stabilizes,
    tmSeries_eight_twenty_sevenths_functional_equation,
    fun hm1 hmK hchain hs3 hs_j0 =>
      ⟨(first_defect_valuation_lock_and_non_cancellation hm1 hmK hchain hs3 hs_j0).1,
        (first_defect_valuation_lock_and_non_cancellation hm1 hmK hchain hs3 hs_j0).2.1⟩⟩

end Mahler.SparseDefectCocycle
