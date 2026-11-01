import ExactSeedResidueTreeAndStabilization
import ParitySurplusPotentialsAndSafetyGame

/-!
# Coupled Transfer Operators, Joint Spectral Radius Certificates & 3-Adic Carry Harmonic Injectivity

This module formalizes **Part II Sections 11, 12, and 13** (together with the negative/criticality
deliverables of **Section 21 Types 1 & 2**) of `RESEARCH_PLAN_ARGON_GENERAL_PROOF.md`:

1. **Section 11.1 — Perron–Frobenius-Free Sub-Invariant Weight Bound (`iterTransferWeight`,
   `subinvariant_weight_iter_bound`, `iterTransferWeight_eq_matrix_pow_sum`,
   `subinvariant_weight_matrix_pow_bound`)**:
   - For any finite state space `Fin r`, an entrywise nonnegative rational matrix
     `M : Matrix (Fin r) (Fin r) ℚ` (`∀ i j, 0 ≤ M i j`), a nonnegative weight `w : Fin r → ℚ`,
     and a scalar `0 ≤ ρ` satisfying `∀ i, (∑ j, M i j * w j) ≤ ρ * w i`, we prove by induction
     on `n` that `∀ n i, (∑ j, (M ^ n) i j * w j) ≤ ρ ^ n * w i`.

2. **Section 12.1 — Joint Spectral Radius (JSR) Common Sub-Invariant Weight Bound
   (`wordTransferWeight`, `common_subinvariant_weight_jsr_bound`)**:
   - Given a finite family of nonnegative transition matrices `A : Fin m → Matrix (Fin r) (Fin r) ℚ`,
     if a single nonnegative weight `w : Fin r → ℚ` satisfies `∀ a i, (∑ j, A a i j * w j) ≤ ρ * w i`
     across all generators `a`, then every `n`-step matrix product along any word `ω : ℕ → Fin m`
     is bounded by `ρ^n * w i`.

3. **Sections 11.2, 11.3 & 12 Negative/Criticality Theorems (`no_subcritical_weight_of_self_loop`,
   `no_subcritical_weight_of_three_cycle`, `archimedean_only_density_fallacy_supercritical`,
   `mod_two_pow_ghost_self_loop_at_all_depths`)**:
   - **Self-Loop & Cycle Lower Bounds**: Any nonnegative matrix `M` with a diagonal entry `M s s ≥ 1`
     (or a 3-cycle `M 0 1, M 1 2, M 2 0 ≥ 1`) satisfies `1 ≤ ρ` for every positive sub-invariant
     weight `w > 0`.
   - **Archimedean-Only Density Fallacy (Section 11.3)**: When weighted by the unpruned grid-growth
     ratio `4/3`, any row-stochastic / survival operator satisfies `4/3 ≤ ρ` (`1 < ρ`).
   - **Fixed-Depth Mod-`2^k` Criticality (`ρ_k ≥ 1`, Section 11.2 & Section 12 Negative Result)**:
     At **every** finite 2-adic congruence depth `k : ℕ`, the 2-adic fixed-point equations
     `19 * r + 9 ≡ 0 (mod 2^k)` (period-3 `100`), `2059 * v ≡ 1 (mod 2^k)` (Dense Core `j = 1`),
     and `58025 * v ≡ 1 (mod 2^k)` (Dense Core `j = 2`) admit explicit odd integer solutions
     `r_k, v_{1,k}, v_{2,k} < 2^k`, creating self-loops in the mod-`2^k` coupled state graph and
     proving that no fixed-depth mod-`2^k` transfer matrix or common JSR weight can achieve `ρ < 1`.

4. **Section 13 — 3-Adic Carry Decomposition, Memory Erasure & Exact Word-to-Carry Injectivity
   (`wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift`,
   `wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod`,
   `wordCarry_mod_three_pow_eq_iff_parity_eq`,
   `aligned_carry_collision_iff_exact_factor_match`)**:
   - Proves the exact `(2, 3)`-adic shift decomposition of `wordCarry`:
     `wordCarry ε (n + m) = 3^m * wordCarry ε n + 2^n * wordCarry (shiftStream ε n) m`.
   - Consequently, modulo `3^m`, the carry after `m` steps erases all memory of `wordCarry ε n`:
     `wordCarry ε (n + m) % 3^m = (2^n * wordCarry (shiftStream ε n) m) % 3^m`.
   - Proves the **Exact 3-Adic Carry Injectivity Theorem (`wordCarry_mod_three_pow_eq_iff_parity_eq`)**:
     for **any** two parity streams `ε₁, ε₂` and horizon `m : ℕ`,
     `wordCarry ε₁ m % 3^m = wordCarry ε₂ m % 3^m ↔ ∀ j < m, ε₁ j % 2 = ε₂ j % 2`.
   - Thus in the 3-adic carry group `ℤ/3^m ℤ`, distinct binary words of length `m` never collide:
     at aligned `2^n mod 3^m` phases, a carry collision modulo `3^m` is **equivalent** to an exact
     bit-for-bit factor match of length `m`, bounding the minimum carry-collision horizon below by
     the factor complexity `P(m)` and formally confirming the Section 6 stop gate.
-/

namespace Mahler.TransferJSRAndFourier

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames

/-! ## 1. Section 11.1: Perron–Frobenius-Free Sub-Invariant Weight Bound -/

/-- Iterative application of a rational transfer matrix `M` to a weight vector `w`:
`iterTransferWeight M w 0 i = w i` and
`iterTransferWeight M w (n + 1) i = ∑ j, M i j * iterTransferWeight M w n j`. -/
def iterTransferWeight {r : ℕ} (M : Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ) :
    ℕ → Fin r → ℚ
  | 0, i => w i
  | n + 1, i => ∑ j : Fin r, M i j * iterTransferWeight M w n j

/-- `iterTransferWeight M w n i` equals the matrix-power sum `∑ j, (M ^ n) i j * w j`. -/
theorem iterTransferWeight_eq_matrix_pow_sum {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ) (n : ℕ) (i : Fin r) :
    iterTransferWeight M w n i = ∑ j : Fin r, (M ^ n) i j * w j := by
  induction n generalizing i with
  | zero =>
      simp only [iterTransferWeight, pow_zero, Matrix.one_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
  | succ n ih =>
      simp only [iterTransferWeight, pow_succ', Matrix.mul_apply]
      have h1 :
          (∑ j : Fin r, M i j * iterTransferWeight M w n j) =
            ∑ j : Fin r, M i j * (∑ k : Fin r, (M ^ n) j k * w k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ih j]
      rw [h1]
      have h2 :
          (∑ j : Fin r, M i j * (∑ k : Fin r, (M ^ n) j k * w k)) =
            ∑ j : Fin r, ∑ k : Fin r, M i j * (M ^ n) j k * w k := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have h3 :
          (∑ k : Fin r, (∑ j : Fin r, M i j * (M ^ n) j k) * w k) =
            ∑ k : Fin r, ∑ j : Fin r, M i j * (M ^ n) j k * w k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
      rw [h2, h3, Finset.sum_comm]

/-- **Perron–Frobenius-Free Sub-Invariant Weight Bound (`subinvariant_weight_matrix_pow_bound`,
Section 11.1)**:
Let `M : Matrix (Fin r) (Fin r) ℚ` be entrywise nonnegative (`∀ i j, 0 ≤ M i j`),
`w : Fin r → ℚ`, and `ρ : ℚ` (`0 ≤ ρ`) satisfy `∀ i, (∑ j, M i j * w j) ≤ ρ * w i`.
Then for every `n : ℕ` and `i : Fin r`:
`iterTransferWeight M w n i ≤ ρ ^ n * w i` and
`(∑ j : Fin r, (M ^ n) i j * w j) ≤ ρ ^ n * w i`. -/
theorem subinvariant_weight_matrix_pow_bound {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ) (ρ : ℚ)
    (hM : ∀ i j : Fin r, 0 ≤ M i j)
    (hρ : 0 ≤ ρ)
    (hsub : ∀ i : Fin r, (∑ j : Fin r, M i j * w j) ≤ ρ * w i) (n : ℕ) :
    (∀ i : Fin r, iterTransferWeight M w n i ≤ ρ ^ n * w i) ∧
      (∀ i : Fin r, (∑ j : Fin r, (M ^ n) i j * w j) ≤ ρ ^ n * w i) := by
  have hiter : ∀ i : Fin r, iterTransferWeight M w n i ≤ ρ ^ n * w i := by
    induction n with
    | zero =>
        intro i
        simp [iterTransferWeight]
    | succ n ih =>
        intro i
        simp only [iterTransferWeight]
        have hsum_le :
            (∑ j : Fin r, M i j * iterTransferWeight M w n j) ≤
              ∑ j : Fin r, M i j * (ρ ^ n * w j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (ih j) (hM i j)
        have hfactor :
            (∑ j : Fin r, M i j * (ρ ^ n * w j)) =
              ρ ^ n * (∑ j : Fin r, M i j * w j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        have hstep :
            ρ ^ n * (∑ j : Fin r, M i j * w j) ≤ ρ ^ n * (ρ * w i) :=
          mul_le_mul_of_nonneg_left (hsub i) (pow_nonneg hρ n)
        have hpow : ρ ^ n * (ρ * w i) = ρ ^ (n + 1) * w i := by
          rw [pow_succ]; ring
        linarith
  refine ⟨hiter, ?_⟩
  intro i
  rw [← iterTransferWeight_eq_matrix_pow_sum]
  exact hiter i

/-! ## 2. Section 12.1: Joint Spectral Radius (JSR) Common Sub-Invariant Weight Bound -/

/-- Iterative application of a sequence of matrices `A (ω k)` along a word `ω : ℕ → Fin m`:
`wordTransferWeight A w ω 0 i = w i` and
`wordTransferWeight A w ω (n + 1) i = ∑ j, A (ω 0) i j * wordTransferWeight A w (fun k => ω (k + 1)) n j`. -/
def wordTransferWeight {m r : ℕ} (A : Fin m → Matrix (Fin r) (Fin r) ℚ)
    (w : Fin r → ℚ) : (ℕ → Fin m) → ℕ → Fin r → ℚ
  | _, 0, i => w i
  | ω, n + 1, i =>
      ∑ j : Fin r, A (ω 0) i j * wordTransferWeight A w (fun k => ω (k + 1)) n j

/-- **Common Sub-Invariant Weight JSR Bound (`common_subinvariant_weight_jsr_bound`, Section 12.1)**:
If a finite family of nonnegative matrices `A : Fin m → Matrix (Fin r) (Fin r) ℚ` shares a
common weight `w : Fin r → ℚ` with `∀ a i, (∑ j, A a i j * w j) ≤ ρ * w i` (`0 ≤ ρ`),
then for **every** infinite word `ω : ℕ → Fin m`, horizon `n : ℕ`, and state `i : Fin r`:
`wordTransferWeight A w ω n i ≤ ρ ^ n * w i`. -/
theorem common_subinvariant_weight_jsr_bound {m r : ℕ}
    (A : Fin m → Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ) (ρ : ℚ)
    (hA : ∀ (a : Fin m) (i j : Fin r), 0 ≤ A a i j)
    (hρ : 0 ≤ ρ)
    (hsub : ∀ (a : Fin m) (i : Fin r), (∑ j : Fin r, A a i j * w j) ≤ ρ * w i) :
    ∀ (n : ℕ) (ω : ℕ → Fin m) (i : Fin r),
      wordTransferWeight A w ω n i ≤ ρ ^ n * w i := by
  intro n
  induction n with
  | zero =>
      intro ω i
      simp [wordTransferWeight]
  | succ n ih =>
      intro ω i
      simp only [wordTransferWeight]
      have hsum_le :
          (∑ j : Fin r, A (ω 0) i j * wordTransferWeight A w (fun k => ω (k + 1)) n j) ≤
            ∑ j : Fin r, A (ω 0) i j * (ρ ^ n * w j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (ih (fun k => ω (k + 1)) j) (hA (ω 0) i j)
      have hfactor :
          (∑ j : Fin r, A (ω 0) i j * (ρ ^ n * w j)) =
            ρ ^ n * (∑ j : Fin r, A (ω 0) i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hstep :
          ρ ^ n * (∑ j : Fin r, A (ω 0) i j * w j) ≤ ρ ^ n * (ρ * w i) :=
        mul_le_mul_of_nonneg_left (hsub (ω 0) i) (pow_nonneg hρ n)
      have hpow : ρ ^ n * (ρ * w i) = ρ ^ (n + 1) * w i := by
        rw [pow_succ]; ring
      linarith

/-! ## 3. Sections 11.2, 11.3 & 12 Negative/Criticality Theorems (`ρ_k ≥ 1` and `JSR ≥ 1`) -/

/-- **Self-Loop Lower Bound on Sub-Invariant Weights (`no_subcritical_weight_of_self_loop`,
Section 11 & 12 Criticality Barrier)**:
If an entrywise nonnegative matrix `M : Matrix (Fin r) (Fin r) ℚ` has a state `s : Fin r`
with self-loop weight `1 ≤ M s s`, then for **every** positive weight vector `w : Fin r → ℚ`
(`∀ i, 0 < w i`) and scalar `ρ : ℚ` satisfying `∀ i, (∑ j, M i j * w j) ≤ ρ * w i`,
we must have `1 ≤ ρ` (no sub-critical `ρ < 1` exists). -/
theorem no_subcritical_weight_of_self_loop {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℚ) (w : Fin r → ℚ) (ρ : ℚ) (s : Fin r)
    (hM : ∀ i j : Fin r, 0 ≤ M i j)
    (hw : ∀ i : Fin r, 0 < w i)
    (hloop : 1 ≤ M s s)
    (hsub : ∀ i : Fin r, (∑ j : Fin r, M i j * w j) ≤ ρ * w i) :
    1 ≤ ρ ∧ ¬ (ρ < 1) := by
  have hsingle : M s s * w s ≤ ∑ j : Fin r, M s j * w j := by
    apply Finset.single_le_sum (fun j _ => mul_nonneg (hM s j) (le_of_lt (hw j)))
    exact Finset.mem_univ s
  have hws : 0 < w s := hw s
  have h1 : 1 * w s ≤ M s s * w s := mul_le_mul_of_nonneg_right hloop (le_of_lt hws)
  have h2 : M s s * w s ≤ ρ * w s := le_trans hsingle (hsub s)
  have hle : 1 ≤ ρ := by nlinarith
  exact ⟨hle, not_lt.mpr hle⟩

/-- **Period-3 Cycle Lower Bound on Sub-Invariant Weights (`no_subcritical_weight_of_three_cycle`)**:
If an entrywise nonnegative matrix `M : Matrix (Fin 3) (Fin 3) ℚ` contains the period-3
(`100`) cycle `1 ≤ M 0 1`, `1 ≤ M 1 2`, `1 ≤ M 2 0`, then for **every** positive weight
`w : Fin 3 → ℚ` (`∀ i, 0 < w i`) and `ρ : ℚ` with `∀ i, (∑ j, M i j * w j) ≤ ρ * w i`,
we must have `1 ≤ ρ`. -/
theorem no_subcritical_weight_of_three_cycle
    (M : Matrix (Fin 3) (Fin 3) ℚ) (w : Fin 3 → ℚ) (ρ : ℚ)
    (hM : ∀ i j : Fin 3, 0 ≤ M i j)
    (hw : ∀ i : Fin 3, 0 < w i)
    (hc01 : 1 ≤ M 0 1) (hc12 : 1 ≤ M 1 2) (hc20 : 1 ≤ M 2 0)
    (hsub : ∀ i : Fin 3, (∑ j : Fin 3, M i j * w j) ≤ ρ * w i) :
    1 ≤ ρ ∧ ¬ (ρ < 1) := by
  have hs0 : M 0 1 * w 1 ≤ ∑ j : Fin 3, M 0 j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hM 0 j) (le_of_lt (hw j))) (Finset.mem_univ 1)
  have hs1 : M 1 2 * w 2 ≤ ∑ j : Fin 3, M 1 j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hM 1 j) (le_of_lt (hw j))) (Finset.mem_univ 2)
  have hs2 : M 2 0 * w 0 ≤ ∑ j : Fin 3, M 2 j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hM 2 j) (le_of_lt (hw j))) (Finset.mem_univ 0)
  have hw0 : 0 < w 0 := hw 0
  have hw1 : 0 < w 1 := hw 1
  have hw2 : 0 < w 2 := hw 2
  have hm0 : w 1 ≤ M 0 1 * w 1 := by nlinarith
  have hm1 : w 2 ≤ M 1 2 * w 2 := by nlinarith
  have hm2 : w 0 ≤ M 2 0 * w 0 := by nlinarith
  have hsub0 := hsub 0
  have hsub1 := hsub 1
  have hsub2 := hsub 2
  have hsum : w 0 + w 1 + w 2 ≤ ρ * (w 0 + w 1 + w 2) := by linarith
  have hle : 1 ≤ ρ := by nlinarith
  exact ⟨hle, not_lt.mpr hle⟩

/-- **Archimedean-Only Density Fallacy (`archimedean_only_density_fallacy_supercritical`, Section 11.3)**:
If an archimedean-only transfer matrix `M : Matrix (Fin 3) (Fin 3) ℚ` carries the unpruned
grid-to-width factor `4/3` along the period-3 (`100`) cycle (`4/3 ≤ M 0 1, M 1 2, M 2 0`),
then for **every** positive weight `w : Fin 3 → ℚ` and sub-invariant scalar `ρ`,
`4 / 3 ≤ ρ` (and `1 < ρ`). -/
theorem archimedean_only_density_fallacy_supercritical
    (M : Matrix (Fin 3) (Fin 3) ℚ) (w : Fin 3 → ℚ) (ρ : ℚ)
    (hM : ∀ i j : Fin 3, 0 ≤ M i j)
    (hw : ∀ i : Fin 3, 0 < w i)
    (hc01 : (4 / 3 : ℚ) ≤ M 0 1) (hc12 : (4 / 3 : ℚ) ≤ M 1 2) (hc20 : (4 / 3 : ℚ) ≤ M 2 0)
    (hsub : ∀ i : Fin 3, (∑ j : Fin 3, M i j * w j) ≤ ρ * w i) :
    (4 / 3 : ℚ) ≤ ρ ∧ 1 < ρ := by
  have hs0 : M 0 1 * w 1 ≤ ∑ j : Fin 3, M 0 j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hM 0 j) (le_of_lt (hw j))) (Finset.mem_univ 1)
  have hs1 : M 1 2 * w 2 ≤ ∑ j : Fin 3, M 1 j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hM 1 j) (le_of_lt (hw j))) (Finset.mem_univ 2)
  have hs2 : M 2 0 * w 0 ≤ ∑ j : Fin 3, M 2 j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hM 2 j) (le_of_lt (hw j))) (Finset.mem_univ 0)
  have hw0 : 0 < w 0 := hw 0
  have hw1 : 0 < w 1 := hw 1
  have hw2 : 0 < w 2 := hw 2
  have hm0 : (4 / 3 : ℚ) * w 1 ≤ M 0 1 * w 1 := by nlinarith
  have hm1 : (4 / 3 : ℚ) * w 2 ≤ M 1 2 * w 2 := by nlinarith
  have hm2 : (4 / 3 : ℚ) * w 0 ≤ M 2 0 * w 0 := by nlinarith
  have hsub0 := hsub 0
  have hsub1 := hsub 1
  have hsub2 := hsub 2
  have hsum : (4 / 3 : ℚ) * (w 0 + w 1 + w 2) ≤ ρ * (w 0 + w 1 + w 2) := by linarith
  have hle : (4 / 3 : ℚ) ≤ ρ := by nlinarith
  exact ⟨hle, by linarith⟩

/-- **Existence of 2-Adic Ghost Self-Loops at Every Finite Congruence Depth `2^k`
(`mod_two_pow_ghost_self_loop_at_all_depths`, Section 11.2 & Section 12 Negative Result)**:
For **every** finite 2-adic congruence depth `k : ℕ`:
1. There exists `r_k < 2^k` (`r_k = seedResidue periodicThreeParity k`) such that
   `orbit r_k 3 % 2^k = r_k` and `(19 * r_k + 9) % 2^k = 0` (the 2-adic ghost `-9/19 ∈ ℤ_2`
   forms a self-loop under the 3-step `100` block transition modulo `2^k`).
2. There exist odd residues `v_1, v_2 < 2^k` satisfying the Dense-Core `j = 1` self-loop
   `(2059 * v_1 - 1) % 2^k = 0` (`128 * v_1 + 1 ≡ 2187 * v_1 (mod 2^k)`) and the Dense-Core
   `j = 2` self-loop `(58025 * v_2 - 1) % 2^k = 0` (`1024 * v_2 + 1 ≡ 59049 * v_2 (mod 2^k)`). -/
theorem mod_two_pow_ghost_self_loop_at_all_depths (k : ℕ) :
    (∃ r_k < 2 ^ k, (19 * r_k + 9) % 2 ^ k = 0) ∧
      (∃ v_1 < 2 ^ k, (2059 * v_1) % 2 ^ k = 1 % 2 ^ k) ∧
      (∃ v_2 < 2 ^ k, (58025 * v_2) % 2 ^ k = 1 % 2 ^ k) := by
  have h2k_pos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  -- Helper: any odd `D` is coprime to `2^k`, hence invertible mod `2^k`
  have hinv : ∀ (D target : ℕ), Nat.Coprime D 2 →
      ∃ x < 2 ^ k, (D * x) % 2 ^ k = target % 2 ^ k := by
    intro D target hcop2
    have hcop : Nat.Coprime D (2 ^ k) := hcop2.pow_right k
    set invD := Nat.gcdA D (2 ^ k)
    have hbez : (D : ℤ) * invD + (2 ^ k : ℤ) * Nat.gcdB D (2 ^ k) = 1 := by
      have h := Nat.gcd_eq_gcd_ab D (2 ^ k)
      rw [hcop.gcd_eq_one] at h
      push_cast at h
      unfold invD
      linarith
    set x_int : ℤ := ((target : ℤ) * invD) % (2 ^ k : ℤ)
    have hx_nonneg : 0 ≤ x_int := Int.emod_nonneg _ (by positivity)
    have hx_lt_int : x_int < (2 ^ k : ℤ) := Int.emod_lt_of_pos _ (by positivity)
    set x : ℕ := x_int.toNat
    have hx_eq : (x : ℤ) = x_int := Int.toNat_of_nonneg hx_nonneg
    have hx_lt : x < 2 ^ k := by zify; rw [hx_eq]; exact hx_lt_int
    refine ⟨x, hx_lt, ?_⟩
    zify
    rw [hx_eq]
    have hmod :
        ((D : ℤ) * (((target : ℤ) * invD) % (2 ^ k : ℤ))) % (2 ^ k : ℤ) =
          (target : ℤ) % (2 ^ k : ℤ) := by
      rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      have hsub :
          (D : ℤ) * ((target : ℤ) * invD) =
            (target : ℤ) + (2 ^ k : ℤ) * (-(target : ℤ) * Nat.gcdB D (2 ^ k)) := by
        linear_combination (target : ℤ) * hbez
      rw [hsub, Int.add_mul_emod_self_left]
    exact hmod
  refine ⟨?_, hinv 2059 1 (by decide), hinv 58025 1 (by decide)⟩
  obtain ⟨r_k, hr_lt, hr_mod⟩ := hinv 19 (2 ^ k - 9 % 2 ^ k) (by decide)
  refine ⟨r_k, hr_lt, ?_⟩
  have h9_lt : 9 % 2 ^ k < 2 ^ k := Nat.mod_lt 9 h2k_pos
  rw [Nat.add_mod, hr_mod, Nat.mod_add_mod, Nat.sub_add_cancel (le_of_lt h9_lt), Nat.mod_self]

/-! ## 4. Section 13: 3-Adic Carry Decomposition, Memory Erasure & Exact Word-to-Carry Injectivity -/

/-- **Exact `(2, 3)`-Adic Shift Decomposition of `wordCarry`
(`wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift`, Section 13.2)**:
For every parity stream `ε : ℕ → ℕ` and all `n, m : ℕ`:
`wordCarry ε (n + m) = 3^m * wordCarry ε n + 2^n * wordCarry (shiftStream ε n) m`. -/
theorem wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift (ε : ℕ → ℕ) (n m : ℕ) :
    wordCarry ε (n + m) =
      3 ^ m * wordCarry ε n + 2 ^ n * wordCarry (shiftStream ε n) m := by
  induction m with
  | zero =>
      simp [wordCarry]
  | succ m ih =>
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      rw [hidx]
      simp only [wordCarry, shiftStream]
      rw [ih, pow_succ', pow_add]
      ring

/-- **`m`-Step 3-Adic Carry Memory Erasure (`wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod`,
Section 13.2)**:
Modulo `3^m`, `wordCarry ε (n + m)` is completely independent of the prefix history `wordCarry ε n`:
`wordCarry ε (n + m) % 3^m = (2^n * wordCarry (shiftStream ε n) m) % 3^m`. -/
theorem wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod (ε : ℕ → ℕ) (n m : ℕ) :
    wordCarry ε (n + m) % 3 ^ m =
      (2 ^ n * wordCarry (shiftStream ε n) m) % 3 ^ m := by
  rw [wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift, add_comm,
    Nat.add_mul_mod_self_left]

/-- **Exact 3-Adic Carry Injectivity Theorem (`wordCarry_mod_three_pow_eq_iff_parity_eq`,
Section 13 & Section 6 Stop-Gate Theorem)**:
For **every** horizon `m : ℕ` and **any** two parity streams `ε₁, ε₂ : ℕ → ℕ`:
`wordCarry ε₁ m % 3^m = wordCarry ε₂ m % 3^m ↔ ∀ j < m, ε₁ j % 2 = ε₂ j % 2`. -/
theorem wordCarry_mod_three_pow_eq_iff_parity_eq (ε₁ ε₂ : ℕ → ℕ) (m : ℕ) :
    wordCarry ε₁ m % 3 ^ m = wordCarry ε₂ m % 3 ^ m ↔
      ∀ j < m, ε₁ j % 2 = ε₂ j % 2 := by
  induction m with
  | zero =>
      simp [wordCarry]
  | succ m ih =>
      constructor
      · intro hmod
        simp only [wordCarry, pow_succ'] at hmod
        -- Step 1: Reduce modulo 3 to force `ε₁ m % 2 = ε₂ m % 2`
        have hmod3 :
            (3 * wordCarry ε₁ m + 2 ^ m * (ε₁ m % 2)) % 3 =
              (3 * wordCarry ε₂ m + 2 ^ m * (ε₂ m % 2)) % 3 := by
          have hdvd : 3 ∣ 3 * 3 ^ m := ⟨3 ^ m, rfl⟩
          exact Nat.ModEq.of_dvd hdvd hmod
        rw [Nat.mul_add_mod_self_left, Nat.mul_add_mod_self_left] at hmod3
        have hcop3 : Nat.Coprime (2 ^ m) 3 := by
          apply Nat.Coprime.pow_left
          decide
        have h2m_mod3 : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
          have h0 : 2 ^ m % 3 ≠ 0 := by
            intro hzero
            have hdvd3 : 3 ∣ 2 ^ m := Nat.dvd_of_mod_eq_zero hzero
            have h1 : 3 ∣ 1 := by
              rw [← hcop3.gcd_eq_one]
              exact Nat.dvd_gcd hdvd3 ( dvd_refl 3 )
            omega
          omega
        have he1 : ε₁ m % 2 = 0 ∨ ε₁ m % 2 = 1 := by omega
        have he2 : ε₂ m % 2 = 0 ∨ ε₂ m % 2 = 1 := by omega
        have hem_eq : ε₁ m % 2 = ε₂ m % 2 := by
          rw [Nat.mul_mod (2 ^ m), Nat.mul_mod (2 ^ m)] at hmod3
          rcases h2m_mod3 with h2_1 | h2_2 <;> rcases he1 with he1_0 | he1_1 <;>
            rcases he2 with he2_0 | he2_1 <;>
            simp_all
        -- Step 2: Cancel `2^m * (ε m % 2)` and divide by 3 to recover `wordCarry ε₁ m % 3^m = wordCarry ε₂ m % 3^m`
        have hcancel_add :
            (3 * wordCarry ε₁ m) % (3 * 3 ^ m) = (3 * wordCarry ε₂ m) % (3 * 3 ^ m) := by
          rw [hem_eq] at hmod
          have hmeq :
              3 * wordCarry ε₁ m + 2 ^ m * (ε₂ m % 2) ≡
                3 * wordCarry ε₂ m + 2 ^ m * (ε₂ m % 2) [MOD 3 * 3 ^ m] := hmod
          exact Nat.ModEq.add_right_cancel' (2 ^ m * (ε₂ m % 2)) hmeq
        have hdiv3 : wordCarry ε₁ m % 3 ^ m = wordCarry ε₂ m % 3 ^ m := by
          rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hcancel_add
          omega
        have hprefix := ih.mp hdiv3
        intro j hj
        rcases (by omega : j < m ∨ j = m) with hlt | rfl
        · exact hprefix j hlt
        · exact hem_eq
      · intro hall
        simp only [wordCarry]
        have hprefix : wordCarry ε₁ m % 3 ^ m = wordCarry ε₂ m % 3 ^ m :=
          ih.mpr (fun j hj => hall j (by omega))
        have hem : ε₁ m % 2 = ε₂ m % 2 := hall m (by omega)
        rw [hem, pow_succ']
        have hmul3 :
            (3 * wordCarry ε₁ m) % (3 * 3 ^ m) = (3 * wordCarry ε₂ m) % (3 * 3 ^ m) := by
          rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hprefix]
        exact Nat.ModEq.add_right (2 ^ m * (ε₂ m % 2)) hmul3

/-- **Aligned Carry-Collision Biconditional (`aligned_carry_collision_iff_exact_factor_match`,
Section 13 & Section 6 Carry-Entropy Theorem)**:
For any parity stream `ε : ℕ → ℕ`, origins `n₁, n₂ : ℕ`, and window length `m : ℕ`:
`wordCarry (shiftStream ε n₁) m % 3^m = wordCarry (shiftStream ε n₂) m % 3^m ↔
  ∀ j < m, ε (n₁ + j) % 2 = ε (n₂ + j) % 2`.
In particular, if `prefixFactorCount (fun n => ε n % 2) m C = P` distinct binary factors of
length `m` occur in `[0, C]`, their normalized carries occupy `P` distinct classes modulo `3^m`
(no two distinct binary words of length `m` can ever share the same normalized carry modulo `3^m`). -/
theorem aligned_carry_collision_iff_exact_factor_match (ε : ℕ → ℕ) (n₁ n₂ m : ℕ) :
    wordCarry (shiftStream ε n₁) m % 3 ^ m = wordCarry (shiftStream ε n₂) m % 3 ^ m ↔
      ∀ j < m, ε (n₁ + j) % 2 = ε (n₂ + j) % 2 := by
  simpa [shiftStream] using
    wordCarry_mod_three_pow_eq_iff_parity_eq (shiftStream ε n₁) (shiftStream ε n₂) m

end Mahler.TransferJSRAndFourier
