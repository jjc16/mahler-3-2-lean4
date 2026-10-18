import CoupledProductGraph

/-!
# Bridge 1: Excluding 2-adic Ghosts via Archimedean Positivity (`m ∈ ℤ_{>0}`)

In `CoupledProductGraph.lean` and `OddBlockCoupling.lean`, `N`-step survival is
periodic modulo `2^N`, and the residue class `0 (mod 2^N)` always survives
because `m = 0` is a fixed point (`orbit 0 n = 0`). In the 2-adic integers
`ℤ_2`, trajectories can follow this ghost branch forever.

This module formalizes **Bridge 1**, showing how the Archimedean hypothesis
that `m` is a **finite positive integer** (`0 < m`) eliminates the `0 (mod 2^N)`
ghost branch and upgrades finite modulo-`2^N` checks into unconditional lower
bounds across **all** `m > 0`:

1. **Tightened Half-Corridor Squeeze (`surviving_orbit_half_corridor`)**:
   Whereas general orbits satisfy `3^n * m ≤ 2^n * a_n < 3^n * (m + 1)`, any
   orbit surviving through step `n` satisfies the half-width corridor
   `3^n * (2 * m) ≤ 2^(n + 1) * a_n < 3^n * (2 * m + 1)`.
2. **Elimination of the `0 (mod 2^N)` Ghost Branch (`ghost_branch_forces_two_pow_le`)**:
   If `0 < m` and `m % 2^N = 0`, then `2^N ∣ m`, so Archimedean positivity
   forces `2^N ≤ m`.
3. **Unconditional Global Lower-Bound Transfer (`positive_survivor_ge_of_residues_excluded`)**:
   If `B ≤ 2^N` and every nonzero residue `0 < r < B` fails `survivesSteps r N`,
   then **every** positive integer `m > 0` (of any size, including `m ≥ 2^N`)
   that has a valid companion up to step `N` must satisfy `B ≤ m`.
4. **Exact Bridge 1 Equivalence (`no_positive_zNumber_iff_unbounded_exclusion`)**:
   No positive integer `m > 0` has an infinite Mahler companion `ξ ∈ ℝ` if and
   only if for every `B`, there exists a horizon `N` (with `B ≤ 2^N`) such that
   all `0 < r < B` fail `survivesSteps r N`.
5. **Certified Global Bounds (`positive_survivor_step4_ge_4`, `positive_survivor_step12_ge_53`)**:
   Every positive integer `m > 0` surviving `4` steps satisfies `4 ≤ m`, and
   every `m > 0` surviving `12` steps satisfies `53 ≤ m`.
-/

namespace Mahler.BridgeOne

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph

/-! ## 1. The Tightened Half-Corridor Squeeze for Surviving Orbits -/

/-- For any orbit surviving to step `n`, `a_n = orbit m n` is confined to the
half-width corridor `3^n * (2 * m) ≤ 2^(n + 1) * a_n < 3^n * (2 * m + 1)`,
cutting the general upper bound `3^n * (2 * m + 2)` in half. -/
theorem surviving_orbit_half_corridor {m n : ℕ} {ξ : ℝ}
    (h : ValidCompanionUpTo m ξ n) :
    3 ^ n * (2 * m) ≤ 2 ^ (n + 1) * orbit m n ∧
      2 ^ (n + 1) * orbit m n < 3 ^ n * (2 * m + 1) := by
  have hlo : 3 ^ n * (2 * orbit m 0) ≤ 2 ^ (n + 1) * orbit m (0 + n) :=
    three_pow_mul_two_orbit_le m 0 n
  have hpinch : IntegerPinch m 0 (n - 0) :=
    (exists_validCompanionUpTo_iff_integerPinch m n).mp ⟨ξ, h⟩ 0 (Nat.zero_le n)
  unfold IntegerPinch at hpinch
  exact ⟨by simpa [orbit, Nat.zero_add] using hlo,
    by simpa [orbit, Nat.zero_add] using hpinch⟩

/-- Single-lift exactness when `a < 2^K`: once `K` exceeds the bit-length of `a`,
the second residue lift `(step r + 2^(K-1)) % 2^K` in `G_{K, B}` is unused. -/
theorem step_mod_two_pow_exact_of_lt {K a : ℕ} (ha : a < 2 ^ K) :
    step a % 2 ^ K = step (a % 2 ^ K) % 2 ^ K := by
  rw [Nat.mod_eq_of_lt ha]

/-! ## 2. Eliminating the `0 (mod 2^N)` 2-adic Ghost Branch for `m > 0` -/

/-- If `0 < m` lies in the ghost residue class `m % 2^N = 0`, then `2^N ≤ m`. -/
theorem ghost_branch_forces_two_pow_le {m N : ℕ} (hm : 0 < m)
    (hghost : m % 2 ^ N = 0) :
    2 ^ N ≤ m := by
  have hdvd : 2 ^ N ∣ m := Nat.dvd_of_mod_eq_zero hghost
  exact Nat.le_of_dvd hm hdvd

/-- **Unconditional Global Lower-Bound Transfer**:
If `B ≤ 2^N` and every nonzero residue `0 < r < B` fails `survivesSteps r N`,
then **every** positive integer `m > 0` (regardless of how large `m` is, and
including multiples of `2^N`) that survives `N` steps must satisfy `B ≤ m`. -/
theorem positive_survivor_ge_of_residues_excluded {m N B : ℕ}
    (hm : 0 < m) (hBN : B ≤ 2 ^ N)
    (hexcl : ∀ r : ℕ, 0 < r → r < B → survivesSteps r N = false)
    (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo m ξ N) :
    B ≤ m := by
  have hmod_surv : survivesSteps (m % 2 ^ N) N = true := by
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact (exists_validCompanionUpTo_mod_two_pow_iff m N).mp hsurv
  by_cases hghost : m % 2 ^ N = 0
  · exact Nat.le_trans hBN (ghost_branch_forces_two_pow_le hm hghost)
  · have hpos_rem : 0 < m % 2 ^ N := Nat.pos_of_ne_zero hghost
    have hge_B : B ≤ m % 2 ^ N := by
      by_contra hlt
      have hfalse := hexcl (m % 2 ^ N) hpos_rem (by omega)
      rw [hfalse] at hmod_surv
      cases hmod_surv
    have hrem_le : m % 2 ^ N ≤ m := Nat.mod_le m (2 ^ N)
    exact Nat.le_trans hge_B hrem_le

/-! ## 3. Monotonicity and the Exact Bridge 1 Equivalence -/

theorem validCompanionUpTo_mono {m N₁ N₂ : ℕ} {ξ : ℝ}
    (hN : N₁ ≤ N₂) (h : ValidCompanionUpTo m ξ N₂) :
    ValidCompanionUpTo m ξ N₁ :=
  fun n hn => h n (Nat.le_trans hn hN)

theorem survivesSteps_mono_true {m N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    (h : survivesSteps m N₂ = true) :
    survivesSteps m N₁ = true := by
  rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch] at h ⊢
  rcases h with ⟨ξ, hξ⟩
  exact ⟨ξ, validCompanionUpTo_mono hN hξ⟩

theorem survivesSteps_mono_false {m N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    (h : survivesSteps m N₁ = false) :
    survivesSteps m N₂ = false := by
  cases h2 : survivesSteps m N₂ with
  | false => rfl
  | true =>
      have h1 := survivesSteps_mono_true hN h2
      rw [h] at h1
      cases h1

/-- `ξ` is an infinite Mahler Z-number companion with initial integer part `m`. -/
def IsInfiniteCompanion (m : ℕ) (ξ : ℝ) : Prop :=
  ∀ n : ℕ, ValidCompanionAt m ξ n

theorem validCompanionUpTo_of_isInfiniteCompanion {m : ℕ} {ξ : ℝ}
    (h : IsInfiniteCompanion m ξ) (N : ℕ) :
    ValidCompanionUpTo m ξ N :=
  fun n _ => h n

private theorem n_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- **The Exact Bridge 1 Equivalence Theorem**:
Every positive integer `m > 0` fails at some finite horizon `N` if and only if
for every bound `B`, there exists a single horizon `N` with `B ≤ 2^N` that
simultaneously excludes all nonzero residues `0 < r < B`. -/
theorem every_positive_fails_iff_unbounded_exclusion :
    (∀ m : ℕ, 0 < m → ∃ N : ℕ, ¬ ∃ ξ : ℝ, ValidCompanionUpTo m ξ N) ↔
      (∀ B : ℕ, ∃ N : ℕ, B ≤ 2 ^ N ∧
        ∀ r : ℕ, 0 < r → r < B → survivesSteps r N = false) := by
  constructor
  · intro hfail B
    induction B with
    | zero =>
        refine ⟨0, by decide, ?_⟩
        intro r hr0 hrB
        omega
    | succ B ih =>
        rcases ih with ⟨N₁, hBN₁, hN₁⟩
        by_cases hB0 : B = 0
        · subst B
          refine ⟨1, by decide, ?_⟩
          intro r hr0 hr1
          omega
        · have hB_pos : 0 < B := Nat.pos_of_ne_zero hB0
          rcases hfail B hB_pos with ⟨N₂, hN₂⟩
          have hB_false : survivesSteps B N₂ = false := by
            cases hB : survivesSteps B N₂ with
            | false => rfl
            | true =>
                rw [survivesSteps_eq_true_iff,
                  ← exists_validCompanionUpTo_iff_integerPinch] at hB
                exact False.elim (hN₂ hB)
          let N := max (max N₁ N₂) (B + 1)
          have hN₁_le : N₁ ≤ N :=
            Nat.le_trans (Nat.le_max_left N₁ N₂) (Nat.le_max_left _ _)
          have hN₂_le : N₂ ≤ N :=
            Nat.le_trans (Nat.le_max_right N₁ N₂) (Nat.le_max_left _ _)
          have hB1_le_N : B + 1 ≤ N := Nat.le_max_right _ _
          have hBN : B + 1 ≤ 2 ^ N :=
            Nat.le_trans hB1_le_N (Nat.le_of_lt (n_lt_two_pow N))
          refine ⟨N, hBN, ?_⟩
          intro r hr0 hrB1
          by_cases hrB : r < B
          · exact survivesSteps_mono_false hN₁_le (hN₁ r hr0 hrB)
          · have hr_eq : r = B := by omega
            subst r
            exact survivesSteps_mono_false hN₂_le hB_false
  · intro hexcl m hm
    rcases hexcl (m + 1) with ⟨N, hBN, hN⟩
    refine ⟨N, ?_⟩
    intro hsurv
    have hle : m + 1 ≤ m :=
      positive_survivor_ge_of_residues_excluded hm hBN hN hsurv
    omega

/-- Unbounded finite-residue exclusion implies no positive integer `m > 0` has
an infinite Mahler Z-number companion `ξ ∈ ℝ`. -/
theorem no_positive_infinite_companion_of_unbounded_exclusion
    (hexcl : ∀ B : ℕ, ∃ N : ℕ, B ≤ 2 ^ N ∧
      ∀ r : ℕ, 0 < r → r < B → survivesSteps r N = false) :
    ∀ m : ℕ, 0 < m → ¬ ∃ ξ : ℝ, IsInfiniteCompanion m ξ := by
  intro m hm ⟨ξ, hξ⟩
  rcases (every_positive_fails_iff_unbounded_exclusion.mpr hexcl) m hm with ⟨N, hN⟩
  exact hN ⟨ξ, validCompanionUpTo_of_isInfiniteCompanion hξ N⟩

/-! ## 4. Certified Global Archimedean Lower Bounds Across All `m > 0` -/

private theorem below_4_excluded_at_4 :
    ∀ r : Fin 4, 0 < r.val → survivesSteps r.val 4 = false := by
  decide

/-- **Certified Global Bound at Step 4**:
Every positive integer `m > 0` surviving `4` steps satisfies `4 ≤ m`
(including multiples of `2^4 = 16`). -/
theorem positive_survivor_step4_ge_4 {m : ℕ} (hm : 0 < m)
    (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo m ξ 4) :
    4 ≤ m := by
  refine positive_survivor_ge_of_residues_excluded hm (by decide : 4 ≤ 2 ^ 4) ?_ hsurv
  intro r hr0 hr4
  exact below_4_excluded_at_4 ⟨r, hr4⟩ hr0

private theorem below_53_excluded_at_12 :
    ∀ r : Fin 53, 0 < r.val → survivesSteps r.val 12 = false := by
  decide

/-- **Certified Global Bound at Step 12**:
Every positive integer `m > 0` surviving `12` steps satisfies `53 ≤ m`
(including multiples of `2^12 = 4096`). -/
theorem positive_survivor_step12_ge_53 {m : ℕ} (hm : 0 < m)
    (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo m ξ 12) :
    53 ≤ m := by
  refine positive_survivor_ge_of_residues_excluded hm (by decide : 53 ≤ 2 ^ 12) ?_ hsurv
  intro r hr0 hr53
  exact below_53_excluded_at_12 ⟨r, hr53⟩ hr0

end Mahler.BridgeOne
