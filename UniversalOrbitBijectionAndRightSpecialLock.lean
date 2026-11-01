import ExactSeedResidueTreeAndStabilization
import ParitySurplusPotentialsAndSafetyGame
import TransferOperatorJSRAndCarryFourier
import EndpointCompactnessAndBalancedExclusion

/-!
# Universal Forward $2^m$ / Backward $3^m$ Orbit Bijection, Global Right-Special Lock, Raw-Orbit $1.7095$ Complexity & Mod-3 Valuation Trichotomy

This module formalizes **Round 2 Tracks 1 & 4** and **Part II Sections 7 & 14** of
`RESEARCH_PLAN_ARGON_ROUND2_COMPLETION.md`:

1. **Strict Monotonicity & Step-by-Step $(2^m, 3^m)$ Identity for All Positive Orbits
   (`orbit_strictMono_of_pos`, `two_pow_mul_orbit_add_eq`, `two_pow_mul_orbit_add_one_le_three_pow_mul`)**:
   - For every positive integer seed `1 ≤ a_0`, `orbit a_0` is strictly increasing
     (`n₁ < n₂ → orbit a_0 n₁ < orbit a_0 n₂`) and satisfies `2^n * (orbit a_0 n + 1) ≤ 3^n * (a_0 + 1)`.
   - For every `a_0, n, m : ℕ`, `2^m * orbit a_0 (n + m) = 3^m * orbit a_0 n + wordCarry (shiftStream (orbit a_0) n) m`.

2. **Universal Forward $2^m$ / Backward $3^m$ Orbit Bijection on All of $[0, 1/2)$
   (`orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow`, Track 1.1–1.3)**:
   - Combining `orbit_parity_eq_upto_iff_mod_two_pow` with Round 1's 3-adic carry injectivity theorem
     `wordCarry_mod_three_pow_eq_iff_parity_eq` establishes the assumption-free 3-way biconditional
     for **every** seed `a_0 : ℕ`, **every** pair of indices `n₁, n₂ : ℕ`, and **every** window length `m : ℕ`:
     `orbit a_0 n₁ % 2^m = orbit a_0 n₂ % 2^m ↔
       (∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ↔
       orbit a_0 (n₁ + m) % 3^m = orbit a_0 (n₂ + m) % 3^m`.

3. **Global Right-Special Exact Valuation & Odd-Quotient Lock (`right_special_orbit_exact_two_and_three_adic_lock`,
   `three_occurrence_raw_orbit_two_pow_add_one_dvd`, Track 1.2–1.3 & Section 14)**:
   - Whenever `1 ≤ a_0`, `n₁ < n₂`, `∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2`,
     and `orbit a_0 (n₁ + m) % 2 ≠ orbit a_0 (n₂ + m) % 2` (a right-special parity factor), there
     exists a unique positive **odd** integer `q_odd ≥ 1` (`q_odd % 2 = 1`) such that:
     `orbit a_0 n₂ - orbit a_0 n₁ = 2^m * q_odd` and
     `orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m) = 3^m * q_odd`.
   - If a length-`m` parity factor occurs at three indices `n₁ < n₂ < n₃`, at least one pair shares the
     `m`-th bit and satisfies `2^(m + 1) ∣ (orbit a_0 n_b - orbit a_0 n_a)` and
     `3^(m + 1) ∣ (orbit a_0 (n_b + m + 1) - orbit a_0 (n_a + m + 1))`.

4. **Unconditional Raw-Orbit $(p, q)$ Repetition Cutoff & $\log 2 / \log(3/2) \approx 1.709511$ Complexity
   Lower Bound for ALL Positive Integers (`raw_orbit_repeated_parity_window_pq_cutoff`,
   `raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds`, Track 4.1–4.2)**:
   - For **every** positive integer `1 ≤ a_0 < 2^W` (without assuming `ValidCompanionForever` or
     $[8/81, 1/2)$ confinement!), any repeated length-`m` parity factor at `n₁ < n₂` satisfies
     `q * m < p * n₂ + q * W` for all `1 ≤ q` with `3^q ≤ 2^(p + q)` (and `17 * m < 10 * n₂ + 17 * W`
     at `(p, q) = (10, 17)`).
   - Consequently, for **every** positive integer `1 ≤ a_0`, the rational-base $T(x) = \lceil 3x/2 \rceil$
     parity stream `n ↦ orbit a_0 n % 2` has liminf prefix-factor complexity slope at least
     `log 2 / log(3/2) ≈ 1.709511` (`raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds`),
     establishing a universal deterministic complexity lower bound toward the Andrieu–Eliahou–Vivion
     rational-base normality conjecture.

5. **Section 7 — The Mod-3 Valuation Trichotomy & Exact Epoch Coding
   (`three_mul_affInv_eq_nineteen_mul_add_eight`, `two_adic_valuation_affInv_trichotomy`,
   `epoch_period_three_run_exit_trichotomy`)**:
   - Proves the master identity `3 * (19 * b + 9) = 19 * (3 * b + 1) + 8`.
   - Deduces the exact 4-way valuation trichotomy for `3 * b + 1 = 2^s * u` (`u % 2 = 1`):
     `v_2(19b+9) = 1 ↔ s = 1`, `v_2(19b+9) = 2 ↔ s = 2`, `v_2(19b+9) = 3 ↔ 4 ≤ s`, and
     `v_2(19b+9) ≥ 4 ↔ s = 3`.
   - Proves that across `j` blocks of length `3` (`2^(3*j) * I(b_j) = 27^j * I(b_0)`), the initial
     valuation `v_2(19 * b_0 + 9) = 3 * j + r` (`r ∈ {1, 2, 3}`) uniquely determines both the run
     length `j` and the exit block type (`r = 1 → s_j = 1` death class, `r = 2 → s_j = 2`,
     `r = 3 → 4 ≤ s_j`).
-/

namespace Mahler.UniversalOrbitBijection

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier

/-! ## 1. Strict Monotonicity, Exponential Upper Bound & Step-by-Step $(2^m, 3^m)$ Identity -/

/-- For every positive integer `1 ≤ x`, `x < step x` and `2 * (step x + 1) ≤ 3 * (x + 1)`. -/
theorem lt_step_and_two_mul_step_add_one_le {x : ℕ} (hx : 1 ≤ x) :
    x < step x ∧ 2 * (step x + 1) ≤ 3 * (x + 1) := by
  have hid := step_identity x
  have hmod : x % 2 ≤ 1 := by omega
  omega

/-- **Strict Monotonicity & Upper Growth Bound for Positive Orbits
(`orbit_strictMono_of_pos`, `two_pow_mul_orbit_add_one_le_three_pow_mul`)**:
For every positive integer seed `1 ≤ a_0`:
1. `1 ≤ orbit a_0 n` and `orbit a_0 n < orbit a_0 (n + 1)` for all `n : ℕ`,
2. `n₁ < n₂ → orbit a_0 n₁ < orbit a_0 n₂`, and
3. `2^n * (orbit a_0 n + 1) ≤ 3^n * (a_0 + 1)` for all `n : ℕ`. -/
theorem orbit_strictMono_of_pos {a_0 : ℕ} (ha0 : 1 ≤ a_0) :
    (∀ n : ℕ, 1 ≤ orbit a_0 n ∧ orbit a_0 n < orbit a_0 (n + 1)) ∧
      (∀ n₁ n₂ : ℕ, n₁ < n₂ → orbit a_0 n₁ < orbit a_0 n₂) ∧
      (∀ n : ℕ, 2 ^ n * (orbit a_0 n + 1) ≤ 3 ^ n * (a_0 + 1)) := by
  have hstep : ∀ n : ℕ, 1 ≤ orbit a_0 n ∧ orbit a_0 n < orbit a_0 (n + 1) := by
    intro n
    induction n with
    | zero =>
        have h := (lt_step_and_two_mul_step_add_one_le ha0).1
        exact ⟨ha0, h⟩
    | succ n ih =>
        have hpos : 1 ≤ orbit a_0 (n + 1) := by omega
        exact ⟨hpos, (lt_step_and_two_mul_step_add_one_le hpos).1⟩
  have hmono : ∀ n₁ n₂ : ℕ, n₁ < n₂ → orbit a_0 n₁ < orbit a_0 n₂ := by
    intro n₁ n₂ hlt
    induction n₂ with
    | zero => omega
    | succ n₂ ih =>
        rcases (by omega : n₁ < n₂ ∨ n₁ = n₂) with hlt' | rfl
        · exact lt_trans (ih hlt') (hstep n₂).2
        · exact (hstep n₁).2
  have hbound : ∀ n : ℕ, 2 ^ n * (orbit a_0 n + 1) ≤ 3 ^ n * (a_0 + 1) := by
    intro n
    induction n with
    | zero => simp [orbit]
    | succ n ih =>
        have hpos : 1 ≤ orbit a_0 n := (hstep n).1
        have hle := (lt_step_and_two_mul_step_add_one_le hpos).2
        have horb : orbit a_0 (n + 1) = step (orbit a_0 n) := rfl
        rw [horb]
        have h1 :
            2 ^ (n + 1) * (step (orbit a_0 n) + 1) =
              2 ^ n * (2 * (step (orbit a_0 n) + 1)) := by
          rw [pow_succ]; ring
        have h2 :
            2 ^ n * (2 * (step (orbit a_0 n) + 1)) ≤
              2 ^ n * (3 * (orbit a_0 n + 1)) :=
          Nat.mul_le_mul_left (2 ^ n) hle
        have h3 :
            2 ^ n * (3 * (orbit a_0 n + 1)) = 3 * (2 ^ n * (orbit a_0 n + 1)) := by
          ring
        have h4 : 3 * (2 ^ n * (orbit a_0 n + 1)) ≤ 3 * (3 ^ n * (a_0 + 1)) :=
          Nat.mul_le_mul_left 3 ih
        have h5 : 3 * (3 ^ n * (a_0 + 1)) = 3 ^ (n + 1) * (a_0 + 1) := by
          rw [pow_succ']; ring
        omega
  exact ⟨hstep, hmono, hbound⟩

/-- Composition of `orbit` across `n + m` steps: `orbit a_0 (n + m) = orbit (orbit a_0 n) m`. -/
theorem orbit_add_eq (a_0 n m : ℕ) :
    orbit a_0 (n + m) = orbit (orbit a_0 n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      rw [hidx]
      exact congrArg step ih

/-- **Exact Step-by-Step $(2^m, 3^m)$ Shifted Orbit Identity (`two_pow_mul_orbit_add_eq`)**:
For every seed `a_0 : ℕ`, start index `n : ℕ`, and window length `m : ℕ`:
`2^m * orbit a_0 (n + m) = 3^m * orbit a_0 n + wordCarry (shiftStream (orbit a_0) n) m`. -/
theorem two_pow_mul_orbit_add_eq (a_0 n m : ℕ) :
    2 ^ m * orbit a_0 (n + m) =
      3 ^ m * orbit a_0 n + wordCarry (shiftStream (orbit a_0) n) m := by
  rw [orbit_add_eq]
  have hmatch : ∀ j < m, orbit (orbit a_0 n) j % 2 = shiftStream (orbit a_0) n j % 2 := by
    intro j _
    simp [shiftStream, ← orbit_add_eq]
  exact (wordCarry_eq_carry_of_parity_match hmatch).2

/-! ## 2. Universal Forward $2^m$ / Backward $3^m$ Orbit Bijection on All of $[0, 1/2)$ (Track 1) -/

/-- **Universal Forward $2^m$ / Backward $3^m$ Orbit Bijection
(`orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow`, Track 1.1–1.3)**:
For **every** integer seed `a_0 : ℕ`, **every** pair of indices `n₁, n₂ : ℕ`, and **every**
window length `m : ℕ`:
1. `orbit a_0 n₁ % 2^m = orbit a_0 n₂ % 2^m ↔ ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2`,
2. `(∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ↔ orbit a_0 (n₁ + m) % 3^m = orbit a_0 (n₂ + m) % 3^m`. -/
theorem orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow
    (a_0 n₁ n₂ m : ℕ) :
    (orbit a_0 n₁ % 2 ^ m = orbit a_0 n₂ % 2 ^ m ↔
      ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ∧
    ((∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ↔
      orbit a_0 (n₁ + m) % 3 ^ m = orbit a_0 (n₂ + m) % 3 ^ m) := by
  have h2 :
      orbit a_0 n₁ % 2 ^ m = orbit a_0 n₂ % 2 ^ m ↔
        ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2 := by
    simpa [orbit_add_eq] using
      (orbit_parity_eq_upto_iff_mod_two_pow (orbit a_0 n₁) (orbit a_0 n₂) m).symm
  refine ⟨h2, ?_⟩
  have hcarry_iff :=
    wordCarry_mod_three_pow_eq_iff_parity_eq
      (shiftStream (orbit a_0) n₁) (shiftStream (orbit a_0) n₂) m
  simp only [shiftStream] at hcarry_iff
  rw [← hcarry_iff]
  have hid1 := two_pow_mul_orbit_add_eq a_0 n₁ m
  have hid2 := two_pow_mul_orbit_add_eq a_0 n₂ m
  have hmod1 :
      (2 ^ m * orbit a_0 (n₁ + m)) % 3 ^ m =
        wordCarry (shiftStream (orbit a_0) n₁) m % 3 ^ m := by
    rw [hid1, add_comm, Nat.add_mul_mod_self_left]
  have hmod2 :
      (2 ^ m * orbit a_0 (n₂ + m)) % 3 ^ m =
        wordCarry (shiftStream (orbit a_0) n₂) m % 3 ^ m := by
    rw [hid2, add_comm, Nat.add_mul_mod_self_left]
  rw [← hmod1, ← hmod2]
  have hcop : Nat.Coprime (2 ^ m) (3 ^ m) := by
    apply Nat.Coprime.pow
    decide
  constructor
  · intro hmeq
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm hmeq
  · intro hmeq
    exact Nat.ModEq.mul_left (2 ^ m) hmeq

/-- If two streams agree in parity up to step `m`, their `m`-step `wordCarry` values are equal. -/
theorem wordCarry_congr_of_parity_eq {ε₁ ε₂ : ℕ → ℕ} (m : ℕ)
    (h : ∀ j < m, ε₁ j % 2 = ε₂ j % 2) :
    wordCarry ε₁ m = wordCarry ε₂ m := by
  induction m with
  | zero => rfl
  | succ k ih =>
      simp only [wordCarry]
      rw [ih (fun j hj => h j (by omega)), h k (by omega)]

/-- **Global Right-Special Exact Valuation & Odd-Quotient Lock
(`right_special_orbit_exact_two_and_three_adic_lock`, Track 1.2–1.3)**:
Suppose `1 ≤ a_0`, `n₁ < n₂`, `∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2`,
and `orbit a_0 (n₁ + m) % 2 ≠ orbit a_0 (n₂ + m) % 2` (a right-special parity factor of length `m`).
Then there exists a positive **odd** integer `q_odd ≥ 1` (`q_odd % 2 = 1`) such that:
1. `orbit a_0 n₂ - orbit a_0 n₁ = 2^m * q_odd`,
2. `orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m) = 3^m * q_odd`, and
3. `2^m ≤ orbit a_0 n₂ - orbit a_0 n₁` and `¬ (2^(m + 1) ∣ (orbit a_0 n₂ - orbit a_0 n₁))`. -/
theorem right_special_orbit_exact_two_and_three_adic_lock {a_0 n₁ n₂ m : ℕ}
    (ha0 : 1 ≤ a_0) (hlt : n₁ < n₂)
    (hmatch : ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2)
    (hdiverge : orbit a_0 (n₁ + m) % 2 ≠ orbit a_0 (n₂ + m) % 2) :
    ∃ q_odd : ℕ, 1 ≤ q_odd ∧ q_odd % 2 = 1 ∧
      orbit a_0 n₂ - orbit a_0 n₁ = 2 ^ m * q_odd ∧
      orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m) = 3 ^ m * q_odd ∧
      2 ^ m ≤ orbit a_0 n₂ - orbit a_0 n₁ ∧
      ¬ (2 ^ (m + 1) ∣ (orbit a_0 n₂ - orbit a_0 n₁)) := by
  have hmono := (orbit_strictMono_of_pos ha0).2.1
  have hb_lt : orbit a_0 n₁ < orbit a_0 n₂ := hmono n₁ n₂ hlt
  have hbm_lt : orbit a_0 (n₁ + m) < orbit a_0 (n₂ + m) := hmono (n₁ + m) (n₂ + m) (by omega)
  have hcarry_eq :
      wordCarry (shiftStream (orbit a_0) n₁) m =
        wordCarry (shiftStream (orbit a_0) n₂) m :=
    wordCarry_congr_of_parity_eq m hmatch
  have hid1 := two_pow_mul_orbit_add_eq a_0 n₁ m
  have hid2 := two_pow_mul_orbit_add_eq a_0 n₂ m
  rw [← hcarry_eq] at hid2
  have hdiff_eq :
      2 ^ m * (orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m)) =
        3 ^ m * (orbit a_0 n₂ - orbit a_0 n₁) := by
    zify [le_of_lt hbm_lt, le_of_lt hb_lt] at hid1 hid2 ⊢
    linarith
  have hmod2m : orbit a_0 n₁ % 2 ^ m = orbit a_0 n₂ % 2 ^ m :=
    (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₂ m).1.mpr hmatch
  have hdvd2m : 2 ^ m ∣ (orbit a_0 n₂ - orbit a_0 n₁) := by
    rw [← Nat.modEq_iff_dvd' (le_of_lt hb_lt)]
    exact hmod2m
  have hnot_dvd2m1 : ¬ (2 ^ (m + 1) ∣ (orbit a_0 n₂ - orbit a_0 n₁)) := by
    intro hdvd1
    have hmod2m1 : orbit a_0 n₁ % 2 ^ (m + 1) = orbit a_0 n₂ % 2 ^ (m + 1) :=
      (Nat.modEq_iff_dvd' (le_of_lt hb_lt)).mpr hdvd1
    have hall1 :=
      (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₂ (m + 1)).1.mp hmod2m1
    exact hdiverge (hall1 m (by omega))
  obtain ⟨q_odd, hq_eq⟩ := hdvd2m
  have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  have hdiff_pos : 0 < orbit a_0 n₂ - orbit a_0 n₁ := Nat.sub_pos_of_lt hb_lt
  have hq_pos : 1 ≤ q_odd := by
    rcases Nat.eq_zero_or_pos q_odd with rfl | hpos
    · rw [mul_zero] at hq_eq
      omega
    · exact hpos
  have hq_odd : q_odd % 2 = 1 := by
    by_contra hq_even
    have hq_0 : q_odd % 2 = 0 := by omega
    have h2q : 2 * (q_odd / 2) = q_odd := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hq_0)
    apply hnot_dvd2m1
    refine ⟨q_odd / 2, ?_⟩
    calc
      orbit a_0 n₂ - orbit a_0 n₁ = 2 ^ m * q_odd := hq_eq
      _ = 2 ^ m * (2 * (q_odd / 2)) := by rw [h2q]
      _ = 2 ^ (m + 1) * (q_odd / 2) := by rw [pow_succ]; ring
  have h3m_eq : orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m) = 3 ^ m * q_odd := by
    rw [hq_eq] at hdiff_eq
    have hmul :
        2 ^ m * (orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m)) =
          2 ^ m * (3 ^ m * q_odd) := by
      linarith
    exact Nat.eq_of_mul_eq_mul_left h2m_pos hmul
  refine ⟨q_odd, hq_pos, hq_odd, hq_eq, h3m_eq, ?_, hnot_dvd2m1⟩
  rw [hq_eq]
  exact Nat.le_mul_of_pos_right _ hq_pos

/-- **Three-Occurrence Raw-Orbit Ultrametric Pairing (`three_occurrence_raw_orbit_two_pow_add_one_dvd`,
Track 1.3(5) & Section 14)**:
If a length-`m` parity factor occurs at three positions `n₁, n₂, n₃` along `orbit a_0`,
then at least two of the three occurrences share their `m`-th parity bit as well, forcing
`2^(m + 1) ∣ (orbit a_0 n_b - orbit a_0 n_a)` and
`3^(m + 1) ∣ (orbit a_0 (n_b + m + 1) - orbit a_0 (n_a + m + 1))` for one of the pairs
`(n_a, n_b) ∈ {(n₁, n₂), (n₂, n₃), (n₁, n₃)}`. -/
theorem three_occurrence_raw_orbit_two_pow_add_one_dvd {a_0 n₁ n₂ n₃ m : ℕ}
    (_hlt12 : n₁ < n₂) (_hlt23 : n₂ < n₃)
    (h12 : ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2)
    (h23 : ∀ j < m, orbit a_0 (n₂ + j) % 2 = orbit a_0 (n₃ + j) % 2) :
    (orbit a_0 n₁ % 2 ^ (m + 1) = orbit a_0 n₂ % 2 ^ (m + 1) ∧
      orbit a_0 (n₁ + m + 1) % 3 ^ (m + 1) = orbit a_0 (n₂ + m + 1) % 3 ^ (m + 1)) ∨
    (orbit a_0 n₂ % 2 ^ (m + 1) = orbit a_0 n₃ % 2 ^ (m + 1) ∧
      orbit a_0 (n₂ + m + 1) % 3 ^ (m + 1) = orbit a_0 (n₃ + m + 1) % 3 ^ (m + 1)) ∨
    (orbit a_0 n₁ % 2 ^ (m + 1) = orbit a_0 n₃ % 2 ^ (m + 1) ∧
      orbit a_0 (n₁ + m + 1) % 3 ^ (m + 1) = orbit a_0 (n₃ + m + 1) % 3 ^ (m + 1)) := by
  have hb1 : orbit a_0 (n₁ + m) % 2 = 0 ∨ orbit a_0 (n₁ + m) % 2 = 1 := by omega
  have hb2 : orbit a_0 (n₂ + m) % 2 = 0 ∨ orbit a_0 (n₂ + m) % 2 = 1 := by omega
  have hb3 : orbit a_0 (n₃ + m) % 2 = 0 ∨ orbit a_0 (n₃ + m) % 2 = 1 := by omega
  have hpigeon :
      orbit a_0 (n₁ + m) % 2 = orbit a_0 (n₂ + m) % 2 ∨
      orbit a_0 (n₂ + m) % 2 = orbit a_0 (n₃ + m) % 2 ∨
      orbit a_0 (n₁ + m) % 2 = orbit a_0 (n₃ + m) % 2 := by
    omega
  rcases hpigeon with hm12 | hm23 | hm13
  · left
    have hall : ∀ j < m + 1, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2 := by
      intro j hj
      rcases (by omega : j < m ∨ j = m) with hlt | rfl
      · exact h12 j hlt
      · exact hm12
    have hbij := orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₂ (m + 1)
    have hidx1 : n₁ + (m + 1) = n₁ + m + 1 := by omega
    have hidx2 : n₂ + (m + 1) = n₂ + m + 1 := by omega
    exact ⟨hbij.1.mpr hall, by rw [← hidx1, ← hidx2]; exact hbij.2.mp hall⟩
  · right; left
    have hall : ∀ j < m + 1, orbit a_0 (n₂ + j) % 2 = orbit a_0 (n₃ + j) % 2 := by
      intro j hj
      rcases (by omega : j < m ∨ j = m) with hlt | rfl
      · exact h23 j hlt
      · exact hm23
    have hbij := orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₂ n₃ (m + 1)
    have hidx2 : n₂ + (m + 1) = n₂ + m + 1 := by omega
    have hidx3 : n₃ + (m + 1) = n₃ + m + 1 := by omega
    exact ⟨hbij.1.mpr hall, by rw [← hidx2, ← hidx3]; exact hbij.2.mp hall⟩
  · right; right
    have hall : ∀ j < m + 1, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₃ + j) % 2 := by
      intro j hj
      rcases (by omega : j < m ∨ j = m) with hlt | rfl
      · exact (h12 j hlt).trans (h23 j hlt)
      · exact hm13
    have hbij := orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₃ (m + 1)
    have hidx1 : n₁ + (m + 1) = n₁ + m + 1 := by omega
    have hidx3 : n₃ + (m + 1) = n₃ + m + 1 := by omega
    exact ⟨hbij.1.mpr hall, by rw [← hidx1, ← hidx3]; exact hbij.2.mp hall⟩

/-! ## 3. Track 4: Unconditional Raw-Orbit $(p, q)$ Cutoff & $1.709511$ Complexity Lower Bound -/

/-- **Unconditional Raw-Orbit Repeated-Parity-Window $(p, q)$ Cutoff
(`raw_orbit_repeated_parity_window_pq_cutoff`, Track 4.2(1))**:
For **every** positive integer seed `1 ≤ a_0 < 2^W` (with **no** Mahler companion or block-chain
assumption!), if a length-`m` parity window repeats at `n₁ < n₂`
(`∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2`), then:
1. `2^m + 1 ≤ orbit a_0 n₂` and `2^(m + n₂) < 3^n₂ * 2^W`,
2. For every `p, q : ℕ` with `1 ≤ q` and `3^q ≤ 2^(p + q)`:
   `q * m < p * n₂ + q * W` (and at `(p, q) = (10, 17)`, `17 * m < 10 * n₂ + 17 * W`). -/
theorem raw_orbit_repeated_parity_window_pq_cutoff {a_0 W n₁ n₂ m : ℕ}
    (ha0 : 1 ≤ a_0) (hW : a_0 < 2 ^ W) (hlt : n₁ < n₂)
    (hmatch : ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) :
    (2 ^ m + 1 ≤ orbit a_0 n₂ ∧ 2 ^ (m + n₂) < 3 ^ n₂ * 2 ^ W) ∧
      (∀ p q : ℕ, 1 ≤ q → 3 ^ q ≤ 2 ^ (p + q) → q * m < p * n₂ + q * W) ∧
      17 * m < 10 * n₂ + 17 * W := by
  rcases orbit_strictMono_of_pos ha0 with ⟨hstep, hmono, hbound⟩
  have hb1_pos : 1 ≤ orbit a_0 n₁ := (hstep n₁).1
  have hb_lt : orbit a_0 n₁ < orbit a_0 n₂ := hmono n₁ n₂ hlt
  have hmod2m : orbit a_0 n₁ % 2 ^ m = orbit a_0 n₂ % 2 ^ m :=
    (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₂ m).1.mpr hmatch
  have hdvd : 2 ^ m ∣ (orbit a_0 n₂ - orbit a_0 n₁) :=
    (Nat.modEq_iff_dvd' (le_of_lt hb_lt)).mp hmod2m
  have hdiff_ge : 2 ^ m ≤ orbit a_0 n₂ - orbit a_0 n₁ :=
    Nat.le_of_dvd (by omega) hdvd
  have hb2_ge : 2 ^ m + 1 ≤ orbit a_0 n₂ := by omega
  have hexp_lt : 2 ^ (m + n₂) < 3 ^ n₂ * 2 ^ W := by
    have h1 : 2 ^ m < orbit a_0 n₂ + 1 := by omega
    have h2 : 2 ^ n₂ * 2 ^ m < 2 ^ n₂ * (orbit a_0 n₂ + 1) :=
      Nat.mul_lt_mul_of_pos_left h1 (Nat.pow_pos (by decide))
    have h3 : 2 ^ n₂ * (orbit a_0 n₂ + 1) ≤ 3 ^ n₂ * (a_0 + 1) := hbound n₂
    have h4 : 3 ^ n₂ * (a_0 + 1) ≤ 3 ^ n₂ * 2 ^ W :=
      Nat.mul_le_mul_left (3 ^ n₂) (by omega)
    rw [pow_add, mul_comm (2 ^ m) (2 ^ n₂)]
    omega
  have hpq_cut : ∀ p q : ℕ, 1 ≤ q → 3 ^ q ≤ 2 ^ (p + q) → q * m < p * n₂ + q * W := by
    intro p q hq hpq
    have hpow_q : (2 ^ (m + n₂)) ^ q < (3 ^ n₂ * 2 ^ W) ^ q :=
      Nat.pow_lt_pow_left hexp_lt (by omega)
    have hlhs : (2 ^ (m + n₂)) ^ q = 2 ^ (q * m + q * n₂) := by
      rw [← pow_mul, show (m + n₂) * q = q * m + q * n₂ by ring]
    have hrhs1 : (3 ^ n₂ * 2 ^ W) ^ q = (3 ^ q) ^ n₂ * 2 ^ (q * W) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n₂ q, pow_mul, mul_comm W q]
    have hrhs2 : (3 ^ q) ^ n₂ * 2 ^ (q * W) ≤ (2 ^ (p + q)) ^ n₂ * 2 ^ (q * W) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpq n₂)
    have hrhs3 : (2 ^ (p + q)) ^ n₂ * 2 ^ (q * W) = 2 ^ (p * n₂ + q * W + q * n₂) := by
      rw [← pow_mul, ← pow_add, show (p + q) * n₂ + q * W = p * n₂ + q * W + q * n₂ by ring]
    have hpow_lt : 2 ^ (q * m + q * n₂) < 2 ^ (p * n₂ + q * W + q * n₂) := by
      calc
        2 ^ (q * m + q * n₂) = (2 ^ (m + n₂)) ^ q := hlhs.symm
        _ < (3 ^ n₂ * 2 ^ W) ^ q := hpow_q
        _ = (3 ^ q) ^ n₂ * 2 ^ (q * W) := hrhs1
        _ ≤ (2 ^ (p + q)) ^ n₂ * 2 ^ (q * W) := hrhs2
        _ = 2 ^ (p * n₂ + q * W + q * n₂) := hrhs3
    have hexp : q * m + q * n₂ < p * n₂ + q * W + q * n₂ :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow_lt
    omega
  exact ⟨⟨hb2_ge, hexp_lt⟩, hpq_cut, hpq_cut 10 17 (by decide) (by decide)⟩

/-- Parity stream of `orbit a_0`: `orbitParityStream a_0 n = orbit a_0 n % 2`. -/
def orbitParityStream (a_0 : ℕ) (n : ℕ) : ℕ :=
  orbit a_0 n % 2

/-- **Unconditional Transcendental $\frac{\log 2}{\log(3/2)} \approx 1.709511$ Parity-Complexity
Lower Bound for ALL Positive Integers (`raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds`,
Track 4.2(2))**:
For **every** positive integer seed `1 ≤ a_0` (whether or not `a_0` is a $Z$-number candidate!):
1. If `prefixFactorCount (orbitParityStream a_0) m C ≤ C` and `a_0 < 2^W`, then for every
   `p, q : ℕ` with `1 ≤ q` and `3^q ≤ 2^(p + q)`, `q * m < p * C + q * W`
   (and for `m = 10 * k + W`, `17 * k + 1 ≤ prefixFactorCount (orbitParityStream a_0) (10 * k + W) (17 * k)`).
2. For every real slope `κ : ℝ` and constant `C_0 ≥ 0` satisfying
   `κ * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ)`,
   the parity stream `orbitParityStream a_0` cannot satisfy
   `prefixFactorCount (orbitParityStream a_0) m (C m) ≤ C m ∧ (C m : ℝ) ≤ κ * m + C_0`
   at arbitrarily large window lengths `m`. -/
theorem raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds
    {a_0 : ℕ} (ha0 : 1 ≤ a_0) :
    (∀ {W m C p q : ℕ}, a_0 < 2 ^ W → 1 ≤ q → 3 ^ q ≤ 2 ^ (p + q) →
      prefixFactorCount (orbitParityStream a_0) m C ≤ C →
        q * m < p * C + q * W) ∧
    (∀ {W : ℕ} (k : ℕ), a_0 < 2 ^ W →
      17 * k + 1 ≤ prefixFactorCount (orbitParityStream a_0) (10 * k + W) (17 * k)) ∧
    (∀ (κ C_0 : ℝ) (C : ℕ → ℕ),
      0 ≤ C_0 →
      κ * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ) →
      ¬ (∀ m_min : ℕ, ∃ m ≥ m_min,
        prefixFactorCount (orbitParityStream a_0) m (C m) ≤ C m ∧
          (C m : ℝ) ≤ κ * (m : ℝ) + C_0)) := by
  have hpq_card :
      ∀ {W m C p q : ℕ}, a_0 < 2 ^ W → 1 ≤ q → 3 ^ q ≤ 2 ^ (p + q) →
        prefixFactorCount (orbitParityStream a_0) m C ≤ C →
          q * m < p * C + q * W := by
    intro W m C p q hW hq hpq hcard
    obtain ⟨n₁, n₂, hlt, hn₂_le, hmatch⟩ :=
      (prefixFactorCount_le_iff_exists_repeated_subword (orbitParityStream a_0) m C).mp hcard
    have hmatch_orb : ∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2 :=
      hmatch
    have hcut :=
      (raw_orbit_repeated_parity_window_pq_cutoff ha0 hW hlt hmatch_orb).2.1 p q hq hpq
    have hmul : p * n₂ ≤ p * C := Nat.mul_le_mul_left p hn₂_le
    omega
  refine ⟨hpq_card, ?_, ?_⟩
  · intro W k hW
    by_contra hle
    have hcard : prefixFactorCount (orbitParityStream a_0) (10 * k + W) (17 * k) ≤ 17 * k := by
      omega
    have hcut := hpq_card hW (by decide : 1 ≤ 17) (by decide : 3 ^ 17 ≤ 2 ^ (10 + 17)) hcard
    omega
  · intro κ C_0 C hC0 hlog hliminf
    obtain ⟨p, q, hq, hpq_lt, hsub⟩ := exists_pq_of_lt_log_threshold hlog
    have hpq : 3 ^ q ≤ 2 ^ (p + q) := le_of_lt hpq_lt
    have hpow_self : ∀ n : ℕ, n < 2 ^ n := by
      intro n
      induction n with
      | zero => decide
      | succ k ih =>
          have hp : 1 ≤ 2 ^ k := Nat.pow_pos (by decide)
          rw [pow_succ]
          omega
    set W := a_0
    have hW : a_0 < 2 ^ W := hpow_self a_0
    set gap : ℝ := (q : ℝ) - (p : ℝ) * κ
    have hgap_pos : 0 < gap := by unfold gap; linarith
    set RHS : ℝ := (p : ℝ) * C_0 + (q : ℝ) * (W : ℝ)
    obtain ⟨m_min, hm_min⟩ := exists_nat_gt (RHS / gap + 1)
    obtain ⟨m, hm_ge, hcard, hC_bound⟩ := hliminf m_min
    have hcut_nat : q * m + 1 ≤ p * C m + q * W :=
      hpq_card hW hq hpq hcard
    have hcut_real :
        (q : ℝ) * (m : ℝ) + 1 ≤ (p : ℝ) * (C m : ℝ) + (q : ℝ) * (W : ℝ) := by
      exact_mod_cast hcut_nat
    have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hp_mul : (p : ℝ) * (C m : ℝ) ≤ (p : ℝ) * (κ * (m : ℝ) + C_0) :=
      mul_le_mul_of_nonneg_left hC_bound hp_nonneg
    have hgap_le : gap * (m : ℝ) + 1 ≤ RHS := by
      unfold gap RHS; linarith
    have hm_real : (m_min : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
    have h1 : RHS / gap < (m : ℝ) := by linarith
    have h2 : RHS < (m : ℝ) * gap := (div_lt_iff₀ hgap_pos).mp h1
    linarith

/-! ## 4. Section 7: The Mod-3 Valuation Trichotomy & Exact Symbolic Epoch Coding -/

/-- **Master Mod-3 Valuation Identity (`three_mul_affInv_eq_nineteen_mul_add_eight`, Section 7)**:
For every natural number `b`, `3 * (19 * b + 9) = 19 * (3 * b + 1) + 8`. -/
theorem three_mul_affInv_eq_nineteen_mul_add_eight (b : ℕ) :
    3 * (19 * b + 9) = 19 * (3 * b + 1) + 8 := by
  ring

/-- **The 4-Way 2-Adic Valuation Trichotomy on `19 * b + 9`
(`two_adic_valuation_affInv_trichotomy`, Section 7)**:
Let `b, s, u : ℕ` satisfy `3 * b + 1 = 2^s * u` with `u % 2 = 1`. Then:
1. `s = 1 ↔ (2 ∣ (19 * b + 9) ∧ ¬ (4 ∣ (19 * b + 9)))` (`v_2(19b+9) = 1`, the forbidden `11` class),
2. `s = 2 ↔ (4 ∣ (19 * b + 9) ∧ ¬ (8 ∣ (19 * b + 9)))` (`v_2(19b+9) = 2`, the `s = 2` exit class),
3. `4 ≤ s ↔ (8 ∣ (19 * b + 9) ∧ ¬ (16 ∣ (19 * b + 9)))` (`v_2(19b+9) = 3`, the `s ≥ 4` defect exit class),
4. `s = 3 ↔ 16 ∣ (19 * b + 9)` (`v_2(19b+9) ≥ 4`, the `100` continuation class), and
5. `s = 0 ↔ ¬ (2 ∣ (19 * b + 9))` (when `b` is even). -/
theorem two_adic_valuation_affInv_trichotomy {b s u : ℕ}
    (hblock : 3 * b + 1 = 2 ^ s * u) (hu : u % 2 = 1) :
    (s = 1 ↔ (2 ∣ (19 * b + 9) ∧ ¬ (4 ∣ (19 * b + 9)))) ∧
      (s = 2 ↔ (4 ∣ (19 * b + 9) ∧ ¬ (8 ∣ (19 * b + 9)))) ∧
      (4 ≤ s ↔ (8 ∣ (19 * b + 9) ∧ ¬ (16 ∣ (19 * b + 9)))) ∧
      (s = 3 ↔ 16 ∣ (19 * b + 9)) ∧
      (s = 0 ↔ ¬ (2 ∣ (19 * b + 9))) := by
  have hid := three_mul_affInv_eq_nineteen_mul_add_eight b
  rw [hblock] at hid
  have hdvd_three : ∀ k : ℕ, 2 ^ k ∣ (19 * b + 9) ↔ 2 ^ k ∣ 3 * (19 * b + 9) := by
    intro k
    have hcop : Nat.Coprime (2 ^ k) 3 := (by decide : Nat.Coprime 2 3).pow_left k
    exact ⟨fun h => dvd_mul_of_dvd_right h 3, fun h => hcop.dvd_of_dvd_mul_left h⟩
  have hmod_three : ∀ k : ℕ, (19 * b + 9) % 2 ^ k = 0 ↔ (3 * (19 * b + 9)) % 2 ^ k = 0 := by
    intro k
    rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    exact hdvd_three k
  have hm1 : 2 ∣ (19 * b + 9) ↔ (19 * (2 ^ s * u) + 8) % 2 = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← hid]; exact hmod_three 1
  have hm2 : 4 ∣ (19 * b + 9) ↔ (19 * (2 ^ s * u) + 8) % 4 = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← hid]; exact hmod_three 2
  have hm3 : 8 ∣ (19 * b + 9) ↔ (19 * (2 ^ s * u) + 8) % 8 = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← hid]; exact hmod_three 3
  have hm4 : 16 ∣ (19 * b + 9) ↔ (19 * (2 ^ s * u) + 8) % 16 = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← hid]; exact hmod_three 4
  rw [hm1, hm2, hm3, hm4]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, u = 2 * m + 1 := ⟨u / 2, by omega⟩
  have hpart : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ 4 ≤ s := by omega
  rcases hpart with rfl | rfl | rfl | rfl | hs4
  · have h0 : 19 * (2 ^ 0 * (2 * m + 1)) + 8 = 16 * (2 * m + 1) + 2 * (3 * m + 5) + 1 := by ring
    rw [h0]
    omega
  · have h1' : 19 * (2 ^ 1 * (2 * m + 1)) + 8 = 4 * (19 * m + 11) + 2 := by ring
    rw [h1']
    omega
  · have h2' : 19 * (2 ^ 2 * (2 * m + 1)) + 8 = 8 * (19 * m + 10) + 4 := by ring
    rw [h2']
    omega
  · have h3' : 19 * (2 ^ 3 * (2 * m + 1)) + 8 = 16 * (19 * m + 10) := by ring
    rw [h3']
    omega
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, s = d + 4 := ⟨s - 4, by omega⟩
    have h4' : 19 * (2 ^ (d + 4) * (2 * m + 1)) + 8 = 16 * (19 * (2 ^ d * (2 * m + 1))) + 8 := by
      rw [pow_add]; ring
    have hm_2 : (19 * (2 ^ (d + 4) * (2 * m + 1)) + 8) % 2 = 0 := by rw [h4']; omega
    have hm_4 : (19 * (2 ^ (d + 4) * (2 * m + 1)) + 8) % 4 = 0 := by rw [h4']; omega
    have hm_8 : (19 * (2 ^ (d + 4) * (2 * m + 1)) + 8) % 8 = 0 := by rw [h4']; omega
    have hm_16 : (19 * (2 ^ (d + 4) * (2 * m + 1)) + 8) % 16 = 8 := by rw [h4']; omega
    simp [hm_2, hm_4, hm_8, hm_16]

/-- **Exact Run-Length & Exit-Type Coding by `v_2(19 * b_0 + 9)`
(`epoch_period_three_run_exit_trichotomy`, Section 7)**:
Suppose a sequence of odd boundaries `b : ℕ → ℕ` undergoes `j` consecutive blocks of length `3`
(`8 * (19 * b (k + 1) + 9) = 27 * (19 * b k + 9)` for all `k < j`), and at step `j` has
`3 * b j + 1 = 2^s_j * u_j` with `u_j % 2 = 1`.
If `19 * b 0 + 9 = 2^(3 * j + r) * q` with `q % 2 = 1`:
1. `19 * b j + 9 = 2^r * (27^j * q)`,
2. **Mod-3 Death Class (`r = 1`)**: `r = 1 ↔ s_j = 1` (the forbidden `11` transition),
3. **Mod-3 Short-Block Class (`r = 2`)**: `r = 2 ↔ s_j = 2`, and
4. **Mod-3 Defect Class (`r = 3`)**: `r = 3 ↔ 4 ≤ s_j`. -/
theorem epoch_period_three_run_exit_trichotomy {b : ℕ → ℕ} {j r q s_j u_j : ℕ}
    (hrun : ∀ k < j, 8 * (19 * b (k + 1) + 9) = 27 * (19 * b k + 9))
    (hexit : 3 * b j + 1 = 2 ^ s_j * u_j)
    (hu_j : u_j % 2 = 1)
    (hb0 : 19 * b 0 + 9 = 2 ^ (3 * j + r) * q)
    (hq : q % 2 = 1) :
    19 * b j + 9 = 2 ^ r * (27 ^ j * q) ∧
      (r = 1 ↔ s_j = 1) ∧
      (r = 2 ↔ s_j = 2) ∧
      (r = 3 ↔ 4 ≤ s_j) := by
  have hiter : 8 ^ j * (19 * b j + 9) = 27 ^ j * (19 * b 0 + 9) := by
    clear hexit hb0
    induction j with
    | zero => simp
    | succ m ih =>
        have ihm := ih (fun k hk => hrun k (by omega))
        have hstep := hrun m (by omega)
        calc
          8 ^ (m + 1) * (19 * b (m + 1) + 9)
            = 8 ^ m * (8 * (19 * b (m + 1) + 9)) := by rw [pow_succ]; ring
          _ = 8 ^ m * (27 * (19 * b m + 9)) := by rw [hstep]
          _ = 27 * (8 ^ m * (19 * b m + 9)) := by ring
          _ = 27 * (27 ^ m * (19 * b 0 + 9)) := by rw [ihm]
          _ = 27 ^ (m + 1) * (19 * b 0 + 9) := by rw [pow_succ']; ring
  have h8j : 8 ^ j = 2 ^ (3 * j) := by
    rw [show (8 : ℕ) = 2 ^ 3 by rfl, ← pow_mul]
  have hbj_eq : 19 * b j + 9 = 2 ^ r * (27 ^ j * q) := by
    have h1 : 8 ^ j * (19 * b j + 9) = 8 ^ j * (2 ^ r * (27 ^ j * q)) := by
      rw [hiter, hb0, pow_add, ← h8j]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h1
  have h27q_odd : (27 ^ j * q) % 2 = 1 := by
    have h27_odd : ∀ n : ℕ, 27 ^ n % 2 = 1 := by
      intro n
      induction n with
      | zero => rfl
      | succ m ih => rw [pow_succ, Nat.mul_mod, ih]
    rw [Nat.mul_mod, h27_odd j, hq]
  have htri := two_adic_valuation_affInv_trichotomy hexit hu_j
  have hdvd_pow : ∀ k : ℕ, 2 ^ k ∣ (19 * b j + 9) ↔ k ≤ r := by
    intro k
    rw [hbj_eq]
    constructor
    · intro hdvd
      by_contra hgt
      have hkr : r + 1 ≤ k := by omega
      obtain ⟨c, hc⟩ := dvd_trans (Nat.pow_dvd_pow 2 hkr) hdvd
      have hmul : 2 ^ r * (27 ^ j * q) = 2 ^ r * (2 * c) := by
        calc
          2 ^ r * (27 ^ j * q) = 2 ^ (r + 1) * c := hc
          _ = 2 ^ r * (2 * c) := by rw [pow_succ]; ring
      have heven : 27 ^ j * q = 2 * c :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul
      omega
    · intro hle
      exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hle) _
  have hd1 : 2 ∣ (19 * b j + 9) ↔ 1 ≤ r := hdvd_pow 1
  have hd2 : 4 ∣ (19 * b j + 9) ↔ 2 ≤ r := hdvd_pow 2
  have hd3 : 8 ∣ (19 * b j + 9) ↔ 3 ≤ r := hdvd_pow 3
  have hd4 : 16 ∣ (19 * b j + 9) ↔ 4 ≤ r := hdvd_pow 4
  rw [htri.1, htri.2.1, htri.2.2.1, hd1, hd2, hd3, hd4]
  refine ⟨hbj_eq, ?_, ?_, ?_⟩ <;> omega

end Mahler.UniversalOrbitBijection
