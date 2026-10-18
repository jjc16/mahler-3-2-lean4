import TwoSidedSqueeze

/-!
# Sharpened Two-Sided Squeezes: Moving the Lower Bound Higher and the Upper Bound Lower

This module tightens **both ends** of Squeeze 1 and Squeeze 2 from
`TwoSidedSqueeze.lean`:

1. **The Fundamental Odd-Return Fixed-Point Identity (`three_mul_fixed_point_term_eq`)**:
   For any block length `c ≥ 1` and integer `b`,
   `3 * ((3^c - 2^c) * b + 3^(c - 1)) = (3^c - 2^c) * (3 * b + 1) + 2^c`.
2. **Moving the Lower Bound Higher (`sharpened_odd_block_repeat_bound`,
   `sharpened_odd_block_repeat_bound_min`, `odd_block_repeat_not_dvd_of_lt`)**:
   - Applying `three_mul_fixed_point_term_eq` at the end `b m` of an `m`-block run
     of length `c`, any power `2^d` (`d ≤ c`) dividing `3 * b m + 1` also divides
     `(3^c - 2^c) * b m + 3^(c - 1)`, boosting the 2-adic divisibility and lower
     bound from `2^(c * m)` to `2^(c * m + d)`:
     `2^(c * m + min c s_next) ∣ ((3^c - 2^c) * b 0 + 3^(c - 1))` and
     `2^(c * m + min c s_next) ≤ (3^c - 2^c) * b 0 + 3^(c - 1)`.
   - When the run exits to a strictly smaller block `s_next < c` (`3 * b m + 1 = 2^s_next * u_next`
     with `u_next` odd), the 2-adic valuation is locked at `c * m + s_next`:
     `¬ (2^(c * m + s_next + 1) ∣ ((3^c - 2^c) * b 0 + 3^(c - 1)))`.
3. **Moving the Upper Bound Lower (`odd_return_three_corridor`,
   `sharpened_intermediate_repeat_squeeze`, `sharpened_coasting_repeat_squeeze`)**:
   - Because `b 0 = orbit a_0 T` is odd at an odd return `T`, step `T + 1` gives the
     tightened corridor `2^(T + 1) * (3 * orbit a_0 T + 1) < 3^(T + 1) * (2 * a_0 + 1)`.
   - Applying `three_mul_fixed_point_term_eq` at `b 0` cancels the `3^c` remainder
     against `-(3^c - 2^c)`, shrinking the additive remainder from `3^c` to `2^c`:
     `3 * 2^(c * m + d + T + 1) < (3^c - 2^c) * 3^(T + 1) * (2 * a_0 + 1) + 2^(T + c + 1)`.
   - In the coasting regime (`a_0 < 2^W`, `W ≤ T`), canceling `2^(W + 1)` yields:
     `3 * 2^(c * m + d + (T - W)) < (3^c - 2^c) * 3^(T + 1) + 2^((T - W) + c)`.
4. **Tightening Both Ends of Squeeze 1 (`sharpened_archimedean_deficiency_squeeze`,
   `integerSlack_le_pow_mul_prefix`)**:
   - Lookahead lower-bound boost: surviving one step past `k + m` (`0 < integerSlack s (k + m + 1)`)
     forces `2^(blockSteps s (k + m + 1) + 1) < 3^(s (k + m)) * integerSlack s (k + m)`,
     raising the lower bound on `3^(c * m + s (k + m)) * slackDeficiency s c k`.
   - Prefix slack ceiling: `integerSlack s (j + r) ≤ 3^(blockSteps s (j + r) - blockSteps s j) * integerSlack s j`.
-/

namespace Mahler.SharpenedSqueezes

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB
open Mahler.JumpValuation
open Mahler.EscapeBranchCap
open Mahler.PhaseLock
open Mahler.MasterReduction
open Mahler.ModEightClassifier
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.KernelDuality
open Mahler.Coasting
open Mahler.TwoSidedSqueeze

/-! ## 1. The Fundamental Odd-Return Fixed-Point Identity -/

/-- **Fundamental Odd-Return Fixed-Point Identity (`three_mul_fixed_point_term_eq`)**:
For any `c ≥ 1` and `b : ℕ`,
`3 * ((3^c - 2^c) * b + 3^(c - 1)) = (3^c - 2^c) * (3 * b + 1) + 2^c`. -/
theorem three_mul_fixed_point_term_eq {c : ℕ} (hc : 1 ≤ c) (b : ℕ) :
    3 * ((3 ^ c - 2 ^ c) * b + 3 ^ (c - 1)) =
      (3 ^ c - 2 ^ c) * (3 * b + 1) + 2 ^ c := by
  have h3c : 3 * 3 ^ (c - 1) = 3 ^ c := by
    have hsub : c = (c - 1) + 1 := by omega
    conv_rhs => rw [hsub, Nat.pow_succ]
    ring
  have hle : 2 ^ c ≤ 3 ^ c := Nat.pow_le_pow_left (by decide) c
  calc
    3 * ((3 ^ c - 2 ^ c) * b + 3 ^ (c - 1)) =
        (3 ^ c - 2 ^ c) * (3 * b) + 3 * 3 ^ (c - 1) := by ring
    _ = (3 ^ c - 2 ^ c) * (3 * b) + 3 ^ c := by rw [h3c]
    _ = (3 ^ c - 2 ^ c) * (3 * b) + ((3 ^ c - 2 ^ c) + 2 ^ c) := by
        rw [Nat.sub_add_cancel hle]
    _ = (3 ^ c - 2 ^ c) * (3 * b + 1) + 2 ^ c := by ring

/-! ## 2. Moving the Lower Bound Higher: Exit-Block Divisibility Boost & Valuation Lock -/

/-- If `d ≤ c` and `2^d ∣ (3 * b + 1)`, then `2^d ∣ ((3^c - 2^c) * b + 3^(c - 1))`. -/
theorem pow_two_dvd_fixed_point_term {c d b : ℕ} (hc : 1 ≤ c) (hdc : d ≤ c)
    (hdvd : 2 ^ d ∣ (3 * b + 1)) :
    2 ^ d ∣ ((3 ^ c - 2 ^ c) * b + 3 ^ (c - 1)) := by
  have hdvd_rhs : 2 ^ d ∣ ((3 ^ c - 2 ^ c) * (3 * b + 1) + 2 ^ c) := by
    have h1 : 2 ^ d ∣ (3 ^ c - 2 ^ c) * (3 * b + 1) :=
      dvd_mul_of_dvd_right hdvd (3 ^ c - 2 ^ c)
    have h2 : 2 ^ d ∣ 2 ^ c := Nat.pow_dvd_pow 2 hdc
    exact Nat.dvd_add h1 h2
  rw [← three_mul_fixed_point_term_eq hc b] at hdvd_rhs
  have hg : Nat.Coprime (2 ^ d) 3 :=
    Nat.Coprime.pow_left d (by decide : Nat.Coprime 2 3)
  exact hg.dvd_of_dvd_mul_left hdvd_rhs

/-- **Sharpened Block-Repetition Lower Bound (`sharpened_odd_block_repeat_bound`)**:
If `b 0` undergoes `m` consecutive odd-to-odd blocks of length `c ≥ 1` and at
the terminal state `b m` we have `2^d ∣ (3 * b m + 1)` with `d ≤ c`, then
`2^(c * m + d)` divides `(3^c - 2^c) * b 0 + 3^(c - 1)` and
`2^(c * m + d) ≤ (3^c - 2^c) * b 0 + 3^(c - 1)`. -/
theorem sharpened_odd_block_repeat_bound {c d : ℕ} (hc : 1 ≤ c) (hdc : d ≤ c)
    (b u : ℕ → ℕ) (m : ℕ)
    (hstep : ∀ k < m, 3 * b k + 1 = 2 ^ c * u k ∧ b (k + 1) = orbit (b k) c)
    (hnext : 2 ^ d ∣ (3 * b m + 1)) :
    2 ^ (c * m + d) ∣ ((3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1)) ∧
      2 ^ (c * m + d) ≤ (3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1) := by
  have hchain := odd_block_chain_fixed_point hc b u m hstep
  have hdvd_end := pow_two_dvd_fixed_point_term hc hdc hnext
  have hdvd_prod :
      2 ^ (c * m + d) ∣ 3 ^ (c * m) * ((3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1)) := by
    rw [← hchain, Nat.pow_add]
    exact mul_dvd_mul_left (2 ^ (c * m)) hdvd_end
  have hg : Nat.Coprime (2 ^ (c * m + d)) (3 ^ (c * m)) :=
    (Nat.Coprime.pow_left (c * m + d) (by decide : Nat.Coprime 2 3)).pow_right (c * m)
  have hdvd0 : 2 ^ (c * m + d) ∣ ((3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1)) :=
    hg.dvd_of_dvd_mul_left hdvd_prod
  have hpos : 0 < (3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1) := by
    have h3 : 0 < 3 ^ (c - 1) := Nat.pow_pos (by decide)
    omega
  exact ⟨hdvd0, Nat.le_of_dvd hpos hdvd0⟩

/-- **Specialization to Next Block Length `s_next` (`sharpened_odd_block_repeat_bound_min`)**:
If `3 * b m + 1 = 2^s_next * u_next` at the end of an `m`-block run of length
`c ≥ 1`, then `2^(c * m + min c s_next)` divides `(3^c - 2^c) * b 0 + 3^(c - 1)`
and `2^(c * m + min c s_next) ≤ (3^c - 2^c) * b 0 + 3^(c - 1)`. -/
theorem sharpened_odd_block_repeat_bound_min {c s_next u_next : ℕ} (hc : 1 ≤ c)
    (b u : ℕ → ℕ) (m : ℕ)
    (hstep : ∀ k < m, 3 * b k + 1 = 2 ^ c * u k ∧ b (k + 1) = orbit (b k) c)
    (hnext : 3 * b m + 1 = 2 ^ s_next * u_next) :
    2 ^ (c * m + min c s_next) ∣ ((3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1)) ∧
      2 ^ (c * m + min c s_next) ≤ (3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1) := by
  apply sharpened_odd_block_repeat_bound hc (Nat.min_le_left c s_next) b u m hstep
  rw [hnext]
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (Nat.min_le_right c s_next)) u_next

/-- **Downward-Transition 2-adic Valuation Lock (`odd_block_repeat_not_dvd_of_lt`)**:
When an `m`-block run of length `c` exits to a strictly smaller block
`s_next < c` (`3 * b m + 1 = 2^s_next * u_next` with `u_next % 2 = 1`),
`2^(c * m + s_next + 1)` does **not** divide `(3^c - 2^c) * b 0 + 3^(c - 1)`. -/
theorem odd_block_repeat_not_dvd_of_lt {c s_next u_next : ℕ}
    (hs_lt : s_next < c) (hu_odd : u_next % 2 = 1)
    (b u : ℕ → ℕ) (m : ℕ)
    (hstep : ∀ k < m, 3 * b k + 1 = 2 ^ c * u k ∧ b (k + 1) = orbit (b k) c)
    (hnext : 3 * b m + 1 = 2 ^ s_next * u_next) :
    ¬ (2 ^ (c * m + s_next + 1) ∣ ((3 ^ c - 2 ^ c) * b 0 + 3 ^ (c - 1))) := by
  intro hdvd0
  have hc : 1 ≤ c := by omega
  have hchain := odd_block_chain_fixed_point hc b u m hstep
  have hdvd_lhs :
      2 ^ (c * m + s_next + 1) ∣
        2 ^ (c * m) * ((3 ^ c - 2 ^ c) * b m + 3 ^ (c - 1)) := by
    rw [hchain]
    exact dvd_mul_of_dvd_right hdvd0 (3 ^ (c * m))
  have hdvd_end :
      2 ^ (s_next + 1) ∣ ((3 ^ c - 2 ^ c) * b m + 3 ^ (c - 1)) := by
    rw [show c * m + s_next + 1 = c * m + (s_next + 1) by omega, Nat.pow_add] at hdvd_lhs
    exact (Nat.mul_dvd_mul_iff_left (Nat.pow_pos (by decide : 0 < 2))).mp hdvd_lhs
  have hdvd3 :
      2 ^ (s_next + 1) ∣ 3 * ((3 ^ c - 2 ^ c) * b m + 3 ^ (c - 1)) :=
    dvd_mul_of_dvd_right hdvd_end 3
  rw [three_mul_fixed_point_term_eq hc (b m), hnext] at hdvd3
  have hdvd2c : 2 ^ (s_next + 1) ∣ 2 ^ c :=
    Nat.pow_dvd_pow 2 (by omega : s_next + 1 ≤ c)
  have hdvd_term :
      2 ^ (s_next + 1) ∣ (3 ^ c - 2 ^ c) * (2 ^ s_next * u_next) :=
    (Nat.dvd_add_left hdvd2c).mp hdvd3
  have hdvd_rearrange :
      2 ^ s_next * 2 ∣ 2 ^ s_next * ((3 ^ c - 2 ^ c) * u_next) := by
    simpa [Nat.pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdvd_term
  have hdvd_two : 2 ∣ (3 ^ c - 2 ^ c) * u_next :=
    (Nat.mul_dvd_mul_iff_left (Nat.pow_pos (by decide : 0 < 2))).mp hdvd_rearrange
  have h3pow_all : ∀ k : ℕ, 3 ^ k % 2 = 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Nat.pow_succ]
        omega
  have h3pow_odd : 3 ^ c % 2 = 1 := h3pow_all c
  have h2pow_even : 2 ^ c % 2 = 0 := by
    have hsub : c = (c - 1) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    omega
  have hle : 2 ^ c ≤ 3 ^ c := Nat.pow_le_pow_left (by decide) c
  have hdiff_odd : (3 ^ c - 2 ^ c) % 2 = 1 := by omega
  have hprod_odd : ((3 ^ c - 2 ^ c) * u_next) % 2 = 1 := by
    rw [Nat.mul_mod, hdiff_odd, hu_odd]
  have hprod_even : ((3 ^ c - 2 ^ c) * u_next) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd_two
  omega

/-! ## 3. Moving the Upper Bound Lower: The Odd-Return Corridor & Sharpened Squeeze 2 -/

/-- **Odd-Return Corridor Bound (`odd_return_three_corridor`)**:
If `orbit a_0 T` is odd (`orbit a_0 T % 2 = 1`) and the trajectory survives
through step `T + 1`, then
`2^(T + 1) * (3 * orbit a_0 T + 1) < 3^(T + 1) * (2 * a_0 + 1)`. -/
theorem odd_return_three_corridor {a_0 T : ℕ} {ξ : ℝ}
    (hodd : orbit a_0 T % 2 = 1)
    (hsurv : ValidCompanionUpTo a_0 ξ (T + 1)) :
    2 ^ (T + 1) * (3 * orbit a_0 T + 1) < 3 ^ (T + 1) * (2 * a_0 + 1) := by
  have hcor := (surviving_orbit_half_corridor hsurv).2
  have hstep : 2 * orbit a_0 (T + 1) = 3 * orbit a_0 T + 1 := by
    change 2 * step (orbit a_0 T) = 3 * orbit a_0 T + 1
    unfold step
    omega
  calc
    2 ^ (T + 1) * (3 * orbit a_0 T + 1) =
        2 ^ (T + 1) * (2 * orbit a_0 (T + 1)) := by rw [hstep]
    _ = 2 ^ (T + 1 + 1) * orbit a_0 (T + 1) := by
        rw [Nat.pow_succ]
        ring
    _ < 3 ^ (T + 1) * (2 * a_0 + 1) := hcor

/-- **Sharpened Squeeze 2 (`sharpened_intermediate_repeat_squeeze`)**:
Combining `sharpened_odd_block_repeat_bound`, `three_mul_fixed_point_term_eq`,
and `odd_return_three_corridor` simultaneously raises the lower bound by `2^d`
(`d ≤ c`, `2^d ∣ (3 * b m + 1)`) and reduces the additive upper-bound remainder
from `3^c` to `2^c`:
`3 * 2^(c * m + d + T + 1) < (3^c - 2^c) * 3^(T + 1) * (2 * a_0 + 1) + 2^(T + c + 1)`. -/
theorem sharpened_intermediate_repeat_squeeze {a_0 T c d m : ℕ}
    (hc : 1 ≤ c) (hdc : d ≤ c)
    (b u' : ℕ → ℕ) (hb0 : b 0 = orbit a_0 T)
    (hodd0 : orbit a_0 T % 2 = 1)
    (hstep : ∀ i < m, 3 * b i + 1 = 2 ^ c * u' i ∧ b (i + 1) = orbit (b i) c)
    (hnext : 2 ^ d ∣ (3 * b m + 1))
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (T + 1)) :
    3 * 2 ^ (c * m + d + T + 1) <
      (3 ^ c - 2 ^ c) * 3 ^ (T + 1) * (2 * a_0 + 1) + 2 ^ (T + c + 1) := by
  have hrep := (sharpened_odd_block_repeat_bound hc hdc b u' m hstep hnext).2
  rw [hb0] at hrep
  have hcor := odd_return_three_corridor hodd0 hsurv
  have hid := three_mul_fixed_point_term_eq hc (orbit a_0 T)
  have h2lt3 : 2 ^ c < 3 ^ c :=
    Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_pos : 0 < 3 ^ c - 2 ^ c := by omega
  have hmul1 :
      2 ^ (T + 1) * (3 * 2 ^ (c * m + d)) ≤
        2 ^ (T + 1) * (3 * ((3 ^ c - 2 ^ c) * orbit a_0 T + 3 ^ (c - 1))) :=
    Nat.mul_le_mul_left (2 ^ (T + 1)) (Nat.mul_le_mul_left 3 hrep)
  have hmul2 :
      (3 ^ c - 2 ^ c) * (2 ^ (T + 1) * (3 * orbit a_0 T + 1)) <
        (3 ^ c - 2 ^ c) * (3 ^ (T + 1) * (2 * a_0 + 1)) :=
    Nat.mul_lt_mul_of_pos_left hcor hdiff_pos
  calc
    3 * 2 ^ (c * m + d + T + 1) = 2 ^ (T + 1) * (3 * 2 ^ (c * m + d)) := by
      rw [show c * m + d + T + 1 = (T + 1) + (c * m + d) by omega, Nat.pow_add]
      ring
    _ ≤ 2 ^ (T + 1) * (3 * ((3 ^ c - 2 ^ c) * orbit a_0 T + 3 ^ (c - 1))) := hmul1
    _ = 2 ^ (T + 1) * ((3 ^ c - 2 ^ c) * (3 * orbit a_0 T + 1) + 2 ^ c) := by
        rw [hid]
    _ = (3 ^ c - 2 ^ c) * (2 ^ (T + 1) * (3 * orbit a_0 T + 1)) +
          2 ^ (T + c + 1) := by
        rw [show T + c + 1 = (T + 1) + c by omega, Nat.pow_add]
        ring
    _ < (3 ^ c - 2 ^ c) * (3 ^ (T + 1) * (2 * a_0 + 1)) + 2 ^ (T + c + 1) :=
        Nat.add_lt_add_right hmul2 _
    _ = (3 ^ c - 2 ^ c) * 3 ^ (T + 1) * (2 * a_0 + 1) + 2 ^ (T + c + 1) := by
        ring

/-- **Sharpened Coasting Squeeze (`sharpened_coasting_repeat_squeeze`)**:
In the coasting regime (`a_0 < 2^W` and `W ≤ T`), canceling `2^(W + 1)` from
`sharpened_intermediate_repeat_squeeze` yields the `a_0`-free inequality:
`3 * 2^(c * m + d + (T - W)) < (3^c - 2^c) * 3^(T + 1) + 2^((T - W) + c)`. -/
theorem sharpened_coasting_repeat_squeeze {a_0 W T c d m : ℕ}
    (hc : 1 ≤ c) (hdc : d ≤ c) (ha0 : a_0 < 2 ^ W) (hWT : W ≤ T)
    (b u' : ℕ → ℕ) (hb0 : b 0 = orbit a_0 T)
    (hodd0 : orbit a_0 T % 2 = 1)
    (hstep : ∀ i < m, 3 * b i + 1 = 2 ^ c * u' i ∧ b (i + 1) = orbit (b i) c)
    (hnext : 2 ^ d ∣ (3 * b m + 1))
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (T + 1)) :
    3 * 2 ^ (c * m + d + (T - W)) <
      (3 ^ c - 2 ^ c) * 3 ^ (T + 1) + 2 ^ ((T - W) + c) := by
  have hsq :=
    sharpened_intermediate_repeat_squeeze hc hdc b u' hb0 hodd0 hstep hnext hsurv
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsplit1 : c * m + d + T + 1 = (W + 1) + (c * m + d + (T - W)) := by omega
  have hsplit2 : T + c + 1 = (W + 1) + ((T - W) + c) := by omega
  have hmul :
      2 ^ (W + 1) * (3 * 2 ^ (c * m + d + (T - W))) <
        2 ^ (W + 1) * ((3 ^ c - 2 ^ c) * 3 ^ (T + 1) + 2 ^ ((T - W) + c)) := by
    calc
      2 ^ (W + 1) * (3 * 2 ^ (c * m + d + (T - W))) =
          3 * 2 ^ (c * m + d + T + 1) := by
        rw [hsplit1, Nat.pow_add]
        ring
      _ < (3 ^ c - 2 ^ c) * 3 ^ (T + 1) * (2 * a_0 + 1) + 2 ^ (T + c + 1) := hsq
      _ ≤ (3 ^ c - 2 ^ c) * 3 ^ (T + 1) * 2 ^ (W + 1) + 2 ^ (T + c + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ h2a0) _
      _ = 2 ^ (W + 1) *
            ((3 ^ c - 2 ^ c) * 3 ^ (T + 1) + 2 ^ ((T - W) + c)) := by
          conv_lhs => rw [hsplit2, Nat.pow_add]
          ring
  exact Nat.lt_of_mul_lt_mul_left hmul

/-! ## 4. Tightening Both Ends of Squeeze 1: Lookahead Floor & Prefix Slack Ceiling -/

/-- **One-Step Strict Ceiling on `integerSlack` (`integerSlack_step_lt`)**:
For every block index `n`,
`integerSlack s (n + 1) < 3^(s n) * integerSlack s n`. -/
theorem integerSlack_step_lt (s : ℕ → ℕ) (n : ℕ) :
    integerSlack s (n + 1) < (3 : ℤ) ^ (s n) * integerSlack s n := by
  rw [integerSlack_succ]
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (n + 1) + 1) :=
    pow_pos (by decide) _
  linarith

/-- **Multi-Step Prefix Ceiling on `integerSlack` (`integerSlack_le_pow_mul_prefix`)**:
For every prefix index `j` and offset `r`,
`integerSlack s (j + r) ≤ 3^(blockSteps (shiftSeq s j) r) * integerSlack s j`. -/
theorem integerSlack_le_pow_mul_prefix (s : ℕ → ℕ) (j r : ℕ) :
    integerSlack s (j + r) ≤
      (3 : ℤ) ^ (blockSteps (shiftSeq s j) r) * integerSlack s j := by
  induction r with
  | zero => simp [blockSteps]
  | succ r ih =>
      have hlt := le_of_lt (integerSlack_step_lt s (j + r))
      have hmul :
          (3 : ℤ) ^ (s (j + r)) * integerSlack s (j + r) ≤
            (3 : ℤ) ^ (s (j + r)) *
              ((3 : ℤ) ^ (blockSteps (shiftSeq s j) r) * integerSlack s j) :=
        mul_le_mul_of_nonneg_left ih (pow_nonneg (by decide) _)
      calc
        integerSlack s (j + (r + 1)) = integerSlack s ((j + r) + 1) := by
          rw [Nat.add_assoc]
        _ ≤ (3 : ℤ) ^ (s (j + r)) * integerSlack s (j + r) := hlt
        _ ≤ (3 : ℤ) ^ (s (j + r)) *
              ((3 : ℤ) ^ (blockSteps (shiftSeq s j) r) * integerSlack s j) := hmul
        _ = (3 : ℤ) ^ (blockSteps (shiftSeq s j) (r + 1)) * integerSlack s j := by
              simp only [blockSteps, shiftSeq, pow_add]
              ring

/-- **Lookahead-Sharpened Squeeze 1 (`sharpened_archimedean_deficiency_squeeze`)**:
If `1 ≤ c`, `s (k + i) = c` for all `i < m`, and the orbit survives one more
block past `k + m` so that `0 < integerSlack s (k + m + 1)`, then
`3^(c * m + s (k + m)) * slackDeficiency s c k +
  (3^c - 2^c) * 2^(c * m + s (k + m) + blockSteps s k + 1) <
  3^(s (k + m)) * 2^(c * m + c + blockSteps s k + 1)`. -/
theorem sharpened_archimedean_deficiency_squeeze (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) = c)
    (hpos_next : 0 < integerSlack s (k + m + 1)) :
    (3 : ℤ) ^ (c * m + s (k + m)) * slackDeficiency s c k +
        ((3 : ℤ) ^ c - (2 : ℤ) ^ c) *
          (2 : ℤ) ^ (c * m + s (k + m) + blockSteps s k + 1) <
      (3 : ℤ) ^ (s (k + m)) * (2 : ℤ) ^ (c * m + c + blockSteps s k + 1) := by
  have hcons := archimedean_deficiency_conservation s c k m hrun
  have hnext := integerSlack_succ s (k + m)
  have hsteps :
      blockSteps s (k + m + 1) + 1 = c * m + s (k + m) + blockSteps s k + 1 := by
    simp only [blockSteps]
    rw [blockSteps_const_run s c k m hrun]
    omega
  rw [hsteps] at hnext
  have hfloor :
      (2 : ℤ) ^ (c * m + s (k + m) + blockSteps s k + 1) <
        (3 : ℤ) ^ (s (k + m)) * integerSlack s (k + m) := by
    linarith
  have h2lt3 : (2 : ℤ) ^ c < (3 : ℤ) ^ c := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_pos : 0 < (3 : ℤ) ^ c - (2 : ℤ) ^ c := by linarith
  have hmul_floor :
      ((3 : ℤ) ^ c - (2 : ℤ) ^ c) *
          (2 : ℤ) ^ (c * m + s (k + m) + blockSteps s k + 1) <
        ((3 : ℤ) ^ c - (2 : ℤ) ^ c) *
          ((3 : ℤ) ^ (s (k + m)) * integerSlack s (k + m)) :=
    mul_lt_mul_of_pos_left hfloor hdiff_pos
  have hmul_cons :
      (3 : ℤ) ^ (s (k + m)) *
          ((3 : ℤ) ^ (c * m) * slackDeficiency s c k +
            ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * integerSlack s (k + m)) =
        (3 : ℤ) ^ (s (k + m)) * (2 : ℤ) ^ (c * m + c + blockSteps s k + 1) := by
    rw [hcons]
  have hexp :
      (3 : ℤ) ^ (c * m + s (k + m)) * slackDeficiency s c k =
        (3 : ℤ) ^ (s (k + m)) * ((3 : ℤ) ^ (c * m) * slackDeficiency s c k) := by
    rw [pow_add]
    ring
  linarith

end Mahler.SharpenedSqueezes
