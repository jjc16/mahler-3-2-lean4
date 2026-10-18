import ConverseCompanionReconstruction

/-!
# Explicit Linear Horizon Cutoffs, Coasting Tree Branching Caps & Closed-Form Seeds

This module converts our exponential two-sided squeezes into explicit,
logarithm-free linear integer cutoffs and formalizes the closed-form odd
seed family `a_0(r) = (92 * 2^(12 * r) - 27) / 65`:

1. **Elementary Power-Collision Inequalities
   (`two_pow_three_mul_le_three_pow_two_mul`, `three_pow_lt_two_pow_two_mul`)**:
   - `2^(3 * B) = 8^B ≤ 9^B = 3^(2 * B)` for all `B : ℕ`.
   - `3^B < 4^B = 2^(2 * B)` for all `B ≥ 1`.
2. **Explicit Linear Step Cutoff on Sub-Critical Runs (`deficiency_linear_step_cutoff`)**:
   Whenever `1 ≤ c`, `s (k + i) = c` for `i < m`, `0 < integerSlack s (k + m)`,
   and `1 ≤ slackDeficiency s c k`, the exponential squeeze
   `3^(c * m) * slackDeficiency s c k < 2^(c * m + c + blockSteps s k + 1)`
   forces the explicit linear step cutoff:
   `c * m < 2 * (c + blockSteps s k + 1)`.
3. **Explicit Logarithm-Free Branching Cap in the Coasting Tree
   (`coasting_linear_block_cutoff`)**:
   In the coasting regime (`a_0 < 2^W`, `W ≤ blockSteps s m`), every surviving
   block length `s m` is bounded by the explicit linear cap:
   `s m < blockSteps s m + W + 2`,
   proving that the coasting tree is strictly finitely branching at every node.
4. **The Closed-Form Family `closedFormSeed r = (92 * 2^(12 * r) - 27) / 65`
   (`two_pow_twelve_mul_mod_65`, `sixty_five_mul_closedFormSeed_add_27`,
   `closedFormSeed_odd`, `closedFormSeed_fixed_point_valuation`)**:
   - Because `2^12 = 4096 ≡ 1 (mod 65)` and `92 ≡ 27 (mod 65)`, `65` divides
     `92 * 2^(12 * r) - 27` for every `r : ℕ`.
   - `closedFormSeed r` is always odd (`closedFormSeed r % 2 = 1`) and satisfies
     `65 * closedFormSeed r + 27 = 23 * 2^(12 * r + 2)`, locking its `c = 4`
     fixed-point 2-adic valuation at `12 * r + 2 = 4 * (3 * r) + 2`.
-/

namespace Mahler.ExplicitCutoffs

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
open Mahler.SharpenedSqueezes
open Mahler.AperiodicCocycle
open Mahler.MinSlackSystem
open Mahler.GlobalStepRate
open Mahler.BaseTwoLock
open Mahler.CeilingSynthesis
open Mahler.TelescopingDuality
open Mahler.ConverseReconstruction

/-! ## 1. Elementary Power-Collision Inequalities -/

/-- For every `B : ℕ`, `2^(3 * B) ≤ 3^(2 * B)` (`8^B ≤ 9^B`). -/
theorem two_pow_three_mul_le_three_pow_two_mul (B : ℕ) :
    2 ^ (3 * B) ≤ 3 ^ (2 * B) := by
  rw [Nat.pow_mul, Nat.pow_mul]
  exact Nat.pow_le_pow_left (by decide : 2 ^ 3 ≤ 3 ^ 2) B

/-- For every `B ≥ 1`, `3^B < 2^(2 * B)` (`3^B < 4^B`). -/
theorem three_pow_lt_two_pow_two_mul {B : ℕ} (hB : 1 ≤ B) :
    3 ^ B < 2 ^ (2 * B) := by
  rw [Nat.pow_mul]
  exact Nat.pow_lt_pow_left (by decide : 3 < 2 ^ 2) (by omega : B ≠ 0)

/-! ## 2. Explicit Linear Step Cutoff on Sub-Critical Runs -/

/-- **Explicit Linear Step Cutoff (`deficiency_linear_step_cutoff`)**:
In the sub-critical deficiency regime (`1 ≤ slackDeficiency s c k`), any run of
`m` consecutive blocks of length `c ≥ 1` with `0 < integerSlack s (k + m)` must
terminate strictly before `2 * (c + blockSteps s k + 1)` steps:
`c * m < 2 * (c + blockSteps s k + 1)`. -/
theorem deficiency_linear_step_cutoff (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) = c)
    (hpos : 0 < integerSlack s (k + m))
    (hdef : 1 ≤ slackDeficiency s c k) :
    c * m < 2 * (c + blockSteps s k + 1) := by
  by_contra hge
  set B := c + blockSteps s k + 1
  have h2B : 2 * B ≤ c * m := by omega
  have hsq := archimedean_deficiency_squeeze s hc hrun hpos
  have h3pos : (0 : ℤ) < (3 : ℤ) ^ (c * m) := pow_pos (by decide) _
  have h1le :
      (3 : ℤ) ^ (c * m) ≤ (3 : ℤ) ^ (c * m) * slackDeficiency s c k := by
    have := mul_le_mul_of_nonneg_left hdef (le_of_lt h3pos)
    linarith
  have hlt_int : (3 : ℤ) ^ (c * m) < (2 : ℤ) ^ (c * m + B) := by
    have hlt' := lt_of_le_of_lt h1le hsq
    simpa [B, Nat.add_assoc] using hlt'
  have hlt_nat : 3 ^ (c * m) < 2 ^ (c * m + B) := by
    exact_mod_cast hlt_int
  have hpow_le : 2 ^ (c * m + B) ≤ 3 ^ (c * m) := by
    have hsplit2 : c * m + B = 3 * B + (c * m - 2 * B) := by omega
    have hsplit3 : c * m = 2 * B + (c * m - 2 * B) := by omega
    rw [hsplit2, Nat.pow_add]
    conv_rhs => rw [hsplit3, Nat.pow_add]
    exact Nat.mul_le_mul
      (two_pow_three_mul_le_three_pow_two_mul B)
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (c * m - 2 * B))
  omega

/-! ## 3. Explicit Logarithm-Free Branching Cap in the Coasting Tree -/

/-- **Explicit Coasting Branching Cap (`coasting_linear_block_cutoff`)**:
In the coasting regime (`a_0 < 2^W` and `W ≤ blockSteps s m`), every surviving
block length `s m` satisfies the explicit linear bound
`s m < blockSteps s m + W + 2`. -/
theorem coasting_linear_block_cutoff {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm : m < K) (hchain : ValidBlockChain a_0 s u K)
    (ha0 : a_0 < 2 ^ W) (hWT : W ≤ blockSteps s m) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + s m)) :
    s m < blockSteps s m + W + 2 := by
  have hbound := coasting_single_block_bound hm hchain ha0 hWT hsurv
  have h3lt4 :
      3 ^ (blockSteps s m + 1) < 2 ^ (2 * (blockSteps s m + 1)) :=
    three_pow_lt_two_pow_two_mul (by omega : 1 ≤ blockSteps s m + 1)
  have h2lt2 :
      2 ^ (blockSteps s m + s m - W) < 2 ^ (2 * (blockSteps s m + 1)) :=
    lt_trans hbound h3lt4
  by_contra hge
  have hexp_ge : 2 * (blockSteps s m + 1) ≤ blockSteps s m + s m - W := by
    omega
  have hpow_ge :
      2 ^ (2 * (blockSteps s m + 1)) ≤ 2 ^ (blockSteps s m + s m - W) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp_ge
  omega

/-! ## 4. The Closed-Form Odd Seed Family `closedFormSeed r = (92 * 2^(12 * r) - 27) / 65` -/

/-- Because `2^12 = 4096 = 63 * 65 + 1`, `2^(12 * r) % 65 = 1` for all `r : ℕ`. -/
theorem two_pow_twelve_mul_mod_65 (r : ℕ) :
    2 ^ (12 * r) % 65 = 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih]

/-- `65` divides `92 * 2^(12 * r) - 27` for every `r : ℕ`. -/
theorem sixty_five_dvd_closed_form_num (r : ℕ) :
    65 ∣ (92 * 2 ^ (12 * r) - 27) := by
  have hmod := two_pow_twelve_mul_mod_65 r
  have hpos : 1 ≤ 2 ^ (12 * r) := Nat.pow_pos (by decide)
  have hge : 27 ≤ 92 * 2 ^ (12 * r) := by omega
  have hrem : (92 * 2 ^ (12 * r) - 27) % 65 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero hrem

/-- Closed-form seed `a_0(r) = (92 * 2^(12 * r) - 27) / 65`. -/
def closedFormSeed (r : ℕ) : ℕ :=
  (92 * 2 ^ (12 * r) - 27) / 65

/-- Exact fixed-point identity for `closedFormSeed r` (`c = 4`, `3^4 - 2^4 = 65`, `3^3 = 27`):
`65 * closedFormSeed r + 27 = 92 * 2^(12 * r)`. -/
theorem sixty_five_mul_closedFormSeed_add_27 (r : ℕ) :
    65 * closedFormSeed r + 27 = 92 * 2 ^ (12 * r) := by
  unfold closedFormSeed
  have hdvd := sixty_five_dvd_closed_form_num r
  have hmul := Nat.mul_div_cancel' hdvd
  have hpos : 1 ≤ 2 ^ (12 * r) := Nat.pow_pos (by decide)
  omega

/-- Every `closedFormSeed r` is an odd positive integer. -/
theorem closedFormSeed_odd (r : ℕ) :
    1 ≤ closedFormSeed r ∧ closedFormSeed r % 2 = 1 := by
  have hid := sixty_five_mul_closedFormSeed_add_27 r
  have hpos : 1 ≤ 2 ^ (12 * r) := Nat.pow_pos (by decide)
  omega

/-- **Exact `c = 4` Fixed-Point Valuation of `closedFormSeed r`
(`closedFormSeed_fixed_point_valuation`)**:
For every `r : ℕ`, `65 * closedFormSeed r + 27 = 23 * 2^(12 * r + 2)`, so its
exact 2-adic valuation is `12 * r + 2 = 4 * (3 * r) + 2` (divisible by
`2^(12 * r + 2)` and not by `2^(12 * r + 3)`). -/
theorem closedFormSeed_fixed_point_valuation (r : ℕ) :
    65 * closedFormSeed r + 27 = 23 * 2 ^ (12 * r + 2) ∧
      2 ^ (12 * r + 2) ∣ (65 * closedFormSeed r + 27) ∧
      ¬ (2 ^ (12 * r + 3) ∣ (65 * closedFormSeed r + 27)) := by
  have hid := sixty_five_mul_closedFormSeed_add_27 r
  have hfact : 92 * 2 ^ (12 * r) = 23 * 2 ^ (12 * r + 2) := by
    rw [Nat.pow_add]
    ring
  rw [hfact] at hid
  refine ⟨hid, ⟨23, by rw [hid]; ring⟩, ?_⟩
  rw [hid]
  rintro ⟨q, hq⟩
  have hsplit :
      2 ^ (12 * r + 3) * q = 2 ^ (12 * r + 2) * (2 * q) := by
    rw [show 12 * r + 3 = (12 * r + 2) + 1 by omega, Nat.pow_add]
    ring
  have hmul :
      2 ^ (12 * r + 2) * 23 = 2 ^ (12 * r + 2) * (2 * q) := by
    calc
      2 ^ (12 * r + 2) * 23 = 23 * 2 ^ (12 * r + 2) := by ring
      _ = 2 ^ (12 * r + 3) * q := hq
      _ = 2 ^ (12 * r + 2) * (2 * q) := hsplit
  have hpos : 0 < 2 ^ (12 * r + 2) := Nat.pow_pos (by decide)
  have h23 : 23 = 2 * q := Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

end Mahler.ExplicitCutoffs
