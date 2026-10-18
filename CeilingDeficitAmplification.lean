import ExplicitHorizonCutoffs

/-!
# Unconditional Coasting Run Cutoffs, `9×` Deficit Amplification & Recovery Thresholds

This module formalizes three quantitative laws governing the coasting tree and
the ceiling deficit `ceilingDeficit s m = 2^(blockSteps s m) - minSlack s m`:

1. **Unconditional Linear Coasting Run-Length Cutoff
   (`unconditional_coasting_repeat_linear_cutoff`)**:
   Applying `3^B < 2^(2 * B)` to `sharpened_coasting_repeat_squeeze` eliminates
   all exponentials unconditionally (without requiring `1 ≤ slackDeficiency`):
   in the coasting regime (`a_0 < 2^W`, `W ≤ T`), any run of `m` blocks of
   length `c ≥ 1` with `2^d ∣ (3 * b m + 1)` (`d ≤ c`) satisfies
   `c * m + d < T + W + 2 * c + 2`.
2. **The Ceiling Deficit `ceilingDeficit` & `9×` Amplification at `s m = 2`
   (`ceilingDeficit_nonneg`, `post_two_quarter_deficit_amplification`,
   `post_two_ceilingDeficit_amplification`)**:
   Define `ceilingDeficit s m = 2^(blockSteps s m) - minSlack s m ≥ 0`.
   Whenever `s m = 2`:
   - `9 * ceilingDeficit s m ≤ 2^(blockSteps s m) - minSlack s (m + 1)`, and
   - `3 * 2^(blockSteps s m) + 9 * ceilingDeficit s m ≤ ceilingDeficit s (m + 1)`.
3. **Full-Ceiling Recovery Threshold (`one_block_full_recovery_requires_seven_le`,
   `persistent_ceilingDeficit_of_two_six_three_three`)**:
   - Restoring `ceilingDeficit s (m + 2) = 0` in a single block after `s m = 2`
     requires `12 * 2^(s (m + 1)) ≤ 3^(s (m + 1))`, forcing **`7 ≤ s (m + 1)`**.
   - Along `(s m, s (m + 1), s (m + 2), s (m + 3)) = (2, 6, 3, 3)`, the ceiling
     deficit remains strictly positive at every step:
     `39 * 2^T(m) ≤ ceilingDeficit s (m + 2)`,
     `285 * 2^T(m) ≤ ceilingDeficit s (m + 3)`, and
     `1551 * 2^T(m) ≤ ceilingDeficit s (m + 4)`.
   - If `s (m + 4) = 2` (`(2, 6, 3, 3, 2)`), the `9×` deficit amplification law
     immediately forces `minSlack s (m + 5) ≤ 2425 * 2^T(m)`.
-/

namespace Mahler.DeficitAmplification

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
open Mahler.ExplicitCutoffs

/-! ## 1. Unconditional Linear Coasting Run-Length Cutoff -/

/-- **Unconditional Linear Coasting Run-Length Cutoff
(`unconditional_coasting_repeat_linear_cutoff`)**:
In the coasting regime (`a_0 < 2^W` and `W ≤ T`), any run of `m` consecutive
odd-to-odd blocks of length `c ≥ 1` starting at `b 0 = orbit a_0 T` with
`2^d ∣ (3 * b m + 1)` (`d ≤ c`) satisfies the explicit linear bound
`c * m + d < T + W + 2 * c + 2`. -/
theorem unconditional_coasting_repeat_linear_cutoff {a_0 W T c d m : ℕ}
    (hc : 1 ≤ c) (hdc : d ≤ c) (ha0 : a_0 < 2 ^ W) (hWT : W ≤ T)
    (b u' : ℕ → ℕ) (hb0 : b 0 = orbit a_0 T)
    (hodd0 : orbit a_0 T % 2 = 1)
    (hstep : ∀ i < m, 3 * b i + 1 = 2 ^ c * u' i ∧ b (i + 1) = orbit (b i) c)
    (hnext : 2 ^ d ∣ (3 * b m + 1))
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (T + 1)) :
    c * m + d < T + W + 2 * c + 2 := by
  have hsq :=
    sharpened_coasting_repeat_squeeze hc hdc ha0 hWT b u' hb0 hodd0 hstep hnext hsurv
  have hTW : (T - W) + W = T := Nat.sub_add_cancel hWT
  have hsub_le : 3 ^ c - 2 ^ c ≤ 3 ^ c := Nat.sub_le _ _
  have hmul3 :
      (3 ^ c - 2 ^ c) * 3 ^ (T + 1) ≤ 3 ^ (T + c + 1) := by
    calc
      (3 ^ c - 2 ^ c) * 3 ^ (T + 1) ≤ 3 ^ c * 3 ^ (T + 1) :=
        Nat.mul_le_mul_right _ hsub_le
      _ = 3 ^ (T + c + 1) := by
        rw [← Nat.pow_add, show c + (T + 1) = T + c + 1 by omega]
  have h3lt4 :
      3 ^ (T + c + 1) < 2 ^ (2 * (T + c + 1)) :=
    three_pow_lt_two_pow_two_mul (by omega : 1 ≤ T + c + 1)
  have hlt1 :
      (3 ^ c - 2 ^ c) * 3 ^ (T + 1) < 2 ^ (2 * (T + c + 1)) :=
    lt_of_le_of_lt hmul3 h3lt4
  have hpow_le :
      2 ^ ((T - W) + c) ≤ 2 ^ (2 * (T + c + 1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hrhs_lt :
      (3 ^ c - 2 ^ c) * 3 ^ (T + 1) + 2 ^ ((T - W) + c) <
        2 ^ (2 * (T + c + 1) + 1) := by
    have htwo :
        2 ^ (2 * (T + c + 1) + 1) =
          2 ^ (2 * (T + c + 1)) + 2 ^ (2 * (T + c + 1)) := by
      rw [Nat.pow_succ]
      ring
    omega
  have hlhs_le :
      2 ^ (c * m + d + (T - W) + 1) ≤ 3 * 2 ^ (c * m + d + (T - W)) := by
    rw [Nat.pow_succ]
    omega
  have hpow_lt :
      2 ^ (c * m + d + (T - W) + 1) < 2 ^ (2 * (T + c + 1) + 1) :=
    lt_of_le_of_lt hlhs_le (lt_trans hsq hrhs_lt)
  by_contra hge
  have hexp_ge :
      2 * (T + c + 1) + 1 ≤ c * m + d + (T - W) + 1 := by omega
  have hpow_ge :
      2 ^ (2 * (T + c + 1) + 1) ≤ 2 ^ (c * m + d + (T - W) + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp_ge
  omega

/-! ## 2. The Ceiling Deficit `ceilingDeficit` & `9×` Deficit Amplification at `s m = 2` -/

/-- The ceiling deficit `G_m = 2^(blockSteps s m) - minSlack s m`. -/
def ceilingDeficit (s : ℕ → ℕ) (m : ℕ) : ℤ :=
  (2 : ℤ) ^ (blockSteps s m) - minSlack s m

/-- `ceilingDeficit s m` is always non-negative (`0 ≤ ceilingDeficit s m`). -/
theorem ceilingDeficit_nonneg (s : ℕ → ℕ) (m : ℕ) :
    0 ≤ ceilingDeficit s m := by
  unfold ceilingDeficit
  have hle := minSlack_le_two_pow s m
  linarith

/-- **The `9×` Quarter-Cap Deficit Amplification Law
(`post_two_quarter_deficit_amplification`)**:
Whenever `s m = 2`, the deficit of `minSlack s (m + 1)` below the quarter-cap
`2^(blockSteps s m)` is at least `9 * ceilingDeficit s m`:
`9 * ceilingDeficit s m ≤ 2^(blockSteps s m) - minSlack s (m + 1)`. -/
theorem post_two_quarter_deficit_amplification (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) :
    9 * ceilingDeficit s m ≤
      (2 : ℤ) ^ (blockSteps s m) - minSlack s (m + 1) := by
  unfold ceilingDeficit
  have hstep := minSlack_succ_le_step s m
  have hpow :
      (2 : ℤ) ^ (blockSteps s (m + 1) + 1) =
        8 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm]
    rw [show blockSteps s m + 2 + 1 = blockSteps s m + 3 by omega, pow_add]
    ring
  rw [hsm, hpow] at hstep
  linarith

/-- **Full Ceiling-Deficit Amplification at `s m = 2`
(`post_two_ceilingDeficit_amplification`)**:
Whenever `s m = 2`,
`3 * 2^(blockSteps s m) + 9 * ceilingDeficit s m ≤ ceilingDeficit s (m + 1)`. -/
theorem post_two_ceilingDeficit_amplification (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) :
    3 * (2 : ℤ) ^ (blockSteps s m) + 9 * ceilingDeficit s m ≤
      ceilingDeficit s (m + 1) := by
  have hamp := post_two_quarter_deficit_amplification s hsm
  unfold ceilingDeficit at hamp ⊢
  have hpow :
      (2 : ℤ) ^ (blockSteps s (m + 1)) = 4 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm, pow_add]
    ring
  rw [hpow]
  linarith

/-! ## 3. Full-Ceiling Recovery Threshold & Persistent Deficits Across `(2, 6, 3, 3)` -/

/-- **One-Block Full-Recovery Threshold (`one_block_full_recovery_requires_seven_le`)**:
If `s m = 2` and `ceilingDeficit s (m + 2) = 0` (so `minSlack` reaches the full
ceiling `2^(blockSteps s (m + 2))` in a single block after `s m = 2`), then
**`7 ≤ s (m + 1)`**. -/
theorem one_block_full_recovery_requires_seven_le (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hfull : ceilingDeficit s (m + 2) = 0) :
    7 ≤ s (m + 1) := by
  unfold ceilingDeficit at hfull
  have hmax : minSlack s (m + 2) = (2 : ℤ) ^ (blockSteps s (m + 2)) := by
    linarith
  have hq := post_two_minSlack_le_quarter s hsm
  have hstep := minSlack_succ_le_step s (m + 1)
  rw [hmax] at hstep
  have hpow1 :
      (2 : ℤ) ^ (blockSteps s (m + 2)) =
        (2 : ℤ) ^ (s (m + 1)) * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    simp only [blockSteps, pow_add]
    ring
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s (m + 2) + 1) =
        2 * ((2 : ℤ) ^ (s (m + 1)) * (2 : ℤ) ^ (blockSteps s (m + 1))) := by
    rw [pow_succ, hpow1]
    ring
  have h3pos : (0 : ℤ) ≤ (3 : ℤ) ^ (s (m + 1)) := pow_nonneg (by decide) _
  have hmul := mul_le_mul_of_nonneg_left hq h3pos
  have hineq :
      12 * (2 : ℤ) ^ (s (m + 1)) * (2 : ℤ) ^ (blockSteps s (m + 1)) ≤
        (3 : ℤ) ^ (s (m + 1)) * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    rw [hpow1, hpow2] at hstep
    linarith
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1)) :=
    pow_pos (by decide) _
  have h12 : 12 * (2 : ℤ) ^ (s (m + 1)) ≤ (3 : ℤ) ^ (s (m + 1)) :=
    le_of_mul_le_mul_right hineq h2pos
  by_contra hlt7
  have hcases :
      s (m + 1) = 0 ∨ s (m + 1) = 1 ∨ s (m + 1) = 2 ∨ s (m + 1) = 3 ∨
      s (m + 1) = 4 ∨ s (m + 1) = 5 ∨ s (m + 1) = 6 := by omega
  rcases hcases with h | h | h | h | h | h | h <;>
    { rw [h] at h12; norm_num at h12 }

/-- **Persistent Ceiling Deficit Across `(2, 6, 3, 3)` and Collapse at `(2, 6, 3, 3, 2)`
(`persistent_ceilingDeficit_of_two_six_three_three`)**:
Whenever `(s m, s (m + 1), s (m + 2), s (m + 3)) = (2, 6, 3, 3)`:
- `39 * 2^(blockSteps s m) ≤ ceilingDeficit s (m + 2)`,
- `285 * 2^(blockSteps s m) ≤ ceilingDeficit s (m + 3)`,
- `1551 * 2^(blockSteps s m) ≤ ceilingDeficit s (m + 4)`, and
- if `s (m + 4) = 2`, then `minSlack s (m + 5) ≤ 2425 * 2^(blockSteps s m)`. -/
theorem persistent_ceilingDeficit_of_two_six_three_three (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hsm1 : s (m + 1) = 6)
    (hsm2 : s (m + 2) = 3) (hsm3 : s (m + 3) = 3) :
    39 * (2 : ℤ) ^ (blockSteps s m) ≤ ceilingDeficit s (m + 2) ∧
      285 * (2 : ℤ) ^ (blockSteps s m) ≤ ceilingDeficit s (m + 3) ∧
      1551 * (2 : ℤ) ^ (blockSteps s m) ≤ ceilingDeficit s (m + 4) ∧
      (s (m + 4) = 2 →
        minSlack s (m + 5) ≤ 2425 * (2 : ℤ) ^ (blockSteps s m)) := by
  have hm1_pow :
      (2 : ℤ) ^ (blockSteps s (m + 1)) = 4 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm, pow_add]
    ring
  have hm2_pow :
      (2 : ℤ) ^ (blockSteps s (m + 2)) = 256 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm, hsm1]
    rw [show blockSteps s m + 2 + 6 = blockSteps s m + 8 by omega, pow_add]
    ring
  have hm3_pow :
      (2 : ℤ) ^ (blockSteps s (m + 3)) = 2048 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm, hsm1, hsm2]
    rw [show blockSteps s m + 2 + 6 + 3 = blockSteps s m + 11 by omega, pow_add]
    ring
  have hm4_pow :
      (2 : ℤ) ^ (blockSteps s (m + 4)) = 16384 * (2 : ℤ) ^ (blockSteps s m) := by
    simp only [blockSteps, hsm, hsm1, hsm2, hsm3]
    rw [show blockSteps s m + 2 + 6 + 3 + 3 = blockSteps s m + 14 by omega, pow_add]
    ring
  have h217 := four_mul_minSlack_after_two_six_le s hsm hsm1
  have h1763 := four_mul_minSlack_after_two_six_three_le s hsm hsm1 hsm2
  rw [hm1_pow] at h217 h1763
  have hstep3 := minSlack_succ_le_step s (m + 3)
  have hm4_next :
      (2 : ℤ) ^ (blockSteps s (m + 4) + 1) =
        32768 * (2 : ℤ) ^ (blockSteps s m) := by
    rw [pow_succ, hm4_pow]
    ring
  rw [hsm3, hm4_next] at hstep3
  have h33 : (3 : ℤ) ^ 3 = 27 := by norm_num
  rw [h33] at hstep3
  have hd2 : 39 * (2 : ℤ) ^ (blockSteps s m) ≤ ceilingDeficit s (m + 2) := by
    unfold ceilingDeficit
    rw [hm2_pow]
    linarith
  have hd3 : 285 * (2 : ℤ) ^ (blockSteps s m) ≤ ceilingDeficit s (m + 3) := by
    unfold ceilingDeficit
    rw [hm3_pow]
    linarith
  have hd4 : 1551 * (2 : ℤ) ^ (blockSteps s m) ≤ ceilingDeficit s (m + 4) := by
    unfold ceilingDeficit
    rw [hm4_pow]
    linarith
  refine ⟨hd2, hd3, hd4, ?_⟩
  intro hsm4
  have hamp := post_two_quarter_deficit_amplification s hsm4
  rw [hm4_pow] at hamp
  linarith

end Mahler.DeficitAmplification
