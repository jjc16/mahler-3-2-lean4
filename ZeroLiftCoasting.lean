import KernelFactorizationDuality

/-!
# The Zero-Lift Coasting Regime (`T(m) ≥ W`, `a_0 < 2^W`)

A finite positive integer `a_0 < 2^W` has at most `W` binary bits. Once the
step count reaches `W`, all remaining binary bits of `a_0` are `0`. This module
formalizes the laws governing the **Zero-Lift Coasting Regime** (`W ≤ blockSteps s m`):

1. **The Coasting Entry Ceiling (`orbit_at_bit_length_lt_three_pow`)**:
   Whenever `a_0 < 2^W` survives to step `W` (`ValidCompanionUpTo a_0 ξ W`),
   the half-corridor bound `2^(W + 1) * orbit a_0 W < 3^W * (2 * a_0 + 1)`
   combined with `2 * a_0 + 1 ≤ 2^(W + 1)` cancels `2^(W + 1)` from both sides:
   `orbit a_0 W < 3^W`.
2. **Permanent Zero-Lift Freeze (`coasting_residue_eq_self`,
   `coasting_jumpQuotient_eq_zero`)**:
   For every return `m` in the coasting regime (`a_0 < 2^W` and `W ≤ blockSteps s m`),
   `a_0 % 2^(blockSteps s m) = a_0` and `jumpQuotient a_0 s m = 0`. Thus neither
   Escape Branch 1 nor Escape Branch 2 can ever be used after step `W`.
3. **The Coasting Coprime Quotient Cap (`coasting_coprime_quotient_bound`)**:
   Along `ValidBlockChain a_0 s u K` (`m < K`) with `a_0 < 2^W` and
   `W ≤ blockSteps s (m + 1)`, surviving to the end of block `m` forces
   `2^(blockSteps s (m + 1) - W) * u m < 3^(blockSteps s m + 1)`.
4. **Closure of Both Escape Branches When `b_m ≡ 3 (mod 4)`
   (`coasting_mod_four_eq_three_impossible`)**:
   In the coasting regime (`a_0 < 2^W` and `W ≤ blockSteps s m`), if the odd
   return integer `orbit a_0 (blockSteps s m)` satisfies `% 4 = 3`, then `s m = 1`
   is forced with no high-bit escape possible, killing the trajectory within 2 steps:
   `¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s m + 2)`.
-/

namespace Mahler.Coasting

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

/-! ## 1. The Coasting Entry Ceiling (`orbit a_0 W < 3^W`) -/

/-- **The Coasting Entry Ceiling (`orbit_at_bit_length_lt_three_pow`)**:
If `a_0 < 2^W` survives `W` steps (`ValidCompanionUpTo a_0 ξ W`), then at the
moment coasting begins (step `W`), `orbit a_0 W < 3^W`. -/
theorem orbit_at_bit_length_lt_three_pow {a_0 W : ℕ}
    (ha0 : a_0 < 2 ^ W) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ W) :
    orbit a_0 W < 3 ^ W := by
  have hcor := (surviving_orbit_half_corridor hsurv).2
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hmul :
      2 ^ (W + 1) * orbit a_0 W < 2 ^ (W + 1) * 3 ^ W := by
    calc
      2 ^ (W + 1) * orbit a_0 W < 3 ^ W * (2 * a_0 + 1) := hcor
      _ ≤ 3 ^ W * 2 ^ (W + 1) := Nat.mul_le_mul_left (3 ^ W) h2a0
      _ = 2 ^ (W + 1) * 3 ^ W := by ring
  exact Nat.lt_of_mul_lt_mul_left hmul

/-! ## 2. Permanent Zero-Lift Freeze (`jumpQuotient = 0`) in the Coasting Regime -/

/-- In the coasting regime (`a_0 < 2^W` and `W ≤ blockSteps s m`), the minimal
residue `a_0 % 2^(blockSteps s m)` freezes permanently at `a_0`. -/
theorem coasting_residue_eq_self {a_0 W : ℕ} {s : ℕ → ℕ} {m : ℕ}
    (ha0 : a_0 < 2 ^ W) (hW : W ≤ blockSteps s m) :
    a_0 % 2 ^ (blockSteps s m) = a_0 := by
  have hpow : 2 ^ W ≤ 2 ^ (blockSteps s m) :=
    Nat.pow_le_pow_right (by decide) hW
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha0 hpow)

/-- **Permanent Zero-Lift Freeze (`coasting_jumpQuotient_eq_zero`)**:
Once `W ≤ blockSteps s m` (`a_0 < 2^W`), the high-bit jump quotient
`jumpQuotient a_0 s m` is identically `0`. -/
theorem coasting_jumpQuotient_eq_zero {a_0 W : ℕ} {s : ℕ → ℕ} {m : ℕ}
    (ha0 : a_0 < 2 ^ W) (hW : W ≤ blockSteps s m) :
    jumpQuotient a_0 s m = 0 := by
  unfold jumpQuotient
  have hW1 : W ≤ blockSteps s (m + 1) := by
    simp only [blockSteps]
    omega
  rw [coasting_residue_eq_self ha0 hW1]
  have hpow : 2 ^ W ≤ 2 ^ (blockSteps s m) :=
    Nat.pow_le_pow_right (by decide) hW
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha0 hpow)

/-! ## 3. The Coasting Coprime Quotient Cap -/

/-- **The Coasting Coprime Quotient Cap (`coasting_coprime_quotient_bound`)**:
Along `ValidBlockChain a_0 s u K` (`m < K`) with `a_0 < 2^W` and
`W ≤ blockSteps s (m + 1)`, surviving through the end of block `m` forces
`2^(blockSteps s (m + 1) - W) * u m < 3^(blockSteps s m + 1)`. -/
theorem coasting_coprime_quotient_bound {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (ha0 : a_0 < 2 ^ W) (hW : W ≤ blockSteps s (m + 1)) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + s m)) :
    2 ^ (blockSteps s (m + 1) - W) * u m <
      3 ^ (blockSteps s m + 1) := by
  have hcap := (block_length_archimedean_cap hmK hchain hsurv).1
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsplit :
      blockSteps s m + s m + 1 =
        (W + 1) + (blockSteps s (m + 1) - W) := by
    change blockSteps s (m + 1) + 1 = (W + 1) + (blockSteps s (m + 1) - W)
    omega
  have hmul :
      2 ^ (W + 1) * (2 ^ (blockSteps s (m + 1) - W) * u m) <
        2 ^ (W + 1) * 3 ^ (blockSteps s m + 1) := by
    calc
      2 ^ (W + 1) * (2 ^ (blockSteps s (m + 1) - W) * u m) =
          2 ^ (blockSteps s m + s m + 1) * u m := by
            rw [hsplit, Nat.pow_add]
            ring
      _ < 3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := hcap
      _ ≤ 3 ^ (blockSteps s m + 1) * 2 ^ (W + 1) :=
            Nat.mul_le_mul_left _ h2a0
      _ = 2 ^ (W + 1) * 3 ^ (blockSteps s m + 1) := by ring
  exact Nat.lt_of_mul_lt_mul_left hmul

/-! ## 4. Closure of Both Escape Branches When `orbit a_0 (blockSteps s m) % 4 = 3` -/

/-- **Closure of Both Escape Branches in the Coasting Regime**:
If `ValidBlockChain a_0 s u K` (`m < K`) reaches a return `blockSteps s m`
where `orbit a_0 (blockSteps s m) % 4 = 3`, then `s m = 1` is forced directly
on `a_0` with no high-bit escape available, so `a_0` cannot survive to step
`blockSteps s m + 2`. -/
theorem coasting_mod_four_eq_three_impossible {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hmod4 : orbit a_0 (blockSteps s m) % 4 = 3) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s m + 2) := by
  rintro ⟨ξ, hξ⟩
  rcases hchain m hmK with ⟨hsm, hum, hdecomp⟩
  have hsm_eq1 : s m = 1 := by
    by_contra hne1
    have hsm_ge2 : 2 ≤ s m := by omega
    have hdvd4 : 4 ∣ 2 ^ (s m) * u m := by
      have hsplit : s m = 2 + (s m - 2) := by omega
      rw [hsplit, Nat.pow_add]
      exact ⟨2 ^ (s m - 2) * u m, by ring⟩
    have h0 : (3 * orbit a_0 (blockSteps s m) + 1) % 4 = 0 := by
      rw [hdecomp]
      exact Nat.mod_eq_zero_of_dvd hdvd4
    omega
  rw [hsm_eq1] at hdecomp
  have hshift :
      ValidCompanionUpTo (orbit a_0 (blockSteps s m))
        (ξ * (3 / 2 : ℝ) ^ (blockSteps s m)) 2 :=
    validCompanionUpTo_shift (blockSteps s m) 2 hξ
  exact s_eq_one_impossible hum hdecomp ⟨_, hshift⟩

end Mahler.Coasting
