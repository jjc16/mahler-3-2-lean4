import CeilingSaturatedModTraps

/-!
# The 2-adic Lifting-the-Exponent (LTE) Theorem & Dyadic Step-Sum Valuation Locks

This module formalizes **Attack Vector 2**—the exact 2-adic Lifting-the-Exponent
(LTE) theorem for `3^(2^(r+1)) - 1` and its coupling to the multi-step coprime
quotient identity:

1. **The LTE Odd Quotient Sequence `lteQuotient` & Exact Identity
   (`lteQuotient_odd`, `three_pow_two_pow_eq_one_add`,
   `three_pow_two_pow_mod`, `three_pow_two_pow_sub_one_valuation`)**:
   Define `lteQuotient 0 = 1` and
   `lteQuotient (r + 1) = lteQuotient r + 2^(r + 2) * (lteQuotient r)^2`.
   For every `r : ℕ`:
   - `lteQuotient r % 2 = 1` (always odd),
   - `3^(2^(r + 1)) = 1 + 2^(r + 3) * lteQuotient r`,
   - `3^(2^(r + 1)) % 2^(r + 4) = 1 + 2^(r + 3)`, and
   - `2^(r + 3) ∣ (3^(2^(r + 1)) - 1)` while `¬ (2^(r + 4) ∣ (3^(2^(r + 1)) - 1))`.
2. **Dyadic Step-Sum Valuation Lock on `2^(tailSteps) * u m - (u 0 + R(s, m))`
   (`coprime_step_sum_diff_eq`, `dyadic_step_sum_valuation_lock`,
   `dyadic_step_sum_u0_add_remainder_valuation`)**:
   - Along any `ValidBlockChain a_0 s u K` (`m < K`),
     `2^(tailSteps s m) * u m = (3^(blockSteps s m) - 1) * u 0 + (u 0 + coprimeRemainder s m)`.
   - Whenever the cumulative step sum hits a power of two `blockSteps s m = 2^(r + 1)`,
     the difference `2^(tailSteps s m) * u m - (u 0 + coprimeRemainder s m)` equals
     `2^(r + 3) * (lteQuotient r * u 0)` with `lteQuotient r * u 0` odd, locking its
     2-adic valuation at `r + 3`.
   - Consequently, when `r + 4 ≤ tailSteps s m`, `2^(r + 3)` divides
     `u 0 + coprimeRemainder s m` and `2^(r + 4)` does **not**.
-/

namespace Mahler.TwoAdicLTE

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
open Mahler.DeficitAmplification
open Mahler.TwoVisitSeparation
open Mahler.MonotonicSeparation
open Mahler.CeilingModTraps

/-! ## 1. The 2-adic Lifting-the-Exponent (LTE) Sequence & Exact Valuation -/

/-- The odd quotient `q_r` in `3^(2^(r + 1)) = 1 + 2^(r + 3) * q_r`. -/
def lteQuotient : ℕ → ℕ
  | 0 => 1
  | r + 1 => lteQuotient r + 2 ^ (r + 2) * (lteQuotient r) ^ 2

/-- For every `r : ℕ`, `lteQuotient r` is odd (`lteQuotient r % 2 = 1`). -/
theorem lteQuotient_odd (r : ℕ) : lteQuotient r % 2 = 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [lteQuotient]
      have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
        rw [Nat.pow_succ]
        ring
      rw [hpow]
      have heven : (2 * 2 ^ (r + 1) * lteQuotient r ^ 2) % 2 = 0 := by
        have : 2 * 2 ^ (r + 1) * lteQuotient r ^ 2 =
            2 * (2 ^ (r + 1) * lteQuotient r ^ 2) := by ring
        rw [this]
        omega
      omega

/-- **Exact 2-adic LTE Identity (`three_pow_two_pow_eq_one_add`)**:
For every `r : ℕ`, `3^(2^(r + 1)) = 1 + 2^(r + 3) * lteQuotient r`. -/
theorem three_pow_two_pow_eq_one_add (r : ℕ) :
    3 ^ (2 ^ (r + 1)) = 1 + 2 ^ (r + 3) * lteQuotient r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hexp : 2 ^ (r + 2) = 2 ^ (r + 1) * 2 := by
        rw [Nat.pow_succ]
      rw [hexp, Nat.pow_mul, ih]
      simp only [lteQuotient]
      have hpow1 : 2 ^ (r + 1 + 3) = 2 * 2 ^ (r + 3) := by
        rw [show r + 1 + 3 = (r + 3) + 1 by omega, Nat.pow_succ]
        ring
      have hpow2 :
          2 ^ (r + 1 + 3) * (2 ^ (r + 2) * lteQuotient r ^ 2) =
            (2 ^ (r + 3) * lteQuotient r) ^ 2 := by
        have hsum : (r + 1 + 3) + (r + 2) = (r + 3) + (r + 3) := by omega
        calc
          2 ^ (r + 1 + 3) * (2 ^ (r + 2) * lteQuotient r ^ 2) =
              (2 ^ (r + 1 + 3) * 2 ^ (r + 2)) * lteQuotient r ^ 2 := by ring
          _ = 2 ^ ((r + 1 + 3) + (r + 2)) * lteQuotient r ^ 2 := by
                rw [← Nat.pow_add]
          _ = 2 ^ ((r + 3) + (r + 3)) * lteQuotient r ^ 2 := by rw [hsum]
          _ = (2 ^ (r + 3) * 2 ^ (r + 3)) * lteQuotient r ^ 2 := by
                rw [Nat.pow_add]
          _ = (2 ^ (r + 3) * lteQuotient r) ^ 2 := by ring
      calc
        (1 + 2 ^ (r + 3) * lteQuotient r) ^ 2 =
            1 + (2 * 2 ^ (r + 3)) * lteQuotient r +
              (2 ^ (r + 3) * lteQuotient r) ^ 2 := by ring
        _ = 1 + 2 ^ (r + 1 + 3) * lteQuotient r +
              2 ^ (r + 1 + 3) * (2 ^ (r + 2) * lteQuotient r ^ 2) := by
              rw [← hpow1, ← hpow2]
        _ = 1 + 2 ^ (r + 1 + 3) *
              (lteQuotient r + 2 ^ (r + 2) * lteQuotient r ^ 2) := by ring

/-- **Exact Modulo-`2^(r+4)` Residue of `3^(2^(r+1))` (`three_pow_two_pow_mod`)**:
For every `r : ℕ`, `3^(2^(r + 1)) % 2^(r + 4) = 1 + 2^(r + 3)`. -/
theorem three_pow_two_pow_mod (r : ℕ) :
    3 ^ (2 ^ (r + 1)) % 2 ^ (r + 4) = 1 + 2 ^ (r + 3) := by
  rw [three_pow_two_pow_eq_one_add]
  have hodd := lteQuotient_odd r
  have hdiv : lteQuotient r = 2 * (lteQuotient r / 2) + 1 := by omega
  have hpow : 2 ^ (r + 4) = 2 * 2 ^ (r + 3) := by
    rw [show r + 4 = (r + 3) + 1 by omega, Nat.pow_succ]
    ring
  have hexpand :
      1 + 2 ^ (r + 3) * lteQuotient r =
        (1 + 2 ^ (r + 3)) + 2 ^ (r + 4) * (lteQuotient r / 2) := by
    conv_lhs => rw [hdiv]
    rw [hpow]
    ring
  rw [hexpand, Nat.add_mul_mod_self_left]
  have hlt : 1 + 2 ^ (r + 3) < 2 ^ (r + 4) := by
    have hpos : 1 < 2 ^ (r + 3) := by
      have : 2 ^ 1 ≤ 2 ^ (r + 3) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r + 3)
      omega
    omega
  exact Nat.mod_eq_of_lt hlt

/-- **The 2-adic Lifting-the-Exponent Valuation Theorem
(`three_pow_two_pow_sub_one_valuation`)**:
For every `r : ℕ`, `2^(r + 3)` divides `3^(2^(r + 1)) - 1` and `2^(r + 4)` does not. -/
theorem three_pow_two_pow_sub_one_valuation (r : ℕ) :
    3 ^ (2 ^ (r + 1)) - 1 = 2 ^ (r + 3) * lteQuotient r ∧
      2 ^ (r + 3) ∣ (3 ^ (2 ^ (r + 1)) - 1) ∧
      ¬ (2 ^ (r + 4) ∣ (3 ^ (2 ^ (r + 1)) - 1)) := by
  have hid := three_pow_two_pow_eq_one_add r
  have hsub : 3 ^ (2 ^ (r + 1)) - 1 = 2 ^ (r + 3) * lteQuotient r := by omega
  have hodd := lteQuotient_odd r
  refine ⟨hsub, ⟨lteQuotient r, hsub⟩, ?_⟩
  rw [hsub]
  rintro ⟨k, hk⟩
  have hsplit : 2 ^ (r + 4) * k = 2 ^ (r + 3) * (2 * k) := by
    rw [show r + 4 = (r + 3) + 1 by omega, Nat.pow_add]
    ring
  rw [hsplit] at hk
  have hpos : 0 < 2 ^ (r + 3) := Nat.pow_pos (by decide)
  have hq : lteQuotient r = 2 * k := Nat.eq_of_mul_eq_mul_left hpos hk
  omega

/-! ## 2. Dyadic Step-Sum Valuation Lock on the Multi-Step Coprime Recurrence -/

/-- **Subtraction-Free Step-Sum Difference Identity (`coprime_step_sum_diff_eq`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`),
`2^(tailSteps s m) * u m = (3^(blockSteps s m) - 1) * u 0 + (u 0 + coprimeRemainder s m)`. -/
theorem coprime_step_sum_diff_eq {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (tailSteps s m) * u m =
      (3 ^ (blockSteps s m) - 1) * u 0 + (u 0 + coprimeRemainder s m) := by
  have hid := coprime_quotient_m_step_identity hmK hchain
  have hpos : 1 ≤ 3 ^ (blockSteps s m) := Nat.pow_pos (by decide)
  have hmul :
      3 ^ (blockSteps s m) * u 0 =
        (3 ^ (blockSteps s m) - 1) * u 0 + u 0 := by
    calc
      3 ^ (blockSteps s m) * u 0 =
          ((3 ^ (blockSteps s m) - 1) + 1) * u 0 := by
            rw [Nat.sub_add_cancel hpos]
      _ = (3 ^ (blockSteps s m) - 1) * u 0 + u 0 := by ring
  rw [hmul] at hid
  omega

/-- **Dyadic Step-Sum Valuation Lock (`dyadic_step_sum_valuation_lock`)**:
Whenever `blockSteps s m = 2^(r + 1)` along `ValidBlockChain a_0 s u K` (`m < K`),
the difference `2^(tailSteps s m) * u m - (u 0 + coprimeRemainder s m)` has
exact 2-adic valuation `r + 3` (divisible by `2^(r + 3)` and not by `2^(r + 4)`). -/
theorem dyadic_step_sum_valuation_lock {a_0 : ℕ} {s u : ℕ → ℕ} {K m r : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hsteps : blockSteps s m = 2 ^ (r + 1)) :
    2 ^ (tailSteps s m) * u m - (u 0 + coprimeRemainder s m) =
        2 ^ (r + 3) * (lteQuotient r * u 0) ∧
      2 ^ (r + 3) ∣
        (2 ^ (tailSteps s m) * u m - (u 0 + coprimeRemainder s m)) ∧
      ¬ (2 ^ (r + 4) ∣
        (2 ^ (tailSteps s m) * u m - (u 0 + coprimeRemainder s m))) := by
  have hdiff := coprime_step_sum_diff_eq hmK hchain
  have hlte := (three_pow_two_pow_sub_one_valuation r).1
  rw [hsteps, hlte] at hdiff
  have hsub :
      2 ^ (tailSteps s m) * u m - (u 0 + coprimeRemainder s m) =
        2 ^ (r + 3) * (lteQuotient r * u 0) := by
    have : 2 ^ (r + 3) * lteQuotient r * u 0 =
        2 ^ (r + 3) * (lteQuotient r * u 0) := by ring
    omega
  rcases hchain 0 (by omega : 0 < K) with ⟨_, hu0_odd, _⟩
  have hq_odd := lteQuotient_odd r
  have hprod_odd : (lteQuotient r * u 0) % 2 = 1 := by
    rw [Nat.mul_mod, hq_odd, hu0_odd]
  refine ⟨hsub, ⟨lteQuotient r * u 0, hsub⟩, ?_⟩
  rw [hsub]
  rintro ⟨k, hk⟩
  have hsplit : 2 ^ (r + 4) * k = 2 ^ (r + 3) * (2 * k) := by
    rw [show r + 4 = (r + 3) + 1 by omega, Nat.pow_add]
    ring
  rw [hsplit] at hk
  have hpos : 0 < 2 ^ (r + 3) := Nat.pow_pos (by decide)
  have heq : lteQuotient r * u 0 = 2 * k := Nat.eq_of_mul_eq_mul_left hpos hk
  omega

/-- **Dyadic Step-Sum Valuation of `u 0 + coprimeRemainder s m`
(`dyadic_step_sum_u0_add_remainder_valuation`)**:
Whenever `blockSteps s m = 2^(r + 1)` and `r + 4 ≤ tailSteps s m` along
`ValidBlockChain a_0 s u K` (`m < K`), `2^(r + 3)` divides
`u 0 + coprimeRemainder s m` and `2^(r + 4)` does **not**. -/
theorem dyadic_step_sum_u0_add_remainder_valuation
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m r : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hsteps : blockSteps s m = 2 ^ (r + 1))
    (htail : r + 4 ≤ tailSteps s m) :
    2 ^ (r + 3) ∣ (u 0 + coprimeRemainder s m) ∧
      ¬ (2 ^ (r + 4) ∣ (u 0 + coprimeRemainder s m)) := by
  have hdiff := coprime_step_sum_diff_eq hmK hchain
  have hlte := (three_pow_two_pow_sub_one_valuation r).1
  rw [hsteps, hlte] at hdiff
  have hdvd3_lhs : 2 ^ (r + 3) ∣ 2 ^ (tailSteps s m) * u m :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega : r + 3 ≤ tailSteps s m)) (u m)
  have hdvd3_term :
      2 ^ (r + 3) ∣ 2 ^ (r + 3) * lteQuotient r * u 0 :=
    ⟨lteQuotient r * u 0, by ring⟩
  have hdvd3 : 2 ^ (r + 3) ∣ (u 0 + coprimeRemainder s m) := by
    rw [hdiff] at hdvd3_lhs
    exact (Nat.dvd_add_right hdvd3_term).mp hdvd3_lhs
  refine ⟨hdvd3, ?_⟩
  intro hdvd4
  have hdvd4_lhs : 2 ^ (r + 4) ∣ 2 ^ (tailSteps s m) * u m :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 htail) (u m)
  rw [hdiff] at hdvd4_lhs
  have hdvd4_term :
      2 ^ (r + 4) ∣ 2 ^ (r + 3) * lteQuotient r * u 0 :=
    (Nat.dvd_add_left hdvd4).mp hdvd4_lhs
  have hlock := (dyadic_step_sum_valuation_lock hmK hchain hsteps)
  rw [hlock.1] at hlock
  have hmul :
      2 ^ (r + 3) * lteQuotient r * u 0 =
        2 ^ (r + 3) * (lteQuotient r * u 0) := by ring
  rw [hmul] at hdvd4_term
  exact hlock.2.2 hdvd4_term

end Mahler.TwoAdicLTE
