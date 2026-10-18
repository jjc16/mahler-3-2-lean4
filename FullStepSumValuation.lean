import TwoAdicLiftingExponent

/-!
# Full Step-Sum LTE Valuation (`S = 2^(r+1) * d` and Odd `S`) & Cross-Horizon `u 0`-Elimination

This module generalizes the 2-adic Lifting-the-Exponent (LTE) valuation lock
from pure powers of two `2^(r + 1)` to **every positive step sum** (`S` odd and
`S = 2^(r + 1) * d` with `d` odd), and derives the `u 0`-free cross-horizon
compatibility law on `coprimeRemainder s m2 - coprimeRemainder s m1`:

1. **The Geometric Sum `oddGeomSum` & Full LTE for `3^(2^(r+1) * d) - 1`
   (`one_add_mul_oddGeomSum`, `oddGeomSum_mod_two`,
   `three_pow_two_pow_mul_eq_one_add`, `three_pow_even_step_valuation`)**:
   - For every `k` and `d`, `(1 + k)^d = 1 + k * oddGeomSum (1 + k) d`.
   - Whenever `X % 2 = 1`, `oddGeomSum X d % 2 = d % 2`.
   - Consequently, for every `r` and odd `d` (`d % 2 = 1`),
     `3^(2^(r + 1) * d) - 1` has exact 2-adic valuation `r + 3`:
     `2^(r + 3) ∣ (3^(2^(r + 1) * d) - 1)` and `¬ (2^(r + 4) ∣ (3^(2^(r + 1) * d) - 1))`.
2. **Full Step-Sum Valuation Lock on `u 0 + coprimeRemainder s m`
   (`odd_step_sum_u0_add_remainder_mod_four`,
   `even_step_sum_u0_add_remainder_valuation`)**:
   - When `blockSteps s m % 2 = 1` and `2 ≤ tailSteps s m`,
     `(u 0 + coprimeRemainder s m) % 4 = 2`.
   - When `blockSteps s m = 2^(r + 1) * d` (`d % 2 = 1`) and `r + 4 ≤ tailSteps s m`,
     `2^(r + 3) ∣ (u 0 + coprimeRemainder s m)` and
     `¬ (2^(r + 4) ∣ (u 0 + coprimeRemainder s m))`.
3. **Cross-Horizon `u 0`-Elimination Compatibility Law
   (`cross_horizon_even_step_sum_valuation_lock`)**:
   If at two horizons `m1, m2 < K` (`coprimeRemainder s m1 ≤ coprimeRemainder s m2`)
   we have `blockSteps s m1 = 2^(r1 + 1) * d1` and `blockSteps s m2 = 2^(r2 + 1) * d2`
   (`d1, d2` odd, `r1 < r2`), eliminating `u 0` locks the exact 2-adic valuation of
   `coprimeRemainder s m2 - coprimeRemainder s m1` at `r1 + 3`:
   `2^(r1 + 3) ∣ (coprimeRemainder s m2 - coprimeRemainder s m1)` and
   `¬ (2^(r1 + 4) ∣ (coprimeRemainder s m2 - coprimeRemainder s m1))`.
-/

namespace Mahler.FullStepValuation

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
open Mahler.TwoAdicLTE

/-! ## 1. The Geometric Sum `oddGeomSum` & Full LTE for `3^(2^(r+1) * d) - 1` -/

/-- The geometric sum `1 + X + X^2 + ... + X^(d - 1)`. -/
def oddGeomSum (X : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => oddGeomSum X d + X ^ d

/-- Subtraction-free geometric sum identity:
`(1 + k)^d = 1 + k * oddGeomSum (1 + k) d`. -/
theorem one_add_mul_oddGeomSum (k d : ℕ) :
    (1 + k) ^ d = 1 + k * oddGeomSum (1 + k) d := by
  induction d with
  | zero => simp [oddGeomSum]
  | succ d ih =>
      simp only [oddGeomSum]
      calc
        (1 + k) ^ (d + 1) = (1 + k) ^ d + k * (1 + k) ^ d := by
          rw [Nat.pow_succ]
          ring
        _ = (1 + k * oddGeomSum (1 + k) d) + k * (1 + k) ^ d := by
          rw [ih]
        _ = 1 + k * (oddGeomSum (1 + k) d + (1 + k) ^ d) := by ring

private theorem odd_pow_mod_two {X : ℕ} (hX : X % 2 = 1) (n : ℕ) :
    X ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hX]

/-- Whenever `X % 2 = 1`, `oddGeomSum X d % 2 = d % 2`. -/
theorem oddGeomSum_mod_two {X : ℕ} (hX : X % 2 = 1) (d : ℕ) :
    oddGeomSum X d % 2 = d % 2 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [oddGeomSum]
      have hpow := odd_pow_mod_two hX d
      rw [Nat.add_mod, ih, hpow]
      omega

/-- **Exact Factorization of `3^(2^(r+1) * d)` (`three_pow_two_pow_mul_eq_one_add`)**:
For every `r, d : ℕ`,
`3^(2^(r + 1) * d) = 1 + 2^(r + 3) * (lteQuotient r * oddGeomSum (3^(2^(r + 1))) d)`. -/
theorem three_pow_two_pow_mul_eq_one_add (r d : ℕ) :
    3 ^ (2 ^ (r + 1) * d) =
      1 + 2 ^ (r + 3) *
        (lteQuotient r * oddGeomSum (3 ^ (2 ^ (r + 1))) d) := by
  rw [Nat.pow_mul, three_pow_two_pow_eq_one_add r]
  rw [one_add_mul_oddGeomSum (2 ^ (r + 3) * lteQuotient r) d]
  rw [← three_pow_two_pow_eq_one_add r]
  ring

/-- **Full LTE Valuation for Even Exponents `2^(r+1) * d` (`three_pow_even_step_valuation`)**:
For every `r : ℕ` and odd `d` (`d % 2 = 1`), `3^(2^(r + 1) * d) - 1` has exact
2-adic valuation `r + 3` (divisible by `2^(r + 3)` and not by `2^(r + 4)`). -/
theorem three_pow_even_step_valuation (r : ℕ) {d : ℕ} (hd : d % 2 = 1) :
    3 ^ (2 ^ (r + 1) * d) - 1 =
        2 ^ (r + 3) *
          (lteQuotient r * oddGeomSum (3 ^ (2 ^ (r + 1))) d) ∧
      2 ^ (r + 3) ∣ (3 ^ (2 ^ (r + 1) * d) - 1) ∧
      ¬ (2 ^ (r + 4) ∣ (3 ^ (2 ^ (r + 1) * d) - 1)) := by
  have hid := three_pow_two_pow_mul_eq_one_add r d
  have hsub :
      3 ^ (2 ^ (r + 1) * d) - 1 =
        2 ^ (r + 3) *
          (lteQuotient r * oddGeomSum (3 ^ (2 ^ (r + 1))) d) := by
    omega
  have h3odd : 3 ^ (2 ^ (r + 1)) % 2 = 1 :=
    odd_pow_mod_two (by decide : 3 % 2 = 1) (2 ^ (r + 1))
  have hg_odd : oddGeomSum (3 ^ (2 ^ (r + 1))) d % 2 = 1 := by
    rw [oddGeomSum_mod_two h3odd, hd]
  have hq_odd := lteQuotient_odd r
  have hprod_odd :
      (lteQuotient r * oddGeomSum (3 ^ (2 ^ (r + 1))) d) % 2 = 1 := by
    rw [Nat.mul_mod, hq_odd, hg_odd]
  refine ⟨hsub, ⟨_, hsub⟩, ?_⟩
  rw [hsub]
  rintro ⟨k, hk⟩
  have hsplit : 2 ^ (r + 4) * k = 2 ^ (r + 3) * (2 * k) := by
    rw [show r + 4 = (r + 3) + 1 by omega, Nat.pow_add]
    ring
  rw [hsplit] at hk
  have hpos : 0 < 2 ^ (r + 3) := Nat.pow_pos (by decide)
  have heq :
      lteQuotient r * oddGeomSum (3 ^ (2 ^ (r + 1))) d = 2 * k :=
    Nat.eq_of_mul_eq_mul_left hpos hk
  omega

/-! ## 2. Full Step-Sum Valuation Lock for Odd and Even Step Sums -/

/-- **Odd Step-Sum Modulo-4 Lock (`odd_step_sum_u0_add_remainder_mod_four`)**:
Whenever `blockSteps s m % 2 = 1` and `2 ≤ tailSteps s m` along
`ValidBlockChain a_0 s u K` (`m < K`),
`(u 0 + coprimeRemainder s m) % 4 = 2`. -/
theorem odd_step_sum_u0_add_remainder_mod_four
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hodd : blockSteps s m % 2 = 1)
    (htail : 2 ≤ tailSteps s m) :
    (u 0 + coprimeRemainder s m) % 4 = 2 := by
  have hid := coprime_quotient_m_step_identity hmK hchain
  have hdvd4 : 4 ∣ 2 ^ (tailSteps s m) * u m := by
    have h4 : 2 ^ 2 ∣ 2 ^ (tailSteps s m) := Nat.pow_dvd_pow 2 htail
    simpa using dvd_mul_of_dvd_left h4 (u m)
  have h0_mod4 : (2 ^ (tailSteps s m) * u m) % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd4
  have h3_mod8 := (three_pow_mod_eight (blockSteps s m)).2 hodd
  have h3_mod4 : 3 ^ (blockSteps s m) % 4 = 3 := by omega
  rcases hchain 0 (by omega : 0 < K) with ⟨_, hu0_odd, _⟩
  rw [hid, Nat.add_mod, Nat.mul_mod, h3_mod4] at h0_mod4
  omega

/-- **Even Step-Sum Valuation Lock (`even_step_sum_u0_add_remainder_valuation`)**:
Whenever `blockSteps s m = 2^(r + 1) * d` (`d % 2 = 1`) and `r + 4 ≤ tailSteps s m`
along `ValidBlockChain a_0 s u K` (`m < K`), `2^(r + 3)` divides
`u 0 + coprimeRemainder s m` and `2^(r + 4)` does **not**. -/
theorem even_step_sum_u0_add_remainder_valuation
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m r d : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hsteps : blockSteps s m = 2 ^ (r + 1) * d)
    (hd_odd : d % 2 = 1)
    (htail : r + 4 ≤ tailSteps s m) :
    2 ^ (r + 3) ∣ (u 0 + coprimeRemainder s m) ∧
      ¬ (2 ^ (r + 4) ∣ (u 0 + coprimeRemainder s m)) := by
  have hdiff := coprime_step_sum_diff_eq hmK hchain
  have hlte := (three_pow_even_step_valuation r hd_odd).1
  rw [hsteps, hlte] at hdiff
  set Q := lteQuotient r * oddGeomSum (3 ^ (2 ^ (r + 1))) d
  have h3odd : 3 ^ (2 ^ (r + 1)) % 2 = 1 :=
    odd_pow_mod_two (by decide : 3 % 2 = 1) (2 ^ (r + 1))
  have hg_odd : oddGeomSum (3 ^ (2 ^ (r + 1))) d % 2 = 1 := by
    rw [oddGeomSum_mod_two h3odd, hd_odd]
  have hq_odd := lteQuotient_odd r
  rcases hchain 0 (by omega : 0 < K) with ⟨_, hu0_odd, _⟩
  have hQ_odd : Q % 2 = 1 := by
    dsimp only [Q]
    rw [Nat.mul_mod, hq_odd, hg_odd]
  have hQu0_odd : (Q * u 0) % 2 = 1 := by
    rw [Nat.mul_mod, hQ_odd, hu0_odd]
  have hdvd3_lhs : 2 ^ (r + 3) ∣ 2 ^ (tailSteps s m) * u m :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega : r + 3 ≤ tailSteps s m)) (u m)
  have hdvd3_term : 2 ^ (r + 3) ∣ 2 ^ (r + 3) * Q * u 0 :=
    ⟨Q * u 0, by ring⟩
  have hdvd3 : 2 ^ (r + 3) ∣ (u 0 + coprimeRemainder s m) := by
    rw [hdiff] at hdvd3_lhs
    exact (Nat.dvd_add_right hdvd3_term).mp hdvd3_lhs
  refine ⟨hdvd3, ?_⟩
  intro hdvd4
  have hdvd4_lhs : 2 ^ (r + 4) ∣ 2 ^ (tailSteps s m) * u m :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 htail) (u m)
  rw [hdiff] at hdvd4_lhs
  have hdvd4_term : 2 ^ (r + 4) ∣ 2 ^ (r + 3) * Q * u 0 :=
    (Nat.dvd_add_left hdvd4).mp hdvd4_lhs
  rcases hdvd4_term with ⟨k, hk⟩
  have hsplit :
      2 ^ (r + 3) * (Q * u 0) = 2 ^ (r + 3) * (2 * k) := by
    calc
      2 ^ (r + 3) * (Q * u 0) = 2 ^ (r + 3) * Q * u 0 := by ring
      _ = 2 ^ (r + 4) * k := hk
      _ = 2 ^ (r + 3) * (2 * k) := by
        rw [show r + 4 = (r + 3) + 1 by omega, Nat.pow_add]
        ring
  have hpos : 0 < 2 ^ (r + 3) := Nat.pow_pos (by decide)
  have heq : Q * u 0 = 2 * k := Nat.eq_of_mul_eq_mul_left hpos hsplit
  omega

/-! ## 3. Cross-Horizon `u 0`-Elimination Compatibility Law -/

/-- **Cross-Horizon `u 0`-Elimination Valuation Lock
(`cross_horizon_even_step_sum_valuation_lock`)**:
If at two horizons `m1, m2 < K` (`coprimeRemainder s m1 ≤ coprimeRemainder s m2`)
along `ValidBlockChain a_0 s u K` we have
- `blockSteps s m1 = 2^(r1 + 1) * d1` (`d1 % 2 = 1`, `r1 + 4 ≤ tailSteps s m1`),
- `blockSteps s m2 = 2^(r2 + 1) * d2` (`d2 % 2 = 1`, `r2 + 4 ≤ tailSteps s m2`), and
- `r1 < r2`,
then eliminating `u 0` locks the exact 2-adic valuation of the purely
`s`-dependent polynomial difference `coprimeRemainder s m2 - coprimeRemainder s m1`
at `r1 + 3` (divisible by `2^(r1 + 3)` and not by `2^(r1 + 4)`). -/
theorem cross_horizon_even_step_sum_valuation_lock
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m1 m2 r1 r2 d1 d2 : ℕ}
    (hm1 : m1 < K) (hm2 : m2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsteps1 : blockSteps s m1 = 2 ^ (r1 + 1) * d1) (hd1 : d1 % 2 = 1)
    (htail1 : r1 + 4 ≤ tailSteps s m1)
    (hsteps2 : blockSteps s m2 = 2 ^ (r2 + 1) * d2) (hd2 : d2 % 2 = 1)
    (htail2 : r2 + 4 ≤ tailSteps s m2)
    (hr : r1 < r2)
    (hle : coprimeRemainder s m1 ≤ coprimeRemainder s m2) :
    2 ^ (r1 + 3) ∣ (coprimeRemainder s m2 - coprimeRemainder s m1) ∧
      ¬ (2 ^ (r1 + 4) ∣ (coprimeRemainder s m2 - coprimeRemainder s m1)) := by
  have hv1 :=
    even_step_sum_u0_add_remainder_valuation hm1 hchain hsteps1 hd1 htail1
  have hv2 :=
    even_step_sum_u0_add_remainder_valuation hm2 hchain hsteps2 hd2 htail2
  have hadd :
      u 0 + coprimeRemainder s m2 =
        (u 0 + coprimeRemainder s m1) +
          (coprimeRemainder s m2 - coprimeRemainder s m1) := by
    omega
  have hdvd_2_r1_4 : 2 ^ (r1 + 4) ∣ (u 0 + coprimeRemainder s m2) :=
    dvd_trans (Nat.pow_dvd_pow 2 (by omega : r1 + 4 ≤ r2 + 3)) hv2.1
  have hdvd_2_r1_3 : 2 ^ (r1 + 3) ∣ (u 0 + coprimeRemainder s m2) :=
    dvd_trans (Nat.pow_dvd_pow 2 (by omega : r1 + 3 ≤ r2 + 3)) hv2.1
  have hdvd3_diff :
      2 ^ (r1 + 3) ∣ (coprimeRemainder s m2 - coprimeRemainder s m1) := by
    rw [hadd] at hdvd_2_r1_3
    exact (Nat.dvd_add_right hv1.1).mp hdvd_2_r1_3
  refine ⟨hdvd3_diff, ?_⟩
  intro hdvd4_diff
  rw [hadd] at hdvd_2_r1_4
  have hdvd4_1 : 2 ^ (r1 + 4) ∣ (u 0 + coprimeRemainder s m1) :=
    (Nat.dvd_add_left hdvd4_diff).mp hdvd_2_r1_4
  exact hv1.2 hdvd4_1

end Mahler.FullStepValuation
