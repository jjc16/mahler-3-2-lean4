import CoprimeRemainderAdditionLaw

/-!
# The 2-adic Cauchy Convergence Law for `-R(s, r) / 3^T(r)` & Intrinsic Difference Valuations

This module formalizes the 2-adic Cauchy convergence law for the rational
fractions `coprimeRemainder s r / 3^(blockSteps s r)` and proves the
unconditional intrinsic 2-adic valuation laws for
`coprimeRemainder s (r + d) - coprimeRemainder s r` (requiring no
`ValidBlockChain` hypothesis):

1. **Cross-Multiplied 2-adic Cauchy Identity & Exact Valuation
   (`cross_multiplied_coprimeRemainder_eq`,
   `cross_multiplied_coprimeRemainder_valuation`)**:
   - For every sequence `s : ℕ → ℕ`, prefix `r`, and offset `d`,
     `3^(blockSteps s r) * coprimeRemainder s (r + d) =
       3^(blockSteps s (r + d)) * coprimeRemainder s r +
         2^(tailSteps s r) * (3^(blockSteps s r) * coprimeRemainder (shiftSeq s r) d)`.
   - Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the cross-multiplied
     difference has exact 2-adic valuation `tailSteps s r` (divisible by
     `2^(tailSteps s r)` and not by `2^(tailSteps s r + 1)`).
2. **Unconditional Intrinsic Difference Valuations
   (`coprimeRemainder_step_diff_eq`,
   `intrinsic_odd_step_diff_mod_four`,
   `intrinsic_even_step_diff_valuation`)**:
   - `coprimeRemainder s (r + d) =
       coprimeRemainder s r +
         (3^(blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r +
         2^(tailSteps s r) * coprimeRemainder (shiftSeq s r) d`.
   - When `blockSteps (shiftSeq s r) d % 2 = 1` and `2 ≤ tailSteps s r`
     (`1 ≤ r`, `∀ k < r, 1 ≤ s k`),
     `(coprimeRemainder s (r + d) - coprimeRemainder s r) % 4 = 2`.
   - When `blockSteps (shiftSeq s r) d = 2^(k + 1) * q` (`q % 2 = 1`) and
     `k + 4 ≤ tailSteps s r` (`1 ≤ r`, `∀ k' < r, 1 ≤ s k'`),
     `coprimeRemainder s (r + d) - coprimeRemainder s r` has exact 2-adic
     valuation `k + 3` (`2^(k + 3)` divides it and `2^(k + 4)` does not).
-/

namespace Mahler.TwoAdicCauchy

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
open Mahler.FullStepValuation
open Mahler.RemainderAdditionLaw

/-! ## 1. Cross-Multiplied 2-adic Cauchy Identity & Exact Valuation -/

/-- **Cross-Multiplied 2-adic Cauchy Identity (`cross_multiplied_coprimeRemainder_eq`)**:
For every sequence `s : ℕ → ℕ`, prefix `r`, and offset `d`,
`3^(blockSteps s r) * coprimeRemainder s (r + d) =
  3^(blockSteps s (r + d)) * coprimeRemainder s r +
    2^(tailSteps s r) * (3^(blockSteps s r) * coprimeRemainder (shiftSeq s r) d)`. -/
theorem cross_multiplied_coprimeRemainder_eq (s : ℕ → ℕ) (r d : ℕ) :
    3 ^ (blockSteps s r) * coprimeRemainder s (r + d) =
      3 ^ (blockSteps s (r + d)) * coprimeRemainder s r +
        2 ^ (tailSteps s r) *
          (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) := by
  rw [coprimeRemainder_add_eq s r d, blockSteps_add s r d, Nat.pow_add]
  ring

private theorem three_pow_odd (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **Exact 2-adic Cauchy Valuation (`cross_multiplied_coprimeRemainder_valuation`)**:
Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the cross-multiplied difference
`3^(blockSteps s r) * coprimeRemainder s (r + d) - 3^(blockSteps s (r + d)) * coprimeRemainder s r`
has exact 2-adic valuation `tailSteps s r`. -/
theorem cross_multiplied_coprimeRemainder_valuation {s : ℕ → ℕ} {r d : ℕ}
    (hd : 1 ≤ d) (hs : ∀ k < d, 1 ≤ s (r + k)) :
    3 ^ (blockSteps s r) * coprimeRemainder s (r + d) -
        3 ^ (blockSteps s (r + d)) * coprimeRemainder s r =
        2 ^ (tailSteps s r) *
          (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) ∧
      2 ^ (tailSteps s r) ∣
        (3 ^ (blockSteps s r) * coprimeRemainder s (r + d) -
          3 ^ (blockSteps s (r + d)) * coprimeRemainder s r) ∧
      ¬ (2 ^ (tailSteps s r + 1) ∣
        (3 ^ (blockSteps s r) * coprimeRemainder s (r + d) -
          3 ^ (blockSteps s (r + d)) * coprimeRemainder s r)) := by
  have hid := cross_multiplied_coprimeRemainder_eq s r d
  have hsub :
      3 ^ (blockSteps s r) * coprimeRemainder s (r + d) -
          3 ^ (blockSteps s (r + d)) * coprimeRemainder s r =
        2 ^ (tailSteps s r) *
          (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) := by
    omega
  have hR_odd : coprimeRemainder (shiftSeq s r) d % 2 = 1 :=
    coprimeRemainder_odd hd (fun k hk => by simpa [shiftSeq] using hs k hk)
  have h3_odd : 3 ^ (blockSteps s r) % 2 = 1 := three_pow_odd (blockSteps s r)
  have hprod_odd :
      (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) % 2 = 1 := by
    rw [Nat.mul_mod, h3_odd, hR_odd]
  refine ⟨hsub, ⟨_, hsub⟩, ?_⟩
  rw [hsub]
  rintro ⟨q, hq⟩
  have hsplit : 2 ^ (tailSteps s r + 1) * q = 2 ^ (tailSteps s r) * (2 * q) := by
    rw [Nat.pow_add]
    ring
  rw [hsplit] at hq
  have hpos : 0 < 2 ^ (tailSteps s r) := Nat.pow_pos (by decide)
  have heq :
      3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d = 2 * q :=
    Nat.eq_of_mul_eq_mul_left hpos hq
  omega

/-! ## 2. Unconditional Intrinsic Valuations of `coprimeRemainder s (r + d) - coprimeRemainder s r` -/

/-- Exact decomposition of `coprimeRemainder s (r + d)` relative to `coprimeRemainder s r`:
`coprimeRemainder s (r + d) =
  coprimeRemainder s r +
    (3^(blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r +
    2^(tailSteps s r) * coprimeRemainder (shiftSeq s r) d`. -/
theorem coprimeRemainder_step_diff_eq (s : ℕ → ℕ) (r d : ℕ) :
    coprimeRemainder s (r + d) =
      coprimeRemainder s r +
        (3 ^ (blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r +
        2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d := by
  have hadd := coprimeRemainder_add_eq s r d
  have hpos : 1 ≤ 3 ^ (blockSteps (shiftSeq s r) d) := Nat.pow_pos (by decide)
  have hmul :
      3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r =
        coprimeRemainder s r +
          (3 ^ (blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r := by
    calc
      3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r =
          ((3 ^ (blockSteps (shiftSeq s r) d) - 1) + 1) * coprimeRemainder s r := by
            rw [Nat.sub_add_cancel hpos]
      _ = coprimeRemainder s r +
            (3 ^ (blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r := by ring
  rw [hmul] at hadd
  exact hadd

/-- **Unconditional Intrinsic Odd Step-Difference Modulo-4 Law
(`intrinsic_odd_step_diff_mod_four`)**:
For any sequence `s : ℕ → ℕ` with `1 ≤ r`, `∀ k < r, 1 ≤ s k`,
`2 ≤ tailSteps s r`, and `blockSteps (shiftSeq s r) d % 2 = 1`,
`(coprimeRemainder s (r + d) - coprimeRemainder s r) % 4 = 2`. -/
theorem intrinsic_odd_step_diff_mod_four {s : ℕ → ℕ} {r d : ℕ}
    (hr : 1 ≤ r) (hs : ∀ k < r, 1 ≤ s k)
    (htail : 2 ≤ tailSteps s r)
    (hodd_step : blockSteps (shiftSeq s r) d % 2 = 1) :
    (coprimeRemainder s (r + d) - coprimeRemainder s r) % 4 = 2 := by
  have hdiff_eq := coprimeRemainder_step_diff_eq s r d
  have hsub :
      coprimeRemainder s (r + d) - coprimeRemainder s r =
        (3 ^ (blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r +
          2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d := by
    omega
  have hR_odd : coprimeRemainder s r % 2 = 1 := coprimeRemainder_odd hr hs
  have h3_mod8 := (three_pow_mod_eight (blockSteps (shiftSeq s r) d)).2 hodd_step
  have hpos3 : 1 ≤ 3 ^ (blockSteps (shiftSeq s r) d) := Nat.pow_pos (by decide)
  have h3_sub_mod4 : (3 ^ (blockSteps (shiftSeq s r) d) - 1) % 4 = 2 := by omega
  have hdvd4 : 4 ∣ 2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d := by
    have h4 : 2 ^ 2 ∣ 2 ^ (tailSteps s r) := Nat.pow_dvd_pow 2 htail
    simpa using dvd_mul_of_dvd_left h4 (coprimeRemainder (shiftSeq s r) d)
  have h0_mod4 :
      (2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d) % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd4
  rw [hsub, Nat.add_mod, h0_mod4, Nat.mul_mod, h3_sub_mod4]
  omega

/-- **Unconditional Intrinsic Even Step-Difference Valuation Law
(`intrinsic_even_step_diff_valuation`)**:
For any sequence `s : ℕ → ℕ` with `1 ≤ r`, `∀ k' < r, 1 ≤ s k'`,
`blockSteps (shiftSeq s r) d = 2^(k + 1) * q` (`q % 2 = 1`), and
`k + 4 ≤ tailSteps s r`, the difference
`coprimeRemainder s (r + d) - coprimeRemainder s r` has exact 2-adic valuation
`k + 3` (`2^(k + 3)` divides it and `2^(k + 4)` does not). -/
theorem intrinsic_even_step_diff_valuation {s : ℕ → ℕ} {r d k q : ℕ}
    (hr : 1 ≤ r) (hs : ∀ k' < r, 1 ≤ s k')
    (hsteps : blockSteps (shiftSeq s r) d = 2 ^ (k + 1) * q)
    (hq_odd : q % 2 = 1)
    (htail : k + 4 ≤ tailSteps s r) :
    2 ^ (k + 3) ∣ (coprimeRemainder s (r + d) - coprimeRemainder s r) ∧
      ¬ (2 ^ (k + 4) ∣ (coprimeRemainder s (r + d) - coprimeRemainder s r)) := by
  have hdiff_eq := coprimeRemainder_step_diff_eq s r d
  have hsub :
      coprimeRemainder s (r + d) - coprimeRemainder s r =
        (3 ^ (blockSteps (shiftSeq s r) d) - 1) * coprimeRemainder s r +
          2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d := by
    omega
  have hlte := (three_pow_even_step_valuation k hq_odd).1
  rw [hsteps, hlte] at hsub
  set Q := lteQuotient k * oddGeomSum (3 ^ (2 ^ (k + 1))) q
  have h3odd : 3 ^ (2 ^ (k + 1)) % 2 = 1 := three_pow_odd (2 ^ (k + 1))
  have hg_odd : oddGeomSum (3 ^ (2 ^ (k + 1))) q % 2 = 1 := by
    rw [oddGeomSum_mod_two h3odd, hq_odd]
  have hlk_odd := lteQuotient_odd k
  have hQ_odd : Q % 2 = 1 := by
    dsimp only [Q]
    rw [Nat.mul_mod, hlk_odd, hg_odd]
  have hR_odd : coprimeRemainder s r % 2 = 1 := coprimeRemainder_odd hr hs
  have hQR_odd : (Q * coprimeRemainder s r) % 2 = 1 := by
    rw [Nat.mul_mod, hQ_odd, hR_odd]
  have hdvd3_1 :
      2 ^ (k + 3) ∣ 2 ^ (k + 3) * Q * coprimeRemainder s r :=
    ⟨Q * coprimeRemainder s r, by ring⟩
  have hdvd3_2 :
      2 ^ (k + 3) ∣ 2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega : k + 3 ≤ tailSteps s r)) _
  have hdvd3 :
      2 ^ (k + 3) ∣ (coprimeRemainder s (r + d) - coprimeRemainder s r) := by
    rw [hsub]
    exact Nat.dvd_add hdvd3_1 hdvd3_2
  refine ⟨hdvd3, ?_⟩
  intro hdvd4
  rw [hsub] at hdvd4
  have hdvd4_2 :
      2 ^ (k + 4) ∣ 2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 htail) _
  have hdvd4_1 :
      2 ^ (k + 4) ∣ 2 ^ (k + 3) * Q * coprimeRemainder s r :=
    (Nat.dvd_add_left hdvd4_2).mp hdvd4
  rcases hdvd4_1 with ⟨m', hm'⟩
  have hsplit :
      2 ^ (k + 3) * (Q * coprimeRemainder s r) = 2 ^ (k + 3) * (2 * m') := by
    calc
      2 ^ (k + 3) * (Q * coprimeRemainder s r) =
          2 ^ (k + 3) * Q * coprimeRemainder s r := by ring
      _ = 2 ^ (k + 4) * m' := hm'
      _ = 2 ^ (k + 3) * (2 * m') := by
        rw [show k + 4 = (k + 3) + 1 by omega, Nat.pow_add]
        ring
  have hpos : 0 < 2 ^ (k + 3) := Nat.pow_pos (by decide)
  have heq : Q * coprimeRemainder s r = 2 * m' :=
    Nat.eq_of_mul_eq_mul_left hpos hsplit
  omega

end Mahler.TwoAdicCauchy
