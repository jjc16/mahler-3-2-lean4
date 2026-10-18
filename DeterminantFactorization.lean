import CoprimeUnitRigidity

/-!
# Exact `(3^T, Δ)` Interpolation Determinant Factorization & Rank-1 Valuation Collapse

This module formalizes the $2 \times 2$ interpolation determinant of the points
`(3^(blockSteps s m), integerSlack s m)` from **Idea 3** and proves its exact
2-adic and 3-adic valuations (establishing **Dead End 12**: why polynomial
interpolation determinants in `(3^T, Δ)` alone have 2-adic valuation locked at
the smaller index `T(r + 1) + 1` rather than `T(r + 1) + T(r + d + 1)`):

1. **The $2 \times 2$ Interpolation Determinant `slackDeterminant`
   (`slackDeterminant`, `slackDeterminant_eq_three_pow_mul_two_pow_mul_remainder`)**:
   Define
   `slackDeterminant s r d : ℤ :=
     3^(blockSteps s (r + d)) * integerSlack s r -
       3^(blockSteps s r) * integerSlack s (r + d)`.
   For every sequence `s`, prefix `r`, and offset `d`:
   `slackDeterminant s r d =
     3^(blockSteps s r) * 2^(blockSteps s (r + 1) + 1) * coprimeRemainder (shiftSeq s r) d`.
2. **Exact 2-adic and 3-adic Valuations of the Determinant — Dead End 12
   (`slackDeterminant_two_adic_valuation`,
   `slackDeterminant_three_adic_valuation`)**:
   Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, because
   `coprimeRemainder (shiftSeq s r) d` is coprime to `6`:
   - The **exact 2-adic valuation** of the unsigned determinant is
     `blockSteps s (r + 1) + 1` (locked at the smaller index `r`, independent of `d`!).
   - The **exact 3-adic valuation** of the unsigned determinant is
     `blockSteps s r` (locked at the smaller index `r`, independent of `d`!).
3. **Dual Column-Operation Factorization via `u r` and `u (r + d)`
   (`slackDeterminant_eq_quotient_determinant`)**:
   Along any `ValidBlockChain a_0 s u K` (`r + d < K`), eliminating `2 * a_0 + 1`
   between rows `r` and `r + d` yields:
   `slackDeterminant s r d =
     3^(blockSteps s r) * 2^(blockSteps s (r + 1) + 1) *
       (2^(tailSteps (shiftSeq s r) d) * u (r + d) -
         3^(blockSteps (shiftSeq s r) d) * u r)`.
-/

namespace Mahler.DeterminantCollapse

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
open Mahler.TwoAdicCauchy
open Mahler.AllHistoryRecovery
open Mahler.ParametricCorridor
open Mahler.AperiodicBoundedSqueeze
open Mahler.TimeIndependentSqueeze
open Mahler.SlackDeadEnds
open Mahler.GrandSynthesis
open Mahler.Mod256Sieve
open Mahler.UnitRigidity

/-! ## 1. The $2 \times 2$ Interpolation Determinant `slackDeterminant` -/

/-- The $2 \times 2$ determinant
`det [[3^T(r), Δ_r], [3^T(r+d), Δ_{r+d}]] = 3^T(r+d) * Δ_r - 3^T(r) * Δ_{r+d}`. -/
def slackDeterminant (s : ℕ → ℕ) (r d : ℕ) : ℤ :=
  (3 : ℤ) ^ (blockSteps s (r + d)) * integerSlack s r -
    (3 : ℤ) ^ (blockSteps s r) * integerSlack s (r + d)

/-- The unsigned natural-number value of `slackDeterminant s r d`:
`3^T(r) * 2^(T(r + 1) + 1) * coprimeRemainder (shiftSeq s r) d`. -/
def slackDeterminantNat (s : ℕ → ℕ) (r d : ℕ) : ℕ :=
  3 ^ (blockSteps s r) * 2 ^ (blockSteps s (r + 1) + 1) *
    coprimeRemainder (shiftSeq s r) d

/-- **Exact Factorization of `slackDeterminant`
(`slackDeterminant_eq_three_pow_mul_two_pow_mul_remainder`)**:
For every sequence `s`, prefix `r`, and offset `d`,
`slackDeterminant s r d = (slackDeterminantNat s r d : ℤ)`. -/
theorem slackDeterminant_eq_three_pow_mul_two_pow_mul_remainder
    (s : ℕ → ℕ) (r d : ℕ) :
    slackDeterminant s r d = (slackDeterminantNat s r d : ℤ) := by
  unfold slackDeterminant slackDeterminantNat
  have hdepl := slack_depletion_eq_two_pow_mul_remainder s r d
  have hpow3 :
      (3 : ℤ) ^ (blockSteps s (r + d)) =
        (3 : ℤ) ^ (blockSteps s r) *
          (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) := by
    rw [blockSteps_add, pow_add]
  have hsteps1 : blockSteps s (r + 1) = blockSteps s r + s r := rfl
  push_cast
  rw [hpow3, hsteps1]
  calc
    (3 : ℤ) ^ (blockSteps s r) * (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) *
        integerSlack s r -
      (3 : ℤ) ^ (blockSteps s r) * integerSlack s (r + d) =
      (3 : ℤ) ^ (blockSteps s r) *
        ((3 : ℤ) ^ (blockSteps (shiftSeq s r) d) * integerSlack s r -
          integerSlack s (r + d)) := by ring
    _ = (3 : ℤ) ^ (blockSteps s r) *
          ((2 : ℤ) ^ (blockSteps s r + s r + 1) *
            (coprimeRemainder (shiftSeq s r) d : ℤ)) := by rw [hdepl]
    _ = (3 : ℤ) ^ (blockSteps s r) * (2 : ℤ) ^ (blockSteps s r + s r + 1) *
          (coprimeRemainder (shiftSeq s r) d : ℤ) := by ring

/-! ## 2. Dead End 12: Exact 2-adic and 3-adic Valuation Collapse of `slackDeterminantNat` -/

private theorem three_pow_odd_nat (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem two_pow_mod_three_ne_zero_nat (n : ℕ) : 2 ^ n % 3 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      omega

/-- **Dead End 12a — Exact 2-adic Valuation of `slackDeterminantNat`
(`slackDeterminant_two_adic_valuation`)**:
Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the 2-adic valuation of
`slackDeterminantNat s r d` is locked at `blockSteps s (r + 1) + 1` (depending
only on `r`, not on `r + d`!). -/
theorem slackDeterminant_two_adic_valuation {s : ℕ → ℕ} {r d : ℕ}
    (hd : 1 ≤ d) (hs : ∀ k < d, 1 ≤ s (r + k)) :
    2 ^ (blockSteps s (r + 1) + 1) ∣ slackDeterminantNat s r d ∧
      ¬ (2 ^ (blockSteps s (r + 1) + 2) ∣ slackDeterminantNat s r d) := by
  unfold slackDeterminantNat
  have hR_odd : coprimeRemainder (shiftSeq s r) d % 2 = 1 :=
    coprimeRemainder_odd hd (fun k hk => by simpa [shiftSeq] using hs k hk)
  have h3_odd : 3 ^ (blockSteps s r) % 2 = 1 :=
    three_pow_odd_nat (blockSteps s r)
  have hprod_odd :
      (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) % 2 = 1 := by
    rw [Nat.mul_mod, h3_odd, hR_odd]
  refine ⟨⟨3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d, by ring⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hmul :
      2 ^ (blockSteps s (r + 1) + 1) *
          (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) =
        2 ^ (blockSteps s (r + 1) + 1) * (2 * q) := by
    calc
      2 ^ (blockSteps s (r + 1) + 1) *
          (3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d) =
        3 ^ (blockSteps s r) * 2 ^ (blockSteps s (r + 1) + 1) *
          coprimeRemainder (shiftSeq s r) d := by ring
      _ = 2 ^ (blockSteps s (r + 1) + 2) * q := hq
      _ = 2 ^ (blockSteps s (r + 1) + 1) * (2 * q) := by
        rw [show blockSteps s (r + 1) + 2 =
          (blockSteps s (r + 1) + 1) + 1 by omega, Nat.pow_add]
        ring
  have hpos : 0 < 2 ^ (blockSteps s (r + 1) + 1) := Nat.pow_pos (by decide)
  have heq :
      3 ^ (blockSteps s r) * coprimeRemainder (shiftSeq s r) d = 2 * q :=
    Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

/-- **Dead End 12b — Exact 3-adic Valuation of `slackDeterminantNat`
(`slackDeterminant_three_adic_valuation`)**:
Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the 3-adic valuation of
`slackDeterminantNat s r d` is locked at `blockSteps s r` (divisible by
`3^(blockSteps s r)` and not by `3^(blockSteps s r + 1)`). -/
theorem slackDeterminant_three_adic_valuation {s : ℕ → ℕ} {r d : ℕ}
    (hd : 1 ≤ d) (hs : ∀ k < d, 1 ≤ s (r + k)) :
    3 ^ (blockSteps s r) ∣ slackDeterminantNat s r d ∧
      ¬ (3 ^ (blockSteps s r + 1) ∣ slackDeterminantNat s r d) := by
  unfold slackDeterminantNat
  have hR_mod3 : coprimeRemainder (shiftSeq s r) d % 3 ≠ 0 :=
    coprimeRemainder_mod_three_ne_zero hd
      (fun k hk => by simpa [shiftSeq] using hs k hk)
  have h2_mod3 : 2 ^ (blockSteps s (r + 1) + 1) % 3 ≠ 0 :=
    two_pow_mod_three_ne_zero_nat (blockSteps s (r + 1) + 1)
  have hprod_mod3 :
      (2 ^ (blockSteps s (r + 1) + 1) *
          coprimeRemainder (shiftSeq s r) d) % 3 ≠ 0 := by
    have h2cases :
        2 ^ (blockSteps s (r + 1) + 1) % 3 = 1 ∨
          2 ^ (blockSteps s (r + 1) + 1) % 3 = 2 := by omega
    rcases h2cases with h1 | h2
    · rw [Nat.mul_mod, h1]
      omega
    · rw [Nat.mul_mod, h2]
      omega
  refine ⟨⟨2 ^ (blockSteps s (r + 1) + 1) *
    coprimeRemainder (shiftSeq s r) d, by ring⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hmul :
      3 ^ (blockSteps s r) *
          (2 ^ (blockSteps s (r + 1) + 1) *
            coprimeRemainder (shiftSeq s r) d) =
        3 ^ (blockSteps s r) * (3 * q) := by
    calc
      3 ^ (blockSteps s r) *
          (2 ^ (blockSteps s (r + 1) + 1) *
            coprimeRemainder (shiftSeq s r) d) =
        3 ^ (blockSteps s r) * 2 ^ (blockSteps s (r + 1) + 1) *
          coprimeRemainder (shiftSeq s r) d := by ring
      _ = 3 ^ (blockSteps s r + 1) * q := hq
      _ = 3 ^ (blockSteps s r) * (3 * q) := by
        rw [Nat.pow_add]
        ring
  have hpos : 0 < 3 ^ (blockSteps s r) := Nat.pow_pos (by decide)
  have heq :
      2 ^ (blockSteps s (r + 1) + 1) *
        coprimeRemainder (shiftSeq s r) d = 3 * q :=
    Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

/-! ## 3. Dual Column-Operation Factorization via `u r` and `u (r + d)` -/

/-- **Dual Column-Operation Factorization (`slackDeterminant_eq_quotient_determinant`)**:
Along any `ValidBlockChain a_0 s u K` (`r + d < K`),
`slackDeterminantNat s r d =
  3^(blockSteps s r) * 2^(blockSteps s (r + 1) + 1) *
    (2^(tailSteps (shiftSeq s r) d) * u (r + d) -
      3^(blockSteps (shiftSeq s r) d) * u r)`. -/
theorem slackDeterminant_eq_quotient_determinant
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hrd : r + d < K) (hchain : ValidBlockChain a_0 s u K) :
    slackDeterminantNat s r d =
      3 ^ (blockSteps s r) * 2 ^ (blockSteps s (r + 1) + 1) *
        (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * u r) := by
  unfold slackDeterminantNat
  have hid := shifted_coprime_quotient_m_step_identity hrd hchain
  have hsub :
      2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * u r =
        coprimeRemainder (shiftSeq s r) d := by
    omega
  rw [hsub]

end Mahler.DeterminantCollapse
