import TwoAdicCauchyConvergence

/-!
# Horizon-Independent Slack Depletion Valuations & All-History Recovery of `u r`

This module formalizes the horizon-independent 2-adic valuation of the slack
depletion `3^S_d * integerSlack s r - integerSlack s (r + d)` and the
unconditional all-history recovery of every intermediate coprime quotient `u r`
(`0 ≤ r < r + d`) from the terminal quotient `u (r + d)`:

1. **Horizon-Independent 2-adic Valuation of Slack Depletion
   (`slack_depletion_eq_two_pow_mul_remainder`,
   `slack_depletion_horizon_independent_valuation`)**:
   - For every sequence `s`, prefix `r`, and lookahead `d`,
     `3^(blockSteps (shiftSeq s r) d) * integerSlack s r - integerSlack s (r + d) =
       2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d`.
   - Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, its exact 2-adic valuation
     is `blockSteps s (r + 1) + 1`, completely independent of the lookahead `d`.
2. **Unconditional All-History Recovery of `u r` from `u (r + d)`
   (`shifted_coprime_quotient_m_step_identity`,
   `all_history_quotient_and_remainder_recovery`,
   `shifted_coprime_step_diff_coprime_six`)**:
   - Along any `ValidBlockChain a_0 s u K` (`r + d < K`),
     `2^(tailSteps (shiftSeq s r) d) * u (r + d) =
       3^(blockSteps (shiftSeq s r) d) * u r + coprimeRemainder (shiftSeq s r) d`.
   - For every `1 ≤ d` (`r + d < K`), dividing
     `2^(tailSteps (shiftSeq s r) d) * u (r + d)` by
     `3^(blockSteps (shiftSeq s r) d)` recovers exact quotient `u r` and exact
     remainder `coprimeRemainder (shiftSeq s r) d` unconditionally.
   - The difference `2^(tailSteps (shiftSeq s r) d) * u (r + d) - 3^(blockSteps (shiftSeq s r) d) * u r`
     is always coprime to `6` (divisible by neither `2` nor `3`).
-/

namespace Mahler.AllHistoryRecovery

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

/-! ## 1. Horizon-Independent 2-adic Valuation of Slack Depletion -/

/-- Exact identity for the multi-step slack depletion from `r` to `r + d`:
`3^(blockSteps (shiftSeq s r) d) * integerSlack s r - integerSlack s (r + d) =
  2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d`. -/
theorem slack_depletion_eq_two_pow_mul_remainder (s : ℕ → ℕ) (r d : ℕ) :
    (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) * integerSlack s r -
        integerSlack s (r + d) =
      (2 : ℤ) ^ (blockSteps s r + s r + 1) *
        (coprimeRemainder (shiftSeq s r) d : ℤ) := by
  have hid := integerSlack_add_coprimeRemainder_eq s r d
  linarith

/-- **Horizon-Independent 2-adic Valuation of Slack Depletion
(`slack_depletion_horizon_independent_valuation`)**:
Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the multi-step slack depletion
`2^(blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d` has exact
2-adic valuation `blockSteps s (r + 1) + 1`, independent of `d` (divisible by
`2^(blockSteps s (r + 1) + 1)` and not by `2^(blockSteps s (r + 1) + 2)`). -/
theorem slack_depletion_horizon_independent_valuation {s : ℕ → ℕ} {r d : ℕ}
    (hd : 1 ≤ d) (hs : ∀ k < d, 1 ≤ s (r + k)) :
    2 ^ (blockSteps s (r + 1) + 1) ∣
        (2 ^ (blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d) ∧
      ¬ (2 ^ (blockSteps s (r + 1) + 2) ∣
        (2 ^ (blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d)) := by
  have hodd : coprimeRemainder (shiftSeq s r) d % 2 = 1 :=
    coprimeRemainder_odd hd (fun k hk => by simpa [shiftSeq] using hs k hk)
  have hsteps : blockSteps s (r + 1) = blockSteps s r + s r := rfl
  rw [hsteps]
  refine ⟨⟨coprimeRemainder (shiftSeq s r) d, rfl⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hsplit :
      2 ^ (blockSteps s r + s r + 2) * q =
        2 ^ (blockSteps s r + s r + 1) * (2 * q) := by
    rw [show blockSteps s r + s r + 2 = (blockSteps s r + s r + 1) + 1 by omega,
      Nat.pow_add]
    ring
  rw [hsplit] at hq
  have hpos : 0 < 2 ^ (blockSteps s r + s r + 1) := Nat.pow_pos (by decide)
  have heq : coprimeRemainder (shiftSeq s r) d = 2 * q :=
    Nat.eq_of_mul_eq_mul_left hpos hq
  omega

/-! ## 2. All-History Backward Recovery of Every `u r` from `u (r + d)` -/

/-- **Shifted `d`-Step Coprime Quotient Identity
(`shifted_coprime_quotient_m_step_identity`)**:
Along any `ValidBlockChain a_0 s u K` (`r + d < K`),
`2^(tailSteps (shiftSeq s r) d) * u (r + d) =
  3^(blockSteps (shiftSeq s r) d) * u r + coprimeRemainder (shiftSeq s r) d`. -/
theorem shifted_coprime_quotient_m_step_identity
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hrd : r + d < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) =
      3 ^ (blockSteps (shiftSeq s r) d) * u r +
        coprimeRemainder (shiftSeq s r) d := by
  have hchain_sub : ValidBlockChain a_0 s u (r + (d + 1)) :=
    fun k hk => hchain k (by omega)
  have hchain_shift := validBlockChain_shift hchain_sub
  have hid :=
    coprime_quotient_m_step_identity (Nat.lt_succ_self d) hchain_shift
  simpa [shiftSeq] using hid

/-- **Unconditional All-History Recovery of `u r` and `R^{(r)}_d`
(`all_history_quotient_and_remainder_recovery`)**:
Along any `ValidBlockChain a_0 s u K` with `1 ≤ d` and `r + d < K` (requiring
no real companion or `minSlack > 0` hypothesis), dividing
`2^(tailSteps (shiftSeq s r) d) * u (r + d)` by `3^(blockSteps (shiftSeq s r) d)`
recovers exact quotient `u r` and exact remainder
`coprimeRemainder (shiftSeq s r) d`. -/
theorem all_history_quotient_and_remainder_recovery
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K) :
    (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) /
        3 ^ (blockSteps (shiftSeq s r) d) = u r ∧
      (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) %
        3 ^ (blockSteps (shiftSeq s r) d) =
        coprimeRemainder (shiftSeq s r) d := by
  have hchain_sub : ValidBlockChain a_0 s u (r + (d + 1)) :=
    fun k hk => hchain k (by omega)
  have hchain_shift := validBlockChain_shift hchain_sub
  have hrec :=
    unconditional_u0_div_mod_recovery hd (Nat.lt_succ_self d) hchain_shift
  simpa [shiftSeq] using hrec

/-- **Universal Coprimality to `6` of the Multi-Step Quotient Difference
(`shifted_coprime_step_diff_coprime_six`)**:
Along any `ValidBlockChain a_0 s u K` with `1 ≤ d` and `r + d < K`, the
difference `2^(tailSteps (shiftSeq s r) d) * u (r + d) - 3^(blockSteps (shiftSeq s r) d) * u r`
equals `coprimeRemainder (shiftSeq s r) d` and is divisible by neither `2` nor `3`. -/
theorem shifted_coprime_step_diff_coprime_six
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) -
        3 ^ (blockSteps (shiftSeq s r) d) * u r =
        coprimeRemainder (shiftSeq s r) d ∧
      ¬ (2 ∣
        (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * u r)) ∧
      ¬ (3 ∣
        (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * u r)) := by
  have hid := shifted_coprime_quotient_m_step_identity hrd hchain
  have hsub :
      2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * u r =
        coprimeRemainder (shiftSeq s r) d := by
    omega
  have hcop :=
    coprimeRemainder_coprime_six (s := shiftSeq s r) hd
      (fun k hk => (hchain (r + k) (by omega)).1)
  rw [hsub]
  exact ⟨rfl, hcop.2.2.1, hcop.2.2.2⟩

end Mahler.AllHistoryRecovery
