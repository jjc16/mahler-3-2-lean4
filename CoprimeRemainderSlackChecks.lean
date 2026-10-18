import CoprimeRemainderSlack

/-! Kernel-checked examples and axiom reports for CoprimeRemainderSlack. -/

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

-- Example 1: On `s = (2, 6, 2)`, at `m = 2` (`blockSteps s 2 = 8`),
-- `coprimeRemainder` is `3^6 + 2^6 = 793`, and the tail budget requires
-- `2^3 * 793 = 6344 < 6561 = 3^8` (leaving only `6561 - 6344 = 217` of slack!).
-- If a third block `s_2 = 2` is followed by any `m = 3` block, `coprimeRemainder s 3 = 7393`,
-- and `2^3 * 7393 = 59144 > 59049 = 3^10`, violating `tail_budget_of_validCompanionUpTo`!
def seq2_6_2 : ℕ → ℕ
  | 0 => 2
  | 1 => 6
  | 2 => 2
  | _ => 6

example :
    coprimeRemainder seq2_6_2 2 = 793 ∧
    2 ^ (seq2_6_2 0 + 1) * coprimeRemainder seq2_6_2 2 <
      3 ^ (blockSteps seq2_6_2 2) ∧
    coprimeRemainder seq2_6_2 3 = 7393 ∧
    ¬ (2 ^ (seq2_6_2 0 + 1) * coprimeRemainder seq2_6_2 3 <
        3 ^ (blockSteps seq2_6_2 3)) := by
  decide

/-- Consequently, no starting integer `a_0` can realize a 4-block chain starting
with `(2, 6, 2, s_3)` and survive through step `blockSteps seq2_6_2 3 + seq2_6_2 3`! -/
theorem no_companion_for_seq2_6_2 (a_0 : ℕ) (u : ℕ → ℕ)
    (hchain : ValidBlockChain a_0 seq2_6_2 u 4) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps seq2_6_2 3 + seq2_6_2 3) := by
  rintro ⟨ξ, hξ⟩
  have hbudget := tail_budget_of_validCompanionUpTo (m := 3) (by decide : 3 < 4) hchain hξ
  revert hbudget
  decide

#print axioms Mahler.CoprimeSlack.coprime_quotient_m_step_identity
#print axioms Mahler.CoprimeSlack.coprimeRemainder_add_two_pow_le
#print axioms Mahler.CoprimeSlack.coprimeRemainder_lt_three_pow
#print axioms Mahler.CoprimeSlack.unconditional_u0_div_mod_recovery
#print axioms Mahler.CoprimeSlack.archimedean_slack_addition_identity
#print axioms Mahler.CoprimeSlack.tail_budget_iff_archimedean_cap
#print axioms Mahler.CoprimeSlack.tail_budget_of_validCompanionUpTo
#print axioms no_companion_for_seq2_6_2
