import CoprimeQuotientPhaseLock

/-! Kernel-checked examples and axiom reports for CoprimeQuotientPhaseLock. -/

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

-- Example 1: On the 28-step survivor `a_0 = 149`, trace its 5 blocks:
-- k=0: s_0 = 6 (even), u_0 = 7   (7 % 4 = 3: phase-locked!)
-- k=1: s_1 = 4 (even), u_1 = 319 (319 % 4 = 3: phase-locked!)
-- k=2: s_2 = 4 (even), u_2 = 1615 (1615 % 4 = 3: phase-locked!)
-- k=3: s_3 = 8 (even), u_3 = 511 (511 % 4 = 3: phase-locked!)
-- k=4: s_4 = 5 (ODD!), u_4 = 104771 (104771 % 4 = 3: PHASE-LOCK RUPTURE!)
def s149 : ℕ → ℕ
  | 0 => 6 | 1 => 4 | 2 => 4 | 3 => 8 | 4 => 5 | _ => 1

def u149 : ℕ → ℕ
  | 0 => 7 | 1 => 319 | 2 => 1615 | 3 => 511 | 4 => 104771 | _ => 12729677

private theorem chain149 : ValidBlockChain 149 s149 u149 6 := by
  intro k hk
  have hfin : ∀ j : Fin 6,
      1 ≤ s149 j.val ∧
      u149 j.val % 2 = 1 ∧
      3 * orbit 149 (blockSteps s149 j.val) + 1 =
        2 ^ (s149 j.val) * u149 j.val := by
    decide
  exact hfin ⟨k, hk⟩

-- Phase-lock rupture at k = 4 (`s149 4 = 5` is odd and `u149 4 = 104771 ≡ 3 mod 4`)
-- immediately certifies via `no_companion_of_phase_lock_rupture` that `a_0 = 149`
-- cannot survive to step `blockSteps s149 5 + 2 = 27 + 2 = 29`!
example : ¬ ∃ ξ : ℝ, ValidCompanionUpTo 149 ξ 29 := by
  have h29 : blockSteps s149 (4 + 1) + 2 = 29 := by decide
  rw [← h29]
  exact no_companion_of_phase_lock_rupture (k := 4) (by decide : 4 + 1 < 6)
    chain149 (Or.inr ⟨by decide, by decide⟩)

#print axioms Mahler.PhaseLock.odd_quotient_mod_six
#print axioms Mahler.PhaseLock.coprime_quotient_recurrence
#print axioms Mahler.PhaseLock.three_even_pow_mul_add_one_mod_eight
#print axioms Mahler.PhaseLock.parity_mod_four_phase_lock_iff
#print axioms Mahler.PhaseLock.phase_lock_of_survives_next_block
#print axioms Mahler.PhaseLock.no_companion_of_phase_lock_rupture
#print axioms Mahler.PhaseLock.compressed_real_iterate_identity
#print axioms Mahler.PhaseLock.compressed_real_approximation_bounds
