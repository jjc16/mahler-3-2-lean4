import ModEightPhaseClassifier

/-! Kernel-checked examples and axiom reports for ModEightPhaseClassifier. -/

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

-- Example 1: On `a_0 = 149`, blocks k = 0, 1, 2, 3 all have even `s_k` (`6, 4, 4, 8`)
-- and `s_{k+1} ≥ 4 ≥ 3`, so `three_le_next_block_iff_mod_eight` forces every
-- single one of `u_0, u_1, u_2, u_3` (`7, 319, 1615, 511`) to equal `7 (mod 8)`!
private def s149 : ℕ → ℕ
  | 0 => 6 | 1 => 4 | 2 => 4 | 3 => 8 | 4 => 5 | _ => 1

private def u149 : ℕ → ℕ
  | 0 => 7 | 1 => 319 | 2 => 1615 | 3 => 511 | 4 => 104771 | _ => 12729677

example :
    u149 0 % 8 = 7 ∧
    u149 1 % 8 = 7 ∧
    u149 2 % 8 = 7 ∧
    u149 3 % 8 = 7 := by
  decide

-- Example 2: Verify the Memoryless 3-adic Erasure Law `(2^s(k+1) * u(k+1)) % 3^s(k) = 1`
-- across all 4 transitions of `a_0 = 149`:
example :
    (2 ^ (s149 1) * u149 1) % 3 ^ (s149 0) = 1 ∧
    (2 ^ (s149 2) * u149 2) % 3 ^ (s149 1) = 1 ∧
    (2 ^ (s149 3) * u149 3) % 3 ^ (s149 2) = 1 ∧
    (2 ^ (s149 4) * u149 4) % 3 ^ (s149 3) = 1 := by
  decide

#print axioms Mahler.ModEightClassifier.three_pow_mod_eight
#print axioms Mahler.ModEightClassifier.s_eq_two_iff_mod_eight
#print axioms Mahler.ModEightClassifier.three_le_s_iff_mod_eight
#print axioms Mahler.ModEightClassifier.three_le_next_block_iff_mod_eight
#print axioms Mahler.ModEightClassifier.mod_eight_trap_forces_mod_256_eq_28
#print axioms Mahler.ModEightClassifier.memoryless_mod_three_pow_erasure
