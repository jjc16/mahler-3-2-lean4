import ZeroLiftCoasting

/-! Kernel-checked examples and axiom reports for ZeroLiftCoasting. -/

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

-- Example 1: `a_0 = 149` has `W = 8` bits (`149 < 2^8 = 256`).
-- At step `W = 8`, `orbit 149 8 = 3848 < 6561 = 3^8` (`orbit_at_bit_length_lt_three_pow`).
-- After running out of bits at `W = 8`, `149` coasts through returns `T_2 = 10`,
-- `T_3 = 14`, `T_4 = 22` with `jumpQuotient = 0` until `T_5 = 27`, where
-- `orbit 149 27 = 8486451 ≡ 3 (mod 4)` kills it at step `27 + 2 = 29`!
private def s149 : ℕ → ℕ
  | 0 => 6 | 1 => 4 | 2 => 4 | 3 => 8 | 4 => 5 | _ => 1

example :
    149 < 2 ^ 8 ∧
    orbit 149 8 = 3828 ∧
    3828 < 3 ^ 8 ∧
    jumpQuotient 149 s149 2 = 0 ∧
    jumpQuotient 149 s149 3 = 0 ∧
    jumpQuotient 149 s149 4 = 0 ∧
    orbit 149 (blockSteps s149 5) % 4 = 3 := by
  decide

#print axioms Mahler.Coasting.orbit_at_bit_length_lt_three_pow
#print axioms Mahler.Coasting.coasting_residue_eq_self
#print axioms Mahler.Coasting.coasting_jumpQuotient_eq_zero
#print axioms Mahler.Coasting.coasting_coprime_quotient_bound
#print axioms Mahler.Coasting.coasting_mod_four_eq_three_impossible
