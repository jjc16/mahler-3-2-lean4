import KernelFactorizationDuality

/-! Kernel-checked examples and axiom reports for KernelFactorizationDuality. -/

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

-- Example 1: On `a_0 = 149` (`s = [6, 4, 4, 8, 5]`, `u = [7, 319, 1615, 511, 104771]`):
-- At `m = 3` (`s 3 = 8`, `blockSteps s 3 = 14`, `blockSteps s 4 = 22`, `u 3 = 511`):
-- - `blockKernel s 4 = 3^7 * kernelQuotient s 3` (`11595913587 = 2187 * 5302201`),
-- - `2 * kernelQuotient s 3 + integerSlack s 3 = 3^15` (`2 * 5302201 + 3744505 = 14348907`),
-- - `(2^22 * 511) / 3^15 = 149` and `(2^22 * 511) % 3^15 = 5302201 = kernelQuotient s 3`!
private def s149 : ℕ → ℕ
  | 0 => 6 | 1 => 4 | 2 => 4 | 3 => 8 | 4 => 5 | _ => 1

example :
    kernelQuotient s149 3 = 5302201 ∧
    blockKernel s149 4 = 3 ^ 7 * kernelQuotient s149 3 ∧
    2 * (kernelQuotient s149 3 : ℤ) + integerSlack s149 3 = 3 ^ 15 ∧
    (2 ^ 22 * 511) / 3 ^ 15 = 149 ∧
    (2 ^ 22 * 511) % 3 ^ 15 = kernelQuotient s149 3 := by
  decide

#print axioms Mahler.KernelDuality.blockKernel_succ_eq_three_pow_mul
#print axioms Mahler.KernelDuality.coprimeRemainder_mod_three_ne_zero
#print axioms Mahler.KernelDuality.kernelQuotient_not_three_dvd
#print axioms Mahler.KernelDuality.blockKernel_three_pow_valuation
#print axioms Mahler.KernelDuality.two_mul_kernelQuotient_add_slack
#print axioms Mahler.KernelDuality.two_pow_mul_u_eq_a0_add_kernelQuotient
#print axioms Mahler.KernelDuality.a0_and_kernelQuotient_div_mod_recovery
