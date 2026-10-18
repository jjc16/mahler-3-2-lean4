import FormulationBHighBitJump

/-! Kernel-checked examples and axiom reports for FormulationBHighBitJump. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB

-- Example 1: At step 8, `r_2 = 9` has `orbit 9 8 = 243`, so `3 * 243 + 1 = 730 = 2 * 365`
-- (`v_2 = 1`), which fails at step 10 (`survivesSteps 9 10 = false`), while `265 = 9 + 2^8`
-- survives step 10!
example :
    orbit 9 8 = 243 ∧
    survivesSteps 9 10 = false ∧
    survivesSteps 265 10 = true := by
  decide

-- Example 2: Any `a_0` with `a_0 % 8 = 1` surviving 10 steps satisfies `265 ≤ a_0`.
example {a_0 : ℕ} (h8 : a_0 % 8 = 1)
    (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ 10) :
    265 ≤ a_0 :=
  s_eq_two_survives_ten_forces_ge_265 h8 hsurv

#print axioms Mahler.FormulationB.block_chain_mod_two_pow_eq
#print axioms Mahler.FormulationB.block_residue_odd_and_pos
#print axioms Mahler.FormulationB.residue_high_bit_jump_of_not_two_pow_dvd
#print axioms Mahler.FormulationB.block_high_bit_jump_of_zero_lift_mismatch
#print axioms Mahler.FormulationB.high_bit_jump_of_zero_lift_fails
#print axioms Mahler.FormulationB.not_survives_of_lt_two_pow_and_zero_lift_fails
#print axioms Mahler.FormulationB.s_eq_two_survives_ten_forces_ge_265
