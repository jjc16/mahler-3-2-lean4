import OddBlockCoupling

/-! Kernel-checked examples and axiom reports for OddBlockCoupling. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock

-- Example 1: a = 53 has 3*53 + 1 = 160 = 2^5 * 5 (s = 5, u = 5).
-- Its next odd integer is at step 5: orbit 53 5 = 3^4 * 5 = 405, with v_3(405) = 4.
example : orbit 53 5 = 405 ∧ 3 ^ 4 ∣ orbit 53 5 ∧ ¬ (3 ^ 5 ∣ orbit 53 5) :=
  ⟨by decide, (odd_block_three_pow_valuation (a := 53) (s := 5) (u := 5) (by decide) (by decide)).1,
    (odd_block_three_pow_valuation (a := 53) (s := 5) (u := 5) (by decide) (by decide)).2⟩

-- Example 2: a = 9 has a % 8 = 1 (s = 2) and survives 8 steps, whereas a = 137 fails at step 8.
example : survivesSteps 9 8 = true ∧ survivesSteps 137 8 = false := by decide

#print axioms Mahler.OddBlock.orbit_odd_block_even_interior
#print axioms Mahler.OddBlock.orbit_odd_block_return
#print axioms Mahler.OddBlock.odd_block_three_pow_valuation
#print axioms Mahler.OddBlock.fracPart_odd_block
#print axioms Mahler.OddBlock.s_eq_two_fractional_drain
#print axioms Mahler.OddBlock.exists_validCompanionUpTo_mod_two_pow_iff
#print axioms Mahler.OddBlock.s_eq_two_survives_eight_iff_mod_256_eq_9
