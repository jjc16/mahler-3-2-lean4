import BridgeOneArchimedean

/-! Kernel-checked examples and axiom reports for BridgeOneArchimedean. -/

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne

-- Even though 4096 ≡ 0 (mod 2^12) lands in the 2-adic ghost residue class at N = 12,
-- Bridge 1's Archimedean bound proves that ANY m > 0 surviving 12 steps satisfies 53 ≤ m.
example {m : ℕ} (hm : 0 < m) (h : ∃ ξ : ℝ, ValidCompanionUpTo m ξ 12) :
    53 ≤ m :=
  positive_survivor_step12_ge_53 hm h

-- And `m = 53` genuinely survives 12 steps (in fact through step 24):
example : survivesSteps 53 12 = true := by decide

#print axioms Mahler.BridgeOne.surviving_orbit_half_corridor
#print axioms Mahler.BridgeOne.ghost_branch_forces_two_pow_le
#print axioms Mahler.BridgeOne.positive_survivor_ge_of_residues_excluded
#print axioms Mahler.BridgeOne.survivesSteps_mono_false
#print axioms Mahler.BridgeOne.every_positive_fails_iff_unbounded_exclusion
#print axioms Mahler.BridgeOne.no_positive_infinite_companion_of_unbounded_exclusion
#print axioms Mahler.BridgeOne.positive_survivor_step4_ge_4
#print axioms Mahler.BridgeOne.positive_survivor_step12_ge_53
