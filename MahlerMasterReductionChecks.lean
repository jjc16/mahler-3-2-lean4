import MahlerMasterReduction

/-! Kernel-checked examples and axiom reports for MahlerMasterReduction. -/

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

-- Example 1: For `a_0 = 9`, `s_0 = 2` and `3 * 9 + 1 = 28 = 4 * 7`, so `u_0 = 7`,
-- which satisfies the Level-2 phase-lock condition `u_0 % 64 = 7`!
-- Whereas for `a_0 = 25` (`25 % 8 = 1`, `s_0 = 2`), `3 * 25 + 1 = 76 = 4 * 19`,
-- so `u_0 = 19 % 64 ≠ 7` (a Level-2 Phase-Lock Rupture!).
example :
    (3 * 9 + 1) / 4 % 64 = 7 ∧
    (3 * 25 + 1) / 4 % 64 = 19 ∧
    (3 * 25 + 1) / 4 % 64 ≠ 7 := by
  decide

#print axioms Mahler.MasterReduction.six_le_s_iff_u_mod_64_eq_7
#print axioms Mahler.MasterReduction.level_two_phase_lock_of_s_eq_two
#print axioms Mahler.MasterReduction.no_infinite_companion_of_phase_lock_rupture
#print axioms Mahler.MasterReduction.mahler_framework_master_synthesis
