import EscapeBranchTwoCap

/-! Kernel-checked examples and axiom reports for EscapeBranchTwoCap. -/

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

-- Example 1: For `a_0 = 265 = 9 + 2^8` taking Escape Branch 2 at `T = 8`,
-- `orbit 265 8 = 6804 = 2^2 * 1701` (`Δs = 2` extra even steps, `w = 1701`),
-- so step `8 + 2 = 10` is `3^2 * 1701 = 15309` (odd!), and any further extra
-- even steps `Δs ≥ 3` would violate `2^(8 + Δs + 1) * w < 3^8 * (2 * 265 + 1)`.
example :
    orbit 265 8 = 2 ^ 2 * 1701 ∧
    orbit 265 10 = 3 ^ 2 * 1701 ∧
    2 ^ (8 + 2 + 1) * 1701 < 3 ^ 8 * (2 * 265 + 1) := by
  decide

-- Example 2: For `a_0 = 9` at block `k = 1` (`T_1 = 2`, `2 * a_0 + 1 = 19`),
-- the `3^(s-1)`-cancellation cap requires `2^(2 + s_1 + 1) < 3^3 * 19 = 513`,
-- i.e. `2^(s_1 + 3) < 513`, which caps `s_1 ≤ 6` (`2^9 = 512 < 513`, while `s_1 = 7` gives `1024 > 513`)!
-- Combined with `6 ≤ s_1` from Bridge 2 (`s_eq_two_forces_next_block_ge_six`),
-- this pins `s_1 = 6` for `a_0 = 9` uniquely from above and below!
example :
    2 ^ (2 + 6 + 1) < 3 ^ (2 + 1) * (2 * 9 + 1) ∧
    ¬ (2 ^ (2 + 7 + 1) < 3 ^ (2 + 1) * (2 * 9 + 1)) := by
  decide

#print axioms Mahler.EscapeBranchCap.unique_window_of_mem
#print axioms Mahler.EscapeBranchCap.windowLow_caps_block_length
#print axioms Mahler.EscapeBranchCap.block_length_archimedean_cap
#print axioms Mahler.EscapeBranchCap.escape_branch_two_extra_steps_cap
