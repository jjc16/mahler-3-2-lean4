import DubickasConfinementAndComplexityExtension

/-!
# Verification Checks for `DubickasConfinementAndComplexityExtension`
-/

namespace Mahler.DubickasExtension.Checks

open Mahler
open Mahler.ShiftSlack
open Mahler.EndpointAndBalancedExclusion
open Mahler.DubickasExtension

-- 1. Verify exact fractional formula and repeated-window exponential bound for shifted carry words
example (ξ θ : ℝ) (n : ℕ) :
    (dubCarry ξ θ n : ℝ) = 3 * dubY ξ θ n - 2 * dubY ξ θ (n + 1) - θ :=
  dubCarry_eq_fract_linear ξ θ n

example {ξ θ : ℝ} {W i j L : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hi2 : 2 ≤ i) (hij : i < j)
    (hmatch : ∀ t < L, dubCarry ξ θ (i + t) = dubCarry ξ θ (j + t)) :
    2 ^ (L + j) < 3 ^ j * 2 ^ W :=
  dubX_repeated_window_exp_bound hξ1 hξW hθ_lo hθ_hi hi2 hij hmatch

-- 2. Verify sharp log(2)/log(3/2) sub-critical complexity exclusion for shifted carry words
example {ξ θ kappa C_0 : ℝ} {C : ℕ → ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ)) :
    ¬ (∀ L_min : ℕ, ∃ L ≥ L_min,
      prefixFactorCount (shiftSeq (dubCarryNat ξ θ) 2) L (C L) ≤ C L ∧
        (C L : ℝ) ≤ kappa * (L : ℝ) + C_0) :=
  no_subcritical_log_threshold_dubCarry hξ1 hθ_lo hθ_hi hC0 hlog

-- 3. Verify explicit O(W) and infinite-horizon escape for [0, 1/5) U [4/5, 1), [1/6, 13/24), and Dubickas (2008) closed union
example {ξ : ℝ} {W : ℕ} (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    (∃ n ≤ W + 5,
      (1 / 5 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) ∧
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (4 / 5 : ℝ)) ∧
    (∃ n ≤ W + 15,
      Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (1 / 6 : ℝ) ∨
        (13 / 24 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n)) ∧
    (∃ n ≤ 3 * W + 19,
      ¬ InDubickas2008ClosedUnion (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) :=
  ⟨nearest_int_fifth_explicit_escape hξ1 hξW,
    window_three_eighths_explicit_escape hξ1 hξW,
    dubickas2008_closed_union_explicit_escape hξ1 hξW⟩

example {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    (∃ n ≥ N_0,
      (1 / 5 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) ∧
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (4 / 5 : ℝ)) ∧
    (∃ n ≥ N_0,
      Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (1 / 6 : ℝ) ∨
        (13 / 24 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n)) ∧
    (∃ n ≥ N_0,
      ¬ InDubickas2008ClosedUnion (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) :=
  ⟨nearest_int_fifth_infinite_escape hξ N_0,
    window_three_eighths_infinite_escape hξ N_0,
    dubickas2008_closed_union_infinite_escape hξ N_0⟩

-- 4. Verify unconditional shifted 1/3-window escape (Dubickas 2009 Theorem 1 for 3/2), floor residue non-stabilization for m >= 3, and general-base p/q carry cancellation
example {ξ s : ℝ} {W : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hs0 : 0 ≤ s) (hs23 : s ≤ (2 / 3 : ℝ)) :
    (∃ n ≤ 5 * W + 14, (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n - s)) ∧
      (∃ n ≤ 5 * W + 14,
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < s ∨
          s + (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n)) :=
  shifted_third_unconditional_explicit_escape hξ1 hξW hs0 hs23

example {m : ℕ} (hm3 : 3 ≤ m) {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ n ≥ N_0,
      ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) ≠ ⌊ξ * (3 / 2 : ℝ) ^ N_0⌋ % (m : ℤ) :=
  (floor_mod_non_stabilization_of_three_le hm3).2 hξ N_0

#print axioms Mahler.DubickasExtension.prefixFactorCount_succ_le_of_no_bispecial
#print axioms Mahler.DubickasExtension.prefixFactorCount_le_add_one_of_no_bispecial
#print axioms Mahler.DubickasExtension.dubCarryNat_shifted_third_prefixFactorCount_le
#print axioms Mahler.DubickasExtension.shifted_third_unconditional_explicit_escape
#print axioms Mahler.DubickasExtension.shifted_third_unconditional_infinite_escape
#print axioms Mahler.DubickasExtension.floor_emod_eq_iff_fract_div_mem_cell
#print axioms Mahler.DubickasExtension.floor_mod_non_stabilization_of_three_le
#print axioms Mahler.DubickasExtension.dubickas2008_four_cycle_two_pow_dvd
#print axioms Mahler.DubickasExtension.dubBaseX_multi_step_carry_identity
#print axioms Mahler.DubickasExtension.dubBaseX_repeat_factor_cancellation
#print axioms Mahler.DubickasExtension.dubBaseX_repeated_window_exp_and_power_cutoff

#print axioms Mahler.DubickasExtension.dubCarry_eq_fract_linear
#print axioms Mahler.DubickasExtension.dubX_multi_step_carry_identity
#print axioms Mahler.DubickasExtension.dubY_multi_step_carry_identity
#print axioms Mahler.DubickasExtension.dubX_repeat_factor_cancellation
#print axioms Mahler.DubickasExtension.dubX_strict_step_growth
#print axioms Mahler.DubickasExtension.dubX_repeated_window_exp_bound
#print axioms Mahler.DubickasExtension.dubX_repeated_window_pq_cutoff
#print axioms Mahler.DubickasExtension.dubCarry_subcritical_pq_finite_cutoff
#print axioms Mahler.DubickasExtension.no_subcritical_log_threshold_dubCarry
#print axioms Mahler.DubickasExtension.dubCarry_shifted_third_mem_zero_one
#print axioms Mahler.DubickasExtension.dubCarry_shifted_third_no_bispecial_pair
#print axioms Mahler.DubickasExtension.shifted_third_sturmian_explicit_escape_bound
#print axioms Mahler.DubickasExtension.nearest_int_fifth_explicit_escape
#print axioms Mahler.DubickasExtension.nearest_int_fifth_infinite_escape
#print axioms Mahler.DubickasExtension.window_three_eighths_carry_period_three
#print axioms Mahler.DubickasExtension.window_three_eighths_explicit_escape
#print axioms Mahler.DubickasExtension.window_three_eighths_infinite_escape
#print axioms Mahler.DubickasExtension.dubickas2008_open_union_explicit_escape
#print axioms Mahler.DubickasExtension.dubickas2008_closed_union_explicit_escape
#print axioms Mahler.DubickasExtension.dubickas2008_closed_union_infinite_escape

end Mahler.DubickasExtension.Checks
