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

-- 5. Verify full general-base Dubickas (2009) Theorem 1 for 1 < q < p < q^2, open-regime p >= 2q cell escape, and 7/12 union escape
example {p q : ℕ} {s : ℝ}
    (hq2 : 2 ≤ q) (hqp : q < p) (hpq2 : p < q ^ 2) (hcop_pq : Nat.Coprime p q)
    (hs0 : 0 ≤ s) (hs_hi : s + 1 / (p : ℝ) ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ n ≥ N_0,
      Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) < s ∨
        s + 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) :=
  (dubickas2009_general_base_explicit_and_infinite_escape hq2 hqp hpq2 hcop_pq hs0 hs_hi).2 hξ N_0

example {ξ : ℝ} {W : ℕ} (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    ∃ n ≤ W + 12, ¬ InUnionSevenTwelfths (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) :=
  union_seven_twelfths_explicit_and_infinite_escape.1 hξ1 hξW

-- 6. Verify general-base log threshold, linear-in-W Dubickas (2009) escape, Base 4/3 [1/3, 5/8) escape, and 2/3 & 25/36 unions
example {p q : ℕ} {kappa : ℝ}
    (hq2 : 2 ≤ q) (hqp : q < p)
    (hlog : kappa * Real.log ((p : ℝ) / (q : ℝ)) < Real.log (q : ℝ)) :
    ∃ a b : ℕ, 1 ≤ b ∧ p ^ b < q ^ (a + b) ∧ (a : ℝ) * kappa < (b : ℝ) :=
  exists_ab_of_lt_general_log_threshold hq2 hqp hlog

example {ξ : ℝ} {W : ℕ} (hξ8 : (8 : ℝ) ≤ ξ) (hξW : ξ < (3 : ℝ) ^ W) :
    ∃ n ≤ W + 8,
      Int.fract (ξ * (4 / 3 : ℝ) ^ n) < (1 / 3 : ℝ) ∨
        (5 / 8 : ℝ) ≤ Int.fract (ξ * (4 / 3 : ℝ) ^ n) :=
  base_four_three_beyond_quarter_explicit_and_infinite_escape.1 hξ8 hξW

example {ξ : ℝ} {W : ℕ} (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    (∃ n ≤ W + 14, ¬ InUnionTwoThirds (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) ∧
    (∃ n ≤ W + 16, ¬ InUnionTwentyFiveThirtySixths (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) :=
  ⟨union_two_thirds_explicit_and_infinite_escape.1 hξ1 hξW,
    union_twenty_five_thirty_sixths_explicit_and_infinite_escape.1 hξ1 hξW⟩

#print axioms Mahler.DubickasExtension.exists_ab_of_lt_general_log_threshold
#print axioms Mahler.DubickasExtension.no_subcritical_general_log_threshold_dubBaseCarry
#print axioms Mahler.DubickasExtension.dubickas2009_general_base_linear_in_W_escape
#print axioms Mahler.DubickasExtension.base_four_three_carry_period_two
#print axioms Mahler.DubickasExtension.base_four_three_beyond_quarter_explicit_and_infinite_escape
#print axioms Mahler.DubickasExtension.inRatIntervalList_next_of_forwardStepOk
#print axioms Mahler.DubickasExtension.union_two_thirds_explicit_and_infinite_escape
#print axioms Mahler.DubickasExtension.union_twenty_five_thirty_sixths_explicit_and_infinite_escape

-- 7. Verify Thue-Morse Cantor cascade and general g-rung window ladder & valuation lock
example :
    tmCascadeEntry 5 < (2 / 7 : ℝ) ∧ (2 / 7 : ℝ) < tmCascadeEntry 4 :=
  ⟨tmCascadeEntry_explicit_values_and_two_sevenths_cutoff.2.2.2.2.2.2.2.1,
    tmCascadeEntry_explicit_values_and_two_sevenths_cutoff.2.2.2.2.2.2.2.2⟩

example {g : ℕ} (hg : 3 ≤ g) :
    (1 / 3 : ℝ) < rungAlpha g ∧ rungAlpha g < rungBeta g ∧ rungBeta g < (1 / 2 : ℝ) :=
  ⟨(rungAlpha_lt_rungBeta_lt_half hg).1,
    (rungAlpha_lt_rungBeta_lt_half hg).2.1,
    (rungAlpha_lt_rungBeta_lt_half hg).2.2.1⟩

#print axioms Mahler.DubickasExtension.tmCascadeCarryAcc_mahlerProd_identity
#print axioms Mahler.DubickasExtension.tmCascadeEntry_closed_form
#print axioms Mahler.DubickasExtension.tmCascadeEntry_step_ratio_and_strictAnti
#print axioms Mahler.DubickasExtension.tmCascadeEntry_explicit_values_and_two_sevenths_cutoff
#print axioms Mahler.DubickasExtension.tmCascade_periodic_orbit_two_pow_dvd
#print axioms Mahler.DubickasExtension.cantorTwoSevenths_matches_mahlerBinaryPartition_up_to_15_and_splits_at_16
#print axioms Mahler.DubickasExtension.rungAlpha_lt_rungBeta_lt_half
#print axioms Mahler.DubickasExtension.gap_ladder_short_gap_cost_and_cap
#print axioms Mahler.DubickasExtension.general_rung_first_defect_valuation_lock

-- 8. Verify punctured [8/57, 1/2) homoclinic catapult trap and phase transition
example {ξ : ℝ} {W : ℕ} (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    (∃ n ≤ W + 8,
      Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (4 / 27 : ℝ) ∨
        (1 / 2 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n)) ∧
    (∃ n ≤ 3 * W + 20,
      Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (8 / 57 : ℝ) ∨
        (1 / 2 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n)) :=
  ⟨punctured_four_twenty_sevenths_period_three_lock_and_escape.2.1 hξ1 hξW,
    punctured_eight_fifty_sevenths_explicit_and_infinite_escape.1 hξ1 hξW⟩

#print axioms Mahler.DubickasExtension.punctured_half_step_dichotomy_and_forbidden_short_gaps
#print axioms Mahler.DubickasExtension.punctured_four_twenty_sevenths_period_three_lock_and_escape
#print axioms Mahler.DubickasExtension.punctured_eight_fifty_sevenths_catapult_and_absorbing_trap
#print axioms Mahler.DubickasExtension.punctured_eight_fifty_sevenths_explicit_and_infinite_escape
#print axioms Mahler.DubickasExtension.homoclinicCycleMin_closed_form_and_strictMono
#print axioms Mahler.DubickasExtension.cantorPuncturedHalf_phase_transition_counts

-- 9. Verify universal rung-g catapult staircase and leak-free inductive elevator
example {G : ℕ} {z : ℕ → ℝ} {s : ℕ → ℕ}
    (hG : 3 ≤ G) (helev : ValidLeakFreeElevator G z s) :
    (∀ m : ℕ, 1 ≤ m → z m ≤ z (m + 1)) ∧ (∀ m : ℕ, s (m + 1) ≤ s m) :=
  ⟨(leak_free_inductive_elevator_monotone_rung_descent hG helev).2.1,
    (leak_free_inductive_elevator_monotone_rung_descent hG helev).2.2⟩

#print axioms Mahler.DubickasExtension.rungCatapult_ordering_and_corridor_overlap
#print axioms Mahler.DubickasExtension.universal_rung_catapult_and_upward_expansion
#print axioms Mahler.DubickasExtension.leak_free_inductive_elevator_monotone_rung_descent

-- 10. Verify self-cleaning leak-window death bands and 7-step catapult-death trap
example :
    rungCleanedMeasure 3 (8 / 57 : ℝ) / rungLeakWidth 3 = (18 / 19 : ℝ) ∧
    rungResidualLeakMeasure 3 (8 / 57 : ℝ) = (32 / 9747 : ℝ) :=
  ⟨rungDeathBand_step_and_measure_decomposition.2.2.2,
    rungDeathBand_step_and_measure_decomposition.2.2.1⟩

#print axioms Mahler.DubickasExtension.rungDeathBand_step_and_measure_decomposition
#print axioms Mahler.DubickasExtension.catapult_into_death_band_seven_step_escape

-- 11. Verify higher-order gap bijection and 2059 leak-threading survivor lock
example :
    1 - rungCleanedMeasure 3 (8 / 57 : ℝ) / rungLeakWidth 3 = (1 / 19 : ℝ) ∧
    ((2 : ℤ) ^ 7 ∣ (2059 * 56 + 280)) ∧
    ((2 : ℤ) ^ 14 ∣ (2059 * 1464 + 280)) ∧
    ((2 : ℤ) ^ 21 ∣ (2059 * 1443256 + 280)) :=
  ⟨rungDeathGap_maps_onto_catapult_zone.2.1,
    homoclinic_seven_cycle_in_gap_and_divisibility_lock.2.2⟩

#print axioms Mahler.DubickasExtension.rungDeathGap_maps_onto_catapult_zone
#print axioms Mahler.DubickasExtension.homoclinic_seven_cycle_in_gap_and_divisibility_lock

-- 12. Verify universal homoclinic lock family and multi-defect simultaneous valuation locks
example :
    (homoclinicCycleNum 2 = 8072 ∧ homoclinicCycleDen 2 = 58025) ∧
    (homoclinicCycleNum 3 = 222040 ∧ homoclinicCycleDen 3 = 1586131) :=
  ⟨homoclinic_family_cycle_divisibility_lock.2.1.2.1,
    homoclinic_family_cycle_divisibility_lock.2.1.2.2⟩

#print axioms Mahler.DubickasExtension.homoclinic_family_cycle_divisibility_lock
#print axioms Mahler.DubickasExtension.rungAffInv_general_defect_step_identity
#print axioms Mahler.DubickasExtension.exactTwoPowLock_incompatible_of_ne
#print axioms Mahler.DubickasExtension.general_rung_two_defect_simultaneous_lock

-- 13. Verify Sections 17-19: Two-island punctured [0, 1/2), 17/24 > 70% union, and K-defect tower
example {ξ : ℝ} {W : ℕ} (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    (∃ n ≤ 3 * W + 27, ¬ InTwoIslandPuncturedHalf (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) ∧
    (∃ n ≤ W + 17, ¬ InUnionSeventeenTwentyFourths (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) :=
  ⟨two_island_punctured_half_explicit_and_infinite_escape.2.1 hξ1 hξW,
    union_seventeen_twenty_fourths_explicit_and_infinite_escape.1 hξ1 hξW⟩

#print axioms Mahler.DubickasExtension.two_island_punctured_half_explicit_and_infinite_escape
#print axioms Mahler.DubickasExtension.inRatIntervalList_terminal_of_selfFunnelChainOk
#print axioms Mahler.DubickasExtension.union_seventeen_twenty_fourths_explicit_and_infinite_escape
#print axioms Mahler.DubickasExtension.rungDefectCocycle_tower_identity
#print axioms Mahler.DubickasExtension.general_rung_multi_defect_valuation_tower

-- 14. Verify Section 20: k-block defect spacing law and (3, 3k+4) Perron-Fibonacci hierarchy in the Cantor dust
example {k : ℕ} {z : ℝ} (hk : 1 ≤ k) (hz : homoclinicCycleMin k ≤ z) :
    homoclinicCycleMin k ≤ rungReturnMapIter 3 k (rungReturnMap 4 z) :=
  (cantor_dust_minimum_defect_spacing_law hk hz).1

#print axioms Mahler.DubickasExtension.cantor_dust_minimum_defect_spacing_law
#print axioms Mahler.DubickasExtension.punctured_eps1_forced_seven_step_macro_block
#print axioms Mahler.DubickasExtension.cantorDust_perron_fibonacci_counts
#print axioms Mahler.DubickasExtension.perronCharPoly_sign_change_and_root_squeeze

-- 15. Verify Section 21: Universal catapult-death band ladder and homoclinic tangency
example (m : ℕ) :
    catapultDeathHi m (homoclinicCycleMin m) = homoclinicCycleMin m :=
  (universal_catapult_death_band_ladder.1 m (homoclinicCycleMin m) 0).2.2.2.1

#print axioms Mahler.DubickasExtension.universal_catapult_death_band_ladder

-- 16. Verify Section 22: Defect-to-defect quotient recurrence, mod-8 lock, and sparse-defect descent
#print axioms Mahler.DubickasExtension.punctured_eight_eighty_firsts_forbids_four_zeros_and_short_gaps
#print axioms Mahler.DubickasExtension.cantor_dust_defect_to_defect_quotient_recurrence
#print axioms Mahler.DubickasExtension.cantor_dust_mod_eight_lock_and_sparse_descent
#print axioms Mahler.DubickasExtension.no_infinite_sparse_defect_cantor_dust_chain

-- 17. Verify Section 23: 3-adic valuation v_3(U_r)=2, non-stationarity V_2 != V_1, and cumulative-epoch exclusion
#print axioms Mahler.DubickasExtension.three_pow_ne_two_pow_add_one_of_four_le
#print axioms Mahler.DubickasExtension.cantor_dust_three_adic_valuation_and_normalized_recurrence
#print axioms Mahler.DubickasExtension.cantor_dust_multi_step_telescoping_and_epoch_descent
#print axioms Mahler.DubickasExtension.no_infinite_cumulative_sparse_epoch_cantor_dust_chain

#print axioms Mahler.DubickasExtension.dubBaseCarry_eq_fract_linear
#print axioms Mahler.DubickasExtension.dubBaseY_multi_step_carry_identity
#print axioms Mahler.DubickasExtension.dubBaseCarry_mem_two_letters
#print axioms Mahler.DubickasExtension.dubBaseCarry_no_bispecial_pair
#print axioms Mahler.DubickasExtension.dubBaseCarryNat_prefixFactorCount_le
#print axioms Mahler.DubickasExtension.dubickas2009_general_base_explicit_and_infinite_escape
#print axioms Mahler.DubickasExtension.general_base_non_straddling_cell_escape
#print axioms Mahler.DubickasExtension.general_base_floor_mod_non_stabilization
#print axioms Mahler.DubickasExtension.inRatIntervalList_next_of_funnelStepOk
#print axioms Mahler.DubickasExtension.inRatIntervalList_terminal_of_funnelChainOk
#print axioms Mahler.DubickasExtension.union_seven_twelfths_explicit_and_infinite_escape

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
