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

-- 18. Verify Section 24: Exact 2-adic valuation determinism, mod-16/mod-128 spacing bijections, zero-branching uniqueness, and dual (2,3)-adic CRT renormalization
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_exact_two_adic_valuation_and_forward_uniqueness
#print axioms Mahler.DubickasExtension.three_pow_step_mod_sixteen
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_mod_sixteen_spacing_bijection
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_orbit_unique_of_V0
#print axioms Mahler.DubickasExtension.mod_and_div_of_bezout
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_binary_crt_parametrization
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_cooldown_mod_128_and_three_adic_lock
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_renormalized_k_recurrence

-- 19. Verify Section 25: Level-2 and Level-3 CRT renormalizations, extinction of l_1=0 base witnesses (V_1 >= 94,389,155), and general multi-step homogeneous (2,3)-adic tower law
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_level2_crt_parametrization
#print axioms Mahler.DubickasExtension.le_of_linear_and_div
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_level3_renormalized_l_recurrence_j1_eq_one
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_level3_renormalized_l_recurrence_j1_eq_two
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_multi_step_homogeneous_tower

-- 20. Verify Section 26: Base-3^(3j_1+4) carry-digit identity, backward 2-adic renormalization tree engine, and certified horizon bounds through depth 10 (V_0 >= 7.729e21 > 2^72)
#print axioms Mahler.DubickasExtension.renormalized_three_adic_carry_digit_identity
#print axioms Mahler.DubickasExtension.backward_two_adic_residue_lift_of_stepOk
#print axioms Mahler.DubickasExtension.min_seed_of_certifyBinaryDustTree
#print axioms Mahler.DubickasExtension.binary_cantor_dust_min_seed_of_certifyBinaryDustDepth
#print axioms Mahler.DubickasExtension.binary_cantor_dust_certified_horizon_bounds_up_to_depth_ten

-- 21. Verify Section 27: Universal (2,3)-adic quotient-remainder conservation law, multi-step quotient duality, depth-11/12 binary bounds (V_0 > 2^89), and ternary {1,2,3} tree certification
#print axioms Mahler.DubickasExtension.one_step_quotient_and_remainder_conservation
#print axioms Mahler.DubickasExtension.universal_two_three_adic_quotient_duality
#print axioms Mahler.DubickasExtension.binary_cantor_dust_certified_depth_11_and_12
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_ternary_cooldown_mod_128_sieve
#print axioms Mahler.DubickasExtension.min_seed_of_certifyTernaryDustTree
#print axioms Mahler.DubickasExtension.ternary_cantor_dust_min_seed_of_certifyTernaryDustDepth
#print axioms Mahler.DubickasExtension.ternary_cantor_dust_certified_horizon_bounds_up_to_depth_six

-- 22. Verify Section 28: Single-exponent homogeneous identity, archimedean floor invariant V(0)-1, cyclotomic mod-7/13/19 automata, and 101-bit Mahler Depth-12 bound
#print axioms Mahler.DubickasExtension.defectStepSum_shift_cancellation_and_single_exponent_identity
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_archimedean_floor_invariant
#print axioms Mahler.DubickasExtension.defectNormalizedQuotient_cyclotomic_mod_7_13_19_locks
#print axioms Mahler.DubickasExtension.mahler_min_seed_of_mahlerLeafOk
#print axioms Mahler.DubickasExtension.mahler_binary_cantor_dust_min_seed_of_certifyMahlerBinaryDustDepth
#print axioms Mahler.DubickasExtension.mahler_binary_cantor_dust_certified_bounds_up_to_depth_12

-- 23. Verify Section 29: Dense-core strict doubling growth, repeated defect-subword cancellation 2^E | (V(r_2)-V(r_1)), and unconditional exclusion of low-complexity dense-core trajectories
#print axioms Mahler.DubickasExtension.dense_core_strict_doubling_and_monotonicity
#print axioms Mahler.DubickasExtension.dense_core_repeated_subword_divisibility_and_exp_bound
#print axioms Mahler.DubickasExtension.dense_core_repeated_subword_cutoff_and_complexity_exclusion

-- 24. Verify Section 30: Right-special 2-adic valuation locks, 7-bit spectral gap, symmetric bispecial (2^S, 3^S) resonance, parameterized (p, q) cutoffs, and transcendental 7 log 2 / (10 log(3/2)) complexity exclusion
#print axioms Mahler.DubickasExtension.dense_core_all_V_odd_and_mod_four_divergence
#print axioms Mahler.DubickasExtension.dense_core_right_special_exact_two_adic_valuation_and_spectral_gap
#print axioms Mahler.DubickasExtension.dense_core_symmetric_bispecial_resonance
#print axioms Mahler.DubickasExtension.dense_core_parameterized_pq_cutoff_and_convergents
#print axioms Mahler.DubickasExtension.no_subcritical_log_threshold_dense_core
#print axioms Mahler.DubickasExtension.no_density_weighted_subcritical_log_threshold_dense_core

-- 25. Verify Section 31: Bottom-part remainder invariance and floor conservation, shifted-horizon 98-bit corridor, repeated-window top-part isolation and squeeze, and 3-occurrence ultrametric pigeonhole
#print axioms Mahler.DubickasExtension.bottom_part_remainder_invariance_and_floor_conservation
#print axioms Mahler.DubickasExtension.dense_core_shifted_horizon_floor_and_ninety_eight_bit_corridor
#print axioms Mahler.DubickasExtension.dense_core_repeated_window_top_part_isolation_and_squeeze
#print axioms Mahler.DubickasExtension.dense_core_three_occurrence_ultrametric_pigeonhole

-- 26. Verify Section 32: Infinite (128^d, 2187^d) sieve tower, explicit 4-in-16384 and 8-in-2097152 bijections, and exact prefix-collision biconditional for all horizons
#print axioms Mahler.DubickasExtension.normalizedDefectAcc_master_identity_and_infinite_sieve_tower
#print axioms Mahler.DubickasExtension.dense_core_depth2_four_in_16384_and_depth3_eight_in_2097152_sieves
#print axioms Mahler.DubickasExtension.dense_core_exact_prefix_collision_biconditional_and_mod_cutoff

-- 27. Verify Section 33: Exact normalizedDefectAcc cocycle composition, frozen-remainder stabilization beyond bit W, and return-loop homoclinic denominator syzygy
#print axioms Mahler.DubickasExtension.normalizedDefectAcc_cocycle_composition_law
#print axioms Mahler.DubickasExtension.dense_core_frozen_remainder_and_exact_valuation_conspiracy_law
#print axioms Mahler.DubickasExtension.dense_core_return_loop_homoclinic_denominator_syzygy

-- 28. Verify Section 34: Global origin-to-return syzygy and seed-free two-return-loop compatibility obstruction on {1, 2}^N
#print axioms Mahler.DubickasExtension.dense_core_global_origin_return_loop_syzygy
#print axioms Mahler.DubickasExtension.dense_core_seed_free_two_return_loop_syzygy_and_congruence

-- 29. Verify Section 35: Universal 3-step maximal branching loop spawning, seed-free bit-M_A flip law, and seed-free two-loop 7-bit spectral gap dichotomy
#print axioms Mahler.DubickasExtension.dense_core_every_three_step_window_spawns_maximal_branching_return_loop
#print axioms Mahler.DubickasExtension.dense_core_seed_free_two_loop_bit_flip_and_spectral_gap

-- 30. Verify Section 36: Exact constant-run (2059, 58025) and alternating-run (129009091) valuation locks across every 3-step window
#print axioms Mahler.DubickasExtension.dense_core_constant_run_length_2059_and_58025_valuation_locks
#print axioms Mahler.DubickasExtension.dense_core_alternating_run_129009091_valuation_locks

-- 31. Verify Section 37: Exact run-compression and macro-transition laws (8*2059*V = 3^(7L)*U_1 + 1 and 58025*V = 3^(10L)*U_2 + 8) for all run lengths L = m + 1 >= 1
#print axioms Mahler.DubickasExtension.dense_core_one_run_compression_and_macro_transition
#print axioms Mahler.DubickasExtension.dense_core_two_run_compression_and_macro_transition

-- 32. Verify Section 38: Universal 4(L+1) exponent-weight anagram pigeonhole and anagram drift-cancellation cutoff
#print axioms Mahler.DubickasExtension.dense_core_anagram_weight_decomposition_and_universal_pigeonhole
#print axioms Mahler.DubickasExtension.dense_core_anagram_collision_syzygy_and_drift_cancellation_cutoff

-- 33. Verify Section 39 & 40: (1-Run -> 2-Run) and (2-Run -> 1-Run) interface renormalizations, 58025 - 8*2059 = 2187*19 determinant identity, and 3-run wave W_2 elimination
#print axioms Mahler.DubickasExtension.dense_core_one_to_two_run_interface_syzygy_and_ten_mul_valuation_lock
#print axioms Mahler.DubickasExtension.dense_core_two_to_one_run_interface_and_wave_elimination

-- 34. Verify Section 41: Complete 2 -> 1 -> 2 wave elimination, Mod-19 conservation, and strict well-founded odd-quotient descent W_4 + 2 <= W_2 inside the Dense Core
#print axioms Mahler.DubickasExtension.dense_core_two_one_two_wave_elimination_and_strict_W_descent

-- 35. Verify Section 42: Multi-wave telescoping cancellation, terminal run-spike descent, and unconditional exclusion of infinite wave-descent epochs
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_telescoping_and_epoch_W_descent

-- 36. Verify Section 43 & 44: Same-middle-run wave cancellation, non-descent run-growth speed limit (17*L_4 < 27*L_2 + 7*L_3), and (L_2=1, L_3=1) alternation-vs.-descent dichotomy
#print axioms Mahler.DubickasExtension.dense_core_same_middle_run_wave_cancellation_and_divisibility
#print axioms Mahler.DubickasExtension.dense_core_non_descent_run_growth_speed_limit_and_212_dichotomy

-- 37. Verify Section 45 & 46: Macro-run mod-16/128/1024 bijections, disjoint mod-8 sectors, 4x/8x accelerated wave descent, and singleton-bridge cross-wave pure (2, 3)-power balance
#print axioms Mahler.DubickasExtension.dense_core_macro_run_mod_16_128_1024_bijections_and_step_8_descent
#print axioms Mahler.DubickasExtension.dense_core_singleton_bridge_wave_identities_and_cross_wave_power_balance

-- 38. Verify Section 47: Pure power-of-3 macro-run sieves (W_2 mod 128 in {113, 9}, W_3 mod 1024 in {143, 141}), 1/6377292 macro-wave corridor, and macro-wave constant of motion W_2 - 1
#print axioms Mahler.DubickasExtension.dense_core_macro_run_pure_power_three_sieves_and_exact_residues
#print axioms Mahler.DubickasExtension.dense_core_macro_wave_archimedean_floor_invariant_and_corridor

-- 39. Verify Sections 48–55: 3-adic mirror sieves (mod 2187 and mod 59049), universal mod-24 conservation, mod-9 & mod-144 bijections, 12x/24x/36x/72x accelerated wave descent, exact full-power 3-adic remainders, dual 1->2->1 floor invariant, +19-cancellation homogeneous difference & run-expansion laws, Fermat-prime mod-11 & mod-25 homoclinic sieves (mod 4400 & mod 39600), 4-run W_2-free cross-wave syzygy, exact 2-adic wave valuations & short-run 2-adic Euclidean laws, symmetric (2^Σ_N, 3^Σ_N) multi-wave master identity, and 275 * 2^(Σ_N + 10*L_end + 4) super-divisibility law
#print axioms Mahler.DubickasExtension.dense_core_three_adic_mirror_sieves_and_mod_24_144_bijections
#print axioms Mahler.DubickasExtension.dense_core_dual_wave_full_three_adic_remainders_and_one_run_floor_invariant
#print axioms Mahler.DubickasExtension.dense_core_plus_19_cancellation_homogeneous_difference_and_run_expansion_laws
#print axioms Mahler.DubickasExtension.dense_core_fermat_homoclinic_sieves_and_mod_4400_39600_bijections
#print axioms Mahler.DubickasExtension.dense_core_four_run_W2_free_cross_wave_syzygy
#print axioms Mahler.DubickasExtension.dense_core_wave_exact_two_adic_valuations_and_short_run_euclidean_laws
#print axioms Mahler.DubickasExtension.dense_core_symmetric_multi_wave_master_identity_and_boundary_independence
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_interior_match_cancellation_and_275_super_divisibility
#print axioms Mahler.DubickasExtension.dense_core_macro_wave_archimedean_repetition_cutoff
#print axioms Mahler.DubickasExtension.dense_core_waveInteriorAcc_telescopic_cross_defect_and_mirror_collapses
#print axioms Mahler.DubickasExtension.dense_core_same_run_length_crt_moduli_and_billion_step_descent
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_58025_super_divisibility_and_22_bit_repetition_cutoff
#print axioms Mahler.DubickasExtension.dense_core_dual_one_run_multi_wave_master_identity_and_2059_super_divisibility
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_half_step_elimination_and_7427200_sieve
#print axioms Mahler.DubickasExtension.dense_core_dualWaveInteriorAcc_telescopic_cross_defect_and_mirror_collapses
#print axioms Mahler.DubickasExtension.dense_core_waveCrossDefect_boundary_valuations_and_anagram_locks
#print axioms Mahler.DubickasExtension.dense_core_waveCrossDefect_prefix_filtration_and_anagram_divisibility
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_incoming_elimination_and_126900675_sieve
#print axioms Mahler.DubickasExtension.dense_core_two_way_16243286400_tower_super_divisibility_and_33_bit_cutoff
#print axioms Mahler.DubickasExtension.dense_core_interface_2059_and_58025_automatic_self_propagation
#print axioms Mahler.DubickasExtension.dense_core_universal_multi_wave_constant_of_motion_and_three_adic_remainders
#print axioms Mahler.DubickasExtension.dense_core_cross_defect_dual_accumulator_factorization_and_complementarity
#print axioms Mahler.DubickasExtension.dense_core_two_sided_prefix_suffix_anagram_super_divisibility
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_homogeneous_difference_and_all_horizon_corridor
#print axioms Mahler.DubickasExtension.dense_core_all_horizon_same_run_strict_growth_and_mandatory_expansion
#print axioms Mahler.DubickasExtension.dense_core_dual_multi_wave_homogeneous_difference_and_124499856384_growth
#print axioms Mahler.DubickasExtension.dense_core_multi_horizon_shift_composition_and_three_point_wronskian_syzygy
#print axioms Mahler.DubickasExtension.dense_core_cumulative_level_growth_and_exponential_run_explosion
#print axioms Mahler.DubickasExtension.dense_core_one_run_mod_29_71_464_1392_bijections
#print axioms Mahler.DubickasExtension.dense_core_multi_wave_three_way_gcd_equality_and_corridor_bound
#print axioms Mahler.DubickasExtension.dense_core_multi_horizon_wronskian_archimedean_and_divisibility_bounds
#print axioms Mahler.DubickasExtension.dense_core_accumulator_exponential_bands_and_cauchy_pinch
#print axioms Mahler.DubickasExtension.dense_core_full_exponent_archimedean_wave_bound_and_step_sum_expansion
#print axioms Mahler.DubickasExtension.dense_core_short_run_two_wave_631_growth_and_isolated_dip_law
#print axioms Mahler.DubickasExtension.dense_core_dual_one_run_full_exponent_expansion_and_seven_pow_growth

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
