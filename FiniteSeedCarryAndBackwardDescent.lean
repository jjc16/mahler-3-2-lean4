import SturmianAndBalancedComplexityExclusion

/-!
# Finite-Seed Carry Isolation, Product-Graph False Positives & Backward Descent

This module implements Path 1 of the research plan (Centerpiece 2: distinguishing
finite positive integer seeds from indefinitely compatible 2-adic / symbolic paths):

1. **Exact Resolution of the $G_{3,6}$ Product-Graph False Positive
   $(5,5) \to (4,2) \to (6,3) \to (5,5)$ (`g3_6_false_positive_cycle_and_real_orbit`,
   `constant_three_step_aff_invariant`,
   `constant_three_block_chain_eight_pow_dvd`,
   `constant_three_block_chain_horizon_bound`)**:
   - In the finite coupled product graph `G_{3, 6}`, the 3-cycle
     `(5, 5) → (4, 2) → (6, 3) → (5, 5)` is a valid infinite directed walk,
     its real fractional cycle `9/19 → 4/19 → 6/19 → 9/19` stays strictly in
     `[0, 1/2)`, and `minSlack (fun _ => 3) m = 2^(3 * m) > 0` holds for all `m`.
   - However, along any integer block chain with `s k = 3` (`k < m`), we prove
     the exact affine invariant:
     `8^m * (19 * orbit a_0 (blockSteps s m) + 9) = 27^m * (19 * a_0 + 9)`,
     forcing **`8^m ∣ (19 * a_0 + 9)`** and `8^m ≤ 19 * a_0 + 9`.
   - In `ℤ_2`, this is solved for all `m` by the negative rational 2-adic seed
     `a_0 = -9/19 ≡ 5 (mod 8)` (`19 * a_0 + 9 = 0`). For any positive integer
     `a_0 < 2^W`, `19 * a_0 + 9 > 0` forces `3 * m ≤ W + 4`.

2. **Uniqueness of Arithmetic-Controlled Block Parameters & Coasting Isolation
   (`arith_block_parameters_unique`, `finite_positive_seed_coasting_isolation`)**:
   - Unlike the scalar recurrence `μ' = min(1, (3/2)^c μ - 2)` where `c ≥ 3` is
     an unconstrained parameter at `μ = 1`, for any odd integer `b` the pair
     `(c, u)` with `1 ≤ c`, `u % 2 = 1`, and `3 * b + 1 = 2^c * u` is **uniquely
     determined by `b`**, fixing the next arithmetic state `b' = 3^(c - 1) * u`.
   - Once `W ≤ blockSteps s m` (`a_0 < 2^W`), `jumpQuotient a_0 s m = 0` and
     `2^(blockSteps s (m + 1)) * u m = 3^(blockSteps s m) * (3 * a_0 + 1) + 2^(s 0) * coprimeRemainder s m`.

3. **Backward-Lifting & Minimal-Survivor Stopping Classification
   (`predecessor_lt_boundary`, `exists_odd_predecessor_iff_mod_three`,
   `fracPart_backward_lift_identity`, `backward_archimedean_survival_dichotomy`)**:
   - Every predecessor block boundary `a` (`3 * a + 1 = 2^c * u`) is strictly
     smaller than the current boundary `b = 3^(c - 1) * u` (`a < b` for all `c ≥ 1`, `u ≥ 1`).
   - For `2 ≤ c` and `u % 2 = 1`, an odd natural predecessor `a` with `3 * a + 1 = 2^c * u`
     exists **if and only if** `(2^c * u) % 3 = 1`.
   - Across an odd block of length `c`, the initial and terminal fractional parts
     satisfy `r_a = 1/3 + (2/3)^c * r_b`. For `0 ≤ r_b < 1/2`:
     * when `3 ≤ c`, `1/3 ≤ r_a < 13/27 < 1/2` holds **unconditionally**;
     * when `c = 2`, `r_a < 1/2 ↔ r_b < 3/8`;
     * when `c = 1`, `r_a < 1/2 ↔ r_b < 1/4`.
-/

namespace Mahler.FiniteSeedAndBackwardDescent

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
open Mahler.TwoSidedSqueeze
open Mahler.SharpenedSqueezes
open Mahler.AperiodicCocycle
open Mahler.MinSlackSystem
open Mahler.GlobalStepRate
open Mahler.BaseTwoLock
open Mahler.CeilingSynthesis
open Mahler.TelescopingDuality
open Mahler.ConverseReconstruction
open Mahler.ExplicitCutoffs
open Mahler.DeficitAmplification
open Mahler.TwoVisitSeparation
open Mahler.MonotonicSeparation
open Mahler.CeilingModTraps
open Mahler.TwoAdicLTE
open Mahler.FullStepValuation
open Mahler.RemainderAdditionLaw
open Mahler.TwoAdicCauchy
open Mahler.AllHistoryRecovery
open Mahler.ParametricCorridor
open Mahler.AperiodicBoundedSqueeze
open Mahler.TimeIndependentSqueeze
open Mahler.SlackDeadEnds
open Mahler.GrandSynthesis
open Mahler.Mod256Sieve
open Mahler.UnitRigidity
open Mahler.DeterminantCollapse
open Mahler.BakerMatveev
open Mahler.RidoutSubspace
open Mahler.MultiOriginSyzygy
open Mahler.SubwordComplexity
open Mahler.SimultaneousBaseDigits
open Mahler.MultiStepGCD
open Mahler.SeriesHankel
open Mahler.ThreeAdicSeedLocks
open Mahler.CoupledFractionalDynamics
open Mahler.Mod2304Sieve
open Mahler.TwoSidedCRTObstructions
open Mahler.ThreeAdicConservation
open Mahler.Mod216QuotientFloor
open Mahler.InfiniteZNumberBridge
open Mahler.SturmianComplexityExclusion

/-! ## 1. The $G_{3,6}$ Product-Graph False Positive $(5,5) \to (4,2) \to (6,3) \to (5,5)$ & 2-Adic Seed $-9/19$ -/

/-- **The $G_{3,6}$ False-Positive Cycle & Real Fractional Orbit (`g3_6_false_positive_cycle_and_real_orbit`)**:
In `G_{3, 6}`, `(5, 5) → (4, 2) → (6, 3) → (5, 5)` is a valid directed 3-cycle,
its fractional orbit `9/19 → 4/19 → 6/19 → 9/19` stays strictly in `[0, 1/2)`,
and the constant block sequence `s k = 3` keeps `minSlack (fun _ => 3) m = 2^(3 * m) > 0`
for all `m : ℕ`. -/
theorem g3_6_false_positive_cycle_and_real_orbit :
    coupledEdge 3 6 5 5 4 2 = true ∧
      coupledEdge 3 6 4 2 6 3 = true ∧
      coupledEdge 3 6 6 3 5 5 = true ∧
      ((3 / 2 : ℝ) * (9 / 19 : ℝ) - 1 / 2 = (4 / 19 : ℝ) ∧
        (3 / 2 : ℝ) * (4 / 19 : ℝ) = (6 / 19 : ℝ) ∧
        (3 / 2 : ℝ) * (6 / 19 : ℝ) = (9 / 19 : ℝ)) ∧
      (∀ m : ℕ, minSlack (fun _ => 3) m = (2 : ℤ) ^ (blockSteps (fun _ => 3) m)) := by
  refine ⟨by decide, by decide, by decide, ⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
  intro m
  exact minSlack_eq_two_pow_of_three_le (fun _ => 3) m (fun _ _ => le_rfl)

/-- Across any single block `k` with `s k = 3`, the affine quantity
`19 * orbit a_0 (blockSteps s k) + 9` satisfies:
`8 * (19 * orbit a_0 (blockSteps s (k + 1)) + 9) =
  27 * (19 * orbit a_0 (blockSteps s k) + 9)`. -/
theorem constant_three_step_aff_invariant
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hkK : k < K) (hchain : ValidBlockChain a_0 s u K) (hs3 : s k = 3) :
    8 * (19 * orbit a_0 (blockSteps s (k + 1)) + 9) =
      27 * (19 * orbit a_0 (blockSteps s k) + 9) := by
  rcases hchain k hkK with ⟨hsk, _, hdecomp⟩
  have horb_next : orbit a_0 (blockSteps s (k + 1)) = 3 ^ (s k - 1) * u k := by
    have hsteps : blockSteps s (k + 1) = blockSteps s k + s k := rfl
    rw [hsteps, orbit_add]
    exact orbit_odd_block_return hsk hdecomp
  rw [hs3] at hdecomp horb_next
  norm_num at hdecomp horb_next
  omega

/-- **Exact $s(k)=3$ Multi-Block Affine Invariant & $8^m$-Divisibility Law
(`constant_three_block_chain_eight_pow_dvd`)**:
Along any `ValidBlockChain a_0 s u K`, if `s k = 3` for all `k < m` (`m ≤ K`), then:
1. `8^m * (19 * orbit a_0 (blockSteps s m) + 9) = 27^m * (19 * a_0 + 9)`,
2. `8^m ∣ (19 * a_0 + 9)`, and
3. `8^m ≤ 19 * a_0 + 9`. -/
theorem constant_three_block_chain_eight_pow_dvd
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m ≤ K) (hchain : ValidBlockChain a_0 s u K)
    (hs3 : ∀ k < m, s k = 3) :
    8 ^ m * (19 * orbit a_0 (blockSteps s m) + 9) =
        27 ^ m * (19 * a_0 + 9) ∧
      8 ^ m ∣ (19 * a_0 + 9) ∧
      8 ^ m ≤ 19 * a_0 + 9 := by
  have heq :
      8 ^ m * (19 * orbit a_0 (blockSteps s m) + 9) =
        27 ^ m * (19 * a_0 + 9) := by
    induction m with
    | zero => simp [blockSteps, orbit]
    | succ m ih =>
        have ihm := ih (by omega) (fun k hk => hs3 k (by omega))
        have hstep :=
          constant_three_step_aff_invariant (by omega : m < K) hchain
            (hs3 m (Nat.lt_succ_self m))
        calc
          8 ^ (m + 1) * (19 * orbit a_0 (blockSteps s (m + 1)) + 9) =
              8 ^ m * (8 * (19 * orbit a_0 (blockSteps s (m + 1)) + 9)) := by
            rw [Nat.pow_succ]
            ring
          _ = 8 ^ m * (27 * (19 * orbit a_0 (blockSteps s m) + 9)) := by
            rw [hstep]
          _ = 27 * (8 ^ m * (19 * orbit a_0 (blockSteps s m) + 9)) := by ring
          _ = 27 * (27 ^ m * (19 * a_0 + 9)) := by rw [ihm]
          _ = 27 ^ (m + 1) * (19 * a_0 + 9) := by
            rw [Nat.pow_succ]
            ring
  have hcop : Nat.Coprime (8 ^ m) (27 ^ m) :=
    (by decide : Nat.Coprime 8 27).pow m m
  have hdvd_mul : 8 ^ m ∣ 27 ^ m * (19 * a_0 + 9) :=
    ⟨19 * orbit a_0 (blockSteps s m) + 9, heq.symm⟩
  have hdvd : 8 ^ m ∣ (19 * a_0 + 9) := hcop.dvd_of_dvd_mul_left hdvd_mul
  have hle : 8 ^ m ≤ 19 * a_0 + 9 := Nat.le_of_dvd (by omega) hdvd
  exact ⟨heq, hdvd, hle⟩

/-- **Finite-Seed Horizon Cutoff on the $(5,5) \to (4,2) \to (6,3)$ Cycle
(`constant_three_block_chain_horizon_bound`)**:
For any positive integer seed `a_0 < 2^W`, a valid block chain with `s k = 3`
for `k < m` (`m ≤ K`) satisfies `3 * m ≤ W + 4`. -/
theorem constant_three_block_chain_horizon_bound
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m ≤ K) (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hs3 : ∀ k < m, s k = 3) :
    3 * m ≤ W + 4 := by
  have hle := (constant_three_block_chain_eight_pow_dvd hmK hchain hs3).2.2
  have h8 : 8 ^ m = 2 ^ (3 * m) := by
    change (2 ^ 3) ^ m = 2 ^ (3 * m)
    rw [← Nat.pow_mul]
  have h19 : 19 * a_0 + 9 < 2 ^ (W + 5) := by
    have hpow : 2 ^ (W + 5) = 32 * 2 ^ W := by
      rw [Nat.pow_add]
      ring
    omega
  have hlt : 2 ^ (3 * m) < 2 ^ (W + 5) := by omega
  by_contra hgt
  have hge : 2 ^ (W + 5) ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ## 2. Uniqueness of Arithmetic-Controlled Block Parameters & Coasting Isolation -/

/-- **Uniqueness of Arithmetic-Controlled Block Parameters (`arith_block_parameters_unique`)**:
For any natural number `b`, if `2^c1 * u1 = 3 * b + 1` and `2^c2 * u2 = 3 * b + 1`
with `u1 % 2 = 1` and `u2 % 2 = 1`, then `c1 = c2`, `u1 = u2`, and the next
block boundary `3^(c1 - 1) * u1 = 3^(c2 - 1) * u2` is uniquely determined by `b`. -/
theorem arith_block_parameters_unique {b c1 c2 u1 u2 : ℕ}
    (hu1 : u1 % 2 = 1) (hu2 : u2 % 2 = 1)
    (heq1 : 3 * b + 1 = 2 ^ c1 * u1) (heq2 : 3 * b + 1 = 2 ^ c2 * u2) :
    c1 = c2 ∧ u1 = u2 ∧ 3 ^ (c1 - 1) * u1 = 3 ^ (c2 - 1) * u2 := by
  have hcomb : 2 ^ c1 * u1 = 2 ^ c2 * u2 := heq1.symm.trans heq2
  have hc_eq : c1 = c2 := by
    rcases lt_trichotomy c1 c2 with hlt | rfl | hgt
    · exfalso
      have hsplit : 2 ^ c2 * u2 = 2 ^ c1 * (2 ^ (c2 - c1) * u2) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, show c1 + (c2 - c1) = c2 by omega]
      rw [hsplit] at hcomb
      have hpos : 0 < 2 ^ c1 := Nat.pow_pos (by decide)
      have hu1_eq : u1 = 2 ^ (c2 - c1) * u2 := Nat.eq_of_mul_eq_mul_left hpos hcomb
      have hdvd2 : 2 ∣ 2 ^ (c2 - c1) := by
        have hdiff : c2 - c1 = (c2 - c1 - 1) + 1 := by omega
        rw [hdiff, Nat.pow_succ]
        exact ⟨2 ^ (c2 - c1 - 1), by ring⟩
      rcases hdvd2 with ⟨q, hq⟩
      have heven : u1 = 2 * (q * u2) := by rw [hu1_eq, hq]; ring
      omega
    · rfl
    · exfalso
      have hsplit : 2 ^ c1 * u1 = 2 ^ c2 * (2 ^ (c1 - c2) * u1) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, show c2 + (c1 - c2) = c1 by omega]
      rw [hsplit] at hcomb
      have hpos : 0 < 2 ^ c2 := Nat.pow_pos (by decide)
      have hu2_eq : 2 ^ (c1 - c2) * u1 = u2 := Nat.eq_of_mul_eq_mul_left hpos hcomb
      have hdvd2 : 2 ∣ 2 ^ (c1 - c2) := by
        have hdiff : c1 - c2 = (c1 - c2 - 1) + 1 := by omega
        rw [hdiff, Nat.pow_succ]
        exact ⟨2 ^ (c1 - c2 - 1), by ring⟩
      rcases hdvd2 with ⟨q, hq⟩
      have heven : u2 = 2 * (q * u1) := by rw [← hu2_eq, hq]; ring
      omega
  subst hc_eq
  have hpos : 0 < 2 ^ c1 := Nat.pow_pos (by decide)
  have hu_eq : u1 = u2 := Nat.eq_of_mul_eq_mul_left hpos hcomb
  subst hu_eq
  exact ⟨rfl, rfl, rfl⟩

/-- **Finite Positive Seed Coasting Isolation (`finite_positive_seed_coasting_isolation`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`) with `a_0 < 2^W` and
`W ≤ blockSteps s m`:
1. The high-bit carry from `a_0` freezes at `jumpQuotient a_0 s m = 0` (`a_0 % 2^(blockSteps s m) = a_0`),
2. `2^(blockSteps s (m + 1)) * u m = 3^(blockSteps s m) * (3 * a_0 + 1) + 2^(s 0) * coprimeRemainder s m`, and
3. If `0 < integerSlack s m`, then `2^(blockSteps s (m + 1) + 1) * u m < 3^(blockSteps s m + 1) * 2^(W + 1)`. -/
theorem finite_positive_seed_coasting_isolation
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (ha0 : a_0 < 2 ^ W) (hW : W ≤ blockSteps s m) :
    jumpQuotient a_0 s m = 0 ∧
      2 ^ (blockSteps s (m + 1)) * u m =
        3 ^ (blockSteps s m) * (3 * a_0 + 1) + 2 ^ (s 0) * coprimeRemainder s m ∧
      (0 < integerSlack s m →
        2 ^ (blockSteps s (m + 1) + 1) * u m <
          3 ^ (blockSteps s m + 1) * 2 ^ (W + 1)) := by
  refine ⟨coasting_jumpQuotient_eq_zero ha0 hW, ?_, ?_⟩
  · have hm_id := coprime_quotient_m_step_identity hmK hchain
    have h0 := (hchain 0 (by omega)).2.2
    simp only [blockSteps, orbit] at h0
    have hpow_add :
        2 ^ (blockSteps s (m + 1)) * u m =
          2 ^ (s 0) * (2 ^ (tailSteps s m) * u m) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, add_tailSteps_eq_blockSteps_succ]
    calc
      2 ^ (blockSteps s (m + 1)) * u m =
          2 ^ (s 0) * (2 ^ (tailSteps s m) * u m) := hpow_add
      _ = 2 ^ (s 0) * (3 ^ (blockSteps s m) * u 0 + coprimeRemainder s m) := by
        rw [hm_id]
      _ = 3 ^ (blockSteps s m) * (2 ^ (s 0) * u 0) + 2 ^ (s 0) * coprimeRemainder s m := by
        ring
      _ = 3 ^ (blockSteps s m) * (3 * a_0 + 1) + 2 ^ (s 0) * coprimeRemainder s m := by
        rw [← h0]
  · intro hslack
    have horbit := integerSlack_eq_orbit_slack hmK hchain
    have hlt_int :
        (2 : ℤ) ^ (blockSteps s (m + 1) + 1) * (u m : ℤ) <
          (3 : ℤ) ^ (blockSteps s m + 1) * (2 * (a_0 : ℤ) + 1) := by
      linarith
    have hlt_nat :
        2 ^ (blockSteps s (m + 1) + 1) * u m <
          3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
      exact_mod_cast hlt_int
    have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
      rw [Nat.pow_succ]
      omega
    have hle :
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) ≤
          3 ^ (blockSteps s m + 1) * 2 ^ (W + 1) :=
      Nat.mul_le_mul_left _ h2a0
    exact lt_of_lt_of_le hlt_nat hle

/-! ## 3. Exact Backward-Lifting & Minimal-Survivor Stopping Classification -/

private theorem two_pow_lt_three_pow {c : ℕ} (hc : 1 ≤ c) : 2 ^ c < 3 ^ c := by
  induction c with
  | zero => omega
  | succ c ih =>
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · decide
      · have ihc := ih hpos
        rw [Nat.pow_succ, Nat.pow_succ]
        omega

/-- **Strict Backward Integer Descent (`predecessor_lt_boundary`)**:
For any block length `1 ≤ c` and positive quotient `1 ≤ u`, if `3 * a + 1 = 2^c * u`
and `b = 3^(c - 1) * u`, then `a < b` (and in fact `3 * a + 1 ≤ (3^c - 1) * u < 3 * b`). -/
theorem predecessor_lt_boundary {a b c u : ℕ}
    (hc : 1 ≤ c) (hu : 1 ≤ u)
    (ha : 3 * a + 1 = 2 ^ c * u) (hb : b = 3 ^ (c - 1) * u) :
    a < b := by
  have h23 : 2 ^ c + 1 ≤ 3 ^ c := two_pow_lt_three_pow hc
  have h3b : 3 * b = 3 ^ c * u := by
    rw [hb]
    have hc_eq : c = (c - 1) + 1 := by omega
    conv_rhs => rw [hc_eq, Nat.pow_succ]
    ring
  have hmul : (2 ^ c + 1) * u ≤ 3 ^ c * u := Nat.mul_le_mul_right u h23
  have hdist : (2 ^ c + 1) * u = 2 ^ c * u + u := by ring
  omega

/-- **Arithmetic Predecessor Integrality Criterion (`exists_odd_predecessor_iff_mod_three`)**:
For `2 ≤ c` and `u % 2 = 1`, there exists an odd natural number `a` (`a % 2 = 1`)
such that `3 * a + 1 = 2^c * u` **if and only if** `(2^c * u) % 3 = 1`
(equivalently `(2^c * u) % 6 = 4`). -/
theorem exists_odd_predecessor_iff_mod_three {c u : ℕ}
    (hc : 2 ≤ c) :
    (∃ a : ℕ, a % 2 = 1 ∧ 3 * a + 1 = 2 ^ c * u) ↔
      (2 ^ c * u) % 3 = 1 := by
  constructor
  · rintro ⟨a, _, ha⟩
    omega
  · intro hmod3
    have h4_dvd : 4 ∣ 2 ^ c * u := by
      have hpow : 2 ^ 2 ∣ 2 ^ c := Nat.pow_dvd_pow 2 hc
      exact dvd_mul_of_dvd_left (by simpa using hpow) u
    rcases h4_dvd with ⟨q4, hq4⟩
    refine ⟨(2 ^ c * u - 1) / 3, ?_, ?_⟩
    · omega
    · omega

/-- **Exact Backward Fractional Lift (`fracPart_backward_lift_identity`)**:
For any starting odd integer `a`, block length `1 ≤ s`, quotient `u` with
`3 * a + 1 = 2^s * u`, and any real `ξ : ℝ`, the fractional parts
`r_a = fracPart a ξ 0` and `r_b = fracPart a ξ s` satisfy:
`r_a = 1 / 3 + (2 / 3 : ℝ)^s * r_b`. -/
theorem fracPart_backward_lift_identity
    {a s u : ℕ} (hs : 1 ≤ s) (hdecomp : 3 * a + 1 = 2 ^ s * u) (ξ : ℝ) :
    fracPart a ξ 0 =
      1 / 3 + (2 / 3 : ℝ) ^ s * fracPart a ξ s := by
  have hforw := fracPart_odd_block hs hdecomp ξ
  have hinv : (2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have hmul := congrArg (fun x : ℝ => (2 / 3 : ℝ) ^ s * x) hforw
  dsimp at hmul
  calc
    fracPart a ξ 0 =
        ((2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s) * fracPart a ξ 0 := by
      rw [hinv, one_mul]
    _ = (2 / 3 : ℝ) ^ s * ((3 / 2 : ℝ) ^ s * (fracPart a ξ 0 - 1 / 3)) +
          ((2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s) * (1 / 3) := by ring
    _ = (2 / 3 : ℝ) ^ s * fracPart a ξ s + 1 / 3 := by
      rw [← hmul, hinv]
      ring
    _ = 1 / 3 + (2 / 3 : ℝ) ^ s * fracPart a ξ s := by ring

private theorem two_thirds_pow_le_eight_twenty_sevenths {c : ℕ} (hc : 3 ≤ c) :
    (2 / 3 : ℝ) ^ c ≤ 8 / 27 := by
  have hsub : c = 3 + (c - 3) := by omega
  rw [hsub, pow_add]
  have h1 : (2 / 3 : ℝ) ^ 3 = 8 / 27 := by norm_num
  have h2 : (2 / 3 : ℝ) ^ (c - 3) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-- **Backward Archimedean Survival Dichotomy (`backward_archimedean_survival_dichotomy`)**:
For any block length `c : ℕ` and fractional parts `r_a, r_b : ℝ` satisfying
`r_a = 1 / 3 + (2 / 3 : ℝ)^c * r_b` with `0 ≤ r_b < 1 / 2`:
1. `1 / 3 ≤ r_a` always holds,
2. `r_a < 1 / 2 ↔ (2 / 3 : ℝ)^c * r_b < 1 / 6`,
3. If `3 ≤ c`, then `r_a < 13 / 27` and `r_a < 1 / 2` hold **unconditionally**,
4. If `c = 2`, then `r_a < 1 / 2 ↔ r_b < 3 / 8`, and
5. If `c = 1`, then `r_a < 1 / 2 ↔ r_b < 1 / 4`. -/
theorem backward_archimedean_survival_dichotomy {c : ℕ} {r_a r_b : ℝ}
    (heq : r_a = 1 / 3 + (2 / 3 : ℝ) ^ c * r_b)
    (hr0 : 0 ≤ r_b) (hr1 : r_b < 1 / 2) :
    (1 / 3 : ℝ) ≤ r_a ∧
      (r_a < 1 / 2 ↔ (2 / 3 : ℝ) ^ c * r_b < 1 / 6) ∧
      (3 ≤ c → r_a < 13 / 27 ∧ r_a < 1 / 2) ∧
      (c = 2 → (r_a < 1 / 2 ↔ r_b < 3 / 8)) ∧
      (c = 1 → (r_a < 1 / 2 ↔ r_b < 1 / 4)) := by
  have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ c := by positivity
  refine ⟨by nlinarith, ⟨fun h => by linarith, fun h => by linarith⟩, ?_, ?_, ?_⟩
  · intro hc3
    have hpow := two_thirds_pow_le_eight_twenty_sevenths hc3
    have hmul : (2 / 3 : ℝ) ^ c * r_b < 4 / 27 := by nlinarith
    exact ⟨by linarith, by linarith⟩
  · intro hc2
    subst hc2
    norm_num at heq
    constructor <;> intro h <;> linarith
  · intro hc1
    subst hc1
    norm_num at heq
    constructor <;> intro h <;> linarith

end Mahler.FiniteSeedAndBackwardDescent
