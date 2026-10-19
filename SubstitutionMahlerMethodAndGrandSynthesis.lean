import FiniteSeedCarryAndBackwardDescent

/-!
# Dual-Place Rational-Limit Sign Duality, Periodic Macro-Block Summation & 122-Module Grand Synthesis

This module implements Path 3 of the research plan and provides the 122-module
Grand Synthesis:

1. **Archimedean vs. 2-Adic Rational-Limit Sign Split (`dual_place_rational_limit_sign_split`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ m < K`) with `0 < integerSlack s m`,
   the partial sum `blockDrainSum s m = ∑_{k=1}^m (2/3)^(T(k)+1)` simultaneously satisfies:
   - **Archimedean Positivity & `1/3`-Ceiling:** `0 < blockDrainSum s m < 1 / 3`,
   - **Negative 2-Adic Target Gap:**
     `blockDrainSum s m - (-(6 * (a_0 : ℝ) + 2) / 3) = (2^(T(m+1)+1) * u m) / 3^(T(m)+1)`,
     where the target rational `-(6 * (a_0 : ℝ) + 2) / 3 ≤ -2 / 3 < 0` is strictly
     negative while `blockDrainSum s m > 0` is strictly positive, and the numerator
     of their difference is divisible by `2^(T(m+1)+1)`.

2. **Closed-Form Geometric Summation for Uniform/Periodic Macro-Blocks & $2^{D m}$-Divisibility
   (`uniform_macro_block_remainder_geometric_sum`,
   `periodic_macro_block_seed_divisibility`)**:
   - Whenever a sequence `s` decomposes into `m` macro-blocks of length `1 ≤ d`
     with constant macro-block step sum `1 ≤ D` and constant macro-block remainder `R_0`
     (`blockSteps (shiftSeq s (d * j)) d = D`, `tailSteps s (d * j) = D * j`, and
     `coprimeRemainder (shiftSeq s (d * j)) d = R_0` for `j < m`), the cumulative
     remainder collapses in closed form to:
     `(3^D - 2^D) * coprimeRemainder s (d * m) = R_0 * (3^(D * m) - 2^(D * m))`.
   - Along any `ValidBlockChain a_0 s u K` (`d * m < K`), this forces the exact
     rational-series vs. negative-seed identity:
     `(3^D - 2^D) * 2^(blockSteps s (d * m + 1)) * u (d * m) + 2^(s 0) * R_0 * 2^(D * m) =
       3^(D * m) * ((3^D - 2^D) * (3 * a_0 + 1) + 2^(s 0) * R_0)`,
     and hence **`2^(D * m) ∣ ((3^D - 2^D) * (3 * a_0 + 1) + 2^(s 0) * R_0)`**:
     because a rational geometric series sums to the same positive rational number
     `2^(s 0 + 1) * R_0 / (3 * (3^D - 2^D)) > 0` in both `ℝ` and `ℚ_2`, its gap to
     the negative seed constant `-(6 * a_0 + 2) / 3 < 0` is a fixed positive integer
     that can only be divisible by `2^(D * m)` for finitely many `m`.

3. **Three-Point Substitution / Multi-Scale Cocycle Relation
   (`three_point_macro_block_remainder_syzygy`)**:
   For any non-periodic (e.g., substitution or automatic) sequence decomposed at
   `r`, `r + d1`, and `r + d1 + d2`, the three prefix remainders satisfy an exact
   two-scale syzygy governed by the macro-block remainders `R^{(r)}_{d1}` and
   `R^{(r + d1)}_{d2}`.

4. **The 122-Module Grand Synthesis (`mahler_grand_122_module_synthesis`)**:
   Unifies the infinite-horizon $Z$-number bridge, the upstream `Int.fract`
   113-step record-holder theorem, the aperiodic Sturmian/balanced complexity
   exclusions, the $G_{3,6}$ false-positive / $8^m \mid (19 a_0 + 9)$ seed isolation,
   the backward-lifting descent dichotomy, and the dual-place generating-series
   sign split into a single machine-checked theorem.
-/

namespace Mahler.SubstitutionAndGrandSynthesis

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
open Mahler.FiniteSeedAndBackwardDescent

/-! ## 1. Archimedean vs. 2-Adic Rational-Limit Sign Split -/

/-- **Archimedean vs. 2-Adic Rational-Limit Sign Split (`dual_place_rational_limit_sign_split`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ m < K`) with `0 < integerSlack s m`,
the partial sum `blockDrainSum s m` is strictly in `(0, 1 / 3)`, the 2-adic target
rational `-(6 * (a_0 : ℝ) + 2) / 3` is at most `-2 / 3 < 0`, and their difference
equals `(2^(blockSteps s (m + 1) + 1) * u m) / 3^(blockSteps s m + 1)`. -/
theorem dual_place_rational_limit_sign_split
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    0 < blockDrainSum s m ∧
      blockDrainSum s m < 1 / 3 ∧
      -((6 * (a_0 : ℝ) + 2) / 3) ≤ -2 / 3 ∧
      blockDrainSum s m - (-((6 * (a_0 : ℝ) + 2) / 3)) =
        ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) /
          (3 : ℝ) ^ (blockSteps s m + 1) := by
  have hform := blockDrainSum_eq_remainder_div_three_pow s m
  have hs : ∀ k < m, 1 ≤ s k := fun k hk => (hchain k (by omega)).1
  have hR_odd := coprimeRemainder_odd hm1 hs
  have hR_pos : 0 < coprimeRemainder s m := by omega
  have hnum_pos : (0 : ℝ) < ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by decide)) hR_pos
  have hden_pos : (0 : ℝ) < (3 : ℝ) ^ (blockSteps s m + 1) := by positivity
  have hdrain_pos : 0 < blockDrainSum s m := by
    rw [hform]
    exact div_pos hnum_pos hden_pos
  have hdrain_lt : blockDrainSum s m < 1 / 3 := by
    have h1 := slackSeries_eq_one_third_sub_blockDrainSum s m
    have h2 := slackSeries_eq_integerSlack_div s m
    have hslack_real : (0 : ℝ) < (integerSlack s m : ℝ) := by exact_mod_cast hslack
    have hdiv_pos : (0 : ℝ) < (integerSlack s m : ℝ) / (3 : ℝ) ^ (blockSteps s m + 1) :=
      div_pos hslack_real hden_pos
    linarith
  have ha0_nonneg : (0 : ℝ) ≤ (a_0 : ℝ) := Nat.cast_nonneg a_0
  have hgap := dual_place_series_rational_gap_identity hmK hchain
  refine ⟨hdrain_pos, hdrain_lt, by linarith, by linarith⟩

/-! ## 2. Closed-Form Geometric Summation for Uniform/Periodic Macro-Blocks -/

private theorem two_pow_le_three_pow (n : ℕ) : 2 ^ n ≤ 3 ^ n :=
  Nat.pow_le_pow_left (by decide) n

/-- **Closed-Form Geometric Summation for Uniform Macro-Block Remainders
(`uniform_macro_block_remainder_geometric_sum`)**:
If a sequence `s` has constant macro-block step sum `D` and remainder `R_0` across
the first `m` macro-blocks of length `d` (`blockSteps (shiftSeq s (d * j)) d = D`,
`tailSteps s (d * j) = D * j`, and `coprimeRemainder (shiftSeq s (d * j)) d = R_0`
for all `j < m`), then:
`blockSteps s (d * m) = D * m` and
`(3^D - 2^D) * coprimeRemainder s (d * m) = R_0 * (3^(D * m) - 2^(D * m))`. -/
theorem uniform_macro_block_remainder_geometric_sum
    (s : ℕ → ℕ) (d D R_0 m : ℕ)
    (hsteps : ∀ j < m, blockSteps (shiftSeq s (d * j)) d = D)
    (htail : ∀ j < m, tailSteps s (d * j) = D * j)
    (hrem : ∀ j < m, coprimeRemainder (shiftSeq s (d * j)) d = R_0) :
    blockSteps s (d * m) = D * m ∧
      (3 ^ D - 2 ^ D) * coprimeRemainder s (d * m) =
        R_0 * (3 ^ (D * m) - 2 ^ (D * m)) := by
  induction m with
  | zero =>
      simp [blockSteps, coprimeRemainder]
  | succ m ih =>
      rcases ih (fun j hj => hsteps j (by omega))
        (fun j hj => htail j (by omega))
        (fun j hj => hrem j (by omega)) with ⟨ih_steps, ih_rem⟩
      have hdm : d * (m + 1) = d * m + d := by ring
      have hstep_m := hsteps m (Nat.lt_succ_self m)
      have htail_m := htail m (Nat.lt_succ_self m)
      have hrem_m := hrem m (Nat.lt_succ_self m)
      have htot_steps : blockSteps s (d * (m + 1)) = D * (m + 1) := by
        rw [hdm, blockSteps_add, ih_steps, hstep_m]
        ring
      refine ⟨htot_steps, ?_⟩
      rw [hdm, coprimeRemainder_add_eq, hstep_m, htail_m, hrem_m]
      have hle_D : 2 ^ D ≤ 3 ^ D := two_pow_le_three_pow D
      have hle_Dm : 2 ^ (D * m) ≤ 3 ^ (D * m) := two_pow_le_three_pow (D * m)
      have hle_Dm1 : 2 ^ (D * (m + 1)) ≤ 3 ^ (D * (m + 1)) :=
        two_pow_le_three_pow (D * (m + 1))
      have hD_add : D * (m + 1) = D * m + D := by ring
      zify [hle_D, hle_Dm, hle_Dm1] at ih_rem ⊢
      rw [hD_add, pow_add (3 : ℤ) (D * m) D, pow_add (2 : ℤ) (D * m) D]
      linear_combination (3 : ℤ) ^ D * ih_rem

/-- **Periodic Macro-Block $2^{D m}$-Divisibility & Horizon Bound
(`periodic_macro_block_seed_divisibility`)**:
Under the uniform macro-block hypotheses of `uniform_macro_block_remainder_geometric_sum`,
along any `ValidBlockChain a_0 s u K` (`d * m < K`) with `D * m ≤ blockSteps s (d * m + 1)`:
1. `(3^D - 2^D) * 2^(blockSteps s (d * m + 1)) * u (d * m) + 2^(s 0) * R_0 * 2^(D * m) =
     3^(D * m) * ((3^D - 2^D) * (3 * a_0 + 1) + 2^(s 0) * R_0)`, and
2. `2^(D * m) ∣ ((3^D - 2^D) * (3 * a_0 + 1) + 2^(s 0) * R_0)`. -/
theorem periodic_macro_block_seed_divisibility
    {a_0 : ℕ} {s u : ℕ → ℕ} {K d D R_0 m : ℕ}
    (hdmK : d * m < K) (hchain : ValidBlockChain a_0 s u K)
    (hsteps : ∀ j < m, blockSteps (shiftSeq s (d * j)) d = D)
    (htail : ∀ j < m, tailSteps s (d * j) = D * j)
    (hrem : ∀ j < m, coprimeRemainder (shiftSeq s (d * j)) d = R_0) :
    (3 ^ D - 2 ^ D) * 2 ^ (blockSteps s (d * m + 1)) * u (d * m) +
        2 ^ (s 0) * R_0 * 2 ^ (D * m) =
      3 ^ (D * m) * ((3 ^ D - 2 ^ D) * (3 * a_0 + 1) + 2 ^ (s 0) * R_0) ∧
    2 ^ (D * m) ∣ ((3 ^ D - 2 ^ D) * (3 * a_0 + 1) + 2 ^ (s 0) * R_0) := by
  rcases uniform_macro_block_remainder_geometric_sum s d D R_0 m hsteps htail hrem with
    ⟨htot_steps, hgeom⟩
  have hm_id := coprime_quotient_m_step_identity hdmK hchain
  have h0 := (hchain 0 (by omega)).2.2
  simp only [blockSteps, orbit] at h0
  have hmul_s0 :
      2 ^ (blockSteps s (d * m + 1)) * u (d * m) =
        3 ^ (D * m) * (3 * a_0 + 1) + 2 ^ (s 0) * coprimeRemainder s (d * m) := by
    calc
      2 ^ (blockSteps s (d * m + 1)) * u (d * m) =
          2 ^ (s 0) * (2 ^ (tailSteps s (d * m)) * u (d * m)) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, add_tailSteps_eq_blockSteps_succ]
      _ = 2 ^ (s 0) * (3 ^ (blockSteps s (d * m)) * u 0 + coprimeRemainder s (d * m)) := by
        rw [hm_id]
      _ = 3 ^ (blockSteps s (d * m)) * (2 ^ (s 0) * u 0) +
            2 ^ (s 0) * coprimeRemainder s (d * m) := by
        ring
      _ = 3 ^ (D * m) * (3 * a_0 + 1) + 2 ^ (s 0) * coprimeRemainder s (d * m) := by
        rw [← h0, htot_steps]
  have hle_D : 2 ^ D ≤ 3 ^ D := two_pow_le_three_pow D
  have hle_Dm : 2 ^ (D * m) ≤ 3 ^ (D * m) := two_pow_le_three_pow (D * m)
  have heq :
      (3 ^ D - 2 ^ D) * 2 ^ (blockSteps s (d * m + 1)) * u (d * m) +
          2 ^ (s 0) * R_0 * 2 ^ (D * m) =
        3 ^ (D * m) * ((3 ^ D - 2 ^ D) * (3 * a_0 + 1) + 2 ^ (s 0) * R_0) := by
    zify [hle_D, hle_Dm] at hgeom hmul_s0 ⊢
    linear_combination ((3 : ℤ) ^ D - (2 : ℤ) ^ D) * hmul_s0 + (2 : ℤ) ^ (s 0) * hgeom
  have hDm_le : D * m ≤ blockSteps s (d * m + 1) := by
    simp only [blockSteps]
    omega
  have hdvd_lhs :
      2 ^ (D * m) ∣
        ((3 ^ D - 2 ^ D) * 2 ^ (blockSteps s (d * m + 1)) * u (d * m) +
          2 ^ (s 0) * R_0 * 2 ^ (D * m)) := by
    apply Nat.dvd_add
    · have hpow_dvd : 2 ^ (D * m) ∣ 2 ^ (blockSteps s (d * m + 1)) :=
        Nat.pow_dvd_pow 2 hDm_le
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpow_dvd _) _
    · exact dvd_mul_left (2 ^ (D * m)) (2 ^ (s 0) * R_0)
  rw [heq] at hdvd_lhs
  have hcop : Nat.Coprime (2 ^ (D * m)) (3 ^ (D * m)) :=
    (by decide : Nat.Coprime 2 3).pow (D * m) (D * m)
  exact ⟨heq, hcop.dvd_of_dvd_mul_left hdvd_lhs⟩

/-! ## 3. Three-Point Substitution / Multi-Scale Cocycle Relation -/

/-- **Three-Point Multi-Scale Remainder Syzygy (`three_point_macro_block_remainder_syzygy`)**:
For any sequence `s : ℕ → ℕ`, origin `r`, and two consecutive macro-block lengths
`d1, d2`, the prefix remainders at `r`, `r + d1`, and `r + d1 + d2` satisfy:
`coprimeRemainder s (r + d1 + d2) =
  3^(blockSteps (shiftSeq s r) (d1 + d2)) * coprimeRemainder s r +
    2^(tailSteps s r) *
      (3^(blockSteps (shiftSeq s (r + d1)) d2) * coprimeRemainder (shiftSeq s r) d1 +
        2^(tailSteps (shiftSeq s r) d1) * coprimeRemainder (shiftSeq s (r + d1)) d2)`. -/
theorem three_point_macro_block_remainder_syzygy
    (s : ℕ → ℕ) (r d1 d2 : ℕ) :
    coprimeRemainder s (r + d1 + d2) =
      3 ^ (blockSteps (shiftSeq s r) (d1 + d2)) * coprimeRemainder s r +
        2 ^ (tailSteps s r) *
          (3 ^ (blockSteps (shiftSeq s (r + d1)) d2) *
              coprimeRemainder (shiftSeq s r) d1 +
            2 ^ (tailSteps (shiftSeq s r) d1) *
              coprimeRemainder (shiftSeq s (r + d1)) d2) := by
  have h1 := coprimeRemainder_add_eq s r (d1 + d2)
  have h2 := coprimeRemainder_add_eq (shiftSeq s r) d1 d2
  have hshift_add : shiftSeq (shiftSeq s r) d1 = shiftSeq s (r + d1) := by
    funext k
    simp [shiftSeq, Nat.add_assoc]
  rw [hshift_add] at h2
  rw [show r + d1 + d2 = r + (d1 + d2) by omega, h1, h2]

/-! ## 4. The 122-Module Grand Synthesis -/

/-- **The 122-Module Grand Synthesis (`mahler_grand_122_module_synthesis`)**:
Combines in a single machine-checked theorem:
1. **Direct `Int.fract` Infinite-Horizon Equivalence:**
   `ValidCompanionForever a_0 α ↔ (⌊α⌋ = (a_0 : ℤ) ∧ ∀ n : ℕ, Int.fract (α * (3 / 2 : ℝ) ^ n) < 1 / 2)`,
2. **Direct `Int.fract` 113-Step Record-Holder Theorem:**
   `recordHolderA0 = 29871555608238677` survives `113` steps and dies at `114`
   in the exact `∃ ξ ∈ [0, 1), ∀ n ≤ N, Int.fract ((a_0 + ξ)(3/2)^n) < 1/2` formulation,
3. **The $17:10$ Weighted Repeated-Subword Cutoff:**
   `17 * blockSteps (shiftSeq s r1) L ≤ 10 * blockSteps s r2 + 17 * W + 9`,
4. **Unconditional Exclusion of Ceiling-Saturated Sturmian `{3, 4}` Sequences:**
   `3 * L ≤ 12 * C_0 + 5 * W + 2` for any `{3, 4}` chain of complexity `L + C_0`,
5. **Product-Graph False Positive $(5,5) \to (4,2) \to (6,3)$ vs. $8^m \mid (19 a_0 + 9)$ Isolation:**
   Every `s k = 3` chain satisfies `8^m ∣ (19 * a_0 + 9)` and `3 * m ≤ W + 4` for `a_0 < 2^W`,
6. **Backward-Lifting Descent & Automatic $c \ge 3$ Archimedean Survival:**
   `a < b` and `r_a = 1/3 + (2/3)^c * r_b < 13/27 < 1/2` whenever `c ≥ 3` and `0 ≤ r_b < 1/2`, and
7. **Dual-Place (`ℝ × ℚ_2`) Rational-Limit Sign Split:**
   `0 < blockDrainSum s m < 1 / 3` vs. `-(6 * a_0 + 2) / 3 ≤ -2 / 3 < 0`. -/
theorem mahler_grand_122_module_synthesis :
    (∀ (a_0 : ℕ) (α : ℝ),
      ValidCompanionForever a_0 α ↔
        (⌊α⌋ = (a_0 : ℤ) ∧ ∀ n : ℕ, Int.fract (α * (3 / 2 : ℝ) ^ n) < 1 / 2)) ∧
    ((∃ ξ : ℝ, 0 ≤ ξ ∧ ξ < 1 ∧
        ∀ n ≤ 113, Int.fract (((recordHolderA0 : ℝ) + ξ) * (3 / 2 : ℝ) ^ n) < 1 / 2) ∧
      ¬ (∃ ξ : ℝ, 0 ≤ ξ ∧ ξ < 1 ∧
        ∀ n ≤ 114, Int.fract (((recordHolderA0 : ℝ) + ξ) * (3 / 2 : ℝ) ^ n) < 1 / 2)) ∧
    (∀ {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ},
      1 ≤ L → r1 < r2 → r2 + (L - 1) < K → a_0 < 2 ^ W →
      ValidBlockChain a_0 s u K → 0 < integerSlack s r2 →
      (∀ i < L, s (r1 + i) = s (r2 + i)) →
        17 * blockSteps (shiftSeq s r1) L ≤ 10 * blockSteps s r2 + 17 * W + 9) ∧
    (∀ {a_0 W L C_0 K : ℕ} {s u : ℕ → ℕ},
      1 ≤ L → 2 * L + C_0 ≤ K → a_0 < 2 ^ W →
      ValidBlockChain a_0 s u K → (∀ k < K, 3 ≤ s k ∧ s k ≤ 4) →
      ∀ (pat : ℕ → Fin (L + C_0)),
        (∀ r1 ≤ L + C_0, ∀ r2 ≤ L + C_0,
          pat r1 = pat r2 → ∀ i < L, s (r1 + i) = s (r2 + i)) →
        3 * L ≤ 12 * C_0 + 5 * W + 2) ∧
    (∀ {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ},
      m ≤ K → a_0 < 2 ^ W → ValidBlockChain a_0 s u K → (∀ k < m, s k = 3) →
        8 ^ m ∣ (19 * a_0 + 9) ∧ 3 * m ≤ W + 4) ∧
    (∀ {c : ℕ} {r_a r_b : ℝ},
      r_a = 1 / 3 + (2 / 3 : ℝ) ^ c * r_b → 0 ≤ r_b → r_b < 1 / 2 → 3 ≤ c →
        (1 / 3 : ℝ) ≤ r_a ∧ r_a < 13 / 27 ∧ r_a < 1 / 2) ∧
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ},
      1 ≤ m → m < K → ValidBlockChain a_0 s u K → 0 < integerSlack s m →
        0 < blockDrainSum s m ∧ blockDrainSum s m < 1 / 3 ∧
          -((6 * (a_0 : ℝ) + 2) / 3) ≤ -2 / 3) := by
  refine ⟨validCompanionForever_iff_floor_and_forall_fract_lt_half,
    recordHolderA0_fract_offset_113_survival_and_114_death,
    fun hL hr12 hr2L ha0 hchain hslack hmatch =>
      weighted_seventeen_ten_repeated_subword_cutoff hL hr12 hr2L ha0 hchain hslack hmatch,
    fun hL hK ha0 hchain hs pat hpat =>
      aperiodic_sturmian_three_four_exclusion hL hK ha0 hchain hs pat hpat,
    fun hmK ha0 hchain hs3 =>
      ⟨(constant_three_block_chain_eight_pow_dvd hmK hchain hs3).2.1,
        constant_three_block_chain_horizon_bound hmK ha0 hchain hs3⟩,
    fun heq hr0 hr1 hc3 => by
      have h := backward_archimedean_survival_dichotomy heq hr0 hr1
      exact ⟨h.1, (h.2.2.1 hc3).1, (h.2.2.1 hc3).2⟩,
    fun hm1 hmK hchain hslack => by
      have h := dual_place_rational_limit_sign_split hm1 hmK hchain hslack
      exact ⟨h.1, h.2.1, h.2.2.1⟩⟩

end Mahler.SubstitutionAndGrandSynthesis
