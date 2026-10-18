import BakerMatveevFramework

/-!
# The Ridout / `{∞, 2, 3}`-Place Subspace Framework & Critical `Q_m^(-2)` Product Law

This module formalizes the multi-place (`S = {∞, 2, 3}`) Ridout / `p`-adic Subspace
Theorem framework for the reduced Mahler coprime system:

1. **Intrinsic `S = {2, 3}` Coprimality of `integerSlack` (`integerSlack_toNat_coprime_six`,
   `intrinsic_equation_pairwise_coprime`)**:
   - Whenever `1 ≤ m`, `∀ k < m, 1 ≤ s k`, and `0 < integerSlack s m`, the positive
     integer `Δ_m = (integerSlack s m).toNat` in the intrinsic equation
     `3^(blockSteps s m) = 2^(s 0 + 1) * coprimeRemainder s m + Δ_m`
     satisfies `Nat.Coprime Δ_m 6`, and all three terms `3^(T(m))`,
     `2^(s 0 + 1) * R(s, m)`, and `Δ_m` are pairwise coprime.
2. **Exact `2^(T(m))`-Cancellation Law for `u(m) * Δ_m`
   (`ridout_non_s_part_cancellation`, `ridout_pinched_slack_cancellation`)**:
   - In the orbit equation
     `Q_m - P_m = Δ_m` with `Q_m = 3^(T(m) + 1) * (2 * a_0 + 1)` and
     `P_m = 2^(T(m + 1) + 1) * u m`, the `{2, 3}`-free parts of `P_m` and `Δ_m`
     are bounded by `u m ~ (3/2)^(T(m))` and `Δ_m ≤ 2^(T(m))` in any sub-ceiling phase.
   - Multiplying `u m` and `Δ_m` cancels `2^(T(m))` identically, yielding the exact
     integer inequality:
     `2^(s m + 1) * u m * (integerSlack s m).toNat < 3^(blockSteps s m + 1) * (2 * a_0 + 1)`.
   - More generally, if `2^D * (integerSlack s m).toNat ≤ 2^(blockSteps s m)` (a slack
     pinch of `D` bits below ceiling), then:
     `2^(s m + D + 1) * u m * (integerSlack s m).toNat < 3^(blockSteps s m + 1) * (2 * a_0 + 1)`.
3. **The Three-Place (`{∞, 2, 3}`) Ridout Product Inequality at the Critical `Q_m^(-2)`
   Boundary (`ridout_three_place_product_lt`, `ridout_three_place_quadratic_bound`)**:
   - Combining the archimedean factor `1 - P_m / Q_m = Δ_m / Q_m`, the 2-adic factor
     `u m / P_m = 2^(-(T(m + 1) + 1))`, and the 3-adic factor
     `(2 * a_0 + 1) / Q_m = 3^(-(T(m) + 1))` yields:
     `(1 - P_m / Q_m) * (u m / P_m) * ((2 * a_0 + 1) / Q_m) <
       ((2 * a_0 + 1) / 2^(s m + 1)) * (1 / (P_m * Q_m)) <
       ((6 * a_0 + 3) * (2 * a_0 + 1) / (2^(s m + 1) * (6 * a_0 + 2))) * (1 / Q_m^2)`.
   - This proves that the 3-place Ridout product sits right at Ridout's critical
     `Q_m^(-2)` exponent, and drops strictly below `Q_m^(-2 - ε)` whenever either
     `s m` grows linearly with `T(m)` or `Δ_m ≤ 2^((1 - δ) * T(m))` pinches below ceiling.
4. **Two-Seed Shared-Prefix Ridout Difference Lock (`two_seed_shared_prefix_divisibility`)**:
   - If two seeds `a_0, b_0` share the same block sequence `s` up to block `m`,
     subtracting their orbit slack identities eliminates `integerSlack s m` completely:
     `3^(blockSteps s m + 1) * (a_0 - b_0) = 2^(blockSteps s (m + 1)) * (u m - v m)`,
     forcing `2^(blockSteps s (m + 1)) ∣ (a_0 - b_0)`.
-/

namespace Mahler.RidoutSubspace

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

/-! ## 1. Intrinsic `S = {2, 3}` Coprimality of `integerSlack` -/

private theorem three_pow_odd (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem two_pow_mod_three_ne_zero (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rcases ih with h1 | h2
    · right; rw [Nat.pow_succ, Nat.mul_mod, h1]
    · left; rw [Nat.pow_succ, Nat.mul_mod, h2]

/-- **Intrinsic `S = {2, 3}` Coprimality of `integerSlack` (`integerSlack_toNat_coprime_six`)**:
For any sequence `s` with `1 ≤ m`, `∀ k < m, 1 ≤ s k`, and `0 < integerSlack s m`,
the positive integer `Δ_m = (integerSlack s m).toNat` satisfies:
1. `2^(s 0 + 1) * coprimeRemainder s m + (integerSlack s m).toNat = 3^(blockSteps s m)`,
2. `(integerSlack s m).toNat % 2 = 1`,
3. `(integerSlack s m).toNat % 3 ≠ 0`, and
4. `Nat.Coprime (integerSlack s m).toNat 6`. -/
theorem integerSlack_toNat_coprime_six {s : ℕ → ℕ} {m : ℕ}
    (hm1 : 1 ≤ m) (hs : ∀ k < m, 1 ≤ s k) (hpos : 0 < integerSlack s m) :
    2 ^ (s 0 + 1) * coprimeRemainder s m + (integerSlack s m).toNat =
        3 ^ (blockSteps s m) ∧
      (integerSlack s m).toNat % 2 = 1 ∧
      (integerSlack s m).toNat % 3 ≠ 0 ∧
      Nat.Coprime (integerSlack s m).toNat 6 := by
  have hdef :
      integerSlack s m =
        ((3 ^ (blockSteps s m) : ℕ) : ℤ) -
          ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) := by
    unfold integerSlack
    push_cast
    rfl
  have hadd :
      2 ^ (s 0 + 1) * coprimeRemainder s m + (integerSlack s m).toNat =
        3 ^ (blockSteps s m) := by
    omega
  have hs0 : 1 ≤ s 0 := hs 0 (by omega)
  have h2_even : 2 ^ (s 0 + 1) % 2 = 0 := by
    rw [Nat.pow_succ]
    omega
  have h3_odd : 3 ^ (blockSteps s m) % 2 = 1 := three_pow_odd (blockSteps s m)
  have hodd : (integerSlack s m).toNat % 2 = 1 := by
    have hmod :
        (2 ^ (s 0 + 1) * coprimeRemainder s m + (integerSlack s m).toNat) % 2 =
          3 ^ (blockSteps s m) % 2 := by
      rw [hadd]
    rw [Nat.add_mod, Nat.mul_mod, h2_even, h3_odd] at hmod
    omega
  have hT_pos : 1 ≤ blockSteps s m := by
    have h01 : blockSteps s 1 = s 0 := by simp [blockSteps]
    have hmono := Mahler.BridgeThree.blockSteps_mono s (show 1 ≤ m by omega)
    omega
  have h3_div3 : 3 ^ (blockSteps s m) % 3 = 0 := by
    rw [show blockSteps s m = (blockSteps s m - 1) + 1 by omega, Nat.pow_succ]
    omega
  have hR_ne := coprimeRemainder_mod_three_ne_zero hm1 hs
  have hR_mod3 : coprimeRemainder s m % 3 = 1 ∨ coprimeRemainder s m % 3 = 2 := by
    omega
  have h2_mod3 := two_pow_mod_three_ne_zero (s 0 + 1)
  have hmod3_ne : (integerSlack s m).toNat % 3 ≠ 0 := by
    have hmod :
        (2 ^ (s 0 + 1) * coprimeRemainder s m + (integerSlack s m).toNat) % 3 =
          3 ^ (blockSteps s m) % 3 := by
      rw [hadd]
    rw [Nat.add_mod, Nat.mul_mod, h3_div3] at hmod
    rcases hR_mod3 with hR1 | hR2 <;> rcases h2_mod3 with h21 | h22
    · rw [hR1, h21] at hmod; omega
    · rw [hR1, h22] at hmod; omega
    · rw [hR2, h21] at hmod; omega
    · rw [hR2, h22] at hmod; omega
  have hcop2 : Nat.Coprime (integerSlack s m).toNat 2 :=
    (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)))
  have hcop3 : Nat.Coprime (integerSlack s m).toNat 3 :=
    (Nat.Coprime.symm (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)))
  have hcop6 : Nat.Coprime (integerSlack s m).toNat 6 := by
    simpa using hcop2.mul_right hcop3
  exact ⟨hadd, hodd, hmod3_ne, hcop6⟩

/-! ## 2. Exact `2^(T(m))`-Cancellation Law for `u(m) * Δ_m` -/

/-- **Ridout Non-`S`-Part Cancellation Law (`ridout_non_s_part_cancellation`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`) in a sub-ceiling phase
(`0 < integerSlack s m ≤ 2^(blockSteps s m)`), the product of the odd quotient `u m`
and the positive integer slack `(integerSlack s m).toNat` satisfies the exact
`2^(blockSteps s m)`-canceled bound:
`2^(s m + 1) * u m * (integerSlack s m).toNat < 3^(blockSteps s m + 1) * (2 * a_0 + 1)`. -/
theorem ridout_non_s_part_cancellation
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hle : integerSlack s m ≤ (2 : ℤ) ^ (blockSteps s m)) :
    2 ^ (s m + 1) * u m * (integerSlack s m).toNat <
      3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
  have hslack := integerSlack_eq_orbit_slack hmK hchain
  have hslack' :
      integerSlack s m =
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℤ) := by
    rw [hslack]
    push_cast
    rfl
  have hle' : integerSlack s m ≤ ((2 ^ (blockSteps s m) : ℕ) : ℤ) := by
    simpa using hle
  have hDelta_le : (integerSlack s m).toNat ≤ 2 ^ (blockSteps s m) := by omega
  have horbit_lt :
      2 ^ (blockSteps s (m + 1) + 1) * u m <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
    omega
  have hpow_split :
      2 ^ (blockSteps s (m + 1) + 1) * u m =
        2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) := by
    have hstep : blockSteps s (m + 1) + 1 = blockSteps s m + (s m + 1) := by
      change blockSteps s m + s m + 1 = blockSteps s m + (s m + 1)
      omega
    rw [hstep, Nat.pow_add, mul_assoc]
  rw [hpow_split] at horbit_lt
  have hmul1 :
      2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m * (integerSlack s m).toNat) ≤
        2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) * 2 ^ (blockSteps s m) := by
    have h := Nat.mul_le_mul_left (2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m)) hDelta_le
    linarith
  have hmul2 :
      2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) * 2 ^ (blockSteps s m) <
        2 ^ (blockSteps s m) * (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) := by
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hmul1 hmul2)

/-- **Pinched-Slack Ridout Cancellation Law (`ridout_pinched_slack_cancellation`)**:
More generally, if `0 < integerSlack s m` and
`2^D * (integerSlack s m).toNat ≤ 2^(blockSteps s m)` (a slack pinch of `D` bits below
the ceiling `2^(blockSteps s m)`), then both `s m` and `D` combine additively in the
exponent:
`2^(s m + D + 1) * u m * (integerSlack s m).toNat < 3^(blockSteps s m + 1) * (2 * a_0 + 1)`. -/
theorem ridout_pinched_slack_cancellation
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m D : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hpinch : 2 ^ D * (integerSlack s m).toNat ≤ 2 ^ (blockSteps s m)) :
    2 ^ (s m + D + 1) * u m * (integerSlack s m).toNat <
      3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
  have hslack := integerSlack_eq_orbit_slack hmK hchain
  have hslack' :
      integerSlack s m =
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℤ) := by
    rw [hslack]
    push_cast
    rfl
  have horbit_lt :
      2 ^ (blockSteps s (m + 1) + 1) * u m <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
    omega
  have hpow_split :
      2 ^ (blockSteps s (m + 1) + 1) * u m =
        2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) := by
    have hstep : blockSteps s (m + 1) + 1 = blockSteps s m + (s m + 1) := by
      change blockSteps s m + s m + 1 = blockSteps s m + (s m + 1)
      omega
    rw [hstep, Nat.pow_add, mul_assoc]
  rw [hpow_split] at horbit_lt
  have hpow_D :
      2 ^ (s m + D + 1) * u m * (integerSlack s m).toNat =
        (2 ^ (s m + 1) * u m) * (2 ^ D * (integerSlack s m).toNat) := by
    rw [show s m + D + 1 = (s m + 1) + D by omega, Nat.pow_add]
    ring
  have hmul1 :
      2 ^ (blockSteps s m) * (2 ^ (s m + D + 1) * u m * (integerSlack s m).toNat) ≤
        2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) * 2 ^ (blockSteps s m) := by
    rw [hpow_D, ← mul_assoc]
    exact Nat.mul_le_mul_left (2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m)) hpinch
  have hmul2 :
      2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) * 2 ^ (blockSteps s m) <
        2 ^ (blockSteps s m) * (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) := by
    rw [mul_comm _ (2 ^ (blockSteps s m))]
    exact Nat.mul_lt_mul_of_pos_left horbit_lt (Nat.pow_pos (by decide))
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hmul1 hmul2)

/-! ## 3. The Three-Place (`{∞, 2, 3}`) Ridout Product Bound at `Q_m^(-2)` -/

/-- **Three-Place (`{∞, 2, 3}`) Ridout Product Bound (`ridout_three_place_product_lt`)**:
Let `P_m = 2^(blockSteps s (m + 1) + 1) * u m` and
`Q_m = 3^(blockSteps s m + 1) * (2 * a_0 + 1)`.
Along any `ValidBlockChain a_0 s u K` (`m < K`) in a sub-ceiling phase
(`0 < integerSlack s m ≤ 2^(blockSteps s m)`), the 3-place Ridout product
`(1 - P_m / Q_m) * (u m / P_m) * ((2 * a_0 + 1) / Q_m)`
is strictly bounded above by
`((2 * a_0 + 1) / 2^(s m + 1)) * (1 / (P_m * Q_m))`. -/
theorem ridout_three_place_product_lt
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hle : integerSlack s m ≤ (2 : ℤ) ^ (blockSteps s m)) :
    (1 - ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) /
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ)) *
        ((u m : ℝ) / ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ)) *
        (((2 * a_0 + 1 : ℕ) : ℝ) /
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ)) <
      (((2 * a_0 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (s m + 1)) *
        (1 / (((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) *
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ))) := by
  have hcancel := ridout_non_s_part_cancellation hmK hchain hpos hle
  have hslack := integerSlack_eq_orbit_slack hmK hchain
  have hslack' :
      integerSlack s m =
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℤ) := by
    rw [hslack]
    push_cast
    rfl
  rcases hchain m hmK with ⟨_, hum_odd, _⟩
  have hP_pos_nat : 0 < 2 ^ (blockSteps s (m + 1) + 1) * u m :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hQ_pos_nat : 0 < 3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hP_pos : (0 : ℝ) < ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
    exact_mod_cast hP_pos_nat
  have hQ_pos : (0 : ℝ) < ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hQ_pos_nat
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ (s m + 1) := pow_pos (by norm_num) _
  have hnat :
      2 ^ (blockSteps s (m + 1) + 1) * u m + (integerSlack s m).toNat =
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
    omega
  have hreal :
      ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) +
          ((integerSlack s m).toNat : ℝ) =
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hcancel_real :
      (2 : ℝ) ^ (s m + 1) * (u m : ℝ) * ((integerSlack s m).toNat : ℝ) <
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) := by
    have hcast :
        ((2 ^ (s m + 1) * u m * (integerSlack s m).toNat : ℕ) : ℝ) <
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcancel
    simpa [Nat.cast_mul, Nat.cast_pow] using hcast
  set P : ℝ := ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ)
  set Q : ℝ := ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ)
  set D : ℝ := ((integerSlack s m).toNat : ℝ)
  have hQP_eq : Q - P = D := by linarith
  have h1_sub : 1 - P / Q = D / Q := by
    rw [one_sub_div (ne_of_gt hQ_pos), hQP_eq]
  rw [h1_sub]
  have ha0_pos : (0 : ℝ) < ((2 * a_0 + 1 : ℕ) : ℝ) := by
    have : 0 < 2 * a_0 + 1 := by omega
    exact_mod_cast this
  have hnum_lt :
      D * (u m : ℝ) * ((2 * a_0 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (s m + 1) <
        ((2 * a_0 + 1 : ℕ) : ℝ) * Q := by
    nlinarith
  have hden1_pos : 0 < Q * P * Q := mul_pos (mul_pos hQ_pos hP_pos) hQ_pos
  have hden2_pos : 0 < (2 : ℝ) ^ (s m + 1) * (P * Q) :=
    mul_pos h2s_pos (mul_pos hP_pos hQ_pos)
  have hlhs :
      (D / Q) * ((u m : ℝ) / P) * (((2 * a_0 + 1 : ℕ) : ℝ) / Q) =
        (D * (u m : ℝ) * ((2 * a_0 + 1 : ℕ) : ℝ)) / (Q * P * Q) := by
    ring
  have hrhs :
      (((2 * a_0 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (s m + 1)) * (1 / (P * Q)) =
        ((2 * a_0 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ (s m + 1) * (P * Q)) := by
    ring
  rw [hlhs, hrhs, div_lt_div_iff₀ hden1_pos hden2_pos]
  nlinarith

/-- **Quadratic `Q_m^(-2)` Three-Place Ridout Bound (`ridout_three_place_quadratic_bound`)**:
Combining `ridout_three_place_product_lt` with `global_coprime_width_corridor`
(`P_m > ((6 * a_0 + 2) / (6 * a_0 + 3)) * Q_m` for `1 ≤ m < K`) yields the pure
quadratic `1 / Q_m^2` bound at Ridout's critical exponent `2`:
`(1 - P_m / Q_m) * (u m / P_m) * ((2 * a_0 + 1) / Q_m) <
  ((6 * a_0 + 3) * (2 * a_0 + 1) / (2^(s m + 1) * (6 * a_0 + 2))) * (1 / Q_m^2)`. -/
theorem ridout_three_place_quadratic_bound
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hle : integerSlack s m ≤ (2 : ℤ) ^ (blockSteps s m)) :
    (1 - ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) /
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ)) *
        ((u m : ℝ) / ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ)) *
        (((2 * a_0 + 1 : ℕ) : ℝ) /
          ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ)) <
      (((6 * (a_0 : ℝ) + 3) * (2 * (a_0 : ℝ) + 1)) /
          ((2 : ℝ) ^ (s m + 1) * (6 * (a_0 : ℝ) + 2))) *
        (1 / (((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) ^ 2)) := by
  have hlt1 := ridout_three_place_product_lt hmK hchain hpos hle
  have hcor := (global_coprime_width_corridor hm1 hmK hchain hpos).1
  rcases hchain m hmK with ⟨_, hum_odd, _⟩
  have hP_pos_nat : 0 < 2 ^ (blockSteps s (m + 1) + 1) * u m :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hQ_pos_nat : 0 < 3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hP_pos : (0 : ℝ) < ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
    exact_mod_cast hP_pos_nat
  have hQ_pos : (0 : ℝ) < ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hQ_pos_nat
  have hQ_expand :
      ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ) =
        (3 : ℝ) ^ (blockSteps s m) * (6 * (a_0 : ℝ) + 3) := by
    push_cast
    rw [pow_succ]
    ring
  have hcor_real :
      (3 : ℝ) ^ (blockSteps s m) * (6 * (a_0 : ℝ) + 2) <
        ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) := by
    exact_mod_cast hcor
  set P : ℝ := ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ)
  set Q : ℝ := ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℝ)
  have hPQ_gt :
      (6 * (a_0 : ℝ) + 2) * Q < (6 * (a_0 : ℝ) + 3) * P := by
    rw [hQ_expand]
    nlinarith
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ (s m + 1) := pow_pos (by norm_num) _
  have ha0_2 : (0 : ℝ) < 6 * (a_0 : ℝ) + 2 := by positivity
  have ha0_1 : (0 : ℝ) < 2 * (a_0 : ℝ) + 1 := by positivity
  have hden1_pos : (0 : ℝ) < (2 : ℝ) ^ (s m + 1) * (P * Q) :=
    mul_pos h2s_pos (mul_pos hP_pos hQ_pos)
  have hden2_pos :
      (0 : ℝ) < (2 : ℝ) ^ (s m + 1) * (6 * (a_0 : ℝ) + 2) * Q ^ 2 := by
    positivity
  have hstep2 :
      (((2 * a_0 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (s m + 1)) * (1 / (P * Q)) <
        (((6 * (a_0 : ℝ) + 3) * (2 * (a_0 : ℝ) + 1)) /
            ((2 : ℝ) ^ (s m + 1) * (6 * (a_0 : ℝ) + 2))) *
          (1 / (Q ^ 2)) := by
    have hl :
        (((2 * a_0 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (s m + 1)) * (1 / (P * Q)) =
          (2 * (a_0 : ℝ) + 1) / ((2 : ℝ) ^ (s m + 1) * (P * Q)) := by
      push_cast
      ring
    have hr :
        (((6 * (a_0 : ℝ) + 3) * (2 * (a_0 : ℝ) + 1)) /
            ((2 : ℝ) ^ (s m + 1) * (6 * (a_0 : ℝ) + 2))) *
          (1 / (Q ^ 2)) =
          ((6 * (a_0 : ℝ) + 3) * (2 * (a_0 : ℝ) + 1)) /
            ((2 : ℝ) ^ (s m + 1) * (6 * (a_0 : ℝ) + 2) * Q ^ 2) := by
      rw [div_mul_div_comm, mul_one]
    rw [hl, hr, div_lt_div_iff₀ hden1_pos hden2_pos]
    have hmul_pos : (0 : ℝ) < (2 * (a_0 : ℝ) + 1) * (2 : ℝ) ^ (s m + 1) * Q :=
      mul_pos (mul_pos ha0_1 h2s_pos) hQ_pos
    nlinarith
  exact lt_trans hlt1 hstep2

/-- **Telescoping Approximant Step Difference (`telescoping_approximant_step_difference`)**:
Along any `ValidBlockChain a_0 s u K` (`m + 1 < K`), consecutive rational approximants
`P_m / Q_m = (2^(T(m + 1) + 1) * u m) / 3^(T(m) + 1)` satisfy the exact step identity:
`(2^(blockSteps s (m + 2) + 1) * u (m + 1) : ℝ) / 3^(blockSteps s (m + 1) + 1) -
  (2^(blockSteps s (m + 1) + 1) * u m : ℝ) / 3^(blockSteps s m + 1) =
  (2 / 3 : ℝ)^(blockSteps s (m + 1) + 1)`. -/
theorem telescoping_approximant_step_difference
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1K : m + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    ((2 ^ (blockSteps s (m + 2) + 1) * u (m + 1) : ℕ) : ℝ) /
        (3 : ℝ) ^ (blockSteps s (m + 1) + 1) -
      ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℝ) /
        (3 : ℝ) ^ (blockSteps s m + 1) =
      (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1) := by
  have hd1 := dual_metric_series_identity (by omega : m < K) hchain
  have hd2 := dual_metric_series_identity hm1K hchain
  have hdrain :
      blockDrainSum s (m + 1) =
        blockDrainSum s m + (2 / 3 : ℝ) ^ (blockSteps s (m + 1) + 1) := rfl
  push_cast
  linarith

/-! ## 4. Two-Seed Shared-Prefix Ridout Difference Lock -/

/-- **Two-Seed Shared-Prefix Divisibility Lock (`two_seed_shared_prefix_divisibility`)**:
If two seeds `a_0 ≥ b_0` share the same block sequence `s` up to block `m`
(`ValidBlockChain a_0 s u K` and `ValidBlockChain b_0 s v K` with `m < K`),
then subtracting their orbit slack equations eliminates `integerSlack s m`
completely, yielding:
`3^(blockSteps s m + 1) * (a_0 - b_0) = 2^(blockSteps s (m + 1)) * (u m - v m)`
and consequently `2^(blockSteps s (m + 1)) ∣ (a_0 - b_0)`. -/
theorem two_seed_shared_prefix_divisibility
    {a_0 b_0 : ℕ} {s u v : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hab : b_0 ≤ a_0)
    (hchain_a : ValidBlockChain a_0 s u K)
    (hchain_b : ValidBlockChain b_0 s v K) :
    3 ^ (blockSteps s m + 1) * (a_0 - b_0) =
        2 ^ (blockSteps s (m + 1)) * (u m - v m) ∧
      2 ^ (blockSteps s (m + 1)) ∣ (a_0 - b_0) := by
  have hsa := integerSlack_eq_orbit_slack hmK hchain_a
  have hsb := integerSlack_eq_orbit_slack hmK hchain_b
  have heq_int :
      (3 : ℤ) ^ (blockSteps s m + 1) * (2 * (a_0 : ℤ) + 1) -
          (2 : ℤ) ^ (blockSteps s (m + 1) + 1) * (u m : ℤ) =
        (3 : ℤ) ^ (blockSteps s m + 1) * (2 * (b_0 : ℤ) + 1) -
          (2 : ℤ) ^ (blockSteps s (m + 1) + 1) * (v m : ℤ) := by
    rw [← hsa, ← hsb]
  have hpow2 :
      (2 : ℤ) ^ (blockSteps s (m + 1) + 1) =
        2 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    rw [pow_succ']
  rw [hpow2] at heq_int
  have hdiff_int :
      (3 : ℤ) ^ (blockSteps s m + 1) * ((a_0 : ℤ) - (b_0 : ℤ)) =
        (2 : ℤ) ^ (blockSteps s (m + 1)) * ((u m : ℤ) - (v m : ℤ)) := by
    linarith
  have hv_le_u : v m ≤ u m := by
    have hpos2 : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1)) :=
      pow_pos (by decide) _
    have hnonneg : (0 : ℤ) ≤ (3 : ℤ) ^ (blockSteps s m + 1) * ((a_0 : ℤ) - (b_0 : ℤ)) :=
      mul_nonneg (pow_nonneg (by decide) _) (by omega)
    rw [hdiff_int] at hnonneg
    have hsub_nonneg : (0 : ℤ) ≤ (u m : ℤ) - (v m : ℤ) :=
      nonneg_of_mul_nonneg_right hnonneg hpos2
    omega
  have hcast_eq :
      ((3 ^ (blockSteps s m + 1) * (a_0 - b_0) : ℕ) : ℤ) =
        ((2 ^ (blockSteps s (m + 1)) * (u m - v m) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hab, Nat.cast_sub hv_le_u]
    exact hdiff_int
  have hdiff_nat :
      3 ^ (blockSteps s m + 1) * (a_0 - b_0) =
        2 ^ (blockSteps s (m + 1)) * (u m - v m) := by
    exact_mod_cast hcast_eq
  refine ⟨hdiff_nat, ?_⟩
  have hcop : Nat.Coprime (2 ^ (blockSteps s (m + 1))) (3 ^ (blockSteps s m + 1)) :=
    (Nat.Coprime.pow (blockSteps s (m + 1)) (blockSteps s m + 1) (by decide))
  have hdvd_mul :
      2 ^ (blockSteps s (m + 1)) ∣ 3 ^ (blockSteps s m + 1) * (a_0 - b_0) :=
    ⟨u m - v m, hdiff_nat⟩
  exact hcop.dvd_of_dvd_mul_left hdvd_mul

/-- **Mahler Two-Seed Same-Step Ridout Corridor (`mahler_two_seed_same_step_ridout_bound`)**:
If two seeds `a_0, b_0` with `ValidBlockChain a_0 s1 u1 K1` (`m1 < K1`) and
`ValidBlockChain b_0 s2 u2 K2` (`m2 < K2`) reach the same cumulative step count
`T = blockSteps s1 m1 = blockSteps s2 m2` in sub-ceiling phases
(`0 < integerSlack s1 m1 ≤ 2^T` and `0 < integerSlack s2 m2 ≤ 2^T`), then
`|(3 : ℤ)^(T + 1) * (2 * (a_0 : ℤ) - 2 * (b_0 : ℤ)) -
  (2 : ℤ)^(T + 1) * ((2 : ℤ)^(s1 m1) * (u1 m1 : ℤ) - (2 : ℤ)^(s2 m2) * (u2 m2 : ℤ))| <
  (2 : ℤ)^T`. -/
theorem mahler_two_seed_same_step_ridout_bound
    {a_0 b_0 : ℕ} {s1 u1 s2 u2 : ℕ → ℕ} {K1 m1 K2 m2 T : ℕ}
    (hm1K : m1 < K1) (hm2K : m2 < K2)
    (hchain1 : ValidBlockChain a_0 s1 u1 K1)
    (hchain2 : ValidBlockChain b_0 s2 u2 K2)
    (hT1 : blockSteps s1 m1 = T) (hT2 : blockSteps s2 m2 = T)
    (hpos1 : 0 < integerSlack s1 m1) (hle1 : integerSlack s1 m1 ≤ (2 : ℤ) ^ T)
    (hpos2 : 0 < integerSlack s2 m2) (hle2 : integerSlack s2 m2 ≤ (2 : ℤ) ^ T) :
    |(3 : ℤ) ^ (T + 1) * (2 * (a_0 : ℤ) - 2 * (b_0 : ℤ)) -
        (2 : ℤ) ^ (T + 1) *
          ((2 : ℤ) ^ (s1 m1) * (u1 m1 : ℤ) - (2 : ℤ) ^ (s2 m2) * (u2 m2 : ℤ))| <
      (2 : ℤ) ^ T := by
  have hs1 := integerSlack_eq_orbit_slack hm1K hchain1
  have hs2 := integerSlack_eq_orbit_slack hm2K hchain2
  have hstep1 : blockSteps s1 (m1 + 1) + 1 = (T + 1) + s1 m1 := by
    change blockSteps s1 m1 + s1 m1 + 1 = (T + 1) + s1 m1
    omega
  have hstep2 : blockSteps s2 (m2 + 1) + 1 = (T + 1) + s2 m2 := by
    change blockSteps s2 m2 + s2 m2 + 1 = (T + 1) + s2 m2
    omega
  rw [hT1, hstep1, pow_add (2 : ℤ) (T + 1)] at hs1
  rw [hT2, hstep2, pow_add (2 : ℤ) (T + 1)] at hs2
  have hdiff :
      (3 : ℤ) ^ (T + 1) * (2 * (a_0 : ℤ) - 2 * (b_0 : ℤ)) -
          (2 : ℤ) ^ (T + 1) *
            ((2 : ℤ) ^ (s1 m1) * (u1 m1 : ℤ) - (2 : ℤ) ^ (s2 m2) * (u2 m2 : ℤ)) =
        integerSlack s1 m1 - integerSlack s2 m2 := by
    linarith
  rw [hdiff, abs_lt]
  constructor <;> linarith

end Mahler.RidoutSubspace
