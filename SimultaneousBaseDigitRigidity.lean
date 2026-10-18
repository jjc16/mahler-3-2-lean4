import RepeatedSubwordComplexity

/-!
# Simultaneous Base-2 / Base-3 Digit Rigidity, Carryless Prefix Equivalence & Dual Remainder Law

This module formalizes Path 2: the simultaneous Base-2 and Base-3 digit structure
of `P_m = 2^(blockSteps s (m + 1) + 1) * u m` and
`Q_m = 3^(blockSteps s m + 1) * (2 * a_0 + 1)`:

1. **Base-3 Shift-and-Add Recurrence for `P_m`
   (`scaled_quotient_base_three_shift_recurrence`)**:
   Along any `ValidBlockChain a_0 s u K` (`m + 1 < K`),
   `2^(blockSteps s (m + 2) + 1) * u (m + 1) =
     3^(s m) * (2^(blockSteps s (m + 1) + 1) * u m) + 2^(blockSteps s (m + 1) + 1)`.
   In base 3, advancing one block shifts `P_m` left by `s m` ternary digits and
   adds `2^(T(m + 1) + 1)`.
2. **Unconditional Global Base-3 Addition Identity
   (`unconditional_global_coprime_addition_identity`)**:
   Along **every** `ValidBlockChain a_0 s u K` (`m < K`, requiring no slack
   positivity hypothesis),
   `2^(blockSteps s (m + 1) + 1) * u m =
     3^(blockSteps s m) * (6 * a_0 + 2) + 2^(s 0 + 1) * coprimeRemainder s m`.
3. **Two-Way Base-3 Frozen-Prefix Equivalence & Carry Overflow Law
   (`integerSlack_pos_iff_base_three_prefix_frozen`,
   `integerSlack_nonpos_iff_base_three_carry_overflow`)**:
   - `0 < integerSlack s m ↔ (2^(blockSteps s (m + 1) + 1) * u m) / 3^(blockSteps s m) = 6 * a_0 + 2`.
   - `integerSlack s m ≤ 0 ↔ 6 * a_0 + 3 ≤ (2^(blockSteps s (m + 1) + 1) * u m) / 3^(blockSteps s m)`.
   Thus archimedean survival at block `m` is equivalent to the absence of a base-3
   carry into the `3^(T(m))` place.
4. **Carryless Multi-Origin Characterization of `0 < minSlack s m`
   (`minSlack_pos_iff_all_shifted_base_three_prefixes_frozen`)**:
   `0 < minSlack s m` holds if and only if for every origin `j ≤ m`, the base-3
   quotient of `2^(blockSteps (shiftSeq s j) (m - j + 1) + 1) * u m` by
   `3^(blockSteps (shiftSeq s j) (m - j))` is frozen at `6 * orbit a_0 (blockSteps s j) + 2`.
5. **Dual Base-2 / Base-3 Remainder Complement Law
   (`dual_base_two_base_three_remainder_complement_law`)**:
   In any sub-ceiling phase (`0 < integerSlack s m < 2^(blockSteps s m)`), the
   Base-3 remainder of `P_m` modulo `3^(T(m))` and the Base-2 remainder of `Q_m`
   modulo `2^(T(m))` sum to exact `3^(T(m))`:
   `((2^(blockSteps s (m + 1) + 1) * u m) % 3^(blockSteps s m)) +
     ((3^(blockSteps s m + 1) * (2 * a_0 + 1)) % 2^(blockSteps s m)) =
     3^(blockSteps s m)`.
-/

namespace Mahler.SimultaneousBaseDigits

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

/-! ## 1. Base-3 Shift-and-Add Recurrence for `P_m = 2^(T(m + 1) + 1) * u m` -/

/-- **Base-3 Shift-and-Add Recurrence (`scaled_quotient_base_three_shift_recurrence`)**:
Along any `ValidBlockChain a_0 s u K` (`m + 1 < K`),
`2^(blockSteps s (m + 2) + 1) * u (m + 1) =
  3^(s m) * (2^(blockSteps s (m + 1) + 1) * u m) + 2^(blockSteps s (m + 1) + 1)`. -/
theorem scaled_quotient_base_three_shift_recurrence
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1K : m + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (blockSteps s (m + 2) + 1) * u (m + 1) =
      3 ^ (s m) * (2 ^ (blockSteps s (m + 1) + 1) * u m) +
        2 ^ (blockSteps s (m + 1) + 1) := by
  have hrec := coprime_quotient_recurrence hm1K hchain
  have hstep :
      blockSteps s (m + 2) + 1 = (blockSteps s (m + 1) + 1) + s (m + 1) := by
    change blockSteps s (m + 1) + s (m + 1) + 1 = (blockSteps s (m + 1) + 1) + s (m + 1)
    omega
  rw [hstep, Nat.pow_add, mul_assoc, hrec]
  ring

/-! ## 2. Unconditional Global Base-3 Addition Identity -/

/-- **Unconditional Global Base-3 Addition Identity
(`unconditional_global_coprime_addition_identity`)**:
Along **every** `ValidBlockChain a_0 s u K` (`m < K`, requiring no positivity
assumption on `integerSlack s m`),
`2^(blockSteps s (m + 1) + 1) * u m =
  3^(blockSteps s m) * (6 * a_0 + 2) + 2^(s 0 + 1) * coprimeRemainder s m`. -/
theorem unconditional_global_coprime_addition_identity
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (blockSteps s (m + 1) + 1) * u m =
      3 ^ (blockSteps s m) * (6 * a_0 + 2) +
        2 ^ (s 0 + 1) * coprimeRemainder s m := by
  have horbit := integerSlack_eq_orbit_slack hmK hchain
  have hdef :
      integerSlack s m =
        (3 : ℤ) ^ (blockSteps s m) -
          (2 : ℤ) ^ (s 0 + 1) * (coprimeRemainder s m : ℤ) := rfl
  have hpow3 :
      (3 : ℤ) ^ (blockSteps s m + 1) * (2 * (a_0 : ℤ) + 1) =
        (3 : ℤ) ^ (blockSteps s m) * (6 * (a_0 : ℤ) + 2) +
          (3 : ℤ) ^ (blockSteps s m) := by
    rw [pow_succ]
    ring
  have heq_int :
      ((2 ^ (blockSteps s (m + 1) + 1) * u m : ℕ) : ℤ) =
        ((3 ^ (blockSteps s m) * (6 * a_0 + 2) +
          2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast heq_int

/-! ## 3. Two-Way Base-3 Frozen-Prefix Equivalence & Carry Overflow Law -/

/-- **Two-Way Base-3 Frozen-Prefix Equivalence (`integerSlack_pos_iff_base_three_prefix_frozen`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`),
`0 < integerSlack s m ↔
  (2^(blockSteps s (m + 1) + 1) * u m) / 3^(blockSteps s m) = 6 * a_0 + 2`. -/
theorem integerSlack_pos_iff_base_three_prefix_frozen
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    0 < integerSlack s m ↔
      (2 ^ (blockSteps s (m + 1) + 1) * u m) / 3 ^ (blockSteps s m) =
        6 * a_0 + 2 := by
  constructor
  · intro hpos
    exact (global_coprime_div_mod_lock hmK hchain hpos).1
  · intro hdiv
    have hid := unconditional_global_coprime_addition_identity hmK hchain
    have h3_pos : 0 < 3 ^ (blockSteps s m) := Nat.pow_pos (by decide)
    have hdiv_add :
        (3 ^ (blockSteps s m) * (6 * a_0 + 2) +
            2 ^ (s 0 + 1) * coprimeRemainder s m) /
          3 ^ (blockSteps s m) =
          6 * a_0 + 2 +
            (2 ^ (s 0 + 1) * coprimeRemainder s m) / 3 ^ (blockSteps s m) := by
      rw [Nat.add_comm (3 ^ (blockSteps s m) * (6 * a_0 + 2)),
        Nat.add_mul_div_left _ _ h3_pos, Nat.add_comm]
    rw [hid, hdiv_add] at hdiv
    have hrem_div_zero :
        (2 ^ (s 0 + 1) * coprimeRemainder s m) / 3 ^ (blockSteps s m) = 0 := by
      omega
    have hlt : 2 ^ (s 0 + 1) * coprimeRemainder s m < 3 ^ (blockSteps s m) :=
      (Nat.div_eq_zero_iff.mp hrem_div_zero).resolve_left (by omega)
    exact (integerSlack_pos_iff_tail_budget s m).mpr hlt

/-- **Base-3 Carry Overflow Characterization of Slack Exhaustion
(`integerSlack_nonpos_iff_base_three_carry_overflow`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`), the slack is exhausted
(`integerSlack s m ≤ 0`) if and only if a base-3 carry overflows across `3^(T(m))`:
`integerSlack s m ≤ 0 ↔
  6 * a_0 + 3 ≤ (2^(blockSteps s (m + 1) + 1) * u m) / 3^(blockSteps s m)`. -/
theorem integerSlack_nonpos_iff_base_three_carry_overflow
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    integerSlack s m ≤ 0 ↔
      6 * a_0 + 3 ≤
        (2 ^ (blockSteps s (m + 1) + 1) * u m) / 3 ^ (blockSteps s m) := by
  have hid := unconditional_global_coprime_addition_identity hmK hchain
  have h3_pos : 0 < 3 ^ (blockSteps s m) := Nat.pow_pos (by decide)
  have hdiv_add :
      (2 ^ (blockSteps s (m + 1) + 1) * u m) / 3 ^ (blockSteps s m) =
        6 * a_0 + 2 +
          (2 ^ (s 0 + 1) * coprimeRemainder s m) / 3 ^ (blockSteps s m) := by
    rw [hid, Nat.add_comm (3 ^ (blockSteps s m) * (6 * a_0 + 2)),
      Nat.add_mul_div_left _ _ h3_pos, Nat.add_comm]
  rw [hdiv_add]
  have hdef :
      integerSlack s m =
        ((3 ^ (blockSteps s m) : ℕ) : ℤ) -
          ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) := by
    unfold integerSlack
    push_cast
    rfl
  constructor
  · intro hle
    have hge : 3 ^ (blockSteps s m) ≤ 2 ^ (s 0 + 1) * coprimeRemainder s m := by
      omega
    have hdiv_pos :
        1 ≤ (2 ^ (s 0 + 1) * coprimeRemainder s m) / 3 ^ (blockSteps s m) :=
      Nat.div_pos hge h3_pos
    omega
  · intro hge
    have hdiv_pos :
        1 ≤ (2 ^ (s 0 + 1) * coprimeRemainder s m) / 3 ^ (blockSteps s m) := by
      omega
    have hlt_not : ¬ (2 ^ (s 0 + 1) * coprimeRemainder s m < 3 ^ (blockSteps s m)) := by
      intro hlt
      have h0 : (2 ^ (s 0 + 1) * coprimeRemainder s m) / 3 ^ (blockSteps s m) = 0 :=
        Nat.div_eq_zero_iff.mpr (Or.inr hlt)
      omega
    omega

/-! ## 4. Carryless Multi-Origin Characterization of `0 < minSlack s m` -/

/-- **Carryless Multi-Origin Characterization of `0 < minSlack s m`
(`minSlack_pos_iff_all_shifted_base_three_prefixes_frozen`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`), `0 < minSlack s m` holds if and
only if for every origin `j ≤ m`, the base-3 prefix of
`2^(blockSteps (shiftSeq s j) (m - j + 1) + 1) * u m` above
`3^(blockSteps (shiftSeq s j) (m - j))` is frozen at `6 * orbit a_0 (blockSteps s j) + 2`. -/
theorem minSlack_pos_iff_all_shifted_base_three_prefixes_frozen
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    0 < minSlack s m ↔
      ∀ j ≤ m,
        (2 ^ (blockSteps (shiftSeq s j) (m - j + 1) + 1) * u m) /
            3 ^ (blockSteps (shiftSeq s j) (m - j)) =
          6 * orbit a_0 (blockSteps s j) + 2 := by
  rw [minSlack_pos_iff_all_shifted_pos]
  constructor
  · intro hall j hjm
    have hchain_sub : ValidBlockChain a_0 s u (j + (K - j)) := by
      rw [show j + (K - j) = K by omega]
      exact hchain
    have hchain_shift := validBlockChain_shift hchain_sub
    have hiff :=
      integerSlack_pos_iff_base_three_prefix_frozen (m := m - j) (by omega) hchain_shift
    have hpos := hall j hjm
    have hdiv := hiff.mp hpos
    have hu_eq : shiftSeq u j (m - j) = u m := by
      simp only [shiftSeq]
      congr 1
      omega
    rw [hu_eq] at hdiv
    exact hdiv
  · intro hall j hjm
    have hchain_sub : ValidBlockChain a_0 s u (j + (K - j)) := by
      rw [show j + (K - j) = K by omega]
      exact hchain
    have hchain_shift := validBlockChain_shift hchain_sub
    have hiff :=
      integerSlack_pos_iff_base_three_prefix_frozen (m := m - j) (by omega) hchain_shift
    have hdiv := hall j hjm
    have hu_eq : shiftSeq u j (m - j) = u m := by
      simp only [shiftSeq]
      congr 1
      omega
    rw [← hu_eq] at hdiv
    exact hiff.mpr hdiv

/-! ## 5. Dual Base-2 / Base-3 Remainder Complement Law -/

/-- **Dual Base-2 / Base-3 Remainder Complement Law
(`dual_base_two_base_three_remainder_complement_law`)**:
Along any `ValidBlockChain a_0 s u K` (`m < K`) in a sub-ceiling phase
(`0 < integerSlack s m < 2^(blockSteps s m)`), the Base-3 remainder of
`P_m = 2^(blockSteps s (m + 1) + 1) * u m` modulo `3^(blockSteps s m)` and the
Base-2 remainder of `Q_m = 3^(blockSteps s m + 1) * (2 * a_0 + 1)` modulo
`2^(blockSteps s m)` sum to exact `3^(blockSteps s m)`:
`((2^(blockSteps s (m + 1) + 1) * u m) % 3^(blockSteps s m)) +
  ((3^(blockSteps s m + 1) * (2 * a_0 + 1)) % 2^(blockSteps s m)) =
  3^(blockSteps s m)`. -/
theorem dual_base_two_base_three_remainder_complement_law
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hlt : integerSlack s m < (2 : ℤ) ^ (blockSteps s m)) :
    (2 ^ (blockSteps s (m + 1) + 1) * u m) % 3 ^ (blockSteps s m) +
        (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) % 2 ^ (blockSteps s m) =
      3 ^ (blockSteps s m) := by
  have hmod3 := (global_coprime_div_mod_lock hmK hchain hpos).2
  have hmod2 := (base_two_div_mod_lock hmK hchain hpos hlt).2
  rw [hmod3, hmod2]
  have hdef :
      integerSlack s m =
        ((3 ^ (blockSteps s m) : ℕ) : ℤ) -
          ((2 ^ (s 0 + 1) * coprimeRemainder s m : ℕ) : ℤ) := by
    unfold integerSlack
    push_cast
    rfl
  omega

/-- **Companion Existence ↔ All Historical Base-3 Prefixes Frozen
(`exists_validCompanionUpTo_iff_base_three_prefixes_frozen`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ K`), a real Mahler companion `ξ ∈ ℝ`
surviving through step `blockSteps s K` exists **if and only if** the terminal
odd quotient `u (K - 1)` recovers every historical orbit value
`6 * orbit a_0 (blockSteps s j) + 2` (`0 ≤ j ≤ K - 1`) via integer division by
`3^(blockSteps (shiftSeq s j) (K - 1 - j))`. -/
theorem exists_validCompanionUpTo_iff_base_three_prefixes_frozen
    {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hK : 1 ≤ K) (hchain : ValidBlockChain a_0 s u K) :
    (∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s K)) ↔
      ∀ j ≤ K - 1,
        (2 ^ (blockSteps (shiftSeq s j) (K - 1 - j + 1) + 1) * u (K - 1)) /
            3 ^ (blockSteps (shiftSeq s j) (K - 1 - j)) =
          6 * orbit a_0 (blockSteps s j) + 2 := by
  rw [exists_validCompanionUpTo_iff_minSlack_pos hK hchain,
    minSlack_pos_iff_all_shifted_base_three_prefixes_frozen (by omega : K - 1 < K) hchain]

end Mahler.SimultaneousBaseDigits
