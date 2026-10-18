import SimultaneousBaseDigitRigidity

/-!
# Multi-Step Quotient GCD Identity, Two-Step `(3^s + 2^s)` Sieve & Reduced-Height Barrier

This module formalizes Path 3 (Modules 99–100): the exact multi-step GCD laws
for the odd coprime quotients `u r` and `u (r + d)`, their specialization to
2-step transitions `3^(s (k + 1)) + 2^(s (k + 1))`, and the exponential lower
bound on the reduced denominator `u r / Nat.gcd (u r) (u (r + d))` (Dead End 17):

1. **Exact Three-Way Multi-Step GCD Identity
   (`multi_step_u_gcd_eq_gcd_coprimeRemainder`)**:
   Along any `ValidBlockChain a_0 s u K` (`r + d < K`), because `u r` is coprime
   to `2` and `u (r + d)` is coprime to `3`, the `d`-step recurrence
   `2^(tailSteps (shiftSeq s r) d) * u (r + d) =
     3^(blockSteps (shiftSeq s r) d) * u r + coprimeRemainder (shiftSeq s r) d`
   yields the exact GCD equalities:
   `Nat.gcd (u r) (u (r + d)) = Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d)`
   and
   `Nat.gcd (u r) (u (r + d)) = Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d)`.
2. **Exact Two-Step GCD Formula via `3^(s (k + 1)) + 2^(s (k + 1))`
   (`two_step_u_gcd_eq_fermat_sum`, `two_step_u_gcd_at_small_blocks`)**:
   - Across any two blocks `k → k + 2` (`k + 2 < K`),
     `Nat.gcd (u k) (u (k + 2)) = Nat.gcd (u k) (3^(s (k + 1)) + 2^(s (k + 1)))`.
   - In particular:
     - When `s (k + 1) = 2`, `Nat.gcd (u k) (u (k + 2)) ∣ 13` (a prime!).
     - When `s (k + 1) = 3`, `Nat.gcd (u k) (u (k + 2)) ∣ 35`.
     - When `s (k + 1) = 4`, `Nat.gcd (u k) (u (k + 2)) ∣ 97` (a prime!).
3. **Upper Bound on Multi-Step GCD & Dead End 17 — Exponential Growth of the
   Reduced Denominator `u r / gcd(u r, u (r + d))`
   (`multi_step_u_gcd_upper_bound`,
   `multi_step_reduced_denominator_exponential_lower_bound`)**:
   - Whenever `1 ≤ d`, `r + d < K`, and `0 < integerSlack (shiftSeq s r) d`,
     `2^(s r + 1) * Nat.gcd (u r) (u (r + d)) < 3^(blockSteps (shiftSeq s r) d)`.
   - Consequently, even after canceling `Nat.gcd (u r) (u (r + d))` from the
     fraction `u (r + d) / u r`, the reduced denominator
     `u r / Nat.gcd (u r) (u (r + d))` still grows exponentially with `T(r)`:
     `3^(blockSteps s r) * (3 * a_0 + 1) <
       2^(blockSteps s r) * 3^(blockSteps (shiftSeq s r) d) *
         (u r / Nat.gcd (u r) (u (r + d)))`.
-/

namespace Mahler.MultiStepGCD

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

/-! ## 1. Exact Three-Way Multi-Step GCD Identity -/

/-- **Exact Three-Way Multi-Step GCD Identity (`multi_step_u_gcd_eq_gcd_coprimeRemainder`)**:
Along any `ValidBlockChain a_0 s u K` (`r + d < K`),
`Nat.gcd (u r) (u (r + d)) = Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d)`
and
`Nat.gcd (u r) (u (r + d)) = Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d)`. -/
theorem multi_step_u_gcd_eq_gcd_coprimeRemainder
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hrd : r + d < K) (hchain : ValidBlockChain a_0 s u K) :
    Nat.gcd (u r) (u (r + d)) =
        Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d) ∧
      Nat.gcd (u r) (u (r + d)) =
        Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d) := by
  have hid := shifted_coprime_quotient_m_step_identity hrd hchain
  have hur_odd : u r % 2 = 1 := (hchain r (by omega)).2.1
  have hur_cop2 : Nat.Coprime (u r) (2 ^ (tailSteps (shiftSeq s r) d)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)))
  have hurd_cop6 := u_coprime_six_of_validBlockChain hrd hchain
  have hurd_mod3 : u (r + d) % 3 ≠ 0 := hurd_cop6.2.1
  have hurd_cop3 :
      Nat.Coprime (u (r + d)) (3 ^ (blockSteps (shiftSeq s r) d)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)))
  constructor
  · apply Nat.dvd_antisymm
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        (multi_step_u_gcd_dvd_coprimeRemainder hrd hchain)
    · have hdvd_ur :
          Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d) ∣
            3 ^ (blockSteps (shiftSeq s r) d) * u r :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
      have hdvd_R :
          Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d) ∣
            coprimeRemainder (shiftSeq s r) d :=
        Nat.gcd_dvd_right _ _
      have hdvd_sum :
          Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d) ∣
            2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) := by
        rw [hid]
        exact Nat.dvd_add hdvd_ur hdvd_R
      have hcop_gcd :
          Nat.Coprime (Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d))
            (2 ^ (tailSteps (shiftSeq s r) d)) :=
        hur_cop2.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      have hdvd_urd :
          Nat.gcd (u r) (coprimeRemainder (shiftSeq s r) d) ∣ u (r + d) :=
        hcop_gcd.dvd_of_dvd_mul_left hdvd_sum
      exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hdvd_urd
  · apply Nat.dvd_antisymm
    · exact Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
        (multi_step_u_gcd_dvd_coprimeRemainder hrd hchain)
    · have hdvd_urd :
          Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d) ∣
            2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
      have hdvd_R :
          Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d) ∣
            coprimeRemainder (shiftSeq s r) d :=
        Nat.gcd_dvd_right _ _
      rw [hid] at hdvd_urd
      have hdvd_3ur :
          Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d) ∣
            3 ^ (blockSteps (shiftSeq s r) d) * u r :=
        (Nat.dvd_add_left hdvd_R).mp hdvd_urd
      have hcop_gcd :
          Nat.Coprime (Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d))
            (3 ^ (blockSteps (shiftSeq s r) d)) :=
        hurd_cop3.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      have hdvd_ur :
          Nat.gcd (u (r + d)) (coprimeRemainder (shiftSeq s r) d) ∣ u r :=
        hcop_gcd.dvd_of_dvd_mul_left hdvd_3ur
      exact Nat.dvd_gcd hdvd_ur (Nat.gcd_dvd_left _ _)

/-! ## 2. Exact Two-Step GCD Formula via `3^(s (k + 1)) + 2^(s (k + 1))` -/

/-- Exact evaluation of `coprimeRemainder t 2`:
`coprimeRemainder t 2 = 3^(t 1) + 2^(t 1)`. -/
theorem coprimeRemainder_two_eq (t : ℕ → ℕ) :
    coprimeRemainder t 2 = 3 ^ (t 1) + 2 ^ (t 1) := by
  simp [coprimeRemainder, tailSteps]

/-- **Two-Step Quotient GCD Formula (`two_step_u_gcd_eq_fermat_sum`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`),
`Nat.gcd (u k) (u (k + 2)) = Nat.gcd (u k) (3^(s (k + 1)) + 2^(s (k + 1)))`
and
`Nat.gcd (u k) (u (k + 2)) = Nat.gcd (u (k + 2)) (3^(s (k + 1)) + 2^(s (k + 1)))`. -/
theorem two_step_u_gcd_eq_fermat_sum
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K) :
    Nat.gcd (u k) (u (k + 2)) =
        Nat.gcd (u k) (3 ^ (s (k + 1)) + 2 ^ (s (k + 1))) ∧
      Nat.gcd (u k) (u (k + 2)) =
        Nat.gcd (u (k + 2)) (3 ^ (s (k + 1)) + 2 ^ (s (k + 1))) := by
  have hgcd := multi_step_u_gcd_eq_gcd_coprimeRemainder (r := k) (d := 2) hk2 hchain
  have hR2 : coprimeRemainder (shiftSeq s k) 2 = 3 ^ (s (k + 1)) + 2 ^ (s (k + 1)) := by
    rw [coprimeRemainder_two_eq]
    rfl
  rw [hR2] at hgcd
  exact hgcd

/-- **Explicit Small-Block Two-Step GCD Divisibility (`two_step_u_gcd_at_small_blocks`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`):
1. If `s (k + 1) = 2`, then `Nat.gcd (u k) (u (k + 2)) ∣ 13`.
2. If `s (k + 1) = 3`, then `Nat.gcd (u k) (u (k + 2)) ∣ 35`.
3. If `s (k + 1) = 4`, then `Nat.gcd (u k) (u (k + 2)) ∣ 97`. -/
theorem two_step_u_gcd_at_small_blocks
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K) :
    (s (k + 1) = 2 → Nat.gcd (u k) (u (k + 2)) ∣ 13) ∧
      (s (k + 1) = 3 → Nat.gcd (u k) (u (k + 2)) ∣ 35) ∧
      (s (k + 1) = 4 → Nat.gcd (u k) (u (k + 2)) ∣ 97) := by
  have hgcd := (two_step_u_gcd_eq_fermat_sum hk2 hchain).1
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    rw [hgcd, hs]
    simpa using (Nat.gcd_dvd_right (u k) 13)
  · intro hs
    rw [hgcd, hs]
    simpa using (Nat.gcd_dvd_right (u k) 35)
  · intro hs
    rw [hgcd, hs]
    simpa using (Nat.gcd_dvd_right (u k) 97)

/-! ## 3. Multi-Step GCD Upper Bound & Dead End 17: Reduced-Denominator Exponential Growth -/

/-- **Multi-Step GCD Upper Bound (`multi_step_u_gcd_upper_bound`)**:
Along any `ValidBlockChain a_0 s u K` with `1 ≤ d`, `r + d < K`, and
`0 < integerSlack (shiftSeq s r) d`,
`Nat.gcd (u r) (u (r + d)) ≤ coprimeRemainder (shiftSeq s r) d` and
`2^(s r + 1) * Nat.gcd (u r) (u (r + d)) < 3^(blockSteps (shiftSeq s r) d)`. -/
theorem multi_step_u_gcd_upper_bound
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack_shift : 0 < integerSlack (shiftSeq s r) d) :
    Nat.gcd (u r) (u (r + d)) ≤ coprimeRemainder (shiftSeq s r) d ∧
      2 ^ (s r + 1) * Nat.gcd (u r) (u (r + d)) <
        3 ^ (blockSteps (shiftSeq s r) d) := by
  have hdvd := multi_step_u_gcd_dvd_coprimeRemainder hrd hchain
  have hR_pos := coprimeRemainder_pos (shiftSeq s r) hd
  have hle : Nat.gcd (u r) (u (r + d)) ≤ coprimeRemainder (shiftSeq s r) d :=
    Nat.le_of_dvd hR_pos hdvd
  have hbudget := (integerSlack_pos_iff_tail_budget (shiftSeq s r) d).mp hslack_shift
  have hshift0 : shiftSeq s r 0 = s r := rfl
  rw [hshift0] at hbudget
  have hmul_le :
      2 ^ (s r + 1) * Nat.gcd (u r) (u (r + d)) ≤
        2 ^ (s r + 1) * coprimeRemainder (shiftSeq s r) d :=
    Nat.mul_le_mul_left _ hle
  exact ⟨hle, lt_of_le_of_lt hmul_le hbudget⟩

/-- **Dead End 17 — Exponential Lower Bound on Reduced Denominator
(`multi_step_reduced_denominator_exponential_lower_bound`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ r`, `1 ≤ d`, `r + d < K`) with
`0 < integerSlack s r` and `0 < integerSlack (shiftSeq s r) d`, even after canceling
`G = Nat.gcd (u r) (u (r + d))` from `u (r + d) / u r`, the reduced denominator
`u r / Nat.gcd (u r) (u (r + d))` still grows exponentially with `T(r)`:
`3^(blockSteps s r) * (3 * a_0 + 1) <
  2^(blockSteps s r) * 3^(blockSteps (shiftSeq s r) d) *
    (u r / Nat.gcd (u r) (u (r + d)))`. -/
theorem multi_step_reduced_denominator_exponential_lower_bound
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hr1 : 1 ≤ r) (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack_r : 0 < integerSlack s r)
    (hslack_shift : 0 < integerSlack (shiftSeq s r) d) :
    3 ^ (blockSteps s r) * (3 * a_0 + 1) <
      2 ^ (blockSteps s r) * 3 ^ (blockSteps (shiftSeq s r) d) *
        (u r / Nat.gcd (u r) (u (r + d))) := by
  have hgrow := exponential_height_growth_of_u hr1 (by omega : r < K) hchain hslack_r
  have hgcd_lt :=
    (multi_step_u_gcd_upper_bound hd hrd hchain hslack_shift).2
  set G := Nat.gcd (u r) (u (r + d))
  have hG_dvd : G ∣ u r := Nat.gcd_dvd_left (u r) (u (r + d))
  have hur_eq : u r = G * (u r / G) := (Nat.mul_div_cancel' hG_dvd).symm
  have hur_pos : 0 < u r := by
    have hodd := (hchain r (by omega)).2.1
    omega
  have hquot_pos : 0 < u r / G := by
    by_contra h0
    have hq0 : u r / G = 0 := Nat.eq_zero_of_not_pos h0
    rw [hq0, mul_zero] at hur_eq
    omega
  have h2sr_lt :
      2 ^ (s r) * G < 3 ^ (blockSteps (shiftSeq s r) d) := by
    have hle : 2 ^ (s r) * G ≤ 2 ^ (s r + 1) * G :=
      Nat.mul_le_mul_right G (Nat.pow_le_pow_right (by decide) (by omega))
    exact lt_of_le_of_lt hle hgcd_lt
  have hstep_le :
      2 ^ (blockSteps s r) * (2 ^ (s r) * u r) <
        2 ^ (blockSteps s r) * 3 ^ (blockSteps (shiftSeq s r) d) * (u r / G) := by
    have hmul_q :
        (2 ^ (s r) * G) * (u r / G) <
          3 ^ (blockSteps (shiftSeq s r) d) * (u r / G) :=
      Nat.mul_lt_mul_of_pos_right h2sr_lt hquot_pos
    have h2T_pos : 0 < 2 ^ (blockSteps s r) := Nat.pow_pos (by decide)
    have hmul_2T := Nat.mul_lt_mul_of_pos_left hmul_q h2T_pos
    have hlhs :
        2 ^ (blockSteps s r) * ((2 ^ (s r) * G) * (u r / G)) =
          2 ^ (blockSteps s r) * (2 ^ (s r) * u r) := by
      calc
        2 ^ (blockSteps s r) * ((2 ^ (s r) * G) * (u r / G)) =
            2 ^ (blockSteps s r) * (2 ^ (s r) * (G * (u r / G))) := by ring
        _ = 2 ^ (blockSteps s r) * (2 ^ (s r) * u r) := by rw [← hur_eq]
    have hrhs :
        2 ^ (blockSteps s r) * (3 ^ (blockSteps (shiftSeq s r) d) * (u r / G)) =
          2 ^ (blockSteps s r) * 3 ^ (blockSteps (shiftSeq s r) d) * (u r / G) := by
      ring
    rw [hlhs, hrhs] at hmul_2T
    exact hmul_2T
  exact lt_trans hgrow hstep_le

end Mahler.MultiStepGCD
