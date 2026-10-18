import AllHistoryQuotientRecovery

/-!
# The Parametric `(3^c - 2^c)` Remainder Bound & Narrowed `5×` / `19×` Quotient Corridors

This module generalizes `coprimeRemainder_add_two_pow_le` to an arbitrary
minimum block length `c ≤ s k` (`1 ≤ c`) and derives the narrowed `(3^c - 2^c)`
all-history quotient corridor:

1. **Universal Parametric Remainder Bound (`parametric_coprimeRemainder_bound`,
   `parametric_coprimeRemainder_lt`, `five_mul_coprimeRemainder_lt`,
   `nineteen_mul_coprimeRemainder_lt`)**:
   - Whenever `1 ≤ c`, `1 ≤ m`, and `∀ k < m, c ≤ s k`,
     `(3^c - 2^c) * coprimeRemainder s m + 2^c * 2^(tailSteps s (m - 1)) ≤ 3^(blockSteps s m)`.
   - Consequently, `(3^c - 2^c) * coprimeRemainder s m < 3^(blockSteps s m)`.
   - For `c = 2` (`2 ≤ s k`): `5 * coprimeRemainder s m < 3^(blockSteps s m)`.
   - For `c = 3` (`3 ≤ s k`): `19 * coprimeRemainder s m < 3^(blockSteps s m)`.
2. **Narrowed `(3^c - 2^c)` All-History Quotient Corridor & Div/Mod Recovery
   (`parametric_shifted_quotient_div_mod`,
   `surviving_five_mul_quotient_div_mod`,
   `ceiling_saturated_nineteen_mul_quotient_div_mod`)**:
   - Along any `ValidBlockChain a_0 s u K` (`1 ≤ d`, `r + d < K`) with
     `∀ k < d, c ≤ s (r + k)` (`1 ≤ c`), dividing
     `(3^c - 2^c) * 2^(tailSteps (shiftSeq s r) d) * u (r + d)` by
     `3^(blockSteps (shiftSeq s r) d)` yields exact quotient
     `(3^c - 2^c) * u r` and exact remainder
     `(3^c - 2^c) * coprimeRemainder (shiftSeq s r) d`.
   - Specializing to `c = 2` (`5 * u r`) and `c = 3` (`19 * u r`) narrows the
     all-history quotient corridor by factors of `5` and `19` respectively.
-/

namespace Mahler.ParametricCorridor

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

/-! ## 1. The Parametric `(3^c - 2^c)` Remainder Bound -/

/-- Whenever `c ≤ n`, `3^c * 2^n ≤ 2^c * 3^n`. -/
theorem three_pow_mul_two_pow_le_two_pow_mul_three_pow {c n : ℕ}
    (hcn : c ≤ n) :
    3 ^ c * 2 ^ n ≤ 2 ^ c * 3 ^ n := by
  have hsplit : n = c + (n - c) := by omega
  have h23 : 2 ^ (n - c) ≤ 3 ^ (n - c) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) (n - c)
  have hmul := Nat.mul_le_mul_left (3 ^ c * 2 ^ c) h23
  calc
    3 ^ c * 2 ^ n = (3 ^ c * 2 ^ c) * 2 ^ (n - c) := by
      conv_lhs => rw [hsplit, Nat.pow_add]
      ring
    _ ≤ (3 ^ c * 2 ^ c) * 3 ^ (n - c) := hmul
    _ = 2 ^ c * 3 ^ n := by
      conv_rhs => rw [hsplit, Nat.pow_add]
      ring

/-- **Universal Parametric Remainder Bound (`parametric_coprimeRemainder_bound`)**:
Whenever `1 ≤ m` and `∀ k < m, c ≤ s k`,
`(3^c - 2^c) * coprimeRemainder s m + 2^c * 2^(tailSteps s (m - 1)) ≤ 3^(blockSteps s m)`. -/
theorem parametric_coprimeRemainder_bound {s : ℕ → ℕ} {c m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, c ≤ s k) :
    (3 ^ c - 2 ^ c) * coprimeRemainder s m +
        2 ^ c * 2 ^ (tailSteps s (m - 1)) ≤
      3 ^ (blockSteps s m) := by
  have h2le3 : 2 ^ c ≤ 3 ^ c := Nat.pow_le_pow_left (by decide : 2 ≤ 3) c
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          have hs0 : c ≤ s 0 := hs 0 (by omega)
          have h3 : 3 ^ c ≤ 3 ^ (s 0) :=
            Nat.pow_le_pow_right (by decide : 0 < 3) hs0
          simp only [coprimeRemainder, tailSteps, blockSteps,
            Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
          omega
      | succ n =>
          have ihn := ih (by omega) (fun k hk => hs k (by omega))
          have hsn1 : c ≤ s (n + 1) := hs (n + 1) (by omega)
          have hstep := three_pow_mul_two_pow_le_two_pow_mul_three_pow hsn1
          have htail :
              tailSteps s (n + 1) = tailSteps s n + s (n + 1) := rfl
          have hsum_c : (3 ^ c - 2 ^ c) + 2 ^ c = 3 ^ c :=
            Nat.sub_add_cancel h2le3
          calc
            (3 ^ c - 2 ^ c) * coprimeRemainder s (n + 2) +
                2 ^ c * 2 ^ (tailSteps s (n + 1)) =
              (3 ^ c - 2 ^ c) * 3 ^ (s (n + 1)) * coprimeRemainder s (n + 1) +
                ((3 ^ c - 2 ^ c) + 2 ^ c) * 2 ^ (tailSteps s (n + 1)) := by
              simp only [coprimeRemainder]
              ring
            _ = (3 ^ c - 2 ^ c) * 3 ^ (s (n + 1)) * coprimeRemainder s (n + 1) +
                  2 ^ (tailSteps s n) * (3 ^ c * 2 ^ (s (n + 1))) := by
              rw [hsum_c, htail, Nat.pow_add]
              ring
            _ ≤ (3 ^ c - 2 ^ c) * 3 ^ (s (n + 1)) * coprimeRemainder s (n + 1) +
                  2 ^ (tailSteps s n) * (2 ^ c * 3 ^ (s (n + 1))) :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_left (2 ^ (tailSteps s n)) hstep) _
            _ = 3 ^ (s (n + 1)) *
                  ((3 ^ c - 2 ^ c) * coprimeRemainder s (n + 1) +
                    2 ^ c * 2 ^ (tailSteps s n)) := by ring
            _ ≤ 3 ^ (s (n + 1)) * 3 ^ (blockSteps s (n + 1)) :=
              Nat.mul_le_mul_left (3 ^ (s (n + 1))) ihn
            _ = 3 ^ (blockSteps s (n + 2)) := by
              simp only [blockSteps, Nat.pow_add]
              ring

/-- Strict parametric remainder bound:
`(3^c - 2^c) * coprimeRemainder s m < 3^(blockSteps s m)`. -/
theorem parametric_coprimeRemainder_lt {s : ℕ → ℕ} {c m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, c ≤ s k) :
    (3 ^ c - 2 ^ c) * coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  have hle := parametric_coprimeRemainder_bound hm hs
  have hpos1 : 0 < 2 ^ c := Nat.pow_pos (by decide)
  have hpos2 : 0 < 2 ^ (tailSteps s (m - 1)) := Nat.pow_pos (by decide)
  have hprod : 0 < 2 ^ c * 2 ^ (tailSteps s (m - 1)) := Nat.mul_pos hpos1 hpos2
  omega

/-- **The `5×` Remainder Bound on `{2 ≤ s k}` (`five_mul_coprimeRemainder_lt`)**:
Whenever `1 ≤ m` and `∀ k < m, 2 ≤ s k`,
`5 * coprimeRemainder s m < 3^(blockSteps s m)`. -/
theorem five_mul_coprimeRemainder_lt {s : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, 2 ≤ s k) :
    5 * coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  have h := parametric_coprimeRemainder_lt (c := 2) hm hs
  simpa using h

/-- **The `19×` Remainder Bound on `{3 ≤ s k}` (`nineteen_mul_coprimeRemainder_lt`)**:
Whenever `1 ≤ m` and `∀ k < m, 3 ≤ s k`,
`19 * coprimeRemainder s m < 3^(blockSteps s m)`. -/
theorem nineteen_mul_coprimeRemainder_lt {s : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, 3 ≤ s k) :
    19 * coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  have h := parametric_coprimeRemainder_lt (c := 3) hm hs
  simpa using h

/-! ## 2. Narrowed `(3^c - 2^c)` All-History Quotient Corridors & Div/Mod Recovery -/

/-- **Parametric All-History Div/Mod Recovery (`parametric_shifted_quotient_div_mod`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ d`, `r + d < K`) with
`∀ k < d, c ≤ s (r + k)`, dividing
`(3^c - 2^c) * 2^(tailSteps (shiftSeq s r) d) * u (r + d)` by
`3^(blockSteps (shiftSeq s r) d)` recovers exact quotient `(3^c - 2^c) * u r`
and exact remainder `(3^c - 2^c) * coprimeRemainder (shiftSeq s r) d`. -/
theorem parametric_shifted_quotient_div_mod
    {a_0 : ℕ} {s u : ℕ → ℕ} {K c r d : ℕ}
    (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_ge : ∀ k < d, c ≤ s (r + k)) :
    ((3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) /
        3 ^ (blockSteps (shiftSeq s r) d) =
        (3 ^ c - 2 ^ c) * u r ∧
      ((3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) %
        3 ^ (blockSteps (shiftSeq s r) d) =
        (3 ^ c - 2 ^ c) * coprimeRemainder (shiftSeq s r) d := by
  have hid := shifted_coprime_quotient_m_step_identity hrd hchain
  have hmul :
      (3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) =
        3 ^ (blockSteps (shiftSeq s r) d) * ((3 ^ c - 2 ^ c) * u r) +
          (3 ^ c - 2 ^ c) * coprimeRemainder (shiftSeq s r) d := by
    calc
      (3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) =
          (3 ^ c - 2 ^ c) *
            (2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) := by ring
      _ = (3 ^ c - 2 ^ c) *
            (3 ^ (blockSteps (shiftSeq s r) d) * u r +
              coprimeRemainder (shiftSeq s r) d) := by rw [hid]
      _ = 3 ^ (blockSteps (shiftSeq s r) d) * ((3 ^ c - 2 ^ c) * u r) +
            (3 ^ c - 2 ^ c) * coprimeRemainder (shiftSeq s r) d := by ring
  have hlt :
      (3 ^ c - 2 ^ c) * coprimeRemainder (shiftSeq s r) d <
        3 ^ (blockSteps (shiftSeq s r) d) :=
    parametric_coprimeRemainder_lt hd (fun k hk => by simpa [shiftSeq] using hs_ge k hk)
  have hpos : 0 < 3 ^ (blockSteps (shiftSeq s r) d) := Nat.pow_pos (by decide)
  have hdiv :
      ((3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) /
          3 ^ (blockSteps (shiftSeq s r) d) =
        (3 ^ c - 2 ^ c) * u r := by
    apply Nat.le_antisymm
    · have hhi :
          (3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) <
            ((3 ^ c - 2 ^ c) * u r + 1) * 3 ^ (blockSteps (shiftSeq s r) d) := by
        rw [hmul]
        have : ((3 ^ c - 2 ^ c) * u r + 1) * 3 ^ (blockSteps (shiftSeq s r) d) =
            3 ^ (blockSteps (shiftSeq s r) d) * ((3 ^ c - 2 ^ c) * u r) +
              3 ^ (blockSteps (shiftSeq s r) d) := by ring
        omega
      exact (Nat.div_lt_iff_lt_mul hpos).mpr hhi |> Nat.le_of_lt_succ
    · have hlo :
          ((3 ^ c - 2 ^ c) * u r) * 3 ^ (blockSteps (shiftSeq s r) d) ≤
            (3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d) := by
        rw [hmul]
        have : ((3 ^ c - 2 ^ c) * u r) * 3 ^ (blockSteps (shiftSeq s r) d) =
            3 ^ (blockSteps (shiftSeq s r) d) * ((3 ^ c - 2 ^ c) * u r) := by ring
        omega
      exact (Nat.le_div_iff_mul_le hpos).mpr hlo
  have hdm :=
    Nat.div_add_mod
      ((3 ^ c - 2 ^ c) * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d))
      (3 ^ (blockSteps (shiftSeq s r) d))
  rw [hdiv] at hdm
  exact ⟨hdiv, by omega⟩

/-- **The `5×` Narrowed All-History Quotient Recovery (`surviving_five_mul_quotient_div_mod`)**:
Whenever `∀ k < d, 2 ≤ s (r + k)`, dividing
`5 * 2^(tailSteps (shiftSeq s r) d) * u (r + d)` by `3^(blockSteps (shiftSeq s r) d)`
yields exact quotient `5 * u r` and exact remainder
`5 * coprimeRemainder (shiftSeq s r) d`. -/
theorem surviving_five_mul_quotient_div_mod
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_ge2 : ∀ k < d, 2 ≤ s (r + k)) :
    (5 * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) /
        3 ^ (blockSteps (shiftSeq s r) d) = 5 * u r ∧
      (5 * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) %
        3 ^ (blockSteps (shiftSeq s r) d) =
        5 * coprimeRemainder (shiftSeq s r) d := by
  have h := parametric_shifted_quotient_div_mod (c := 2) hd hrd hchain hs_ge2
  simpa using h

/-- **The `19×` Narrowed All-History Quotient Recovery (`ceiling_saturated_nineteen_mul_quotient_div_mod`)**:
Whenever `∀ k < d, 3 ≤ s (r + k)`, dividing
`19 * 2^(tailSteps (shiftSeq s r) d) * u (r + d)` by `3^(blockSteps (shiftSeq s r) d)`
yields exact quotient `19 * u r` and exact remainder
`19 * coprimeRemainder (shiftSeq s r) d`. -/
theorem ceiling_saturated_nineteen_mul_quotient_div_mod
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r d : ℕ}
    (hd : 1 ≤ d) (hrd : r + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hs_ge3 : ∀ k < d, 3 ≤ s (r + k)) :
    (19 * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) /
        3 ^ (blockSteps (shiftSeq s r) d) = 19 * u r ∧
      (19 * 2 ^ (tailSteps (shiftSeq s r) d) * u (r + d)) %
        3 ^ (blockSteps (shiftSeq s r) d) =
        19 * coprimeRemainder (shiftSeq s r) d := by
  have h := parametric_shifted_quotient_div_mod (c := 3) hd hrd hchain hs_ge3
  simpa using h

end Mahler.ParametricCorridor
