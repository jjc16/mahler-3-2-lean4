import FullStepSumValuation

/-!
# Universal Oddness of `coprimeRemainder`, Coprimality to `6` & The Polynomial Addition Law

This module proves the universal 2-adic and 3-adic coprimality of
`coprimeRemainder s m`, the constant 2-adic valuation of
`3^(blockSteps s m) - integerSlack s m`, and the exact cocycle addition law for
`coprimeRemainder s (r + d)`:

1. **Universal Oddness & Coprimality to `6` of `coprimeRemainder`
   (`tailSteps_pos`, `coprimeRemainder_odd`, `coprimeRemainder_coprime_six`)**:
   - Whenever `1 ≤ m` and `1 ≤ s 1`, `1 ≤ tailSteps s m`.
   - Consequently, for every `1 ≤ m` with `∀ k < m, 1 ≤ s k`,
     `coprimeRemainder s m % 2 = 1` (always odd) and `coprimeRemainder s m % 3 ≠ 0`
     (coprime to `6`).
2. **Constant 2-adic Valuation of `3^T(m) - integerSlack s m`
   (`three_pow_sub_integerSlack_eq`, `three_pow_sub_integerSlack_valuation`)**:
   Because `3^(blockSteps s m) - integerSlack s m = 2^(s 0 + 1) * coprimeRemainder s m`
   and `coprimeRemainder s m` is odd for all `m ≥ 1`, the exact 2-adic valuation
   of `2^(s 0 + 1) * coprimeRemainder s m` is `s 0 + 1` for **every** horizon `m ≥ 1`
   (divisible by `2^(s 0 + 1)` and not by `2^(s 0 + 2)`).
3. **Exact Polynomial Addition Law & Valuation for `coprimeRemainder`
   (`tailSteps_add`, `coprimeRemainder_add_eq`,
   `coprimeRemainder_add_sub_valuation`)**:
   - `tailSteps s (r + d) = tailSteps s r + tailSteps (shiftSeq s r) d`.
   - `coprimeRemainder s (r + d) =
       3^(blockSteps (shiftSeq s r) d) * coprimeRemainder s r +
         2^(tailSteps s r) * coprimeRemainder (shiftSeq s r) d`.
   - Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the difference
     `coprimeRemainder s (r + d) - 3^(blockSteps (shiftSeq s r) d) * coprimeRemainder s r`
     has exact 2-adic valuation `tailSteps s r`.
-/

namespace Mahler.RemainderAdditionLaw

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

/-! ## 1. Universal Oddness & Coprimality to `6` of `coprimeRemainder` -/

/-- Whenever `1 ≤ m` and `1 ≤ s 1`, `1 ≤ tailSteps s m`. -/
theorem tailSteps_pos {s : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hs1 : 1 ≤ s 1) :
    1 ≤ tailSteps s m := by
  induction m with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [tailSteps, hs1]
      · have ihn := ih hn
        simp only [tailSteps]
        omega

private theorem three_pow_odd_all (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **Universal Oddness of `coprimeRemainder` (`coprimeRemainder_odd`)**:
Whenever `1 ≤ m` and `∀ k < m, 1 ≤ s k`, `coprimeRemainder s m % 2 = 1`. -/
theorem coprimeRemainder_odd {s : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, 1 ≤ s k) :
    coprimeRemainder s m % 2 = 1 := by
  induction m with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [coprimeRemainder, tailSteps]
      · have ihn := ih hn (fun k hk => hs k (by omega))
        have hs1 : 1 ≤ s 1 := hs 1 (by omega)
        have htail_pos : 1 ≤ tailSteps s n := tailSteps_pos hn hs1
        have h2_even : 2 ^ (tailSteps s n) % 2 = 0 := by
          have hsub : tailSteps s n = (tailSteps s n - 1) + 1 := by omega
          rw [hsub, Nat.pow_succ]
          omega
        have h3_odd : 3 ^ (s n) % 2 = 1 := three_pow_odd_all (s n)
        simp only [coprimeRemainder]
        rw [Nat.add_mod, Nat.mul_mod, h3_odd, ihn, h2_even]

/-- **Universal Coprimality to `6` (`coprimeRemainder_coprime_six`)**:
Whenever `1 ≤ m` and `∀ k < m, 1 ≤ s k`, `coprimeRemainder s m` is divisible
by neither `2` nor `3`. -/
theorem coprimeRemainder_coprime_six {s : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, 1 ≤ s k) :
    coprimeRemainder s m % 2 = 1 ∧
      coprimeRemainder s m % 3 ≠ 0 ∧
      ¬ (2 ∣ coprimeRemainder s m) ∧
      ¬ (3 ∣ coprimeRemainder s m) := by
  have hodd := coprimeRemainder_odd hm hs
  have hmod3 := coprimeRemainder_mod_three_ne_zero hm hs
  refine ⟨hodd, hmod3, ?_, ?_⟩
  · intro hdvd2
    have h0 := Nat.mod_eq_zero_of_dvd hdvd2
    omega
  · intro hdvd3
    exact hmod3 (Nat.mod_eq_zero_of_dvd hdvd3)

/-! ## 2. Constant 2-adic Valuation of `3^T(m) - integerSlack s m` -/

/-- Exact identity `(3 : ℤ)^(blockSteps s m) - integerSlack s m =
  2^(s 0 + 1) * coprimeRemainder s m`. -/
theorem three_pow_sub_integerSlack_eq (s : ℕ → ℕ) (m : ℕ) :
    (3 : ℤ) ^ (blockSteps s m) - integerSlack s m =
      (2 : ℤ) ^ (s 0 + 1) * (coprimeRemainder s m : ℤ) := by
  unfold integerSlack
  ring

/-- **Constant 2-adic Valuation Law (`three_pow_sub_integerSlack_valuation`)**:
For every `m ≥ 1` with `∀ k < m, 1 ≤ s k`, the difference
`2^(s 0 + 1) * coprimeRemainder s m` (which equals `3^T(m) - integerSlack s m`)
has exact 2-adic valuation `s 0 + 1` (independent of `m`!):
- `2^(s 0 + 1) ∣ (2^(s 0 + 1) * coprimeRemainder s m)`, and
- `¬ (2^(s 0 + 2) ∣ (2^(s 0 + 1) * coprimeRemainder s m))`. -/
theorem three_pow_sub_integerSlack_valuation {s : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, 1 ≤ s k) :
    2 ^ (s 0 + 1) ∣ (2 ^ (s 0 + 1) * coprimeRemainder s m) ∧
      ¬ (2 ^ (s 0 + 2) ∣ (2 ^ (s 0 + 1) * coprimeRemainder s m)) := by
  have hodd := coprimeRemainder_odd hm hs
  refine ⟨⟨coprimeRemainder s m, rfl⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hsplit : 2 ^ (s 0 + 2) * q = 2 ^ (s 0 + 1) * (2 * q) := by
    rw [show s 0 + 2 = (s 0 + 1) + 1 by omega, Nat.pow_add]
    ring
  rw [hsplit] at hq
  have hpos : 0 < 2 ^ (s 0 + 1) := Nat.pow_pos (by decide)
  have heq : coprimeRemainder s m = 2 * q := Nat.eq_of_mul_eq_mul_left hpos hq
  omega

/-! ## 3. Exact Polynomial Addition Law & Valuation for `coprimeRemainder` -/

/-- Additive cocycle property of `tailSteps`:
`tailSteps s (r + d) = tailSteps s r + tailSteps (shiftSeq s r) d`. -/
theorem tailSteps_add (s : ℕ → ℕ) (r d : ℕ) :
    tailSteps s (r + d) =
      tailSteps s r + tailSteps (shiftSeq s r) d := by
  induction d with
  | zero => simp [tailSteps]
  | succ d ih =>
      have h1 : tailSteps s (r + (d + 1)) = tailSteps s (r + d) + s (r + d + 1) := by
        rw [← Nat.add_assoc]
        rfl
      have h2 :
          tailSteps (shiftSeq s r) (d + 1) =
            tailSteps (shiftSeq s r) d + s (r + d + 1) := by
        simp [tailSteps, shiftSeq, Nat.add_assoc]
      omega

/-- **Exact Polynomial Addition Law (`coprimeRemainder_add_eq`)**:
For every sequence `s : ℕ → ℕ`, prefix `r`, and offset `d`,
`coprimeRemainder s (r + d) =
  3^(blockSteps (shiftSeq s r) d) * coprimeRemainder s r +
    2^(tailSteps s r) * coprimeRemainder (shiftSeq s r) d`. -/
theorem coprimeRemainder_add_eq (s : ℕ → ℕ) (r d : ℕ) :
    coprimeRemainder s (r + d) =
      3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r +
        2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d := by
  induction d with
  | zero =>
      simp [blockSteps, coprimeRemainder]
  | succ d ih =>
      have hsucc :
          coprimeRemainder s (r + (d + 1)) =
            3 ^ (s (r + d)) * coprimeRemainder s (r + d) +
              2 ^ (tailSteps s (r + d)) := by
        rw [← Nat.add_assoc]
        rfl
      have htail :
          2 ^ (tailSteps s (r + d)) =
            2 ^ (tailSteps s r) * 2 ^ (tailSteps (shiftSeq s r) d) := by
        rw [tailSteps_add, Nat.pow_add]
      have hpow3 :
          3 ^ (blockSteps (shiftSeq s r) (d + 1)) =
            3 ^ (s (r + d)) * 3 ^ (blockSteps (shiftSeq s r) d) := by
        simp only [blockSteps, shiftSeq, Nat.pow_add]
        ring
      rw [hsucc, ih, htail]
      calc
        3 ^ (s (r + d)) *
            (3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r +
              2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d) +
          2 ^ (tailSteps s r) * 2 ^ (tailSteps (shiftSeq s r) d) =
          (3 ^ (s (r + d)) * 3 ^ (blockSteps (shiftSeq s r) d)) *
            coprimeRemainder s r +
          2 ^ (tailSteps s r) *
            (3 ^ (s (r + d)) * coprimeRemainder (shiftSeq s r) d +
              2 ^ (tailSteps (shiftSeq s r) d)) := by ring
        _ = 3 ^ (blockSteps (shiftSeq s r) (d + 1)) * coprimeRemainder s r +
              2 ^ (tailSteps s r) *
                coprimeRemainder (shiftSeq s r) (d + 1) := by
              rw [← hpow3]
              rfl

/-- **Exact 2-adic Valuation of the `coprimeRemainder` Step Difference
(`coprimeRemainder_add_sub_valuation`)**:
Whenever `1 ≤ d` and `∀ k < d, 1 ≤ s (r + k)`, the difference
`coprimeRemainder s (r + d) - 3^(blockSteps (shiftSeq s r) d) * coprimeRemainder s r`
has exact 2-adic valuation `tailSteps s r` (divisible by `2^(tailSteps s r)` and
not by `2^(tailSteps s r + 1)`). -/
theorem coprimeRemainder_add_sub_valuation {s : ℕ → ℕ} {r d : ℕ}
    (hd : 1 ≤ d) (hs : ∀ k < d, 1 ≤ s (r + k)) :
    coprimeRemainder s (r + d) -
        3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r =
        2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d ∧
      2 ^ (tailSteps s r) ∣
        (coprimeRemainder s (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r) ∧
      ¬ (2 ^ (tailSteps s r + 1) ∣
        (coprimeRemainder s (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r)) := by
  have hadd := coprimeRemainder_add_eq s r d
  have hsub :
      coprimeRemainder s (r + d) -
          3 ^ (blockSteps (shiftSeq s r) d) * coprimeRemainder s r =
        2 ^ (tailSteps s r) * coprimeRemainder (shiftSeq s r) d := by
    omega
  have hodd : coprimeRemainder (shiftSeq s r) d % 2 = 1 :=
    coprimeRemainder_odd hd (fun k hk => by simpa [shiftSeq] using hs k hk)
  refine ⟨hsub, ⟨coprimeRemainder (shiftSeq s r) d, hsub⟩, ?_⟩
  rw [hsub]
  rintro ⟨q, hq⟩
  have hsplit : 2 ^ (tailSteps s r + 1) * q = 2 ^ (tailSteps s r) * (2 * q) := by
    rw [Nat.pow_add]
    ring
  rw [hsplit] at hq
  have hpos : 0 < 2 ^ (tailSteps s r) := Nat.pow_pos (by decide)
  have heq : coprimeRemainder (shiftSeq s r) d = 2 * q :=
    Nat.eq_of_mul_eq_mul_left hpos hq
  omega

end Mahler.RemainderAdditionLaw
