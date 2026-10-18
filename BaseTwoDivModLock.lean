import GlobalStepRateBounds

/-!
# The Base-2 Div/Mod Lock, Zero-Bit Windows, and Two-Step Compound Coprime Squeezes

This module formalizes **Attack Vector A** (the Base-2 Euclidean Quotient &
Remainder Lock and Zero-Bit Window Theorem during sub-ceiling recovery phases)
and **Attack Vector B** (the Two-Step Compound Coprime Identity and its `2^17`
divisibility lock on the `(2, 6, 3, 3, 2, 10)` cascade):

1. **Attack Vector A — The Base-2 Div/Mod Lock & Zero-Bit Window Theorem
   (`base_two_slack_decomposition`, `base_two_div_mod_lock`,
   `base_two_quotient_two_pow_valuation`, `base_two_shifted_div_mod_lock`)**:
   - Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`) with
     `0 < integerSlack s m`:
     `3^(blockSteps s m + 1) * (2 * a_0 + 1) =
       2^(blockSteps s m) * (2^(s m + 1) * u m) + (integerSlack s m).toNat`.
   - Whenever `integerSlack s m < 2^(blockSteps s m)` (the sub-ceiling recovery
     regime), dividing `3^(blockSteps s m + 1) * (2 * a_0 + 1)` by
     `2^(blockSteps s m)` locks both the quotient and remainder:
     `(3^(blockSteps s m + 1) * (2 * a_0 + 1)) / 2^(blockSteps s m) = 2^(s m + 1) * u m`
     and
     `(3^(blockSteps s m + 1) * (2 * a_0 + 1)) % 2^(blockSteps s m) = (integerSlack s m).toNat`.
   - Because `u m` is odd, the exact 2-adic valuation of the quotient is `s m + 1`
     (bits `S .. S + s m` of `3^(S + 1) * (2 * a_0 + 1)` are `0`, and bit
     `S + s m + 1` is `1`).
   - By shift-invariance (`base_two_shifted_div_mod_lock`), the same lock holds
     at every intermediate return `b_j = orbit a_0 (blockSteps s j)`.
2. **Attack Vector B — The Two-Step Compound Coprime Identity & `2^17` Cascade Lock
   (`two_step_compound_coprime_identity`, `two_step_compound_coprime_dvd`,
   `cascade_2_6_3_3_2_10_compound_dvd`)**:
   - Across any two consecutive transitions `k → k + 1 → k + 2` (`k + 2 < K`),
     `2^(s (k + 1) + s (k + 2)) * u (k + 2) =
       3^(s k + s (k + 1)) * u k + (3^(s (k + 1)) + 2^(s (k + 1)))`.
   - Along the `(2, 6, 3, 3, 2, 10)` cascade where `7 ≤ s (j + 6)` is forced,
     `17 ≤ s (j + 5) + s (j + 6)`, so `2^17 = 131072` divides
     `531441 * u (j + 4) + 60073`.
-/

namespace Mahler.BaseTwoLock

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

/-! ## 1. Attack Vector A: The Base-2 Div/Mod Lock & Zero-Bit Window Theorem -/

/-- **Base-2 Subtraction-Free Decomposition (`base_two_slack_decomposition`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`) with
`0 < integerSlack s m`,
`3^(blockSteps s m + 1) * (2 * a_0 + 1) =
  2^(blockSteps s m) * (2^(s m + 1) * u m) + (integerSlack s m).toNat`. -/
theorem base_two_slack_decomposition {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m) :
    3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) =
      2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) +
        (integerSlack s m).toNat := by
  have hslack := integerSlack_eq_orbit_slack hmK hchain
  have htoNat : ((integerSlack s m).toNat : ℤ) = integerSlack s m :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  have hpow2 :
      2 ^ (blockSteps s (m + 1) + 1) * u m =
        2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) := by
    simp only [blockSteps]
    rw [show blockSteps s m + s m + 1 = blockSteps s m + (s m + 1) by omega, Nat.pow_add]
    ring
  have hcast :
      ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) : ℕ) : ℤ) =
        ((2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) +
          (integerSlack s m).toNat : ℕ) : ℤ) := by
    rw [← hpow2]
    push_cast
    rw [htoNat]
    linarith
  exact_mod_cast hcast

/-- **The Base-2 Euclidean Div/Mod Lock (`base_two_div_mod_lock`)**:
Whenever `0 < integerSlack s m < 2^(blockSteps s m)` (the sub-ceiling recovery
regime), dividing `3^(blockSteps s m + 1) * (2 * a_0 + 1)` by `2^(blockSteps s m)`
yields exact quotient `2^(s m + 1) * u m` and exact remainder `(integerSlack s m).toNat`. -/
theorem base_two_div_mod_lock {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hlt : integerSlack s m < (2 : ℤ) ^ (blockSteps s m)) :
    (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) / 2 ^ (blockSteps s m) =
        2 ^ (s m + 1) * u m ∧
      (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) % 2 ^ (blockSteps s m) =
        (integerSlack s m).toNat := by
  have hdecomp := base_two_slack_decomposition hmK hchain hpos
  have htoNat : ((integerSlack s m).toNat : ℤ) = integerSlack s m :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  have hlt_nat : (integerSlack s m).toNat < 2 ^ (blockSteps s m) := by
    have hcast :
        (((integerSlack s m).toNat : ℕ) : ℤ) <
          ((2 ^ (blockSteps s m) : ℕ) : ℤ) := by
      push_cast
      rw [htoNat]
      exact hlt
    exact_mod_cast hcast
  have h2pos : 0 < 2 ^ (blockSteps s m) := Nat.pow_pos (by decide)
  have hdiv :
      (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) / 2 ^ (blockSteps s m) =
        2 ^ (s m + 1) * u m := by
    apply Nat.le_antisymm
    · have hhi :
          3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) <
            (2 ^ (s m + 1) * u m + 1) * 2 ^ (blockSteps s m) := by
        rw [hdecomp]
        have : (2 ^ (s m + 1) * u m + 1) * 2 ^ (blockSteps s m) =
            2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) +
              2 ^ (blockSteps s m) := by ring
        omega
      exact (Nat.div_lt_iff_lt_mul h2pos).mpr hhi |> Nat.le_of_lt_succ
    · have hlo :
          (2 ^ (s m + 1) * u m) * 2 ^ (blockSteps s m) ≤
            3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
        rw [hdecomp]
        have : (2 ^ (s m + 1) * u m) * 2 ^ (blockSteps s m) =
            2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) := by ring
        omega
      exact (Nat.le_div_iff_mul_le h2pos).mpr hlo
  have hdm :=
    Nat.div_add_mod (3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) (2 ^ (blockSteps s m))
  rw [hdiv] at hdm
  exact ⟨hdiv, by omega⟩

/-- **Zero-Bit Window & Exact 2-adic Valuation of the Base-2 Quotient
(`base_two_quotient_two_pow_valuation`)**:
In the sub-ceiling recovery regime (`0 < integerSlack s m < 2^(blockSteps s m)`),
the base-2 quotient `(3^(blockSteps s m + 1) * (2 * a_0 + 1)) / 2^(blockSteps s m)`
is divisible by `2^(s m + 1)` and not by `2^(s m + 2)`. -/
theorem base_two_quotient_two_pow_valuation {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m)
    (hlt : integerSlack s m < (2 : ℤ) ^ (blockSteps s m)) :
    2 ^ (s m + 1) ∣
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) / 2 ^ (blockSteps s m)) ∧
      ¬ (2 ^ (s m + 2) ∣
        ((3 ^ (blockSteps s m + 1) * (2 * a_0 + 1)) / 2 ^ (blockSteps s m))) := by
  have hdiv := (base_two_div_mod_lock hmK hchain hpos hlt).1
  rw [hdiv]
  rcases hchain m hmK with ⟨_, hum_odd, _⟩
  refine ⟨⟨u m, rfl⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hpow : 2 ^ (s m + 2) * q = 2 ^ (s m + 1) * (2 * q) := by
    rw [show s m + 2 = (s m + 1) + 1 by omega, Nat.pow_add]
    ring
  rw [hpow] at hq
  have hpos2 : 0 < 2 ^ (s m + 1) := Nat.pow_pos (by decide)
  have hum_eq : u m = 2 * q := Nat.eq_of_mul_eq_mul_left hpos2 hq
  omega

/-- **Shifted Multi-Origin Base-2 Div/Mod Lock (`base_two_shifted_div_mod_lock`)**:
For any origin `j` and offset `r` (`j + r < K`) where
`0 < integerSlack (shiftSeq s j) r < 2^(blockSteps (shiftSeq s j) r)`,
let `S = blockSteps (shiftSeq s j) r` and `b_j = orbit a_0 (blockSteps s j)`.
Then dividing `3^(S + 1) * (2 * b_j + 1)` by `2^S` yields quotient
`2^(s (j + r) + 1) * u (j + r)` and remainder `(integerSlack (shiftSeq s j) r).toNat`. -/
theorem base_two_shifted_div_mod_lock {a_0 : ℕ} {s u : ℕ → ℕ} {K j r : ℕ}
    (hjr : j + r < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack (shiftSeq s j) r)
    (hlt : integerSlack (shiftSeq s j) r < (2 : ℤ) ^ (blockSteps (shiftSeq s j) r)) :
    (3 ^ (blockSteps (shiftSeq s j) r + 1) *
        (2 * orbit a_0 (blockSteps s j) + 1)) /
        2 ^ (blockSteps (shiftSeq s j) r) =
        2 ^ (s (j + r) + 1) * u (j + r) ∧
      (3 ^ (blockSteps (shiftSeq s j) r + 1) *
        (2 * orbit a_0 (blockSteps s j) + 1)) %
        2 ^ (blockSteps (shiftSeq s j) r) =
        (integerSlack (shiftSeq s j) r).toNat := by
  have hchain_sub : ValidBlockChain a_0 s u (j + (r + 1)) :=
    fun k hk => hchain k (by omega)
  have hchain_shift := validBlockChain_shift hchain_sub
  have hlock :=
    base_two_div_mod_lock (Nat.lt_succ_self r) hchain_shift hpos hlt
  simpa [shiftSeq] using hlock

/-! ## 2. Attack Vector B: Two-Step Compound Coprime Identity & `2^17` Cascade Lock -/

/-- **Two-Step Compound Coprime Identity (`two_step_compound_coprime_identity`)**:
Across any two consecutive transitions `k → k + 1 → k + 2` (`k + 2 < K`) of
`ValidBlockChain a_0 s u K`,
`2^(s (k + 1) + s (k + 2)) * u (k + 2) =
  3^(s k + s (k + 1)) * u k + (3^(s (k + 1)) + 2^(s (k + 1)))`. -/
theorem two_step_compound_coprime_identity {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk : k + 2 < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (s (k + 1) + s (k + 2)) * u (k + 2) =
      3 ^ (s k + s (k + 1)) * u k + (3 ^ (s (k + 1)) + 2 ^ (s (k + 1))) := by
  have h1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have h2 := coprime_quotient_recurrence (by omega : k + 2 < K) hchain
  calc
    2 ^ (s (k + 1) + s (k + 2)) * u (k + 2) =
        2 ^ (s (k + 1)) * (2 ^ (s (k + 2)) * u (k + 2)) := by
          rw [Nat.pow_add]
          ring
    _ = 2 ^ (s (k + 1)) * (3 ^ (s (k + 1)) * u (k + 1) + 1) := by rw [h2]
    _ = 3 ^ (s (k + 1)) * (2 ^ (s (k + 1)) * u (k + 1)) + 2 ^ (s (k + 1)) := by
          ring
    _ = 3 ^ (s (k + 1)) * (3 ^ (s k) * u k + 1) + 2 ^ (s (k + 1)) := by
          rw [h1]
    _ = 3 ^ (s k + s (k + 1)) * u k + (3 ^ (s (k + 1)) + 2 ^ (s (k + 1))) := by
          rw [Nat.pow_add]
          ring

/-- **Two-Step Compound Divisibility (`two_step_compound_coprime_dvd`)**:
If `k + 2 < K` and `B ≤ s (k + 1) + s (k + 2)` along `ValidBlockChain a_0 s u K`,
then `2^B` divides `3^(s k + s (k + 1)) * u k + (3^(s (k + 1)) + 2^(s (k + 1)))`. -/
theorem two_step_compound_coprime_dvd {a_0 : ℕ} {s u : ℕ → ℕ} {K k B : ℕ}
    (hk : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hB : B ≤ s (k + 1) + s (k + 2)) :
    2 ^ B ∣
      (3 ^ (s k + s (k + 1)) * u k + (3 ^ (s (k + 1)) + 2 ^ (s (k + 1)))) := by
  rw [← two_step_compound_coprime_identity hk hchain]
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hB) (u (k + 2))

/-- **The `2^17 = 131072` Divisibility Lock on the `(2, 6, 3, 3, 2, 10)` Cascade
(`cascade_2_6_3_3_2_10_compound_dvd`)**:
If `(s j, ..., s (j + 5)) = (2, 6, 3, 3, 2, 10)` occurs at block index `j`
(`j + 7 < K`) along a surviving orbit, then `7 ≤ s (j + 6)` and
`131072 ∣ (531441 * u (j + 4) + 60073)`. -/
theorem cascade_2_6_3_3_2_10_compound_dvd {a_0 : ℕ} {s u : ℕ → ℕ} {K j : ℕ}
    (hj : j + 7 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs0 : s j = 2) (hs1 : s (j + 1) = 6) (hs2 : s (j + 2) = 3)
    (hs3 : s (j + 3) = 3) (hs4 : s (j + 4) = 2) (hs5 : s (j + 5) = 10)
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (j + 7 + 1))) :
    7 ≤ s (j + 6) ∧ 131072 ∣ (531441 * u (j + 4) + 60073) := by
  have hs6 : 7 ≤ s (j + 6) :=
    seven_le_after_subword_2_6_3_3_2_10 hj hchain hs0 hs1 hs2 hs3 hs4 hs5 hsurv
  have hdvd :=
    two_step_compound_coprime_dvd (k := j + 4) (B := 17)
      (by omega : (j + 4) + 2 < K) hchain
      (by
        have h5 : s ((j + 4) + 1) = 10 := by simpa [Nat.add_assoc] using hs5
        have h6 : 7 ≤ s ((j + 4) + 2) := by simpa [Nat.add_assoc] using hs6
        omega)
  have h5 : s ((j + 4) + 1) = 10 := by simpa [Nat.add_assoc] using hs5
  rw [hs4, h5] at hdvd
  norm_num at hdvd
  exact ⟨hs6, hdvd⟩

end Mahler.BaseTwoLock
