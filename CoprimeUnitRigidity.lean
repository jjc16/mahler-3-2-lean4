import Mod256CompleteSieve

/-!
# Tri-Metric Unit-Sum Rigidity (`2^(s(k+1)) * u(k+1) - 3^(s k) * u k = 1`), `5 ≤ u k` & Contraction Laws

This module pushes **Idea 2** (the unit-sum coprime recurrence
`2^(s (k + 1)) * u (k + 1) - 3^(s k) * u k = 1`) to derive four structural
rigidity theorems:

1. **Universal Coprimality to `6` of Every Coprime Quotient `u k`
   (`u_coprime_six_of_validBlockChain`)**:
   Along any `ValidBlockChain a_0 s u K`, every `u k` (`k < K`) satisfies
   `u k % 2 = 1`, `u k % 3 ≠ 0`, `¬ (2 ∣ u k)`, and `¬ (3 ∣ u k)` (in particular,
   `u k ≠ 3` and `u k ≠ 9`).
2. **The Catalan / Modulo-8 Obstruction on `u k = 1` & The `5 ≤ u k` Lower Bound
   (`three_pow_add_one_mod_eight`, `three_pow_add_one_not_dvd_eight`,
   `u_eq_one_forces_next_block_le_two`, `ceiling_saturated_five_le_u`)**:
   - For every `s : ℕ`, `(3^s + 1) % 8` is `2` (for even `s`) or `4` (for odd `s`),
     so `¬ (8 ∣ (3^s + 1))`.
   - Consequently, if `u k = 1`, then `s (k + 1) ≤ 2` (`s (k + 1) = 1` when `s k`
     is even, `s (k + 1) = 2` when `s k` is odd).
   - Combining `u k ≠ 1` (whenever `3 ≤ s (k + 1)`), `u k % 2 = 1`, and
     `u k % 3 ≠ 0` (`u k ≠ 3`) proves that **`5 ≤ u k`** at every step with
     `3 ≤ s (k + 1)`!
3. **`5×` Sharpened Coasting Single-Block Bound
   (`coasting_five_mul_single_block_bound`)**:
   Using `5 ≤ u m` in `coasting_coprime_quotient_bound` sharpens the coasting
   single-block bound by a factor of `5` whenever `3 ≤ s (m + 1)`:
   `5 * 2^(blockSteps s m + s m - W) < 3^(blockSteps s m + 1)`.
4. **Quotient Contraction Laws Across `s k = 2`
   (`seven_mul_u_next_le_of_s_eq_two`,
   `hundred_thirteen_mul_u_next_le_of_s_eq_two_ten`)**:
   - Whenever `s k = 2` and `6 ≤ s (k + 1)` (forced by `0 < minSlack s (k + 2)`),
     `64 * u (k + 1) ≤ 9 * u k + 1`, so **`7 * u (k + 1) ≤ u k`**.
   - Whenever `s k = 2` and `10 ≤ s (k + 1)` (forced after `(2, 6, 3, 3, 2)`),
     `1024 * u (k + 1) ≤ 9 * u k + 1`, so **`113 * u (k + 1) ≤ u k`**.
-/

namespace Mahler.UnitRigidity

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

/-! ## 1. Universal Coprimality to `6` of Every Coprime Quotient `u k` -/

/-- **Universal Coprimality to `6` of `u k` (`u_coprime_six_of_validBlockChain`)**:
Along any `ValidBlockChain a_0 s u K`, every `u k` (`k < K`) is odd and not
divisible by `3`. -/
theorem u_coprime_six_of_validBlockChain {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk : k < K) (hchain : ValidBlockChain a_0 s u K) :
    u k % 2 = 1 ∧ u k % 3 ≠ 0 ∧ ¬ (2 ∣ u k) ∧ ¬ (3 ∣ u k) := by
  rcases hchain k hk with ⟨_, huk_odd, hdecomp⟩
  have hnot3 : ¬ (3 ∣ u k) := not_three_dvd_odd_part hdecomp
  have hmod3 : u k % 3 ≠ 0 := by
    intro h0
    exact hnot3 (Nat.dvd_of_mod_eq_zero h0)
  have hnot2 : ¬ (2 ∣ u k) := by
    intro hdvd2
    have h0 := Nat.mod_eq_zero_of_dvd hdvd2
    omega
  exact ⟨huk_odd, hmod3, hnot2, hnot3⟩

/-! ## 2. The Modulo-8 Obstruction on `u k = 1` & The `5 ≤ u k` Lower Bound -/

/-- For every `s : ℕ`, `(3^s + 1) % 8` is `2` when `s` is even and `4` when `s` is odd. -/
theorem three_pow_add_one_mod_eight (s : ℕ) :
    (s % 2 = 0 → (3 ^ s + 1) % 8 = 2) ∧
    (s % 2 = 1 → (3 ^ s + 1) % 8 = 4) := by
  rcases three_pow_mod_eight s with ⟨he, ho⟩
  constructor <;> intro hs
  · have := he hs
    omega
  · have := ho hs
    omega

/-- `8` never divides `3^s + 1` for any `s : ℕ`. -/
theorem three_pow_add_one_not_dvd_eight (s : ℕ) :
    ¬ (8 ∣ (3 ^ s + 1)) := by
  intro hdvd
  have h0 := Nat.mod_eq_zero_of_dvd hdvd
  rcases three_pow_add_one_mod_eight s with ⟨he, ho⟩
  have hpar : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases hpar with hs0 | hs1
  · have := he hs0
    omega
  · have := ho hs1
    omega

/-- **If `u k = 1`, the Next Block Cannot Exceed `2`
(`u_eq_one_forces_next_block_le_two`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), if `u k = 1`, then
`s (k + 1) ≤ 2` (`s (k + 1) = 1` if `s k` is even, `s (k + 1) = 2` if `s k` is odd). -/
theorem u_eq_one_forces_next_block_le_two {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (huk1 : u k = 1) :
    s (k + 1) ≤ 2 ∧
      (s k % 2 = 0 → s (k + 1) = 1) ∧
      (s k % 2 = 1 → s (k + 1) = 2) := by
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [huk1, Nat.mul_one] at hrec
  rcases hchain (k + 1) hk1 with ⟨hsk1_pos, huk1_odd, _⟩
  have hle2 : s (k + 1) ≤ 2 := by
    by_contra hgt2
    have hge3 : 3 ≤ s (k + 1) := by omega
    have hdvd8 : 8 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge3) _
    rw [hrec] at hdvd8
    exact three_pow_add_one_not_dvd_eight (s k) hdvd8
  rcases three_pow_add_one_mod_eight (s k) with ⟨he, ho⟩
  refine ⟨hle2, ?_, ?_⟩ <;> intro hpar
  · have hmod8 : (2 ^ (s (k + 1)) * u (k + 1)) % 8 = 2 := by
      rw [hrec]
      exact he hpar
    have hcases : s (k + 1) = 1 ∨ s (k + 1) = 2 := by omega
    rcases hcases with h1 | h2
    · exact h1
    · rw [h2] at hmod8
      omega
  · have hmod8 : (2 ^ (s (k + 1)) * u (k + 1)) % 8 = 4 := by
      rw [hrec]
      exact ho hpar
    have hcases : s (k + 1) = 1 ∨ s (k + 1) = 2 := by omega
    rcases hcases with h1 | h2
    · rw [h1] at hmod8
      omega
    · exact h2

/-- **The `5 ≤ u k` Lower Bound on Ceiling-Saturated Steps
(`ceiling_saturated_five_le_u`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), whenever `3 ≤ s (k + 1)`,
we have **`5 ≤ u k`** (since `u k` is odd, `u k ≠ 1`, and `u k ≠ 3`). -/
theorem ceiling_saturated_five_le_u {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs3 : 3 ≤ s (k + 1)) :
    5 ≤ u k := by
  have hcop := u_coprime_six_of_validBlockChain (by omega : k < K) hchain
  have huk_odd := hcop.1
  have huk_mod3 := hcop.2.1
  have hne1 : u k ≠ 1 := by
    intro h1
    have hle2 := (u_eq_one_forces_next_block_le_two hk1 hchain h1).1
    omega
  omega

/-! ## 3. `5×` Sharpened Coasting Single-Block Bound -/

/-- **`5×` Sharpened Coasting Single-Block Bound
(`coasting_five_mul_single_block_bound`)**:
In the coasting regime (`a_0 < 2^W`, `W ≤ blockSteps s m`), whenever
`3 ≤ s (m + 1)` (`m + 1 < K`), `5 ≤ u m` sharpens `coasting_single_block_bound`
by a factor of `5`:
`5 * 2^(blockSteps s m + s m - W) < 3^(blockSteps s m + 1)`. -/
theorem coasting_five_mul_single_block_bound {a_0 W : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : m + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (ha0 : a_0 < 2 ^ W) (hWT : W ≤ blockSteps s m)
    (hs3 : 3 ≤ s (m + 1)) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + s m)) :
    5 * 2 ^ (blockSteps s m + s m - W) < 3 ^ (blockSteps s m + 1) := by
  have hWT1 : W ≤ blockSteps s (m + 1) := by
    simp only [blockSteps]
    omega
  have hbound :=
    coasting_coprime_quotient_bound (by omega : m < K) hchain ha0 hWT1 hsurv
  have hu5 : 5 ≤ u m := ceiling_saturated_five_le_u hm1 hchain hs3
  have hmul :
      2 ^ (blockSteps s (m + 1) - W) * 5 ≤
        2 ^ (blockSteps s (m + 1) - W) * u m :=
    Nat.mul_le_mul_left _ hu5
  simp only [blockSteps] at hmul hbound ⊢
  omega

/-! ## 4. Quotient Contraction Laws Across `s k = 2` (`7×` and `113×`) -/

/-- **The `7×` Quotient Contraction Law Across `s k = 2`
(`seven_mul_u_next_le_of_s_eq_two`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), if `s k = 2` and
`6 ≤ s (k + 1)` (which holds whenever `0 < minSlack s (k + 2)`), then
`64 * u (k + 1) ≤ 9 * u k + 1` and **`7 * u (k + 1) ≤ u k`**. -/
theorem seven_mul_u_next_le_of_s_eq_two {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsk : s k = 2) (hsk1 : 6 ≤ s (k + 1)) :
    64 * u (k + 1) ≤ 9 * u k + 1 ∧ 7 * u (k + 1) ≤ u k := by
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [hsk] at hrec
  rcases hchain (k + 1) hk1 with ⟨_, huk1_odd, _⟩
  have hu1_pos : 1 ≤ u (k + 1) := by omega
  have hpow : 64 ≤ 2 ^ (s (k + 1)) := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hsk1
    simpa using this
  have h64 : 64 * u (k + 1) ≤ 9 * u k + 1 := by
    calc
      64 * u (k + 1) ≤ 2 ^ (s (k + 1)) * u (k + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 ^ 2 * u k + 1 := hrec
      _ = 9 * u k + 1 := by ring
  exact ⟨h64, by omega⟩

/-- **The `113×` Quotient Contraction Law Across `(s k, s (k + 1)) = (2, ≥ 10)`
(`hundred_thirteen_mul_u_next_le_of_s_eq_two_ten`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), if `s k = 2` and
`10 ≤ s (k + 1)` (forced after `(2, 6, 3, 3, 2)`), then
`1024 * u (k + 1) ≤ 9 * u k + 1` and **`113 * u (k + 1) ≤ u k`**. -/
theorem hundred_thirteen_mul_u_next_le_of_s_eq_two_ten
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsk : s k = 2) (hsk1 : 10 ≤ s (k + 1)) :
    1024 * u (k + 1) ≤ 9 * u k + 1 ∧ 113 * u (k + 1) ≤ u k := by
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [hsk] at hrec
  rcases hchain (k + 1) hk1 with ⟨_, huk1_odd, _⟩
  have hu1_pos : 1 ≤ u (k + 1) := by omega
  have hpow : 1024 ≤ 2 ^ (s (k + 1)) := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hsk1
    simpa using this
  have h1024 : 1024 * u (k + 1) ≤ 9 * u k + 1 := by
    calc
      1024 * u (k + 1) ≤ 2 ^ (s (k + 1)) * u (k + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 ^ 2 * u k + 1 := hrec
      _ = 9 * u k + 1 := by ring
  exact ⟨h1024, by omega⟩

end Mahler.UnitRigidity
