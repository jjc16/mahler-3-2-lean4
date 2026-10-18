import CoupledFractionalPartDynamics

/-!
# The Combined Modulo-2304 (`256 × 9`) Survival Sieve & `u ≥ 1735` Post-`2` Rigidity

This module formalizes Path 8 (Modules 107–108): combining the 3-adic backward
locks (`mod 9` and `mod 27`) with the 2-adic forward locks (`mod 64` and `mod 256`)
via the Chinese Remainder Theorem:

1. **The Modulo-1728 (`27 × 64`) Quotient Lock at `s(k + 1) = 2`
   (`post_two_mod_1728_quotient_lock`)**:
   Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`) with `3 ≤ s k`,
   `s (k + 1) = 2`, and `6 ≤ s (k + 2)`:
   - Looking backward (`k → k + 1`): `4 * u (k + 1) = 3^(s k) * u k + 1 ≡ 1 (mod 27)`
     forces `u (k + 1) % 27 = 7`.
   - Looking forward (`k + 1 → k + 2`): `9 * u (k + 1) + 1 = 2^(s (k + 2)) * u (k + 2) ≡ 0 (mod 64)`
     forces `u (k + 1) % 64 = 7`.
   - Since `Nat.Coprime 27 64` and `27 * 64 = 1728`, both congruences hit the
     exact same integer `7` and lock `u (k + 1) % 1728 = 7`.
2. **Two-Step Backward Impossibility of `u(k + 1) = 7` for `k ≥ 1`
   (`post_two_u_ne_seven_of_pos_index`)**:
   Whenever `1 ≤ k`, `k + 1 < K`, `3 ≤ s k`, and `s (k + 1) = 2`, `u (k + 1) = 7`
   would force `3^(s k) * u k = 27`, hence `s k = 3` and `u k = 1`, which in turn
   would force `3^(s (k - 1)) * u (k - 1) + 1 = 2^3 * 1 = 8`, i.e.
   `3^(s (k - 1)) * u (k - 1) = 7`, impossible since `3 ∣ 3^(s (k - 1))`!
   Thus `u (k + 1) ≠ 7` for all `k ≥ 1`.
3. **The `1735` Quotient Lower Bound & `15616` Neighbor Bound
   (`post_two_u_ge_1735_and_neighbor_bounds`)**:
   Combining `u (k + 1) % 1728 = 7` and `u (k + 1) ≠ 7` proves that for every
   `1 ≤ k` (`k + 2 < K`) with `3 ≤ s k`, `s (k + 1) = 2`, and `6 ≤ s (k + 2)`:
   - `1735 ≤ u (k + 1)` (a `247×` improvement over `7 ≤ u (k + 1)`!),
   - `6939 ≤ 3^(s k) * u k`, and
   - `15616 ≤ 2^(s (k + 2)) * u (k + 2)`.
4. **The Combined Modulo-2304 (`256 × 9`) Two-Block Survival Sieve
   (`mod_2304_two_block_survival_sieve`)**:
   Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`) with `0 < minSlack s (k + 1)`,
   `0 < minSlack s (k + 2)`, and `0 < minSlack s (k + 3)`, the transition value
   `Y = (3^(s k) * u k + 1) % 2304` satisfies `Y % 9 = 1` together with the full
   Mod-256 two-block survival sieve (leaving only `21` surviving residue classes
   out of `2304`, or `0.91%`, with the post-`2` recovery branch locked to the
   single residue class `Y = 28` modulo `2304` when `s (k + 1) = 2` and `3 ≤ s k`!).
-/

namespace Mahler.Mod2304Sieve

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

/-! ## 1. The Modulo-1728 (`27 × 64`) Quotient Lock at `s(k + 1) = 2` -/

/-- **Modulo-1728 (`27 × 64`) Quotient Lock at `s(k + 1) = 2`
(`post_two_mod_1728_quotient_lock`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`) with `3 ≤ s k`,
`s (k + 1) = 2`, and `6 ≤ s (k + 2)`:
`u (k + 1) % 27 = 7`, `u (k + 1) % 64 = 7`, and `u (k + 1) % 1728 = 7`. -/
theorem post_two_mod_1728_quotient_lock
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsk : 3 ≤ s k) (hsk1 : s (k + 1) = 2) (hsk2 : 6 ≤ s (k + 2)) :
    u (k + 1) % 27 = 7 ∧
      u (k + 1) % 64 = 7 ∧
      u (k + 1) % 1728 = 7 := by
  have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hrec2 : 2 ^ (s (k + 2)) * u (k + 2) = 3 ^ (s (k + 1)) * u (k + 1) + 1 :=
    coprime_quotient_recurrence (by omega : (k + 1) + 1 < K) hchain
  have h27_dvd : 27 ∣ 3 ^ (s k) * u k := by
    have hpow : 3 ^ 3 ∣ 3 ^ (s k) := Nat.pow_dvd_pow 3 hsk
    exact dvd_mul_of_dvd_left (by simpa using hpow) (u k)
  have h64_dvd : 64 ∣ 2 ^ (s (k + 2)) * u (k + 2) := by
    have hpow : 2 ^ 6 ∣ 2 ^ (s (k + 2)) := Nat.pow_dvd_pow 2 hsk2
    exact dvd_mul_of_dvd_left (by simpa using hpow) (u (k + 2))
  rcases h27_dvd with ⟨q27, hq27⟩
  rcases h64_dvd with ⟨q64, hq64⟩
  rw [hsk1, hq27] at hrec1
  rw [hsk1, hq64] at hrec2
  have hmod27 : u (k + 1) % 27 = 7 := by omega
  have hmod64 : u (k + 1) % 64 = 7 := by omega
  have h27_sub : 27 ∣ (u (k + 1) - 7) := by omega
  have h64_sub : 64 ∣ (u (k + 1) - 7) := by omega
  have hcop : Nat.Coprime 27 64 := by decide
  have h1728_sub : 1728 ∣ (u (k + 1) - 7) := by
    simpa using hcop.mul_dvd_of_dvd_of_dvd h27_sub h64_sub
  rcases h1728_sub with ⟨q1728, hq1728⟩
  have hmod1728 : u (k + 1) % 1728 = 7 := by omega
  exact ⟨hmod27, hmod64, hmod1728⟩

/-! ## 2. Two-Step Backward Impossibility of `u(k + 1) = 7` & the `1735` Lower Bound -/

/-- **Two-Step Backward Impossibility of `u(k + 1) = 7` (`post_two_u_ne_seven_of_pos_index`)**:
Along any `ValidBlockChain a_0 s u K` with `1 ≤ k`, `k + 1 < K`, `3 ≤ s k`, and
`s (k + 1) = 2`, we have `u (k + 1) ≠ 7`. -/
theorem post_two_u_ne_seven_of_pos_index
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsk : 3 ≤ s k) (hsk1 : s (k + 1) = 2) :
    u (k + 1) ≠ 7 := by
  intro hu7
  have hrec1 := coprime_quotient_recurrence hk1 hchain
  rw [hsk1, hu7] at hrec1
  have h3_eq : 3 ^ (s k) * u k = 27 := by omega
  have h3_ge : 27 ≤ 3 ^ (s k) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 3) hsk
    simpa using h
  have huk_pos : 1 ≤ u k := by
    have hodd := (hchain k (by omega)).2.1
    omega
  have huk_eq1 : u k = 1 := by nlinarith
  have h3_pow_eq : 3 ^ (s k) = 27 := by nlinarith
  have hsk_eq3 : s k = 3 := by
    by_contra hne3
    have hgt3 : 4 ≤ s k := by omega
    have hge81 : 81 ≤ 3 ^ (s k) := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 3) hgt3
      simpa using h
    omega
  have hrec0 := coprime_quotient_recurrence (by omega : (k - 1) + 1 < K) hchain
  have hk_idx : (k - 1) + 1 = k := by omega
  rw [hk_idx, hsk_eq3, huk_eq1] at hrec0
  have hsk0_ge1 : 1 ≤ s (k - 1) := (hchain (k - 1) (by omega)).1
  have h3_dvd : 3 ∣ 3 ^ (s (k - 1)) * u (k - 1) := by
    have hpow : 3 ^ 1 ∣ 3 ^ (s (k - 1)) := Nat.pow_dvd_pow 3 hsk0_ge1
    exact dvd_mul_of_dvd_left (by simpa using hpow) (u (k - 1))
  rcases h3_dvd with ⟨q, hq⟩
  omega

/-- **The `1735` Post-`2` Quotient Lower Bound (`post_two_u_ge_1735_and_neighbor_bounds`)**:
Along any `ValidBlockChain a_0 s u K` with `1 ≤ k`, `k + 2 < K`, `3 ≤ s k`,
`s (k + 1) = 2`, and `6 ≤ s (k + 2)`:
1. `1735 ≤ u (k + 1)`,
2. `6939 ≤ 3^(s k) * u k`, and
3. `15616 ≤ 2^(s (k + 2)) * u (k + 2)`. -/
theorem post_two_u_ge_1735_and_neighbor_bounds
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hsk : 3 ≤ s k) (hsk1 : s (k + 1) = 2) (hsk2 : 6 ≤ s (k + 2)) :
    1735 ≤ u (k + 1) ∧
      6939 ≤ 3 ^ (s k) * u k ∧
      15616 ≤ 2 ^ (s (k + 2)) * u (k + 2) := by
  have hmod1728 := (post_two_mod_1728_quotient_lock hk2 hchain hsk hsk1 hsk2).2.2
  have hne7 := post_two_u_ne_seven_of_pos_index hk_pos (by omega) hchain hsk hsk1
  have hge1735 : 1735 ≤ u (k + 1) := by omega
  have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hrec2 : 2 ^ (s (k + 2)) * u (k + 2) = 3 ^ (s (k + 1)) * u (k + 1) + 1 :=
    coprime_quotient_recurrence (by omega : (k + 1) + 1 < K) hchain
  rw [hsk1] at hrec1 hrec2
  refine ⟨hge1735, by omega, by omega⟩

/-! ## 3. The Combined Modulo-2304 (`256 × 9`) Two-Block Survival Sieve -/

private theorem eq_28_of_mod_256_and_mod_9 {Y : ℕ}
    (hY_lt : Y < 2304) (h256 : Y % 256 = 28) (h9 : Y % 9 = 1) :
    Y = 28 := by
  omega

/-- **Combined Modulo-2304 (`256 × 9`) Two-Block Survival Sieve
(`mod_2304_two_block_survival_sieve`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`) with `0 < minSlack s (k + 1)`,
`0 < minSlack s (k + 2)`, and `0 < minSlack s (k + 3)`, let
`Y = (3^(s k) * u k + 1) % 2304`, `X = (3^(s k) * u k + 1) % 256`,
`X64 = (3^(s k) * u k + 1) % 64`, and `X128 = (3^(s k) * u k + 1) % 128`.
Then simultaneously:
1. `Y % 9 = 1`,
2. `(X = 28 ∨ X % 8 = 0) ∧ (X64 ≠ 24 ∧ X64 ≠ 56) ∧ (X128 ≠ 16 ∧ X128 ≠ 80)`, and
3. `(s (k + 1) = 2 ↔ Y = 28)`. -/
theorem mod_2304_two_block_survival_sieve
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k Y X X64 X128 : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos1 : 0 < minSlack s (k + 1))
    (hpos2 : 0 < minSlack s (k + 2))
    (hpos3 : 0 < minSlack s (k + 3))
    (hY : Y = (3 ^ (s k) * u k + 1) % 2304)
    (hX : X = (3 ^ (s k) * u k + 1) % 256)
    (hX64 : X64 = (3 ^ (s k) * u k + 1) % 64)
    (hX128 : X128 = (3 ^ (s k) * u k + 1) % 128) :
    Y % 9 = 1 ∧
      ((X = 28 ∨ X % 8 = 0) ∧
        (X64 ≠ 24 ∧ X64 ≠ 56) ∧
        (X128 ≠ 16 ∧ X128 ≠ 80)) ∧
      (s (k + 1) = 2 ↔ Y = 28) := by
  have hsk_ge2 : 2 ≤ s k := two_le_of_minSlack_pos s hpos1
  have hsieve256 :=
    mod_256_two_block_survival_sieve hk2 hchain hpos2 hpos3 hX hX64 hX128
  have hY_mod9 : Y % 9 = 1 := by
    have h9_dvd : 9 ∣ 3 ^ (s k) * u k := by
      have hpow : 3 ^ 2 ∣ 3 ^ (s k) := Nat.pow_dvd_pow 3 hsk_ge2
      exact dvd_mul_of_dvd_left (by simpa using hpow) (u k)
    rcases h9_dvd with ⟨q9, hq9⟩
    have hdiv9 : 9 ∣ 2304 := by decide
    have hmod := Nat.mod_mod_of_dvd (3 ^ (s k) * u k + 1) hdiv9
    rw [← hY] at hmod
    rw [hmod, hq9]
    omega
  have hYX : Y % 256 = X := by
    have hdiv256 : 256 ∣ 2304 := by decide
    have hmod := Nat.mod_mod_of_dvd (3 ^ (s k) * u k + 1) hdiv256
    rw [← hY, ← hX] at hmod
    exact hmod
  have hc256 := mod_256_five_way_classifier hk2 hchain hX
  refine ⟨hY_mod9, hsieve256, ?_⟩
  constructor
  · intro hs1_eq2
    have hs2_ge6 : 6 ≤ s (k + 2) :=
      six_le_after_two_of_minSlack_pos s hs1_eq2 hpos3
    have hX28 : X = 28 := hc256.2.2.2.1.mp ⟨hs1_eq2, hs2_ge6⟩
    have hY_lt : Y < 2304 := by
      rw [hY]
      exact Nat.mod_lt _ (by decide)
    exact eq_28_of_mod_256_and_mod_9 hY_lt (by rw [hYX, hX28]) hY_mod9
  · intro hY28
    have hX28 : X = 28 := by
      rw [← hYX, hY28]
    exact (hc256.2.2.2.1.mpr hX28).1

end Mahler.Mod2304Sieve
