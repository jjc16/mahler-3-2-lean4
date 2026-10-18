import MahlerGrandSynthesis

/-!
# The Modulo-256 Single-Variable Classifier & Multi-Block Survival Sieve

This module proves that the single 8-bit residue
`X = (3^(s k) * u k + 1) % 256` simultaneously classifies both `s (k + 1)` and
`s (k + 2)` across `s (k + 1) ∈ {1, 2, 3, 4}`, eliminating **107 of the 128**
even residue classes of `X mod 256` within two blocks:

1. **Exact Modulo-256 Five-Way Classifier (`mod_256_five_way_classifier`)**:
   Along `ValidBlockChain a_0 s u K` (`k + 2 < K`), let
   `X = (3^(s k) * u k + 1) % 256`. Then:
   - `s (k + 1) = 1 ↔ X % 4 = 2` (64 classes: Immediate Mode A death),
   - `(s (k + 1) = 2 ∧ s (k + 2) = 1) ↔ X % 16 = 4` (16 classes: Delayed Mode A death),
   - `(s (k + 1) = 2 ∧ 2 ≤ s (k + 2) ∧ s (k + 2) ≤ 5) ↔ (X % 16 = 12 ∧ X ≠ 28)`
     (15 classes: Mode B slack exhaustion),
   - `(s (k + 1) = 2 ∧ 6 ≤ s (k + 2)) ↔ X = 28` (1 class: Post-`2` recovery),
   - `3 ≤ s (k + 1) ↔ X % 8 = 0` (32 classes: Ceiling-saturated continuation).
2. **Exact Modulo-64 Sub-Classifier for `s(k + 1) = 3`
   (`mod_64_s_eq_three_next_block_classifier`)**:
   Let `X64 = (3^(s k) * u k + 1) % 64`. Then:
   - `(s (k + 1) = 3 ∧ s (k + 2) = 1) ↔ (X64 = 24 ∨ X64 = 56)` (8 classes mod 256),
   - `(s (k + 1) = 3 ∧ s (k + 2) = 2) ↔ X64 = 8` (4 classes mod 256),
   - `(s (k + 1) = 3 ∧ 3 ≤ s (k + 2)) ↔ X64 = 40` (4 classes mod 256).
3. **Exact Modulo-128 Sub-Classifier for `s(k + 1) = 4`
   (`mod_128_s_eq_four_next_block_classifier`)**:
   Let `X128 = (3^(s k) * u k + 1) % 128`. Then:
   - `(s (k + 1) = 4 ∧ s (k + 2) = 1) ↔ (X128 = 16 ∨ X128 = 80)` (4 classes mod 256),
   - `(s (k + 1) = 4 ∧ s (k + 2) = 2) ↔ X128 = 48` (2 classes mod 256),
   - `(s (k + 1) = 4 ∧ 3 ≤ s (k + 2)) ↔ X128 = 112` (2 classes mod 256).
4. **The Two-Block Modulo-256 Survival Sieve (`mod_256_two_block_survival_sieve`)**:
   Surviving through step `blockSteps s (k + 2) + 2` forces `X = (3^(s k) * u k + 1) % 256`
   to avoid all 107 dead classes (`X = 28 ∨ X % 8 = 0`, with `X % 64 ∉ {24, 56}`
   and `X % 128 ∉ {16, 80}`).
-/

namespace Mahler.Mod256Sieve

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

/-! ## 1. Algebraic Valuation Classifiers for `2^s' * u' = Y` (`u'` Odd) -/

private theorem two_pow_mul_odd_mod_four_eq_two_iff {s' u' : ℕ}
    (hs' : 1 ≤ s') (hu' : u' % 2 = 1) :
    s' = 1 ↔ (2 ^ s' * u') % 4 = 2 := by
  constructor
  · intro h1
    subst h1
    omega
  · intro hmod
    by_contra hne1
    have hge2 : 2 ≤ s' := by omega
    have hdvd4 : 4 ∣ 2 ^ s' * u' :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge2) u'
    have h0 := Nat.mod_eq_zero_of_dvd hdvd4
    omega

private theorem two_pow_mul_odd_mod_eight_eq_four_iff {s' u' : ℕ}
    (hs' : 1 ≤ s') (hu' : u' % 2 = 1) :
    s' = 2 ↔ (2 ^ s' * u') % 8 = 4 := by
  constructor
  · intro h2
    subst h2
    omega
  · intro hmod
    by_cases h1 : s' = 1
    · subst h1
      omega
    · by_cases h2 : s' = 2
      · exact h2
      · have hge3 : 3 ≤ s' := by omega
        have hdvd8 : 8 ∣ 2 ^ s' * u' :=
          dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge3) u'
        have h0 := Nat.mod_eq_zero_of_dvd hdvd8
        omega

private theorem three_le_iff_two_pow_mul_odd_mod_eight_eq_zero {s' u' : ℕ}
    (hs' : 1 ≤ s') (hu' : u' % 2 = 1) :
    3 ≤ s' ↔ (2 ^ s' * u') % 8 = 0 := by
  constructor
  · intro hge3
    have hdvd8 : 8 ∣ 2 ^ s' * u' :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge3) u'
    exact Nat.mod_eq_zero_of_dvd hdvd8
  · intro h0
    by_contra hlt3
    have hcases : s' = 1 ∨ s' = 2 := by omega
    rcases hcases with rfl | rfl <;> omega

/-! ## 2. Exact Modulo-256 Five-Way Classifier -/

/-- **Exact Modulo-256 Five-Way Classifier (`mod_256_five_way_classifier`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 2 < K`), let
`X = (3^(s k) * u k + 1) % 256`. Then:
1. `s (k + 1) = 1 ↔ X % 4 = 2`,
2. `(s (k + 1) = 2 ∧ s (k + 2) = 1) ↔ X % 16 = 4`,
3. `(s (k + 1) = 2 ∧ 2 ≤ s (k + 2) ∧ s (k + 2) ≤ 5) ↔ (X % 16 = 12 ∧ X ≠ 28)`,
4. `(s (k + 1) = 2 ∧ 6 ≤ s (k + 2)) ↔ X = 28`,
5. `3 ≤ s (k + 1) ↔ X % 8 = 0`. -/
theorem mod_256_five_way_classifier {a_0 : ℕ} {s u : ℕ → ℕ} {K k X : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hX : X = (3 ^ (s k) * u k + 1) % 256) :
    (s (k + 1) = 1 ↔ X % 4 = 2) ∧
      ((s (k + 1) = 2 ∧ s (k + 2) = 1) ↔ X % 16 = 4) ∧
      ((s (k + 1) = 2 ∧ 2 ≤ s (k + 2) ∧ s (k + 2) ≤ 5) ↔
        (X % 16 = 12 ∧ X ≠ 28)) ∧
      ((s (k + 1) = 2 ∧ 6 ≤ s (k + 2)) ↔ X = 28) ∧
      (3 ≤ s (k + 1) ↔ X % 8 = 0) := by
  have hsk1 : 1 ≤ s (k + 1) := (hchain (k + 1) (by omega)).1
  have huk1 : u (k + 1) % 2 = 1 := (hchain (k + 1) (by omega)).2.1
  have hsk2 : 1 ≤ s (k + 2) := (hchain (k + 2) hk2).1
  have huk2 : u (k + 2) % 2 = 1 := (hchain (k + 2) hk2).2.1
  have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hrec2 : 2 ^ (s (k + 2)) * u (k + 2) = 3 ^ (s (k + 1)) * u (k + 1) + 1 :=
    coprime_quotient_recurrence (by omega : (k + 1) + 1 < K) hchain
  have hX_def : X = (2 ^ (s (k + 1)) * u (k + 1)) % 256 := by
    rw [hX, ← hrec1]
  have hX_mod4 : X % 4 = (2 ^ (s (k + 1)) * u (k + 1)) % 4 := by
    rw [hX_def]
    omega
  have hX_mod8 : X % 8 = (2 ^ (s (k + 1)) * u (k + 1)) % 8 := by
    rw [hX_def]
    omega
  have hX_mod16 : X % 16 = (2 ^ (s (k + 1)) * u (k + 1)) % 16 := by
    rw [hX_def]
    omega
  have hc1 : s (k + 1) = 1 ↔ X % 4 = 2 := by
    rw [hX_mod4]
    exact two_pow_mul_odd_mod_four_eq_two_iff hsk1 huk1
  have hc5 : 3 ≤ s (k + 1) ↔ X % 8 = 0 := by
    rw [hX_mod8]
    exact three_le_iff_two_pow_mul_odd_mod_eight_eq_zero hsk1 huk1
  have hs2_iff : s (k + 1) = 2 ↔ X % 8 = 4 := by
    rw [hX_mod8]
    exact two_pow_mul_odd_mod_eight_eq_four_iff hsk1 huk1
  have hwhen2 :
      s (k + 1) = 2 →
        X = 4 * (u (k + 1) % 64) ∧
          (s (k + 2) = 1 ↔ u (k + 1) % 4 = 1) ∧
          ((2 ≤ s (k + 2) ∧ s (k + 2) ≤ 5) ↔
            (u (k + 1) % 4 = 3 ∧ u (k + 1) % 64 ≠ 7)) ∧
          (6 ≤ s (k + 2) ↔ u (k + 1) % 64 = 7) := by
    intro hs2
    have hX4 : X = 4 * (u (k + 1) % 64) := by
      rw [hX_def, hs2]
      simpa using Nat.mul_mod_mul_left 4 (u (k + 1)) 64
    have hrec2' : 2 ^ (s (k + 2)) * u (k + 2) = 9 * u (k + 1) + 1 := by
      rw [hs2] at hrec2
      simpa using hrec2
    exact ⟨hX4, post_two_mod_64_three_way_partition huk1 hsk2 huk2 hrec2'⟩
  refine ⟨hc1, ?_, ?_, ?_, hc5⟩
  · constructor
    · rintro ⟨hs2, hs2_1⟩
      rcases hwhen2 hs2 with ⟨hX4, hp1, _, _⟩
      have hu4 := hp1.mp hs2_1
      omega
    · intro hX16
      have hs2 : s (k + 1) = 2 := hs2_iff.mpr (by omega)
      rcases hwhen2 hs2 with ⟨hX4, hp1, _, _⟩
      exact ⟨hs2, hp1.mpr (by omega)⟩
  · constructor
    · rintro ⟨hs2, h25⟩
      rcases hwhen2 hs2 with ⟨hX4, _, hp2, _⟩
      have hu := hp2.mp h25
      omega
    · rintro ⟨hX16, hX28⟩
      have hs2 : s (k + 1) = 2 := hs2_iff.mpr (by omega)
      rcases hwhen2 hs2 with ⟨hX4, _, hp2, _⟩
      exact ⟨hs2, hp2.mpr ⟨by omega, by omega⟩⟩
  · constructor
    · rintro ⟨hs2, hge6⟩
      rcases hwhen2 hs2 with ⟨hX4, _, _, hp3⟩
      have hu64 := hp3.mp hge6
      omega
    · intro hX28
      have hs2 : s (k + 1) = 2 := hs2_iff.mpr (by omega)
      rcases hwhen2 hs2 with ⟨hX4, _, _, hp3⟩
      exact ⟨hs2, hp3.mpr (by omega)⟩

/-! ## 3. Exact Sub-Classifiers for `s(k + 1) = 3` (`mod 64`) & `s(k + 1) = 4` (`mod 128`) -/

/-- **Exact Modulo-64 Sub-Classifier for `s(k + 1) = 3`
(`mod_64_s_eq_three_next_block_classifier`)**:
Along `ValidBlockChain a_0 s u K` (`k + 2 < K`), let
`X64 = (3^(s k) * u k + 1) % 64`. Then:
1. `(s (k + 1) = 3 ∧ s (k + 2) = 1) ↔ (X64 = 24 ∨ X64 = 56)`,
2. `(s (k + 1) = 3 ∧ s (k + 2) = 2) ↔ X64 = 8`,
3. `(s (k + 1) = 3 ∧ 3 ≤ s (k + 2)) ↔ X64 = 40`. -/
theorem mod_64_s_eq_three_next_block_classifier
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k X64 : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hX64 : X64 = (3 ^ (s k) * u k + 1) % 64) :
    ((s (k + 1) = 3 ∧ s (k + 2) = 1) ↔ (X64 = 24 ∨ X64 = 56)) ∧
      ((s (k + 1) = 3 ∧ s (k + 2) = 2) ↔ X64 = 8) ∧
      ((s (k + 1) = 3 ∧ 3 ≤ s (k + 2)) ↔ X64 = 40) := by
  have hsk1 : 1 ≤ s (k + 1) := (hchain (k + 1) (by omega)).1
  have huk1 : u (k + 1) % 2 = 1 := (hchain (k + 1) (by omega)).2.1
  have hsk2 : 1 ≤ s (k + 2) := (hchain (k + 2) hk2).1
  have huk2 : u (k + 2) % 2 = 1 := (hchain (k + 2) hk2).2.1
  have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hrec2 : 2 ^ (s (k + 2)) * u (k + 2) = 3 ^ (s (k + 1)) * u (k + 1) + 1 :=
    coprime_quotient_recurrence (by omega : (k + 1) + 1 < K) hchain
  have hX64_def : X64 = (2 ^ (s (k + 1)) * u (k + 1)) % 64 := by
    rw [hX64, ← hrec1]
  have hs3_iff : s (k + 1) = 3 ↔ X64 % 16 = 8 := by
    rw [hX64_def]
    constructor
    · intro h3
      rw [h3]
      omega
    · intro hmod
      by_cases hlt3 : s (k + 1) < 3
      · have hcases : s (k + 1) = 1 ∨ s (k + 1) = 2 := by omega
        rcases hcases with h | h <;> { rw [h] at hmod; omega }
      · by_cases h3 : s (k + 1) = 3
        · exact h3
        · have hge4 : 4 ≤ s (k + 1) := by omega
          have hdvd16 : 16 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
            dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge4) _
          have h0 := Nat.mod_eq_zero_of_dvd hdvd16
          omega
  have hwhen3 :
      s (k + 1) = 3 →
        X64 = 8 * (u (k + 1) % 8) ∧
          (s (k + 2) = 1 ↔ (u (k + 1) % 8 = 3 ∨ u (k + 1) % 8 = 7)) ∧
          (s (k + 2) = 2 ↔ u (k + 1) % 8 = 1) ∧
          (3 ≤ s (k + 2) ↔ u (k + 1) % 8 = 5) := by
    intro hs3
    have hX8 : X64 = 8 * (u (k + 1) % 8) := by
      rw [hX64_def, hs3]
      simpa using Nat.mul_mod_mul_left 8 (u (k + 1)) 8
    have hs2_2 := s_eq_two_iff_mod_eight huk1 hsk2 huk2 hrec2
    have hs2_3 := three_le_s_iff_mod_eight huk1 hsk2 huk2 hrec2
    rw [hs3] at hs2_2 hs2_3
    have h2_iff : s (k + 2) = 2 ↔ u (k + 1) % 8 = 1 := by
      simpa using hs2_2
    have h3_iff : 3 ≤ s (k + 2) ↔ u (k + 1) % 8 = 5 := by
      simpa using hs2_3
    have h1_iff : s (k + 2) = 1 ↔ (u (k + 1) % 8 = 3 ∨ u (k + 1) % 8 = 7) := by
      constructor
      · intro h1
        have hn2 : u (k + 1) % 8 ≠ 1 := by
          intro hu1
          have := h2_iff.mpr hu1
          omega
        have hn3 : u (k + 1) % 8 ≠ 5 := by
          intro hu5
          have := h3_iff.mpr hu5
          omega
        omega
      · intro hu37
        have hn2 : s (k + 2) ≠ 2 := by
          intro h2
          have := h2_iff.mp h2
          omega
        have hn3 : ¬ (3 ≤ s (k + 2)) := by
          intro h3
          have := h3_iff.mp h3
          omega
        omega
    exact ⟨hX8, h1_iff, h2_iff, h3_iff⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hs3, h1⟩
      rcases hwhen3 hs3 with ⟨hX8, hp1, _, _⟩
      have := hp1.mp h1
      omega
    · intro hX24
      have hs3 : s (k + 1) = 3 := hs3_iff.mpr (by omega)
      rcases hwhen3 hs3 with ⟨hX8, hp1, _, _⟩
      exact ⟨hs3, hp1.mpr (by omega)⟩
  · constructor
    · rintro ⟨hs3, h2⟩
      rcases hwhen3 hs3 with ⟨hX8, _, hp2, _⟩
      have := hp2.mp h2
      omega
    · intro hX8'
      have hs3 : s (k + 1) = 3 := hs3_iff.mpr (by omega)
      rcases hwhen3 hs3 with ⟨hX8, _, hp2, _⟩
      exact ⟨hs3, hp2.mpr (by omega)⟩
  · constructor
    · rintro ⟨hs3, h3⟩
      rcases hwhen3 hs3 with ⟨hX8, _, _, hp3⟩
      have := hp3.mp h3
      omega
    · intro hX40
      have hs3 : s (k + 1) = 3 := hs3_iff.mpr (by omega)
      rcases hwhen3 hs3 with ⟨hX8, _, _, hp3⟩
      exact ⟨hs3, hp3.mpr (by omega)⟩

/-- **Exact Modulo-128 Sub-Classifier for `s(k + 1) = 4`
(`mod_128_s_eq_four_next_block_classifier`)**:
Along `ValidBlockChain a_0 s u K` (`k + 2 < K`), let
`X128 = (3^(s k) * u k + 1) % 128`. Then:
1. `(s (k + 1) = 4 ∧ s (k + 2) = 1) ↔ (X128 = 16 ∨ X128 = 80)`,
2. `(s (k + 1) = 4 ∧ s (k + 2) = 2) ↔ X128 = 48`,
3. `(s (k + 1) = 4 ∧ 3 ≤ s (k + 2)) ↔ X128 = 112`. -/
theorem mod_128_s_eq_four_next_block_classifier
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k X128 : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hX128 : X128 = (3 ^ (s k) * u k + 1) % 128) :
    ((s (k + 1) = 4 ∧ s (k + 2) = 1) ↔ (X128 = 16 ∨ X128 = 80)) ∧
      ((s (k + 1) = 4 ∧ s (k + 2) = 2) ↔ X128 = 48) ∧
      ((s (k + 1) = 4 ∧ 3 ≤ s (k + 2)) ↔ X128 = 112) := by
  have hsk1 : 1 ≤ s (k + 1) := (hchain (k + 1) (by omega)).1
  have huk1 : u (k + 1) % 2 = 1 := (hchain (k + 1) (by omega)).2.1
  have hsk2 : 1 ≤ s (k + 2) := (hchain (k + 2) hk2).1
  have huk2 : u (k + 2) % 2 = 1 := (hchain (k + 2) hk2).2.1
  have hrec1 := coprime_quotient_recurrence (by omega : k + 1 < K) hchain
  have hrec2 : 2 ^ (s (k + 2)) * u (k + 2) = 3 ^ (s (k + 1)) * u (k + 1) + 1 :=
    coprime_quotient_recurrence (by omega : (k + 1) + 1 < K) hchain
  have hX128_def : X128 = (2 ^ (s (k + 1)) * u (k + 1)) % 128 := by
    rw [hX128, ← hrec1]
  have hs4_iff : s (k + 1) = 4 ↔ X128 % 32 = 16 := by
    rw [hX128_def]
    constructor
    · intro h4
      rw [h4]
      omega
    · intro hmod
      by_cases hlt4 : s (k + 1) < 4
      · have hcases : s (k + 1) = 1 ∨ s (k + 1) = 2 ∨ s (k + 1) = 3 := by omega
        rcases hcases with h | h | h <;> { rw [h] at hmod; omega }
      · by_cases h4 : s (k + 1) = 4
        · exact h4
        · have hge5 : 5 ≤ s (k + 1) := by omega
          have hdvd32 : 32 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
            dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge5) _
          have h0 := Nat.mod_eq_zero_of_dvd hdvd32
          omega
  have hwhen4 :
      s (k + 1) = 4 →
        X128 = 16 * (u (k + 1) % 8) ∧
          (s (k + 2) = 1 ↔ (u (k + 1) % 8 = 1 ∨ u (k + 1) % 8 = 5)) ∧
          (s (k + 2) = 2 ↔ u (k + 1) % 8 = 3) ∧
          (3 ≤ s (k + 2) ↔ u (k + 1) % 8 = 7) := by
    intro hs4
    have hX16 : X128 = 16 * (u (k + 1) % 8) := by
      rw [hX128_def, hs4]
      simpa using Nat.mul_mod_mul_left 16 (u (k + 1)) 8
    have hs2_2 := s_eq_two_iff_mod_eight huk1 hsk2 huk2 hrec2
    have hs2_3 := three_le_s_iff_mod_eight huk1 hsk2 huk2 hrec2
    rw [hs4] at hs2_2 hs2_3
    have h2_iff : s (k + 2) = 2 ↔ u (k + 1) % 8 = 3 := by
      simpa using hs2_2
    have h3_iff : 3 ≤ s (k + 2) ↔ u (k + 1) % 8 = 7 := by
      simpa using hs2_3
    have h1_iff : s (k + 2) = 1 ↔ (u (k + 1) % 8 = 1 ∨ u (k + 1) % 8 = 5) := by
      constructor
      · intro h1
        have hn2 : u (k + 1) % 8 ≠ 3 := by
          intro hu3
          have := h2_iff.mpr hu3
          omega
        have hn3 : u (k + 1) % 8 ≠ 7 := by
          intro hu7
          have := h3_iff.mpr hu7
          omega
        omega
      · intro hu15
        have hn2 : s (k + 2) ≠ 2 := by
          intro h2
          have := h2_iff.mp h2
          omega
        have hn3 : ¬ (3 ≤ s (k + 2)) := by
          intro h3
          have := h3_iff.mp h3
          omega
        omega
    exact ⟨hX16, h1_iff, h2_iff, h3_iff⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hs4, h1⟩
      rcases hwhen4 hs4 with ⟨hX16, hp1, _, _⟩
      have := hp1.mp h1
      omega
    · intro hX16'
      have hs4 : s (k + 1) = 4 := hs4_iff.mpr (by omega)
      rcases hwhen4 hs4 with ⟨hX16, hp1, _, _⟩
      exact ⟨hs4, hp1.mpr (by omega)⟩
  · constructor
    · rintro ⟨hs4, h2⟩
      rcases hwhen4 hs4 with ⟨hX16, _, hp2, _⟩
      have := hp2.mp h2
      omega
    · intro hX48
      have hs4 : s (k + 1) = 4 := hs4_iff.mpr (by omega)
      rcases hwhen4 hs4 with ⟨hX16, _, hp2, _⟩
      exact ⟨hs4, hp2.mpr (by omega)⟩
  · constructor
    · rintro ⟨hs4, h3⟩
      rcases hwhen4 hs4 with ⟨hX16, _, _, hp3⟩
      have := hp3.mp h3
      omega
    · intro hX112
      have hs4 : s (k + 1) = 4 := hs4_iff.mpr (by omega)
      rcases hwhen4 hs4 with ⟨hX16, _, _, hp3⟩
      exact ⟨hs4, hp3.mpr (by omega)⟩

/-! ## 4. The Two-Block Modulo-256 Survival Sieve -/

/-- **Two-Block Modulo-256 Survival Sieve (`mod_256_two_block_survival_sieve`)**:
Along `ValidBlockChain a_0 s u K` (`k + 2 < K`), if the trajectory survives
through step `blockSteps s (k + 3)`, then `X = (3^(s k) * u k + 1) % 256`
satisfies:
- `X = 28 ∨ X % 8 = 0`,
- `X % 64 ≠ 24 ∧ X % 64 ≠ 56`, and
- `X % 128 ≠ 16 ∧ X % 128 ≠ 80`. -/
theorem mod_256_two_block_survival_sieve
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k X X64 X128 : ℕ}
    (hk2 : k + 2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos2 : 0 < minSlack s (k + 2))
    (hpos3 : 0 < minSlack s (k + 3))
    (hX : X = (3 ^ (s k) * u k + 1) % 256)
    (hX64 : X64 = (3 ^ (s k) * u k + 1) % 64)
    (hX128 : X128 = (3 ^ (s k) * u k + 1) % 128) :
    (X = 28 ∨ X % 8 = 0) ∧
      (X64 ≠ 24 ∧ X64 ≠ 56) ∧
      (X128 ≠ 16 ∧ X128 ≠ 80) := by
  have hs1_ge2 : 2 ≤ s (k + 1) := two_le_of_minSlack_pos s hpos2
  have hs2_ge2 : 2 ≤ s (k + 2) := two_le_of_minSlack_pos s hpos3
  have hc256 := mod_256_five_way_classifier hk2 hchain hX
  have hc64 := mod_64_s_eq_three_next_block_classifier hk2 hchain hX64
  have hc128 := mod_128_s_eq_four_next_block_classifier hk2 hchain hX128
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_or_lt_of_le hs1_ge2 with hs1_eq2 | hs1_ge3
    · left
      have hs2_ge6 : 6 ≤ s (k + 2) :=
        six_le_after_two_of_minSlack_pos s hs1_eq2.symm hpos3
      exact hc256.2.2.2.1.mp ⟨hs1_eq2.symm, hs2_ge6⟩
    · right
      exact hc256.2.2.2.2.mp hs1_ge3
  · constructor <;> intro hbad
    · have := (hc64.1.mpr (Or.inl hbad)).2
      omega
    · have := (hc64.1.mpr (Or.inr hbad)).2
      omega
  · constructor <;> intro hbad
    · have := (hc128.1.mpr (Or.inl hbad)).2
      omega
    · have := (hc128.1.mpr (Or.inr hbad)).2
      omega

end Mahler.Mod256Sieve
