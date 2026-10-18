import SlackDeadEndsAndWitnesses

/-!
# Capstone: Converse Coprime Chain Equivalence, The 113-Step Record-Holder & 82-Module Synthesis

This capstone module completes our 82-module Lean 4 formalization of Mahler's
`3/2` problem:

1. **Two-Way Equivalence Between `ValidBlockChain` and the Coprime Recurrence
   (`validBlockChain_of_coprime_recurrence`, `validBlockChain_iff_coprime_recurrence`)**:
   `ValidBlockChain a_0 s u K` holds if and only if for all `k < K`,
   `1 ≤ s k ∧ u k % 2 = 1`, `3 * a_0 + 1 = 2^(s 0) * u 0` (when `0 < K`), and
   for all `k + 1 < K`, `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1`.
2. **Exact 113-Step Survival and 114-Step Death of the 55-Bit Record-Holder
   (`recordHolderA0_exact_113_survival_and_114_death`)**:
   For the 55-bit integer `recordHolderA0 = 29871555608238677 < 2^55`:
   - `∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 113` (survives 113 steps,
     achieving a post-bit-length coasting excess of `E = 113 - 55 = 58` steps), and
   - `¬ ∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 114` (dies at step 114).
3. **Exact Modulo-64 Three-Way Branch Partition After `s = 2`
   (`post_two_mod_64_three_way_partition`)**:
   Whenever `2^s' * u' = 9 * u + 1` (`u, u'` odd, `1 ≤ s'`), the 32 odd residue
   classes of `u mod 64` partition into:
   - **Mode A (`s' = 1`):** `u % 4 = 1` (16 classes),
   - **Mode B (`2 ≤ s' ≤ 5`, slack exhaustion):** `u % 4 = 3 ∧ u % 64 ≠ 7` (15 classes),
   - **Survival (`6 ≤ s'`):** `u % 64 = 7` (1 class).
4. **The 82-Module Grand Synthesis (`mahler_grand_82_module_synthesis`)**:
   Bundles the flagship theorems of the entire 82-module library.
-/

namespace Mahler.GrandSynthesis

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

/-! ## 1. Two-Way Equivalence Between `ValidBlockChain` and the Coprime Recurrence -/

/-- **Converse Block-Chain Construction from the Coprime Recurrence
(`validBlockChain_of_coprime_recurrence`)**:
If `1 ≤ s k` and `u k % 2 = 1` for all `k < K`, `3 * a_0 + 1 = 2^(s 0) * u 0`
(for `0 < K`), and `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1` for all
`k + 1 < K`, then `ValidBlockChain a_0 s u K` holds. -/
theorem validBlockChain_of_coprime_recurrence {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hs : ∀ k < K, 1 ≤ s k)
    (hu : ∀ k < K, u k % 2 = 1)
    (h0 : 0 < K → 3 * a_0 + 1 = 2 ^ (s 0) * u 0)
    (hrec : ∀ k, k + 1 < K → 2 ^ (s (k + 1)) * u (k + 1) = 3 ^ (s k) * u k + 1) :
    ValidBlockChain a_0 s u K := by
  intro k hk
  refine ⟨hs k hk, hu k hk, ?_⟩
  induction k with
  | zero =>
      simpa [blockSteps, orbit] using h0 hk
  | succ k ih =>
      have ihk := ih (by omega)
      have hsk : 1 ≤ s k := hs k (by omega)
      have hret :
          orbit a_0 (blockSteps s (k + 1)) = 3 ^ (s k - 1) * u k := by
        simp only [blockSteps]
        rw [orbit_add]
        exact orbit_odd_block_return hsk ihk
      have h3pow : 3 * (3 ^ (s k - 1) * u k) = 3 ^ (s k) * u k := by
        have hsub : s k = (s k - 1) + 1 := by omega
        conv_rhs => rw [hsub, Nat.pow_succ]
        ring
      rw [hret, h3pow, ← hrec k hk]

/-- **Two-Way Equivalence (`validBlockChain_iff_coprime_recurrence`)**:
`ValidBlockChain a_0 s u K` holds if and only if the 1-step coprime recurrence
conditions hold for all `k < K`. -/
theorem validBlockChain_iff_coprime_recurrence {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ} :
    ValidBlockChain a_0 s u K ↔
      (∀ k < K, 1 ≤ s k) ∧
      (∀ k < K, u k % 2 = 1) ∧
      (0 < K → 3 * a_0 + 1 = 2 ^ (s 0) * u 0) ∧
      (∀ k, k + 1 < K → 2 ^ (s (k + 1)) * u (k + 1) = 3 ^ (s k) * u k + 1) := by
  constructor
  · intro hchain
    refine ⟨fun k hk => (hchain k hk).1, fun k hk => (hchain k hk).2.1, ?_, ?_⟩
    · intro h0
      simpa [blockSteps, orbit] using (hchain 0 h0).2.2
    · intro k hk1
      exact coprime_quotient_recurrence hk1 hchain
  · rintro ⟨hs, hu, h0, hrec⟩
    exact validBlockChain_of_coprime_recurrence hs hu h0 hrec

/-! ## 2. Exact 113-Step Survival & 114-Step Death of the 55-Bit Record-Holder -/

/-- The 55-bit coasting record-holder `a_0 = 29871555608238677 < 2^55`. -/
def recordHolderA0 : ℕ := 29871555608238677

/-- Block-length sequence `[8, 4, 6, 11, 8, 5, 7, 7, 3, 4, 3, 6, 6, 3, 6, 5, 7, 7, 6, 1]`
for `recordHolderA0`. -/
def recordHolderS : ℕ → ℕ
  | 0 => 8
  | 1 => 4
  | 2 => 6
  | 3 => 11
  | 4 => 8
  | 5 => 5
  | 6 => 7
  | 7 => 7
  | 8 => 3
  | 9 => 4
  | 10 => 3
  | 11 => 6
  | 12 => 6
  | 13 => 3
  | 14 => 6
  | 15 => 5
  | 16 => 7
  | 17 => 7
  | 18 => 6
  | _ => 1

/-- Coprime odd quotient sequence `u` for `recordHolderA0`. -/
def recordHolderU : ℕ → ℕ
  | 0 => 350057292284047
  | 1 => 143545368417227023
  | 2 => 181674606903052951
  | 3 => 64668353726721485
  | 4 => 44749237725107542591
  | 5 => 9174992147325955841861
  | 6 => 17418149154689119293533
  | 7 => 297605407822696124179349
  | 8 => 81357878363529552947529533
  | 9 => 137291419738456120598956087
  | 10 => 1390075624851868221064430381
  | 11 => 586438154234381905761556567
  | 12 => 6679897100576006395315230271
  | 13 => 608705623289988582773100358445
  | 14 => 256797684825463933357401713719
  | 15 => 5850172257430100231798307790661
  | 16 => 11106186394964955908804599946333
  | 17 => 189759606607721551348091094395549
  | 18 => 6484441557048234887473050366297901
  | _ => 2363578947544081616483926858515584915

/-- `recordHolderA0` forms a valid 20-block chain with `recordHolderS` and
`recordHolderU`. -/
theorem recordHolder_validBlockChain :
    ValidBlockChain recordHolderA0 recordHolderS recordHolderU 20 := by
  apply validBlockChain_of_coprime_recurrence
  · intro k hk
    have hcases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
        k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 := by omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro k hk
    have hcases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
        k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 := by omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro _
    decide
  · intro k hk
    have hcases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
        k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Exact 113-Step Survival and 114-Step Death of the 55-Bit Record-Holder
(`recordHolderA0_exact_113_survival_and_114_death`)**:
`recordHolderA0 = 29871555608238677 < 2^55` admits a real Mahler companion
surviving `113` steps (`E = 58` coasting steps beyond its 55-bit length) and
admits no companion surviving `114` steps. -/
theorem recordHolderA0_exact_113_survival_and_114_death :
    recordHolderA0 < 2 ^ 55 ∧
      (∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 113) ∧
      (¬ ∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 114) := by
  refine ⟨by decide, ?_, ?_⟩
  · have hsteps : blockSteps recordHolderS 20 = 113 := by rfl
    rw [← hsteps]
    apply exists_validCompanionUpTo_of_three_le (by decide : 1 ≤ 20)
      recordHolder_validBlockChain
    intro k hk
    have hcases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
        k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have hsteps19 : blockSteps recordHolderS (18 + 1) + 2 = 114 := by rfl
    rw [← hsteps19]
    apply no_companion_of_phase_lock_rupture (k := 18) (by decide : 18 + 1 < 20)
      recordHolder_validBlockChain
    left
    exact ⟨by decide, by decide⟩

/-! ## 3. Exact Modulo-64 Three-Way Branch Partition After `s = 2` -/

/-- **Exact Modulo-64 Three-Way Branch Partition After `s = 2`
(`post_two_mod_64_three_way_partition`)**:
Whenever `2^s' * u' = 9 * u + 1` with `u % 2 = 1`, `u' % 2 = 1`, and `1 ≤ s'`:
- `s' = 1 ↔ u % 4 = 1` (Mode A: 16 of 32 odd classes mod 64),
- `(2 ≤ s' ∧ s' ≤ 5) ↔ (u % 4 = 3 ∧ u % 64 ≠ 7)` (Mode B: 15 of 32 odd classes mod 64),
- `6 ≤ s' ↔ u % 64 = 7` (Survival: 1 of 32 odd classes mod 64). -/
theorem post_two_mod_64_three_way_partition {u s' u' : ℕ}
    (hu : u % 2 = 1) (hs' : 1 ≤ s') (hu' : u' % 2 = 1)
    (heq : 2 ^ s' * u' = 9 * u + 1) :
    (s' = 1 ↔ u % 4 = 1) ∧
      ((2 ≤ s' ∧ s' ≤ 5) ↔ (u % 4 = 3 ∧ u % 64 ≠ 7)) ∧
      (6 ≤ s' ↔ u % 64 = 7) := by
  have hrec2 : 2 ^ s' * u' = 3 ^ 2 * u + 1 := by simpa using heq
  have hge2_iff : 2 ≤ s' ↔ u % 4 = 3 := by
    have hlock := parity_mod_four_phase_lock_iff hu hs' hu' hrec2
    simpa using hlock
  have hge6_iff := six_le_s_iff_u_mod_64_eq_7 hu' heq
  refine ⟨?_, ?_, hge6_iff⟩
  · constructor
    · intro hs'1
      have hnot2 : ¬ (2 ≤ s') := by omega
      have hnot3 : u % 4 ≠ 3 := mt hge2_iff.mpr hnot2
      omega
    · intro hu1
      have hnot3 : u % 4 ≠ 3 := by omega
      have hnot2 : ¬ (2 ≤ s') := mt hge2_iff.mp hnot3
      omega
  · constructor
    · rintro ⟨h2, h5⟩
      have hnot6 : ¬ (6 ≤ s') := by omega
      exact ⟨hge2_iff.mp h2, mt hge6_iff.mpr hnot6⟩
    · rintro ⟨hu3, hu64⟩
      have h2 : 2 ≤ s' := hge2_iff.mpr hu3
      have hnot6 : ¬ (6 ≤ s') := mt hge6_iff.mp hu64
      omega

/-! ## 4. The 82-Module Grand Synthesis -/

/-- **The 82-Module Grand Synthesis (`mahler_grand_82_module_synthesis`)**:
Unites the crown-jewel theorems of the 82-module formalization. -/
theorem mahler_grand_82_module_synthesis :
    -- 1. Terminal `minSlack` Two-Way Equivalence (`∃ ξ ↔ 0 < minSlack s (K - 1)`):
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ},
      1 ≤ K → ValidBlockChain a_0 s u K →
        ((∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s K)) ↔
          0 < minSlack s (K - 1))) ∧
    -- 2. Dual-Metric Series Identity (`(2 * a_0 + 1) - slackSeries = 2^(T+1) * u / 3^(T+1)`):
    (∀ {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ},
      m < K → ValidBlockChain a_0 s u K →
        (2 * (a_0 : ℝ) + 1) - ((1 / 3 : ℝ) - blockDrainSum s m) =
          (2 : ℝ) ^ (blockSteps s (m + 1) + 1) * (u m : ℝ) /
            (3 : ℝ) ^ (blockSteps s m + 1)) ∧
    -- 3. Time-Independent Bounded-Block Escape Squeeze:
    (∀ (s : ℕ → ℕ) {c k m : ℕ} {p q : ℤ},
      1 ≤ c → 0 < q →
      q * minSlack s k ≤ p * (2 : ℤ) ^ (blockSteps s k) →
      (∀ i < m, s (k + i) ≤ c) → 0 < minSlack s (k + m) →
      (q * (2 : ℤ) ^ (c + 1) - ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * p) *
          (3 : ℤ) ^ (blockSteps (shiftSeq s k) m) <
        q * (2 : ℤ) ^ (c + 1) * (2 : ℤ) ^ (blockSteps (shiftSeq s k) m)) ∧
    -- 4. Exact 113-Step Survival & 114-Step Death of the 55-Bit Record-Holder:
    (recordHolderA0 < 2 ^ 55 ∧
      (∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 113) ∧
      (¬ ∃ ξ : ℝ, ValidCompanionUpTo recordHolderA0 ξ 114)) := by
  exact ⟨fun hK hchain => exists_validCompanionUpTo_iff_minSlack_pos hK hchain,
    fun hmK hchain => dual_metric_series_identity hmK hchain,
    time_independent_bounded_block_squeeze,
    recordHolderA0_exact_113_survival_and_114_death⟩

end Mahler.GrandSynthesis
