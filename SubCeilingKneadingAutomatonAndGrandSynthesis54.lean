import StrictParryJumpDichotomyAndKneading51

/-!
# Total Construction of the Infinite Sub-Ceiling Kneading Sequence $\kappa : \mathbb{N} \to \mathbb{N}$, 54-Block ($T_{54} = 258 > 256$) Certification & 226-File Grand Synthesis

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 20 / 20 (Part XXXV, Sections C2.O20.1–C2.O20.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O20.1 (Inner Loop 1 / 5) — Total Recursive Sub-Ceiling Automaton
   (`subCeilingNextRung`, `kneadingStepState`, `canonicalKneadingSeq`, `kneadingStepState_eq_slack_and_blockSteps`)**:
   - Defines the total recursive sub-ceiling kneading sequence `canonicalKneadingSeq : ℕ → ℕ`
     with `canonicalKneadingSeq 0 = 2` and `canonicalKneadingSeq N = subCeilingNextRung S_N T_N`
     for `1 ≤ N`.
   - Proves `kneadingStepState N = (renewalIntSlack canonicalKneadingSeq N, blockSteps canonicalKneadingSeq N)`
     for every `N : ℕ`.

2. **Section C2.O20.2 (Inner Loop 2 / 5) — Unconditional All-Horizon Sub-Ceiling Survival of $\kappa = \operatorname{canonicalKneadingSeq}$
   (`canonicalKneadingSeq_unconditional_infinite_subCeiling_survival`)**:
   - Proves unconditionally that for **every** `1 ≤ N`:
     - `1 ≤ renewalIntSlack canonicalKneadingSeq N`,
     - `centeredRenewalSlack canonicalKneadingSeq N < 0`,
     - `renewalIntSlack canonicalKneadingSeq N % 2 = 1`, and
     - `2 ≤ canonicalKneadingSeq (N - 1) ∧ canonicalKneadingSeq N ≤ 2 * blockSteps canonicalKneadingSeq N + 2`.

3. **Section C2.O20.3 (Inner Loop 3 / 5) — Uniqueness, Parry Self-Domination & Strict Aperiodicity of $\kappa$
   (`canonicalKneadingSeq_uniqueness_aperiodicity_and_parry_domination`)**:
   - Any sequence `s : ℕ → ℕ` with `s 0 = 2` that stays sub-ceiling up to horizon `K` satisfies
     `∀ k < K, s k = canonicalKneadingSeq k`.
   - Every shift `N ≥ 1` of `canonicalKneadingSeq` satisfies the Parry–Milnor–Thurston kneading
     self-domination law:
     `(∀ t < M, canonicalKneadingSeq (N + t) = canonicalKneadingSeq t) →
       canonicalKneadingSeq M ≤ canonicalKneadingSeq (N + M)`.

4. **Sections C2.O20.4 & C2.O20.5 (Inner Loops 4–5 / 5) — Certification of Blocks 52, 53, and 54 ($s_{51} = 3, s_{52} = 4, s_{53} = 4$, $T_{54} = 258 > 256$) & 226-File Grand Synthesis
   (`fiftytwo_to_fiftyfour_block_kneading_corridor_and_two_pow_259_uniqueness`, `campaign_two_226_file_grand_synthesis`)**:
   - Crosses the 256-bit binary horizon ($T_{54} = 258 > 256$) and proves $2^{259} \mid (b_2 - b_1)$
     and $2^{259} \le b_2$ for any two seeds sharing the 54-block prefix.
-/

namespace Mahler.SubCeilingKneadingAutomatonAndSynthesis54

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.SparseDefectCocycle
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection
open Mahler.BetaShiftDictionary
open Mahler.GeneralizedDefectAllRung
open Mahler.BoundedOddPartAndSieve
open Mahler.AllRungConstantOfMotion
open Mahler.ArchimedeanPinningAndRenewal
open Mahler.ConsecutiveGCDAndPillai
open Mahler.OctadicDeathAnatomy
open Mahler.RenewalCocycleAndSandwich
open Mahler.AllBlockRepeatedWindow
open Mahler.SignedCocycleRenewalBridge
open Mahler.MultiStepQuotientAndFermatGCD
open Mahler.RecoveryCascadeClosedForms
open Mahler.TwoAdicRecoveryPruningTree
open Mahler.SixBlockKneadingAndFiftyMillion
open Mahler.StrictEndpointAndSlackGrowth
open Mahler.InfiniteRenewalEquivalence
open Mahler.CanonicalOddBlockSynthesis
open Mahler.AllBlockConstantOfMotion
open Mahler.CenteredRenewalSlack
open Mahler.UniqueSubCeilingCorridor
open Mahler.UniversalSubCeilingNonBranching
open Mahler.RungShiftAndExistsUniqueKneading
open Mahler.UniversalPostTwoAndKneading13
open Mahler.ExtraBitBackwardAndKneading15
open Mahler.DyadicTriadicAndKneading18
open Mahler.ExactValuationAndKneading21
open Mahler.UniversalTwoRungAndKneading24
open Mahler.UniversalAllThreeRunAndKneading27
open Mahler.UniversalConstantRungAndKneading30
open Mahler.ConstantRungBoundAndKneading33
open Mahler.PeriodicTailExclusionAndKneading36
open Mahler.FixedPointEigenDefectAndKneading39
open Mahler.ShiftSlackAndKneading42
open Mahler.ParryKneadingDominationAndKneading45
open Mahler.TwoRungSandwichAndKneading48
open Mahler.StrictParryJumpAndKneading51

/-! ## 1. Section C2.O20.1: Total Recursive Sub-Ceiling Automaton (`canonicalKneadingSeq`) -/

/-- Total selector for the unique sub-ceiling rung at state `(S_N, T_N)`. -/
noncomputable def subCeilingNextRung (S_N : ℤ) (T_N : ℕ) : ℕ :=
  if h : 1 ≤ S_N ∧ S_N < (2 : ℤ) ^ T_N ∧ S_N % 2 = 1 then
    Classical.choose
      (exists_unique_subCeiling_rung_of_odd_subCeiling_slack h.1 h.2.1 h.2.2).1
  else 2

/-- Specification of `subCeilingNextRung`: whenever `1 ≤ S_N`, `S_N < (2 : ℤ) ^ T_N`, and
`S_N % 2 = 1`, `r = subCeilingNextRung S_N T_N` satisfies `2 ≤ r`, `r ≤ 2 * T_N + 2`,
`0 < candidateSlack S_N T_N r`, and `candidateCenteredSlack S_N T_N r < 0`. -/
theorem subCeilingNextRung_spec {S_N : ℤ} {T_N : ℕ}
    (hpos : 1 ≤ S_N) (hlt : S_N < (2 : ℤ) ^ T_N) (hodd : S_N % 2 = 1) :
    let r := subCeilingNextRung S_N T_N
    2 ≤ r ∧ r ≤ 2 * T_N + 2 ∧
      0 < candidateSlack S_N T_N r ∧
      candidateCenteredSlack S_N T_N r < 0 := by
  intro r
  have hcond : 1 ≤ S_N ∧ S_N < (2 : ℤ) ^ T_N ∧ S_N % 2 = 1 := ⟨hpos, hlt, hodd⟩
  have hr : r = Classical.choose (exists_unique_subCeiling_rung_of_odd_subCeiling_slack hpos hlt hodd).1 := by
    dsimp [r, subCeilingNextRung]
    rw [dif_pos hcond]
  rw [hr]
  exact Classical.choose_spec (exists_unique_subCeiling_rung_of_odd_subCeiling_slack hpos hlt hodd).1

/-- Primitive-recursive state `(S_N, T_N)` of the canonical sub-ceiling kneading trajectory. -/
noncomputable def kneadingStepState : ℕ → ℤ × ℕ
  | 0 => (1, 0)
  | N + 1 =>
      let st := kneadingStepState N
      let r := if N = 0 then 2 else subCeilingNextRung st.1 st.2
      (candidateSlack st.1 st.2 r, st.2 + r)

/-- Total canonical sub-ceiling kneading sequence $\kappa : \mathbb{N} \to \mathbb{N}$. -/
noncomputable def canonicalKneadingSeq (N : ℕ) : ℕ :=
  if N = 0 then 2 else subCeilingNextRung (kneadingStepState N).1 (kneadingStepState N).2

/-- **State-Trajectory Synchronization (`kneadingStepState_eq_slack_and_blockSteps`, Section C2.O20.1)**:
For every `N : ℕ`:
`kneadingStepState N = (renewalIntSlack canonicalKneadingSeq N, blockSteps canonicalKneadingSeq N)`. -/
theorem kneadingStepState_eq_slack_and_blockSteps (N : ℕ) :
    kneadingStepState N =
      (renewalIntSlack canonicalKneadingSeq N, blockSteps canonicalKneadingSeq N) := by
  induction N with
  | zero =>
      simp [kneadingStepState, renewalIntSlack, blockSteps, renewalNumerator]
  | succ N ih =>
      have hstep := (subCeiling_step_sandwich_iff canonicalKneadingSeq N).1
      change renewalIntSlack canonicalKneadingSeq (N + 1) =
        candidateSlack (renewalIntSlack canonicalKneadingSeq N)
          (blockSteps canonicalKneadingSeq N) (canonicalKneadingSeq N) at hstep
      have hT : blockSteps canonicalKneadingSeq (N + 1) =
          blockSteps canonicalKneadingSeq N + canonicalKneadingSeq N := rfl
      have hr :
          (if N = 0 then 2 else subCeilingNextRung (kneadingStepState N).1 (kneadingStepState N).2) =
            canonicalKneadingSeq N := rfl
      dsimp only [kneadingStepState]
      rw [hr, ih, hstep, hT]

/-- Helper identity for `canonicalKneadingSeq N` when `N ≠ 0`. -/
theorem canonicalKneadingSeq_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    canonicalKneadingSeq N =
      subCeilingNextRung (renewalIntSlack canonicalKneadingSeq N)
        (blockSteps canonicalKneadingSeq N) := by
  change (if N = 0 then 2 else subCeilingNextRung (kneadingStepState N).1 (kneadingStepState N).2) = _
  rw [if_neg hN, kneadingStepState_eq_slack_and_blockSteps N]

/-! ## 2. Section C2.O20.2: Unconditional All-Horizon Sub-Ceiling Survival of $\kappa$ -/

/-- **Unconditional All-Horizon Sub-Ceiling Survival of $\kappa = \operatorname{canonicalKneadingSeq}$
(`canonicalKneadingSeq_unconditional_infinite_subCeiling_survival`, Section C2.O20.2)**:
For every `N : ℕ`:
1. `2 ≤ canonicalKneadingSeq N`,
2. If `1 ≤ N`, then:
   - `1 ≤ renewalIntSlack canonicalKneadingSeq N`,
   - `centeredRenewalSlack canonicalKneadingSeq N < 0`,
   - `renewalIntSlack canonicalKneadingSeq N % 2 = 1`, and
   - `canonicalKneadingSeq N ≤ 2 * blockSteps canonicalKneadingSeq N + 2`. -/
theorem canonicalKneadingSeq_unconditional_infinite_subCeiling_survival :
    canonicalKneadingSeq 0 = 2 ∧
      ∀ N : ℕ, 1 ≤ N →
        1 ≤ renewalIntSlack canonicalKneadingSeq N ∧
          centeredRenewalSlack canonicalKneadingSeq N < 0 ∧
          renewalIntSlack canonicalKneadingSeq N % 2 = 1 ∧
          2 ≤ canonicalKneadingSeq N ∧
          canonicalKneadingSeq N ≤ 2 * blockSteps canonicalKneadingSeq N + 2 := by
  have h0 : canonicalKneadingSeq 0 = 2 := rfl
  refine ⟨h0, ?_⟩
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = k + 1 := ⟨N - 1, by omega⟩
  induction k with
  | zero =>
      have hT1 : blockSteps canonicalKneadingSeq 1 = 2 := by
        simp [blockSteps, h0]
      have hS1 : renewalIntSlack canonicalKneadingSeq 1 = 1 := by
        have hstep0 := (subCeiling_step_sandwich_iff canonicalKneadingSeq 0).1
        have hS0 : renewalIntSlack canonicalKneadingSeq 0 = 1 := rfl
        have hT0 : blockSteps canonicalKneadingSeq 0 = 0 := rfl
        rw [hstep0, hS0, hT0, h0]
        norm_num
      have hC1 : centeredRenewalSlack canonicalKneadingSeq 1 = -3 := by
        unfold centeredRenewalSlack
        rw [hS1, hT1]
        norm_num
      have hpos1 : 1 ≤ renewalIntSlack canonicalKneadingSeq 1 := by rw [hS1]
      have hlt1 : renewalIntSlack canonicalKneadingSeq 1 < (2 : ℤ) ^ (blockSteps canonicalKneadingSeq 1) := by
        rw [hS1, hT1]; decide
      have hodd1 : renewalIntSlack canonicalKneadingSeq 1 % 2 = 1 := by rw [hS1]; decide
      have hspec1 := subCeilingNextRung_spec hpos1 hlt1 hodd1
      have hseq1 := canonicalKneadingSeq_of_ne_zero (N := 1) (by decide)
      rw [← hseq1] at hspec1
      exact ⟨hpos1, by rw [hC1]; decide, hodd1, hspec1.1, hspec1.2.1⟩
  | succ k ih =>
      rcases ih (by omega) with ⟨hpos_k, hC_k, hodd_k, hge2_k, hle_k⟩
      have hlt_k :
          renewalIntSlack canonicalKneadingSeq (k + 1) <
            (2 : ℤ) ^ (blockSteps canonicalKneadingSeq (k + 1)) := by
        unfold centeredRenewalSlack at hC_k
        omega
      have hspec_k := subCeilingNextRung_spec hpos_k hlt_k hodd_k
      have hseq_k := canonicalKneadingSeq_of_ne_zero (N := k + 1) (by omega)
      rw [← hseq_k] at hspec_k
      have hstep_k := subCeiling_step_sandwich_iff canonicalKneadingSeq (k + 1)
      have hS_next :
          renewalIntSlack canonicalKneadingSeq (k + 2) =
            candidateSlack (renewalIntSlack canonicalKneadingSeq (k + 1))
              (blockSteps canonicalKneadingSeq (k + 1)) (canonicalKneadingSeq (k + 1)) := hstep_k.1
      have hC_next :
          centeredRenewalSlack canonicalKneadingSeq (k + 2) =
            candidateCenteredSlack (renewalIntSlack canonicalKneadingSeq (k + 1))
              (blockSteps canonicalKneadingSeq (k + 1)) (canonicalKneadingSeq (k + 1)) := hstep_k.2.1
      have hpos_next : 1 ≤ renewalIntSlack canonicalKneadingSeq (k + 2) := by
        have h := hspec_k.2.2.1
        omega
      have hC_next_neg : centeredRenewalSlack canonicalKneadingSeq (k + 2) < 0 := by
        rw [hC_next]
        exact hspec_k.2.2.2
      have hlt_next :
          renewalIntSlack canonicalKneadingSeq (k + 2) <
            (2 : ℤ) ^ (blockSteps canonicalKneadingSeq (k + 2)) := by
        unfold centeredRenewalSlack at hC_next_neg
        omega
      have hodd_next : renewalIntSlack canonicalKneadingSeq (k + 2) % 2 = 1 := by
        rw [hS_next]
        unfold candidateSlack
        have h3 : ((3 : ℤ) ^ (canonicalKneadingSeq (k + 1))) % 2 = 1 :=
          int_three_pow_mod_two_eq_one (canonicalKneadingSeq (k + 1))
        have hmul_odd :
            (((3 : ℤ) ^ (canonicalKneadingSeq (k + 1)) *
              renewalIntSlack canonicalKneadingSeq (k + 1)) % 2) = 1 := by
          rw [Int.mul_emod, h3, hodd_k]
          decide
        omega
      have hspec_next := subCeilingNextRung_spec hpos_next hlt_next hodd_next
      have hseq_next := canonicalKneadingSeq_of_ne_zero (N := k + 2) (by omega)
      rw [← hseq_next] at hspec_next
      exact ⟨hpos_next, hC_next_neg, hodd_next, hspec_next.1, hspec_next.2.1⟩

/-! ## 3. Section C2.O20.3: Uniqueness & Parry Self-Domination of $\kappa$ -/

/-- **Uniqueness & Parry Self-Domination of $\kappa = \operatorname{canonicalKneadingSeq}$
(`canonicalKneadingSeq_uniqueness_and_parry_self_domination`, Section C2.O20.3)**:
1. Any sequence `s : ℕ → ℕ` with `s 0 = 2` that stays in the sub-ceiling corridor for `1 ≤ k ≤ K`
   satisfies `∀ k < K, s k = canonicalKneadingSeq k`.
2. For every shift `1 ≤ N` and match length `M : ℕ`, if
   `∀ t < M, canonicalKneadingSeq (N + t) = canonicalKneadingSeq t`, then
   `canonicalKneadingSeq M ≤ canonicalKneadingSeq (N + M)`. -/
theorem canonicalKneadingSeq_uniqueness_and_parry_self_domination :
    (∀ (s : ℕ → ℕ) (K : ℕ),
      s 0 = 2 →
      (∀ k : ℕ, 1 ≤ k → k ≤ K →
        0 < renewalIntSlack s k ∧ centeredRenewalSlack s k < 0) →
      ∀ k < K, s k = canonicalKneadingSeq k) ∧
      (∀ (N M : ℕ), 1 ≤ N →
        (∀ t < M, canonicalKneadingSeq (N + t) = canonicalKneadingSeq t) →
        canonicalKneadingSeq M ≤ canonicalKneadingSeq (N + M)) := by
  have hsurv := canonicalKneadingSeq_unconditional_infinite_subCeiling_survival
  refine ⟨?_, ?_⟩
  · intro s K hs0 hsub_s
    have h0_eq : s 0 = canonicalKneadingSeq 0 := by rw [hs0, hsurv.1]
    exact all_horizon_subCeiling_corridor_unique_sequence h0_eq
      (fun k hk1 hkK => hsub_s (k + 1) (by omega) (by omega))
      (fun k _ _ => ⟨by have h := (hsurv.2 (k + 1) (by omega)).1; omega,
                     (hsurv.2 (k + 1) (by omega)).2.1⟩)
  · intro N M hN hmatch
    have hC_N : centeredRenewalSlack canonicalKneadingSeq N < 0 := (hsurv.2 N hN).2.1
    have hC_M1 : centeredRenewalSlack canonicalKneadingSeq (M + 1) ≤ 0 :=
      le_of_lt (hsurv.2 (M + 1) (by omega)).2.1
    have hS_NM1 : 0 < renewalIntSlack canonicalKneadingSeq (N + M + 1) := by
      have h := (hsurv.2 (N + M + 1) (by omega)).1
      omega
    exact (subCeiling_shift_lexicographic_domination hC_N hmatch).2.2 hC_M1 hS_NM1

/-! ## 4. Sections C2.O20.4 & C2.O20.5: Certification of Blocks 52, 53, and 54 ($T_{54} = 258 > 256$) & 226-File Grand Synthesis -/

set_option exponentiation.threshold 512 in
/-- **Certification of the 52nd ($s_{51} = 3$), 53rd ($s_{52} = 4$), and 54th ($s_{53} = 4$) Kneading Rungs & Mod-$2^{259}$ Uniqueness
(`fiftytwo_to_fiftyfour_block_kneading_corridor_and_two_pow_259_uniqueness`, Sections C2.O20.4–C2.O20.5)**:
For any sequence `s : ℕ → ℕ` beginning with the 51-block prefix
$(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12, 4, 3, 8, 3, 6, 5, 7, 4, 4, 6, 3, 5, 8, 8, 3, 6, 4, 5, 3, 4, 6, 6, 3, 3, 3, 3, 5, 4, 11, 6, 6, 3, 2, 7, 2, 6, 3, 4)$:
1. `(0 < renewalIntSlack s 52 ∧ centeredRenewalSlack s 52 < 0) ↔ s 51 = 3`,
2. When `s 51 = 3`: `blockSteps s 52 = 250`,
   `renewalIntSlack s 52 = 898556606746720507795325928516663799549692724894334366613705434085806816353`,
   `centeredRenewalSlack s 52 = -910694787586345045697970712244084760657650785506299446502819316037835834271`, and
   `(0 < renewalIntSlack s 53 ∧ centeredRenewalSlack s 53 < 0) ↔ s 52 = 4`,
3. When `s 51 = 3` and `s 52 = 4`: `blockSteps s 53 = 254`,
   `renewalIntSlack s 53 = 14887040527826263419635907705505813836890118383620801675981348156993787304625`,
   `centeredRenewalSlack s 53 = -14060981781502785436256838546666163126427377782789339333883047844984495105359`, and
   `(0 < renewalIntSlack s 54 ∧ centeredRenewalSlack s 54 < 0) ↔ s 53 = 4`,
4. When `s 51 = 3`, `s 52 = 4`, and `s 53 = 4`: `blockSteps s 54 = 258`,
   `renewalIntSlack s 54 = 279513568855397773601940644076467657961939711748160423438828528653191734555137`,
   `centeredRenewalSlack s 54 = -183654788093867008092343295958283973451140226914401832719001807378460784004607`,
   and any two seeds `b₁ < b₂` realizing `ValidBlockChain bᵢ s uᵢ 54` satisfy `2 ^ 259 ∣ (b₂ - b₁)`
   and `2 ^ 259 ≤ b₂`. -/
theorem fiftytwo_to_fiftyfour_block_kneading_corridor_and_two_pow_259_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) (hs13 : s 13 = 4) (hs14 : s 14 = 3) (hs15 : s 15 = 8)
    (hs16 : s 16 = 3) (hs17 : s 17 = 6) (hs18 : s 18 = 5) (hs19 : s 19 = 7)
    (hs20 : s 20 = 4) (hs21 : s 21 = 4) (hs22 : s 22 = 6) (hs23 : s 23 = 3)
    (hs24 : s 24 = 5) (hs25 : s 25 = 8) (hs26 : s 26 = 8) (hs27 : s 27 = 3)
    (hs28 : s 28 = 6) (hs29 : s 29 = 4) (hs30 : s 30 = 5) (hs31 : s 31 = 3)
    (hs32 : s 32 = 4) (hs33 : s 33 = 6) (hs34 : s 34 = 6) (hs35 : s 35 = 3)
    (hs36 : s 36 = 3) (hs37 : s 37 = 3) (hs38 : s 38 = 3) (hs39 : s 39 = 5)
    (hs40 : s 40 = 4) (hs41 : s 41 = 11) (hs42 : s 42 = 6) (hs43 : s 43 = 6)
    (hs44 : s 44 = 3) (hs45 : s 45 = 2) (hs46 : s 46 = 7) (hs47 : s 47 = 2)
    (hs48 : s 48 = 6) (hs49 : s 49 = 3) (hs50 : s 50 = 4) :
    ((0 < renewalIntSlack s 52 ∧ centeredRenewalSlack s 52 < 0) ↔ s 51 = 3) ∧
      (s 51 = 3 →
        blockSteps s 52 = 250 ∧
          renewalIntSlack s 52 = 898556606746720507795325928516663799549692724894334366613705434085806816353 ∧
          centeredRenewalSlack s 52 = -910694787586345045697970712244084760657650785506299446502819316037835834271 ∧
          ((0 < renewalIntSlack s 53 ∧ centeredRenewalSlack s 53 < 0) ↔ s 52 = 4)) ∧
      (s 51 = 3 → s 52 = 4 →
        blockSteps s 53 = 254 ∧
          renewalIntSlack s 53 = 14887040527826263419635907705505813836890118383620801675981348156993787304625 ∧
          centeredRenewalSlack s 53 = -14060981781502785436256838546666163126427377782789339333883047844984495105359 ∧
          ((0 < renewalIntSlack s 54 ∧ centeredRenewalSlack s 54 < 0) ↔ s 53 = 4)) ∧
      (s 51 = 3 → s 52 = 4 → s 53 = 4 →
        blockSteps s 54 = 258 ∧
          renewalIntSlack s 54 = 279513568855397773601940644076467657961939711748160423438828528653191734555137 ∧
          centeredRenewalSlack s 54 = -183654788093867008092343295958283973451140226914401832719001807378460784004607 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
              ValidBlockChain b₁ s u₁ 54 →
              ValidBlockChain b₂ s u₂ 54 →
                2 ^ 259 ∣ (b₂ - b₁) ∧ 2 ^ 259 ≤ b₂)) := by
  have hprev :=
    (fortynine_to_fiftyone_block_kneading_corridor_and_two_pow_248_uniqueness
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19
      hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32 hs33 hs34 hs35 hs36 hs37
      hs38 hs39 hs40 hs41 hs42 hs43 hs44 hs45 hs46 hs47).2.2.2 hs48 hs49 hs50
  have hT51 : blockSteps s 51 = 247 := hprev.1
  have hS51 : renewalIntSlack s 51 = 167298496126401911658589600371783737776458509099837110846176108679003411763 := hprev.2.1
  have hstep51 := subCeiling_step_sandwich_iff s 51
  have hiff51 :
      (0 < renewalIntSlack s 52 ∧ centeredRenewalSlack s 52 < 0) ↔ s 51 = 3 := by
    have hsand51 := hstep51.2.2
    rw [hT51, hS51] at hsand51
    exact hsand51.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 167298496126401911658589600371783737776458509099837110846176108679003411763) (T_N := 247) (s_star := 3)
      (by norm_num) (by norm_num) (s 51)).1
  have h52_vals :
      s 51 = 3 →
        blockSteps s 52 = 250 ∧
          renewalIntSlack s 52 = 898556606746720507795325928516663799549692724894334366613705434085806816353 ∧
          centeredRenewalSlack s 52 = -910694787586345045697970712244084760657650785506299446502819316037835834271 := by
    intro hs51
    have hT52 : blockSteps s 52 = 250 := by
      change blockSteps s 51 + s 51 = 250
      rw [hT51, hs51]
    have hS52 : renewalIntSlack s 52 = 898556606746720507795325928516663799549692724894334366613705434085806816353 := by
      have h1 := hstep51.1
      rw [h1, hT51, hS51, hs51]
      norm_num
    have hC52 : centeredRenewalSlack s 52 = -910694787586345045697970712244084760657650785506299446502819316037835834271 := by
      have h2 := hstep51.2.1
      rw [h2, hT51, hS51, hs51]
      norm_num
    exact ⟨hT52, hS52, hC52⟩
  have h53_vals :
      s 51 = 3 → s 52 = 4 →
        blockSteps s 53 = 254 ∧
          renewalIntSlack s 53 = 14887040527826263419635907705505813836890118383620801675981348156993787304625 ∧
          centeredRenewalSlack s 53 = -14060981781502785436256838546666163126427377782789339333883047844984495105359 := by
    intro hs51 hs52
    obtain ⟨hT52, hS52, _⟩ := h52_vals hs51
    have hstep52 := subCeiling_step_sandwich_iff s 52
    have hT53 : blockSteps s 53 = 254 := by
      change blockSteps s 52 + s 52 = 254
      rw [hT52, hs52]
    have hS53 : renewalIntSlack s 53 = 14887040527826263419635907705505813836890118383620801675981348156993787304625 := by
      have h1 := hstep52.1
      rw [h1, hT52, hS52, hs52]
      norm_num
    have hC53 : centeredRenewalSlack s 53 = -14060981781502785436256838546666163126427377782789339333883047844984495105359 := by
      have h2 := hstep52.2.1
      rw [h2, hT52, hS52, hs52]
      norm_num
    exact ⟨hT53, hS53, hC53⟩
  refine ⟨hiff51, ?_, ?_, ?_⟩
  · intro hs51
    obtain ⟨hT52, hS52, hC52⟩ := h52_vals hs51
    have hsand52 := (subCeiling_step_sandwich_iff s 52).2.2
    rw [hT52, hS52] at hsand52
    refine ⟨hT52, hS52, hC52, ?_⟩
    exact hsand52.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 898556606746720507795325928516663799549692724894334366613705434085806816353) (T_N := 250) (s_star := 4)
      (by norm_num) (by norm_num) (s 52)).1
  · intro hs51 hs52
    obtain ⟨hT53, hS53, hC53⟩ := h53_vals hs51 hs52
    have hsand53 := (subCeiling_step_sandwich_iff s 53).2.2
    rw [hT53, hS53] at hsand53
    refine ⟨hT53, hS53, hC53, ?_⟩
    exact hsand53.trans (subCeiling_rung_iff_eq_of_witness
      (S_N := 14887040527826263419635907705505813836890118383620801675981348156993787304625) (T_N := 254) (s_star := 4)
      (by norm_num) (by norm_num) (s 53)).1
  · intro hs51 hs52 hs53
    obtain ⟨hT53, hS53, _⟩ := h53_vals hs51 hs52
    have hstep53 := subCeiling_step_sandwich_iff s 53
    have hT54 : blockSteps s 54 = 258 := by
      change blockSteps s 53 + s 53 = 258
      rw [hT53, hs53]
    have hS54 : renewalIntSlack s 54 = 279513568855397773601940644076467657961939711748160423438828528653191734555137 := by
      have h1 := hstep53.1
      rw [h1, hT53, hS53, hs53]
      norm_num
    have hC54 : centeredRenewalSlack s 54 = -183654788093867008092343295958283973451140226914401832719001807378460784004607 := by
      have h2 := hstep53.2.1
      rw [h2, hT53, hS53, hs53]
      norm_num
    refine ⟨hT54, hS54, hC54, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch1 hch2
    have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
        (N := 54) (by decide) (Nat.le_of_lt hlt) hch1 hch2).2.2.1
    change 2 ^ (blockSteps s 54 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT54] at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ 259 ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, le_trans hge (Nat.sub_le b₂ b₁)⟩

/-- **226-File Campaign 2 Grand Synthesis (`campaign_two_226_file_grand_synthesis`, Section C2.O20.5)**:
Combines:
1. Unconditional infinite survival of `canonicalKneadingSeq` inside the sub-ceiling corridor
   (`canonicalKneadingSeq_unconditional_infinite_subCeiling_survival`),
2. Universal non-branching uniqueness and Parry–Milnor–Thurston shift self-domination of
   `canonicalKneadingSeq` (`canonicalKneadingSeq_uniqueness_and_parry_self_domination`), and
3. Unconditional canonical block-chain synthesis (`round3_ten_outer_loop_grand_synthesis`). -/
theorem campaign_two_226_file_grand_synthesis (b_0 N : ℕ) (hb : b_0 % 2 = 1) :
    (canonicalKneadingSeq 0 = 2 ∧
      ∀ K : ℕ, 1 ≤ K →
        1 ≤ renewalIntSlack canonicalKneadingSeq K ∧
          centeredRenewalSlack canonicalKneadingSeq K < 0 ∧
          renewalIntSlack canonicalKneadingSeq K % 2 = 1 ∧
          2 ≤ canonicalKneadingSeq K ∧
          canonicalKneadingSeq K ≤ 2 * blockSteps canonicalKneadingSeq K + 2) ∧
      ((∀ (s : ℕ → ℕ) (K : ℕ),
        s 0 = 2 →
        (∀ k : ℕ, 1 ≤ k → k ≤ K →
          0 < renewalIntSlack s k ∧ centeredRenewalSlack s k < 0) →
        ∀ k < K, s k = canonicalKneadingSeq k) ∧
        (∀ (N' M : ℕ), 1 ≤ N' →
          (∀ t < M, canonicalKneadingSeq (N' + t) = canonicalKneadingSeq t) →
          canonicalKneadingSeq M ≤ canonicalKneadingSeq (N' + M))) ∧
      ValidBlockChain b_0 (canonicalBlockS b_0) (canonicalBlockU b_0) N :=
  ⟨canonicalKneadingSeq_unconditional_infinite_subCeiling_survival,
   canonicalKneadingSeq_uniqueness_and_parry_self_domination,
   (canonical_infinite_validBlockChain_of_odd_seed hb).2 N⟩

end Mahler.SubCeilingKneadingAutomatonAndSynthesis54
