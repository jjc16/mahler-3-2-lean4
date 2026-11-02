import RungShiftIdentityAndExistsUniqueKneadingRung

/-!
# Universal $8/9$ Short-Block Threshold, Universal Post-`2` $s_{N+1} \ge 6$ Recovery Law & 13-Block ($T_{13} = 65$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 6 / 20 (Part XXI, Sections C2.O6.1–C2.O6.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O6.1 (Inner Loop 1 / 5) — Exact $8/9$ Short-Block Feasibility Threshold at Any Step $N$
   (`short_block_two_slack_and_eight_ninths_threshold`)**:
   - Whenever $s_N = 2$ at an arbitrary step $N$,
     `renewalIntSlack s (N + 1) = 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N = (2 : ℤ) ^ T_N + 9 * centeredRenewalSlack s N`.
   - Consequently, `0 < renewalIntSlack s (N + 1) ↔ 8 * (2 : ℤ) ^ T_N < 9 * renewalIntSlack s N`.

2. **Section C2.O6.2 (Inner Loop 2 / 5) — Universal Two-Step Post-`2` Slack Identity at Any Step $N$
   (`universal_post_two_two_step_slack_identity`)**:
   - Whenever $s_N = 2$ and $s_{N+1} = r$,
     `renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * (9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N) - 8 * (2 : ℤ) ^ (T_N + r)`.

3. **Section C2.O6.3 & C2.O6.4 (Inner Loops 3–4 / 5) — Universal Post-`2` Recovery Lower Bound $s_{N+1} \ge 6$
   (`universal_subCeiling_post_two_requires_six_le`)**:
   - Whenever `centeredRenewalSlack s N ≤ 0` ($\Sigma_N \le 2^{T_N}$) and `s N = 2`:
     `renewalIntSlack s (N + 2) ≤ ((3 : ℤ) ^ (s (N + 1)) - 8 * (2 : ℤ) ^ (s (N + 1))) * (2 : ℤ) ^ T_N`,
     so `0 < renewalIntSlack s (N + 2) → 6 ≤ s (N + 1)` holds at **every** sub-ceiling step $N \in \mathbb{N}$!
   - Moreover, if `217 * (2 : ℤ) ^ T_N + 6561 * centeredRenewalSlack s N ≤ 0`, then $s_{N+1} = 6$ also
     fails (`renewalIntSlack s (N + 2) ≤ 0`).

4. **Section C2.O6.5 (Inner Loop 5 / 5) — Certification of Blocks 11, 12, and 13 ($s_{10} = 3, s_{11} = 2, s_{12} = 12$, $T_{13} = 65$)
   (`eleven_twelve_thirteen_block_kneading_corridor_certification`)**:
   - Certifies in one line of `norm_num` per step that after $(2, 6, 3, 3, 2, 10, 7, 5, 7, 3)$, the
     unique 11th, 12th, and 13th sub-ceiling kneading rungs are $s_{10} = 3$ ($T_{11} = 51$),
     $s_{11} = 2$ ($T_{12} = 53$), and $s_{12} = 12$ ($T_{13} = 65 > 64$).
-/

namespace Mahler.UniversalPostTwoAndKneading13

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

/-! ## 1. Sections C2.O6.1–C2.O6.4: Universal $8/9$ Threshold & Post-`2` Recovery Bound $s_{N+1} \ge 6$ -/

/-- **Exact $8/9$ Short-Block Feasibility Threshold at Any Step $N$
(`short_block_two_slack_and_eight_ninths_threshold`, Section C2.O6.1)**:
Whenever `s N = 2`, setting `T_N = blockSteps s N`:
1. `renewalIntSlack s (N + 1) = 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N`,
2. `renewalIntSlack s (N + 1) = (2 : ℤ) ^ T_N + 9 * centeredRenewalSlack s N`, and
3. `0 < renewalIntSlack s (N + 1) ↔ 8 * (2 : ℤ) ^ T_N < 9 * renewalIntSlack s N`. -/
theorem short_block_two_slack_and_eight_ninths_threshold
    {s : ℕ → ℕ} {N : ℕ} (hsN : s N = 2) :
    let T_N := blockSteps s N
    renewalIntSlack s (N + 1) = 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N ∧
      renewalIntSlack s (N + 1) = (2 : ℤ) ^ T_N + 9 * centeredRenewalSlack s N ∧
      (0 < renewalIntSlack s (N + 1) ↔ 8 * (2 : ℤ) ^ T_N < 9 * renewalIntSlack s N) := by
  intro T_N
  have hstep := (subCeiling_step_sandwich_iff s N).1
  rw [hsN, pow_add (2 : ℤ) T_N 2] at hstep
  have h1 : renewalIntSlack s (N + 1) = 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N := by
    linarith [hstep]
  have h2 : renewalIntSlack s (N + 1) = (2 : ℤ) ^ T_N + 9 * centeredRenewalSlack s N := by
    unfold centeredRenewalSlack
    change renewalIntSlack s (N + 1) = (2 : ℤ) ^ T_N + 9 * (renewalIntSlack s N - (2 : ℤ) ^ T_N)
    linarith [h1]
  refine ⟨h1, h2, ?_⟩
  rw [h1]
  constructor <;> intro h <;> linarith

/-- **Universal Two-Step Post-`2` Slack Identity (`universal_post_two_two_step_slack_identity`,
Section C2.O6.2)**:
Whenever `s N = 2`, setting `T_N = blockSteps s N` and `r = s (N + 1)`:
`renewalIntSlack s (N + 2) = (3 : ℤ) ^ r * (9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N) - 8 * (2 : ℤ) ^ (T_N + r)`. -/
theorem universal_post_two_two_step_slack_identity
    {s : ℕ → ℕ} {N : ℕ} (hsN : s N = 2) :
    let T_N := blockSteps s N
    let r := s (N + 1)
    renewalIntSlack s (N + 2) =
      (3 : ℤ) ^ r * (9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N) - 8 * (2 : ℤ) ^ (T_N + r) := by
  intro T_N r
  have h1 := (short_block_two_slack_and_eight_ninths_threshold hsN).1
  change renewalIntSlack s (N + 1) = 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N at h1
  have h2 := (subCeiling_step_sandwich_iff s (N + 1)).1
  have hTN1 : blockSteps s (N + 1) = T_N + 2 := by
    change blockSteps s N + s N = T_N + 2
    rw [hsN]
  rw [hTN1, h1, show T_N + 2 + r = (T_N + r) + 2 by omega, pow_add (2 : ℤ) (T_N + r) 2] at h2
  linarith [h2]

/-- **Universal Sub-Ceiling Post-`2` Recovery Lower Bound $s_{N+1} \ge 6$
(`universal_subCeiling_post_two_requires_six_le`, Sections C2.O6.3 & C2.O6.4)**:
Whenever `s N = 2` and `centeredRenewalSlack s N ≤ 0` ($\Sigma_N \le 2^{T_N}$):
1. `renewalIntSlack s (N + 2) ≤ ((3 : ℤ) ^ (s (N + 1)) - 8 * (2 : ℤ) ^ (s (N + 1))) * (2 : ℤ) ^ (blockSteps s N)`,
2. `0 < renewalIntSlack s (N + 2) → 6 ≤ s (N + 1)`, and
3. If `s (N + 1) = 6` and `217 * (2 : ℤ) ^ (blockSteps s N) + 6561 * centeredRenewalSlack s N ≤ 0`,
   then `renewalIntSlack s (N + 2) ≤ 0`. -/
theorem universal_subCeiling_post_two_requires_six_le
    {s : ℕ → ℕ} {N : ℕ} (hsN : s N = 2) (hsub : centeredRenewalSlack s N ≤ 0) :
    let T_N := blockSteps s N
    let r := s (N + 1)
    renewalIntSlack s (N + 2) ≤ ((3 : ℤ) ^ r - 8 * (2 : ℤ) ^ r) * (2 : ℤ) ^ T_N ∧
      (0 < renewalIntSlack s (N + 2) → 6 ≤ r) ∧
      (r = 6 → 217 * (2 : ℤ) ^ T_N + 6561 * centeredRenewalSlack s N ≤ 0 →
        renewalIntSlack s (N + 2) ≤ 0) := by
  intro T_N r
  have hid := universal_post_two_two_step_slack_identity hsN
  change renewalIntSlack s (N + 2) =
    (3 : ℤ) ^ r * (9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N) - 8 * (2 : ℤ) ^ (T_N + r) at hid
  have hCS_eq : 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N =
      (2 : ℤ) ^ T_N + 9 * centeredRenewalSlack s N := by
    unfold centeredRenewalSlack
    change 9 * renewalIntSlack s N - 8 * (2 : ℤ) ^ T_N =
      (2 : ℤ) ^ T_N + 9 * (renewalIntSlack s N - (2 : ℤ) ^ T_N)
    ring
  have h3r_nonneg : (0 : ℤ) ≤ (3 : ℤ) ^ r := pow_nonneg (by decide) r
  have hmul_nonpos : (3 : ℤ) ^ r * (9 * centeredRenewalSlack s N) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h3r_nonneg (by linarith)
  have hid_CS :
      renewalIntSlack s (N + 2) =
        ((3 : ℤ) ^ r - 8 * (2 : ℤ) ^ r) * (2 : ℤ) ^ T_N +
          (3 : ℤ) ^ r * (9 * centeredRenewalSlack s N) := by
    rw [hid, hCS_eq, pow_add (2 : ℤ) T_N r]
    ring
  have hbound : renewalIntSlack s (N + 2) ≤ ((3 : ℤ) ^ r - 8 * (2 : ℤ) ^ r) * (2 : ℤ) ^ T_N := by
    linarith [hid_CS, hmul_nonpos]
  have hpow5_le : ∀ n : ℕ, n ≤ 5 → ((3 : ℤ) ^ n - 8 * (2 : ℤ) ^ n) ≤ 0 := by
    intro n hn
    rcases n with _ | _ | _ | _ | _ | _ | n <;> try decide
    omega
  refine ⟨hbound, ?_, ?_⟩
  · intro hpos
    by_contra hnot
    have hle5 : r ≤ 5 := by omega
    have h1 := hpow5_le r hle5
    have h2_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ T_N := pow_nonneg (by decide) T_N
    have hm := mul_nonpos_of_nonpos_of_nonneg h1 h2_nonneg
    linarith
  · intro hr6 hcond
    have hr6_eq : r = 6 := hr6
    rw [hr6_eq] at hid_CS
    linarith [hid_CS, hcond]

/-! ## 2. Section C2.O6.5: Certification of Blocks 11, 12, and 13 ($s_{10} = 3, s_{11} = 2, s_{12} = 12$, $T_{13} = 65$) -/

/-- **One-Line Certification of Blocks 11, 12, and 13 ($s_{10} = 3, s_{11} = 2, s_{12} = 12$, $T_{13} = 65$)
(`eleven_twelve_thirteen_block_kneading_corridor_certification`, Section C2.O6.5)**:
Suppose `s 0 = 2, s 1 = 6, s 2 = 3, s 3 = 3, s 4 = 2, s 5 = 10, s 6 = 7, s 7 = 5, s 8 = 7, s 9 = 3`.
Then:
1. `(0 < renewalIntSlack s 11 ∧ centeredRenewalSlack s 11 < 0) ↔ s 10 = 3`,
2. When `s 10 = 3`:
   - `blockSteps s 11 = 51`,
   - `renewalIntSlack s 11 = 2021023793552195`,
   - `centeredRenewalSlack s 11 = -230776020133053`, and
   - `(0 < renewalIntSlack s 12 ∧ centeredRenewalSlack s 12 < 0) ↔ s 11 = 2`,
3. When `s 10 = 3` and `s 11 = 2`:
   - `blockSteps s 12 = 53`,
   - `renewalIntSlack s 12 = 174815632487771`,
   - `centeredRenewalSlack s 12 = -8832383622253221`, and
   - `(0 < renewalIntSlack s 13 ∧ centeredRenewalSlack s 13 < 0) ↔ s 12 = 12`, and
4. When `s 10 = 3`, `s 11 = 2`, and `s 12 = 12`:
   - `blockSteps s 13 = 65`,
   - `renewalIntSlack s 13 = 19117218250095301547`, and
   - `centeredRenewalSlack s 13 = -17776269897323801685`. -/
theorem eleven_twelve_thirteen_block_kneading_corridor_certification
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) :
    ((0 < renewalIntSlack s 11 ∧ centeredRenewalSlack s 11 < 0) ↔ s 10 = 3) ∧
      (s 10 = 3 →
        blockSteps s 11 = 51 ∧
          renewalIntSlack s 11 = 2021023793552195 ∧
          centeredRenewalSlack s 11 = -230776020133053 ∧
          ((0 < renewalIntSlack s 12 ∧ centeredRenewalSlack s 12 < 0) ↔ s 11 = 2)) ∧
      (s 10 = 3 → s 11 = 2 →
        blockSteps s 12 = 53 ∧
          renewalIntSlack s 12 = 174815632487771 ∧
          centeredRenewalSlack s 12 = -8832383622253221 ∧
          ((0 < renewalIntSlack s 13 ∧ centeredRenewalSlack s 13 < 0) ↔ s 12 = 12)) ∧
      (s 10 = 3 → s 11 = 2 → s 12 = 12 →
        blockSteps s 13 = 65 ∧
          renewalIntSlack s 13 = 19117218250095301547 ∧
          centeredRenewalSlack s 13 = -17776269897323801685) := by
  have h10 :=
    (nine_and_ten_block_kneading_corridor_certification hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7).2.2 hs8 hs9
  rcases h10 with ⟨hT10, hS10, _⟩
  have hsand10 := (subCeiling_step_sandwich_iff s 10).2.2
  rw [hT10, hS10] at hsand10
  have hwit11 := (subCeiling_rung_iff_eq_of_witness
    (S_N := 241652719293433) (T_N := 48) (s_star := 3)
    (by norm_num) (by norm_num) (s 10)).1
  have hiff11 : (0 < renewalIntSlack s 11 ∧ centeredRenewalSlack s 11 < 0) ↔ s 10 = 3 :=
    hsand10.trans hwit11
  refine ⟨hiff11, ?_, ?_, ?_⟩
  · intro hs10
    have hT11 : blockSteps s 11 = 51 := by
      change blockSteps s 10 + s 10 = 51
      rw [hT10, hs10]
    have hS11_eq := (subCeiling_step_sandwich_iff s 10).1
    have hCS11_eq := (subCeiling_step_sandwich_iff s 10).2.1
    rw [hT10, hS10, hs10] at hS11_eq hCS11_eq
    have hS11 : renewalIntSlack s 11 = 2021023793552195 := by rw [hS11_eq]; norm_num
    have hCS11 : centeredRenewalSlack s 11 = -230776020133053 := by rw [hCS11_eq]; norm_num
    have hsand11 := (subCeiling_step_sandwich_iff s 11).2.2
    rw [hT11, hS11] at hsand11
    have hwit12 := (subCeiling_rung_iff_eq_of_witness
      (S_N := 2021023793552195) (T_N := 51) (s_star := 2)
      (by norm_num) (by norm_num) (s 11)).1
    exact ⟨hT11, hS11, hCS11, hsand11.trans hwit12⟩
  · intro hs10 hs11
    have hT11 : blockSteps s 11 = 51 := by
      change blockSteps s 10 + s 10 = 51
      rw [hT10, hs10]
    have hS11_eq := (subCeiling_step_sandwich_iff s 10).1
    rw [hT10, hS10, hs10] at hS11_eq
    have hS11 : renewalIntSlack s 11 = 2021023793552195 := by rw [hS11_eq]; norm_num
    have hT12 : blockSteps s 12 = 53 := by
      change blockSteps s 11 + s 11 = 53
      rw [hT11, hs11]
    have hS12_eq := (subCeiling_step_sandwich_iff s 11).1
    have hCS12_eq := (subCeiling_step_sandwich_iff s 11).2.1
    rw [hT11, hS11, hs11] at hS12_eq hCS12_eq
    have hS12 : renewalIntSlack s 12 = 174815632487771 := by rw [hS12_eq]; norm_num
    have hCS12 : centeredRenewalSlack s 12 = -8832383622253221 := by rw [hCS12_eq]; norm_num
    have hsand12 := (subCeiling_step_sandwich_iff s 12).2.2
    rw [hT12, hS12] at hsand12
    have hwit13 := (subCeiling_rung_iff_eq_of_witness
      (S_N := 174815632487771) (T_N := 53) (s_star := 12)
      (by norm_num) (by norm_num) (s 12)).1
    exact ⟨hT12, hS12, hCS12, hsand12.trans hwit13⟩
  · intro hs10 hs11 hs12
    have hT11 : blockSteps s 11 = 51 := by
      change blockSteps s 10 + s 10 = 51
      rw [hT10, hs10]
    have hS11_eq := (subCeiling_step_sandwich_iff s 10).1
    rw [hT10, hS10, hs10] at hS11_eq
    have hS11 : renewalIntSlack s 11 = 2021023793552195 := by rw [hS11_eq]; norm_num
    have hT12 : blockSteps s 12 = 53 := by
      change blockSteps s 11 + s 11 = 53
      rw [hT11, hs11]
    have hS12_eq := (subCeiling_step_sandwich_iff s 11).1
    rw [hT11, hS11, hs11] at hS12_eq
    have hS12 : renewalIntSlack s 12 = 174815632487771 := by rw [hS12_eq]; norm_num
    have hT13 : blockSteps s 13 = 65 := by
      change blockSteps s 12 + s 12 = 65
      rw [hT12, hs12]
    have hS13_eq := (subCeiling_step_sandwich_iff s 12).1
    have hCS13_eq := (subCeiling_step_sandwich_iff s 12).2.1
    rw [hT12, hS12, hs12] at hS13_eq hCS13_eq
    exact ⟨hT13, by rw [hS13_eq]; norm_num, by rw [hCS13_eq]; norm_num⟩

end Mahler.UniversalPostTwoAndKneading13
