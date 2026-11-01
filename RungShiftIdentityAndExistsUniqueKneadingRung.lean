import UniversalSubCeilingNonBranchingAndKneading78

/-!
# The Rung-Shift Identity $\widehat{\Sigma}_{N+1}(s) = 3 \Sigma_{N+1}(s - 1)$, Universal Existence & Uniqueness (`∃! s_*`) of the Sub-Ceiling Rung, and 10-Block Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 5 / 20 (Part XX, Sections C2.O5.1–C2.O5.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section C2.O5.1 (Inner Loop 1 / 5) — Universal Rung-Shift Identity $\widehat{\Sigma}_{N+1}(s) = 3 \Sigma_{N+1}(s - 1)$
   (`candidateSlack`, `candidateCenteredSlack`, `candidateCenteredSlack_succ_eq_three_mul_candidateSlack`)**:
   - For any current slack $S_N \in \mathbb{Z}$, step sum $T_N \in \mathbb{N}$, and candidate block
     length $s = m + 1 \ge 1$:
     `candidateCenteredSlack S_N T_N (m + 1) = 3 * candidateSlack S_N T_N m`.
   - Thus a candidate rung $s = m + 1$ stays strictly below the ceiling
     (`candidateCenteredSlack S_N T_N (m + 1) < 0`) **if and only if** the rung $m = s - 1$ immediately
     below it dies (`candidateSlack S_N T_N m < 0`)!

2. **Section C2.O5.2 (Inner Loop 2 / 5) — Minimal-Surviving-Rung Characterization
   (`subCeiling_window_iff_survives_and_prev_dies`)**:
   - Whenever $S_N \bmod 2 = 1$, $3^m S_N \ne 2 \cdot 2^{T_N + m}$, so for every $m \in \mathbb{N}$:
     `0 < candidateSlack S_N T_N (m + 1) ∧ candidateCenteredSlack S_N T_N (m + 1) < 0 ↔
       0 < candidateSlack S_N T_N (m + 1) ∧ candidateSlack S_N T_N m ≤ 0`.

3. **Section C2.O5.3 (Inner Loop 3 / 5) — Universal Existence and Uniqueness (`∃! s_*`) of the Sub-Ceiling Rung
   (`exists_unique_subCeiling_rung_of_odd_subCeiling_slack`)**:
   - Whenever $1 \le S_N < 2^{T_N}$ and $S_N \bmod 2 = 1$, at $s = 1$ we have
     `candidateSlack S_N T_N 1 < 0`, while at $s = 2 * T_N + 2$ we have
     `0 < candidateSlack S_N T_N (2 * T_N + 2)`.
   - By `Nat.find` and `subCeiling_survival_rung_unique_and_trichotomy`, there exists a **unique**
     $s_* \in \mathbb{N}$ (`∃! s_star : ℕ`) satisfying
     `2 ≤ s_star ∧ s_star ≤ 2 * T_N + 2 ∧ 0 < candidateSlack S_N T_N s_star ∧ candidateCenteredSlack S_N T_N s_star < 0`!

4. **Sections C2.O5.4 & C2.O5.5 (Inner Loops 4–5 / 5) — Certification of the 9th ($s_8 = 7$) & 10th ($s_9 = 3$) Kneading Rungs
   (`nine_and_ten_block_kneading_corridor_certification`)**:
   - Certifies in one line of `norm_num` that after $(2, 6, 3, 3, 2, 10, 7, 5)$, the unique 9th
     sub-ceiling rung is $s_8 = 7$ ($T_9 = 45$, $\Sigma_9 = 29{,}800{,}098{,}989{,}435$,
     $\widehat{\Sigma}_9 = -5{,}384{,}273{,}099{,}397$) and the unique 10th sub-ceiling rung is
     $s_9 = 3$ ($T_{10} = 48$, $\Sigma_{10} = 241{,}652{,}881{,}249{,}747$,
     $\widehat{\Sigma}_{10} = -39{,}822{,}095{,}460{,}909$).
-/

namespace Mahler.RungShiftAndExistsUniqueKneading

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

/-! ## 1. Section C2.O5.1 & C2.O5.2: The Universal Rung-Shift Identity $\widehat{\Sigma}_{N+1}(s) = 3 \Sigma_{N+1}(s - 1)$ -/

/-- Candidate next-step renewal slack $\Sigma_{N+1}(s) = 3^s S_N - 2 \cdot 2^{T_N + s}$. -/
def candidateSlack (S_N : ℤ) (T_N s : ℕ) : ℤ :=
  (3 : ℤ) ^ s * S_N - 2 * (2 : ℤ) ^ (T_N + s)

/-- Candidate next-step centered slack $\widehat{\Sigma}_{N+1}(s) = 3^s S_N - 3 \cdot 2^{T_N + s}$. -/
def candidateCenteredSlack (S_N : ℤ) (T_N s : ℕ) : ℤ :=
  (3 : ℤ) ^ s * S_N - 3 * (2 : ℤ) ^ (T_N + s)

/-- **Universal Rung-Shift Identity (`candidateCenteredSlack_succ_eq_three_mul_candidateSlack`,
Section C2.O5.1)**:
For every `S_N : ℤ` and `T_N, m : ℕ`:
`candidateCenteredSlack S_N T_N (m + 1) = 3 * candidateSlack S_N T_N m`. -/
theorem candidateCenteredSlack_succ_eq_three_mul_candidateSlack
    (S_N : ℤ) (T_N m : ℕ) :
    candidateCenteredSlack S_N T_N (m + 1) = 3 * candidateSlack S_N T_N m := by
  unfold candidateCenteredSlack candidateSlack
  rw [show T_N + (m + 1) = (T_N + m) + 1 by omega, pow_succ (3 : ℤ) m, pow_succ (2 : ℤ) (T_N + m)]
  ring

/-- **Minimal-Surviving-Rung Characterization (`subCeiling_window_iff_survives_and_prev_dies`,
Section C2.O5.2)**:
Whenever `S_N % 2 = 1`, `candidateSlack S_N T_N m ≠ 0`, and for every `m : ℕ`:
`(0 < candidateSlack S_N T_N (m + 1) ∧ candidateCenteredSlack S_N T_N (m + 1) < 0) ↔
  (0 < candidateSlack S_N T_N (m + 1) ∧ candidateSlack S_N T_N m ≤ 0)`. -/
theorem subCeiling_window_iff_survives_and_prev_dies
    {S_N : ℤ} (hodd : S_N % 2 = 1) (T_N m : ℕ) :
    candidateSlack S_N T_N m ≠ 0 ∧
      ((0 < candidateSlack S_N T_N (m + 1) ∧ candidateCenteredSlack S_N T_N (m + 1) < 0) ↔
        (0 < candidateSlack S_N T_N (m + 1) ∧ candidateSlack S_N T_N m ≤ 0)) := by
  have hodd3 : ∀ n : ℕ, ((3 : ℤ) ^ n) % 2 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Int.mul_emod, ih]; rfl
  have hne0 : candidateSlack S_N T_N m ≠ 0 := by
    unfold candidateSlack
    have h3 : ((3 : ℤ) ^ m * S_N) % 2 = 1 := by
      rw [Int.mul_emod, hodd3 m, hodd]
      rfl
    omega
  rw [candidateCenteredSlack_succ_eq_three_mul_candidateSlack]
  refine ⟨hne0, ?_⟩
  constructor
  · rintro ⟨hpos, hneg⟩
    exact ⟨hpos, by omega⟩
  · rintro ⟨hpos, hle⟩
    exact ⟨hpos, by omega⟩

/-! ## 2. Section C2.O5.3: Universal Existence & Uniqueness (`∃! s_*`) of the Sub-Ceiling Rung -/

/-- Auxiliary inequality: for all `T : ℕ`, `2 * 2 ^ (3 * T + 2) < 3 ^ (2 * T + 2)`. -/
theorem two_mul_two_pow_three_mul_add_two_lt_three_pow (T : ℕ) :
    2 * (2 : ℤ) ^ (3 * T + 2) < (3 : ℤ) ^ (2 * T + 2) := by
  induction T with
  | zero => decide
  | succ T ih =>
      have h1 : 2 * (2 : ℤ) ^ (3 * (T + 1) + 2) = 8 * (2 * (2 : ℤ) ^ (3 * T + 2)) := by
        rw [show 3 * (T + 1) + 2 = (3 * T + 2) + 3 by omega, pow_add]
        ring
      have h2 : (3 : ℤ) ^ (2 * (T + 1) + 2) = 9 * (3 : ℤ) ^ (2 * T + 2) := by
        rw [show 2 * (T + 1) + 2 = (2 * T + 2) + 2 by omega, pow_add]
        ring
      have hpos : (0 : ℤ) ≤ 2 * (2 : ℤ) ^ (3 * T + 2) := by positivity
      linarith

/-- **Universal Existence and Uniqueness (`∃! s_*`) of the Sub-Ceiling Rung
(`exists_unique_subCeiling_rung_of_odd_subCeiling_slack`, Section C2.O5.3)**:
Whenever `1 ≤ S_N`, `S_N < (2 : ℤ) ^ T_N`, and `S_N % 2 = 1`, there exists a **unique**
`s_star : ℕ` (`∃! s_star : ℕ`) such that
`0 < candidateSlack S_N T_N s_star ∧ candidateCenteredSlack S_N T_N s_star < 0`,
and moreover `2 ≤ s_star ∧ s_star ≤ 2 * T_N + 2`! -/
theorem exists_unique_subCeiling_rung_of_odd_subCeiling_slack
    {S_N : ℤ} {T_N : ℕ}
    (hpos : 1 ≤ S_N) (hlt : S_N < (2 : ℤ) ^ T_N) (hodd : S_N % 2 = 1) :
    (∃ s_star : ℕ,
      2 ≤ s_star ∧ s_star ≤ 2 * T_N + 2 ∧
        0 < candidateSlack S_N T_N s_star ∧
        candidateCenteredSlack S_N T_N s_star < 0) ∧
      ∃! s_star : ℕ,
        0 < candidateSlack S_N T_N s_star ∧
          candidateCenteredSlack S_N T_N s_star < 0 := by
  have hex_pos : ∃ s : ℕ, 0 < candidateSlack S_N T_N s := by
    refine ⟨2 * T_N + 2, ?_⟩
    unfold candidateSlack
    have hpow := two_mul_two_pow_three_mul_add_two_lt_three_pow T_N
    have hmul : (3 : ℤ) ^ (2 * T_N + 2) * 1 ≤ (3 : ℤ) ^ (2 * T_N + 2) * S_N :=
      mul_le_mul_of_nonneg_left hpos (by positivity)
    rw [show T_N + (2 * T_N + 2) = 3 * T_N + 2 by omega]
    linarith
  classical
  set s_star := Nat.find hex_pos
  have hs_pos : 0 < candidateSlack S_N T_N s_star := Nat.find_spec hex_pos
  have hs_le_bound : s_star ≤ 2 * T_N + 2 := by
    refine Nat.find_min' hex_pos ?_
    unfold candidateSlack
    have hpow := two_mul_two_pow_three_mul_add_two_lt_three_pow T_N
    have hmul : (3 : ℤ) ^ (2 * T_N + 2) * 1 ≤ (3 : ℤ) ^ (2 * T_N + 2) * S_N :=
      mul_le_mul_of_nonneg_left hpos (by positivity)
    rw [show T_N + (2 * T_N + 2) = 3 * T_N + 2 by omega]
    linarith
  have hs_not_0 : s_star ≠ 0 := by
    intro h0
    have h := hs_pos
    rw [h0] at h
    unfold candidateSlack at h
    simp only [pow_zero, one_mul, Nat.add_zero] at h
    have h2_pos : (0 : ℤ) < (2 : ℤ) ^ T_N := pow_pos (by decide) T_N
    linarith
  have hs_not_1 : s_star ≠ 1 := by
    intro h1
    have h := hs_pos
    rw [h1] at h
    unfold candidateSlack at h
    rw [pow_one, pow_add, pow_one] at h
    have h2_pos : (0 : ℤ) < (2 : ℤ) ^ T_N := pow_pos (by decide) T_N
    linarith
  have hs_ge2 : 2 ≤ s_star := by omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s_star = m + 1 := ⟨s_star - 1, by omega⟩
  have hm_lt : m < s_star := by omega
  have hm_nonpos : candidateSlack S_N T_N m ≤ 0 := by
    have hnot := Nat.find_min hex_pos hm_lt
    linarith
  have hwin :
      0 < candidateSlack S_N T_N s_star ∧
        candidateCenteredSlack S_N T_N s_star < 0 := by
    rw [hm] at hs_pos ⊢
    exact (subCeiling_window_iff_survives_and_prev_dies hodd T_N m).2.mpr ⟨hs_pos, hm_nonpos⟩
  refine ⟨⟨s_star, hs_ge2, hs_le_bound, hwin.1, hwin.2⟩, ⟨s_star, hwin, ?_⟩⟩
  intro s ⟨hs1, hs2⟩
  have h1 := hwin.1
  have h2 := hwin.2
  unfold candidateSlack at hs1 h1
  unfold candidateCenteredSlack at hs2 h2
  exact (subCeiling_survival_rung_unique_and_trichotomy S_N T_N s s_star).2.2
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

/-! ## 3. Sections C2.O5.4 & C2.O5.5: Certification of the 9th ($s_8 = 7$) & 10th ($s_9 = 3$) Kneading Rungs -/

/-- **One-Line Certification of the 9th ($s_8 = 7$) and 10th ($s_9 = 3$) Sub-Ceiling Kneading Rungs
(`nine_and_ten_block_kneading_corridor_certification`, Sections C2.O5.4 & C2.O5.5)**:
Suppose `s 0 = 2, s 1 = 6, s 2 = 3, s 3 = 3, s 4 = 2, s 5 = 10, s 6 = 7, s 7 = 5`. Then:
1. `(0 < renewalIntSlack s 9 ∧ centeredRenewalSlack s 9 < 0) ↔ s 8 = 7`,
2. When `s 8 = 7`:
   - `blockSteps s 9 = 45`,
   - `renewalIntSlack s 9 = 29800098989435`,
   - `centeredRenewalSlack s 9 = -5384273099397`, and
   - `(0 < renewalIntSlack s 10 ∧ centeredRenewalSlack s 10 < 0) ↔ s 9 = 3`, and
3. When `s 8 = 7` and `s 9 = 3`:
   - `blockSteps s 10 = 48`,
   - `renewalIntSlack s 10 = 241652719293433`, and
   - `centeredRenewalSlack s 10 = -39822257417223`. -/
theorem nine_and_ten_block_kneading_corridor_certification
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5) :
    ((0 < renewalIntSlack s 9 ∧ centeredRenewalSlack s 9 < 0) ↔ s 8 = 7) ∧
      (s 8 = 7 →
        blockSteps s 9 = 45 ∧
          renewalIntSlack s 9 = 29800098989435 ∧
          centeredRenewalSlack s 9 = -5384273099397 ∧
          ((0 < renewalIntSlack s 10 ∧ centeredRenewalSlack s 10 < 0) ↔ s 9 = 3)) ∧
      (s 8 = 7 → s 9 = 3 →
        blockSteps s 10 = 48 ∧
          renewalIntSlack s 10 = 241652719293433 ∧
          centeredRenewalSlack s 10 = -39822257417223) := by
  have h8 := (seven_and_eight_block_kneading_corridor_certification hs0 hs1 hs2 hs3 hs4 hs5).2.2 hs6 hs7
  rcases h8 with ⟨hT8, hS8, _⟩
  have hsand8 := (subCeiling_step_sandwich_iff s 8).2.2
  rw [hT8, hS8] at hsand8
  have hwit9 := (subCeiling_rung_iff_eq_of_witness (S_N := 45801940177) (T_N := 38) (s_star := 7)
    (by norm_num) (by norm_num) (s 8)).1
  have hiff9 : (0 < renewalIntSlack s 9 ∧ centeredRenewalSlack s 9 < 0) ↔ s 8 = 7 :=
    hsand8.trans hwit9
  refine ⟨hiff9, ?_, ?_⟩
  · intro hs8
    have hT9 : blockSteps s 9 = 45 := by
      change blockSteps s 8 + s 8 = 45
      rw [hT8, hs8]
    have hS9_eq := (subCeiling_step_sandwich_iff s 8).1
    have hCS9_eq := (subCeiling_step_sandwich_iff s 8).2.1
    rw [hT8, hS8, hs8] at hS9_eq hCS9_eq
    have hS9 : renewalIntSlack s 9 = 29800098989435 := by rw [hS9_eq]; norm_num
    have hCS9 : centeredRenewalSlack s 9 = -5384273099397 := by rw [hCS9_eq]; norm_num
    have hsand9 := (subCeiling_step_sandwich_iff s 9).2.2
    rw [hT9, hS9] at hsand9
    have hwit10 := (subCeiling_rung_iff_eq_of_witness (S_N := 29800098989435) (T_N := 45) (s_star := 3)
      (by norm_num) (by norm_num) (s 9)).1
    exact ⟨hT9, hS9, hCS9, hsand9.trans hwit10⟩
  · intro hs8 hs9
    have hT9 : blockSteps s 9 = 45 := by
      change blockSteps s 8 + s 8 = 45
      rw [hT8, hs8]
    have hS9_eq := (subCeiling_step_sandwich_iff s 8).1
    rw [hT8, hS8, hs8] at hS9_eq
    have hS9 : renewalIntSlack s 9 = 29800098989435 := by rw [hS9_eq]; norm_num
    have hT10 : blockSteps s 10 = 48 := by
      change blockSteps s 9 + s 9 = 48
      rw [hT9, hs9]
    have hS10_eq := (subCeiling_step_sandwich_iff s 9).1
    have hCS10_eq := (subCeiling_step_sandwich_iff s 9).2.1
    rw [hT9, hS9, hs9] at hS10_eq hCS10_eq
    exact ⟨hT10, by rw [hS10_eq]; norm_num, by rw [hCS10_eq]; norm_num⟩

end Mahler.RungShiftAndExistsUniqueKneading
