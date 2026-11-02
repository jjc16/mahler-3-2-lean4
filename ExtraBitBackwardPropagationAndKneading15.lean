import UniversalPostTwoRecoveryAndKneading13

/-!
# Backward Propagation of the Extra-Bit Congruence $2^{T_N+1} \mid (3^{T_N} P_0 + A_{0,N})$, Mod-$2^{T_N+1}$ Seed Uniqueness & 15-Block ($T_{15} = 72$) Kneading Certification

This module formalizes **Second Campaign (`m = 5, n = 20`) — Outer Loop 7 / 20 (Part XXII, Sections C2.O7.1–C2.O7.5)**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Sections C2.O7.1 & C2.O7.2 (Inner Loops 1–2 / 5) — Backward Propagation of the Extra-Bit Congruence
   (`extra_bit_congruence_one_step_backward`,
   `extra_bit_congruence_propagates_to_all_prefixes`)**:
   - Proves that if $1 \le s_N$ and $2^{T_{N+1} + 1} \mid (3^{T_{N+1}} P_0 + A_{0,N+1})$, then there
     exists an odd integer $u_N$ (`u_N % 2 = 1`) such that
     `3 ^ T_N * P_0 + renewalNumerator s N = 2 ^ (T_N + s N) * u_N` and
     `2 ^ (T_N + 1) ∣ (3 ^ T_N * P_0 + renewalNumerator s N)`.
   - By downward induction, a **single** terminal congruence $2^{T_N + 1} \mid (3^{T_N} P_0 + A_{0,N})$
     ($\forall k < N, 1 \le s_k$) propagates backward to every intermediate prefix $k \le N$!

2. **Section C2.O7.3 (Inner Loop 3 / 5) — Mod-$2^{T_N+1}$ Two-Seed Uniqueness for Any $N$-Block Prefix
   (`two_seeds_same_validBlockChain_mod_two_pow_succ_dvd`)**:
   - Whenever two seeds $b_1 \le b_2$ both realize the same $N$-block gap sequence $s$ ($1 \le N$):
     `2 ^ (blockSteps s N + 1) ∣ (b_2 - b_1)` and
     `(2 * 3 ^ (blockSteps s N)) ∣ (orbit b_2 (blockSteps s N) - orbit b_1 (blockSteps s N))`.

3. **Sections C2.O7.4 & C2.O7.5 (Inner Loops 4–5 / 5) — Certification of the 14th ($s_{13} = 4$) & 15th ($s_{14} = 3$) Kneading Rungs ($T_{15} = 72$)
   (`fourteen_and_fifteen_block_kneading_corridor_and_two_pow_73_uniqueness`)**:
   - Certifies that after $(2, 6, 3, 3, 2, 10, 7, 5, 7, 3, 3, 2, 12)$, the unique 14th and 15th
     sub-ceiling kneading rungs are $s_{13} = 4$ ($T_{14} = 69$) and $s_{14} = 3$ ($T_{15} = 72$),
     and any two seeds $b_1 < b_2$ realizing this 15-block prefix satisfy $2^{73} \mid (b_2 - b_1)$
     (`2 ^ 73 ≤ b_2`)!
-/

namespace Mahler.ExtraBitBackwardAndKneading15

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

/-! ## 1. Sections C2.O7.1 & C2.O7.2: Backward Propagation of the Extra-Bit Congruence -/

/-- **One-Step Backward Propagation of the Extra-Bit Congruence
(`extra_bit_congruence_one_step_backward`, Section C2.O7.1)**:
Suppose `1 ≤ s N` and `2 ^ (blockSteps s (N + 1) + 1) ∣ (3 ^ (blockSteps s (N + 1)) * P_0 + renewalNumerator s (N + 1))`.
Set `T_N = blockSteps s N`. Then there exists an odd integer `u_N` (`u_N % 2 = 1`) such that:
1. `3 ^ T_N * P_0 + renewalNumerator s N = 2 ^ (T_N + s N) * u_N`, and
2. `2 ^ (T_N + 1) ∣ (3 ^ T_N * P_0 + renewalNumerator s N)`. -/
theorem extra_bit_congruence_one_step_backward
    {P_0 N : ℕ} {s : ℕ → ℕ} (hsN : 1 ≤ s N)
    (hdvd : 2 ^ (blockSteps s (N + 1) + 1) ∣
      (3 ^ (blockSteps s (N + 1)) * P_0 + renewalNumerator s (N + 1))) :
    let T_N := blockSteps s N
    (∃ u_N : ℕ,
      u_N % 2 = 1 ∧
        3 ^ T_N * P_0 + renewalNumerator s N = 2 ^ (T_N + s N) * u_N) ∧
      2 ^ (T_N + 1) ∣ (3 ^ T_N * P_0 + renewalNumerator s N) := by
  intro T_N
  rcases hdvd with ⟨q, hq⟩
  have hT_succ : blockSteps s (N + 1) = T_N + s N := rfl
  have hA_succ :
      renewalNumerator s (N + 1) = 3 ^ (s N) * renewalNumerator s N + 2 ^ (T_N + s N) := rfl
  rw [hT_succ, hA_succ] at hq
  have hlhs :
      3 ^ (T_N + s N) * P_0 + (3 ^ (s N) * renewalNumerator s N + 2 ^ (T_N + s N)) =
        3 ^ (s N) * (3 ^ T_N * P_0 + renewalNumerator s N) + 2 ^ (T_N + s N) := by
    rw [Nat.pow_add]
    ring
  have hrhs : 2 ^ (T_N + s N + 1) * q = 2 ^ (T_N + s N) * (2 * q) := by
    rw [Nat.pow_succ]
    ring
  rw [hlhs, hrhs] at hq
  have hq_pos : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · have h2_pos : 0 < 2 ^ (T_N + s N) := Nat.pow_pos (by decide)
      omega
    · exact hpos
  have hsub :
      3 ^ (s N) * (3 ^ T_N * P_0 + renewalNumerator s N) =
        2 ^ (T_N + s N) * (2 * q - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  have hcop : Nat.Coprime (3 ^ (s N)) (2 ^ (T_N + s N)) :=
    (Nat.Coprime.pow_left (s N) (by decide)).pow_right (T_N + s N)
  have hdvd_3s : 3 ^ (s N) ∣ (2 * q - 1) :=
    hcop.dvd_of_dvd_mul_left ⟨3 ^ T_N * P_0 + renewalNumerator s N, hsub.symm⟩
  rcases hdvd_3s with ⟨u_N, hu_N⟩
  have hodd3 : ∀ m : ℕ, 3 ^ m % 2 = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hu_odd : u_N % 2 = 1 := by
    have h2q1_odd : (2 * q - 1) % 2 = 1 := by omega
    rw [hu_N, Nat.mul_mod, hodd3 (s N)] at h2q1_odd
    omega
  have hmul_eq :
      3 ^ (s N) * (3 ^ T_N * P_0 + renewalNumerator s N) =
        3 ^ (s N) * (2 ^ (T_N + s N) * u_N) := by
    rw [hsub, hu_N]
    ring
  have hprev_eq :
      3 ^ T_N * P_0 + renewalNumerator s N = 2 ^ (T_N + s N) * u_N :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul_eq
  have hdvd_prev : 2 ^ (T_N + 1) ∣ (3 ^ T_N * P_0 + renewalNumerator s N) := by
    rw [hprev_eq]
    have hsplit : T_N + s N = (T_N + 1) + (s N - 1) := by omega
    rw [hsplit, Nat.pow_add]
    exact ⟨2 ^ (s N - 1) * u_N, by ring⟩
  exact ⟨⟨u_N, hu_odd, hprev_eq⟩, hdvd_prev⟩

/-- **All-Prefix Backward Propagation of the Extra-Bit Congruence
(`extra_bit_congruence_propagates_to_all_prefixes`, Section C2.O7.2)**:
If `∀ k < N, 1 ≤ s k` and `2 ^ (blockSteps s N + 1) ∣ (3 ^ (blockSteps s N) * P_0 + renewalNumerator s N)`,
then for **every** `k ≤ N`:
`2 ^ (blockSteps s k + 1) ∣ (3 ^ (blockSteps s k) * P_0 + renewalNumerator s k)`,
and for every `k < N`, there exists an odd integer `u_k` (`u_k % 2 = 1`) such that
`3 ^ (blockSteps s k) * P_0 + renewalNumerator s k = 2 ^ (blockSteps s (k + 1)) * u_k`! -/
theorem extra_bit_congruence_propagates_to_all_prefixes
    {P_0 N : ℕ} {s : ℕ → ℕ}
    (hs : ∀ k < N, 1 ≤ s k)
    (hdvd : 2 ^ (blockSteps s N + 1) ∣ (3 ^ (blockSteps s N) * P_0 + renewalNumerator s N)) :
    (∀ k ≤ N,
      2 ^ (blockSteps s k + 1) ∣ (3 ^ (blockSteps s k) * P_0 + renewalNumerator s k)) ∧
      (∀ k < N,
        ∃ u_k : ℕ,
          u_k % 2 = 1 ∧
            3 ^ (blockSteps s k) * P_0 + renewalNumerator s k =
              2 ^ (blockSteps s (k + 1)) * u_k) := by
  induction N with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        exact hdvd
      · intro k hk; omega
  | succ N ih =>
      have hback := extra_bit_congruence_one_step_backward (hs N (by omega)) hdvd
      rcases ih (fun k hk => hs k (by omega)) hback.2 with ⟨hall_le, hall_lt⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · exact hdvd
        · exact hall_le k (by omega)
      · intro k hk
        rcases Nat.eq_or_lt_of_le (by omega : k ≤ N) with rfl | hlt
        · exact hback.1
        · exact hall_lt k hlt

/-! ## 2. Section C2.O7.3: Mod-$2^{T_N+1}$ Two-Seed Uniqueness for Any $N$-Block Prefix -/

/-- **Mod-$2^{T_N+1}$ Two-Seed Uniqueness for Any Valid $N$-Block Prefix
(`two_seeds_same_validBlockChain_mod_two_pow_succ_dvd`, Section C2.O7.3)**:
If two seeds `b₁ ≤ b₂` both realize the same `N`-block gap sequence `s` (`1 ≤ N`,
`ValidBlockChain b₁ s u₁ N`, `ValidBlockChain b₂ s u₂ N`), setting `T_N = blockSteps s N`:
1. `orbit b₁ T_N ≤ orbit b₂ T_N`,
2. `2 ^ T_N * (orbit b₂ T_N - orbit b₁ T_N) = 3 ^ T_N * (b₂ - b₁)`, and
3. `2 ^ (T_N + 1) ∣ (b₂ - b₁)` and `(2 * 3 ^ T_N) ∣ (orbit b₂ T_N - orbit b₁ T_N)`. -/
theorem two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
    {b₁ b₂ N : ℕ} {s u₁ u₂ : ℕ → ℕ}
    (hN : 1 ≤ N) (hle : b₁ ≤ b₂)
    (hch₁ : ValidBlockChain b₁ s u₁ N)
    (hch₂ : ValidBlockChain b₂ s u₂ N) :
    let T_N := blockSteps s N
    orbit b₁ T_N ≤ orbit b₂ T_N ∧
      2 ^ T_N * (orbit b₂ T_N - orbit b₁ T_N) = 3 ^ T_N * (b₂ - b₁) ∧
      (2 ^ (T_N + 1) ∣ (b₂ - b₁)) ∧
      ((2 * 3 ^ T_N) ∣ (orbit b₂ T_N - orbit b₁ T_N)) := by
  intro T_N
  have hm₁ := mixed_block_integer_identity hch₁
  have hm₂ := mixed_block_integer_identity hch₂
  change 2 ^ T_N * orbit b₁ T_N = 3 ^ T_N * b₁ + blockKernel s N at hm₁
  change 2 ^ T_N * orbit b₂ T_N = 3 ^ T_N * b₂ + blockKernel s N at hm₂
  have hmul_le : 2 ^ T_N * orbit b₁ T_N ≤ 2 ^ T_N * orbit b₂ T_N := by
    have h3 : 3 ^ T_N * b₁ ≤ 3 ^ T_N * b₂ := Nat.mul_le_mul_left (3 ^ T_N) hle
    omega
  have horb_le : orbit b₁ T_N ≤ orbit b₂ T_N :=
    Nat.le_of_mul_le_mul_left hmul_le (Nat.pow_pos (by decide))
  have hdiff : 2 ^ T_N * (orbit b₂ T_N - orbit b₁ T_N) = 3 ^ T_N * (b₂ - b₁) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  have hodd₁ : orbit b₁ T_N % 2 = 1 := mixed_block_return_odd hN hch₁
  have hodd₂ : orbit b₂ T_N % 2 = 1 := mixed_block_return_odd hN hch₂
  have heven_diff : 2 ∣ (orbit b₂ T_N - orbit b₁ T_N) := by omega
  rcases heven_diff with ⟨q, hq⟩
  have hdiff_q : 2 ^ (T_N + 1) * q = 3 ^ T_N * (b₂ - b₁) := by
    rw [Nat.pow_succ, mul_assoc, ← hq, hdiff]
  have hcop : Nat.Coprime (2 ^ (T_N + 1)) (3 ^ T_N) :=
    (Nat.Coprime.pow_left (T_N + 1) (by decide)).pow_right T_N
  have hdvd_b : 2 ^ (T_N + 1) ∣ (b₂ - b₁) :=
    hcop.dvd_of_dvd_mul_left ⟨q, hdiff_q.symm⟩
  have hcop3 : Nat.Coprime (3 ^ T_N) (2 ^ T_N) :=
    (Nat.Coprime.pow_left T_N (by decide)).pow_right T_N
  have hq_rel : 2 ^ T_N * (2 * q) = 3 ^ T_N * (b₂ - b₁) := by
    rw [← hq, hdiff]
  have hcop3_2 : Nat.Coprime (3 ^ T_N) (2 ^ T_N * 2) := by
    rw [← Nat.pow_succ]
    exact hcop.symm
  have hdvd_q : 3 ^ T_N ∣ q := by
    refine hcop3_2.dvd_of_dvd_mul_left ?_
    exact ⟨b₂ - b₁, by linarith [hq_rel]⟩
  rcases hdvd_q with ⟨k, rfl⟩
  refine ⟨horb_le, hdiff, hdvd_b, ⟨k, by linarith [hq]⟩⟩

/-! ## 3. Sections C2.O7.4 & C2.O7.5: Certification of Blocks 14 & 15 ($s_{13} = 4, s_{14} = 3, T_{15} = 72$) -/

/-- **One-Line Certification of the 14th ($s_{13} = 4$) and 15th ($s_{14} = 3$) Sub-Ceiling Kneading Rungs
(`fourteen_and_fifteen_block_kneading_corridor_and_two_pow_73_uniqueness`, Sections C2.O7.4 & C2.O7.5)**:
Suppose `s 0 = 2, s 1 = 6, s 2 = 3, s 3 = 3, s 4 = 2, s 5 = 10, s 6 = 7, s 7 = 5, s 8 = 7, s 9 = 3, s 10 = 3, s 11 = 2, s 12 = 12`.
Then:
1. `(0 < renewalIntSlack s 14 ∧ centeredRenewalSlack s 14 < 0) ↔ s 13 = 4`,
2. When `s 13 = 4`:
   - `blockSteps s 14 = 69`,
   - `renewalIntSlack s 14 = 367903057540308121883`,
   - `centeredRenewalSlack s 14 = -222392752818397529829`, and
   - `(0 < renewalIntSlack s 15 ∧ centeredRenewalSlack s 15 < 0) ↔ s 14 = 3`,
3. When `s 13 = 4` and `s 14 = 3`:
   - `blockSteps s 15 = 72`,
   - `renewalIntSlack s 15 = 488649587849028863449`,
   - `centeredRenewalSlack s 15 = -4233716895020616350247`, and
   - Any two seeds `b₁ < b₂` realizing this 15-block prefix satisfy `2 ^ 73 ∣ (b₂ - b₁)`
     and `2 ^ 73 ≤ b₂`! -/
theorem fourteen_and_fifteen_block_kneading_corridor_and_two_pow_73_uniqueness
    {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3)
    (hs4 : s 4 = 2) (hs5 : s 5 = 10) (hs6 : s 6 = 7) (hs7 : s 7 = 5)
    (hs8 : s 8 = 7) (hs9 : s 9 = 3) (hs10 : s 10 = 3) (hs11 : s 11 = 2)
    (hs12 : s 12 = 12) :
    ((0 < renewalIntSlack s 14 ∧ centeredRenewalSlack s 14 < 0) ↔ s 13 = 4) ∧
      (s 13 = 4 →
        blockSteps s 14 = 69 ∧
          renewalIntSlack s 14 = 367903057540308121883 ∧
          centeredRenewalSlack s 14 = -222392752818397529829 ∧
          ((0 < renewalIntSlack s 15 ∧ centeredRenewalSlack s 15 < 0) ↔ s 14 = 3)) ∧
      (s 13 = 4 → s 14 = 3 →
        blockSteps s 15 = 72 ∧
          renewalIntSlack s 15 = 488649587849028863449 ∧
          centeredRenewalSlack s 15 = -4233716895020616350247 ∧
          (∀ (b₁ b₂ : ℕ) (u₁ u₂ : ℕ → ℕ),
            b₁ < b₂ →
            ValidBlockChain b₁ s u₁ 15 →
            ValidBlockChain b₂ s u₂ 15 →
              2 ^ 73 ∣ (b₂ - b₁) ∧ 2 ^ 73 ≤ b₂)) := by
  have h13 :=
    (eleven_twelve_thirteen_block_kneading_corridor_certification
      hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9).2.2.2 hs10 hs11 hs12
  rcases h13 with ⟨hT13, hS13, _⟩
  have hsand13 := (subCeiling_step_sandwich_iff s 13).2.2
  rw [hT13, hS13] at hsand13
  have hwit14 := (subCeiling_rung_iff_eq_of_witness
    (S_N := 19117218250095301547) (T_N := 65) (s_star := 4)
    (by norm_num) (by norm_num) (s 13)).1
  have hiff14 : (0 < renewalIntSlack s 14 ∧ centeredRenewalSlack s 14 < 0) ↔ s 13 = 4 :=
    hsand13.trans hwit14
  refine ⟨hiff14, ?_, ?_⟩
  · intro hs13
    have hT14 : blockSteps s 14 = 69 := by
      change blockSteps s 13 + s 13 = 69
      rw [hT13, hs13]
    have hS14_eq := (subCeiling_step_sandwich_iff s 13).1
    have hCS14_eq := (subCeiling_step_sandwich_iff s 13).2.1
    rw [hT13, hS13, hs13] at hS14_eq hCS14_eq
    have hS14 : renewalIntSlack s 14 = 367903057540308121883 := by rw [hS14_eq]; norm_num
    have hCS14 : centeredRenewalSlack s 14 = -222392752818397529829 := by rw [hCS14_eq]; norm_num
    have hsand14 := (subCeiling_step_sandwich_iff s 14).2.2
    rw [hT14, hS14] at hsand14
    have hwit15 := (subCeiling_rung_iff_eq_of_witness
      (S_N := 367903057540308121883) (T_N := 69) (s_star := 3)
      (by norm_num) (by norm_num) (s 14)).1
    exact ⟨hT14, hS14, hCS14, hsand14.trans hwit15⟩
  · intro hs13 hs14
    have hT14 : blockSteps s 14 = 69 := by
      change blockSteps s 13 + s 13 = 69
      rw [hT13, hs13]
    have hS14_eq := (subCeiling_step_sandwich_iff s 13).1
    rw [hT13, hS13, hs13] at hS14_eq
    have hS14 : renewalIntSlack s 14 = 367903057540308121883 := by rw [hS14_eq]; norm_num
    have hT15 : blockSteps s 15 = 72 := by
      change blockSteps s 14 + s 14 = 72
      rw [hT14, hs14]
    have hS15_eq := (subCeiling_step_sandwich_iff s 14).1
    have hCS15_eq := (subCeiling_step_sandwich_iff s 14).2.1
    rw [hT14, hS14, hs14] at hS15_eq hCS15_eq
    refine ⟨hT15, by rw [hS15_eq]; norm_num, by rw [hCS15_eq]; norm_num, ?_⟩
    intro b₁ b₂ u₁ u₂ hlt hch₁ hch₂
    have hdvd := (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd
      (by decide : 1 ≤ 15) (le_of_lt hlt) hch₁ hch₂).2.2.1
    change 2 ^ (blockSteps s 15 + 1) ∣ (b₂ - b₁) at hdvd
    rw [hT15] at hdvd
    have hpos : 0 < b₂ - b₁ := by omega
    have hle := Nat.le_of_dvd hpos hdvd
    exact ⟨hdvd, by omega⟩

end Mahler.ExtraBitBackwardAndKneading15
