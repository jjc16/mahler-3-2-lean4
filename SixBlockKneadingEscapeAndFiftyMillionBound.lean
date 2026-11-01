import TwoAdicRecoveryCascadePruningTree

/-!
# Six-Block $(2, 6, 3, 3, 2, s_5)$ Slack Law ($s_5 \ge 10$) & the $b_0 \equiv 50{,}387{,}465 \pmod{2^{27}}$ Lower Bound

This module formalizes **Outer Loop 7 / 10 (Part XI, Sections O7.1–O7.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O7.1 (Inner Loop 1 / 3) — Mod-131072 Classification of the 5-Block Kneading Prefix $(2, 6, 3, 3, 2)$
   (`two_six_three_three_two_mod_131072_classification`)**:
   - Along $b_0 = 6665 + 16384 k$ ($n = 3 + 8 k$), $P_3 = 8(216206 + 531441 k)$, so $s_3 = 3$
     (`Q_3 % 2 = 1`) $\iff k \bmod 2 = 1$ ($k = 1 + 2 \ell$, $b_0 = 23049 + 32768 \ell$).
   - Along $k = 1 + 2 \ell$, $P_4 = 2(10093235 + 14348907 \ell)$, so:
     - $\ell \bmod 2 = 0 \iff (2 \mid P_4 \land \neg(4 \mid P_4))$ ($s_4 = 1$, instant death),
     - $\ell \bmod 4 = 3 \iff 8 \mid P_4$ ($s_4 \ge 3$), and
     - $\ell \bmod 4 = 1 \iff (4 \mid P_4 \land \neg(8 \mid P_4)) \iff b_0 \bmod 131072 = 55817$ ($s_4 = 2$).

2. **Section O7.2 (Inner Loop 2 / 3) — Six-Block Slack Law $\Sigma_6(2, 6, 3, 3, 2, s_5) = 2425 \cdot 3^{s_5} - 131072 \cdot 2^{s_5}$
   (`six_block_kneading_s5_slack_and_escape_iff_le_nine`)**:
   - Whenever $s = (2, 6, 3, 3, 2, s_5, \dots)$, `blockSteps s 6 = 16 + s 5` and
     `renewalIntSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 131072 * (2 : ℤ) ^ (s 5)`.
   - Consequently, `2 * renewalNumerator s 6 ≥ 3 ^ (blockSteps s 6) ↔ s 5 ≤ 9`, while at $s_5 = 10$,
     `renewalIntSlack s 6 = 8976097 > 0`.

3. **Section O7.3 (Inner Loop 3 / 3) — Mod-$2^{27}$ Pruning of $(2, 6, 3, 3, 2, s_5 \ge 10)$ & the $50{,}387{,}465$ Seed Lower Bound
   (`two_six_three_three_two_ten_mod_two_pow_27_and_50387465_lower_bound`)**:
   - Along $b_0 = 55817 + 131072 r$ ($\ell = 1 + 4 r$), $Q_4 = 6110535 + 14348907 r$ and
     $P_5 = 9 Q_4 + 1 = 54994816 + 129140163 r$.
   - Proves that $1024 \mid P_5 \iff r \bmod 1024 = 384 \iff b_0 \bmod 134217728 = 50387465$,
     forcing **$50{,}387{,}465 \le b_0$** for every seed realizing $(2, 6, 3, 3, 2, s_5 \ge 10)$!
-/

namespace Mahler.SixBlockKneadingAndFiftyMillion

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

/-! ## 1. Section O7.1: Mod-131072 Classification of $(2, 6, 3, 3, 2)$ -/

/-- **Mod-131072 Classification of the 5-Block Kneading Prefix $(2, 6, 3, 3, 2)$
(`two_six_three_three_two_mod_131072_classification`, Section O7.1)**:
1. Along `n = 3 + 8 * k` (`b_0 = 6665 + 16384 * k`), `P_3 = 8 * Q_3` where `Q_3 = 216206 + 531441 * k`,
   and `Q_3 % 2 = 1 ↔ k % 2 = 1`.
2. Along `k = 1 + 2 * ℓ` (`b_0 = 23049 + 32768 * ℓ`), `Q_3 = 747647 + 1062882 * ℓ`,
   `b_4 = 3 ^ (3 - 1) * Q_3`, and `oddReturnP b_4 = 2 * (10093235 + 14348907 * ℓ)`:
   - `ℓ % 2 = 0 ↔ (2 ∣ oddReturnP b_4 ∧ ¬ (4 ∣ oddReturnP b_4))` ($s_4 = 1$, instant death),
   - `ℓ % 4 = 3 ↔ 8 ∣ oddReturnP b_4` ($s_4 \ge 3$), and
   - `ℓ % 4 = 1 ↔ (4 ∣ oddReturnP b_4 ∧ ¬ (8 ∣ oddReturnP b_4)) ↔ b_0 % 131072 = 55817` ($s_4 = 2$). -/
theorem two_six_three_three_two_mod_131072_classification (k ℓ : ℕ) :
    let Q_3_k := 216206 + 531441 * k
    let b_0 := 23049 + 32768 * ℓ
    let Q_3 := 747647 + 1062882 * ℓ
    let b_4 := 3 ^ (3 - 1) * Q_3
    let P_4 := 2 * (10093235 + 14348907 * ℓ)
    (135325 + 531441 * (3 + 8 * k) = 2 ^ 3 * Q_3_k ∧ (Q_3_k % 2 = 1 ↔ k % 2 = 1)) ∧
      (oddReturnP b_4 = P_4 ∧
        (ℓ % 2 = 0 ↔ (2 ∣ P_4 ∧ ¬ (4 ∣ P_4))) ∧
        (ℓ % 4 = 3 ↔ 8 ∣ P_4) ∧
        (ℓ % 4 = 1 ↔ (4 ∣ P_4 ∧ ¬ (8 ∣ P_4))) ∧
        (ℓ % 4 = 1 ↔ b_0 % 131072 = 55817)) := by
  intro Q_3_k b_0 Q_3 b_4 P_4
  have hP3_eq : 135325 + 531441 * (3 + 8 * k) = 2 ^ 3 * Q_3_k := by
    dsimp [Q_3_k]
    ring
  have hQ3k_split : Q_3_k = 2 * (108103 + 265720 * k) + k := by
    dsimp [Q_3_k]
    ring
  have hQ3k_odd : Q_3_k % 2 = 1 ↔ k % 2 = 1 := by
    rw [hQ3k_split]
    clear hP3_eq hQ3k_split Q_3_k b_0 Q_3 b_4 P_4
    generalize 108103 + 265720 * k = q
    omega
  have hP4_eq : oddReturnP b_4 = P_4 := by
    unfold oddReturnP
    dsimp [b_4, Q_3, P_4]
    ring
  have hP4_split : P_4 = 8 * (2523308 + 3587226 * ℓ) + 2 * (3 + 3 * ℓ) := by
    dsimp [P_4]
    ring
  have hb0_def : b_0 = 23049 + 32768 * ℓ := rfl
  refine ⟨⟨hP3_eq, hQ3k_odd⟩, ⟨hP4_eq, ?_⟩⟩
  rw [hP4_split, hb0_def]
  clear hP3_eq hQ3k_split hQ3k_odd hP4_eq hP4_split hb0_def Q_3_k b_0 Q_3 b_4 P_4
  generalize 2523308 + 3587226 * ℓ = q
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## 2. Section O7.2: Six-Block $(2, 6, 3, 3, 2, s_5)$ Slack Law & the $s_5 \le 9$ Escape Theorem -/

/-- **Six-Block $(2, 6, 3, 3, 2, s_5)$ Slack Law & Exact $s_5 \le 9$ Escape Equivalence
(`six_block_kneading_s5_slack_and_escape_iff_le_nine`, Section O7.2)**:
Suppose `s 0 = 2`, `s 1 = 6`, `s 2 = 3`, `s 3 = 3`, and `s 4 = 2`. Then:
1. `blockSteps s 5 = 16` and `renewalIntSlack s 5 = 2425`,
2. `blockSteps s 6 = 16 + s 5` and
   `renewalIntSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 131072 * (2 : ℤ) ^ (s 5)`,
3. `2 * renewalNumerator s 6 ≥ 3 ^ (blockSteps s 6) ↔ s 5 ≤ 9`, and
4. At `s 5 = 10`, `renewalIntSlack s 6 = 8976097`. -/
theorem six_block_kneading_s5_slack_and_escape_iff_le_nine {s : ℕ → ℕ}
    (hs0 : s 0 = 2) (hs1 : s 1 = 6) (hs2 : s 2 = 3) (hs3 : s 3 = 3) (hs4 : s 4 = 2) :
    blockSteps s 5 = 16 ∧
      renewalIntSlack s 5 = 2425 ∧
      blockSteps s 6 = 16 + s 5 ∧
      renewalIntSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 131072 * (2 : ℤ) ^ (s 5) ∧
      (2 * renewalNumerator s 6 ≥ 3 ^ (blockSteps s 6) ↔ s 5 ≤ 9) ∧
      (s 5 = 10 → renewalIntSlack s 6 = 8976097) := by
  have hs_run : ∀ t < 2, s (2 + t) = 3 := by
    intro t ht
    rcases t with _ | _ | t
    · exact hs2
    · exact hs3
    · omega
  have h5 := two_six_three_run_and_next_two_slack_closed_forms hs0 hs1 hs_run
  rcases h5.2.2 hs4 with ⟨hT5, h19S5⟩
  change blockSteps s 5 = 10 + 3 * 2 at hT5
  change 19 * renewalIntSlack s 5 = 9 * (27 : ℤ) ^ (2 + 1) - 2048 * (8 : ℤ) ^ 2 at h19S5
  have hS5 : renewalIntSlack s 5 = 2425 := by omega
  have hT5_eq : blockSteps s 5 = 16 := by omega
  have hT6 : blockSteps s 6 = 16 + s 5 := by
    change blockSteps s 5 + s 5 = 16 + s 5
    rw [hT5_eq]
  have hstep6 := (renewalIntSlack_step_and_cocycle s 5 0 0).2.1
  rw [hS5, hT6] at hstep6
  have hS6 : renewalIntSlack s 6 = 2425 * (3 : ℤ) ^ (s 5) - 131072 * (2 : ℤ) ^ (s 5) := by
    rw [hstep6, show 16 + s 5 + 1 = 17 + s 5 by omega, pow_add (2 : ℤ) 17 (s 5)]
    ring
  have hpow_gt : ∀ m : ℕ, 131072 * 2 ^ (m + 10) < 2425 * 3 ^ (m + 10) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        have h1 : 131072 * 2 ^ (m + 1 + 10) = 2 * (131072 * 2 ^ (m + 10)) := by
          rw [show m + 1 + 10 = (m + 10) + 1 by omega, Nat.pow_succ]; ring
        have h2 : 2425 * 3 ^ (m + 1 + 10) = 3 * (2425 * 3 ^ (m + 10)) := by
          rw [show m + 1 + 10 = (m + 10) + 1 by omega, Nat.pow_succ]; ring
        omega
  have hpow_le : ∀ n : ℕ, n ≤ 9 → (2425 * (3 : ℤ) ^ n - 131072 * (2 : ℤ) ^ n) ≤ 0 := by
    intro n hn
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · omega
  have hslack_iff :
      2 * renewalNumerator s 6 ≥ 3 ^ (blockSteps s 6) ↔ renewalIntSlack s 6 ≤ 0 := by
    unfold renewalIntSlack
    have hcast : (3 : ℤ) ^ (blockSteps s 6) = ((3 ^ (blockSteps s 6) : ℕ) : ℤ) := by norm_cast
    rw [hcast]
    omega
  refine ⟨hT5_eq, hS5, hT6, hS6, ?_, ?_⟩
  · rw [hslack_iff, hS6]
    constructor
    · intro hle
      by_contra hnot
      have hgt : 10 ≤ s 5 := by omega
      obtain ⟨m, hm⟩ : ∃ m : ℕ, s 5 = m + 10 := ⟨s 5 - 10, by omega⟩
      have hlt : (131072 : ℤ) * (2 : ℤ) ^ (s 5) < 2425 * (3 : ℤ) ^ (s 5) := by
        rw [hm]
        exact_mod_cast hpow_gt m
      linarith
    · exact hpow_le (s 5)
  · intro hs5
    rw [hS6, hs5]
    norm_num

/-! ## 3. Section O7.3: Mod-$2^{26}$ Pruning of $(2, 6, 3, 3, 2, s_5 \ge 10)$ & the $61{,}397{,}577$ Bound -/

/-- **Mod-$2^{26}$ Pruning of $(2, 6, 3, 3, 2, s_5 \ge 10)$ & the $b_0 \ge 61{,}397{,}513$ Lower Bound
(`two_six_three_three_two_ten_mod_two_pow_27_and_50387465_lower_bound`, Section O7.3)**:
Along the $(2, 6, 3, 3, 2)$ family `b_0 = 55817 + 131072 * r` (`ℓ = 1 + 4 * r`):
1. `P_4 = 2 ^ 2 * Q_4` with `Q_4 = 12221071 + 28697814 * r` and `Q_4 % 2 = 1`,
2. `b_5 = 3 ^ (2 - 1) * Q_4` has `oddReturnP b_5 = P_5` with `P_5 = 109989640 + 258280326 * r`,
3. `1024 ∣ P_5 ↔ r % 512 = 468 ↔ b_0 % 67108864 = 61397513`, and
4. Every seed `b_0 = 55817 + 131072 * r` satisfying `1024 ∣ P_5` ($s_5 \ge 10$) satisfies
   `61397513 ≤ b_0`. -/
theorem two_six_three_three_two_ten_mod_two_pow_27_and_50387465_lower_bound (r : ℕ) :
    let ℓ := 1 + 4 * r
    let b_0 := 55817 + 131072 * r
    let P_4 := 2 * (10093235 + 14348907 * ℓ)
    let Q_4 := 12221071 + 28697814 * r
    let b_5 := 3 ^ (2 - 1) * Q_4
    let P_5 := 109989640 + 258280326 * r
    P_4 = 2 ^ 2 * Q_4 ∧
      Q_4 % 2 = 1 ∧
      oddReturnP b_5 = P_5 ∧
      (1024 ∣ P_5 ↔ r % 512 = 468) ∧
      (r % 512 = 468 ↔ b_0 % 67108864 = 61397513) ∧
      (1024 ∣ P_5 → 61397513 ≤ b_0) := by
  intro ℓ b_0 P_4 Q_4 b_5 P_5
  have hP4 : P_4 = 2 ^ 2 * Q_4 := by dsimp [P_4, ℓ, Q_4]; ring
  have hQ4_odd : Q_4 % 2 = 1 := by
    have hsplit : Q_4 = 2 * (6110535 + 14348907 * r) + 1 := by dsimp [Q_4]; ring
    rw [hsplit]
    clear hP4 hsplit ℓ b_0 P_4 Q_4 b_5 P_5
    generalize 6110535 + 14348907 * r = q
    omega
  have hP5 : oddReturnP b_5 = P_5 := by
    unfold oddReturnP
    dsimp [b_5, Q_4, P_5]
    ring
  have hP5_split : P_5 = 1024 * (107411 + 252226 * r) + 2 * (388 + 451 * r) := by
    dsimp [P_5]
    ring
  have hdvd_iff : 1024 ∣ 2 * (388 + 451 * r) ↔ r % 512 = 468 := by
    constructor
    · rintro ⟨q, hq⟩
      have hdiv2 : 388 + 451 * r = 512 * q := by omega
      have hinv : 747 * (388 + 451 * r) + 468 = 512 * (567 + 658 * r) + r := by ring
      rw [hdiv2] at hinv
      clear hP4 hQ4_odd hP5 hP5_split hq hdiv2 ℓ b_0 P_4 Q_4 b_5 P_5
      generalize 567 + 658 * r = k at hinv
      omega
    · intro hr
      have hdiv : r = 512 * (r / 512) + 468 := by
        have h := (Nat.div_add_mod r 512).symm
        omega
      rw [hdiv]
      exact ⟨413 + 451 * (r / 512), by ring⟩
  have hP5_dvd : 1024 ∣ P_5 ↔ r % 512 = 468 := by
    rw [hP5_split, Nat.dvd_add_right ⟨107411 + 252226 * r, rfl⟩]
    exact hdvd_iff
  refine ⟨hP4, hQ4_odd, hP5, hP5_dvd, ?_, ?_⟩
  · dsimp only [b_0]
    clear hP4 hQ4_odd hP5 hP5_split hdvd_iff hP5_dvd ℓ b_0 P_4 Q_4 b_5 P_5
    omega
  · intro hdvd
    have hr := hP5_dvd.mp hdvd
    dsimp only [b_0]
    clear hP4 hQ4_odd hP5 hP5_split hdvd_iff hP5_dvd hdvd ℓ b_0 P_4 Q_4 b_5 P_5
    omega

end Mahler.SixBlockKneadingAndFiftyMillion
