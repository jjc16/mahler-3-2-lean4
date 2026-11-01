import RecoveryCascadeClosedFormsAndKneadingWords

/-!
# Exact 2-Adic Symbolic Pruning Tree for $(2, 6, 3, \dots)$ & the $b_0 \equiv 6665 \pmod{16384}$ Lower Bound

This module formalizes **Outer Loop 6 / 10 (Part X, Sections O6.1–O6.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O6.1 (Inner Loop 1 / 3) — Exact Mod-256 and Mod-512 Hensel Classification of $(s_0 = 2, s_1 = 6)$
   (`two_six_prefix_mod_256_and_512_classification`)**:
   - For any seed $b_0 \in \mathbb{N}$ with $3 b_0 + 1 = 4 Q_0$ and $P_1 = 9 Q_0 + 1$:
     - $(Q_0 \bmod 2 = 1 \land 64 \mid P_1) \iff b_0 \bmod 256 = 9$ ($Q_0 \bmod 64 = 7$),
     - $(Q_0 \bmod 2 = 1 \land 64 \mid P_1 \land \neg(128 \mid P_1)) \iff b_0 \bmod 512 = 9$, and
     - $(Q_0 \bmod 2 = 1 \land 128 \mid P_1) \iff b_0 \bmod 512 = 265$.

2. **Section O6.2 (Inner Loop 2 / 3) — Mod-2048 Pruning of $(2, 6, s_2 \ge 3)$ (`b_0 ≡ 521 (mod 2048)`)
   (`two_six_lift_P2_parameterization_and_mod_2048_pruning`)**:
   - Along the exact $(2, 6)$ family $b_0 = 9 + 512 m$:
     - $3 b_0 + 1 = 4(7 + 384 m)$ ($s_0 = 2, Q_0 = 7 + 384 m$),
     - $P_1 = 9 Q_0 + 1 = 64(1 + 54 m)$ ($s_1 = 6, Q_1 = 1 + 54 m$),
     - $P_2 = 729 Q_1 + 1 = 2(365 + 19683 m)$.
   - Consequently:
     - $m \bmod 2 = 0 \implies P_2 \bmod 4 = 2$ ($s_2 = 1$, instant death),
     - $m \bmod 4 = 3 \implies P_2 \bmod 8 = 4$ ($s_2 = 2$, which escapes by `three_block_two_six_s2_escape_iff_s2_le_two`), and
     - $8 \mid P_2$ ($s_2 \ge 3$) $\iff m \bmod 4 = 1 \iff b_0 \bmod 2048 = 521$!

3. **Section O6.3 (Inner Loop 3 / 3) — Mod-16384 Pruning of $(2, 6, 3, s_3 \ge 3)$ (`b_0 ≡ 6665 (mod 16384)`)
   (`two_six_three_lift_P3_parameterization_and_6665_lower_bound`)**:
   - Along the surviving family $b_0 = 521 + 2048 n$ ($m = 4 n + 1$):
     - $P_2 = 8(5012 + 19683 n)$ ($Q_2 = 5012 + 19683 n$),
     - $s_2 = 3$ (`Q_2 % 2 = 1`) $\iff n \bmod 2 = 1$, while $n \bmod 2 = 0 \implies 16 \mid P_2$ ($s_2 \ge 4$),
     - $P_3 = 27 Q_2 + 1 = 135325 + 531441 n$, and
     - $(Q_2 \bmod 2 = 1 \land 8 \mid P_3) \iff n \bmod 8 = 3 \iff b_0 \bmod 16384 = 6665$,
       forcing $6665 \le b_0$ for every seed realizing $(2, 6, 3, s_3 \ge 3)$!
-/

namespace Mahler.TwoAdicRecoveryPruningTree

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

/-! ## 1. Section O6.1: Exact Mod-256 and Mod-512 Hensel Classification of $(s_0 = 2, s_1 = 6)$ -/

/-- **Mod-256 and Mod-512 Classification of $(s_0 = 2, s_1 = 6)$ vs. $(s_0 = 2, s_1 \ge 7)$
(`two_six_prefix_mod_256_and_512_classification`, Section O6.1)**:
For any seed `b_0 : ℕ`, let `P_0 = 3 * b_0 + 1`. Then:
1. `(4 ∣ P_0 ∧ ¬ (8 ∣ P_0) ∧ 64 ∣ (9 * (P_0 / 4) + 1)) ↔ b_0 % 256 = 9`,
2. `(4 ∣ P_0 ∧ ¬ (8 ∣ P_0) ∧ 64 ∣ (9 * (P_0 / 4) + 1) ∧ ¬ (128 ∣ (9 * (P_0 / 4) + 1))) ↔ b_0 % 512 = 9`, and
3. `(4 ∣ P_0 ∧ ¬ (8 ∣ P_0) ∧ 128 ∣ (9 * (P_0 / 4) + 1)) ↔ b_0 % 512 = 265`. -/
theorem two_six_prefix_mod_256_and_512_classification (b_0 : ℕ) :
    let P_0 := 3 * b_0 + 1
    let P_1 := 9 * (P_0 / 4) + 1
    ((4 ∣ P_0 ∧ ¬ (8 ∣ P_0) ∧ 64 ∣ P_1) ↔ b_0 % 256 = 9) ∧
      ((4 ∣ P_0 ∧ ¬ (8 ∣ P_0) ∧ 64 ∣ P_1 ∧ ¬ (128 ∣ P_1)) ↔ b_0 % 512 = 9) ∧
      ((4 ∣ P_0 ∧ ¬ (8 ∣ P_0) ∧ 128 ∣ P_1) ↔ b_0 % 512 = 265) := by
  intro P_0 P_1
  dsimp [P_0, P_1]
  refine ⟨by omega, by omega, by omega⟩

/-! ## 2. Section O6.2: Mod-2048 Pruning of $(2, 6, s_2 \ge 3)$ (`b_0 ≡ 521 (mod 2048)`) -/

/-- **Exact Parameterization & Mod-2048 Pruning of $(2, 6, s_2)$ Lifts
(`two_six_lift_P2_parameterization_and_mod_2048_pruning`, Section O6.2)**:
For every `m : ℕ`, let `b_0 = 9 + 512 * m`, `Q_0 = 7 + 384 * m`, `Q_1 = 1 + 54 * m`, and
`P_2 = 2 * (365 + 19683 * m)`. Then:
1. `3 * b_0 + 1 = 2 ^ 2 * Q_0`, `Q_0 % 2 = 1`, `orbit b_0 2 = 3 * Q_0`,
2. `3 * (3 * Q_0) + 1 = 2 ^ 6 * Q_1`, `Q_1 % 2 = 1`, `orbit (3 * Q_0) 6 = 243 * Q_1`,
3. `oddReturnP (243 * Q_1) = P_2`, and
4. Exact 4-way classification of `m % 4`:
   - `m % 2 = 0 ↔ (2 ∣ P_2 ∧ ¬ (4 ∣ P_2))` ($s_2 = 1$, instant death),
   - `m % 4 = 3 ↔ (4 ∣ P_2 ∧ ¬ (8 ∣ P_2))` ($s_2 = 2$, $(2, 6, 2)$ escape),
   - `8 ∣ P_2 ↔ m % 4 = 1 ↔ b_0 % 2048 = 521` ($s_2 \ge 3$, only surviving class!). -/
theorem two_six_lift_P2_parameterization_and_mod_2048_pruning (m : ℕ) :
    let b_0 := 9 + 512 * m
    let Q_0 := 7 + 384 * m
    let b_1 := 3 ^ (2 - 1) * Q_0
    let Q_1 := 1 + 54 * m
    let b_2 := 3 ^ (6 - 1) * Q_1
    let P_2 := 2 * (365 + 19683 * m)
    (3 * b_0 + 1 = 2 ^ 2 * Q_0 ∧ Q_0 % 2 = 1 ∧ orbit b_0 2 = b_1) ∧
      (3 * b_1 + 1 = 2 ^ 6 * Q_1 ∧ Q_1 % 2 = 1 ∧ orbit b_1 6 = b_2) ∧
      oddReturnP b_2 = P_2 ∧
      ((m % 2 = 0 ↔ (2 ∣ P_2 ∧ ¬ (4 ∣ P_2))) ∧
        (m % 4 = 3 ↔ (4 ∣ P_2 ∧ ¬ (8 ∣ P_2))) ∧
        (8 ∣ P_2 ↔ m % 4 = 1) ∧
        (m % 4 = 1 ↔ b_0 % 2048 = 521)) := by
  intro b_0 Q_0 b_1 Q_1 b_2 P_2
  have hdecomp0 : 3 * b_0 + 1 = 2 ^ 2 * Q_0 := by dsimp [b_0, Q_0]; ring
  have hQ0_odd : Q_0 % 2 = 1 := by dsimp [Q_0]; omega
  have horb0 : orbit b_0 2 = b_1 :=
    orbit_odd_block_return (by decide : 1 ≤ 2) hdecomp0
  have hdecomp1 : 3 * b_1 + 1 = 2 ^ 6 * Q_1 := by dsimp [b_1, Q_0, Q_1]; ring
  have hQ1_odd : Q_1 % 2 = 1 := by dsimp [Q_1]; omega
  have horb1 : orbit b_1 6 = b_2 :=
    orbit_odd_block_return (by decide : 1 ≤ 6) hdecomp1
  have hP2 : oddReturnP b_2 = P_2 := by
    unfold oddReturnP
    dsimp [b_2, Q_1, P_2]
    ring
  refine ⟨⟨hdecomp0, hQ0_odd, horb0⟩, ⟨hdecomp1, hQ1_odd, horb1⟩, hP2, ?_⟩
  clear horb0 horb1 hP2 hdecomp0 hdecomp1
  have hP2_split : P_2 = 8 * (91 + 4920 * m) + 2 * (1 + 3 * m) := by dsimp [P_2]; ring
  have hb0_def : b_0 = 9 + 512 * m := rfl
  rw [hP2_split, hb0_def]
  clear hP2_split hb0_def hQ0_odd hQ1_odd b_0 b_1 b_2 Q_0 Q_1 P_2
  generalize 91 + 4920 * m = q
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## 3. Section O6.3: Mod-16384 Pruning of $(2, 6, 3, s_3 \ge 3)$ & the $6665$ Lower Bound -/

/-- **Mod-16384 Pruning of $(2, 6, 3, s_3 \ge 3)$ & the $b_0 \ge 6665$ Lower Bound
(`two_six_three_lift_P3_parameterization_and_6665_lower_bound`, Section O6.3)**:
For every `n : ℕ`, let `b_0 = 521 + 2048 * n` (`m = 1 + 4 * n`), `Q_2 = 5012 + 19683 * n`,
`b_3 = 9 * Q_2`, and `P_3 = 135325 + 531441 * n`. Then:
1. `P_2 = 2 ^ 3 * Q_2`,
2. `Q_2 % 2 = 1 ↔ n % 2 = 1` (while `n % 2 = 0 ↔ 16 ∣ P_2`, i.e. $s_2 \ge 4$),
3. When `n % 2 = 1`, `orbit (243 * (1 + 54 * (1 + 4 * n))) 3 = b_3` and `oddReturnP b_3 = P_3`,
4. `(Q_2 % 2 = 1 ∧ 8 ∣ P_3) ↔ n % 8 = 3 ↔ b_0 % 16384 = 6665`, and
5. Every seed `b_0 = 521 + 2048 * n` satisfying `Q_2 % 2 = 1 ∧ 8 ∣ P_3` satisfies `6665 ≤ b_0`. -/
theorem two_six_three_lift_P3_parameterization_and_6665_lower_bound (n : ℕ) :
    let m := 1 + 4 * n
    let b_0 := 521 + 2048 * n
    let b_2 := 3 ^ (6 - 1) * (1 + 54 * m)
    let Q_2 := 5012 + 19683 * n
    let b_3 := 3 ^ (3 - 1) * Q_2
    let P_3 := 135325 + 531441 * n
    oddReturnP b_2 = 2 ^ 3 * Q_2 ∧
      (Q_2 % 2 = 1 ↔ n % 2 = 1) ∧
      orbit b_2 3 = b_3 ∧
      oddReturnP b_3 = P_3 ∧
      ((Q_2 % 2 = 1 ∧ 8 ∣ P_3) ↔ n % 8 = 3) ∧
      (n % 8 = 3 ↔ b_0 % 16384 = 6665) ∧
      (Q_2 % 2 = 1 ∧ 8 ∣ P_3 → 6665 ≤ b_0) := by
  intro m b_0 b_2 Q_2 b_3 P_3
  have hdecomp2 : 3 * b_2 + 1 = 2 ^ 3 * Q_2 := by
    dsimp [b_2, m, Q_2]
    ring
  have horb2 : orbit b_2 3 = b_3 :=
    orbit_odd_block_return (by decide : 1 ≤ 3) hdecomp2
  have hP3 : oddReturnP b_3 = P_3 := by
    unfold oddReturnP
    dsimp [b_3, Q_2, P_3]
    ring
  have hQ2_split : Q_2 = 2 * (2506 + 9841 * n) + n := by dsimp [Q_2]; ring
  have hP3_split : P_3 = 8 * (16915 + 66430 * n) + (5 + n) := by dsimp [P_3]; ring
  have hb0_def : b_0 = 521 + 2048 * n := rfl
  refine ⟨hdecomp2, ?_, horb2, hP3, ?_, ?_, ?_⟩
  · clear horb2 hP3 hdecomp2; rw [hQ2_split]; generalize 2506 + 9841 * n = q; omega
  · clear horb2 hP3 hdecomp2; rw [hQ2_split, hP3_split]; generalize 2506 + 9841 * n = q1; generalize 16915 + 66430 * n = q2; omega
  · clear horb2 hP3 hdecomp2; rw [hb0_def]; omega
  · clear horb2 hP3 hdecomp2; rw [hQ2_split, hP3_split, hb0_def]; generalize 2506 + 9841 * n = q1; generalize 16915 + 66430 * n = q2; omega

end Mahler.TwoAdicRecoveryPruningTree
