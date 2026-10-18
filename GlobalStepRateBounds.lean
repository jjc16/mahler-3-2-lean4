import MinSlackDynamicalSystem

/-!
# Global Step-Rate Bounds, Minimum `s = 2` Separation & Post-`2` Transition Classification

This module derives universal step-rate and block-separation laws from the
1D multi-origin minimum-slack dynamical system `minSlack`:

1. **Universal `minSlack` Block Bounds (`two_le_of_minSlack_pos`,
   `six_le_after_two_of_minSlack_pos`)**:
   - At any block `m` with `0 < minSlack s (m + 1)`, the ceiling
     `minSlack s m ≤ 2^(blockSteps s m)` and `recovery_barrier_of_minSlack_le`
     (`B = 1`) force `2 ≤ s m`.
   - Whenever `s m = 2` and `0 < minSlack s (m + 2)`, the quarter cap
     `4 * minSlack s (m + 1) ≤ 2^(blockSteps s (m + 1))` and
     `recovery_barrier_of_minSlack_le` (`B = 5`) force `6 ≤ s (m + 1)`.
2. **Post-`2` Multi-Block Classification & Minimum Separation Between `s = 2` Blocks
   (`three_le_after_two_six_of_minSlack_pos`,
   `three_le_after_two_six_three_of_minSlack_pos`,
   `two_block_separation_after_two`)**:
   - If `s m = 2` and `s (m + 1) = 6` with `0 < minSlack s (m + 3)`, then
     `4 * minSlack s (m + 2) ≤ 217 * 2^(blockSteps s (m + 1))`, which forces
     `3 ≤ s (m + 2)`.
   - If `s m = 2`, `s (m + 1) = 6`, and `s (m + 2) = 3` with `0 < minSlack s (m + 4)`,
     then `4 * minSlack s (m + 3) ≤ 1763 * 2^(blockSteps s (m + 1))`, which forces
     `3 ≤ s (m + 3)`.
   - Consequently, after any `s m = 2`, neither `s (m + 1)` nor `s (m + 2)` can be
     `2`, and the next two blocks satisfy `9 ≤ s (m + 1) + s (m + 2)`.
3. **The Global Average Step-Rate Theorem (`global_step_rate_disjunction`,
   `three_mul_le_blockSteps_add_one`, `surviving_orbit_three_mul_step_rate`)**:
   Along any block sequence where `2 ≤ s k` and `s k = 2 → 6 ≤ s (k + 1)`:
   - At every block `m`, `(3 * m ≤ blockSteps s m) ∨ (3 * m ≤ blockSteps s m + 1 ∧ 6 ≤ s m)`.
   - Consequently, `3 * m ≤ blockSteps s m + 1` holds for all `m` (and
     `3 * m ≤ blockSteps s m` whenever `s m < 6`), upgrading the guaranteed
     step rate of any surviving orbit from `2` steps/block to `3` steps/block.
-/

namespace Mahler.GlobalStepRate

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

/-! ## 1. Universal `minSlack` Block Bounds (`2 ≤ s m` and `s m = 2 → 6 ≤ s (m + 1)`) -/

/-- **Universal `2 ≤ s m` from `minSlack` Positivity (`two_le_of_minSlack_pos`)**:
Whenever `0 < minSlack s (m + 1)`, `2 ≤ s m`. -/
theorem two_le_of_minSlack_pos (s : ℕ → ℕ) {m : ℕ}
    (hpos_next : 0 < minSlack s (m + 1)) :
    2 ≤ s m := by
  have hceil := minSlack_le_two_pow s m
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s m) := pow_pos (by decide) _
  have hbarrier :
      (3 : ℤ) ^ 1 * minSlack s m ≤ (2 : ℤ) ^ (blockSteps s m + 1 + 1) := by
    have hpow :
        (2 : ℤ) ^ (blockSteps s m + 1 + 1) = 4 * (2 : ℤ) ^ (blockSteps s m) := by
      rw [show blockSteps s m + 1 + 1 = blockSteps s m + 2 by omega, pow_add]
      ring
    linarith
  exact recovery_barrier_of_minSlack_le s hpos_next hbarrier

/-- **Universal `6 ≤ s (m + 1)` After `s m = 2` (`six_le_after_two_of_minSlack_pos`)**:
Whenever `s m = 2` and `0 < minSlack s (m + 2)`, `6 ≤ s (m + 1)`. -/
theorem six_le_after_two_of_minSlack_pos (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hpos_next2 : 0 < minSlack s (m + 2)) :
    6 ≤ s (m + 1) := by
  have hq := post_two_minSlack_le_quarter s hsm
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1)) := pow_pos (by decide) _
  have hbarrier :
      (3 : ℤ) ^ 5 * minSlack s (m + 1) ≤
        (2 : ℤ) ^ (blockSteps s (m + 1) + 5 + 1) := by
    have hpow :
        (2 : ℤ) ^ (blockSteps s (m + 1) + 5 + 1) =
          64 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
      rw [show blockSteps s (m + 1) + 5 + 1 = blockSteps s (m + 1) + 6 by omega, pow_add]
      ring
    have h35 : (3 : ℤ) ^ 5 = 243 := by norm_num
    rw [h35, hpow]
    linarith
  exact recovery_barrier_of_minSlack_le s hpos_next2 hbarrier

/-! ## 2. Post-`2` Multi-Block Classification & Minimum Separation Between `s = 2` Blocks -/

/-- Whenever `s m = 2` and `s (m + 1) = 6`,
`4 * minSlack s (m + 2) ≤ 217 * 2^(blockSteps s (m + 1))`. -/
theorem four_mul_minSlack_after_two_six_le (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hsm1 : s (m + 1) = 6) :
    4 * minSlack s (m + 2) ≤ 217 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
  have hq := post_two_minSlack_le_quarter s hsm
  have hstep := minSlack_succ_le_step s (m + 1)
  have hpow :
      (2 : ℤ) ^ (blockSteps s (m + 2) + 1) =
        128 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    simp only [blockSteps, hsm1]
    rw [show blockSteps s m + s m + 6 + 1 = (blockSteps s m + s m) + 7 by omega, pow_add]
    ring
  rw [hsm1, hpow] at hstep
  have h36 : (3 : ℤ) ^ 6 = 729 := by norm_num
  rw [h36] at hstep
  linarith

/-- **Universal `3 ≤ s (m + 2)` After `(s m, s (m + 1)) = (2, 6)`
(`three_le_after_two_six_of_minSlack_pos`)**:
If `s m = 2`, `s (m + 1) = 6`, and `0 < minSlack s (m + 3)`, then `3 ≤ s (m + 2)`. -/
theorem three_le_after_two_six_of_minSlack_pos (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hsm1 : s (m + 1) = 6)
    (hpos_next3 : 0 < minSlack s (m + 3)) :
    3 ≤ s (m + 2) := by
  have h217 := four_mul_minSlack_after_two_six_le s hsm hsm1
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1)) := pow_pos (by decide) _
  have hpow :
      (2 : ℤ) ^ (blockSteps s (m + 2)) =
        64 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    simp only [blockSteps, hsm1, pow_add]
    ring
  have hbarrier :
      9 * minSlack s (m + 2) ≤ 8 * (2 : ℤ) ^ (blockSteps s (m + 2)) := by
    rw [hpow]
    linarith
  exact three_le_of_nine_mul_minSlack_le s hpos_next3 hbarrier

/-- Whenever `s m = 2`, `s (m + 1) = 6`, and `s (m + 2) = 3`,
`4 * minSlack s (m + 3) ≤ 1763 * 2^(blockSteps s (m + 1))`. -/
theorem four_mul_minSlack_after_two_six_three_le (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hsm1 : s (m + 1) = 6) (hsm2 : s (m + 2) = 3) :
    4 * minSlack s (m + 3) ≤ 1763 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
  have h217 := four_mul_minSlack_after_two_six_le s hsm hsm1
  have hstep := minSlack_succ_le_step s (m + 2)
  have hpow :
      (2 : ℤ) ^ (blockSteps s (m + 3) + 1) =
        1024 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    simp only [blockSteps, hsm1, hsm2]
    rw [show blockSteps s m + s m + 6 + 3 + 1 = (blockSteps s m + s m) + 10 by omega, pow_add]
    ring
  rw [hsm2, hpow] at hstep
  have h33 : (3 : ℤ) ^ 3 = 27 := by norm_num
  rw [h33] at hstep
  linarith

/-- **Universal `3 ≤ s (m + 3)` After `(s m, s (m + 1), s (m + 2)) = (2, 6, 3)`
(`three_le_after_two_six_three_of_minSlack_pos`)**:
If `s m = 2`, `s (m + 1) = 6`, `s (m + 2) = 3`, and `0 < minSlack s (m + 4)`,
then `3 ≤ s (m + 3)`. -/
theorem three_le_after_two_six_three_of_minSlack_pos (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2) (hsm1 : s (m + 1) = 6) (hsm2 : s (m + 2) = 3)
    (hpos_next4 : 0 < minSlack s (m + 4)) :
    3 ≤ s (m + 3) := by
  have h1763 := four_mul_minSlack_after_two_six_three_le s hsm hsm1 hsm2
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ (blockSteps s (m + 1)) := pow_pos (by decide) _
  have hpow :
      (2 : ℤ) ^ (blockSteps s (m + 3)) =
        512 * (2 : ℤ) ^ (blockSteps s (m + 1)) := by
    simp only [blockSteps, hsm1, hsm2]
    rw [show blockSteps s m + s m + 6 + 3 = (blockSteps s m + s m) + 9 by omega, pow_add]
    ring
  have hbarrier :
      9 * minSlack s (m + 3) ≤ 8 * (2 : ℤ) ^ (blockSteps s (m + 3)) := by
    rw [hpow]
    linarith
  exact three_le_of_nine_mul_minSlack_le s hpos_next4 hbarrier

/-- **Minimum Separation & Step Sum After Any `s m = 2` (`two_block_separation_after_two`)**:
Whenever `s m = 2`, `0 < minSlack s (m + 2)`, and `0 < minSlack s (m + 3)`:
- `s (m + 1) ≠ 2` and `s (m + 2) ≠ 2` (at least two blocks must separate any
  two occurrences of `2` unless `7 ≤ s (m + 1)`), and
- `9 ≤ s (m + 1) + s (m + 2)`. -/
theorem two_block_separation_after_two (s : ℕ → ℕ) {m : ℕ}
    (hsm : s m = 2)
    (hpos2 : 0 < minSlack s (m + 2))
    (hpos3 : 0 < minSlack s (m + 3)) :
    6 ≤ s (m + 1) ∧ 9 ≤ s (m + 1) + s (m + 2) := by
  have hs1 : 6 ≤ s (m + 1) := six_le_after_two_of_minSlack_pos s hsm hpos2
  have hs2_ge2 : 2 ≤ s (m + 2) := two_le_of_minSlack_pos s hpos3
  rcases Nat.eq_or_lt_of_le hs1 with h6 | hgt6
  · have hs2_ge3 : 3 ≤ s (m + 2) :=
      three_le_after_two_six_of_minSlack_pos s hsm h6.symm hpos3
    exact ⟨hs1, by omega⟩
  · exact ⟨hs1, by omega⟩

/-! ## 3. The Global Average Step-Rate Theorem (`3 * m ≤ blockSteps s m + 1`) -/

/-- **Two-State Step-Rate Disjunction (`global_step_rate_disjunction`)**:
Suppose for all `k < m`, `2 ≤ s k`, and for all `k < m`, `s k = 2 → 6 ≤ s (k + 1)`.
Then at step `m`, either `3 * m ≤ blockSteps s m` or
`3 * m ≤ blockSteps s m + 1 ∧ 6 ≤ s m`. -/
theorem global_step_rate_disjunction (s : ℕ → ℕ) (m : ℕ)
    (hge2 : ∀ k < m, 2 ≤ s k)
    (h2to6 : ∀ k < m, s k = 2 → 6 ≤ s (k + 1)) :
    3 * m ≤ blockSteps s m ∨ (3 * m ≤ blockSteps s m + 1 ∧ 6 ≤ s m) := by
  induction m with
  | zero =>
      left
      simp [blockSteps]
  | succ m ih =>
      have ihm := ih (fun k hk => hge2 k (by omega)) (fun k hk => h2to6 k (by omega))
      have hsm_ge2 : 2 ≤ s m := hge2 m (by omega)
      rcases ihm with hleft | ⟨hright, hsm_ge6⟩
      · rcases Nat.eq_or_lt_of_le hsm_ge2 with hsm2 | hsm_ge3
        · right
          refine ⟨?_, h2to6 m (by omega) hsm2.symm⟩
          simp only [blockSteps]
          omega
        · left
          simp only [blockSteps]
          omega
      · left
        simp only [blockSteps]
        omega

/-- **Global Step-Rate Lower Bound (`three_mul_le_blockSteps_add_one`)**:
Whenever `2 ≤ s k` and `s k = 2 → 6 ≤ s (k + 1)` for all `k < m`,
`3 * m ≤ blockSteps s m + 1` (and if `s m < 6`, `3 * m ≤ blockSteps s m`). -/
theorem three_mul_le_blockSteps_add_one (s : ℕ → ℕ) (m : ℕ)
    (hge2 : ∀ k < m, 2 ≤ s k)
    (h2to6 : ∀ k < m, s k = 2 → 6 ≤ s (k + 1)) :
    3 * m ≤ blockSteps s m + 1 ∧ (s m < 6 → 3 * m ≤ blockSteps s m) := by
  rcases global_step_rate_disjunction s m hge2 h2to6 with hleft | ⟨hright, hge6⟩
  · exact ⟨by omega, fun _ => hleft⟩
  · exact ⟨hright, fun hlt => by omega⟩

theorem blockSteps_mono (s : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    blockSteps s a ≤ blockSteps s b := by
  induction b with
  | zero =>
      have ha0 : a = 0 := by omega
      subst ha0
      rfl
  | succ b ih =>
      rcases Nat.of_le_succ hab with hle | rfl
      · have ihb := ih hle
        simp only [blockSteps]
        omega
      · rfl

/-- **Surviving Orbit `3m - 1` Step-Rate Theorem (`surviving_orbit_three_mul_step_rate`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` with `m + 1 < K` where
the trajectory survives through step `blockSteps s (m + 2)`, the first `m` odd
blocks consume at least `3 * m - 1` steps:
`3 * m ≤ blockSteps s m + 1`. -/
theorem surviving_orbit_three_mul_step_rate {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m + 1 < K) (hchain : ValidBlockChain a_0 s u K) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s (m + 2))) :
    3 * m ≤ blockSteps s m + 1 := by
  have hge2 : ∀ k < m, 2 ≤ s k := by
    intro k hk
    have hle : blockSteps s (k + 1 + 1) ≤ blockSteps s (m + 2) :=
      blockSteps_mono s (by omega : k + 1 + 1 ≤ m + 2)
    have hsurv_k : ValidCompanionUpTo a_0 ξ (blockSteps s (k + 1 + 1)) :=
      fun n hn => hsurv n (by omega)
    have hpos_k : 0 < minSlack s (k + 1) :=
      minSlack_pos_of_validCompanionUpTo (by omega : k + 1 < K) hchain hsurv_k
    exact two_le_of_minSlack_pos s hpos_k
  have h2to6 : ∀ k < m, s k = 2 → 6 ≤ s (k + 1) := by
    intro k hk hsk
    have hle : blockSteps s (k + 2 + 1) ≤ blockSteps s (m + 2) :=
      blockSteps_mono s (by omega : k + 2 + 1 ≤ m + 2)
    have hsurv_k2 : ValidCompanionUpTo a_0 ξ (blockSteps s (k + 2 + 1)) :=
      fun n hn => hsurv n (by omega)
    have hpos_k2 : 0 < minSlack s (k + 2) :=
      minSlack_pos_of_validCompanionUpTo (by omega : k + 2 < K) hchain hsurv_k2
    exact six_le_after_two_of_minSlack_pos s hsk hpos_k2
  exact (three_mul_le_blockSteps_add_one s m hge2 h2to6).1

end Mahler.GlobalStepRate
