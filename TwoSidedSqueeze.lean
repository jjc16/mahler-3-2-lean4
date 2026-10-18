import ZeroLiftCoasting

/-!
# Two-Sided Exponential Squeezes on Intermediate Block Runs

This module formalizes **Squeeze 1** (the Archimedean Slack Eigenvalue Squeeze)
and **Squeeze 2** (the Coupled 2-adic + Half-Corridor Squeeze at any
intermediate return `T`), covering both regimes of the slack deficiency:

1. **Squeeze 1 — The Archimedean Slack Eigenvalue Identity & Deficiency Squeeze
   (`slackDeficiency_step`, `slackDeficiency_chain`,
   `archimedean_deficiency_squeeze`)**:
   Define `slackDeficiency s c k : ℤ := 2^(c + blockSteps s k + 1) - (3^c - 2^c) * integerSlack s k`.
   - Across any step with `s k = c`, `slackDeficiency` multiplies by `3^c`:
     `slackDeficiency s c (k + 1) = 3^c * slackDeficiency s c k`.
   - Across `m` consecutive steps of length `c`,
     `3^(c * m) * slackDeficiency s c k + (3^c - 2^c) * integerSlack s (k + m) =
       2^(c * m + c + blockSteps s k + 1)`.
   - Consequently, whenever `0 < integerSlack s (k + m)` and `1 ≤ c`,
     `3^(c * m) * slackDeficiency s c k < 2^(c * m + c + blockSteps s k + 1)`.
     In the sub-critical regime (`1 ≤ slackDeficiency s c k`), `3^(c * m)`
     collides with `2^(c * m) * 2^(c + blockSteps s k + 1)` independently of `a_0`.
2. **Squeeze 2 — The Coupled 2-adic + Half-Corridor Squeeze
   (`coupled_intermediate_repeat_squeeze`, `coasting_intermediate_repeat_squeeze`)**:
   Combining `odd_block_repeat_bound` at return `T` (`2^(c * m) ≤ (3^c - 2^c) * orbit a_0 T + 3^(c - 1)`)
   with `surviving_orbit_half_corridor` (`2^(T + 1) * orbit a_0 T < 3^T * (2 * a_0 + 1)`)
   eliminates the intermediate state `orbit a_0 T`:
   `2^(c * m + T + 1) < (3^c - 2^c) * 3^T * (2 * a_0 + 1) + 2^(T + 1) * 3^(c - 1)`.
   In the coasting regime (`a_0 < 2^W` and `W ≤ T`), canceling `2^(W + 1)` yields
   the `a_0`-free bound:
   `2^(c * m + (T - W)) < (3^c - 2^c) * 3^T + 2^(T - W) * 3^(c - 1)`.
-/

namespace Mahler.TwoSidedSqueeze

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

/-! ## 1. Squeeze 1: The Archimedean Slack Eigenvalue Identity & Deficiency Squeeze -/

/-- The slack deficiency `D_k(c) = 2^(c + blockSteps s k + 1) - (3^c - 2^c) * integerSlack s k`. -/
def slackDeficiency (s : ℕ → ℕ) (c k : ℕ) : ℤ :=
  (2 : ℤ) ^ (c + blockSteps s k + 1) -
    ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * integerSlack s k

/-- **One-Step Eigenvalue Identity (`slackDeficiency_step`)**:
When `s k = c`, `slackDeficiency s c (k + 1) = 3^c * slackDeficiency s c k`. -/
theorem slackDeficiency_step (s : ℕ → ℕ) (c k : ℕ) (hsk : s k = c) :
    slackDeficiency s c (k + 1) = (3 : ℤ) ^ c * slackDeficiency s c k := by
  unfold slackDeficiency
  rw [integerSlack_succ]
  have hsteps1 :
      c + blockSteps s (k + 1) + 1 = c + (c + blockSteps s k + 1) := by
    simp only [blockSteps, hsk]
    omega
  have hsteps2 :
      blockSteps s (k + 1) + 1 = c + blockSteps s k + 1 := by
    simp only [blockSteps, hsk]
    omega
  rw [hsteps1, hsteps2, hsk, pow_add (2 : ℤ) c (c + blockSteps s k + 1)]
  ring

theorem blockSteps_const_run (s : ℕ → ℕ) (c k m : ℕ)
    (hrun : ∀ i < m, s (k + i) = c) :
    blockSteps s (k + m) = blockSteps s k + c * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ihm := ih (fun i hi => hrun i (by omega))
      have hm : s (k + m) = c := hrun m (by omega)
      calc
        blockSteps s (k + (m + 1)) = blockSteps s ((k + m) + 1) := by
          rw [Nat.add_assoc]
        _ = blockSteps s (k + m) + s (k + m) := rfl
        _ = (blockSteps s k + c * m) + c := by rw [ihm, hm]
        _ = blockSteps s k + c * (m + 1) := by ring

/-- **Iterated `m`-Step Eigenvalue Identity (`slackDeficiency_chain`)**:
Across `m` consecutive blocks of length `c` starting at `k`,
`slackDeficiency s c (k + m) = 3^(c * m) * slackDeficiency s c k`. -/
theorem slackDeficiency_chain (s : ℕ → ℕ) (c k m : ℕ)
    (hrun : ∀ i < m, s (k + i) = c) :
    slackDeficiency s c (k + m) =
      (3 : ℤ) ^ (c * m) * slackDeficiency s c k := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ihm := ih (fun i hi => hrun i (by omega))
      have hm : s (k + m) = c := hrun m (by omega)
      have hstep := slackDeficiency_step s c (k + m) hm
      rw [← Nat.add_assoc, hstep, ihm, Nat.mul_succ, pow_add]
      ring

/-- **Exact Conservation Equation for `m` Blocks of Length `c`
(`archimedean_deficiency_conservation`)**:
`3^(c * m) * slackDeficiency s c k + (3^c - 2^c) * integerSlack s (k + m) =
  2^(c * m + c + blockSteps s k + 1)`. -/
theorem archimedean_deficiency_conservation (s : ℕ → ℕ) (c k m : ℕ)
    (hrun : ∀ i < m, s (k + i) = c) :
    (3 : ℤ) ^ (c * m) * slackDeficiency s c k +
        ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * integerSlack s (k + m) =
      (2 : ℤ) ^ (c * m + c + blockSteps s k + 1) := by
  rw [← slackDeficiency_chain s c k m hrun]
  unfold slackDeficiency
  have hsteps :
      c + blockSteps s (k + m) + 1 = c * m + c + blockSteps s k + 1 := by
    rw [blockSteps_const_run s c k m hrun]
    omega
  rw [hsteps]
  ring

/-- **Squeeze 1 — The Archimedean Deficiency Squeeze (`archimedean_deficiency_squeeze`)**:
If `1 ≤ c`, `s (k + i) = c` for all `i < m`, and `0 < integerSlack s (k + m)`,
then `3^(c * m) * slackDeficiency s c k < 2^(c * m + c + blockSteps s k + 1)`. -/
theorem archimedean_deficiency_squeeze (s : ℕ → ℕ) {c k m : ℕ}
    (hc : 1 ≤ c) (hrun : ∀ i < m, s (k + i) = c)
    (hpos : 0 < integerSlack s (k + m)) :
    (3 : ℤ) ^ (c * m) * slackDeficiency s c k <
      (2 : ℤ) ^ (c * m + c + blockSteps s k + 1) := by
  have hcons := archimedean_deficiency_conservation s c k m hrun
  have h2lt3 : (2 : ℤ) ^ c < (3 : ℤ) ^ c := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_pos : 0 < ((3 : ℤ) ^ c - (2 : ℤ) ^ c) * integerSlack s (k + m) :=
    mul_pos (by linarith) hpos
  linarith

/-! ## 2. Squeeze 2: Coupled 2-adic + Half-Corridor Squeeze at Intermediate Return `T` -/

/-- **Squeeze 2 — Coupled 2-adic + Half-Corridor Squeeze (`coupled_intermediate_repeat_squeeze`)**:
Suppose `ValidCompanionUpTo a_0 ξ T` holds, and starting from `b 0 = orbit a_0 T`,
the trajectory undergoes `m` consecutive odd-to-odd blocks of length `c ≥ 1`.
Eliminating `orbit a_0 T` between `odd_block_repeat_bound` and
`surviving_orbit_half_corridor` yields:
`2^(c * m + T + 1) < (3^c - 2^c) * 3^T * (2 * a_0 + 1) + 2^(T + 1) * 3^(c - 1)`. -/
theorem coupled_intermediate_repeat_squeeze {a_0 T c m : ℕ} (hc : 1 ≤ c)
    (b u' : ℕ → ℕ) (hb0 : b 0 = orbit a_0 T)
    (hstep : ∀ i < m, 3 * b i + 1 = 2 ^ c * u' i ∧ b (i + 1) = orbit (b i) c)
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ T) :
    2 ^ (c * m + T + 1) <
      (3 ^ c - 2 ^ c) * 3 ^ T * (2 * a_0 + 1) + 2 ^ (T + 1) * 3 ^ (c - 1) := by
  have hrep := (odd_block_repeat_bound hc b u' m hstep).2
  rw [hb0] at hrep
  have hcor := (surviving_orbit_half_corridor hsurv).2
  have h2lt3 : 2 ^ c < 3 ^ c :=
    Nat.pow_lt_pow_left (by decide : 2 < 3) (by omega : c ≠ 0)
  have hdiff_pos : 0 < 3 ^ c - 2 ^ c := by omega
  have hmul1 :
      2 ^ (T + 1) * 2 ^ (c * m) ≤
        2 ^ (T + 1) * ((3 ^ c - 2 ^ c) * orbit a_0 T + 3 ^ (c - 1)) :=
    Nat.mul_le_mul_left (2 ^ (T + 1)) hrep
  have hmul2 :
      (3 ^ c - 2 ^ c) * (2 ^ (T + 1) * orbit a_0 T) <
        (3 ^ c - 2 ^ c) * (3 ^ T * (2 * a_0 + 1)) :=
    Nat.mul_lt_mul_of_pos_left hcor hdiff_pos
  calc
    2 ^ (c * m + T + 1) = 2 ^ (T + 1) * 2 ^ (c * m) := by
      rw [show c * m + T + 1 = (T + 1) + c * m by omega, Nat.pow_add]
    _ ≤ 2 ^ (T + 1) * ((3 ^ c - 2 ^ c) * orbit a_0 T + 3 ^ (c - 1)) := hmul1
    _ = (3 ^ c - 2 ^ c) * (2 ^ (T + 1) * orbit a_0 T) +
          2 ^ (T + 1) * 3 ^ (c - 1) := by ring
    _ < (3 ^ c - 2 ^ c) * (3 ^ T * (2 * a_0 + 1)) +
          2 ^ (T + 1) * 3 ^ (c - 1) :=
          Nat.add_lt_add_right hmul2 _
    _ = (3 ^ c - 2 ^ c) * 3 ^ T * (2 * a_0 + 1) +
          2 ^ (T + 1) * 3 ^ (c - 1) := by ring

/-- **Coasting Specialization of Squeeze 2 (`coasting_intermediate_repeat_squeeze`)**:
When `a_0 < 2^W` and `W ≤ T`, canceling `2^(W + 1)` from
`coupled_intermediate_repeat_squeeze` eliminates `a_0` completely:
`2^(c * m + (T - W)) < (3^c - 2^c) * 3^T + 2^(T - W) * 3^(c - 1)`. -/
theorem coasting_intermediate_repeat_squeeze {a_0 W T c m : ℕ} (hc : 1 ≤ c)
    (ha0 : a_0 < 2 ^ W) (hWT : W ≤ T)
    (b u' : ℕ → ℕ) (hb0 : b 0 = orbit a_0 T)
    (hstep : ∀ i < m, 3 * b i + 1 = 2 ^ c * u' i ∧ b (i + 1) = orbit (b i) c)
    {ξ : ℝ} (hsurv : ValidCompanionUpTo a_0 ξ T) :
    2 ^ (c * m + (T - W)) <
      (3 ^ c - 2 ^ c) * 3 ^ T + 2 ^ (T - W) * 3 ^ (c - 1) := by
  have hsq := coupled_intermediate_repeat_squeeze hc b u' hb0 hstep hsurv
  have h2a0 : 2 * a_0 + 1 ≤ 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsplit1 : c * m + T + 1 = (W + 1) + (c * m + (T - W)) := by omega
  have hsplit2 : T + 1 = (W + 1) + (T - W) := by omega
  have hmul :
      2 ^ (W + 1) * 2 ^ (c * m + (T - W)) <
        2 ^ (W + 1) * ((3 ^ c - 2 ^ c) * 3 ^ T + 2 ^ (T - W) * 3 ^ (c - 1)) := by
    calc
      2 ^ (W + 1) * 2 ^ (c * m + (T - W)) = 2 ^ (c * m + T + 1) := by
        rw [← Nat.pow_add, ← hsplit1]
      _ < (3 ^ c - 2 ^ c) * 3 ^ T * (2 * a_0 + 1) +
            2 ^ (T + 1) * 3 ^ (c - 1) := hsq
      _ ≤ (3 ^ c - 2 ^ c) * 3 ^ T * 2 ^ (W + 1) +
            2 ^ (T + 1) * 3 ^ (c - 1) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ h2a0) _
      _ = 2 ^ (W + 1) *
            ((3 ^ c - 2 ^ c) * 3 ^ T + 2 ^ (T - W) * 3 ^ (c - 1)) := by
            conv_lhs => rw [hsplit2, Nat.pow_add]
            ring
  exact Nat.lt_of_mul_lt_mul_left hmul

end Mahler.TwoSidedSqueeze
