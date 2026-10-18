import FormulationBJumpValuation

/-!
# Bounding Escape Branch 2: The Block-Lengthening Caps

In `FormulationBJumpValuation.lean`, we showed that when the zero-lift candidate
`r_m = a_0 % 2^T(m)` fails at return `T(m)`, a larger candidate `a_0 = 2^T(m) * q + r_m`
has two escape branches:
- **Branch 1 (`q` even, `q ≥ 2`)**: preserves step `T(m)` as an odd return and
  jumps by at least `+2^(T(m) + v_2(3 b_m + 1))`.
- **Branch 2 (`q` odd, `q ≥ 1`)**: flips step `T(m)` from odd to even,
  lengthening the `(m - 1)`-st block from `s(m - 1)` to `s(m - 1) + Δs`.

This module formalizes **Part A**, proving that Escape Branch 2 is strictly
capped both by the real partition windows and by an exact `3^(s - 1)`-cancellation
law in the Archimedean half-corridor:

1. **Uniqueness of Block Length & Fractional-Window Cap (`unique_block_length_of_fracPart`,
   `windowLow_caps_block_length`)**:
   - Because the partition windows `[windowLow s, windowLow (s - 1))` are
     pairwise disjoint, any initial fractional part `r_0` admits **at most one**
     block length `s ≥ 1` surviving to step `s + 1`.
   - Moreover, if `windowLow S_max ≤ fracPart a ξ 0`, then surviving to step `s`
     (`ValidCompanionAt a ξ s`) alone forces `s ≤ S_max`.
2. **The `3^(s - 1)`-Cancellation Archimedean Block-Length Cap (`block_length_archimedean_cap`)**:
   At the end of block `k` (`T_{k+1} = T_k + s_k`), the return integer is
   `orbit a_0 (T_k + s_k) = 3^(s_k - 1) * u_k`. Substituting this into the
   half-corridor bound `2^(T_k + s_k + 1) * orbit a_0 (T_k + s_k) < 3^(T_k + s_k) * (2 a_0 + 1)`
   and canceling `3^(s_k - 1)` from both sides eliminates `s_k` from the
   right-hand side completely:
   `2^(blockSteps s k + s k + 1) * u k < 3^(blockSteps s k + 1) * (2 * a_0 + 1)`.
3. **Exact Extra-Step Cap on Escape Branch 2 (`escape_branch_two_extra_steps_cap`)**:
   When `a_0 = 2^T * q + r_m` (`q` odd) flips step `T` from odd to even with
   `orbit a_0 T = 2^Δs * w` (`Δs ≥ 1`), steps `T, ..., T + Δs - 1` are even,
   step `T + Δs` is `3^Δs * w`, and canceling `3^Δs` yields the strict cap
   `2^(T + Δs + 1) * w < 3^T * (2 * a_0 + 1)`.
-/

namespace Mahler.EscapeBranchCap

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

/-! ## 1. Disjoint Partition Windows & Fractional-Window Cap on Block Length -/

/-- Because the partition windows `[windowLow s, windowLow (s - 1))` are
disjoint, a single real value `r` can lie in at most one window. -/
theorem unique_window_of_mem {s₁ s₂ : ℕ} {r : ℝ}
    (h₁ : windowLow s₁ ≤ r ∧ r < windowLow (s₁ - 1))
    (h₂ : windowLow s₂ ≤ r ∧ r < windowLow (s₂ - 1)) :
    s₁ = s₂ := by
  rcases lt_trichotomy s₁ s₂ with hlt | heq | hgt
  · have hle : s₁ ≤ s₂ - 1 := by omega
    have hw : windowLow (s₂ - 1) ≤ windowLow s₁ := windowLow_anti hle
    linarith
  · exact heq
  · have hle : s₂ ≤ s₁ - 1 := by omega
    have hw : windowLow (s₁ - 1) ≤ windowLow s₂ := windowLow_anti hle
    linarith

/-- If `windowLow S_max ≤ fracPart a ξ 0` at an odd start `a`, then any block of
length `s ≥ 1` (`3a + 1 = 2^s * u`) that survives to step `s` must satisfy
`s ≤ S_max`. -/
theorem windowLow_caps_block_length {a s u S_max : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) {ξ : ℝ}
    (hlo : windowLow S_max ≤ fracPart a ξ 0)
    (hs_valid : ValidCompanionAt a ξ s) :
    s ≤ S_max := by
  have hrs_hi : fracPart a ξ s < 1 / 2 :=
    ((validCompanionAt_iff_fracPart a ξ s).mp hs_valid).2
  have hmacro := fracPart_odd_block hs hdecomp ξ
  rw [hmacro] at hrs_hi
  have hp23 : (0 : ℝ) < (2 / 3 : ℝ) ^ s := by positivity
  have hinv : (2 / 3 : ℝ) ^ s * (3 / 2 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have hr0_hi : fracPart a ξ 0 < (1 / 3 : ℝ) + (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ s := by
    have hm := mul_lt_mul_of_pos_left hrs_hi hp23
    nlinarith
  rw [windowUpper_eq_windowLow_pred hs] at hr0_hi
  by_contra hgt
  have hle : S_max ≤ s - 1 := by omega
  have hw : windowLow (s - 1) ≤ windowLow S_max := windowLow_anti hle
  linarith

/-! ## 2. The `3^(s - 1)`-Cancellation Archimedean Cap on Every Block Length -/

/-- **The `3^(s - 1)`-Cancellation Archimedean Cap (`block_length_archimedean_cap`)**:
For any block `k < m` in a valid block chain `ValidBlockChain a_0 s u m` that
survives through the end of block `k` (`ValidCompanionUpTo a_0 ξ (blockSteps s k + s k)`),
the factor `3^(s k - 1)` in `orbit a_0 (blockSteps s k + s k) = 3^(s k - 1) * u k`
cancels against `3^(blockSteps s k + s k)`, leaving an upper bound independent
of `s k` on the right-hand side:
`2^(blockSteps s k + s k + 1) * u k < 3^(blockSteps s k + 1) * (2 * a_0 + 1)`. -/
theorem block_length_archimedean_cap {a_0 : ℕ} {s u : ℕ → ℕ} {m k : ℕ}
    (hk : k < m) (hchain : ValidBlockChain a_0 s u m) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s k + s k)) :
    2 ^ (blockSteps s k + s k + 1) * u k <
      3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) ∧
    2 ^ (blockSteps s k + s k + 1) <
      3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) := by
  rcases hchain k hk with ⟨hsk, huk, hdecomp⟩
  have hret :
      orbit a_0 (blockSteps s k + s k) = 3 ^ (s k - 1) * u k := by
    rw [orbit_add]
    exact orbit_odd_block_return hsk hdecomp
  have hcor := (surviving_orbit_half_corridor hsurv).2
  rw [hret] at hcor
  have hpow3 :
      3 ^ (blockSteps s k + s k) =
        3 ^ (s k - 1) * 3 ^ (blockSteps s k + 1) := by
    have hsum : blockSteps s k + s k = (s k - 1) + (blockSteps s k + 1) := by omega
    rw [hsum, Nat.pow_add]
  have hmul_lt :
      3 ^ (s k - 1) * (2 ^ (blockSteps s k + s k + 1) * u k) <
        3 ^ (s k - 1) * (3 ^ (blockSteps s k + 1) * (2 * a_0 + 1)) := by
    calc
      3 ^ (s k - 1) * (2 ^ (blockSteps s k + s k + 1) * u k) =
          2 ^ (blockSteps s k + s k + 1) * (3 ^ (s k - 1) * u k) := by ring
      _ < 3 ^ (blockSteps s k + s k) * (2 * a_0 + 1) := hcor
      _ = 3 ^ (s k - 1) * (3 ^ (blockSteps s k + 1) * (2 * a_0 + 1)) := by
            rw [hpow3]
            ring
  have hlt1 :
      2 ^ (blockSteps s k + s k + 1) * u k <
        3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) :=
    Nat.lt_of_mul_lt_mul_left hmul_lt
  have hu_pos : 1 ≤ u k := by omega
  have hle_u :
      2 ^ (blockSteps s k + s k + 1) ≤
        2 ^ (blockSteps s k + s k + 1) * u k := by
    simpa using Nat.mul_le_mul_left (2 ^ (blockSteps s k + s k + 1)) hu_pos
  exact ⟨hlt1, Nat.lt_of_le_of_lt hle_u hlt1⟩

/-! ## 3. Exact Extra-Step Cap on Escape Branch 2 (`q` Odd) -/

/-- When Escape Branch 2 flips step `T` from odd to even with
`orbit a_0 T = 2^Δs * w`, the next `Δs` steps achieve `orbit a_0 (T + Δs) = 3^Δs * w`,
and canceling `3^Δs` against the half-corridor bound at `T + Δs` yields the
strict extra-step cap:
`2^(T + Δs + 1) * w < 3^T * (2 * a_0 + 1)`. -/
theorem escape_branch_two_extra_steps_cap {a_0 T ds w : ℕ}
    (hdecomp : orbit a_0 T = 2 ^ ds * w) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (T + ds)) :
    orbit a_0 (T + ds) = 3 ^ ds * w ∧
      2 ^ (T + ds + 1) * w < 3 ^ T * (2 * a_0 + 1) := by
  have horb : orbit a_0 (T + ds) = 3 ^ ds * w := by
    rw [orbit_add, hdecomp, orbit_even_tail w ds ds (Nat.le_refl ds),
      Nat.sub_self, Nat.pow_zero, Nat.mul_one]
  have hcor := (surviving_orbit_half_corridor hsurv).2
  rw [horb] at hcor
  have hmul_lt :
      3 ^ ds * (2 ^ (T + ds + 1) * w) <
        3 ^ ds * (3 ^ T * (2 * a_0 + 1)) := by
    calc
      3 ^ ds * (2 ^ (T + ds + 1) * w) =
          2 ^ (T + ds + 1) * (3 ^ ds * w) := by ring
      _ < 3 ^ (T + ds) * (2 * a_0 + 1) := hcor
      _ = 3 ^ ds * (3 ^ T * (2 * a_0 + 1)) := by
            rw [Nat.pow_add]
            ring
  exact ⟨horb, Nat.lt_of_mul_lt_mul_left hmul_lt⟩

end Mahler.EscapeBranchCap
