import BridgeThreeMixedBlocks

/-!
# Formulation B: The High-Bit Jump and Zero-Lift Obstruction Lemma

This module formalizes the core lifting mechanism of **Formulation B**:

1. **Uniqueness and Oddness of the `m`-Block Residue (`block_chain_mod_two_pow_eq`,
   `block_residue_odd_and_pos`)**:
   Any two starting integers `a₁, a₂` realizing the same `m`-block chain
   `s(0), ..., s(m - 1)` agree modulo `2^(blockSteps s m)`. Moreover, for `m ≥ 1`,
   the canonical minimal residue `r_m = a_0 % 2^(blockSteps s m)` is odd and
   satisfies `1 ≤ r_m < 2^(blockSteps s m)`.
2. **Block-Level Zero-Lift Obstruction (`block_high_bit_jump_of_zero_lift_mismatch`)**:
   Let `T = blockSteps s m` and `r_m = a_0 % 2^T`. If `a_0` realizes `m + 1`
   blocks with lengths `s(0), ..., s(m)`, but the zero-lift candidate `r_m`
   does not have `(m + 1)`-st block length `s(m)` at step `T`, then the next
   minimal residue `r_{m+1} = a_0 % 2^(blockSteps s (m + 1))` is forced to
   activate a nonzero binary bit in `[T, T + s(m))`:
   `r_m + 2^T ≤ r_{m+1} ≤ a_0`.
3. **Survival-Level High-Bit Jump Lemma (`high_bit_jump_of_zero_lift_fails`)**:
   For any `a_0, N, M`, if the zero-lift residue `r_N = a_0 % 2^N` fails at some
   horizon `M` (`survivesSteps (a_0 % 2^N) M = false`) while `a_0` survives to
   step `M`, then `a_0` must jump by at least `+2^N`:
   `a_0 % 2^N + 2^N ≤ a_0`.
4. **Certified Two-Stage High-Bit Jump (`s_eq_two_survives_ten_forces_ge_265`)**:
   For any `a_0` with `s(0) = 2` (`a_0 % 8 = 1`):
   - Stage 1 (`N = 3 → M = 8`): `r_1 = 1` fails at step 4, forcing `a_0 % 256 = 9`.
   - Stage 2 (`N = 8 → M = 10`): the new zero-lift `r_2 = 9` has `orbit 9 8 = 243`
     (`3 * 243 + 1 = 730`, `v_2 = 1`) and fails at step `10` (`survivesSteps 9 10 = false`),
     forcing a second high-bit jump `9 + 2^8 = 265 ≤ a_0`.
-/

namespace Mahler.FormulationB

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree

/-! ## 1. Uniqueness and Oddness of the `m`-Block Minimal Residue -/

private theorem three_pow_mod_two (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- If `a₁, a₂` both realize the same `m`-block length sequence `s`, then
`2^(blockSteps s m)` divides `a₂ - a₁`. -/
theorem block_chain_dvd_difference {a₁ a₂ : ℕ} {s u₁ u₂ : ℕ → ℕ} {m : ℕ}
    (hc₁ : ValidBlockChain a₁ s u₁ m)
    (hc₂ : ValidBlockChain a₂ s u₂ m) :
    2 ^ (blockSteps s m) ∣ (a₂ - a₁) := by
  have hid₁ := mixed_block_integer_identity hc₁
  have hid₂ := mixed_block_integer_identity hc₂
  have hdiff :
      2 ^ (blockSteps s m) *
          (orbit a₂ (blockSteps s m) - orbit a₁ (blockSteps s m)) =
        3 ^ (blockSteps s m) * (a₂ - a₁) := by
    rw [Nat.mul_sub_left_distrib, hid₂, hid₁, Nat.mul_sub_left_distrib]
    omega
  have hd : 2 ^ (blockSteps s m) ∣ 3 ^ (blockSteps s m) * (a₂ - a₁) := by
    rw [← hdiff]
    exact Nat.dvd_mul_right _ _
  have hg : Nat.gcd (2 ^ (blockSteps s m)) (3 ^ (blockSteps s m)) = 1 :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)
  have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
  simpa only [hg, Nat.one_mul] using hc

/-- Any two starting integers realizing the same `m`-block length sequence `s`
have the exact same residue modulo `2^(blockSteps s m)`. -/
theorem block_chain_mod_two_pow_eq {a₁ a₂ : ℕ} {s u₁ u₂ : ℕ → ℕ} {m : ℕ}
    (hc₁ : ValidBlockChain a₁ s u₁ m)
    (hc₂ : ValidBlockChain a₂ s u₂ m) :
    a₁ % 2 ^ (blockSteps s m) = a₂ % 2 ^ (blockSteps s m) := by
  rcases Nat.le_total a₁ a₂ with hle | hge
  · rcases block_chain_dvd_difference hc₁ hc₂ with ⟨q, hq⟩
    have ha₂ : a₂ = a₁ + 2 ^ (blockSteps s m) * q := by omega
    rw [ha₂, Nat.add_mul_mod_self_left]
  · rcases block_chain_dvd_difference hc₂ hc₁ with ⟨q, hq⟩
    have ha₁ : a₁ = a₂ + 2 ^ (blockSteps s m) * q := by omega
    rw [ha₁, Nat.add_mul_mod_self_left]

/-- For `m ≥ 1`, any starting integer `a_0` realizing an `m`-block chain `s`
is odd, and its canonical minimal residue `r_m = a_0 % 2^(blockSteps s m)` is
odd and satisfies `1 ≤ r_m < 2^(blockSteps s m)`. -/
theorem block_residue_odd_and_pos {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hchain : ValidBlockChain a_0 s u m) :
    (a_0 % 2 ^ (blockSteps s m)) % 2 = 1 ∧
      1 ≤ a_0 % 2 ^ (blockSteps s m) ∧
      a_0 % 2 ^ (blockSteps s m) < 2 ^ (blockSteps s m) := by
  have hT : 1 ≤ blockSteps s m := blockSteps_pos hm (fun k hk => (hchain k hk).1)
  have hK_odd : blockKernel s m % 2 = 1 :=
    blockKernel_odd hm (fun k hk => (hchain k hk).1)
  have hid := mixed_block_integer_identity hchain
  have h2T_even : (2 ^ (blockSteps s m) * orbit a_0 (blockSteps s m)) % 2 = 0 := by
    have hpow : 2 ^ (blockSteps s m) = 2 ^ (blockSteps s m - 1) * 2 := by
      have hsub : blockSteps s m = (blockSteps s m - 1) + 1 := by omega
      conv_lhs => rw [hsub, Nat.pow_succ]
    have hmul :
        2 ^ (blockSteps s m) * orbit a_0 (blockSteps s m) =
          2 * (2 ^ (blockSteps s m - 1) * orbit a_0 (blockSteps s m)) := by
      rw [hpow]
      ring
    rw [hmul]
    omega
  have hrhs_even : (3 ^ (blockSteps s m) * a_0 + blockKernel s m) % 2 = 0 := by
    rw [← hid]
    exact h2T_even
  have h3T_odd : 3 ^ (blockSteps s m) % 2 = 1 := three_pow_mod_two (blockSteps s m)
  have ha0_odd : a_0 % 2 = 1 := by
    have hmod := Nat.add_mod (3 ^ (blockSteps s m) * a_0) (blockKernel s m) 2
    have hmul := Nat.mul_mod (3 ^ (blockSteps s m)) a_0 2
    rw [h3T_odd] at hmul
    omega
  have hrm_odd : (a_0 % 2 ^ (blockSteps s m)) % 2 = 1 := by
    rw [mod_two_of_mod_two_pow hT a_0]
    exact ha0_odd
  have hlt : a_0 % 2 ^ (blockSteps s m) < 2 ^ (blockSteps s m) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  refine ⟨hrm_odd, by omega, hlt⟩

/-! ## 2. The Block-Level and Survival-Level High-Bit Jump Lemmas -/

/-- Decomposition relating consecutive block residues `r_m = a_0 % 2^T(m)` and
`r_{m+1} = a_0 % 2^T(m+1)`. -/
theorem next_block_residue_eq_add_mul (a_0 : ℕ) (s : ℕ → ℕ) (m : ℕ) :
    a_0 % 2 ^ (blockSteps s (m + 1)) =
      a_0 % 2 ^ (blockSteps s m) +
        2 ^ (blockSteps s m) *
          ((a_0 % 2 ^ (blockSteps s (m + 1))) / 2 ^ (blockSteps s m)) := by
  have hdvd : 2 ^ (blockSteps s m) ∣ 2 ^ (blockSteps s (m + 1)) := by
    simp only [blockSteps, Nat.pow_add]
    exact Nat.dvd_mul_right _ _
  have hmod : (a_0 % 2 ^ (blockSteps s (m + 1))) % 2 ^ (blockSteps s m) =
      a_0 % 2 ^ (blockSteps s m) :=
    Nat.mod_mod_of_dvd a_0 hdvd
  have hdm := (Nat.div_add_mod (a_0 % 2 ^ (blockSteps s (m + 1)))
    (2 ^ (blockSteps s m))).symm
  rw [hmod] at hdm
  omega

/-- **Residue High-Bit Jump Lemma (`residue_high_bit_jump_of_not_two_pow_dvd`)**:
Suppose `a_0` realizes `m + 1` blocks `s(0), ..., s(m)`. Let `T = blockSteps s m`
and `r_m = a_0 % 2^T`. If `2^(s m)` does not divide `3 * orbit r_m T + 1`, then
the next minimal residue `r_{m+1} = a_0 % 2^(blockSteps s (m + 1))` must jump by
at least `+2^T`:
`r_m + 2^T ≤ r_{m+1} ≤ a_0`. -/
theorem residue_high_bit_jump_of_not_two_pow_dvd {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u (m + 1))
    (hnot_dvd : ¬ (2 ^ (s m) ∣ 3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1)) :
    a_0 % 2 ^ (blockSteps s m) + 2 ^ (blockSteps s m) ≤
        a_0 % 2 ^ (blockSteps s (m + 1)) ∧
      a_0 % 2 ^ (blockSteps s (m + 1)) ≤ a_0 := by
  have hrel := next_block_residue_eq_add_mul a_0 s m
  have hne : a_0 % 2 ^ (blockSteps s (m + 1)) ≠ a_0 % 2 ^ (blockSteps s m) := by
    intro heq
    apply hnot_dvd
    rcases hchain m (by omega) with ⟨_, _, hdecomp⟩
    let q := a_0 / 2 ^ (blockSteps s (m + 1))
    have ha0 : a_0 = 2 ^ (blockSteps s (m + 1)) * q + a_0 % 2 ^ (blockSteps s (m + 1)) :=
      (Nat.div_add_mod a_0 (2 ^ (blockSteps s (m + 1)))).symm
    have horb := orbit_add_two_pow_mul (blockSteps s (m + 1)) q
      (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) (by simp [blockSteps])
    have hsub : blockSteps s (m + 1) - blockSteps s m = s m := by simp [blockSteps]
    rw [hsub, ← ha0, heq] at horb
    have h3orb :
        (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1) +
          2 ^ (s m) * (3 ^ (blockSteps s m + 1) * q) =
          2 ^ (s m) * u m := by
      rw [← hdecomp, horb, Nat.pow_succ]
      ring
    have hmod0 :
        (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1) % 2 ^ (s m) = 0 := by
      have := congrArg (fun x => x % 2 ^ (s m)) h3orb
      simpa [Nat.add_mul_mod_self_left, Nat.mul_mod_right] using this
    exact Nat.dvd_of_mod_eq_zero hmod0
  have hq_pos : 1 ≤ (a_0 % 2 ^ (blockSteps s (m + 1))) / 2 ^ (blockSteps s m) := by
    cases hq : (a_0 % 2 ^ (blockSteps s (m + 1))) / 2 ^ (blockSteps s m) with
    | zero =>
        rw [hq, Nat.mul_zero, Nat.add_zero] at hrel
        exact False.elim (hne hrel)
    | succ k => exact Nat.succ_pos k
  have hmul_ge :
      2 ^ (blockSteps s m) ≤
        2 ^ (blockSteps s m) *
          ((a_0 % 2 ^ (blockSteps s (m + 1))) / 2 ^ (blockSteps s m)) := by
    simpa using Nat.mul_le_mul_left (2 ^ (blockSteps s m)) hq_pos
  exact ⟨by omega, Nat.mod_le a_0 (2 ^ (blockSteps s (m + 1)))⟩

/-- **Block-Valuation High-Bit Jump Lemma (`block_high_bit_jump_of_zero_lift_mismatch`)**:
If `a_0` realizes `m + 1` blocks `s(0), ..., s(m)`, and the zero-lift candidate
`r_m = a_0 % 2^T` (`T = blockSteps s m`) does not have `(m + 1)`-st block length
`s(m)` with an odd quotient, then `a_0` must activate a higher bit above `T`:
`a_0 % 2^T + 2^T ≤ a_0`. -/
theorem block_high_bit_jump_of_zero_lift_mismatch {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u (m + 1))
    (hmismatch : ¬ ∃ u_m : ℕ,
      u_m % 2 = 1 ∧
      3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1 =
        2 ^ (s m) * u_m) :
    a_0 % 2 ^ (blockSteps s m) + 2 ^ (blockSteps s m) ≤ a_0 := by
  have hdm := (Nat.div_add_mod a_0 (2 ^ (blockSteps s m))).symm
  have hne : a_0 ≠ a_0 % 2 ^ (blockSteps s m) := by
    intro heq
    apply hmismatch
    rcases hchain m (by omega) with ⟨_, hum, hdecomp⟩
    exact ⟨u m, hum, by simpa [← heq] using hdecomp⟩
  have hq_pos : 1 ≤ a_0 / 2 ^ (blockSteps s m) := by
    cases hq : a_0 / 2 ^ (blockSteps s m) with
    | zero =>
        rw [hq, Nat.mul_zero, Nat.zero_add] at hdm
        exact False.elim (hne hdm)
    | succ k => exact Nat.succ_pos k
  have hmul_ge :
      2 ^ (blockSteps s m) ≤
        2 ^ (blockSteps s m) * (a_0 / 2 ^ (blockSteps s m)) := by
    simpa using Nat.mul_le_mul_left (2 ^ (blockSteps s m)) hq_pos
  omega

/-- **Survival-Level High-Bit Jump Lemma (`high_bit_jump_of_zero_lift_fails`)**:
For any `a_0, N, M`, if the zero-lift residue `r_N = a_0 % 2^N` fails at some
horizon `M` (`survivesSteps (a_0 % 2^N) M = false`) while `a_0` survives to
step `M`, then `a_0` must jump by at least `+2^N`:
`a_0 % 2^N + 2^N ≤ a_0`. -/
theorem high_bit_jump_of_zero_lift_fails {a_0 N M : ℕ}
    (hz_fail : survivesSteps (a_0 % 2 ^ N) M = false)
    (hsurv : ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ M) :
    a_0 % 2 ^ N + 2 ^ N ≤ a_0 := by
  have ha0_true : survivesSteps a_0 M = true := by
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact hsurv
  have hne : a_0 ≠ a_0 % 2 ^ N := by
    intro heq
    rw [← heq] at hz_fail
    rw [ha0_true] at hz_fail
    cases hz_fail
  have hdm := (Nat.div_add_mod a_0 (2 ^ N)).symm
  have hq_pos : 1 ≤ a_0 / 2 ^ N := by
    cases hq : a_0 / 2 ^ N with
    | zero =>
        rw [hq, Nat.mul_zero, Nat.zero_add] at hdm
        exact False.elim (hne hdm)
    | succ k => exact Nat.succ_pos k
  have hmul_ge : 2 ^ N ≤ 2 ^ N * (a_0 / 2 ^ N) := by
    simpa using Nat.mul_le_mul_left (2 ^ N) hq_pos
  omega

/-! ## 3. Stabilization Obstruction & Certified Two-Stage Jump (`a_0 ≥ 265`) -/

/-- If `a_0 < 2^N` and its zero-lift `a_0 % 2^N` fails at step `M`, then `a_0`
cannot survive `M` steps. -/
theorem not_survives_of_lt_two_pow_and_zero_lift_fails {a_0 N M : ℕ}
    (hlt : a_0 < 2 ^ N)
    (hz_fail : survivesSteps (a_0 % 2 ^ N) M = false) :
    ¬ ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ M := by
  intro hsurv
  have hjump := high_bit_jump_of_zero_lift_fails hz_fail hsurv
  omega

private theorem nine_fails_at_step_10 :
    survivesSteps 9 10 = false := by
  decide

/-- **Certified Two-Stage High-Bit Jump for `s(0) = 2` (`a_0 % 8 = 1`)**:
- Stage 1 (`N = 3 → M = 8`): Any `a_0` with `a_0 % 8 = 1` surviving 8 steps is
  forced to jump from `r_1 = 1` to `r_2 = a_0 % 256 = 9` (`s_eq_two_survives_eight_iff_mod_256_eq_9`).
- Stage 2 (`N = 8 → M = 10`): Because the new zero-lift `r_2 = 9` has
  `orbit 9 8 = 243` (`3 * 243 + 1 = 730`, `v_2 = 1`) and fails at step `10`
  (`survivesSteps 9 10 = false`), any `a_0` with `a_0 % 8 = 1` surviving `10`
  steps must undergo a second high-bit jump to `9 + 2^8 = 265 ≤ a_0`. -/
theorem s_eq_two_survives_ten_forces_ge_265 {a_0 : ℕ}
    (h8 : a_0 % 8 = 1)
    (hsurv10 : ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ 10) :
    265 ≤ a_0 := by
  have hsurv8 : ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ 8 := by
    rcases hsurv10 with ⟨ξ, hξ⟩
    exact ⟨ξ, validCompanionUpTo_mono (by decide : 8 ≤ 10) hξ⟩
  have hmod256 : a_0 % 256 = 9 :=
    (s_eq_two_survives_eight_iff_mod_256_eq_9 a_0).mp ⟨h8, hsurv8⟩
  have hpow : (2 ^ 8 : ℕ) = 256 := by decide
  have hz_fail : survivesSteps (a_0 % 2 ^ 8) 10 = false := by
    rw [hpow, hmod256]
    exact nine_fails_at_step_10
  have hjump := high_bit_jump_of_zero_lift_fails hz_fail hsurv10
  rw [hpow, hmod256] at hjump
  omega

end Mahler.FormulationB
