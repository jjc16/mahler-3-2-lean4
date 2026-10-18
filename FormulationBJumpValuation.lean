import FormulationBHighBitJump

/-!
# Formulation B: Exact Jump Valuation & The Two-Branch Escape Dichotomy

When the `m`-block minimal representative `r_m = a_0 % 2^T(m)` reaches its
`m`-th odd return `b_m = orbit r_m T(m)`, how does `r_{m+1} = a_0 % 2^T(m+1)`
behave as we advance to block `m + 1`?

Writing `r_{m+1} = r_m + 2^T(m) * q_m`, this module proves the exact 2-adic
laws governing the jump quotient `q_m`:

1. **Exact Return Shift Equation (`orbit_next_residue_at_return`)**:
   At step `T = blockSteps s m`,
   `orbit r_{m+1} T = 3^T * q_m + orbit r_m T`, and consequently
   `3 * orbit r_{m+1} T + 1 = 3^(T + 1) * q_m + (3 * orbit r_m T + 1)`.
2. **Universal Evenness of Block-Preserving Jumps (`jump_quotient_even`)**:
   If `r_m` and `r_{m+1}` both have an odd return at step `T` (preserving the
   `m`-block structure), then since `3^T` is odd and `Odd = Odd * q_m + Odd`,
   the jump quotient `q_m` is **always even** (`q_m % 2 = 0`).
3. **Exact 2-adic Valuation Transfer (`two_pow_dvd_jump_quotient_iff`)**:
   Across an `(m + 1)`-block chain with `s(m) ≥ t`,
   `2^t ∣ q_m ↔ 2^t ∣ (3 * orbit r_m T + 1)`.
   Thus the first nonzero binary bit of `q_m` is identically the 2-adic
   valuation `v_2(3 * b_m + 1)` whenever `v_2(3 * b_m + 1) < s(m)`.
4. **The `b_m ≡ 3 (mod 4)` Double High-Bit Jump (`double_jump_of_return_mod_four_eq_three`)**:
   Whenever `orbit r_m T % 4 = 3` and `2 ≤ s(m)`, `q_m % 4 = 2` (`q_m ≥ 2`),
   forcing a **double high-bit jump**:
   `r_m + 2^(T + 1) ≤ r_{m+1} ≤ a_0`.
5. **The Odd-Quotient Escape Branch (`odd_quotient_flips_return_to_even`)**:
   If instead `a_0 = r_m + 2^T * q` uses an **odd** quotient `q % 2 = 1`
   (such as `265 = 9 + 2^8`), then `orbit a_0 T % 2 = 0`: step `T` flips from
   odd to even, mutating the `(m - 1)`-st block length rather than continuing
   from step `T`.
-/

namespace Mahler.JumpValuation

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB

/-! ## 1. The Jump Quotient `jumpQuotient` and Exact Return Shift Equation -/

/-- The high-bit jump quotient `q_m = (r_{m+1} - r_m) / 2^T(m)`. -/
def jumpQuotient (a_0 : ℕ) (s : ℕ → ℕ) (m : ℕ) : ℕ :=
  (a_0 % 2 ^ (blockSteps s (m + 1))) / 2 ^ (blockSteps s m)

theorem next_residue_eq_add_jumpQuotient (a_0 : ℕ) (s : ℕ → ℕ) (m : ℕ) :
    a_0 % 2 ^ (blockSteps s (m + 1)) =
      2 ^ (blockSteps s m) * jumpQuotient a_0 s m + a_0 % 2 ^ (blockSteps s m) := by
  have h := next_block_residue_eq_add_mul a_0 s m
  unfold jumpQuotient
  omega

/-- Exact Return Shift Equation: at cumulative step `T = blockSteps s m`,
`orbit r_{m+1} T = 3^T * jumpQuotient a_0 s m + orbit r_m T`. -/
theorem orbit_next_residue_at_return (a_0 : ℕ) (s : ℕ → ℕ) (m : ℕ) :
    orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) =
      3 ^ (blockSteps s m) * jumpQuotient a_0 s m +
        orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) := by
  have hrel := next_residue_eq_add_jumpQuotient a_0 s m
  have horb := orbit_add_two_pow_mul (blockSteps s m) (jumpQuotient a_0 s m)
    (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) (Nat.le_refl _)
  rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at horb
  rw [← hrel] at horb
  exact horb

/-- Exact Next-Block Numerator Shift Equation:
`3 * orbit r_{m+1} T + 1 = 3^(T + 1) * jumpQuotient a_0 s m + (3 * orbit r_m T + 1)`. -/
theorem three_mul_orbit_next_residue_add_one (a_0 : ℕ) (s : ℕ → ℕ) (m : ℕ) :
    3 * orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) + 1 =
      3 ^ (blockSteps s m + 1) * jumpQuotient a_0 s m +
        (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1) := by
  rw [orbit_next_residue_at_return, Nat.pow_succ]
  ring

/-! ## 2. Universal Evenness of Block-Preserving Jumps & Odd-Quotient Escape -/

private theorem three_pow_mod_two (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **Universal Evenness of Block-Preserving Jumps (`jump_quotient_even`)**:
Whenever both `r_m` and `r_{m+1}` have an odd integer at return `T = blockSteps s m`,
the jump quotient `jumpQuotient a_0 s m` is even (`% 2 = 0`). -/
theorem jump_quotient_even {a_0 : ℕ} {s : ℕ → ℕ} {m : ℕ}
    (hodd_m : orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) % 2 = 1)
    (hodd_next : orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) % 2 = 1) :
    jumpQuotient a_0 s m % 2 = 0 := by
  have horb := orbit_next_residue_at_return a_0 s m
  have hmod := congrArg (fun x => x % 2) horb
  dsimp only at hmod
  have h3 : 3 ^ (blockSteps s m) % 2 = 1 := three_pow_mod_two (blockSteps s m)
  rw [hodd_next, Nat.add_mod, Nat.mul_mod, h3, hodd_m] at hmod
  omega

/-- **The Odd-Quotient Escape Branch (`odd_quotient_flips_return_to_even`)**:
If `r_m` has an odd return at step `T`, then any lift `a_0 = 2^T * q + r_m`
with an **odd** quotient `q % 2 = 1` flips step `T` from odd to even
(`orbit a_0 T % 2 = 0`), mutating the `(m - 1)`-st block length rather than
starting a new odd block at `T`. -/
theorem odd_quotient_flips_return_to_even {r_m T q : ℕ}
    (hodd : orbit r_m T % 2 = 1) (hq : q % 2 = 1) :
    orbit (2 ^ T * q + r_m) T % 2 = 0 := by
  have horb := orbit_add_two_pow_mul T q r_m T (Nat.le_refl T)
  rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at horb
  have h3 : 3 ^ T % 2 = 1 := three_pow_mod_two T
  rw [horb, Nat.add_mod, Nat.mul_mod, h3, hq, hodd]

/-! ## 3. Exact 2-adic Valuation Transfer & The Double High-Bit Jump -/

/-- Along a valid `(m + 1)`-block chain, `2^(s m)` divides
`3 * orbit (a_0 % 2^(blockSteps s (m + 1))) (blockSteps s m) + 1`. -/
theorem two_pow_dvd_three_mul_orbit_next_residue {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u (m + 1)) :
    2 ^ (s m) ∣
      (3 * orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) + 1) := by
  rcases hchain m (by omega) with ⟨_, _, hdecomp⟩
  let q := a_0 / 2 ^ (blockSteps s (m + 1))
  have ha0 : a_0 = 2 ^ (blockSteps s (m + 1)) * q + a_0 % 2 ^ (blockSteps s (m + 1)) :=
    (Nat.div_add_mod a_0 (2 ^ (blockSteps s (m + 1)))).symm
  have horb := orbit_add_two_pow_mul (blockSteps s (m + 1)) q
    (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) (by simp [blockSteps])
  have hsub : blockSteps s (m + 1) - blockSteps s m = s m := by simp [blockSteps]
  rw [hsub, ← ha0] at horb
  have h3orb :
      (3 * orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) + 1) +
        2 ^ (s m) * (3 ^ (blockSteps s m + 1) * q) =
        2 ^ (s m) * u m := by
    rw [← hdecomp, horb, Nat.pow_succ]
    ring
  have hmod0 :
      (3 * orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) + 1) % 2 ^ (s m) = 0 := by
    have := congrArg (fun x => x % 2 ^ (s m)) h3orb
    simpa [Nat.add_mul_mod_self_left, Nat.mul_mod_right] using this
  exact Nat.dvd_of_mod_eq_zero hmod0

/-- **Exact 2-adic Valuation Transfer (`two_pow_dvd_jump_quotient_iff`)**:
Along a valid `(m + 1)`-block chain, for every `t ≤ s m`:
`2^t ∣ jumpQuotient a_0 s m ↔ 2^t ∣ (3 * orbit (a_0 % 2^(blockSteps s m)) (blockSteps s m) + 1)`. -/
theorem two_pow_dvd_jump_quotient_iff {a_0 : ℕ} {s u : ℕ → ℕ} {m t : ℕ}
    (hchain : ValidBlockChain a_0 s u (m + 1))
    (ht : t ≤ s m) :
    2 ^ t ∣ jumpQuotient a_0 s m ↔
      2 ^ t ∣ (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1) := by
  have hdvd_sm := two_pow_dvd_three_mul_orbit_next_residue hchain
  have hdvd_t_sm : 2 ^ t ∣ 2 ^ (s m) := by
    have hsplit : s m = t + (s m - t) := by omega
    rw [hsplit, Nat.pow_add]
    exact Nat.dvd_mul_right _ _
  have hdvd_lhs :
      2 ^ t ∣ (3 * orbit (a_0 % 2 ^ (blockSteps s (m + 1))) (blockSteps s m) + 1) :=
    Nat.dvd_trans hdvd_t_sm hdvd_sm
  have hshift := three_mul_orbit_next_residue_add_one a_0 s m
  have hg : Nat.gcd (2 ^ t) (3 ^ (blockSteps s m + 1)) = 1 :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)
  constructor
  · intro hq
    have hq3 : 2 ^ t ∣ 3 ^ (blockSteps s m + 1) * jumpQuotient a_0 s m :=
      Nat.dvd_mul_left_of_dvd hq _
    rcases hdvd_lhs with ⟨A, hA⟩
    rcases hq3 with ⟨B, hB⟩
    rw [hA, hB] at hshift
    refine ⟨A - B, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega
  · intro hb
    rcases hdvd_lhs with ⟨A, hA⟩
    rcases hb with ⟨B, hB⟩
    have hdiff :
        3 ^ (blockSteps s m + 1) * jumpQuotient a_0 s m = 2 ^ t * (A - B) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    have hd : 2 ^ t ∣ 3 ^ (blockSteps s m + 1) * jumpQuotient a_0 s m :=
      ⟨A - B, hdiff⟩
    have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
    simpa only [hg, Nat.one_mul] using hc

/-- **Valuation-Boosted High-Bit Jump (`valuation_boosted_high_bit_jump`)**:
If `v < s m`, `2^v ∣ (3 * orbit r_m T + 1)`, and `¬ (2^(s m) ∣ (3 * orbit r_m T + 1))`,
then `2^v ∣ jumpQuotient a_0 s m` and `jumpQuotient a_0 s m > 0`, forcing a
boosted jump of at least `+2^(T + v)`:
`r_m + 2^(blockSteps s m + v) ≤ r_{m+1} ≤ a_0`. -/
theorem valuation_boosted_high_bit_jump {a_0 : ℕ} {s u : ℕ → ℕ} {m v : ℕ}
    (hchain : ValidBlockChain a_0 s u (m + 1))
    (hv : v ≤ s m)
    (hdvd_v : 2 ^ v ∣ (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1))
    (hnot_dvd_sm : ¬ (2 ^ (s m) ∣ (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1))) :
    a_0 % 2 ^ (blockSteps s m) + 2 ^ (blockSteps s m + v) ≤
        a_0 % 2 ^ (blockSteps s (m + 1)) ∧
      a_0 % 2 ^ (blockSteps s (m + 1)) ≤ a_0 := by
  have hq_dvd : 2 ^ v ∣ jumpQuotient a_0 s m :=
    (two_pow_dvd_jump_quotient_iff hchain hv).mpr hdvd_v
  have hq_not_sm : ¬ (2 ^ (s m) ∣ jumpQuotient a_0 s m) :=
    fun h => hnot_dvd_sm ((two_pow_dvd_jump_quotient_iff hchain (Nat.le_refl _)).mp h)
  have hq_pos : 0 < jumpQuotient a_0 s m := by
    cases hq : jumpQuotient a_0 s m with
    | zero =>
        rw [hq] at hq_not_sm
        exact False.elim (hq_not_sm (Nat.dvd_zero _))
    | succ k => exact Nat.succ_pos k
  have hq_ge : 2 ^ v ≤ jumpQuotient a_0 s m := Nat.le_of_dvd hq_pos hq_dvd
  have hrel := next_residue_eq_add_jumpQuotient a_0 s m
  have hmul :
      2 ^ (blockSteps s m + v) ≤ 2 ^ (blockSteps s m) * jumpQuotient a_0 s m := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_left (2 ^ (blockSteps s m)) hq_ge
  exact ⟨by omega, Nat.mod_le a_0 (2 ^ (blockSteps s (m + 1)))⟩

/-- **The `b_m ≡ 3 (mod 4)` Double High-Bit Jump (`double_jump_of_return_mod_four_eq_three`)**:
Whenever the zero-lift return integer `b_m = orbit r_m T` satisfies `b_m % 4 = 3`
and the `(m + 1)`-st block has length `s(m) ≥ 2`, the minimal residue must jump
by at least `+2^(T + 1)` (double the single-bit jump `+2^T`):
`r_m + 2^(blockSteps s m + 1) ≤ r_{m+1} ≤ a_0`. -/
theorem double_jump_of_return_mod_four_eq_three {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u (m + 1))
    (hsm : 2 ≤ s m)
    (hmod4 : orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) % 4 = 3) :
    a_0 % 2 ^ (blockSteps s m) + 2 ^ (blockSteps s m + 1) ≤
        a_0 % 2 ^ (blockSteps s (m + 1)) ∧
      a_0 % 2 ^ (blockSteps s (m + 1)) ≤ a_0 := by
  have hdvd_1 : 2 ^ 1 ∣ (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1) := by
    refine ⟨(3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1) / 2, ?_⟩
    omega
  have hnot_dvd_sm :
      ¬ (2 ^ (s m) ∣ (3 * orbit (a_0 % 2 ^ (blockSteps s m)) (blockSteps s m) + 1)) := by
    intro hdvd
    have hdvd4 : 4 ∣ 2 ^ (s m) := by
      have hsplit : s m = 2 + (s m - 2) := by omega
      rw [hsplit, Nat.pow_add]
      exact ⟨2 ^ (s m - 2), by ring⟩
    rcases Nat.dvd_trans hdvd4 hdvd with ⟨k, hk⟩
    omega
  exact valuation_boosted_high_bit_jump hchain (by omega : 1 ≤ s m) hdvd_1 hnot_dvd_sm

end Mahler.JumpValuation
