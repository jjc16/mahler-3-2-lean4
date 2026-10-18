import PureIntegerPinch

/-!
# Approach 2: Odd-to-Odd Block Coupling, Valuation Transfer, and 2-adic Bit Forcing

This module formalizes Approach 2, coupling the 2-adic structure of odd blocks
with the real fractional drift and modulo-`2^N` periodicity of `IntegerPinch`:

1. **Exact Odd-to-Odd Integer Macro-Step (`orbit_odd_block_return`)**:
   If `a` is odd and `3a + 1 = 2^s * u` with `s ≥ 1` and `u` odd, then steps
   `1, ..., s - 1` are even (`orbit a k % 2 = 0`) and step `s` returns to the
   odd integer `orbit a s = 3^(s - 1) * u`.
2. **Exact 2-adic to 3-adic Valuation Transfer (`odd_block_three_pow_valuation`)**:
   The next odd integer `a' = orbit a s` satisfies `3^(s - 1) ∣ a'` and
   `¬ (3^s ∣ a')`, so its 3-adic valuation is exactly `s - 1`.
3. **Exact Coupled Fractional Macro-Step (`fracPart_odd_block`)**:
   Across an odd-to-odd block of length `s`, the real fractional part
   `fracPart a ξ n = ξ * (3/2)^n - orbit a n` updates by
   `fracPart a ξ s = (3/2)^s * (fracPart a ξ 0 - 1/3)`.
4. **The `s = 2` (`OE`) Fractional Drain Law (`s_eq_two_fractional_drain`)**:
   When `s = 2` (`3a + 1 = 4u`) and `0 ≤ r_0 < 1/2`, the fractional part drops
   by more than `1/8` (`r_2 < r_0 - 1/8` and `r_2 < 3/8`), and after the next
   odd step `r_3 < 1/16`.
5. **General `2^N`-Periodicity of `N`-Step Survival (`exists_validCompanionUpTo_mod_two_pow_iff`)
   and Coupled Bit-Forcing (`s_eq_two_survives_eight_iff_mod_256_eq_9`)**:
   For every `N`, `N`-step Mahler survival depends only on `a mod 2^N`. In
   particular, an odd start with `s = 2` (`a % 8 = 1`) survives `8` steps if
   and only if `a % 256 = 9` (forcing 5 additional binary bits at once).
-/

namespace Mahler.OddBlock

open Mahler
open Mahler.Pinch

/-! ## 1. Exact Odd-to-Odd Integer Macro-Step -/

theorem step_two_mul (x : ℕ) : step (2 * x) = 3 * x := by
  unfold step
  omega

theorem step_odd_of_three_mul_add_one {a s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    step a = 2 ^ (s - 1) * u := by
  have hpow : 2 ^ s * u = 2 * (2 ^ (s - 1) * u) := by
    have hsub : s = (s - 1) + 1 := by omega
    conv_lhs => rw [hsub, Nat.pow_succ]
    ring
  unfold step
  omega

/-- Auxiliary formula along the even tail following the initial odd step. -/
theorem orbit_even_tail (u m k : ℕ) (hk : k ≤ m) :
    orbit (2 ^ m * u) k = 3 ^ k * 2 ^ (m - k) * u := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
      have hk' : k ≤ m := by omega
      have hsub : m - k = (m - (k + 1)) + 1 := by omega
      have htwo :
          3 ^ k * 2 ^ (m - k) * u = 2 * (3 ^ k * 2 ^ (m - (k + 1)) * u) := by
        rw [hsub, Nat.pow_succ]
        ring
      have hstep :
          step (3 ^ k * 2 ^ (m - k) * u) = 3 ^ (k + 1) * 2 ^ (m - (k + 1)) * u := by
        rw [htwo, step_two_mul, Nat.pow_succ]
        ring
      simpa [orbit, ih hk'] using hstep

/-- Closed form for `orbit a k` (`1 ≤ k ≤ s`) when `3a + 1 = 2^s * u`. -/
theorem orbit_odd_block {a s u k : ℕ} (hs : 1 ≤ s) (hk1 : 1 ≤ k) (hks : k ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    orbit a k = 3 ^ (k - 1) * 2 ^ (s - k) * u := by
  have hk_eq : k = 1 + (k - 1) := by omega
  conv_lhs => rw [hk_eq, orbit_add]
  have h1 : orbit a 1 = 2 ^ (s - 1) * u := by
    simpa [orbit] using step_odd_of_three_mul_add_one hs hdecomp
  rw [h1, orbit_even_tail u (s - 1) (k - 1) (by omega)]
  have hsub : s - 1 - (k - 1) = s - k := by omega
  rw [hsub]

/-- All intermediate steps `1 ≤ k < s` in the block `O E^(s-1)` are even. -/
theorem orbit_odd_block_even_interior {a s u k : ℕ} (hk1 : 1 ≤ k) (hks : k < s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    orbit a k % 2 = 0 := by
  rw [orbit_odd_block (by omega) hk1 (by omega) hdecomp]
  have hsub : s - k = (s - k - 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  have hmul :
      3 ^ (k - 1) * (2 ^ (s - k - 1) * 2) * u =
        2 * (3 ^ (k - 1) * 2 ^ (s - k - 1) * u) := by ring
  rw [hmul]
  omega

/-- At step `s`, the block returns to the next odd integer `3^(s - 1) * u`. -/
theorem orbit_odd_block_return {a s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    orbit a s = 3 ^ (s - 1) * u := by
  rw [orbit_odd_block hs hs (Nat.le_refl s) hdecomp, Nat.sub_self, Nat.pow_zero,
    Nat.mul_one]

private theorem three_pow_mod_two (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem orbit_odd_block_return_odd {a s u : ℕ} (hs : 1 ≤ s) (hu : u % 2 = 1)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    orbit a s % 2 = 1 := by
  rw [orbit_odd_block_return hs hdecomp, Nat.mul_mod, three_pow_mod_two, hu]

/-! ## 2. Exact 2-adic to 3-adic Valuation Transfer (`v_3(a') = s - 1`) -/

theorem not_three_dvd_odd_part {a s u : ℕ} (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    ¬ (3 ∣ u) := by
  rintro ⟨k, rfl⟩
  have hdiv : 2 ^ s * (3 * k) = 3 * (2 ^ s * k) := by ring
  rw [hdiv] at hdecomp
  omega

/-- Exact valuation transfer: `3^(s - 1)` divides `orbit a s`, and `3^s` does not. -/
theorem odd_block_three_pow_valuation {a s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) :
    3 ^ (s - 1) ∣ orbit a s ∧ ¬ (3 ^ s ∣ orbit a s) := by
  rw [orbit_odd_block_return hs hdecomp]
  refine ⟨⟨u, rfl⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hsub : s = (s - 1) + 1 := by omega
  have hpow : 3 ^ s * q = 3 ^ (s - 1) * (3 * q) := by
    conv_lhs => rw [hsub, Nat.pow_succ]
    ring
  rw [hpow] at hq
  have hpos : 0 < 3 ^ (s - 1) := Nat.pow_pos (by decide)
  have hu : u = 3 * q := Nat.eq_of_mul_eq_mul_left hpos hq
  exact not_three_dvd_odd_part hdecomp ⟨q, hu⟩

/-! ## 3. Coupled Fractional Macro-Step and the `s = 2` Drain Law -/

noncomputable def fracPart (a : ℕ) (ξ : ℝ) (n : ℕ) : ℝ :=
  ξ * (3 / 2 : ℝ) ^ n - (orbit a n : ℝ)

theorem validCompanionAt_iff_fracPart (a : ℕ) (ξ : ℝ) (n : ℕ) :
    ValidCompanionAt a ξ n ↔ 0 ≤ fracPart a ξ n ∧ fracPart a ξ n < 1 / 2 := by
  unfold ValidCompanionAt fracPart
  constructor <;> intro h <;> constructor <;> linarith

/-- Exact step-by-step fractional recurrence coupled to `orbit a n % 2`. -/
theorem fracPart_succ (a : ℕ) (ξ : ℝ) (n : ℕ) :
    fracPart a ξ (n + 1) =
      (3 / 2 : ℝ) * fracPart a ξ n - ((orbit a n % 2 : ℕ) : ℝ) / 2 := by
  unfold fracPart
  have hstep : 2 * (orbit a (n + 1) : ℝ) =
      3 * (orbit a n : ℝ) + ((orbit a n % 2 : ℕ) : ℝ) := by
    exact_mod_cast step_identity (orbit a n)
  rw [pow_succ]
  linarith

/-- Across an odd-to-odd block of length `s ≥ 1` (`3a + 1 = 2^s * u`), the
fractional part updates by `fracPart a ξ s = (3/2)^s * (fracPart a ξ 0 - 1/3)`. -/
theorem fracPart_odd_block {a s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * a + 1 = 2 ^ s * u) (ξ : ℝ) :
    fracPart a ξ s = (3 / 2 : ℝ) ^ s * (fracPart a ξ 0 - 1 / 3) := by
  unfold fracPart
  have hret := orbit_odd_block_return hs hdecomp
  have hmul : 2 ^ s * orbit a s = 3 ^ (s - 1) * (3 * a + 1) := by
    rw [hret, hdecomp]
    ring
  have h3s_nat : 3 ^ s = 3 ^ (s - 1) * 3 := by
    have hsub : s = (s - 1) + 1 := by omega
    conv_lhs => rw [hsub, Nat.pow_succ]
  have hpow3 : 3 ^ (s - 1) * (3 * a + 1) = 3 ^ s * a + 3 ^ (s - 1) := by
    rw [h3s_nat]
    ring
  rw [hpow3] at hmul
  have hreal : (2 : ℝ) ^ s * (orbit a s : ℝ) =
      (3 : ℝ) ^ s * (a : ℝ) + (3 : ℝ) ^ (s - 1) := by
    exact_mod_cast hmul
  have h2s : (2 : ℝ) ^ s ≠ 0 := by positivity
  have h3s : (3 : ℝ) ^ (s - 1) * 3 = (3 : ℝ) ^ s := by
    exact_mod_cast h3s_nat.symm
  have h23 : (3 / 2 : ℝ) ^ s * (2 : ℝ) ^ s = (3 : ℝ) ^ s := by
    rw [← mul_pow]
    norm_num
  simp only [orbit, pow_zero, mul_one]
  apply mul_right_cancel₀ h2s
  calc
    (ξ * (3 / 2 : ℝ) ^ s - (orbit a s : ℝ)) * (2 : ℝ) ^ s =
        ξ * ((3 / 2 : ℝ) ^ s * (2 : ℝ) ^ s) - (2 : ℝ) ^ s * (orbit a s : ℝ) := by
          ring
    _ = ξ * (3 : ℝ) ^ s - ((3 : ℝ) ^ s * (a : ℝ) + (3 : ℝ) ^ (s - 1)) := by
          rw [h23, hreal]
    _ = (3 : ℝ) ^ s * (ξ - (a : ℝ)) - ((3 : ℝ) ^ (s - 1) * 3) * (1 / 3) := by
          ring
    _ = (3 : ℝ) ^ s * (ξ - (a : ℝ) - 1 / 3) := by
          rw [h3s]
          ring
    _ = (3 / 2 : ℝ) ^ s * (ξ - (a : ℝ) - 1 / 3) * (2 : ℝ) ^ s := by
          rw [← h23]
          ring

/-- The `s = 2` (`OE`) Fractional Drain Law: when `3a + 1 = 4u` (`u` odd) and
`0 ≤ r_0 < 1/2`, the fractional part drops by more than `1/8` (`r_2 < r_0 - 1/8`
and `r_2 < 3/8`), and after the next odd step at `t = 2`, `r_3 < 1/16`. -/
theorem s_eq_two_fractional_drain {a u : ℕ} (hu : u % 2 = 1)
    (hdecomp : 3 * a + 1 = 2 ^ 2 * u) {ξ : ℝ}
    (h0 : ValidCompanionAt a ξ 0) :
    fracPart a ξ 2 < fracPart a ξ 0 - 1 / 8 ∧
    fracPart a ξ 2 < 3 / 8 ∧
    fracPart a ξ 3 < 1 / 16 := by
  have hr0 := (validCompanionAt_iff_fracPart a ξ 0).mp h0
  have hr2 := fracPart_odd_block (by decide : 1 ≤ 2) hdecomp ξ
  have hodd2 := orbit_odd_block_return_odd (by decide : 1 ≤ 2) hu hdecomp
  have hr3 := fracPart_succ a ξ 2
  rw [hodd2] at hr3
  norm_num at hr2 hr3
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## 4. General `2^N`-Periodicity and the `a ≡ 9 (mod 256)` Bit-Forcing Theorem -/

theorem step_two_mul_add (x y : ℕ) : step (2 * x + y) = 3 * x + step y := by
  unfold step
  omega

/-- Adding `2^N * q` to a starting integer adds `3^n * 2^(N-n) * q` at step `n ≤ N`. -/
theorem orbit_add_two_pow_mul (N q r n : ℕ) (hn : n ≤ N) :
    orbit (2 ^ N * q + r) n = 3 ^ n * 2 ^ (N - n) * q + orbit r n := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      have hn' : n ≤ N := by omega
      have hsub : N - n = (N - (n + 1)) + 1 := by omega
      have hShift :
          3 ^ n * 2 ^ (N - n) * q = 2 * (3 ^ n * 2 ^ (N - (n + 1)) * q) := by
        rw [hsub, Nat.pow_succ]
        ring
      have hstep :
          step (2 * (3 ^ n * 2 ^ (N - (n + 1)) * q) + orbit r n) =
            3 ^ (n + 1) * 2 ^ (N - (n + 1)) * q + step (orbit r n) := by
        rw [step_two_mul_add, Nat.pow_succ]
        ring
      simpa [orbit, ih hn', hShift] using hstep

/-- `carry m j k` depends only on `m mod 2^N` whenever `j + k ≤ N`. -/
theorem carry_mod_two_pow (N m j k : ℕ) (hjk : j + k ≤ N) :
    carry m j k = carry (m % 2 ^ N) j k := by
  let q := m / 2 ^ N
  let r := m % 2 ^ N
  have hm : m = 2 ^ N * q + r := (Nat.div_add_mod m (2 ^ N)).symm
  have hj : orbit m j = 3 ^ j * 2 ^ (N - j) * q + orbit r j := by
    conv_lhs => rw [hm]
    exact orbit_add_two_pow_mul N q r j (by omega)
  have hjk_orb :
      orbit m (j + k) = 3 ^ (j + k) * 2 ^ (N - (j + k)) * q + orbit r (j + k) := by
    conv_lhs => rw [hm]
    exact orbit_add_two_pow_mul N q r (j + k) hjk
  have hcancel :
      2 ^ k * (3 ^ (j + k) * 2 ^ (N - (j + k)) * q) =
        3 ^ k * (3 ^ j * 2 ^ (N - j) * q) := by
    have hsub : N - j = k + (N - (j + k)) := by omega
    rw [hsub, Nat.pow_add, Nat.pow_add]
    ring
  unfold carry
  rw [hj, hjk_orb]
  change 2 ^ k * (3 ^ (j + k) * 2 ^ (N - (j + k)) * q + orbit r (j + k)) -
      3 ^ k * (3 ^ j * 2 ^ (N - j) * q + orbit r j) =
    2 ^ k * orbit r (j + k) - 3 ^ k * orbit r j
  have hdist1 :
      2 ^ k * (3 ^ (j + k) * 2 ^ (N - (j + k)) * q + orbit r (j + k)) =
        2 ^ k * (3 ^ (j + k) * 2 ^ (N - (j + k)) * q) + 2 ^ k * orbit r (j + k) := by
    ring
  have hdist2 :
      3 ^ k * (3 ^ j * 2 ^ (N - j) * q + orbit r j) =
        3 ^ k * (3 ^ j * 2 ^ (N - j) * q) + 3 ^ k * orbit r j := by
    ring
  rw [hdist1, hdist2, hcancel]
  omega

theorem integerPinch_mod_two_pow_iff (N m j k : ℕ) (hjk : j + k ≤ N) :
    IntegerPinch m j k ↔ IntegerPinch (m % 2 ^ N) j k := by
  rw [integerPinch_iff_two_mul_carry_lt, integerPinch_iff_two_mul_carry_lt,
    carry_mod_two_pow N m j k hjk]

/-- General `2^N`-periodicity: whether `m` has a valid real Mahler companion
through step `N` depends only on `m mod 2^N`. -/
theorem exists_validCompanionUpTo_mod_two_pow_iff (m N : ℕ) :
    (∃ ξ : ℝ, ValidCompanionUpTo m ξ N) ↔
      (∃ ξ : ℝ, ValidCompanionUpTo (m % 2 ^ N) ξ N) := by
  rw [exists_validCompanionUpTo_iff_integerPinch,
    exists_validCompanionUpTo_iff_integerPinch]
  constructor <;> intro h j hj
  · exact (integerPinch_mod_two_pow_iff N m j (N - j) (by omega)).mp (h j hj)
  · exact (integerPinch_mod_two_pow_iff N m j (N - j) (by omega)).mpr (h j hj)

/-- Decidable check for `N`-step survival of a starting integer `m`. -/
def survivesSteps (m N : ℕ) : Bool :=
  (List.range (N + 1)).all fun j =>
    decide (2 ^ (N - j + 1) * orbit m N < 3 ^ (N - j) * (2 * orbit m j + 1))

theorem survivesSteps_eq_true_iff (m N : ℕ) :
    survivesSteps m N = true ↔ ∀ j ≤ N, IntegerPinch m j (N - j) := by
  unfold survivesSteps IntegerPinch
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h j hj
    have hlt : j < N + 1 := by omega
    have hsum : j + (N - j) = N := by omega
    simpa [hsum] using h j hlt
  · intro h j hlt
    have hj : j ≤ N := by omega
    have hsum : j + (N - j) = N := by omega
    simpa [hsum] using h j hj

private theorem fin32_s_eq_two_check :
    ∀ k : Fin 32,
      survivesSteps (8 * k.val + 1) 8 = true ↔ k.val = 1 := by
  decide

/-- **The Coupled Bit-Forcing Theorem for `s = 2` Blocks**:
An odd starting integer `a` with `s = v_2(3a + 1) = 2` (equivalently, `a % 8 = 1`)
has a valid real Mahler companion through step `8` if and only if `a % 256 = 9`. -/
theorem s_eq_two_survives_eight_iff_mod_256_eq_9 (a : ℕ) :
    (a % 8 = 1 ∧ ∃ ξ : ℝ, ValidCompanionUpTo a ξ 8) ↔ a % 256 = 9 := by
  rw [exists_validCompanionUpTo_mod_two_pow_iff a 8,
    exists_validCompanionUpTo_iff_integerPinch, ← survivesSteps_eq_true_iff]
  constructor
  · rintro ⟨h8, hsurv⟩
    have hpow : (2 ^ 8 : ℕ) = 256 := by decide
    rw [hpow] at hsurv
    let k := (a % 256) / 8
    have hk_lt : k < 32 := by omega
    have hdecomp : a % 256 = 8 * k + 1 := by omega
    rw [hdecomp] at hsurv
    have hk1 : k = 1 := (fin32_s_eq_two_check ⟨k, hk_lt⟩).mp hsurv
    omega
  · intro h256
    have h8 : a % 8 = 1 := by omega
    refine ⟨h8, ?_⟩
    have hpow : (2 ^ 8 : ℕ) = 256 := by decide
    rw [hpow, h256]
    exact (fin32_s_eq_two_check ⟨1, by decide⟩).mpr rfl

end Mahler.OddBlock
