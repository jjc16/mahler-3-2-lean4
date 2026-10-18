import BridgeTwoBlockDrain

/-!
# Bridge 3: The Mixed Multi-Block Kernel Invariant & Universal Cycle Ceiling

This module formalizes **Bridge 3**, uniting arbitrary sequences of different
odd-to-odd block lengths `s(0), s(1), ..., s(m - 1)` into a single coupled
Diophantine framework:

1. **Cumulative Steps `blockSteps s m` and Kernel Integer `blockKernel s m`**:
   Given any sequence of block lengths `s : ℕ → ℕ`, define
   - `blockSteps s 0 = 0`, `blockSteps s (k + 1) = blockSteps s k + s k`, and
   - `blockKernel s 0 = 0`,
     `blockKernel s (k + 1) = 3^(s k) * blockKernel s k + 2^(blockSteps s k) * 3^(s k - 1)`.
   When `1 ≤ s k` for all `k < m` and `1 ≤ m`, `blockKernel s m` is always **odd**
   (`blockKernel_odd`), so `blockKernel s m > 0`.
2. **Exact Mixed-Block Integer & Carry Identity (`mixed_block_integer_identity`,
   `blockKernel_eq_carry`)**:
   Across any `m` consecutive odd-to-odd blocks of lengths `s 0, ..., s (m - 1)`,
   `2^(blockSteps s m) * orbit a_0 (blockSteps s m) = 3^(blockSteps s m) * a_0 + blockKernel s m`,
   so `blockKernel s m = carry a_0 0 (blockSteps s m)` and
   `2^(blockSteps s m) ∣ (3^(blockSteps s m) * a_0 + blockKernel s m)`.
3. **Parameter-Free Combinatorial Return Pinch (`mixed_block_return_pinch`) and
   Cross-Return Squeeze (`mixed_block_cross_return_squeeze`)**:
   Because `orbit a_0 (blockSteps s m)` is odd, surviving one step past the
   `m`-th return forces the purely combinatorial inequality on `s` alone:
   `6 * blockKernel s m + 2^(blockSteps s m + 1) < 3^(blockSteps s m + 1)`,
   and for any two return indices `i, j`:
   `2 * 3^(blockSteps s j) * (3 * blockKernel s i + 2^(blockSteps s i)) <
     3^(blockSteps s i + 1) * (2 * blockKernel s j + 2^(blockSteps s j))`.
4. **Universal Mixed-Cycle Repetition Ceiling (`mixed_cycle_repeat_bound`)**:
   Across `d` repetitions of **any** mixed block cycle of total step length
   `T ≥ 1` and kernel integer `K ≥ 1` (`2^T * a_{k+1} = 3^T * a_k + K`),
   `2^(T * d) ∣ ((3^T - 2^T) * a_0 + K)` and `2^(T * d) ≤ (3^T - 2^T) * a_0 + K`.
-/

namespace Mahler.BridgeThree

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo

/-! ## 1. Cumulative Steps `blockSteps` and Kernel Integer `blockKernel` -/

/-- Cumulative step count `T(m) = s(0) + ... + s(m - 1)` after `m` odd blocks. -/
def blockSteps (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => blockSteps s k + s k

/-- Mixed-block kernel integer `K(m)` determined purely by the block lengths `s`. -/
def blockKernel (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 ^ (s k) * blockKernel s k + 2 ^ (blockSteps s k) * 3 ^ (s k - 1)

private theorem three_pow_mod_two (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem blockSteps_pos {s : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hs : ∀ k < m, 1 ≤ s k) :
    1 ≤ blockSteps s m := by
  cases m with
  | zero => omega
  | succ m =>
      have h0 : 1 ≤ s m := hs m (by omega)
      simp only [blockSteps]
      omega

theorem blockSteps_mono (s : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    blockSteps s i ≤ blockSteps s j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (by simp [blockSteps])

/-- For every `m ≥ 1` with positive block lengths, `blockKernel s m` is odd. -/
theorem blockKernel_odd {s : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hs : ∀ k < m, 1 ≤ s k) :
    blockKernel s m % 2 = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          simp only [blockKernel, blockSteps, pow_zero, one_mul, zero_add,
            Nat.mul_zero]
          exact three_pow_mod_two (s 0 - 1)
      | succ m =>
          have ihm : blockKernel s (m + 1) % 2 = 1 :=
            ih (by omega) (fun k hk => hs k (by omega))
          have hT : 1 ≤ blockSteps s (m + 1) :=
            blockSteps_pos (by omega) (fun k hk => hs k (by omega))
          have heven : (2 ^ (blockSteps s (m + 1)) * 3 ^ (s (m + 1) - 1)) % 2 = 0 := by
            have hsub : blockSteps s (m + 1) = (blockSteps s (m + 1) - 1) + 1 := by omega
            rw [hsub, Nat.pow_succ]
            have : 2 ^ (blockSteps s (m + 1) - 1) * 2 * 3 ^ (s (m + 1) - 1) =
                2 * (2 ^ (blockSteps s (m + 1) - 1) * 3 ^ (s (m + 1) - 1)) := by ring
            rw [this]
            omega
          have hodd : (3 ^ (s (m + 1)) * blockKernel s (m + 1)) % 2 = 1 := by
            rw [Nat.mul_mod, three_pow_mod_two, ihm]
          rw [show blockKernel s (m + 1 + 1) =
              3 ^ (s (m + 1)) * blockKernel s (m + 1) +
                2 ^ (blockSteps s (m + 1)) * 3 ^ (s (m + 1) - 1) from rfl,
            Nat.add_mod, hodd, heven]

/-! ## 2. Exact Mixed-Block Integer, Carry, and Fractional Identities -/

/-- Predicate asserting that starting from `a_0`, the first `m` odd-to-odd
blocks have lengths `s 0, ..., s (m - 1)` with odd quotients `u 0, ..., u (m - 1)`. -/
def ValidBlockChain (a_0 : ℕ) (s u : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ k < m,
    1 ≤ s k ∧
    u k % 2 = 1 ∧
    3 * orbit a_0 (blockSteps s k) + 1 = 2 ^ (s k) * u k

/-- Single-block integer step equation: `2^s * orbit b s = 3^s * b + 3^(s - 1)`. -/
theorem single_odd_block_linear_eq {b s u : ℕ} (hs : 1 ≤ s)
    (hdecomp : 3 * b + 1 = 2 ^ s * u) :
    2 ^ s * orbit b s = 3 ^ s * b + 3 ^ (s - 1) := by
  have hret := orbit_odd_block_return hs hdecomp
  have hmul : 2 ^ s * orbit b s = 3 ^ (s - 1) * (3 * b + 1) := by
    rw [hret, hdecomp]
    ring
  have h3s : 3 ^ (s - 1) * 3 = 3 ^ s := by
    have hsub : s = (s - 1) + 1 := by omega
    conv_rhs => rw [hsub, Nat.pow_succ]
  rw [hmul]
  calc
    3 ^ (s - 1) * (3 * b + 1) = (3 ^ (s - 1) * 3) * b + 3 ^ (s - 1) := by ring
    _ = 3 ^ s * b + 3 ^ (s - 1) := by rw [h3s]

/-- **The Mixed-Block Integer Identity**:
Across any valid chain of `m` odd-to-odd blocks from `a_0`,
`2^(blockSteps s m) * orbit a_0 (blockSteps s m) = 3^(blockSteps s m) * a_0 + blockKernel s m`. -/
theorem mixed_block_integer_identity {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u m) :
    2 ^ (blockSteps s m) * orbit a_0 (blockSteps s m) =
      3 ^ (blockSteps s m) * a_0 + blockKernel s m := by
  induction m with
  | zero => simp [blockSteps, blockKernel, orbit]
  | succ m ih =>
      have ih' := ih (fun k hk => hchain k (by omega))
      rcases hchain m (by omega) with ⟨hsm, _, hdecomp⟩
      have hsingle := single_odd_block_linear_eq hsm hdecomp
      rw [← orbit_add a_0 (blockSteps s m) (s m)] at hsingle
      calc
        2 ^ (blockSteps s (m + 1)) * orbit a_0 (blockSteps s (m + 1)) =
            2 ^ (blockSteps s m) *
              (2 ^ (s m) * orbit a_0 (blockSteps s m + s m)) := by
              simp only [blockSteps, Nat.pow_add]
              ring
        _ = 2 ^ (blockSteps s m) *
              (3 ^ (s m) * orbit a_0 (blockSteps s m) + 3 ^ (s m - 1)) := by
              rw [hsingle]
        _ = 3 ^ (s m) * (2 ^ (blockSteps s m) * orbit a_0 (blockSteps s m)) +
              2 ^ (blockSteps s m) * 3 ^ (s m - 1) := by
              ring
        _ = 3 ^ (s m) * (3 ^ (blockSteps s m) * a_0 + blockKernel s m) +
              2 ^ (blockSteps s m) * 3 ^ (s m - 1) := by
              rw [ih']
        _ = 3 ^ (blockSteps s (m + 1)) * a_0 + blockKernel s (m + 1) := by
              simp only [blockSteps, blockKernel, Nat.pow_add]
              ring

/-- `blockKernel s m` is identically equal to the multi-step carry `carry a_0 0 (blockSteps s m)`. -/
theorem blockKernel_eq_carry {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u m) :
    blockKernel s m = carry a_0 0 (blockSteps s m) := by
  have hid := mixed_block_integer_identity hchain
  have hc := two_pow_mul_orbit_eq_add_carry a_0 0 (blockSteps s m)
  simp only [orbit, Nat.zero_add] at hc
  omega

/-- Every valid `m`-block chain imposes the exact 2-adic congruence
`2^(blockSteps s m) ∣ (3^(blockSteps s m) * a_0 + blockKernel s m)`. -/
theorem mixed_block_two_pow_dvd {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u m) :
    2 ^ (blockSteps s m) ∣ (3 ^ (blockSteps s m) * a_0 + blockKernel s m) :=
  ⟨orbit a_0 (blockSteps s m), (mixed_block_integer_identity hchain).symm⟩

/-- At the end of a valid `m`-block chain (`m ≥ 1`), `orbit a_0 (blockSteps s m)` is odd. -/
theorem mixed_block_return_odd {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hchain : ValidBlockChain a_0 s u m) :
    orbit a_0 (blockSteps s m) % 2 = 1 := by
  cases m with
  | zero => omega
  | succ m =>
      rcases hchain m (by omega) with ⟨hsm, hum, hdecomp⟩
      simp only [blockSteps]
      rw [orbit_add]
      exact orbit_odd_block_return_odd hsm hum hdecomp

/-- **The Mixed-Block Fractional Identity**:
`2^(blockSteps s m) * fracPart a_0 ξ (blockSteps s m) =
  3^(blockSteps s m) * fracPart a_0 ξ 0 - blockKernel s m`. -/
theorem mixed_block_fracPart_identity {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ}
    (hchain : ValidBlockChain a_0 s u m) (ξ : ℝ) :
    (2 : ℝ) ^ (blockSteps s m) * fracPart a_0 ξ (blockSteps s m) =
      (3 : ℝ) ^ (blockSteps s m) * fracPart a_0 ξ 0 - (blockKernel s m : ℝ) := by
  rw [two_pow_mul_fracPart_eq, ← blockKernel_eq_carry hchain]

/-! ## 3. Parameter-Free Combinatorial Return Pinch & Cross-Return Squeeze -/

/-- **Parameter-Free Combinatorial Return Pinch**:
If any starting integer `a_0` realizes the block sequence `s(0), ..., s(m - 1)`
(`m ≥ 1`) and survives through step `blockSteps s m + 1`, then `s` must satisfy
`6 * blockKernel s m + 2^(blockSteps s m + 1) < 3^(blockSteps s m + 1)`. -/
theorem mixed_block_return_pinch {a_0 : ℕ} {s u : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hchain : ValidBlockChain a_0 s u m) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + 1)) :
    6 * blockKernel s m + 2 ^ (blockSteps s m + 1) <
      3 ^ (blockSteps s m + 1) := by
  have hodd : orbit a_0 (blockSteps s m) % 2 = 1 :=
    mixed_block_return_odd hm hchain
  have hpinch : IntegerPinch a_0 0 (blockSteps s m + 1 - 0) :=
    (exists_validCompanionUpTo_iff_integerPinch a_0 (blockSteps s m + 1)).mp
      ⟨ξ, hsurv⟩ 0 (by omega)
  have hcarry_lt : 2 * carry a_0 0 (blockSteps s m + 1) < 3 ^ (blockSteps s m + 1) :=
    (integerPinch_iff_two_mul_carry_lt a_0 0 (blockSteps s m + 1)).mp
      (by simpa using hpinch)
  have hcs := carry_succ a_0 0 (blockSteps s m)
  simp only [Nat.zero_add, hodd, Nat.mul_one] at hcs
  rw [← blockKernel_eq_carry hchain] at hcs
  have hpow : 2 * 2 ^ (blockSteps s m) = 2 ^ (blockSteps s m + 1) := by ring
  omega

/-- **Cross-Return Diophantine Squeeze**:
For any two return indices `1 ≤ i ≤ m` and `0 ≤ j ≤ m` along a valid block
chain surviving through `blockSteps s m + 1`, the kernel integers at `i` and
`j` must satisfy:
`2 * 3^(blockSteps s j) * (3 * blockKernel s i + 2^(blockSteps s i)) <
  3^(blockSteps s i + 1) * (2 * blockKernel s j + 2^(blockSteps s j))`. -/
theorem mixed_block_cross_return_squeeze {a_0 : ℕ} {s u : ℕ → ℕ} {m i j : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ m) (hjm : j ≤ m)
    (hchain : ValidBlockChain a_0 s u m) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + 1)) :
    2 * 3 ^ (blockSteps s j) * (3 * blockKernel s i + 2 ^ (blockSteps s i)) <
      3 ^ (blockSteps s i + 1) * (2 * blockKernel s j + 2 ^ (blockSteps s j)) := by
  have hchain_i : ValidBlockChain a_0 s u i := fun k hk => hchain k (by omega)
  have hchain_j : ValidBlockChain a_0 s u j := fun k hk => hchain k (by omega)
  have hTi_le : blockSteps s i ≤ blockSteps s m := blockSteps_mono s him
  have hTj_le : blockSteps s j ≤ blockSteps s m := blockSteps_mono s hjm
  have hodd_i : orbit a_0 (blockSteps s i) % 2 = 1 :=
    mixed_block_return_odd hi1 hchain_i
  have hr_i_lo : (1 / 3 : ℝ) ≤ fracPart a_0 ξ (blockSteps s i) :=
    (even_odd_step_straddles_one_third (blockSteps s i)
      (hsurv (blockSteps s i) (by omega))
      (hsurv (blockSteps s i + 1) (by omega))).2 hodd_i
  have hr_j_hi : fracPart a_0 ξ (blockSteps s j) < 1 / 2 :=
    ((validCompanionAt_iff_fracPart a_0 ξ (blockSteps s j)).mp
      (hsurv (blockSteps s j) (by omega))).2
  have hid_i := mixed_block_fracPart_identity hchain_i ξ
  have hid_j := mixed_block_fracPart_identity hchain_j ξ
  have h2Ti : (0 : ℝ) < (2 : ℝ) ^ (blockSteps s i) := by positivity
  have h2Tj : (0 : ℝ) < (2 : ℝ) ^ (blockSteps s j) := by positivity
  have hr_i_scaled := mul_le_mul_of_nonneg_left hr_i_lo (le_of_lt h2Ti)
  have hr_j_scaled := mul_lt_mul_of_pos_left hr_j_hi h2Tj
  have hlo_r0 :
      (3 * (blockKernel s i : ℝ) + (2 : ℝ) ^ (blockSteps s i)) ≤
        3 * (3 : ℝ) ^ (blockSteps s i) * fracPart a_0 ξ 0 := by
    linarith [hr_i_scaled, hid_i]
  have hhi_r0 :
      2 * (3 : ℝ) ^ (blockSteps s j) * fracPart a_0 ξ 0 <
        2 * (blockKernel s j : ℝ) + (2 : ℝ) ^ (blockSteps s j) := by
    linarith [hr_j_scaled, hid_j]
  have hcross_real :
      2 * (3 : ℝ) ^ (blockSteps s j) *
          (3 * (blockKernel s i : ℝ) + (2 : ℝ) ^ (blockSteps s i)) <
        (3 : ℝ) ^ (blockSteps s i + 1) *
          (2 * (blockKernel s j : ℝ) + (2 : ℝ) ^ (blockSteps s j)) := by
    have hm1 := mul_le_mul_of_nonneg_left hlo_r0 (by positivity : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ (blockSteps s j))
    have hm2 := mul_lt_mul_of_pos_left hhi_r0 (by positivity : (0 : ℝ) < 3 * (3 : ℝ) ^ (blockSteps s i))
    rw [pow_succ]
    linarith
  exact_mod_cast hcross_real

/-! ## 4. The Universal Mixed-Cycle Repetition Ceiling -/

/-- Single macro-cycle fixed-point identity for ANY step length `T ≥ 1` and
kernel integer `K`: if `2^T * a' = 3^T * a + K`, then
`2^T * ((3^T - 2^T) * a' + K) = 3^T * ((3^T - 2^T) * a + K)`. -/
theorem mixed_cycle_fixed_point {a a' T K : ℕ}
    (hstep : 2 ^ T * a' = 3 ^ T * a + K) :
    2 ^ T * ((3 ^ T - 2 ^ T) * a' + K) =
      3 ^ T * ((3 ^ T - 2 ^ T) * a + K) := by
  have hle : 2 ^ T ≤ 3 ^ T := Nat.pow_le_pow_left (by decide) T
  calc
    2 ^ T * ((3 ^ T - 2 ^ T) * a' + K) =
        (3 ^ T - 2 ^ T) * (2 ^ T * a') + 2 ^ T * K := by ring
    _ = (3 ^ T - 2 ^ T) * (3 ^ T * a + K) + 2 ^ T * K := by rw [hstep]
    _ = 3 ^ T * ((3 ^ T - 2 ^ T) * a) + ((3 ^ T - 2 ^ T) * K + 2 ^ T * K) := by ring
    _ = 3 ^ T * ((3 ^ T - 2 ^ T) * a) + ((3 ^ T - 2 ^ T + 2 ^ T) * K) := by
          rw [Nat.add_mul]
    _ = 3 ^ T * ((3 ^ T - 2 ^ T) * a + K) := by
          rw [Nat.sub_add_cancel hle]
          ring

/-- Iterated macro-cycle fixed-point identity across `d` repetitions of any
mixed block pattern `(T, K)`. -/
theorem mixed_cycle_chain_fixed_point {T K : ℕ} (a : ℕ → ℕ) (d : ℕ)
    (hstep : ∀ k < d, 2 ^ T * a (k + 1) = 3 ^ T * a k + K) :
    2 ^ (T * d) * ((3 ^ T - 2 ^ T) * a d + K) =
      3 ^ (T * d) * ((3 ^ T - 2 ^ T) * a 0 + K) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have ih' := ih (fun k hk => hstep k (by omega))
      have hsingle := mixed_cycle_fixed_point (hstep d (by omega))
      calc
        2 ^ (T * (d + 1)) * ((3 ^ T - 2 ^ T) * a (d + 1) + K) =
            2 ^ (T * d) * (2 ^ T * ((3 ^ T - 2 ^ T) * a (d + 1) + K)) := by
              rw [Nat.mul_succ, Nat.pow_add]
              ring
        _ = 2 ^ (T * d) * (3 ^ T * ((3 ^ T - 2 ^ T) * a d + K)) := by
              rw [hsingle]
        _ = 3 ^ T * (2 ^ (T * d) * ((3 ^ T - 2 ^ T) * a d + K)) := by ring
        _ = 3 ^ T * (3 ^ (T * d) * ((3 ^ T - 2 ^ T) * a 0 + K)) := by rw [ih']
        _ = 3 ^ (T * (d + 1)) * ((3 ^ T - 2 ^ T) * a 0 + K) := by
              rw [Nat.mul_succ, Nat.pow_add]
              ring

/-- **The Universal Mixed-Cycle Repetition Ceiling (`mixed_cycle_repeat_bound`)**:
If an integer trajectory `a 0, a 1, ..., a d` repeats ANY mixed block pattern of
total step length `T` and positive kernel `K > 0` (`2^T * a (k + 1) = 3^T * a k + K`
for all `k < d`), then `2^(T * d)` divides `(3^T - 2^T) * a 0 + K` and
consequently `2^(T * d) ≤ (3^T - 2^T) * a 0 + K`. -/
theorem mixed_cycle_repeat_bound {T K : ℕ} (hK : 0 < K) (a : ℕ → ℕ) (d : ℕ)
    (hstep : ∀ k < d, 2 ^ T * a (k + 1) = 3 ^ T * a k + K) :
    2 ^ (T * d) ∣ ((3 ^ T - 2 ^ T) * a 0 + K) ∧
      2 ^ (T * d) ≤ (3 ^ T - 2 ^ T) * a 0 + K := by
  have hchain := mixed_cycle_chain_fixed_point a d hstep
  have hd : 2 ^ (T * d) ∣ 3 ^ (T * d) * ((3 ^ T - 2 ^ T) * a 0 + K) := by
    rw [← hchain]
    exact Nat.dvd_mul_right _ _
  have hg : Nat.gcd (2 ^ (T * d)) (3 ^ (T * d)) = 1 :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)
  have hdvd : 2 ^ (T * d) ∣ ((3 ^ T - 2 ^ T) * a 0 + K) := by
    have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
    simpa only [hg, Nat.one_mul] using hc
  have hpos : 0 < (3 ^ T - 2 ^ T) * a 0 + K := by omega
  exact ⟨hdvd, Nat.le_of_dvd hpos hdvd⟩

end Mahler.BridgeThree
