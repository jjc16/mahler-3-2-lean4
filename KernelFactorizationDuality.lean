import ShiftInvariantSlack

/-!
# Kernel Factorization, `v_3(K(m+1)) = s(m) - 1`, and the `2 Q + Δ = 3^(T+1)` Duality

This module formalizes the exact factorization of the mixed-block kernel
`blockKernel s (m + 1)` and its duality with `integerSlack s m`:

1. **The Coprime Kernel Quotient `kernelQuotient s m` & Exact Kernel Factorization
   (`blockKernel_succ_eq_three_pow_mul`)**:
   Define `kernelQuotient s m = 3^(blockSteps s m) + 2^(s 0) * coprimeRemainder s m`.
   Whenever `1 ≤ s k` for all `k ≤ m`,
   `blockKernel s (m + 1) = 3^(s m - 1) * kernelQuotient s m`.
2. **Exact 3-adic Valuation of `blockKernel s (m + 1)` (`kernelQuotient_not_three_dvd`,
   `blockKernel_three_pow_valuation`)**:
   Because `coprimeRemainder s m` is never divisible by `3` for `m ≥ 1`,
   `kernelQuotient s m` is never divisible by `3` (`¬ (3 ∣ kernelQuotient s m)`).
   Thus the exact 3-adic valuation of `blockKernel s (m + 1)` is `s m - 1`:
   `3^(s m - 1) ∣ blockKernel s (m + 1)` and `¬ (3^(s m) ∣ blockKernel s (m + 1))`.
3. **The Universal Conservation Law (`two_mul_kernelQuotient_add_slack`)**:
   For every sequence `s` and index `m`:
   `2 * (kernelQuotient s m : ℤ) + integerSlack s m = 3^(blockSteps s m + 1)`.
4. **Direct `a_0`-to-`u(m)` Identity & Simultaneous Base-3 Recovery
   (`two_pow_mul_u_eq_a0_add_kernelQuotient`, `a0_and_kernelQuotient_div_mod_recovery`)**:
   Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`),
   `2^(blockSteps s (m + 1)) * u m = 3^(blockSteps s m + 1) * a_0 + kernelQuotient s m`.
   Whenever `0 < integerSlack s m` (which holds along every surviving trajectory),
   `2 * kernelQuotient s m < 3^(blockSteps s m + 1)`, so dividing
   `2^(blockSteps s (m + 1)) * u m` by `3^(blockSteps s m + 1)` recovers
   quotient `a_0` and remainder `kernelQuotient s m`.
-/

namespace Mahler.KernelDuality

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

/-! ## 1. `kernelQuotient` and the Exact Factorization of `blockKernel` -/

/-- The coprime kernel quotient `Q(s, m) = 3^T(m) + 2^(s 0) * R(s, m)`. -/
def kernelQuotient (s : ℕ → ℕ) (m : ℕ) : ℕ :=
  3 ^ (blockSteps s m) + 2 ^ (s 0) * coprimeRemainder s m

/-- **The Exact Kernel Factorization Theorem (`blockKernel_succ_eq_three_pow_mul`)**:
Whenever `1 ≤ s k` for all `k ≤ m`,
`blockKernel s (m + 1) = 3^(s m - 1) * kernelQuotient s m`. -/
theorem blockKernel_succ_eq_three_pow_mul {s : ℕ → ℕ} {m : ℕ}
    (hs : ∀ k ≤ m, 1 ≤ s k) :
    blockKernel s (m + 1) = 3 ^ (s m - 1) * kernelQuotient s m := by
  induction m with
  | zero =>
      simp [blockKernel, kernelQuotient, blockSteps, coprimeRemainder]
  | succ m ih =>
      have ihm := ih (fun k hk => hs k (by omega))
      have hsm : 1 ≤ s m := hs m (by omega)
      have hsm1 : 1 ≤ s (m + 1) := hs (m + 1) (by omega)
      have hpow3_swap :
          3 ^ (s (m + 1)) * 3 ^ (s m - 1) =
            3 ^ (s (m + 1) - 1) * 3 ^ (s m) := by
        have h1 : s (m + 1) = (s (m + 1) - 1) + 1 := by omega
        have h2 : s m = (s m - 1) + 1 := by omega
        conv_lhs => rw [h1, Nat.pow_succ]
        conv_rhs => rw [h2, Nat.pow_succ]
        ring
      have hsteps2 :
          2 ^ (blockSteps s (m + 1)) =
            2 ^ (s 0) * 2 ^ (tailSteps s m) := by
        rw [← add_tailSteps_eq_blockSteps_succ s m, Nat.pow_add]
      calc
        blockKernel s (m + 2) =
            3 ^ (s (m + 1)) * blockKernel s (m + 1) +
              2 ^ (blockSteps s (m + 1)) * 3 ^ (s (m + 1) - 1) := rfl
        _ = (3 ^ (s (m + 1)) * 3 ^ (s m - 1)) * kernelQuotient s m +
              (2 ^ (s 0) * 2 ^ (tailSteps s m)) * 3 ^ (s (m + 1) - 1) := by
              rw [ihm, hsteps2]
              ring
        _ = 3 ^ (s (m + 1) - 1) *
              (3 ^ (s m) * kernelQuotient s m + 2 ^ (s 0) * 2 ^ (tailSteps s m)) := by
              rw [hpow3_swap]
              ring
        _ = 3 ^ (s (m + 1) - 1) * kernelQuotient s (m + 1) := by
              unfold kernelQuotient
              simp only [blockSteps, coprimeRemainder, Nat.pow_add]
              ring

/-! ## 2. Exact 3-adic Valuation of `blockKernel s (m + 1)` -/

private theorem two_pow_mod_three_ne_zero (n : ℕ) : 2 ^ n % 3 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      omega

/-- For `m ≥ 1` with `1 ≤ s k` (`k < m`), `coprimeRemainder s m` is not divisible by `3`. -/
theorem coprimeRemainder_mod_three_ne_zero {s : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hs : ∀ k < m, 1 ≤ s k) :
    coprimeRemainder s m % 3 ≠ 0 := by
  cases m with
  | zero => omega
  | succ m =>
      have hsm : 1 ≤ s m := hs m (by omega)
      have h3div : (3 ^ (s m) * coprimeRemainder s m) % 3 = 0 := by
        have hsub : s m = (s m - 1) + 1 := by omega
        rw [hsub, Nat.pow_succ]
        have : 3 ^ (s m - 1) * 3 * coprimeRemainder s m =
            3 * (3 ^ (s m - 1) * coprimeRemainder s m) := by ring
        rw [this]
        omega
      have h2ne : 2 ^ (tailSteps s m) % 3 ≠ 0 :=
        two_pow_mod_three_ne_zero (tailSteps s m)
      change (3 ^ (s m) * coprimeRemainder s m + 2 ^ (tailSteps s m)) % 3 ≠ 0
      rw [Nat.add_mod, h3div]
      omega

/-- For every `m` with `1 ≤ s k` (`k < m`), `kernelQuotient s m` is not divisible by `3`. -/
theorem kernelQuotient_not_three_dvd {s : ℕ → ℕ} {m : ℕ}
    (hs : ∀ k < m, 1 ≤ s k) :
    ¬ (3 ∣ kernelQuotient s m) := by
  intro hdvd
  have hmod0 : kernelQuotient s m % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  unfold kernelQuotient at hmod0
  cases m with
  | zero =>
      simp [blockSteps, coprimeRemainder] at hmod0
  | succ m =>
      have hT : 1 ≤ blockSteps s (m + 1) := blockSteps_pos (by omega) hs
      have h3div : 3 ^ (blockSteps s (m + 1)) % 3 = 0 := by
        have hsub : blockSteps s (m + 1) = (blockSteps s (m + 1) - 1) + 1 := by omega
        rw [hsub, Nat.pow_succ]
        omega
      have h2ne : 2 ^ (s 0) % 3 ≠ 0 := two_pow_mod_three_ne_zero (s 0)
      have hRne : coprimeRemainder s (m + 1) % 3 ≠ 0 :=
        coprimeRemainder_mod_three_ne_zero (by omega) hs
      have h2cases : 2 ^ (s 0) % 3 = 1 ∨ 2 ^ (s 0) % 3 = 2 := by omega
      rcases h2cases with h2_1 | h2_2 <;>
        rw [Nat.add_mod, h3div, Nat.mul_mod] at hmod0
      · rw [h2_1] at hmod0
        omega
      · rw [h2_2] at hmod0
        omega

/-- **Exact 3-adic Valuation of `blockKernel s (m + 1)` (`blockKernel_three_pow_valuation`)**:
Whenever `1 ≤ s k` for all `k ≤ m`, `3^(s m - 1)` divides `blockKernel s (m + 1)`
and `3^(s m)` does not. -/
theorem blockKernel_three_pow_valuation {s : ℕ → ℕ} {m : ℕ}
    (hs : ∀ k ≤ m, 1 ≤ s k) :
    3 ^ (s m - 1) ∣ blockKernel s (m + 1) ∧
      ¬ (3 ^ (s m) ∣ blockKernel s (m + 1)) := by
  rw [blockKernel_succ_eq_three_pow_mul hs]
  refine ⟨⟨kernelQuotient s m, rfl⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hsm : 1 ≤ s m := hs m (by omega)
  have hsub : s m = (s m - 1) + 1 := by omega
  have hpow : 3 ^ (s m) * q = 3 ^ (s m - 1) * (3 * q) := by
    conv_lhs => rw [hsub, Nat.pow_succ]
    ring
  rw [hpow] at hq
  have hpos : 0 < 3 ^ (s m - 1) := Nat.pow_pos (by decide)
  have hQ : kernelQuotient s m = 3 * q := Nat.eq_of_mul_eq_mul_left hpos hq
  exact kernelQuotient_not_three_dvd (fun k hk => hs k (by omega)) ⟨q, hQ⟩

/-! ## 3. The Conservation Law `2 Q + Δ = 3^(T + 1)` and Direct `a_0` Recovery -/

/-- **Universal Conservation Law (`two_mul_kernelQuotient_add_slack`)**:
`2 * (kernelQuotient s m : ℤ) + integerSlack s m = 3^(blockSteps s m + 1)`. -/
theorem two_mul_kernelQuotient_add_slack (s : ℕ → ℕ) (m : ℕ) :
    2 * (kernelQuotient s m : ℤ) + integerSlack s m =
      (3 : ℤ) ^ (blockSteps s m + 1) := by
  unfold kernelQuotient integerSlack
  push_cast
  rw [pow_succ, pow_succ]
  ring

/-- Direct identity relating `u m`, `a_0`, and `kernelQuotient s m`:
`2^(blockSteps s (m + 1)) * u m = 3^(blockSteps s m + 1) * a_0 + kernelQuotient s m`. -/
theorem two_pow_mul_u_eq_a0_add_kernelQuotient {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (blockSteps s (m + 1)) * u m =
      3 ^ (blockSteps s m + 1) * a_0 + kernelQuotient s m := by
  have hid := mixed_block_integer_identity
    (m := m + 1) (fun k hk => hchain k (by omega))
  rcases hchain m hmK with ⟨hsm, _, hdecomp_m⟩
  have hret :
      orbit a_0 (blockSteps s (m + 1)) = 3 ^ (s m - 1) * u m := by
    simp only [blockSteps]
    rw [orbit_add]
    exact orbit_odd_block_return hsm hdecomp_m
  have hK_fact :
      blockKernel s (m + 1) = 3 ^ (s m - 1) * kernelQuotient s m :=
    blockKernel_succ_eq_three_pow_mul (fun k hk => (hchain k (by omega)).1)
  have hpow3 :
      3 ^ (blockSteps s (m + 1)) =
        3 ^ (s m - 1) * 3 ^ (blockSteps s m + 1) := by
    have hsum : blockSteps s (m + 1) = (s m - 1) + (blockSteps s m + 1) := by
      simp only [blockSteps]
      omega
    rw [hsum, Nat.pow_add]
  rw [hret, hK_fact, hpow3] at hid
  have hmul :
      3 ^ (s m - 1) * (2 ^ (blockSteps s (m + 1)) * u m) =
        3 ^ (s m - 1) * (3 ^ (blockSteps s m + 1) * a_0 + kernelQuotient s m) := by
    calc
      3 ^ (s m - 1) * (2 ^ (blockSteps s (m + 1)) * u m) =
          2 ^ (blockSteps s (m + 1)) * (3 ^ (s m - 1) * u m) := by ring
      _ = 3 ^ (s m - 1) * 3 ^ (blockSteps s m + 1) * a_0 +
            3 ^ (s m - 1) * kernelQuotient s m := hid
      _ = 3 ^ (s m - 1) *
            (3 ^ (blockSteps s m + 1) * a_0 + kernelQuotient s m) := by ring
  have hpos : 0 < 3 ^ (s m - 1) := Nat.pow_pos (by decide)
  exact Nat.eq_of_mul_eq_mul_left hpos hmul

/-- **Simultaneous Quotient & Remainder Recovery of `a_0` and `kernelQuotient s m`
(`a0_and_kernelQuotient_div_mod_recovery`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` (`m < K`) with
`0 < integerSlack s m` (which holds whenever `a_0` survives to step `blockSteps s (m + 1)`),
dividing `2^(blockSteps s (m + 1)) * u m` by `3^(blockSteps s m + 1)` recovers
quotient `a_0` and remainder `kernelQuotient s m` (with `2 * kernelQuotient s m < 3^(blockSteps s m + 1)`). -/
theorem a0_and_kernelQuotient_div_mod_recovery {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s m) :
    2 * kernelQuotient s m < 3 ^ (blockSteps s m + 1) ∧
    (2 ^ (blockSteps s (m + 1)) * u m) / 3 ^ (blockSteps s m + 1) = a_0 ∧
    (2 ^ (blockSteps s (m + 1)) * u m) % 3 ^ (blockSteps s m + 1) = kernelQuotient s m := by
  have hcons := two_mul_kernelQuotient_add_slack s m
  have h2Q_real :
      ((2 * kernelQuotient s m : ℕ) : ℤ) <
        ((3 ^ (blockSteps s m + 1) : ℕ) : ℤ) := by
    push_cast
    linarith
  have h2Q : 2 * kernelQuotient s m < 3 ^ (blockSteps s m + 1) := by
    exact_mod_cast h2Q_real
  have hQ_lt : kernelQuotient s m < 3 ^ (blockSteps s m + 1) := by omega
  have hid := two_pow_mul_u_eq_a0_add_kernelQuotient hmK hchain
  have hpos : 0 < 3 ^ (blockSteps s m + 1) := Nat.pow_pos (by decide)
  have hdiv : (2 ^ (blockSteps s (m + 1)) * u m) / 3 ^ (blockSteps s m + 1) = a_0 := by
    apply Nat.le_antisymm
    · have hhi :
          2 ^ (blockSteps s (m + 1)) * u m <
            (a_0 + 1) * 3 ^ (blockSteps s m + 1) := by
        rw [hid]
        have : (a_0 + 1) * 3 ^ (blockSteps s m + 1) =
            3 ^ (blockSteps s m + 1) * a_0 + 3 ^ (blockSteps s m + 1) := by ring
        omega
      exact (Nat.div_lt_iff_lt_mul hpos).mpr hhi |> Nat.le_of_lt_succ
    · have hlo :
          a_0 * 3 ^ (blockSteps s m + 1) ≤
            2 ^ (blockSteps s (m + 1)) * u m := by
        rw [hid]
        have : a_0 * 3 ^ (blockSteps s m + 1) =
            3 ^ (blockSteps s m + 1) * a_0 := by ring
        omega
      exact (Nat.le_div_iff_mul_le hpos).mpr hlo
  have hdm := Nat.div_add_mod (2 ^ (blockSteps s (m + 1)) * u m) (3 ^ (blockSteps s m + 1))
  rw [hdiv] at hdm
  exact ⟨h2Q, hdiv, by omega⟩

end Mahler.KernelDuality
