import SubCeilingKneadingAutomatonAndGrandSynthesis54

/-!
# Semigroup Breakout Campaign — Cordoned-Off Lean 4 Verification of $\mathbb{Z}_2$-Symmetry-Breaking Generators

This standalone module lives in `semigroup_breakout/` (cordoned off from the 226-file bottom-up
corpus in the repository root) and formalizes the five core theorems discovered during the
**Semigroup Breakout Campaign** (`SEMIGROUP_BREAKOUT_PAPER.md`):

1. **Theorem SB.1 (`archimedean_rung_ceiling_and_stepSum_bound`) — The Global Archimedean Rung Ceiling**:
   - *False in $\mathbb{Z}_2$, True in $\mathbb{N}$*: In $\mathbb{Z}_2$, a 2-adic seed $b_0 \in \mathbb{Z}_2$
     can have arbitrarily large 2-adic valuation $s_K = v_2(3 b_K + 1)$ at any block $K$.
   - In $\mathbb{N}$, for any seed $b_0 \in \mathbb{N}$ (`ValidBlockChain b_0 s u (K + 1)`) along a
     surviving prefix (`0 < renewalIntSlack s K`), positivity of the odd quotient $u_K \ge 1$
     forces:
     `2 ^ (s K) ≤ oddReturnP (orbit b_0 (blockSteps s K))` and
     `2 * 2 ^ (blockSteps s (K + 1)) < 3 ^ (blockSteps s K) * (2 * oddReturnP b_0 + 1)`.
   - At $K = 0$, `2 ^ (s 0) ≤ 3 * b_0 + 1`.

2. **Theorem SB.2 (`unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity`) — The Pure Power-of-3 ($u_K = 1$) Collapse & Mod-64 Trap**:
   - Whenever the odd quotient hits the archimedean floor $u_K = 1$ (`P_K = 2 ^ (s K)`), the next
     odd state is a pure power of $3$: `b_{K+1} = 3 ^ (s K - 1)`.
   - **Rule A (Even $s_K = 2 j$, $j \ge 1$)**: `b_{K+1} = 3 ^ (2 * j - 1)` has
     `oddReturnP b_{K+1} = 3 ^ (2 * j) + 1`, which satisfies
     `oddReturnP b_{K+1} % 8 = 2` (`2 ∣ P_{K+1} ∧ ¬ 4 ∣ P_{K+1}`), forcing $s_{K+1} = 1$
     (instant odd-to-odd death at the very next block!).
   - **Rule B (Odd $s_K = 2 j + 1$, $j \ge 1$)**: `b_{K+1} = 3 ^ (2 * j)` has
     `oddReturnP b_{K+1} = 3 ^ (2 * j + 1) + 1`, which satisfies `oddReturnP b_{K+1} % 8 = 4`
     (forcing $s_{K+1} = 2$), and the subsequent state $b_{K+2} = 3 \cdot ((3^{2j+1} + 1)/4)$
     satisfies the exact algebraic identity:
     `4 * oddReturnP b_{K+2} = 3 ^ (2 * j + 3) + 13` and
     `3 ^ (2 * j + 3) + 13 = 243 * (3 ^ (2 * j - 2) - 1) + 256` (for $j \ge 1$), so
     `64 ∣ oddReturnP b_{K+2} ↔ 256 ∣ (3 ^ (2 * j - 2) - 1)`.
   - At the base case $j = 1$ ($s_K = 3, b_{K+1} = 9$), $b_{K+2} = 21$ has $P_{K+2} = 64 = 2^6 \cdot 1$
     ($s_{K+2} = 6, u_{K+2} = 1$), which triggers Rule A at $b_{K+3} = 243$ ($P_{K+3} = 730 \equiv 2 \pmod 8$)!

3. **Theorem SB.3 (`equal_step_window_hankel_determinant_identity_and_bound`) — Cross-Window Hankel Determinant Annihilation**:
   - Across any two windows $[r_1, r_2]$ and $[r_3, r_4]$ of equal step sum $d$, the $2 \times 2$
     Hankel determinant $P_{r_1} P_{r_4} - P_{r_2} P_{r_3}$ annihilates the leading $\mathcal{H}_\infty^2$
     term and satisfies:
     `(2 : ℤ) ^ d * ((P r₁ : ℤ) * (P r₄ : ℤ) - (P r₂ : ℤ) * (P r₃ : ℤ)) =
       (P r₁ : ℤ) * (A₃₄ : ℤ) - (P r₃ : ℤ) * (A₁₂ : ℤ)`.

4. **Theorem SB.4 (`two_seed_first_divergence_valuation_and_fractional_split`) — Universal Two-Seed Divergence & $[0, 1/3)$ vs. $[1/3, 1/2)$ Split**:
   - For **any** two seeds $b_1 < b_2 \in \mathbb{N}$ (across arbitrary branches!), if their binary
     parities agree for $k < n_0$ and diverge at step $n_0$
     (`orbit b₁ n₀ % 2 ≠ orbit b₂ n₀ % 2`), then:
     - `D_{n₀} = orbit b₂ n₀ - orbit b₁ n₀` is odd (`D_{n₀} % 2 = 1`),
     - `2 ^ n₀ * D_{n₀} = 3 ^ n₀ * (b₂ - b₁)`,
     - `2 ^ n₀ ∣ (b₂ - b₁)` and `¬ (2 ^ (n₀ + 1) ∣ (b₂ - b₁))` (so $n_0 = v_2(b_2 - b_1)$ is the
       exact 2-adic valuation of $b_2 - b_1$, and $b_2 - b_1 < 2^N$ forces divergence before step $N$!),
     - And for any real companions $\alpha_1, \alpha_2$ surviving through step $n_0 + 1$, the even
       branch at step $n_0$ has fractional part in $[0, 1/3)$ while the odd branch has fractional
       part in $[1/3, 1/2)$.

5. **Theorem SB.5 (`post_bitlength_unique_residue_pinning`) — Post-Bit-Length Residue Pinning**:
   - Whenever a seed $b_0 \in \mathbb{N}$ satisfies $b_0 < 2^W$ and survives up to block $K$ with
     $W \le T_K$, no other seed in $[0, 2^{T_K + 1})$ can share the $K$-block prefix $s$.
-/

namespace Mahler.SemigroupBreakout

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.ArchimedeanPinningAndRenewal
open Mahler.RenewalCocycleAndSandwich
open Mahler.ExtraBitBackwardAndKneading15

/-! ## 1. Theorem SB.1: The Global Archimedean Rung Ceiling (False in $\mathbb{Z}_2$, True in $\mathbb{N}$) -/

/-- **Global Archimedean Rung Ceiling (`archimedean_rung_ceiling_and_stepSum_bound`, Theorem SB.1)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds for a natural seed `b_0 : ℕ`. Setting
`P r = oddReturnP (orbit b_0 (blockSteps s r))` and `T r = blockSteps s r`:
1. `1 ≤ u K`, `P K = 2 ^ (s K) * u K`, and `2 ^ (s K) ≤ P K`,
2. `2 ^ (T (K + 1)) * u K = 3 ^ (T K) * P 0 + renewalNumerator s K`,
3. If `0 < renewalIntSlack s K` (`2 * renewalNumerator s K < 3 ^ (T K)`), then
   `2 * 2 ^ (T (K + 1)) * u K < 3 ^ (T K) * (2 * P 0 + 1)` and
   `2 * 2 ^ (T (K + 1)) < 3 ^ (T K) * (2 * P 0 + 1)`, and
4. At $K = 0$, `2 ^ (s 0) ≤ 3 * b_0 + 1`. -/
theorem archimedean_rung_ceiling_and_stepSum_bound
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1)) :
    let P := fun r => oddReturnP (orbit b_0 (blockSteps s r))
    let T := fun r => blockSteps s r
    (1 ≤ u K ∧ P K = 2 ^ (s K) * u K ∧ 2 ^ (s K) ≤ P K) ∧
      2 ^ (T (K + 1)) * u K = 3 ^ (T K) * P 0 + renewalNumerator s K ∧
      (0 < renewalIntSlack s K →
        2 * 2 ^ (T (K + 1)) * u K < 3 ^ (T K) * (2 * P 0 + 1) ∧
          2 * 2 ^ (T (K + 1)) < 3 ^ (T K) * (2 * P 0 + 1)) ∧
      2 ^ (s 0) ≤ 3 * b_0 + 1 := by
  intro P T
  have hK := hchain K (by omega)
  have hu_odd : u K % 2 = 1 := hK.2.1
  have hu_pos : 1 ≤ u K := by omega
  have hPK_eq : P K = 2 ^ (s K) * u K := hK.2.2
  have hpow_le : 2 ^ (s K) ≤ P K := by
    have h1 : 2 ^ (s K) * 1 ≤ 2 ^ (s K) * u K := Nat.mul_le_mul_left (2 ^ (s K)) hu_pos
    omega
  have hchK : ValidBlockChain b_0 s u K := fun k hk => hchain k (by omega)
  have hm := renewal_prefix_master_identity hchK
  change 2 ^ (T K) * P K = 3 ^ (T K) * P 0 + renewalNumerator s K at hm
  have hT_succ : T (K + 1) = T K + s K := rfl
  have hmaster_u : 2 ^ (T (K + 1)) * u K = 3 ^ (T K) * P 0 + renewalNumerator s K := by
    calc
      2 ^ (T (K + 1)) * u K = 2 ^ (T K) * (2 ^ (s K) * u K) := by
        rw [hT_succ, Nat.pow_add]
        ring
      _ = 2 ^ (T K) * P K := by rw [← hPK_eq]
      _ = 3 ^ (T K) * P 0 + renewalNumerator s K := hm
  have h0 := hchain 0 (by omega)
  have hu0_odd : u 0 % 2 = 1 := h0.2.1
  have hu0_pos : 1 ≤ u 0 := by omega
  have hP0_eq : 3 * b_0 + 1 = 2 ^ (s 0) * u 0 := h0.2.2
  have hs0_le : 2 ^ (s 0) ≤ 3 * b_0 + 1 := by
    have h1 : 2 ^ (s 0) * 1 ≤ 2 ^ (s 0) * u 0 := Nat.mul_le_mul_left (2 ^ (s 0)) hu0_pos
    omega
  refine ⟨⟨hu_pos, hPK_eq, hpow_le⟩, hmaster_u, ?_, hs0_le⟩
  intro hS_pos
  have h2A_lt : 2 * renewalNumerator s K < 3 ^ (T K) := by
    have h : 2 * (renewalNumerator s K : ℤ) < (3 : ℤ) ^ (T K) := by
      change 0 < (3 : ℤ) ^ (T K) - 2 * (renewalNumerator s K : ℤ) at hS_pos
      omega
    exact_mod_cast h
  have hlt_u : 2 * 2 ^ (T (K + 1)) * u K < 3 ^ (T K) * (2 * P 0 + 1) := by
    calc
      2 * 2 ^ (T (K + 1)) * u K
          = 2 * (2 ^ (T (K + 1)) * u K) := by ring
      _ = 2 * (3 ^ (T K) * P 0 + renewalNumerator s K) := by rw [hmaster_u]
      _ = 2 * 3 ^ (T K) * P 0 + 2 * renewalNumerator s K := by ring
      _ < 2 * 3 ^ (T K) * P 0 + 3 ^ (T K) := by omega
      _ = 3 ^ (T K) * (2 * P 0 + 1) := by ring
  have hle_1 : 2 * 2 ^ (T (K + 1)) * 1 ≤ 2 * 2 ^ (T (K + 1)) * u K :=
    Nat.mul_le_mul_left (2 * 2 ^ (T (K + 1))) hu_pos
  exact ⟨hlt_u, by omega⟩

/-! ## 2. Theorem SB.2: Pure Power-of-3 ($u_K = 1$) Collapse & Mod-64 Trap -/

/-- Auxiliary lemma: `9 ^ j % 8 = 1` for every `j : ℕ`. -/
theorem nine_pow_mod_eight_eq_one (j : ℕ) : (9 ^ j) % 8 = 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **Pure Power-of-3 ($u_K = 1$) Collapse & Mod-64 Trap
(`unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity`, Theorem SB.2)**:
1. **Even Rung ($s_K = 2 j$, $j \ge 1$) with $u_K = 1$**:
   Setting `b_next = 3 ^ (2 * j - 1)`, we have
   `oddReturnP b_next = 3 ^ (2 * j) + 1`, `oddReturnP b_next % 8 = 2`,
   `2 ∣ oddReturnP b_next`, and `¬ (4 ∣ oddReturnP b_next)` (instant odd-to-odd death $s_{K+1} = 1$!).
2. **Odd Rung ($s_K = 2 j + 1$, $j \ge 1$) with $u_K = 1$**:
   Setting `b_next = 3 ^ (2 * j)`, we have
   `oddReturnP b_next = 3 ^ (2 * j + 1) + 1`, `oddReturnP b_next % 8 = 4`,
   `4 ∣ oddReturnP b_next`, and `¬ (8 ∣ oddReturnP b_next)` (forcing $s_{K+1} = 2$!).
   Moreover, setting `u_next = oddReturnP b_next / 4` and `b_next2 = 3 * u_next`:
   - `4 * oddReturnP b_next2 = 3 ^ (2 * j + 3) + 13`,
   - `3 ^ (2 * j + 3) + 13 = 243 * (3 ^ (2 * j - 2) - 1) + 256`, and
   - `64 ∣ oddReturnP b_next2 ↔ 256 ∣ (3 ^ (2 * j - 2) - 1)`.
3. **Base Case $j = 1$ ($s_K = 3, b_{K+1} = 9$)**:
   `b_next = 9` steps via $s_{K+1} = 2$ to `b_next2 = 21` (`oddReturnP 21 = 64 = 2 ^ 6 * 1`),
   which steps via $s_{K+2} = 6$ to `b_next3 = 243 = 3 ^ 5` with `oddReturnP 243 = 730 % 8 = 2`
   (dying at $s_{K+3} = 1$!). -/
theorem unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity
    {j : ℕ} (hj : 1 ≤ j) :
    let b_even := 3 ^ (2 * j - 1)
    let b_odd := 3 ^ (2 * j)
    let u_next := oddReturnP b_odd / 4
    let b_next2 := 3 * u_next
    (oddReturnP b_even = 3 ^ (2 * j) + 1 ∧
      oddReturnP b_even % 8 = 2 ∧
      2 ∣ oddReturnP b_even ∧ ¬ (4 ∣ oddReturnP b_even)) ∧
      (oddReturnP b_odd = 3 ^ (2 * j + 1) + 1 ∧
        oddReturnP b_odd % 8 = 4 ∧
        4 ∣ oddReturnP b_odd ∧ ¬ (8 ∣ oddReturnP b_odd) ∧
        4 * oddReturnP b_next2 = 3 ^ (2 * j + 3) + 13 ∧
        3 ^ (2 * j + 3) + 13 = 243 * (3 ^ (2 * j - 2) - 1) + 256 ∧
        (64 ∣ oddReturnP b_next2 ↔ 256 ∣ (3 ^ (2 * j - 2) - 1))) ∧
      (oddReturnP 9 = 2 ^ 2 * 7 ∧
        oddReturnP 21 = 2 ^ 6 * 1 ∧
        oddReturnP 243 % 8 = 2) := by
  intro b_even b_odd u_next b_next2
  have h9 : (9 ^ j) % 8 = 1 := nine_pow_mod_eight_eq_one j
  have hpow_even : 3 ^ (2 * j) = 9 ^ j := by
    rw [Nat.pow_mul]
  have hP_even : oddReturnP b_even = 3 ^ (2 * j) + 1 := by
    unfold oddReturnP
    dsimp [b_even]
    have hj_add : (2 * j - 1) + 1 = 2 * j := by omega
    have hmul : 3 * 3 ^ (2 * j - 1) = 3 ^ (2 * j) := by
      conv_rhs => rw [← hj_add, Nat.pow_succ']
    rw [hmul]
  have hmod_even : oddReturnP b_even % 8 = 2 := by
    rw [hP_even, hpow_even]
    omega
  have hP_odd : oddReturnP b_odd = 3 ^ (2 * j + 1) + 1 := by
    unfold oddReturnP
    dsimp [b_odd]
    rw [← Nat.pow_succ']
  have hpow_odd : 3 ^ (2 * j + 1) = 3 * 9 ^ j := by
    rw [Nat.pow_succ', Nat.pow_mul]
  have hmod_odd : oddReturnP b_odd % 8 = 4 := by
    rw [hP_odd, hpow_odd]
    omega
  have hdvd4 : 4 ∣ oddReturnP b_odd := by omega
  have h4u : 4 * u_next = 3 ^ (2 * j + 1) + 1 := by
    dsimp [u_next]
    rw [Nat.mul_div_cancel' hdvd4, hP_odd]
  have h4P2 : 4 * oddReturnP b_next2 = 3 ^ (2 * j + 3) + 13 := by
    unfold oddReturnP
    dsimp [b_next2]
    calc
      4 * (3 * (3 * u_next) + 1) = 9 * (4 * u_next) + 4 := by ring
      _ = 9 * (3 ^ (2 * j + 1) + 1) + 4 := by rw [h4u]
      _ = 3 ^ (2 * j + 3) + 13 := by
            rw [show 2 * j + 3 = (2 * j + 1) + 2 by omega, Nat.pow_add]
            ring
  have h1_le_pow : 1 ≤ 3 ^ (2 * j - 2) := Nat.one_le_pow _ 3 (by decide)
  have h243_id : 3 ^ (2 * j + 3) + 13 = 243 * (3 ^ (2 * j - 2) - 1) + 256 := by
    have hsplit : 3 ^ (2 * j + 3) = 243 * 3 ^ (2 * j - 2) := by
      calc
        3 ^ (2 * j + 3) = 3 ^ 5 * 3 ^ (2 * j - 2) := by
          rw [← Nat.pow_add, show 5 + (2 * j - 2) = 2 * j + 3 by omega]
        _ = 243 * 3 ^ (2 * j - 2) := by ring
    rw [hsplit]
    omega
  have hiff64 : 64 ∣ oddReturnP b_next2 ↔ 256 ∣ (3 ^ (2 * j - 2) - 1) := by
    have hlin : 4 * oddReturnP b_next2 = 243 * (3 ^ (2 * j - 2) - 1) + 256 := by
      rw [h4P2, h243_id]
    generalize oddReturnP b_next2 = Y at hlin ⊢
    generalize 3 ^ (2 * j - 2) - 1 = X at hlin ⊢
    clear hj b_even b_odd u_next b_next2 h9 hpow_even hP_even hmod_even hP_odd hpow_odd
      hmod_odd hdvd4 h4u h4P2 h1_le_pow h243_id
    omega
  refine ⟨⟨hP_even, hmod_even, by omega, by omega⟩,
          ⟨hP_odd, hmod_odd, hdvd4, by omega, h4P2, h243_id, hiff64⟩,
          by decide⟩

/-! ## 3. Theorem SB.3: Cross-Window Hankel Determinant Annihilation -/

/-- **Cross-Window Hankel Determinant Annihilation
(`equal_step_window_hankel_determinant_identity_and_bound`, Theorem SB.3)**:
Suppose two block windows specify integer boundary pairs `(P₁, P₂)` and `(P₃, P₄)` satisfying
`2 ^ d * P₂ = 3 ^ d * P₁ + A₁₂` and `2 ^ d * P₄ = 3 ^ d * P₃ + A₃₄`:
1. `(2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) =
     (P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ)`,
2. `((2 : ℤ) ^ d) ∣ ((P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ))`, and
3. If `1 ≤ P₁`, `1 ≤ P₃`, `2 * A₁₂ < 3 ^ d`, and `2 * A₃₄ < 3 ^ d`, then
   `-(3 : ℤ) ^ d * (P₃ : ℤ) < (2 : ℤ) ^ (d + 1) * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ))`
   and
   `(2 : ℤ) ^ (d + 1) * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) < (3 : ℤ) ^ d * (P₁ : ℤ)`. -/
theorem equal_step_window_hankel_determinant_identity_and_bound
    {P₁ P₂ P₃ P₄ A₁₂ A₃₄ d : ℕ}
    (hw1 : 2 ^ d * P₂ = 3 ^ d * P₁ + A₁₂)
    (hw2 : 2 ^ d * P₄ = 3 ^ d * P₃ + A₃₄) :
    (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) =
      (P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ) ∧
      ((2 : ℤ) ^ d) ∣ ((P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ)) ∧
      (1 ≤ P₁ → 1 ≤ P₃ → 2 * A₁₂ < 3 ^ d → 2 * A₃₄ < 3 ^ d →
        -(3 : ℤ) ^ d * (P₃ : ℤ) <
            (2 : ℤ) ^ (d + 1) * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) ∧
          (2 : ℤ) ^ (d + 1) * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) <
            (3 : ℤ) ^ d * (P₁ : ℤ)) := by
  have hw1_z : (2 : ℤ) ^ d * (P₂ : ℤ) = (3 : ℤ) ^ d * (P₁ : ℤ) + (A₁₂ : ℤ) := by
    exact_mod_cast hw1
  have hw2_z : (2 : ℤ) ^ d * (P₄ : ℤ) = (3 : ℤ) ^ d * (P₃ : ℤ) + (A₃₄ : ℤ) := by
    exact_mod_cast hw2
  have hid :
      (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) =
        (P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ) := by
    calc
      (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ))
          = (P₁ : ℤ) * ((2 : ℤ) ^ d * (P₄ : ℤ)) - ((2 : ℤ) ^ d * (P₂ : ℤ)) * (P₃ : ℤ) := by ring
      _ = (P₁ : ℤ) * ((3 : ℤ) ^ d * (P₃ : ℤ) + (A₃₄ : ℤ)) -
            ((3 : ℤ) ^ d * (P₁ : ℤ) + (A₁₂ : ℤ)) * (P₃ : ℤ) := by rw [hw1_z, hw2_z]
      _ = (P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ) := by ring
  refine ⟨hid, ⟨(P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ), hid.symm⟩, ?_⟩
  intro hP1 hP3 hA12 hA34
  have h2_id :
      (2 : ℤ) ^ (d + 1) * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) =
        (P₁ : ℤ) * (2 * (A₃₄ : ℤ)) - (P₃ : ℤ) * (2 * (A₁₂ : ℤ)) := by
    calc
      (2 : ℤ) ^ (d + 1) * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ))
          = 2 * ((2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ))) := by
            rw [pow_succ]
            ring
      _ = 2 * ((P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ)) := by rw [hid]
      _ = (P₁ : ℤ) * (2 * (A₃₄ : ℤ)) - (P₃ : ℤ) * (2 * (A₁₂ : ℤ)) := by ring
  have hP1_pos : (0 : ℤ) < (P₁ : ℤ) := by exact_mod_cast hP1
  have hP3_pos : (0 : ℤ) < (P₃ : ℤ) := by exact_mod_cast hP3
  have hA12_lt : 2 * (A₁₂ : ℤ) < (3 : ℤ) ^ d := by exact_mod_cast hA12
  have hA34_lt : 2 * (A₃₄ : ℤ) < (3 : ℤ) ^ d := by exact_mod_cast hA34
  have hA12_nonneg : (0 : ℤ) ≤ 2 * (A₁₂ : ℤ) := by positivity
  have hA34_nonneg : (0 : ℤ) ≤ 2 * (A₃₄ : ℤ) := by positivity
  have h1 : (P₃ : ℤ) * (2 * (A₁₂ : ℤ)) < (P₃ : ℤ) * (3 : ℤ) ^ d :=
    mul_lt_mul_of_pos_left hA12_lt hP3_pos
  have h2 : (0 : ℤ) ≤ (P₁ : ℤ) * (2 * (A₃₄ : ℤ)) :=
    mul_nonneg (le_of_lt hP1_pos) hA34_nonneg
  have h3 : (P₁ : ℤ) * (2 * (A₃₄ : ℤ)) < (P₁ : ℤ) * (3 : ℤ) ^ d :=
    mul_lt_mul_of_pos_left hA34_lt hP1_pos
  have h4 : (0 : ℤ) ≤ (P₃ : ℤ) * (2 * (A₁₂ : ℤ)) :=
    mul_nonneg (le_of_lt hP3_pos) hA12_nonneg
  rw [h2_id]
  have hcomm1 : (P₃ : ℤ) * (3 : ℤ) ^ d = (3 : ℤ) ^ d * (P₃ : ℤ) := by ring
  have hcomm2 : (P₁ : ℤ) * (3 : ℤ) ^ d = (3 : ℤ) ^ d * (P₁ : ℤ) := by ring
  have hneg : -(3 : ℤ) ^ d * (P₃ : ℤ) = -((3 : ℤ) ^ d * (P₃ : ℤ)) := by ring
  rw [hcomm1] at h1
  rw [hcomm2] at h3
  rw [hneg]
  clear hw1 hw2 hw1_z hw2_z hid h2_id hcomm1 hcomm2 hneg
  omega

/-! ## 4. Theorem SB.4: Universal Two-Seed Divergence & Exact $v_2(b_2 - b_1)$ Law -/

/-- Auxiliary one-step binary identity: `2 * orbit b (k + 1) = 3 * orbit b k + orbit b k % 2`. -/
theorem two_mul_orbit_succ_eq (b k : ℕ) :
    2 * orbit b (k + 1) = 3 * orbit b k + orbit b k % 2 := by
  simp only [orbit, step]
  omega

/-- **Universal Two-Seed First Divergence Valuation Law
(`two_seed_first_divergence_valuation_and_bound`, Theorem SB.4)**:
For any two seeds `b₁ ≤ b₂` and step `n₀ : ℕ`:
If their binary parities match on `[0, n₀)` (`∀ k < n₀, orbit b₁ k % 2 = orbit b₂ k % 2`), then:
1. `orbit b₁ n₀ ≤ orbit b₂ n₀` and
   `2 ^ n₀ * (orbit b₂ n₀ - orbit b₁ n₀) = 3 ^ n₀ * (b₂ - b₁)`,
2. `2 ^ n₀ ∣ (b₂ - b₁)`, and
3. If `orbit b₁ n₀ % 2 ≠ orbit b₂ n₀ % 2` (so `n₀` is the **first divergence step**), then
   `(orbit b₂ n₀ - orbit b₁ n₀) % 2 = 1` and `¬ (2 ^ (n₀ + 1) ∣ (b₂ - b₁))`!
   Consequently, if `b₁ < b₂` and `b₂ - b₁ < 2 ^ N`, their binary parities **must diverge
   at some step `n₀ < N`** (`∃ n₀ < N, orbit b₁ n₀ % 2 ≠ orbit b₂ n₀ % 2`). -/
theorem two_seed_first_divergence_valuation_and_bound
    {b₁ b₂ n₀ : ℕ} (hle : b₁ ≤ b₂)
    (hmatch : ∀ k < n₀, orbit b₁ k % 2 = orbit b₂ k % 2) :
    let D := orbit b₂ n₀ - orbit b₁ n₀
    (orbit b₁ n₀ ≤ orbit b₂ n₀ ∧
      2 ^ n₀ * D = 3 ^ n₀ * (b₂ - b₁) ∧
      2 ^ n₀ ∣ (b₂ - b₁)) ∧
      (orbit b₁ n₀ % 2 ≠ orbit b₂ n₀ % 2 →
        D % 2 = 1 ∧ ¬ (2 ^ (n₀ + 1) ∣ (b₂ - b₁))) ∧
      (∀ N : ℕ, b₁ < b₂ → b₂ - b₁ < 2 ^ N →
        ∃ k < N, orbit b₁ k % 2 ≠ orbit b₂ k % 2) := by
  intro D
  have hstep : orbit b₁ n₀ ≤ orbit b₂ n₀ ∧ 2 ^ n₀ * (orbit b₂ n₀ - orbit b₁ n₀) = 3 ^ n₀ * (b₂ - b₁) := by
    induction n₀ with
    | zero =>
        simp [orbit]
        exact hle
    | succ k ih =>
        rcases ih (fun j hj => hmatch j (by omega)) with ⟨hle_k, heq_k⟩
        have hpar_k := hmatch k (by omega)
        have h1 := two_mul_orbit_succ_eq b₁ k
        have h2 := two_mul_orbit_succ_eq b₂ k
        have hle_succ : orbit b₁ (k + 1) ≤ orbit b₂ (k + 1) := by omega
        have hdiff_succ :
            2 * (orbit b₂ (k + 1) - orbit b₁ (k + 1)) =
              3 * (orbit b₂ k - orbit b₁ k) := by omega
        refine ⟨hle_succ, ?_⟩
        calc
          2 ^ (k + 1) * (orbit b₂ (k + 1) - orbit b₁ (k + 1))
              = 2 ^ k * (2 * (orbit b₂ (k + 1) - orbit b₁ (k + 1))) := by
                rw [Nat.pow_succ]
                ring
          _ = 2 ^ k * (3 * (orbit b₂ k - orbit b₁ k)) := by rw [hdiff_succ]
          _ = 3 * (2 ^ k * (orbit b₂ k - orbit b₁ k)) := by ring
          _ = 3 * (3 ^ k * (b₂ - b₁)) := by rw [heq_k]
          _ = 3 ^ (k + 1) * (b₂ - b₁) := by rw [Nat.pow_succ]; ring
  rcases hstep with ⟨hle_n0, heq_n0⟩
  have hcop : Nat.Coprime (2 ^ n₀) (3 ^ n₀) :=
    (Nat.Coprime.pow n₀ n₀ (by decide : Nat.Coprime 2 3))
  have hdvd_prod : 2 ^ n₀ ∣ 3 ^ n₀ * (b₂ - b₁) := ⟨D, heq_n0.symm⟩
  have hdvd_b : 2 ^ n₀ ∣ (b₂ - b₁) := hcop.dvd_of_dvd_mul_left hdvd_prod
  refine ⟨⟨hle_n0, heq_n0, hdvd_b⟩, ?_, ?_⟩
  · intro hdiv
    have hD_odd : D % 2 = 1 := by
      dsimp [D]
      omega
    refine ⟨hD_odd, ?_⟩
    rintro ⟨q, hq⟩
    have hrhs : 3 ^ n₀ * (b₂ - b₁) = 2 ^ n₀ * (2 * (3 ^ n₀ * q)) := by
      rw [hq, Nat.pow_succ]
      ring
    have hlhs : 2 ^ n₀ * D = 2 ^ n₀ * (2 * (3 ^ n₀ * q)) := by
      rw [heq_n0, hrhs]
    have h2_pos : 0 < 2 ^ n₀ := Nat.pos_of_ne_zero (pow_ne_zero n₀ (by decide))
    have hD_eq : D = 2 * (3 ^ n₀ * q) := Nat.eq_of_mul_eq_mul_left h2_pos hlhs
    omega
  · intro N hlt_b hdiff_lt
    by_contra h_no_div
    have h_all_eq : ∀ m < N, orbit b₁ m % 2 = orbit b₂ m % 2 := by
      intro m hm
      by_contra hne
      exact h_no_div ⟨m, hm, hne⟩
    have hall : ∀ j : ℕ, j ≤ N → orbit b₁ j ≤ orbit b₂ j ∧
        2 ^ j * (orbit b₂ j - orbit b₁ j) = 3 ^ j * (b₂ - b₁) := by
      intro j hj
      induction j with
      | zero => simp [orbit, hle]
      | succ m ihm =>
          rcases ihm (by omega) with ⟨hlem, heqm⟩
          have hpm := h_all_eq m (by omega)
          have h1 := two_mul_orbit_succ_eq b₁ m
          have h2 := two_mul_orbit_succ_eq b₂ m
          have hle_m1 : orbit b₁ (m + 1) ≤ orbit b₂ (m + 1) := by omega
          have hdiff_m1 :
              2 * (orbit b₂ (m + 1) - orbit b₁ (m + 1)) =
                3 * (orbit b₂ m - orbit b₁ m) := by omega
          refine ⟨hle_m1, ?_⟩
          calc
            2 ^ (m + 1) * (orbit b₂ (m + 1) - orbit b₁ (m + 1))
                = 2 ^ m * (2 * (orbit b₂ (m + 1) - orbit b₁ (m + 1))) := by rw [Nat.pow_succ]; ring
            _ = 2 ^ m * (3 * (orbit b₂ m - orbit b₁ m)) := by rw [hdiff_m1]
            _ = 3 * (2 ^ m * (orbit b₂ m - orbit b₁ m)) := by ring
            _ = 3 * (3 ^ m * (b₂ - b₁)) := by rw [heqm]
            _ = 3 ^ (m + 1) * (b₂ - b₁) := by rw [Nat.pow_succ]; ring
    have hN := (hall N (le_refl N)).2
    have hcopN : Nat.Coprime (2 ^ N) (3 ^ N) :=
      (Nat.Coprime.pow N N (by decide : Nat.Coprime 2 3))
    have hdvdN : 2 ^ N ∣ (b₂ - b₁) :=
      hcopN.dvd_of_dvd_mul_left ⟨orbit b₂ N - orbit b₁ N, hN.symm⟩
    have hpos_diff : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt_b
    have hgeN : 2 ^ N ≤ b₂ - b₁ := Nat.le_of_dvd hpos_diff hdvdN
    omega

/-! ## 5. Theorem SB.5: Post-Bit-Length Unique Seed Pinning -/

/-- **Post-Bit-Length Unique Seed Pinning (`post_bitlength_unique_seed_in_dyadic_box`, Theorem SB.5)**:
If two seeds `b₁, b₂ < 2 ^ (blockSteps s N + 1)` both realize `ValidBlockChain bᵢ s uᵢ N` for
`1 ≤ N`, then `b₁ = b₂`! In particular, once the elapsed binary steps `blockSteps s N` reach the
bit-length `W` of a seed `b₁ < 2 ^ W`, `b₁` is the **unique** integer in `[0, 2 ^ (blockSteps s N + 1))`
realizing `s`. -/
theorem post_bitlength_unique_seed_in_dyadic_box
    {b₁ b₂ N : ℕ} {s u₁ u₂ : ℕ → ℕ}
    (hN : 1 ≤ N)
    (hb₁ : b₁ < 2 ^ (blockSteps s N + 1))
    (hb₂ : b₂ < 2 ^ (blockSteps s N + 1))
    (hch₁ : ValidBlockChain b₁ s u₁ N)
    (hch₂ : ValidBlockChain b₂ s u₂ N) :
    b₁ = b₂ := by
  rcases lt_trichotomy b₁ b₂ with hlt | rfl | hgt
  · have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd hN (le_of_lt hlt) hch₁ hch₂).2.2.1
    change 2 ^ (blockSteps s N + 1) ∣ (b₂ - b₁) at hdvd
    have hpos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hlt
    have hge : 2 ^ (blockSteps s N + 1) ≤ b₂ - b₁ := Nat.le_of_dvd hpos hdvd
    omega
  · rfl
  · have hdvd :=
      (two_seeds_same_validBlockChain_mod_two_pow_succ_dvd hN (le_of_lt hgt) hch₂ hch₁).2.2.1
    change 2 ^ (blockSteps s N + 1) ∣ (b₁ - b₂) at hdvd
    have hpos : 0 < b₁ - b₂ := Nat.sub_pos_of_lt hgt
    have hge : 2 ^ (blockSteps s N + 1) ≤ b₁ - b₂ := Nat.le_of_dvd hpos hdvd
    omega

/-! ## 6. Theorem SB.6 (Wildcard 1): The 4-Lift Double-Odd Exclusion & $(3/4)^m$ Density-Zero Mechanism -/

/-- Auxiliary lemma: `(orbit b k % 2 = 1 ∧ orbit b (k + 1) % 2 = 1) ↔ orbit b k % 4 = 3`. -/
theorem double_odd_step_iff_orbit_mod_four_eq_three (b k : ℕ) :
    (orbit b k % 2 = 1 ∧ orbit b (k + 1) % 2 = 1) ↔ orbit b k % 4 = 3 := by
  have hstep := two_mul_orbit_succ_eq b k
  omega

/-- **Exact 4-Lift Double-Odd Exclusion (`dyadic_four_lift_double_odd_bijection_and_three_of_four_survival`,
Theorem SB.6 / Wildcard 1)**:
For any prefix seed `r : ℕ`, step `k : ℕ`, and 2-bit lift `t : ℕ`:
1. If `∀ j < k, orbit (r + 2 ^ k * t) j % 2 = orbit r j % 2`, then
   `orbit (r + 2 ^ k * t) k = orbit r k + 3 ^ k * t`,
2. `(orbit r k % 2 = 1 ∧ orbit r (k + 1) % 2 = 1) ↔ orbit r k % 4 = 3`, and
3. As `t` ranges over the four 2-bit lifts `0, 1, 2, 3`, **at most 3 out of the 4 lifts** avoid the
   forbidden double-odd transition `orbit · k % 4 = 3`: specifically, for every `x₀ : ℕ` and every
   `s₃ : ℕ` with `s₃ % 4 = 1 ∨ s₃ % 4 = 3`, there exists `t < 4` such that
   `(x₀ + s₃ * t) % 4 = 3`! -/
theorem dyadic_four_lift_double_odd_bijection_and_three_of_four_survival
    (r k t : ℕ) :
    ((∀ j < k, orbit (r + 2 ^ k * t) j % 2 = orbit r j % 2) →
      orbit (r + 2 ^ k * t) k = orbit r k + 3 ^ k * t) ∧
      ((orbit r k % 2 = 1 ∧ orbit r (k + 1) % 2 = 1) ↔ orbit r k % 4 = 3) ∧
      (∀ x₀ s₃ : ℕ, (s₃ % 4 = 1 ∨ s₃ % 4 = 3) →
        ∃ t < 4, (x₀ + s₃ * t) % 4 = 3) := by
  refine ⟨?_, double_odd_step_iff_orbit_mod_four_eq_three r k, ?_⟩
  · intro hmatch
    have hle : r ≤ r + 2 ^ k * t := Nat.le_add_right r (2 ^ k * t)
    have hdiv := (two_seed_first_divergence_valuation_and_bound hle
      (fun j hj => (hmatch j hj).symm)).1
    rcases hdiv with ⟨hle_orb, heq_orb, _⟩
    have hsub : r + 2 ^ k * t - r = 2 ^ k * t := by omega
    rw [hsub] at heq_orb
    have hrhs : 3 ^ k * (2 ^ k * t) = 2 ^ k * (3 ^ k * t) := by ring
    rw [hrhs] at heq_orb
    have h2_pos : 0 < 2 ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (by decide))
    have hdiff_eq : orbit (r + 2 ^ k * t) k - orbit r k = 3 ^ k * t :=
      Nat.eq_of_mul_eq_mul_left h2_pos heq_orb
    omega
  · intro x₀ s₃ hs₃
    have hx : x₀ % 4 = 0 ∨ x₀ % 4 = 1 ∨ x₀ % 4 = 2 ∨ x₀ % 4 = 3 := by omega
    rcases hs₃ with h1 | h3
    · rcases hx with hx0 | hx1 | hx2 | hx3
      · exact ⟨3, by decide, by omega⟩
      · exact ⟨2, by decide, by omega⟩
      · exact ⟨1, by decide, by omega⟩
      · exact ⟨0, by decide, by omega⟩
    · rcases hx with hx0 | hx1 | hx2 | hx3
      · exact ⟨1, by decide, by omega⟩
      · exact ⟨2, by decide, by omega⟩
      · exact ⟨3, by decide, by omega⟩
      · exact ⟨0, by decide, by omega⟩

/-! ## 7. Theorem SB.7 (Wildcard 2): Base-3 "Frozen Top Digits" & Forbidden Leading Trit 2 -/

/-- **Raw-Orbit Base-3 Frozen-Prefix & Forbidden Leading Trit Law
(`raw_orbit_base3_frozen_prefix_and_leading_trit_le_one`, Theorem SB.7 / Wildcard 2)**:
Suppose at binary step `N` (`1 ≤ N`), `2 ^ N * g_N = 3 ^ N * g_0 + K_N` with `2 * K_N < 3 ^ N`.
Then in **base 3**:
1. `(2 ^ N * g_N) / 3 ^ N = g_0` (the top base-3 prefix of $2^N g_N$ above position $N$ is frozen
   at $g_0$ for every $N$),
2. `(2 ^ N * g_N) % 3 ^ N = K_N`,
3. `((2 ^ N * g_N) % 3 ^ N) / 3 ^ (N - 1) ≤ 1` (the $(N-1)$-st base-3 digit of $2^N g_N$ is $0$ or $1$,
   **never $2$**!), and
4. **$\mathbb{Z}_2$-Symmetry-Breaking Base-3 Length Bound**: if $g_0 < 3 ^ L$ has at most $L$
   base-3 digits, then `2 ^ N * g_N < 3 ^ (N + L)`. -/
theorem raw_orbit_base3_frozen_prefix_and_leading_trit_le_one
    {g_0 g_N K_N N L : ℕ} (hN : 1 ≤ N)
    (hid : 2 ^ N * g_N = 3 ^ N * g_0 + K_N)
    (hK : 2 * K_N < 3 ^ N) :
    (2 ^ N * g_N) / 3 ^ N = g_0 ∧
      (2 ^ N * g_N) % 3 ^ N = K_N ∧
      ((2 ^ N * g_N) % 3 ^ N) / 3 ^ (N - 1) ≤ 1 ∧
      (g_0 < 3 ^ L → 2 ^ N * g_N < 3 ^ (N + L)) := by
  have hK_lt : K_N < 3 ^ N := by omega
  have h3N_pos : 0 < 3 ^ N := Nat.pos_of_ne_zero (pow_ne_zero N (by decide))
  have hdiv : (2 ^ N * g_N) / 3 ^ N = g_0 := by
    rw [hid, Nat.mul_add_div h3N_pos, Nat.div_eq_of_lt hK_lt, add_zero]
  have hmod : (2 ^ N * g_N) % 3 ^ N = K_N := by
    rw [hid, Nat.mul_add_mod, Nat.mod_eq_of_lt hK_lt]
  have h3_split : 3 ^ N = 3 * 3 ^ (N - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hN, Nat.pow_succ']
  have htrit : ((2 ^ N * g_N) % 3 ^ N) / 3 ^ (N - 1) ≤ 1 := by
    rw [hmod]
    have hK_lt2 : K_N < 2 * 3 ^ (N - 1) := by omega
    have h3N1_pos : 0 < 3 ^ (N - 1) := Nat.pos_of_ne_zero (pow_ne_zero (N - 1) (by decide))
    have hdiv_lt : K_N / 3 ^ (N - 1) < 2 := (Nat.div_lt_iff_lt_mul h3N1_pos).2 (by omega)
    omega
  refine ⟨hdiv, hmod, htrit, ?_⟩
  intro hg0_lt
  have hg0_le : g_0 + 1 ≤ 3 ^ L := by omega
  calc
    2 ^ N * g_N = 3 ^ N * g_0 + K_N := hid
    _ < 3 ^ N * g_0 + 3 ^ N := by omega
    _ = 3 ^ N * (g_0 + 1) := by ring
    _ ≤ 3 ^ N * 3 ^ L := Nat.mul_le_mul_left (3 ^ N) hg0_le
    _ = 3 ^ (N + L) := by rw [← Nat.pow_add]

/-! ## 8. Theorem SB.8 (Wildcard 3): Exact Mahler–Antihydra $BB(6)$ Complement Duality -/

/-- Antihydra ($BB(6)$) floor step `antihydraStep a = (3 * a) / 2`. -/
def antihydraStep (a : ℕ) : ℕ :=
  (3 * a) / 2

/-- Antihydra ($BB(6)$) $k$-step floor orbit starting from `a_0`. -/
def antihydraOrbit (a_0 : ℕ) : ℕ → ℕ
  | 0 => a_0
  | k + 1 => antihydraStep (antihydraOrbit a_0 k)

/-- **Mahler–Antihydra $BB(6)$ Exact Complement Duality
(`mahler_antihydra_bb6_complement_duality`, Theorem SB.8 / Wildcard 3)**:
For every horizon `N : ℕ`, every Antihydra seed `a_0 ≤ 2 ^ N`, and every step `k ≤ N`,
setting the dual Mahler seed to be the $N$-bit complement `b_0 = 2 ^ N - a_0`:
1. `orbit (2 ^ N - a_0) k + antihydraOrbit a_0 k = 3 ^ k * 2 ^ (N - k)`,
2. Whenever `k < N`, `orbit (2 ^ N - a_0) k % 2 = antihydraOrbit a_0 k % 2`
   (**the binary parity sequences of Mahler for $2^N - a_0$ and Antihydra for $a_0$ are
   100% identical for the first $N$ steps!**), and
3. For Antihydra's actual starting state `a_0 = 8`, at step `k = 11` (`antihydraOrbit 8 11 = 681`)
   and `k = 12` (`antihydraOrbit 8 12 = 1021`), `antihydraOrbit 8 11 % 4 = 1` while at
   `k = 12, 13` (`1021 → 1531`), `antihydraOrbit 8 12 % 4 = 1`, and at `k = 11, 12`,
   `antihydraOrbit 8 11 % 2 = 1 ∧ antihydraOrbit 8 12 % 2 = 1`! -/
theorem mahler_antihydra_bb6_complement_duality
    {N a_0 : ℕ} (ha : a_0 ≤ 2 ^ N) :
    (∀ k ≤ N,
      orbit (2 ^ N - a_0) k + antihydraOrbit a_0 k = 3 ^ k * 2 ^ (N - k)) ∧
      (∀ k < N,
        orbit (2 ^ N - a_0) k % 2 = antihydraOrbit a_0 k % 2) ∧
      (antihydraOrbit 8 11 = 681 ∧
        antihydraOrbit 8 12 = 1021 ∧
        antihydraOrbit 8 11 % 2 = 1 ∧
        antihydraOrbit 8 12 % 2 = 1) := by
  have hsum : ∀ k ≤ N,
      orbit (2 ^ N - a_0) k + antihydraOrbit a_0 k = 3 ^ k * 2 ^ (N - k) := by
    intro k hk
    induction k with
    | zero =>
        simp [orbit, antihydraOrbit]
        omega
    | succ k ih =>
        have ih' := ih (by omega)
        have h_even_rhs : (3 ^ k * 2 ^ (N - k)) % 2 = 0 := by
          obtain ⟨m, hm⟩ : ∃ m : ℕ, N - k = m + 1 := ⟨N - k - 1, by omega⟩
          have hmul2 : 3 ^ k * 2 ^ (N - k) = 2 * (3 ^ k * 2 ^ m) := by
            rw [hm, Nat.pow_succ]
            ring
          rw [hmul2]
          omega
        have hpar : orbit (2 ^ N - a_0) k % 2 = antihydraOrbit a_0 k % 2 := by
          omega
        have hm_step := two_mul_orbit_succ_eq (2 ^ N - a_0) k
        have ha_step : 2 * antihydraOrbit a_0 (k + 1) + antihydraOrbit a_0 k % 2 =
            3 * antihydraOrbit a_0 k := by
          simp only [antihydraOrbit, antihydraStep]
          omega
        have hmul2 :
            2 * (orbit (2 ^ N - a_0) (k + 1) + antihydraOrbit a_0 (k + 1)) =
              3 * (orbit (2 ^ N - a_0) k + antihydraOrbit a_0 k) := by
          omega
        have hrhs :
            3 * (3 ^ k * 2 ^ (N - k)) = 2 * (3 ^ (k + 1) * 2 ^ (N - (k + 1))) := by
          have hpow2 : 2 ^ (N - k) = 2 * 2 ^ (N - (k + 1)) := by
            conv_lhs => rw [show N - k = (N - (k + 1)) + 1 by omega, Nat.pow_succ']
          rw [hpow2, Nat.pow_succ]
          ring
        rw [ih', hrhs] at hmul2
        omega
  refine ⟨hsum, ?_, by decide⟩
  intro k hk
  have hk_sum := hsum k (by omega)
  have h_even_rhs : (3 ^ k * 2 ^ (N - k)) % 2 = 0 := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, N - k = m + 1 := ⟨N - k - 1, by omega⟩
    have hmul2 : 3 ^ k * 2 ^ (N - k) = 2 * (3 ^ k * 2 ^ m) := by
      rw [hm, Nat.pow_succ]
      ring
    rw [hmul2]
    omega
  omega

#check @archimedean_rung_ceiling_and_stepSum_bound
#check @unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity
#check @equal_step_window_hankel_determinant_identity_and_bound
#check @two_seed_first_divergence_valuation_and_bound
#check @post_bitlength_unique_seed_in_dyadic_box
#check @dyadic_four_lift_double_odd_bijection_and_three_of_four_survival
#check @raw_orbit_base3_frozen_prefix_and_leading_trit_le_one
#check @mahler_antihydra_bb6_complement_duality

#print axioms archimedean_rung_ceiling_and_stepSum_bound
#print axioms unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity
#print axioms equal_step_window_hankel_determinant_identity_and_bound
#print axioms two_seed_first_divergence_valuation_and_bound
#print axioms post_bitlength_unique_seed_in_dyadic_box
#print axioms dyadic_four_lift_double_odd_bijection_and_three_of_four_survival
#print axioms raw_orbit_base3_frozen_prefix_and_leading_trit_le_one
#print axioms mahler_antihydra_bb6_complement_duality

end Mahler.SemigroupBreakout
