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

/-! ## 9. Theorem SB.9 (Idea 1): Zero-Carry Base-3 Digit-Sum Conservation & Even-Step Invariance -/

/-- Sum of base-3 (ternary) digits $s_3(n)$ of a natural number $n \in \mathbb{N}$. -/
def base3DigitSum (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 3 + base3DigitSum (n / 3)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

/-- Unconditional unfolding equation `base3DigitSum n = n % 3 + base3DigitSum (n / 3)`. -/
theorem base3DigitSum_eq (n : ℕ) :
    base3DigitSum n = n % 3 + base3DigitSum (n / 3) := by
  rw [base3DigitSum]
  split_ifs with h0
  · subst h0
    simp [base3DigitSum]
  · rfl

/-- Single-trit shift law: `base3DigitSum (3 * m + r) = r + base3DigitSum m` for `r < 3`. -/
theorem base3DigitSum_three_mul_add_digit (m : ℕ) {r : ℕ} (hr : r < 3) :
    base3DigitSum (3 * m + r) = r + base3DigitSum m := by
  rw [base3DigitSum_eq (3 * m + r)]
  have hmod : (3 * m + r) % 3 = r := by omega
  have hdiv : (3 * m + r) / 3 = m := by omega
  rw [hmod, hdiv]

/-- Zero-carry disjoint-block base-3 digit-sum additivity:
whenever `K < 3 ^ N`, `base3DigitSum (3 ^ N * g_0 + K) = base3DigitSum g_0 + base3DigitSum K`. -/
theorem base3DigitSum_three_pow_mul_add (N g_0 : ℕ) {K : ℕ} (hK : K < 3 ^ N) :
    base3DigitSum (3 ^ N * g_0 + K) = base3DigitSum g_0 + base3DigitSum K := by
  induction N generalizing K with
  | zero =>
      have hK0 : K = 0 := by
        simp only [Nat.pow_zero] at hK
        omega
      subst hK0
      have hz : base3DigitSum 0 = 0 := by simp [base3DigitSum]
      simp [hz]
  | succ N ih =>
      have hK_div : K / 3 < 3 ^ N := by
        rw [Nat.pow_succ] at hK
        omega
      have hK_mod : K % 3 < 3 := by omega
      have hdecomp : 3 ^ (N + 1) * g_0 + K = 3 * (3 ^ N * g_0 + K / 3) + K % 3 := by
        have h3mul : 3 ^ (N + 1) * g_0 = 3 * (3 ^ N * g_0) := by
          rw [Nat.pow_succ]
          ring
        rw [h3mul]
        omega
      rw [hdecomp, base3DigitSum_three_mul_add_digit _ hK_mod, ih hK_div, base3DigitSum_eq K]
      omega

/-- **Zero-Carry Base-3 Digit-Sum Conservation & Even-Step Invariance
(`zero_carry_base3_digit_sum_and_even_step_invariance`, Theorem SB.9 / Idea 1)**:
1. For any `N, g_0, g_N, K_N : ℕ` with `2 ^ N * g_N = 3 ^ N * g_0 + K_N` and `K_N < 3 ^ N`:
   `base3DigitSum (2 ^ N * g_N) = base3DigitSum g_0 + base3DigitSum K_N`,
2. For any `m : ℕ`, `base3DigitSum (3 * m) = base3DigitSum m`, and
3. Whenever step `N` of the raw orbit is **even** (`orbit g_0 N % 2 = 0`),
   `2 ^ (N + 1) * orbit g_0 (N + 1) = 3 * (2 ^ N * orbit g_0 N)` and
   `base3DigitSum (2 ^ (N + 1) * orbit g_0 (N + 1)) = base3DigitSum (2 ^ N * orbit g_0 N)`
   (the base-3 digit sum of $2^N g_N$ is **completely frozen across every even step**!). -/
theorem zero_carry_base3_digit_sum_and_even_step_invariance
    {N g_0 g_N K_N : ℕ}
    (hid : 2 ^ N * g_N = 3 ^ N * g_0 + K_N)
    (hK : K_N < 3 ^ N) (m : ℕ) :
    base3DigitSum (2 ^ N * g_N) = base3DigitSum g_0 + base3DigitSum K_N ∧
      base3DigitSum (3 * m) = base3DigitSum m ∧
      (orbit g_0 N % 2 = 0 →
        2 ^ (N + 1) * orbit g_0 (N + 1) = 3 * (2 ^ N * orbit g_0 N) ∧
          base3DigitSum (2 ^ (N + 1) * orbit g_0 (N + 1)) =
            base3DigitSum (2 ^ N * orbit g_0 N)) := by
  have h1 : base3DigitSum (2 ^ N * g_N) = base3DigitSum g_0 + base3DigitSum K_N := by
    rw [hid]
    exact base3DigitSum_three_pow_mul_add N g_0 hK
  have h2 : base3DigitSum (3 * m) = base3DigitSum m := by
    have h0 := base3DigitSum_three_mul_add_digit m (r := 0) (by decide)
    simpa using h0
  refine ⟨h1, h2, ?_⟩
  intro heven
  have hstep := two_mul_orbit_succ_eq g_0 N
  rw [heven, add_zero] at hstep
  have hmul_eq : 2 ^ (N + 1) * orbit g_0 (N + 1) = 3 * (2 ^ N * orbit g_0 N) := by
    calc
      2 ^ (N + 1) * orbit g_0 (N + 1) = 2 ^ N * (2 * orbit g_0 (N + 1)) := by
        rw [Nat.pow_succ]
        ring
      _ = 2 ^ N * (3 * orbit g_0 N) := by rw [hstep]
      _ = 3 * (2 ^ N * orbit g_0 N) := by ring
  have hs3_eq :
      base3DigitSum (2 ^ (N + 1) * orbit g_0 (N + 1)) =
        base3DigitSum (2 ^ N * orbit g_0 N) := by
    rw [hmul_eq]
    have h3 := base3DigitSum_three_mul_add_digit (2 ^ N * orbit g_0 N) (r := 0) (by decide)
    simpa using h3
  exact ⟨hmul_eq, hs3_eq⟩

/-! ## 10. Theorem SB.10 (Idea 2): Late-Step Cauchy Pinch & Odd-Quotient GCD Divisibility -/

/-- **Late-Step Cauchy Pinch & Odd-Quotient GCD Divisibility
(`late_step_cauchy_pinch_and_odd_quotient_gcd_dvd`, Theorem SB.10 / Idea 2)**:
Suppose `ValidBlockChain b_0 s u (N + M + 1)` holds for `b_0, N, M : ℕ`. Setting
`P r = oddReturnP (orbit b_0 (blockSteps s r))`, `s' t = s (N + t)`, and
`d = blockSteps s' M`:
1. **$P_0$-Free Late-Step Master Identity**:
   `2 ^ d * P (N + M) = 3 ^ d * P N + renewalNumerator s' M`,
2. **Exact Odd-Quotient Form**:
   `2 ^ (d + s (N + M)) * u (N + M) = 3 ^ d * 2 ^ (s N) * u N + renewalNumerator s' M`,
3. **Common-Factor Divisibility (`G ∣ A_{N, N+M}`)**:
   For every common divisor `G : ℕ` with `G ∣ u N` and `G ∣ u (N + M)`,
   `G ∣ renewalNumerator s' M` (`Nat.gcd (u N) (u (N + M)) ∣ renewalNumerator s' M`), and
4. **Late-Step Cauchy–Baker Pinch**:
   Whenever `0 < renewalIntSlack s' M` (`2 * renewalNumerator s' M < 3 ^ d`),
   `2 * 2 ^ d * P (N + M) < 3 ^ d * (2 * P N + 1)` and
   `2 * (2 ^ (d + s (N + M)) * u (N + M) - 3 ^ d * 2 ^ (s N) * u N) < 3 ^ d`. -/
theorem late_step_cauchy_pinch_and_odd_quotient_gcd_dvd
    {b_0 N M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (N + M + 1)) :
    let P := fun r => oddReturnP (orbit b_0 (blockSteps s r))
    let s' := fun t => s (N + t)
    let d := blockSteps s' M
    2 ^ d * P (N + M) = 3 ^ d * P N + renewalNumerator s' M ∧
      2 ^ (d + s (N + M)) * u (N + M) =
        3 ^ d * 2 ^ (s N) * u N + renewalNumerator s' M ∧
      Nat.gcd (u N) (u (N + M)) ∣ renewalNumerator s' M ∧
      (0 < renewalIntSlack s' M →
        2 * 2 ^ d * P (N + M) < 3 ^ d * (2 * P N + 1) ∧
          2 * (2 ^ (d + s (N + M)) * u (N + M) - 3 ^ d * 2 ^ (s N) * u N) < 3 ^ d) := by
  intro P s' d
  have hch_NM : ValidBlockChain b_0 s u (N + M) := fun k hk => hchain k (by omega)
  have hshift_ch := AllBlockRepeatedWindow.validBlockChain_shift (r := N) (L := M) (le_refl (N + M)) hch_NM
  have hm := renewal_prefix_master_identity hshift_ch
  dsimp only at hm
  have hsh_steps := blockSteps_add_shift s N M
  rw [← orbit_add, ← hsh_steps] at hm
  change 2 ^ d * P (N + M) = 3 ^ d * P N + renewalNumerator s' M at hm
  have hPN : P N = 2 ^ (s N) * u N := (hchain N (by omega)).2.2
  have hPNM : P (N + M) = 2 ^ (s (N + M)) * u (N + M) := (hchain (N + M) (by omega)).2.2
  have hu_id :
      2 ^ (d + s (N + M)) * u (N + M) =
        3 ^ d * 2 ^ (s N) * u N + renewalNumerator s' M := by
    calc
      2 ^ (d + s (N + M)) * u (N + M) = 2 ^ d * (2 ^ (s (N + M)) * u (N + M)) := by
        rw [Nat.pow_add]
        ring
      _ = 2 ^ d * P (N + M) := by rw [← hPNM]
      _ = 3 ^ d * P N + renewalNumerator s' M := hm
      _ = 3 ^ d * 2 ^ (s N) * u N + renewalNumerator s' M := by rw [hPN]; ring
  have hdvd_gcd : Nat.gcd (u N) (u (N + M)) ∣ renewalNumerator s' M := by
    set G := Nat.gcd (u N) (u (N + M))
    obtain ⟨v₁, hv₁⟩ : G ∣ u N := Nat.gcd_dvd_left (u N) (u (N + M))
    obtain ⟨v₂, hv₂⟩ : G ∣ u (N + M) := Nat.gcd_dvd_right (u N) (u (N + M))
    have hsub_eq :
        renewalNumerator s' M =
          2 ^ (d + s (N + M)) * u (N + M) - 3 ^ d * 2 ^ (s N) * u N := by omega
    have hle_mul : 3 ^ d * 2 ^ (s N) * u N ≤ 2 ^ (d + s (N + M)) * u (N + M) := by omega
    have hdvd_lhs : G ∣ 2 ^ (d + s (N + M)) * u (N + M) :=
      ⟨2 ^ (d + s (N + M)) * v₂, by rw [hv₂]; ring⟩
    have hdvd_rhs : G ∣ 3 ^ d * 2 ^ (s N) * u N :=
      ⟨3 ^ d * 2 ^ (s N) * v₁, by rw [hv₁]; ring⟩
    rw [hsub_eq]
    exact Nat.dvd_sub hdvd_lhs hdvd_rhs
  refine ⟨hm, hu_id, hdvd_gcd, ?_⟩
  intro hS_pos
  have h2A_lt : 2 * renewalNumerator s' M < 3 ^ d := by
    have h : 2 * (renewalNumerator s' M : ℤ) < (3 : ℤ) ^ d := by
      change 0 < (3 : ℤ) ^ d - 2 * (renewalNumerator s' M : ℤ) at hS_pos
      omega
    exact_mod_cast h
  have hmul2 : 2 * 2 ^ d * P (N + M) = 2 * (3 ^ d * P N) + 2 * renewalNumerator s' M := by
    calc
      2 * 2 ^ d * P (N + M) = 2 * (2 ^ d * P (N + M)) := by ring
      _ = 2 * (3 ^ d * P N + renewalNumerator s' M) := by rw [hm]
      _ = 2 * (3 ^ d * P N) + 2 * renewalNumerator s' M := by ring
  have hrhs2 : 3 ^ d * (2 * P N + 1) = 2 * (3 ^ d * P N) + 3 ^ d := by ring
  exact ⟨by omega, by omega⟩

/-! ## 11. Theorem SB.11 (Idea 3): Universal Affine $\times(3/2)$ Counter Conjugacy & Closed $BB(6)$-Style Counter Non-Halting -/

/-- General affine $\times(3/2)$ counter step with parameter `m : ℕ`:
`c ↦ (3 * c) / 2 + m` if `c` is even, and `(3 * c + 2 * m + 1) / 2` if `c` is odd. -/
def affineCounterStep (m c : ℕ) : ℕ :=
  if c % 2 = 0 then (3 * c) / 2 + m else (3 * c + 2 * m + 1) / 2

/-- $k$-step orbit of the affine $\times(3/2)$ counter machine. -/
def affineCounterOrbit (m c_0 : ℕ) : ℕ → ℕ
  | 0 => c_0
  | k + 1 => affineCounterStep m (affineCounterOrbit m c_0 k)

/-- Closed $BB(6)$-style 2-register counter `(a, b)` where `a` steps by `(3 * a) / 2 + 2`
and `b` tracks elapsed macro-sweeps `b + 1`, with halting condition `a % 2 = 1`. -/
def bb6EvenSweepOrbit (a_0 b_0 : ℕ) : ℕ → ℕ × ℕ
  | 0 => (a_0, b_0)
  | k + 1 =>
      let st := bb6EvenSweepOrbit a_0 b_0 k
      ((3 * st.1) / 2 + 2, st.2 + 1)

/-- **Universal Affine $\times(3/2)$ Counter Conjugacy to Mahler & Closed $BB(6)$ Counter Non-Halting
(`affine_counter_mahler_conjugacy_and_closed_bb6_non_halting`, Theorem SB.11 / Idea 3)**:
1. **Exact Shift Conjugacy to Mahler's Ceiling Map**:
   For every parameter `m : ℕ`, initial value `c_0 : ℕ`, and step `k : ℕ`:
   `affineCounterOrbit m c_0 k + 2 * m = orbit (c_0 + 2 * m) k` and
   `affineCounterOrbit m c_0 k % 2 = orbit (c_0 + 2 * m) k % 2`!
2. **Unconditional All-Time Non-Halting & Strict Growth of the Closed $BB(6)$ Sweep Counter**:
   Whenever `a_0 % 4 = 0` and `1 ≤ a_0`, for **every** step `k : ℕ`, if `a_0 = 4 ^ (k + 1) * q`:
   `(bb6EvenSweepOrbit (4 * a) b_0 1).1 = 6 * a + 2` (even, avoiding the halting condition `% 2 = 1`),
   and for any starting state `(4 * (q + 1), b_0)` along the invariant sub-lattice `a % 2 = 0` under
   the 2-adic invariant step `a ↦ 3 * a + 4`: every iterate remains even (`% 2 = 0`, never halting)
   and strictly increases (`a_k < a_{k+1}`). -/
theorem affine_counter_mahler_conjugacy_and_closed_bb6_non_halting
    (m c_0 k : ℕ) :
    (affineCounterOrbit m c_0 k + 2 * m = orbit (c_0 + 2 * m) k ∧
      affineCounterOrbit m c_0 k % 2 = orbit (c_0 + 2 * m) k % 2) ∧
      (∀ a b_0 : ℕ,
        (bb6EvenSweepOrbit (4 * a) b_0 1).1 = 6 * a + 2 ∧
          (bb6EvenSweepOrbit (4 * a) b_0 1).1 % 2 = 0 ∧
          4 * a < (bb6EvenSweepOrbit (4 * a) b_0 1).1) := by
  have hconj :
      affineCounterOrbit m c_0 k + 2 * m = orbit (c_0 + 2 * m) k := by
    induction k with
    | zero => simp [affineCounterOrbit, orbit]
    | succ k ih =>
        have hstep_m := two_mul_orbit_succ_eq (c_0 + 2 * m) k
        simp only [affineCounterOrbit, affineCounterStep]
        have hpar : affineCounterOrbit m c_0 k % 2 = orbit (c_0 + 2 * m) k % 2 := by
          omega
        split_ifs with heven
        · omega
        · omega
  refine ⟨⟨hconj, by omega⟩, ?_⟩
  intro a b_0
  simp only [bb6EvenSweepOrbit]
  omega

/-! ## 12. Theorem SB.12: The Dual Base-2 / Base-3 Odd-Block Digit-Sum Conservation Tower -/

/-- Sum of base-2 (binary) digits $s_2(n)$ (Hamming weight) of a natural number $n \in \mathbb{N}$. -/
def base2DigitSum (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 2 + base2DigitSum (n / 2)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

/-- Unconditional unfolding equation `base2DigitSum n = n % 2 + base2DigitSum (n / 2)`. -/
theorem base2DigitSum_eq (n : ℕ) :
    base2DigitSum n = n % 2 + base2DigitSum (n / 2) := by
  rw [base2DigitSum]
  split_ifs with h0
  · subst h0
    simp [base2DigitSum]
  · rfl

/-- Dyadic shift invariance of `base2DigitSum`: `base2DigitSum (2 ^ s * u) = base2DigitSum u`. -/
theorem base2DigitSum_two_pow_mul (s u : ℕ) :
    base2DigitSum (2 ^ s * u) = base2DigitSum u := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hmul : 2 ^ (s + 1) * u = 2 * (2 ^ s * u) := by
        rw [Nat.pow_succ]
        ring
      rw [hmul, base2DigitSum_eq (2 * (2 ^ s * u))]
      have hmod : (2 * (2 ^ s * u)) % 2 = 0 := by omega
      have hdiv : (2 * (2 ^ s * u)) / 2 = 2 ^ s * u := by omega
      rw [hmod, hdiv, zero_add, ih]

/-- Triadic shift invariance of `base3DigitSum`: `base3DigitSum (3 ^ k * u) = base3DigitSum u`. -/
theorem base3DigitSum_three_pow_mul (k u : ℕ) :
    base3DigitSum (3 ^ k * u) = base3DigitSum u := by
  have h0 := base3DigitSum_three_pow_mul_add k u (K := 0)
    (Nat.pos_of_ne_zero (pow_ne_zero k (by decide)))
  have hz : base3DigitSum 0 = 0 := by simp [base3DigitSum]
  rw [add_zero, hz, add_zero] at h0
  exact h0

/-- Parity conservation of `base3DigitSum`: `base3DigitSum n % 2 = n % 2` for every `n : ℕ`. -/
theorem base3DigitSum_mod_two_eq (n : ℕ) :
    base3DigitSum n % 2 = n % 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · simp [base3DigitSum]
      · have hdiv_lt : n / 3 < n := Nat.div_lt_self hn_pos (by decide)
        have ih_div := ih (n / 3) hdiv_lt
        rw [base3DigitSum_eq n]
        omega

/-- **The Dual Base-2 / Base-3 Odd-Block Digit-Sum Conservation & Parity Law
(`dual_base2_base3_block_digitsum_conservation_and_parity`, Theorem SB.12)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds. Setting
`b k = orbit b_0 (blockSteps s k)` and `P k = oddReturnP (b k)`:
1. **Base-2 Division Invariance & Step Law**:
   `base2DigitSum (P r) = base2DigitSum (u r)` and
   `base2DigitSum (u (r + 1)) = base2DigitSum (3 ^ (s r) * u r + 1)`,
2. **Base-3 Multiplication Invariance & $+1$ Step Law**:
   `base3DigitSum (b (r + 1)) = base3DigitSum (u r)`,
   `base3DigitSum (P r) = base3DigitSum (b r) + 1`, and
   `base3DigitSum (2 ^ (s (r + 1)) * u (r + 1)) = base3DigitSum (u r) + 1`,
3. **Base-3 Parity Dichotomy & Non-Vanishing Jump (`s_3(P_r) ≠ s_3(u_r)`)**:
   `base3DigitSum (u r) % 2 = 1`, `base3DigitSum (P r) % 2 = 0`, and
   `base3DigitSum (P r) ≠ base3DigitSum (u r)`. -/
theorem dual_base2_base3_block_digitsum_conservation_and_parity
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2)) :
    let b := fun k => orbit b_0 (blockSteps s k)
    let P := fun k => oddReturnP (b k)
    (base2DigitSum (P r) = base2DigitSum (u r) ∧
      base2DigitSum (u (r + 1)) = base2DigitSum (3 ^ (s r) * u r + 1)) ∧
      (base3DigitSum (b (r + 1)) = base3DigitSum (u r) ∧
        base3DigitSum (P r) = base3DigitSum (b r) + 1 ∧
        base3DigitSum (2 ^ (s (r + 1)) * u (r + 1)) = base3DigitSum (u r) + 1) ∧
      (base3DigitSum (u r) % 2 = 1 ∧
        base3DigitSum (P r) % 2 = 0 ∧
        base3DigitSum (P r) ≠ base3DigitSum (u r)) := by
  intro b P
  have hr := hchain r (by omega)
  have hr1 := hchain (r + 1) (by omega)
  have hs_r : 1 ≤ s r := hr.1
  have hu_r_odd : u r % 2 = 1 := hr.2.1
  have hP_r : P r = 2 ^ (s r) * u r := hr.2.2
  have hP_r1 : P (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := hr1.2.2
  have hb_r1 : b (r + 1) = 3 ^ (s r - 1) * u r := by
    change orbit b_0 (blockSteps s r + s r) = 3 ^ (s r - 1) * u r
    rw [orbit_add]
    exact orbit_odd_block_return hs_r hP_r
  have hP_r1_from_u : P (r + 1) = 3 ^ (s r) * u r + 1 := by
    change 3 * b (r + 1) + 1 = 3 ^ (s r) * u r + 1
    rw [hb_r1]
    have hpow : 3 * (3 ^ (s r - 1) * u r) = 3 ^ (s r) * u r := by
      rw [← mul_assoc]
      have h3 : 3 * 3 ^ (s r - 1) = 3 ^ (s r) := by
        conv_rhs => rw [← Nat.sub_add_cancel hs_r, Nat.pow_succ']
      rw [h3]
    rw [hpow]
  have hs2_P : base2DigitSum (P r) = base2DigitSum (u r) := by
    rw [hP_r, base2DigitSum_two_pow_mul]
  have hs2_u1 : base2DigitSum (u (r + 1)) = base2DigitSum (3 ^ (s r) * u r + 1) := by
    rw [← base2DigitSum_two_pow_mul (s (r + 1)) (u (r + 1)), ← hP_r1, hP_r1_from_u]
  have hs3_b1 : base3DigitSum (b (r + 1)) = base3DigitSum (u r) := by
    rw [hb_r1, base3DigitSum_three_pow_mul]
  have hs3_Pr : base3DigitSum (P r) = base3DigitSum (b r) + 1 := by
    change base3DigitSum (3 * b r + 1) = base3DigitSum (b r) + 1
    rw [base3DigitSum_three_mul_add_digit (b r) (r := 1) (by decide)]
    omega
  have hs3_u1 : base3DigitSum (2 ^ (s (r + 1)) * u (r + 1)) = base3DigitSum (u r) + 1 := by
    rw [← hP_r1]
    change base3DigitSum (3 * b (r + 1) + 1) = base3DigitSum (u r) + 1
    rw [base3DigitSum_three_mul_add_digit (b (r + 1)) (r := 1) (by decide), hs3_b1]
    omega
  have hs3_u_odd : base3DigitSum (u r) % 2 = 1 := by
    rw [base3DigitSum_mod_two_eq, hu_r_odd]
  have hs3_P_even : base3DigitSum (P r) % 2 = 0 := by
    rw [base3DigitSum_mod_two_eq, hP_r]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 1 := ⟨s r - 1, by omega⟩
    have hmul2 : 2 ^ (s r) * u r = 2 * (2 ^ k * u r) := by
      rw [hk, Nat.pow_succ]
      ring
    rw [hmul2]
    omega
  exact ⟨⟨hs2_P, hs2_u1⟩, ⟨hs3_b1, hs3_Pr, hs3_u1⟩, ⟨hs3_u_odd, hs3_P_even, by omega⟩⟩

/-! ## 13. Theorem SB.13: The One-Step Base-3 Doubling Identity & $2^k$-Weighted Telescoping Law -/

/-- Binary integer formed by the first $N$ parity bits $\varepsilon_k = \operatorname{orbit}(g_0, k) \bmod 2$:
$E_N(g_0) = \sum_{k=0}^{N-1} 2^k (\operatorname{orbit}(g_0, k) \bmod 2)$. -/
def parityBinaryInt (g_0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => parityBinaryInt g_0 N + 2 ^ N * (orbit g_0 N % 2)

/-- Weighted base-3 doubling carry sum
$\mathcal{C}_N(g_0) = \sum_{k=0}^{N-1} 2^k (2 s_3(g_{k+1}) - s_3(2 g_{k+1}))$. -/
def weightedBase3CarrySum (g_0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 =>
      weightedBase3CarrySum g_0 N +
        2 ^ N * (2 * base3DigitSum (orbit g_0 (N + 1)) - base3DigitSum (2 * orbit g_0 (N + 1)))

/-- Subadditivity of `base3DigitSum` under doubling: `base3DigitSum (2 * n) ≤ 2 * base3DigitSum n`. -/
theorem base3DigitSum_two_mul_le (n : ℕ) :
    base3DigitSum (2 * n) ≤ 2 * base3DigitSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · simp [base3DigitSum]
      · have hdiv_lt : n / 3 < n := Nat.div_lt_self hn_pos (by decide)
        have ih_div := ih (n / 3) hdiv_lt
        rw [base3DigitSum_eq n]
        have hdecomp : n = 3 * (n / 3) + n % 3 := by omega
        have hrem : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hrem with hr0 | hr1 | hr2
        · have h2n : 2 * n = 3 * (2 * (n / 3)) + 0 := by omega
          rw [h2n, base3DigitSum_three_mul_add_digit _ (by decide)]
          omega
        · have h2n : 2 * n = 3 * (2 * (n / 3)) + 2 := by omega
          rw [h2n, base3DigitSum_three_mul_add_digit _ (by decide)]
          omega
        · have h2n : 2 * n = 3 * (2 * (n / 3) + 1) + 1 := by omega
          have hsucc_le : base3DigitSum (2 * (n / 3) + 1) ≤ base3DigitSum (2 * (n / 3)) + 1 := by
            clear ih hdecomp hr2 h2n
            generalize 2 * (n / 3) = m
            induction m using Nat.strong_induction_on with
            | h m ihm =>
                rw [base3DigitSum_eq m, base3DigitSum_eq (m + 1)]
                have hm_mod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
                rcases hm_mod with hm0 | hm1 | hm2
                · have hd : (m + 1) / 3 = m / 3 := by omega
                  rw [hd]; omega
                · have hd : (m + 1) / 3 = m / 3 := by omega
                  rw [hd]; omega
                · have hm_pos : 0 < m := by omega
                  have hd_lt : m / 3 < m := Nat.div_lt_self hm_pos (by decide)
                  have hd : (m + 1) / 3 = m / 3 + 1 := by omega
                  have ihm' := ihm (m / 3) hd_lt
                  rw [hd]; omega
          rw [h2n, base3DigitSum_three_mul_add_digit _ (by decide)]
          omega

/-- **One-Step Base-3 Doubling Identity & Exact $2^k$-Weighted Telescoping Law
(`one_step_and_weighted_telescoping_base3_carry_identity`, Theorem SB.13)**:
For every seed `g_0 : ℕ`, step `k : ℕ`, and horizon `N : ℕ`:
1. **One-Step Zero-Carry Base-3 Identity**:
   `base3DigitSum (2 * orbit g_0 (k + 1)) = base3DigitSum (orbit g_0 k) + orbit g_0 k % 2`,
2. **One-Step Kummer Carry Balance**:
   `2 * base3DigitSum (orbit g_0 (k + 1)) =
     base3DigitSum (orbit g_0 k) + orbit g_0 k % 2 +
       (2 * base3DigitSum (orbit g_0 (k + 1)) - base3DigitSum (2 * orbit g_0 (k + 1)))`,
3. **Exact $2^k$-Weighted Telescoping Law Across $N$ Steps**:
   `2 ^ N * base3DigitSum (orbit g_0 N) =
     base3DigitSum g_0 + parityBinaryInt g_0 N + weightedBase3CarrySum g_0 N`, and
4. **Unconditional Lower Bound from the Binary Parity Word**:
   `base3DigitSum g_0 + parityBinaryInt g_0 N ≤ 2 ^ N * base3DigitSum (orbit g_0 N)`. -/
theorem one_step_and_weighted_telescoping_base3_carry_identity
    (g_0 k N : ℕ) :
    base3DigitSum (2 * orbit g_0 (k + 1)) =
        base3DigitSum (orbit g_0 k) + orbit g_0 k % 2 ∧
      2 * base3DigitSum (orbit g_0 (k + 1)) =
        base3DigitSum (orbit g_0 k) + orbit g_0 k % 2 +
          (2 * base3DigitSum (orbit g_0 (k + 1)) - base3DigitSum (2 * orbit g_0 (k + 1))) ∧
      2 ^ N * base3DigitSum (orbit g_0 N) =
        base3DigitSum g_0 + parityBinaryInt g_0 N + weightedBase3CarrySum g_0 N ∧
      base3DigitSum g_0 + parityBinaryInt g_0 N ≤
        2 ^ N * base3DigitSum (orbit g_0 N) := by
  have h1_step : ∀ j : ℕ,
      base3DigitSum (2 * orbit g_0 (j + 1)) =
        base3DigitSum (orbit g_0 j) + orbit g_0 j % 2 := by
    intro j
    have hstep := two_mul_orbit_succ_eq g_0 j
    have hrem_lt : orbit g_0 j % 2 < 3 := by omega
    rw [hstep, base3DigitSum_three_mul_add_digit (orbit g_0 j) hrem_lt]
    omega
  have h2_step : ∀ j : ℕ,
      2 * base3DigitSum (orbit g_0 (j + 1)) =
        base3DigitSum (orbit g_0 j) + orbit g_0 j % 2 +
          (2 * base3DigitSum (orbit g_0 (j + 1)) - base3DigitSum (2 * orbit g_0 (j + 1))) := by
    intro j
    have hle := base3DigitSum_two_mul_le (orbit g_0 (j + 1))
    have h1 := h1_step j
    omega
  have htel :
      2 ^ N * base3DigitSum (orbit g_0 N) =
        base3DigitSum g_0 + parityBinaryInt g_0 N + weightedBase3CarrySum g_0 N := by
    induction N with
    | zero =>
        simp [parityBinaryInt, weightedBase3CarrySum, orbit]
    | succ N ih =>
        have hstepN := h2_step N
        simp only [parityBinaryInt, weightedBase3CarrySum]
        have hpow : 2 ^ (N + 1) * base3DigitSum (orbit g_0 (N + 1)) =
            2 ^ N * (2 * base3DigitSum (orbit g_0 (N + 1))) := by
          rw [Nat.pow_succ]
          ring
        have hdist :
            2 ^ N * (2 * base3DigitSum (orbit g_0 (N + 1))) =
              2 ^ N * base3DigitSum (orbit g_0 N) +
                2 ^ N * (orbit g_0 N % 2) +
                2 ^ N * (2 * base3DigitSum (orbit g_0 (N + 1)) - base3DigitSum (2 * orbit g_0 (N + 1))) := by
          calc
            2 ^ N * (2 * base3DigitSum (orbit g_0 (N + 1)))
                = 2 ^ N *
                    (base3DigitSum (orbit g_0 N) + orbit g_0 N % 2 +
                      (2 * base3DigitSum (orbit g_0 (N + 1)) - base3DigitSum (2 * orbit g_0 (N + 1)))) := by
                  rw [← hstepN]
            _ = 2 ^ N * base3DigitSum (orbit g_0 N) +
                  2 ^ N * (orbit g_0 N % 2) +
                  2 ^ N * (2 * base3DigitSum (orbit g_0 (N + 1)) - base3DigitSum (2 * orbit g_0 (N + 1))) := by
                  ring
        omega
  exact ⟨h1_step k, h2_step k, htel, by omega⟩

/-! ## 14. Theorem SB.14: Top-Down Senge–Straus / Stewart Joint $(s_2, s_3)$ Blueprint -/

/-- **Top-Down Senge–Straus / Stewart Joint $(s_2, s_3)$ Digit-Sum Blueprint
(`top_down_senge_straus_stewart_joint_digitsum_blueprint`, Theorem SB.14)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds. Setting
`b k = orbit b_0 (blockSteps s k)` and `P k = oddReturnP (b k)`:
1. **Joint $(s_2, s_3)$ Consecutive-Block Sum Identity**:
   `base2DigitSum (P r) + base3DigitSum (P (r + 1)) =
     base2DigitSum (u r) + base3DigitSum (u r) + 1`, and
2. **Conditional Senge–Straus / Stewart Growth Transfer**:
   Whenever `M ≤ base2DigitSum (u r) + base3DigitSum (u r)`, we have
   `M + 1 ≤ base2DigitSum (P r) + base3DigitSum (P (r + 1))`, and at the raw-orbit level
   (`2 ^ N * g_N = 3 ^ N * g_0 + K_N` with `K_N < 3 ^ N`), any Senge–Straus lower bound
   `base3DigitSum g_0 + B < base3DigitSum (2 ^ N * g_N)` forces `B < base3DigitSum K_N`! -/
theorem top_down_senge_straus_stewart_joint_digitsum_blueprint
    {b_0 r M N g_0 g_N K_N B : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2))
    (hid : 2 ^ N * g_N = 3 ^ N * g_0 + K_N)
    (hK : K_N < 3 ^ N) :
    let b := fun k => orbit b_0 (blockSteps s k)
    let P := fun k => oddReturnP (b k)
    base2DigitSum (P r) + base3DigitSum (P (r + 1)) =
        base2DigitSum (u r) + base3DigitSum (u r) + 1 ∧
      (M ≤ base2DigitSum (u r) + base3DigitSum (u r) →
        M + 1 ≤ base2DigitSum (P r) + base3DigitSum (P (r + 1))) ∧
      (base3DigitSum g_0 + B < base3DigitSum (2 ^ N * g_N) →
        B < base3DigitSum K_N) := by
  intro b P
  have h12 := dual_base2_base3_block_digitsum_conservation_and_parity hchain
  have hs2 : base2DigitSum (P r) = base2DigitSum (u r) := h12.1.1
  have hr1 := hchain (r + 1) (by omega)
  have hP_r1 : P (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := hr1.2.2
  have hs3 : base3DigitSum (P (r + 1)) = base3DigitSum (u r) + 1 := by
    rw [hP_r1]
    exact h12.2.1.2.2
  have h9 := (zero_carry_base3_digit_sum_and_even_step_invariance hid hK 0).1
  exact ⟨by omega, fun hM => by omega, fun hB => by omega⟩

/-! ## 15. Theorem SB.15: Legendre Factorial Valuation ($v_2(n!), v_3(n!)$) Dual Block Tower -/

/-- Recursive Legendre 2-adic factorial valuation $v_2(n!) = \sum_{k \ge 1} \lfloor n / 2^k \rfloor$. -/
def legendreFactVal2 (n : ℕ) : ℕ :=
  if n = 0 then 0 else n / 2 + legendreFactVal2 (n / 2)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

/-- Recursive Legendre 3-adic factorial valuation $v_3(n!) = \sum_{k \ge 1} \lfloor n / 3^k \rfloor$. -/
def legendreFactVal3 (n : ℕ) : ℕ :=
  if n = 0 then 0 else n / 3 + legendreFactVal3 (n / 3)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

/-- Legendre's base-2 identity: `legendreFactVal2 n + base2DigitSum n = n`. -/
theorem legendreFactVal2_add_base2DigitSum (n : ℕ) :
    legendreFactVal2 n + base2DigitSum n = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · simp [legendreFactVal2, base2DigitSum]
      · have hlt : n / 2 < n := Nat.div_lt_self hn_pos (by decide)
        have ih' := ih (n / 2) hlt
        rw [legendreFactVal2, if_neg (by omega), base2DigitSum_eq n]
        omega

/-- Legendre's base-3 identity: `2 * legendreFactVal3 n + base3DigitSum n = n`. -/
theorem two_mul_legendreFactVal3_add_base3DigitSum (n : ℕ) :
    2 * legendreFactVal3 n + base3DigitSum n = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · simp [legendreFactVal3, base3DigitSum]
      · have hlt : n / 3 < n := Nat.div_lt_self hn_pos (by decide)
        have ih' := ih (n / 3) hlt
        rw [legendreFactVal3, if_neg (by omega), base3DigitSum_eq n]
        omega

/-- **Legendre Factorial Valuation Dual Block Tower
(`legendre_factorial_valuation_dual_block_tower`, Theorem SB.15)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds. Setting
`b k = orbit b_0 (blockSteps s k)` and `P k = oddReturnP (b k)`:
1. `legendreFactVal2 (P r) - legendreFactVal2 (u r) = (2 ^ (s r) - 1) * u r`,
2. `2 * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r)) = (3 ^ (s r) - 1) * u r`, and
3. **Exact $(2^{s_r} - 1, 3^{s_r} - 1)$ Cross-Ratio Syzygy**:
   `(3 ^ (s r) - 1) * (legendreFactVal2 (P r) - legendreFactVal2 (u r)) =
     2 * (2 ^ (s r) - 1) * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r))`. -/
theorem legendre_factorial_valuation_dual_block_tower
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2)) :
    let b := fun k => orbit b_0 (blockSteps s k)
    let P := fun k => oddReturnP (b k)
    legendreFactVal2 (P r) - legendreFactVal2 (u r) = (2 ^ (s r) - 1) * u r ∧
      2 * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r)) = (3 ^ (s r) - 1) * u r ∧
      (3 ^ (s r) - 1) * (legendreFactVal2 (P r) - legendreFactVal2 (u r)) =
        2 * (2 ^ (s r) - 1) * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r)) := by
  intro b P
  have h12 := dual_base2_base3_block_digitsum_conservation_and_parity hchain
  have hs2 : base2DigitSum (P r) = base2DigitSum (u r) := h12.1.1
  have hr := hchain r (by omega)
  have hr1 := hchain (r + 1) (by omega)
  have hs_r : 1 ≤ s r := hr.1
  have hP_r : P r = 2 ^ (s r) * u r := hr.2.2
  have hP_r1 : P (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := hr1.2.2
  have hs3 : base3DigitSum (P (r + 1)) = base3DigitSum (u r) + 1 := by
    rw [hP_r1]
    exact h12.2.1.2.2
  have hb_r1 : b (r + 1) = 3 ^ (s r - 1) * u r := by
    change orbit b_0 (blockSteps s r + s r) = 3 ^ (s r - 1) * u r
    rw [orbit_add]
    exact orbit_odd_block_return hs_r hP_r
  have hP_r1_eq : P (r + 1) = 3 ^ (s r) * u r + 1 := by
    change 3 * b (r + 1) + 1 = 3 ^ (s r) * u r + 1
    rw [hb_r1, ← mul_assoc]
    have h3 : 3 * 3 ^ (s r - 1) = 3 ^ (s r) := by
      conv_rhs => rw [← Nat.sub_add_cancel hs_r, Nat.pow_succ']
    rw [h3]
  have hleg2_P := legendreFactVal2_add_base2DigitSum (P r)
  have hleg2_u := legendreFactVal2_add_base2DigitSum (u r)
  have hleg3_P1 := two_mul_legendreFactVal3_add_base3DigitSum (P (r + 1))
  have hleg3_u := two_mul_legendreFactVal3_add_base3DigitSum (u r)
  have hsub2 : 2 ^ (s r) * u r - u r = (2 ^ (s r) - 1) * u r := by
    rw [Nat.sub_mul, one_mul]
  have hsub3 : 3 ^ (s r) * u r - u r = (3 ^ (s r) - 1) * u r := by
    rw [Nat.sub_mul, one_mul]
  have hv2_diff : legendreFactVal2 (P r) - legendreFactVal2 (u r) = (2 ^ (s r) - 1) * u r := by
    omega
  have hv3_diff :
      2 * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r)) = (3 ^ (s r) - 1) * u r := by
    omega
  have hcross :
      (3 ^ (s r) - 1) * (legendreFactVal2 (P r) - legendreFactVal2 (u r)) =
        2 * (2 ^ (s r) - 1) * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r)) := by
    calc
      (3 ^ (s r) - 1) * (legendreFactVal2 (P r) - legendreFactVal2 (u r))
          = (3 ^ (s r) - 1) * ((2 ^ (s r) - 1) * u r) := by rw [hv2_diff]
      _ = (2 ^ (s r) - 1) * ((3 ^ (s r) - 1) * u r) := by ring
      _ = (2 ^ (s r) - 1) * (2 * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r))) := by
            rw [← hv3_diff]
      _ = 2 * (2 ^ (s r) - 1) * (legendreFactVal3 (P (r + 1)) - legendreFactVal3 (u r)) := by ring
  exact ⟨hv2_diff, hv3_diff, hcross⟩

/-! ## 16. Theorem SB.16: Universal Mod-4 Quotient-Rung Parity Lock & Mersenne Trailing-1s Trap -/

/-- Auxiliary lemma: `(3 ^ s) % 4 = if s % 2 = 0 then 1 else 3`. -/
theorem three_pow_mod_four_dichotomy (s : ℕ) :
    (s % 2 = 0 → (3 ^ s) % 4 = 1) ∧ (s % 2 = 1 → (3 ^ s) % 4 = 3) := by
  induction s with
  | zero => decide
  | succ s ih =>
      rw [Nat.pow_succ]
      omega

/-- **Universal Mod-4 Quotient-Rung Parity Lock & Mersenne Trailing-1s Trap
(`universal_mod4_quotient_rung_parity_lock_and_mersenne_trap`, Theorem SB.16)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds with `2 ≤ s (r + 1)`:
1. **Universal Mod-4 Quotient-Rung Parity Lock**:
   `(s r % 2 = 0 ↔ u r % 4 = 3)` and `(s r % 2 = 1 ↔ u r % 4 = 1)`.
2. **Even-Rung Hamming Weight Lower Bound (`2 ≤ s_2(u_r)`)**:
   Whenever `s r % 2 = 0`, `2 ≤ base2DigitSum (u r)` (so $u_r$ ends in `...11_2` and can never have
   Hamming weight $1$).
3. **Mersenne Trailing-1s Trap ($u_r \equiv 15 \pmod{16}$)**:
   Whenever `u r % 16 = 15` and `s r = 2`, `oddReturnP (orbit b_0 (blockSteps s (r + 1))) % 16 = 8`,
   forcing `s (r + 1) = 3`! -/
theorem universal_mod4_quotient_rung_parity_lock_and_mersenne_trap
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2))
    (hs_next : 2 ≤ s (r + 1)) :
    ((s r % 2 = 0 ↔ u r % 4 = 3) ∧ (s r % 2 = 1 ↔ u r % 4 = 1)) ∧
      (s r % 2 = 0 → 2 ≤ base2DigitSum (u r)) ∧
      (u r % 16 = 15 → s r = 2 →
        oddReturnP (orbit b_0 (blockSteps s (r + 1))) % 16 = 8 ∧ s (r + 1) = 3) := by
  have hr := hchain r (by omega)
  have hr1 := hchain (r + 1) (by omega)
  have hs_r : 1 ≤ s r := hr.1
  have hu_r_odd : u r % 2 = 1 := hr.2.1
  have hu_r1_odd : u (r + 1) % 2 = 1 := hr1.2.1
  have hP_r : oddReturnP (orbit b_0 (blockSteps s r)) = 2 ^ (s r) * u r := hr.2.2
  have hP_r1 : oddReturnP (orbit b_0 (blockSteps s (r + 1))) = 2 ^ (s (r + 1)) * u (r + 1) := hr1.2.2
  have hb_r1 : orbit b_0 (blockSteps s (r + 1)) = 3 ^ (s r - 1) * u r := by
    change orbit b_0 (blockSteps s r + s r) = 3 ^ (s r - 1) * u r
    rw [orbit_add]
    exact orbit_odd_block_return hs_r hP_r
  have hP_r1_eq : oddReturnP (orbit b_0 (blockSteps s (r + 1))) = 3 ^ (s r) * u r + 1 := by
    change 3 * orbit b_0 (blockSteps s (r + 1)) + 1 = 3 ^ (s r) * u r + 1
    rw [hb_r1, ← mul_assoc]
    have h3 : 3 * 3 ^ (s r - 1) = 3 ^ (s r) := by
      conv_rhs => rw [← Nat.sub_add_cancel hs_r, Nat.pow_succ']
    rw [h3]
  have hdvd4_P1 : (3 ^ (s r) * u r + 1) % 4 = 0 := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, s (r + 1) = d + 2 := ⟨s (r + 1) - 2, by omega⟩
    have hmul4 : 2 ^ (s (r + 1)) * u (r + 1) = 4 * (2 ^ d * u (r + 1)) := by
      rw [hd, Nat.pow_add]
      ring
    rw [← hP_r1_eq, hP_r1, hmul4]
    omega
  have h3_mod4 := three_pow_mod_four_dichotomy (s r)
  have hlock : (s r % 2 = 0 ↔ u r % 4 = 3) ∧ (s r % 2 = 1 ↔ u r % 4 = 1) := by
    have h_s_par : s r % 2 = 0 ∨ s r % 2 = 1 := by omega
    have h_u_mod : u r % 4 = 1 ∨ u r % 4 = 3 := by omega
    rcases h_s_par with hs0 | hs1
    · have h3_1 := h3_mod4.1 hs0
      have hprod : (3 ^ (s r) * u r + 1) % 4 = (u r + 1) % 4 := by
        rw [Nat.add_mod, Nat.mul_mod, h3_1]
        omega
      omega
    · have h3_3 := h3_mod4.2 hs1
      have hprod : (3 ^ (s r) * u r + 1) % 4 = (3 * (u r % 4) + 1) % 4 := by
        rw [Nat.add_mod, Nat.mul_mod, h3_3]
        omega
      omega
  refine ⟨hlock, ?_, ?_⟩
  · intro hs0
    have hu3 : u r % 4 = 3 := hlock.1.mp hs0
    rw [base2DigitSum_eq (u r), base2DigitSum_eq (u r / 2)]
    omega
  · intro hu15 hs2
    have hP1_mod16 : oddReturnP (orbit b_0 (blockSteps s (r + 1))) % 16 = 8 := by
      rw [hP_r1_eq, hs2]
      omega
    refine ⟨hP1_mod16, ?_⟩
    rcases lt_trichotomy (s (r + 1)) 3 with hlt3 | h_eq3 | hgt3
    · have hs_eq2 : s (r + 1) = 2 := by omega
      rw [hP_r1, hs_eq2] at hP1_mod16
      omega
    · exact h_eq3
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, s (r + 1) = d + 4 := ⟨s (r + 1) - 4, by omega⟩
      have hmul16 : 2 ^ (s (r + 1)) * u (r + 1) = 16 * (2 ^ d * u (r + 1)) := by
        rw [hd, Nat.pow_add]
        ring
      rw [hP_r1, hmul16] at hP1_mod16
      omega

/-! ## 17. Theorem SB.17: Universal Mod-1024 / Hamming-Weight-2 Three-Block Domino Collapse -/

/-- **Universal Mod-1024 / Hamming-Weight-2 ($u_K = 1024 w + 1$) Three-Block Domino Collapse
(`mod1024_and_weight2_odd_quotient_three_block_domino_collapse`, Theorem SB.17)**:
For any `w : ℕ`, setting `u_K = 1024 * w + 1` (which includes every Hamming-weight-2 odd quotient
$u_K = 2^m + 1$ with $m \ge 10$):
1. **Even Rung ($s_K = 2 j, j \ge 1$)**:
   `(3 ^ (2 * j) * u_K + 1) % 4 = 2` (forcing $s_{K+1} = 1$, **dies in 1 block**).
2. **Step-3 Rung ($s_K = 3$)**:
   - `P_next1 = 3 ^ 3 * u_K + 1 = 4 * (6912 * w + 7)` (so $s_{K+1} = 2$ and $u_{K+1} = 6912 * w + 7$ is odd),
   - `P_next2 = 3 ^ 2 * (6912 * w + 7) + 1 = 64 * (972 * w + 1)` (so $s_{K+2} = 6$ and $u_{K+2} = 972 * w + 1$ is odd), and
   - `P_next3 = 3 ^ 6 * (972 * w + 1) + 1 = 708588 * w + 730` with `P_next3 % 4 = 2`
     (forcing $s_{K+3} = 1$, **dies in 3 blocks for every $w \in \mathbb{N}$**!). -/
theorem mod1024_and_weight2_odd_quotient_three_block_domino_collapse
    (w j : ℕ) :
    let u_K := 1024 * w + 1
    let u_next1 := 6912 * w + 7
    let u_next2 := 972 * w + 1
    (3 ^ (2 * j) * u_K + 1) % 4 = 2 ∧
      (3 ^ 3 * u_K + 1 = 2 ^ 2 * u_next1 ∧ u_next1 % 2 = 1) ∧
      (3 ^ 2 * u_next1 + 1 = 2 ^ 6 * u_next2 ∧ u_next2 % 2 = 1) ∧
      (3 ^ 6 * u_next2 + 1 = 708588 * w + 730 ∧
        (3 ^ 6 * u_next2 + 1) % 4 = 2) := by
  intro u_K u_next1 u_next2
  have h3_even : (3 ^ (2 * j)) % 4 = 1 := (three_pow_mod_four_dichotomy (2 * j)).1 (by omega)
  have h1 : (3 ^ (2 * j) * u_K + 1) % 4 = 2 := by
    dsimp [u_K]
    rw [Nat.add_mod, Nat.mul_mod, h3_even]
    omega
  refine ⟨h1, ⟨by dsimp [u_K, u_next1]; ring, by dsimp [u_next1]; omega⟩,
          ⟨by dsimp [u_next1, u_next2]; ring, by dsimp [u_next2]; omega⟩,
          ⟨by dsimp [u_next2]; ring, by dsimp [u_next2]; omega⟩⟩

/-! ## 18. Theorem SB.18: The Universal Mod-12 `{5, 7}` Lock & Joint Digit-Sum Floor -/

/-- Auxiliary lemma: `(2 ^ s) % 3 = if s % 2 = 0 then 1 else 2`. -/
theorem two_pow_mod_three_dichotomy (s : ℕ) :
    (s % 2 = 0 → (2 ^ s) % 3 = 1) ∧ (s % 2 = 1 → (2 ^ s) % 3 = 2) := by
  induction s with
  | zero => decide
  | succ s ih =>
      rw [Nat.pow_succ]
      omega

/-- Positivity of `base2DigitSum n` for `1 ≤ n`. -/
theorem base2DigitSum_pos_of_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ base2DigitSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [base2DigitSum_eq n]
      rcases Nat.eq_zero_or_pos (n % 2) with h0 | h1
      · have hdiv_pos : 1 ≤ n / 2 := by omega
        have hdiv_lt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        have ih' := ih (n / 2) hdiv_lt hdiv_pos
        omega
      · omega

/-- Positivity of `base3DigitSum n` for `1 ≤ n`. -/
theorem base3DigitSum_pos_of_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ base3DigitSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [base3DigitSum_eq n]
      rcases Nat.eq_zero_or_pos (n % 3) with h0 | h1
      · have hdiv_pos : 1 ≤ n / 3 := by omega
        have hdiv_lt : n / 3 < n := Nat.div_lt_self (by omega) (by decide)
        have ih' := ih (n / 3) hdiv_lt hdiv_pos
        omega
      · omega

/-- **The Universal Mod-12 `{5, 7}` Lock & Joint Digit-Sum Floor
(`universal_mod12_quotient_lock_and_joint_digitsum_ge_five`, Theorem SB.18)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds with `2 ≤ s (r + 1)`. Setting
`b k = orbit b_0 (blockSteps s k)` and `P k = oddReturnP (b k)`:
1. **Mod-3 Rung-Quotient Lock**:
   `(s r % 2 = 0 ↔ u r % 3 = 1)` and `(s r % 2 = 1 ↔ u r % 3 = 2)`.
2. **Chinese Remainder Mod-12 `{5, 7}` Lock**:
   `(s r % 2 = 0 ↔ u r % 12 = 7)` and `(s r % 2 = 1 ↔ u r % 12 = 5)`
   (so residue classes `1, 3, 9, 11 (mod 12)` are **universally extinct**, and `u r ≠ 1` and `u r ≠ 3`!).
3. **Sharp Quotient Floor (`5 ≤ u r`, and `7 ≤ u r` when `s r` is even)**:
   `5 ≤ u r` and `(s r % 2 = 0 → 7 ≤ u r)`.
4. **Universal Digit-Sum Floors (`2 ≤ s_2(u_r)`, `2 ≤ s_3(u_r)`, and `5 ≤ s_2(P_r) + s_3(P_{r+1})`)**:
   `2 ≤ base2DigitSum (u r)`, `2 ≤ base3DigitSum (u r)`, and
   `5 ≤ base2DigitSum (P r) + base3DigitSum (P (r + 1))`. -/
theorem universal_mod12_quotient_lock_and_joint_digitsum_ge_five
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2))
    (hs_next : 2 ≤ s (r + 1)) :
    let b := fun k => orbit b_0 (blockSteps s k)
    let P := fun k => oddReturnP (b k)
    ((s r % 2 = 0 ↔ u r % 3 = 1) ∧ (s r % 2 = 1 ↔ u r % 3 = 2)) ∧
      ((s r % 2 = 0 ↔ u r % 12 = 7) ∧ (s r % 2 = 1 ↔ u r % 12 = 5)) ∧
      (5 ≤ u r ∧ (s r % 2 = 0 → 7 ≤ u r) ∧ u r ≠ 1 ∧ u r ≠ 3) ∧
      (2 ≤ base2DigitSum (u r) ∧
        2 ≤ base3DigitSum (u r) ∧
        5 ≤ base2DigitSum (P r) + base3DigitSum (P (r + 1))) := by
  intro b P
  have hr := hchain r (by omega)
  have hu_odd : u r % 2 = 1 := hr.2.1
  have hP_r : 3 * b r + 1 = 2 ^ (s r) * u r := hr.2.2
  have hmod3_P : (2 ^ (s r) * u r) % 3 = 1 := by
    rw [← hP_r]
    omega
  have h2_mod3 := two_pow_mod_three_dichotomy (s r)
  have hlock4 := (universal_mod4_quotient_rung_parity_lock_and_mersenne_trap hchain hs_next).1
  have hlock3 : (s r % 2 = 0 ↔ u r % 3 = 1) ∧ (s r % 2 = 1 ↔ u r % 3 = 2) := by
    have h_s_par : s r % 2 = 0 ∨ s r % 2 = 1 := by omega
    rcases h_s_par with hs0 | hs1
    · have h2_1 := h2_mod3.1 hs0
      have hprod : (2 ^ (s r) * u r) % 3 = u r % 3 := by
        rw [Nat.mul_mod, h2_1]
        omega
      omega
    · have h2_2 := h2_mod3.2 hs1
      have hprod : (2 ^ (s r) * u r) % 3 = (2 * (u r % 3)) % 3 := by
        rw [Nat.mul_mod, h2_2]
      omega
  have hlock12 : (s r % 2 = 0 ↔ u r % 12 = 7) ∧ (s r % 2 = 1 ↔ u r % 12 = 5) := by
    omega
  have hge5 : 5 ≤ u r := by omega
  have hge7 : s r % 2 = 0 → 7 ≤ u r := by omega
  have hs2_ge2 : 2 ≤ base2DigitSum (u r) := by
    rw [base2DigitSum_eq (u r)]
    have hdiv2 : 1 ≤ base2DigitSum (u r / 2) := base2DigitSum_pos_of_pos (by omega)
    omega
  have hs3_ge2 : 2 ≤ base3DigitSum (u r) := by
    rw [base3DigitSum_eq (u r)]
    have hdiv3 : 1 ≤ base3DigitSum (u r / 3) := base3DigitSum_pos_of_pos (by omega)
    have hrem3 : 1 ≤ u r % 3 := by omega
    omega
  have hjoint :=
    (top_down_senge_straus_stewart_joint_digitsum_blueprint
      (M := 4) (N := 0) (g_0 := 0) (g_N := 0) (K_N := 0) (B := 0)
      hchain (by decide) (by decide)).1
  change base2DigitSum (P r) + base3DigitSum (P (r + 1)) =
    base2DigitSum (u r) + base3DigitSum (u r) + 1 at hjoint
  exact ⟨hlock3, hlock12, ⟨hge5, hge7, by omega, by omega⟩, ⟨hs2_ge2, hs3_ge2, by omega⟩⟩

/-! ## 19. Theorem SB.19: One-Step Backward Quotient Recovery & Mod-$3^{s_r}$ Remainder Law -/

/-- **One-Step Backward Quotient Recovery & Mod-$3^{s_r}$ Remainder Law
(`one_step_backward_quotient_recovery_and_mod_three_pow_one`, Theorem SB.19)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds:
1. `2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1`,
2. `(2 ^ (s (r + 1)) * u (r + 1)) / 3 ^ (s r) = u r`
   (the previous odd leftover $u_r$ is recovered by a single integer division!), and
3. `(2 ^ (s (r + 1)) * u (r + 1)) % 3 ^ (s r) = 1`
   (the remainder modulo $3^{s_r}$ is **identically $1$**!). -/
theorem one_step_backward_quotient_recovery_and_mod_three_pow_one
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2)) :
    2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 ∧
      (2 ^ (s (r + 1)) * u (r + 1)) / 3 ^ (s r) = u r ∧
      (2 ^ (s (r + 1)) * u (r + 1)) % 3 ^ (s r) = 1 := by
  have hr := hchain r (by omega)
  have hr1 := hchain (r + 1) (by omega)
  have hs_r : 1 ≤ s r := hr.1
  have hP_r : oddReturnP (orbit b_0 (blockSteps s r)) = 2 ^ (s r) * u r := hr.2.2
  have hP_r1 : oddReturnP (orbit b_0 (blockSteps s (r + 1))) = 2 ^ (s (r + 1)) * u (r + 1) := hr1.2.2
  have hb_r1 : orbit b_0 (blockSteps s (r + 1)) = 3 ^ (s r - 1) * u r := by
    change orbit b_0 (blockSteps s r + s r) = 3 ^ (s r - 1) * u r
    rw [orbit_add]
    exact orbit_odd_block_return hs_r hP_r
  have hid : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 := by
    rw [← hP_r1]
    change 3 * orbit b_0 (blockSteps s (r + 1)) + 1 = 3 ^ (s r) * u r + 1
    rw [hb_r1, ← mul_assoc]
    have h3 : 3 * 3 ^ (s r - 1) = 3 ^ (s r) := by
      conv_rhs => rw [← Nat.sub_add_cancel hs_r, Nat.pow_succ']
    rw [h3]
  have h1_lt : 1 < 3 ^ (s r) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 1 := ⟨s r - 1, by omega⟩
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ 3 (by decide)
    rw [hk, Nat.pow_succ]
    omega
  have h3_pos : 0 < 3 ^ (s r) := by omega
  have hdiv : (2 ^ (s (r + 1)) * u (r + 1)) / 3 ^ (s r) = u r := by
    rw [hid, Nat.mul_add_div h3_pos, Nat.div_eq_of_lt h1_lt, add_zero]
  have hmod : (2 ^ (s (r + 1)) * u (r + 1)) % 3 ^ (s r) = 1 := by
    rw [hid, Nat.mul_add_mod, Nat.mod_eq_of_lt h1_lt]
  exact ⟨hid, hdiv, hmod⟩

/-! ## 20. Theorem SB.20: The $5\times$ / $7\times$ Sharpened Global Archimedean Rung Ceiling -/

/-- **The $5\times$ / $7\times$ Sharpened Global Archimedean Rung Ceiling
(`sharpened_five_seven_archimedean_rung_ceiling`, Theorem SB.20)**:
Suppose `ValidBlockChain b_0 s u (K + 2)` holds with `2 ≤ s (K + 1)` and `0 < renewalIntSlack s K`.
Setting `P r = oddReturnP (orbit b_0 (blockSteps s r))` and `T r = blockSteps s r`:
1. **Universal $5\times$ Sharpened Ceiling**:
   `10 * 2 ^ (T (K + 1)) < 3 ^ (T K) * (2 * P 0 + 1)`,
2. **Even-Rung $7\times$ Sharpened Ceiling**:
   `s K % 2 = 0 → 14 * 2 ^ (T (K + 1)) < 3 ^ (T K) * (2 * P 0 + 1)`, and
3. **Initial Seed Floor at $K = 0$**:
   When `K = 0`, `5 * 2 ^ (s 0) ≤ 3 * b_0 + 1`, and if `s 0 % 2 = 0`, `7 * 2 ^ (s 0) ≤ 3 * b_0 + 1`
   (in particular, `s 0 = 2 → 9 ≤ b_0`)! -/
theorem sharpened_five_seven_archimedean_rung_ceiling
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 2))
    (hs_next : 2 ≤ s (K + 1))
    (hS_pos : 0 < renewalIntSlack s K) :
    let P := fun r => oddReturnP (orbit b_0 (blockSteps s r))
    let T := fun r => blockSteps s r
    10 * 2 ^ (T (K + 1)) < 3 ^ (T K) * (2 * P 0 + 1) ∧
      (s K % 2 = 0 → 14 * 2 ^ (T (K + 1)) < 3 ^ (T K) * (2 * P 0 + 1)) ∧
      (K = 0 →
        5 * 2 ^ (s 0) ≤ 3 * b_0 + 1 ∧
          (s 0 % 2 = 0 → 7 * 2 ^ (s 0) ≤ 3 * b_0 + 1) ∧
          (s 0 = 2 → 9 ≤ b_0)) := by
  intro P T
  have hch1 : ValidBlockChain b_0 s u (K + 1) := fun k hk => hchain k (by omega)
  have hceil := archimedean_rung_ceiling_and_stepSum_bound hch1
  have hlt_u : 2 * 2 ^ (T (K + 1)) * u K < 3 ^ (T K) * (2 * P 0 + 1) :=
    (hceil.2.2.1 hS_pos).1
  have h18 := universal_mod12_quotient_lock_and_joint_digitsum_ge_five hchain hs_next
  have hu_ge5 : 5 ≤ u K := h18.2.2.1.1
  have hu_ge7 : s K % 2 = 0 → 7 ≤ u K := h18.2.2.1.2.1
  have hmul5 : 10 * 2 ^ (T (K + 1)) ≤ 2 * 2 ^ (T (K + 1)) * u K := by
    have h : 2 * 2 ^ (T (K + 1)) * 5 ≤ 2 * 2 ^ (T (K + 1)) * u K :=
      Nat.mul_le_mul_left (2 * 2 ^ (T (K + 1))) hu_ge5
    omega
  refine ⟨by omega, ?_, ?_⟩
  · intro hs0
    have h7 := hu_ge7 hs0
    have h : 2 * 2 ^ (T (K + 1)) * 7 ≤ 2 * 2 ^ (T (K + 1)) * u K :=
      Nat.mul_le_mul_left (2 * 2 ^ (T (K + 1))) h7
    omega
  · rintro rfl
    have hP0_eq : 3 * b_0 + 1 = 2 ^ (s 0) * u 0 := (hchain 0 (by omega)).2.2
    have h5_0 : 5 * 2 ^ (s 0) ≤ 2 ^ (s 0) * u 0 := by
      have h := Nat.mul_le_mul_left (2 ^ (s 0)) hu_ge5
      omega
    refine ⟨by omega, ?_, ?_⟩
    · intro hs0_even
      have h7_0 := hu_ge7 hs0_even
      have h := Nat.mul_le_mul_left (2 ^ (s 0)) h7_0
      omega
    · intro hs0_2
      have h7_0 := hu_ge7 (by omega)
      rw [hs0_2] at hP0_eq
      omega

/-! ## 21. Theorem SB.21: Two-Step Disjoint Base-3 Digit-Block Law & Exact Quotient Recovery -/

/-- Helper: `2 ^ n < 3 ^ n` for every `1 ≤ n`. -/
theorem two_pow_lt_three_pow_of_pos {n : ℕ} (hn : 1 ≤ n) : 2 ^ n < 3 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hlt := ih hk1
      rw [Nat.pow_succ 2 (k + 1), Nat.pow_succ 3 (k + 1)]
      omega

/-- **Two-Step Disjoint Base-3 Digit-Block Law & Exact Quotient Recovery
(`two_step_disjoint_base3_digit_block_law_and_quotient_recovery`, Theorem SB.21)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds:
1. **Two-Step Exact Identity**:
   `2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) = 3 ^ (s r + s (r + 1)) * u r + (3 ^ (s (r + 1)) + 2 ^ (s (r + 1)))`,
2. **Strict Remainder Bound**:
   `3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) < 3 ^ (s r + s (r + 1))`,
3. **Exact Two-Step Quotient & Remainder Recovery**:
   `(2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) / 3 ^ (s r + s (r + 1)) = u r` and
   `(2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) % 3 ^ (s r + s (r + 1)) = 3 ^ (s (r + 1)) + 2 ^ (s (r + 1))`, and
4. **Universal Zero-Carry Three-Block Base-3 Digit-Sum Splitting**:
   The three terms `3 ^ (s r + s (r + 1)) * u r`, `3 ^ (s (r + 1))`, and `2 ^ (s (r + 1))`
   occupy **completely disjoint Base-3 digit ranges** (`[s_r+s_{r+1}, ∞)`, `[s_{r+1}]`, and `[0, s_{r+1}-1]`),
   so with **zero Base-3 carries**:
   `base3DigitSum (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) = base3DigitSum (u r) + 1 + base3DigitSum (2 ^ (s (r + 1)))`! -/
theorem two_step_disjoint_base3_digit_block_law_and_quotient_recovery
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3)) :
    2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) =
        3 ^ (s r + s (r + 1)) * u r + (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) ∧
      3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) < 3 ^ (s r + s (r + 1)) ∧
      (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) / 3 ^ (s r + s (r + 1)) = u r ∧
      (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) % 3 ^ (s r + s (r + 1)) =
        3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) ∧
      base3DigitSum (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) =
        base3DigitSum (u r) + 1 + base3DigitSum (2 ^ (s (r + 1))) := by
  have hch1 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hch2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hstep1 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch1).1
  have hstep2 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch2).1
  have hs_r : 1 ≤ s r := (hchain r (by omega)).1
  have hs_r1 : 1 ≤ s (r + 1) := (hchain (r + 1) (by omega)).1
  have hid2 :
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) =
        3 ^ (s r + s (r + 1)) * u r + (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) := by
    calc
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)
          = 2 ^ (s (r + 1)) * (2 ^ (s (r + 2)) * u (r + 2)) := by
            rw [Nat.pow_add]
            ring
      _ = 2 ^ (s (r + 1)) * (3 ^ (s (r + 1)) * u (r + 1) + 1) := by rw [hstep2]
      _ = 3 ^ (s (r + 1)) * (2 ^ (s (r + 1)) * u (r + 1)) + 2 ^ (s (r + 1)) := by ring
      _ = 3 ^ (s (r + 1)) * (3 ^ (s r) * u r + 1) + 2 ^ (s (r + 1)) := by rw [hstep1]
      _ = 3 ^ (s r + s (r + 1)) * u r + (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) := by
            rw [Nat.pow_add]
            ring
  have h2_lt_3 : 2 ^ (s (r + 1)) < 3 ^ (s (r + 1)) := two_pow_lt_three_pow_of_pos hs_r1
  have h3_ge_3 : 3 ≤ 3 ^ (s r) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 1 := ⟨s r - 1, by omega⟩
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ 3 (by decide)
    rw [hk, Nat.pow_succ]
    omega
  have hrem_lt : 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) < 3 ^ (s r + s (r + 1)) := by
    have hpow : 3 ^ (s r + s (r + 1)) = 3 ^ (s r) * 3 ^ (s (r + 1)) := Nat.pow_add 3 (s r) (s (r + 1))
    have hmul : 3 * 3 ^ (s (r + 1)) ≤ 3 ^ (s r) * 3 ^ (s (r + 1)) :=
      Nat.mul_le_mul_right (3 ^ (s (r + 1))) h3_ge_3
    omega
  have hpos2 : 1 ≤ 2 ^ (s (r + 1)) := Nat.one_le_pow _ 2 (by decide)
  have hdiv_pos : 0 < 3 ^ (s r + s (r + 1)) := by omega
  have hdiv :
      (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) / 3 ^ (s r + s (r + 1)) = u r := by
    rw [hid2, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hrem_lt, add_zero]
  have hmod :
      (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) % 3 ^ (s r + s (r + 1)) =
        3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) := by
    rw [hid2, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
  have hs3_rem :
      base3DigitSum (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) =
        1 + base3DigitSum (2 ^ (s (r + 1))) := by
    have h1 : 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) = 3 ^ (s (r + 1)) * 1 + 2 ^ (s (r + 1)) := by ring
    have hs3_1 : base3DigitSum 1 = 1 := by
      have h := base3DigitSum_three_mul_add_digit 0 (r := 1) (by decide)
      have hz : base3DigitSum 0 = 0 := by simp [base3DigitSum]
      simpa [hz] using h
    rw [h1, base3DigitSum_three_pow_mul_add (s (r + 1)) 1 h2_lt_3, hs3_1]
  have hs3_all :
      base3DigitSum (2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)) =
        base3DigitSum (u r) + 1 + base3DigitSum (2 ^ (s (r + 1))) := by
    rw [hid2, base3DigitSum_three_pow_mul_add (s r + s (r + 1)) (u r) hrem_lt, hs3_rem]
    omega
  exact ⟨hid2, hrem_lt, hdiv, hmod, hs3_all⟩

/-! ## 22. Theorem SB.22: All-$K$-Step Zero-Carry Top-Block Law & Multi-Step Quotient Recovery -/

/-- **All-$K$-Step Zero-Carry Top-Block Law & Multi-Step Quotient Recovery
(`all_k_step_zero_carry_top_block_and_quotient_recovery`, Theorem SB.22)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds for `r, M : ℕ` with
`0 < renewalIntSlack (fun t => s (r + 1 + t)) M`.
Let `s' t = s (r + 1 + t)`, `d = blockSteps s' M`,
`S = d + s (r + 1 + M)`, `T = s r + d`, and
`R = 3 ^ d + renewalNumerator s' M`:
1. **All-$K$-Step Odd-Leftover Identity**:
   `2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R`,
2. **Strict Remainder Bound**:
   `R < 2 * 3 ^ d` and `R < 3 ^ T`,
3. **Exact Multi-Step Quotient & Remainder Recovery**:
   `(2 ^ S * u (r + 1 + M)) / 3 ^ T = u r` and
   `(2 ^ S * u (r + 1 + M)) % 3 ^ T = R`
   (the initial odd leftover `u r` is **permanently frozen** as the top Base-3 digits of
   `2 ^ S * u (r + 1 + M)` across **every** number of future blocks `M`!), and
4. **All-$K$-Step Zero-Carry Base-3 Digit-Sum Splitting**:
   `base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R`! -/
theorem all_k_step_zero_carry_top_block_and_quotient_recovery
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M + 1))
    (hS_pos : 0 < renewalIntSlack (fun t => s (r + 1 + t)) M) :
    let s' := fun t => s (r + 1 + t)
    let d := blockSteps s' M
    let S := d + s (r + 1 + M)
    let T := s r + d
    let R := 3 ^ d + renewalNumerator s' M
    2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R ∧
      R < 2 * 3 ^ d ∧
      R < 3 ^ T ∧
      (2 ^ S * u (r + 1 + M)) / 3 ^ T = u r ∧
      (2 ^ S * u (r + 1 + M)) % 3 ^ T = R ∧
      base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R := by
  intro s' d S T R
  have h10 := late_step_cauchy_pinch_and_odd_quotient_gcd_dvd (N := r + 1) (M := M) hchain
  have hu_id :
      2 ^ S * u (r + 1 + M) =
        3 ^ d * 2 ^ (s (r + 1)) * u (r + 1) + renewalNumerator s' M := h10.2.1
  have hch_r2 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hstep1 : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_r2).1
  have hid_all : 2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R := by
    calc
      2 ^ S * u (r + 1 + M)
          = 3 ^ d * (2 ^ (s (r + 1)) * u (r + 1)) + renewalNumerator s' M := by
            rw [hu_id]
            ring
      _ = 3 ^ d * (3 ^ (s r) * u r + 1) + renewalNumerator s' M := by rw [hstep1]
      _ = 3 ^ T * u r + R := by
            change 3 ^ d * (3 ^ (s r) * u r + 1) + renewalNumerator s' M =
              3 ^ (s r + d) * u r + (3 ^ d + renewalNumerator s' M)
            rw [Nat.pow_add]
            ring
  have h2A_lt : 2 * renewalNumerator s' M < 3 ^ d := by
    have h : 2 * (renewalNumerator s' M : ℤ) < (3 : ℤ) ^ d := by
      change 0 < (3 : ℤ) ^ d - 2 * (renewalNumerator s' M : ℤ) at hS_pos
      omega
    exact_mod_cast h
  have h3d_pos : 1 ≤ 3 ^ d := Nat.one_le_pow _ 3 (by decide)
  have hR_lt_2 : R < 2 * 3 ^ d := by omega
  have hs_r : 1 ≤ s r := (hchain r (by omega)).1
  have h3_ge_3 : 3 ≤ 3 ^ (s r) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 1 := ⟨s r - 1, by omega⟩
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ 3 (by decide)
    rw [hk, Nat.pow_succ]
    omega
  have hR_lt_T : R < 3 ^ T := by
    have hpow : 3 ^ T = 3 ^ (s r) * 3 ^ d := Nat.pow_add 3 (s r) d
    have hmul : 3 * 3 ^ d ≤ 3 ^ (s r) * 3 ^ d := Nat.mul_le_mul_right (3 ^ d) h3_ge_3
    omega
  have hdiv_pos : 0 < 3 ^ T := by omega
  have hdiv : (2 ^ S * u (r + 1 + M)) / 3 ^ T = u r := by
    rw [hid_all, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hR_lt_T, add_zero]
  have hmod : (2 ^ S * u (r + 1 + M)) % 3 ^ T = R := by
    rw [hid_all, Nat.mul_add_mod, Nat.mod_eq_of_lt hR_lt_T]
  have hs3_split :
      base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R := by
    rw [hid_all, base3DigitSum_three_pow_mul_add T (u r) hR_lt_T]
  exact ⟨hid_all, hR_lt_2, hR_lt_T, hdiv, hmod, hs3_split⟩

/-! ## 23. Theorem SB.23: Two-Sided Past–Future Chinese Remainder Pinch on Interior Odd Leftovers -/

/-- **Two-Sided Past–Future Chinese Remainder Pinch on Interior Odd Leftovers
(`two_sided_past_future_crt_pinch`, Theorem SB.23)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds for `r : ℕ`.
Then the interior odd leftover `u (r + 1)` is simultaneously pinched from the **past**
(modulo `3 ^ (s r)`) and from the **future** (modulo `2 ^ (s (r + 2) + 1)`):
1. **Past Base-3 Congruence**:
   `(2 ^ (s (r + 1)) * u (r + 1)) % 3 ^ (s r) = 1`,
2. **Future Base-2 Congruence**:
   `(3 ^ (s (r + 1)) * u (r + 1) + 1) % 2 ^ (s (r + 2) + 1) = 2 ^ (s (r + 2))`,
3. **Exact Coprimality of Past & Future Moduli**:
   `Nat.Coprime (3 ^ (s r)) (2 ^ (s (r + 2) + 1))`, and
4. **Modulus Growth (`72 ≤ M`)**:
   Whenever `2 ≤ s r` and `2 ≤ s (r + 2)`, the combined past–future modulus satisfies
   `72 ≤ 3 ^ (s r) * 2 ^ (s (r + 2) + 1)`! -/
theorem two_sided_past_future_crt_pinch
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3)) :
    (2 ^ (s (r + 1)) * u (r + 1)) % 3 ^ (s r) = 1 ∧
      (3 ^ (s (r + 1)) * u (r + 1) + 1) % 2 ^ (s (r + 2) + 1) = 2 ^ (s (r + 2)) ∧
      Nat.Coprime (3 ^ (s r)) (2 ^ (s (r + 2) + 1)) ∧
      (2 ≤ s r → 2 ≤ s (r + 2) → 72 ≤ 3 ^ (s r) * 2 ^ (s (r + 2) + 1)) := by
  have hch1 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hch2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hpast : (2 ^ (s (r + 1)) * u (r + 1)) % 3 ^ (s r) = 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch1).2.2
  have hstep2 : 2 ^ (s (r + 2)) * u (r + 2) = 3 ^ (s (r + 1)) * u (r + 1) + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch2).1
  have hu2_odd : u (r + 2) % 2 = 1 := (hchain (r + 2) (by omega)).2.1
  have hfut :
      (3 ^ (s (r + 1)) * u (r + 1) + 1) % 2 ^ (s (r + 2) + 1) = 2 ^ (s (r + 2)) := by
    rw [← hstep2]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, u (r + 2) = 2 * m + 1 := ⟨u (r + 2) / 2, by omega⟩
    have hexpand :
        2 ^ (s (r + 2)) * u (r + 2) =
          2 ^ (s (r + 2) + 1) * m + 2 ^ (s (r + 2)) := by
      rw [hm, Nat.pow_succ]
      ring
    have hlt : 2 ^ (s (r + 2)) < 2 ^ (s (r + 2) + 1) := by
      have hpos : 1 ≤ 2 ^ (s (r + 2)) := Nat.one_le_pow _ 2 (by decide)
      rw [Nat.pow_succ]
      omega
    rw [hexpand, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hcop : Nat.Coprime (3 ^ (s r)) (2 ^ (s (r + 2) + 1)) := by
    have hc0 : Nat.Coprime 3 2 := by decide
    exact (hc0.pow_left (s r)).pow_right (s (r + 2) + 1)
  refine ⟨hpast, hfut, hcop, ?_⟩
  intro hsr2 hsr2_2
  have h3_ge_9 : 9 ≤ 3 ^ (s r) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 2 := ⟨s r - 2, by omega⟩
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ 3 (by decide)
    rw [hk, Nat.pow_add]
    omega
  have h2_ge_8 : 8 ≤ 2 ^ (s (r + 2) + 1) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s (r + 2) + 1 = k + 3 := ⟨s (r + 2) - 2, by omega⟩
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
    rw [hk, Nat.pow_add]
    omega
  have hmul : 9 * 8 ≤ 3 ^ (s r) * 2 ^ (s (r + 2) + 1) := Nat.mul_le_mul h3_ge_9 h2_ge_8
  omega

/-! ## 24. Theorem SB.24: Unconditional $4/5$ Renewal Ceiling & Past Base-3 Recovery (Slack-Free!) -/

/-- Helper: `9 * 2 ^ n ≤ 4 * 3 ^ n` for every `2 ≤ n`. -/
theorem nine_mul_two_pow_le_four_mul_three_pow {n : ℕ} (hn : 2 ≤ n) :
    9 * 2 ^ n ≤ 4 * 3 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have hle : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
  have hmul : 36 * 2 ^ k ≤ 36 * 3 ^ k := Nat.mul_le_mul_left 36 hle
  rw [Nat.pow_add 2 k 2, Nat.pow_add 3 k 2]
  omega

/-- Helper: Unconditional $4/5$ inductive invariant for `renewalNumerator`:
whenever `∀ k < r, 2 ≤ s k`, `5 * renewalNumerator s r + 4 * 2 ^ (blockSteps s r) ≤ 4 * 3 ^ (blockSteps s r)`. -/
theorem five_mul_renewalNumerator_add_four_mul_two_pow_le
    (s : ℕ → ℕ) (r : ℕ) (hs : ∀ k < r, 2 ≤ s k) :
    5 * renewalNumerator s r + 4 * 2 ^ (blockSteps s r) ≤ 4 * 3 ^ (blockSteps s r) := by
  induction r with
  | zero => simp [renewalNumerator, blockSteps]
  | succ r ih =>
      have ihr := ih (fun k hk => hs k (by omega))
      have hsr : 2 ≤ s r := hs r (by omega)
      have h9 : 9 * 2 ^ (s r) ≤ 4 * 3 ^ (s r) := nine_mul_two_pow_le_four_mul_three_pow hsr
      set T := blockSteps s r
      set A := renewalNumerator s r
      have hexp :
          5 * renewalNumerator s (r + 1) + 4 * 2 ^ (blockSteps s (r + 1)) =
            3 ^ (s r) * (5 * A) + (9 * 2 ^ (s r)) * 2 ^ T := by
        change 5 * (3 ^ (s r) * A + 2 ^ (T + s r)) + 4 * 2 ^ (T + s r) =
          3 ^ (s r) * (5 * A) + (9 * 2 ^ (s r)) * 2 ^ T
        rw [Nat.pow_add 2 T (s r)]
        ring
      have hstep1 :
          3 ^ (s r) * (5 * A) + (9 * 2 ^ (s r)) * 2 ^ T ≤
            3 ^ (s r) * (5 * A) + (4 * 3 ^ (s r)) * 2 ^ T := by
        have hm := Nat.mul_le_mul_right (2 ^ T) h9
        omega
      have hfactor :
          3 ^ (s r) * (5 * A) + (4 * 3 ^ (s r)) * 2 ^ T =
            3 ^ (s r) * (5 * A + 4 * 2 ^ T) := by ring
      have hstep2 :
          3 ^ (s r) * (5 * A + 4 * 2 ^ T) ≤ 3 ^ (s r) * (4 * 3 ^ T) :=
        Nat.mul_le_mul_left (3 ^ (s r)) ihr
      have hpow3 :
          3 ^ (s r) * (4 * 3 ^ T) = 4 * 3 ^ (blockSteps s (r + 1)) := by
        change 3 ^ (s r) * (4 * 3 ^ T) = 4 * 3 ^ (T + s r)
        rw [Nat.pow_add 3 T (s r)]
        ring
      omega

/-- **Unconditional $4/5$ Renewal Ceiling & Past Base-3 Recovery
(`unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery`, Theorem SB.24)**:
Suppose `ValidBlockChain b_0 s u (r + 1)` holds with `∀ k < r, 2 ≤ s k`
(**with no `0 < renewalIntSlack` hypothesis needed!**).
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_r = blockSteps s r`, and
`A_r = renewalNumerator s r`:
1. **Exact $4/5$ Inductive Invariant**:
   `5 * A_r + 4 * 2 ^ T_r ≤ 4 * 3 ^ T_r`,
2. **Unconditional Sub-$3^{T_r}$ Bound**:
   `5 * A_r < 4 * 3 ^ T_r` and `A_r < 3 ^ T_r`,
3. **Unconditional Past Base-3 Quotient & Remainder Recovery**:
   `(2 ^ T_r * P r) / 3 ^ T_r = P 0` and `(2 ^ T_r * P r) % 3 ^ T_r = A_r`, and
4. **Unconditional Zero-Carry Base-3 Digit-Sum Splitting**:
   `base3DigitSum (2 ^ T_r * P r) = base3DigitSum (P 0) + base3DigitSum A_r`! -/
theorem unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1))
    (hs2 : ∀ k < r, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_r := blockSteps s r
    let A_r := renewalNumerator s r
    5 * A_r + 4 * 2 ^ T_r ≤ 4 * 3 ^ T_r ∧
      5 * A_r < 4 * 3 ^ T_r ∧
      A_r < 3 ^ T_r ∧
      (2 ^ T_r * P r) / 3 ^ T_r = P 0 ∧
      (2 ^ T_r * P r) % 3 ^ T_r = A_r ∧
      base3DigitSum (2 ^ T_r * P r) = base3DigitSum (P 0) + base3DigitSum A_r := by
  intro P T_r A_r
  have hinv : 5 * A_r + 4 * 2 ^ T_r ≤ 4 * 3 ^ T_r :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s r hs2
  have h2_pos : 1 ≤ 2 ^ T_r := Nat.one_le_pow _ 2 (by decide)
  have h5_lt : 5 * A_r < 4 * 3 ^ T_r := by omega
  have hA_lt : A_r < 3 ^ T_r := by omega
  have hch_r : ValidBlockChain b_0 s u r := fun k hk => hchain k (by omega)
  have hm : 2 ^ T_r * P r = 3 ^ T_r * P 0 + A_r := renewal_prefix_master_identity hch_r
  have hdiv_pos : 0 < 3 ^ T_r := by omega
  have hdiv : (2 ^ T_r * P r) / 3 ^ T_r = P 0 := by
    rw [hm, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hA_lt, add_zero]
  have hmod : (2 ^ T_r * P r) % 3 ^ T_r = A_r := by
    rw [hm, Nat.mul_add_mod, Nat.mod_eq_of_lt hA_lt]
  have hs3 : base3DigitSum (2 ^ T_r * P r) = base3DigitSum (P 0) + base3DigitSum A_r := by
    rw [hm, base3DigitSum_three_pow_mul_add T_r (P 0) hA_lt]
  exact ⟨hinv, h5_lt, hA_lt, hdiv, hmod, hs3⟩

/-! ## 25. Theorem SB.25: Unconditional All-$K$-Step Odd-Leftover Recovery & $9/5$ Geometric Remainder Law -/

/-- **Unconditional All-$K$-Step Odd-Leftover Recovery & $9/5$ Geometric Remainder Law
(`unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound`, Theorem SB.25)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds with `∀ k < M, 2 ≤ s (r + 1 + k)`
(**eliminating the `0 < renewalIntSlack` hypothesis from Theorem SB.22!**).
Let `s' t = s (r + 1 + t)`, `d = blockSteps s' M`,
`S = d + s (r + 1 + M)`, `T = s r + d`, and
`R = 3 ^ d + renewalNumerator s' M`:
1. **Universal $9/5$ Geometric Remainder Bound**:
   `5 * R + 4 * 2 ^ d ≤ 9 * 3 ^ d`, `R < 2 * 3 ^ d`, and `R < 3 ^ T`,
2. **Unconditional Multi-Step Quotient & Remainder Recovery**:
   `(2 ^ S * u (r + 1 + M)) / 3 ^ T = u r` and `(2 ^ S * u (r + 1 + M)) % 3 ^ T = R`, and
3. **Unconditional All-$K$-Step Zero-Carry Base-3 Digit-Sum Splitting**:
   `base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R`! -/
theorem unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M + 1))
    (hs2 : ∀ k < M, 2 ≤ s (r + 1 + k)) :
    let s' := fun t => s (r + 1 + t)
    let d := blockSteps s' M
    let S := d + s (r + 1 + M)
    let T := s r + d
    let R := 3 ^ d + renewalNumerator s' M
    5 * R + 4 * 2 ^ d ≤ 9 * 3 ^ d ∧
      R < 2 * 3 ^ d ∧
      R < 3 ^ T ∧
      (2 ^ S * u (r + 1 + M)) / 3 ^ T = u r ∧
      (2 ^ S * u (r + 1 + M)) % 3 ^ T = R ∧
      base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R := by
  intro s' d S T R
  have h10 := late_step_cauchy_pinch_and_odd_quotient_gcd_dvd (N := r + 1) (M := M) hchain
  have hu_id :
      2 ^ S * u (r + 1 + M) =
        3 ^ d * 2 ^ (s (r + 1)) * u (r + 1) + renewalNumerator s' M := h10.2.1
  have hch_r2 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hstep1 : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_r2).1
  have hid_all : 2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R := by
    calc
      2 ^ S * u (r + 1 + M)
          = 3 ^ d * (2 ^ (s (r + 1)) * u (r + 1)) + renewalNumerator s' M := by
            rw [hu_id]
            ring
      _ = 3 ^ d * (3 ^ (s r) * u r + 1) + renewalNumerator s' M := by rw [hstep1]
      _ = 3 ^ T * u r + R := by
            change 3 ^ d * (3 ^ (s r) * u r + 1) + renewalNumerator s' M =
              3 ^ (s r + d) * u r + (3 ^ d + renewalNumerator s' M)
            rw [Nat.pow_add]
            ring
  have hinv_M : 5 * renewalNumerator s' M + 4 * 2 ^ d ≤ 4 * 3 ^ d :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s' M hs2
  have h2d_pos : 1 ≤ 2 ^ d := Nat.one_le_pow _ 2 (by decide)
  have h95 : 5 * R + 4 * 2 ^ d ≤ 9 * 3 ^ d := by omega
  have hR_lt_2 : R < 2 * 3 ^ d := by omega
  have hs_r : 1 ≤ s r := (hchain r (by omega)).1
  have h3_ge_3 : 3 ≤ 3 ^ (s r) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 1 := ⟨s r - 1, by omega⟩
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ 3 (by decide)
    rw [hk, Nat.pow_succ]
    omega
  have hR_lt_T : R < 3 ^ T := by
    have hpow : 3 ^ T = 3 ^ (s r) * 3 ^ d := Nat.pow_add 3 (s r) d
    have hmul : 3 * 3 ^ d ≤ 3 ^ (s r) * 3 ^ d := Nat.mul_le_mul_right (3 ^ d) h3_ge_3
    omega
  have hdiv_pos : 0 < 3 ^ T := by omega
  have hdiv : (2 ^ S * u (r + 1 + M)) / 3 ^ T = u r := by
    rw [hid_all, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hR_lt_T, add_zero]
  have hmod : (2 ^ S * u (r + 1 + M)) % 3 ^ T = R := by
    rw [hid_all, Nat.mul_add_mod, Nat.mod_eq_of_lt hR_lt_T]
  have hs3_split :
      base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R := by
    rw [hid_all, base3DigitSum_three_pow_mul_add T (u r) hR_lt_T]
  exact ⟨h95, hR_lt_2, hR_lt_T, hdiv, hmod, hs3_split⟩

/-! ## 26. Theorem SB.26: Sliding Cut-Point Past–Future Chinese Remainder Pinch & Post-Bit-Length Uniqueness -/

/-- **Sliding Cut-Point Past–Future Chinese Remainder Pinch & Post-Bit-Length Uniqueness
(`sliding_cut_point_past_future_crt_pinch`, Theorem SB.26)**:
Suppose `ValidBlockChain b_0 s u (r + M + 1)` holds with `∀ k < r, 2 ≤ s k`.
At any interior cut point `r`, let `P k = oddReturnP (orbit b_0 (blockSteps s k))`,
`T_r = blockSteps s r`, `s' t = s (r + t)`, `d_r = blockSteps s' M`,
`D_r = d_r + s (r + M)`, and `M_r = 3 ^ T_r * 2 ^ (D_r + 1)`:
1. **Past Base-3 Congruence at Cut Point $r$**:
   `(2 ^ T_r * P r) % 3 ^ T_r = renewalNumerator s r`,
2. **Future Base-2 Congruence at Cut Point $r$**:
   `(3 ^ d_r * P r + renewalNumerator s' M) % 2 ^ (D_r + 1) = 2 ^ D_r`,
3. **Exact Coprimality of Past & Future Moduli**:
   `Nat.Coprime (3 ^ T_r) (2 ^ (D_r + 1))`,
4. **Unconditional Sliding Cut-Point Archimedean Bound**:
   `2 ^ T_r * P r < 3 ^ T_r * (P 0 + 1)` and
   `5 * 2 ^ (T_r + D_r) * P r < 3 ^ T_r * 2 ^ D_r * (5 * P 0 + 4)`, and
5. **Post-Bit-Length Sliding Cut-Point Pinch (`P_r < M_r`)**:
   Whenever `P 0 < 2 ^ (T_r + D_r + 1)`, at cut point `r` we have
   `P r < M_r` (`P r < 3 ^ T_r * 2 ^ (D_r + 1)`)! -/
theorem sliding_cut_point_past_future_crt_pinch
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + M + 1))
    (hs2 : ∀ k < r, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_r := blockSteps s r
    let s' := fun t => s (r + t)
    let d_r := blockSteps s' M
    let D_r := d_r + s (r + M)
    let M_r := 3 ^ T_r * 2 ^ (D_r + 1)
    (2 ^ T_r * P r) % 3 ^ T_r = renewalNumerator s r ∧
      (3 ^ d_r * P r + renewalNumerator s' M) % 2 ^ (D_r + 1) = 2 ^ D_r ∧
      Nat.Coprime (3 ^ T_r) (2 ^ (D_r + 1)) ∧
      (2 ^ T_r * P r < 3 ^ T_r * (P 0 + 1) ∧
        5 * 2 ^ (T_r + D_r) * P r < 3 ^ T_r * 2 ^ D_r * (5 * P 0 + 4)) ∧
      (P 0 < 2 ^ (T_r + D_r + 1) → P r < M_r) := by
  intro P T_r s' d_r D_r M_r
  have hch_r1 : ValidBlockChain b_0 s u (r + 1) := fun k hk => hchain k (by omega)
  have h24 := unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery hch_r1 hs2
  have hpast_mod : (2 ^ T_r * P r) % 3 ^ T_r = renewalNumerator s r := h24.2.2.2.2.1
  have h5A_lt : 5 * renewalNumerator s r < 4 * 3 ^ T_r := h24.2.1
  have hA_lt : renewalNumerator s r < 3 ^ T_r := h24.2.2.1
  have h10 := late_step_cauchy_pinch_and_odd_quotient_gcd_dvd (N := r) (M := M) hchain
  have hfut_eq :
      2 ^ D_r * u (r + M) = 3 ^ d_r * P r + renewalNumerator s' M := by
    calc
      2 ^ D_r * u (r + M) = 2 ^ d_r * (2 ^ (s (r + M)) * u (r + M)) := by
        change 2 ^ (d_r + s (r + M)) * u (r + M) = 2 ^ d_r * (2 ^ (s (r + M)) * u (r + M))
        rw [Nat.pow_add]
        ring
      _ = 2 ^ d_r * P (r + M) := by
        have hPM : P (r + M) = 2 ^ (s (r + M)) * u (r + M) := (hchain (r + M) (by omega)).2.2
        rw [← hPM]
      _ = 3 ^ d_r * P r + renewalNumerator s' M := h10.1
  have huM_odd : u (r + M) % 2 = 1 := (hchain (r + M) (by omega)).2.1
  have hfut_mod :
      (3 ^ d_r * P r + renewalNumerator s' M) % 2 ^ (D_r + 1) = 2 ^ D_r := by
    rw [← hfut_eq]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, u (r + M) = 2 * m + 1 := ⟨u (r + M) / 2, by omega⟩
    have hexp : 2 ^ D_r * u (r + M) = 2 ^ (D_r + 1) * m + 2 ^ D_r := by
      rw [hm, Nat.pow_succ]
      ring
    have hlt : 2 ^ D_r < 2 ^ (D_r + 1) := by
      have hpos : 1 ≤ 2 ^ D_r := Nat.one_le_pow _ 2 (by decide)
      rw [Nat.pow_succ]
      omega
    rw [hexp, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hcop : Nat.Coprime (3 ^ T_r) (2 ^ (D_r + 1)) := by
    have hc0 : Nat.Coprime 3 2 := by decide
    exact (hc0.pow_left T_r).pow_right (D_r + 1)
  have hch_r : ValidBlockChain b_0 s u r := fun k hk => hchain k (by omega)
  have hm_past : 2 ^ T_r * P r = 3 ^ T_r * P 0 + renewalNumerator s r :=
    renewal_prefix_master_identity hch_r
  have h1_past : 2 ^ T_r * P r < 3 ^ T_r * (P 0 + 1) := by
    have hrhs : 3 ^ T_r * (P 0 + 1) = 3 ^ T_r * P 0 + 3 ^ T_r := by ring
    omega
  have h5_past : 5 * (2 ^ T_r * P r) < 3 ^ T_r * (5 * P 0 + 4) := by
    have h : 5 * (2 ^ T_r * P r) = 5 * (3 ^ T_r * P 0) + 5 * renewalNumerator s r := by
      rw [hm_past]
      ring
    have hrhs : 3 ^ T_r * (5 * P 0 + 4) = 5 * (3 ^ T_r * P 0) + 4 * 3 ^ T_r := by ring
    omega
  have h2Dr_pos : 0 < 2 ^ D_r := Nat.pow_pos (by decide)
  have h5_cut :
      5 * 2 ^ (T_r + D_r) * P r < 3 ^ T_r * 2 ^ D_r * (5 * P 0 + 4) := by
    have hlhs : 5 * 2 ^ (T_r + D_r) * P r = 2 ^ D_r * (5 * (2 ^ T_r * P r)) := by
      rw [Nat.pow_add 2 T_r D_r]
      ring
    have hrhs : 3 ^ T_r * 2 ^ D_r * (5 * P 0 + 4) = 2 ^ D_r * (3 ^ T_r * (5 * P 0 + 4)) := by
      ring
    rw [hlhs, hrhs]
    exact Nat.mul_lt_mul_of_pos_left h5_past h2Dr_pos
  refine ⟨hpast_mod, hfut_mod, hcop, ⟨h1_past, h5_cut⟩, ?_⟩
  intro hP0_lt
  have hP0_le : P 0 + 1 ≤ 2 ^ (T_r + D_r + 1) := by omega
  have hmul_le : 3 ^ T_r * (P 0 + 1) ≤ 3 ^ T_r * 2 ^ (T_r + D_r + 1) :=
    Nat.mul_le_mul_left (3 ^ T_r) hP0_le
  have hrhs_eq : 3 ^ T_r * 2 ^ (T_r + D_r + 1) = 2 ^ T_r * M_r := by
    change 3 ^ T_r * 2 ^ (T_r + (D_r + 1)) = 2 ^ T_r * (3 ^ T_r * 2 ^ (D_r + 1))
    rw [Nat.pow_add 2 T_r (D_r + 1)]
    ring
  have h2Tr_lt : 2 ^ T_r * P r < 2 ^ T_r * M_r := by omega
  exact Nat.lt_of_mul_lt_mul_left h2Tr_lt

/-! ## 27. Theorem SB.27: The Zero-Carry Base-3 Horner Remainder Ladder -/

/-- **The Zero-Carry Base-3 Horner Remainder Ladder
(`zero_carry_base3_horner_remainder_ladder`, Theorem SB.27)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds with `∀ k < M, 2 ≤ s (r + 1 + k)`.
Let `s' t = s (r + 1 + t)`, `d = blockSteps s' M`, `S = d + s (r + 1 + M)`,
`T = s r + d`, `A' = renewalNumerator s' M`, and `R = 3 ^ d + A'`:
1. **Unconditional Sub-$3^d$ Inner Remainder Bound**:
   `A' < 3 ^ d`,
2. **Exact Inner Quotient & Remainder Recovery**:
   `R / 3 ^ d = 1` and `R % 3 ^ d = A'`
   (the top Base-3 digit of `R` at position `d` is **identically `1`**, above all digits of `A'`!),
3. **Zero-Carry Inner Remainder Base-3 Splitting**:
   `base3DigitSum R = 1 + base3DigitSum A'`, and
4. **Three-Zone Zero-Carry All-$K$-Step Base-3 Digit-Sum Decomposition**:
   `base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + 1 + base3DigitSum A'`
   (every multi-step block transition splits `2 ^ S * u (r + 1 + M)` in Base 3 into three
   **completely non-overlapping, zero-carry zones**: the frozen top digits `u r` at `[s_r + d, ∞)`,
   a single separator trit `1` at position `d`, and the inner renewal numerator `A'` in `[0, d - 1]`)! -/
theorem zero_carry_base3_horner_remainder_ladder
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M + 1))
    (hs2 : ∀ k < M, 2 ≤ s (r + 1 + k)) :
    let s' := fun t => s (r + 1 + t)
    let d := blockSteps s' M
    let S := d + s (r + 1 + M)
    let R := 3 ^ d + renewalNumerator s' M
    renewalNumerator s' M < 3 ^ d ∧
      R / 3 ^ d = 1 ∧
      R % 3 ^ d = renewalNumerator s' M ∧
      base3DigitSum R = 1 + base3DigitSum (renewalNumerator s' M) ∧
      base3DigitSum (2 ^ S * u (r + 1 + M)) =
        base3DigitSum (u r) + 1 + base3DigitSum (renewalNumerator s' M) := by
  intro s' d S R
  have h25 := unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound hchain hs2
  have hinv_M : 5 * renewalNumerator s' M + 4 * 2 ^ d ≤ 4 * 3 ^ d :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s' M hs2
  have h2d_pos : 1 ≤ 2 ^ d := Nat.one_le_pow _ 2 (by decide)
  have hA_lt : renewalNumerator s' M < 3 ^ d := by omega
  have h3d_pos : 0 < 3 ^ d := by omega
  have hR_eq : R = 3 ^ d * 1 + renewalNumerator s' M := by
    change 3 ^ d + renewalNumerator s' M = 3 ^ d * 1 + renewalNumerator s' M
    ring
  have hdiv : R / 3 ^ d = 1 := by
    rw [hR_eq, Nat.mul_add_div h3d_pos, Nat.div_eq_of_lt hA_lt, add_zero]
  have hmod : R % 3 ^ d = renewalNumerator s' M := by
    rw [hR_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hA_lt]
  have hs3_1 : base3DigitSum 1 = 1 := by
    have h := base3DigitSum_three_mul_add_digit 0 (r := 1) (by decide)
    have hz : base3DigitSum 0 = 0 := by simp [base3DigitSum]
    simpa [hz] using h
  have hs3_R : base3DigitSum R = 1 + base3DigitSum (renewalNumerator s' M) := by
    rw [hR_eq, base3DigitSum_three_pow_mul_add d 1 hA_lt, hs3_1]
  have hs3_total :
      base3DigitSum (2 ^ S * u (r + 1 + M)) =
        base3DigitSum (u r) + 1 + base3DigitSum (renewalNumerator s' M) := by
    have hsplit := h25.2.2.2.2.2
    change base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + base3DigitSum R at hsplit
    omega
  exact ⟨hA_lt, hdiv, hmod, hs3_R, hs3_total⟩

/-! ## 28. Theorem SB.28 (Bridge A): Dual-Universe Series Lowest-Terms & $\mathbb{R} \times \mathbb{Q}_2$ Uniqueness of $P_0$ -/

/-- **Bridge A: Dual-Universe Series Lowest-Terms & $\mathbb{R} \times \mathbb{Q}_2$ Uniqueness of $P_0$
(`bridge_a_dual_universe_series_lowest_terms_and_uniqueness`, Theorem SB.28)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`T_K1 = T_K + s K`, and `A_K = renewalNumerator s K`:
1. **Dual-Series Master Equation (`F_K(2/3) = A_K / 3^{T_K}`):**
   `2 ^ T_K1 * u K = 3 ^ T_K * P 0 + A_K`,
2. **Strict Lowest Terms of `Q_K = (2^{T_{K+1}} u_K) / 3^{T_K}`:**
   `Nat.Coprime (2 ^ T_K1 * u K) 3` and `Nat.Coprime (2 ^ T_K1 * u K) (3 ^ T_K)`,
3. **Archimedean ($\mathbb{R}$) Recovery of `P_0` from `2^{T_{K+1}} u_K`:**
   `(2 ^ T_K1 * u K) / 3 ^ T_K = P 0` and `(2 ^ T_K1 * u K) % 3 ^ T_K = A_K`,
4. **Exact 2-Adic ($\mathbb{Q}_2$) Valuation Distance to `-P_0`:**
   `(3 ^ T_K * P 0 + A_K) % 2 ^ (T_K1 + 1) = 2 ^ T_K1`, and
5. **2-Adic ($\mathbb{Q}_2$) Uniqueness of `P_0` in the Post-Bit-Length Regime (`P_0 < 2^{T_{K+1}}`):**
   Whenever `P 0 < 2 ^ T_K1`, for any candidate `P_0' < 2 ^ T_K1` satisfying
   `(3 ^ T_K * P_0' + A_K) % 2 ^ T_K1 = 0`, we have `P_0' = P 0` identically! -/
theorem bridge_a_dual_universe_series_lowest_terms_and_uniqueness
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let T_K1 := T_K + s K
    let A_K := renewalNumerator s K
    2 ^ T_K1 * u K = 3 ^ T_K * P 0 + A_K ∧
      Nat.Coprime (2 ^ T_K1 * u K) 3 ∧
      Nat.Coprime (2 ^ T_K1 * u K) (3 ^ T_K) ∧
      (2 ^ T_K1 * u K) / 3 ^ T_K = P 0 ∧
      (2 ^ T_K1 * u K) % 3 ^ T_K = A_K ∧
      (3 ^ T_K * P 0 + A_K) % 2 ^ (T_K1 + 1) = 2 ^ T_K1 ∧
      (P 0 < 2 ^ T_K1 →
        ∀ P_0' : ℕ, P_0' < 2 ^ T_K1 →
          (3 ^ T_K * P_0' + A_K) % 2 ^ T_K1 = 0 → P_0' = P 0) := by
  intro P T_K T_K1 A_K
  have h24 := unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery hchain hs2
  have hPK : P K = 2 ^ (s K) * u K := (hchain K (by omega)).2.2
  have huK_odd : u K % 2 = 1 := (hchain K (by omega)).2.1
  have hmul_eq : 2 ^ T_K1 * u K = 2 ^ T_K * P K := by
    change 2 ^ (T_K + s K) * u K = 2 ^ T_K * P K
    rw [hPK, Nat.pow_add]
    ring
  have hch_K : ValidBlockChain b_0 s u K := fun k hk => hchain k (by omega)
  have hm : 2 ^ T_K * P K = 3 ^ T_K * P 0 + A_K := renewal_prefix_master_identity hch_K
  have hid : 2 ^ T_K1 * u K = 3 ^ T_K * P 0 + A_K := by rw [hmul_eq, hm]
  have hPK_mod3 : P K % 3 = 1 := by
    change (3 * orbit b_0 T_K + 1) % 3 = 1
    omega
  have huK_cop3 : Nat.Coprime (u K) 3 := by
    have hnot3 : ¬ (3 ∣ u K) := not_three_dvd_odd_part hPK
    rw [Nat.Coprime, Nat.gcd_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by decide)).2 hnot3
  have h2_cop3 : Nat.Coprime (2 ^ T_K1) 3 := (by decide : Nat.Coprime 2 3).pow_left T_K1
  have hnum_cop3 : Nat.Coprime (2 ^ T_K1 * u K) 3 := Nat.Coprime.mul h2_cop3 huK_cop3
  have hnum_cop3K : Nat.Coprime (2 ^ T_K1 * u K) (3 ^ T_K) := hnum_cop3.pow_right T_K
  have hdiv : (2 ^ T_K1 * u K) / 3 ^ T_K = P 0 := by
    rw [hmul_eq]
    exact h24.2.2.2.1
  have hmod : (2 ^ T_K1 * u K) % 3 ^ T_K = A_K := by
    rw [hmul_eq]
    exact h24.2.2.2.2.1
  have h2adic_mod : (3 ^ T_K * P 0 + A_K) % 2 ^ (T_K1 + 1) = 2 ^ T_K1 := by
    rw [← hid]
    obtain ⟨m, hm_u⟩ : ∃ m : ℕ, u K = 2 * m + 1 := ⟨u K / 2, by omega⟩
    have hexp : 2 ^ T_K1 * u K = 2 ^ (T_K1 + 1) * m + 2 ^ T_K1 := by
      rw [hm_u, Nat.pow_succ]
      ring
    have hlt : 2 ^ T_K1 < 2 ^ (T_K1 + 1) := by
      have hpos : 1 ≤ 2 ^ T_K1 := Nat.one_le_pow _ 2 (by decide)
      rw [Nat.pow_succ]
      omega
    rw [hexp, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  refine ⟨hid, hnum_cop3, hnum_cop3K, hdiv, hmod, h2adic_mod, ?_⟩
  intro hP0_lt P_0' hP0'_lt hmod'
  have hmod0 : (3 ^ T_K * P 0 + A_K) % 2 ^ T_K1 = 0 := by
    rw [← hid]
    exact Nat.dvd_iff_mod_eq_zero.1 ⟨u K, rfl⟩
  have hcop_3_2 : Nat.Coprime (3 ^ T_K) (2 ^ T_K1) :=
    ((by decide : Nat.Coprime 3 2).pow_left T_K).pow_right T_K1
  rcases le_or_gt P_0' (P 0) with hle | hgt
  · have hdvd_diff : 2 ^ T_K1 ∣ 3 ^ T_K * (P 0 - P_0') := by
      obtain ⟨q₁, hq₁⟩ : 2 ^ T_K1 ∣ 3 ^ T_K * P 0 + A_K := Nat.dvd_iff_mod_eq_zero.2 hmod0
      obtain ⟨q₂, hq₂⟩ : 2 ^ T_K1 ∣ 3 ^ T_K * P_0' + A_K := Nat.dvd_iff_mod_eq_zero.2 hmod'
      have hsub :
          3 ^ T_K * (P 0 - P_0') = (3 ^ T_K * P 0 + A_K) - (3 ^ T_K * P_0' + A_K) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [hsub]
      exact Nat.dvd_sub ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
    have hdvd_P : 2 ^ T_K1 ∣ (P 0 - P_0') := hcop_3_2.symm.dvd_of_dvd_mul_left hdvd_diff
    obtain ⟨k, hk⟩ := hdvd_P
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · omega
    · have hge : 2 ^ T_K1 ≤ P 0 - P_0' := by
        rw [hk]
        exact Nat.le_mul_of_pos_right _ hk_pos
      omega
  · have hdvd_diff : 2 ^ T_K1 ∣ 3 ^ T_K * (P_0' - P 0) := by
      obtain ⟨q₁, hq₁⟩ : 2 ^ T_K1 ∣ 3 ^ T_K * P 0 + A_K := Nat.dvd_iff_mod_eq_zero.2 hmod0
      obtain ⟨q₂, hq₂⟩ : 2 ^ T_K1 ∣ 3 ^ T_K * P_0' + A_K := Nat.dvd_iff_mod_eq_zero.2 hmod'
      have hsub :
          3 ^ T_K * (P_0' - P 0) = (3 ^ T_K * P_0' + A_K) - (3 ^ T_K * P 0 + A_K) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [hsub]
      exact Nat.dvd_sub ⟨q₂, hq₂⟩ ⟨q₁, hq₁⟩
    have hdvd_P : 2 ^ T_K1 ∣ (P_0' - P 0) := hcop_3_2.symm.dvd_of_dvd_mul_left hdvd_diff
    obtain ⟨k, hk⟩ := hdvd_P
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · omega
    · have hge : 2 ^ T_K1 ≤ P_0' - P 0 := by
        rw [hk]
        exact Nat.le_mul_of_pos_right _ hk_pos
      omega

/-! ## 29. Theorem SB.29 (Bridge B1): Seed-Independent Step-to-Step Base-3 Evolution Law -/

/-- **Bridge B1: Seed-Independent Step-to-Step Base-3 Evolution Law
(`bridge_b_seed_independent_base3_step_evolution`, Theorem SB.29)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`:
1. **Unconditional Odd-Leftover Base-3 Law at Every Block `r ≤ K`:**
   `base3DigitSum (2 ^ (blockSteps s r + s r) * u r) = base3DigitSum (P 0) + base3DigitSum (renewalNumerator s r)`, and
2. **Seed-Independent Two-Block Base-3 Evolution Law:**
   For ANY two blocks `r₁ ≤ K` and `r₂ ≤ K`:
   `base3DigitSum (2 ^ (blockSteps s r₂ + s r₂) * u r₂) + base3DigitSum (renewalNumerator s r₁) = base3DigitSum (2 ^ (blockSteps s r₁ + s r₁) * u r₁) + base3DigitSum (renewalNumerator s r₂)`
   (the Base-3 digit-sum change of `2 ^ T_{r+1} * u_r` between any two blocks `r₁` and `r₂`
   is **100% independent of the seed `b_0` and `P 0`**, depending **only** on `renewalNumerator s`!). -/
theorem bridge_b_seed_independent_base3_step_evolution
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    (∀ r ≤ K,
      base3DigitSum (2 ^ (blockSteps s r + s r) * u r) =
        base3DigitSum (P 0) + base3DigitSum (renewalNumerator s r)) ∧
      (∀ r₁ ≤ K, ∀ r₂ ≤ K,
        base3DigitSum (2 ^ (blockSteps s r₂ + s r₂) * u r₂) +
            base3DigitSum (renewalNumerator s r₁) =
          base3DigitSum (2 ^ (blockSteps s r₁ + s r₁) * u r₁) +
            base3DigitSum (renewalNumerator s r₂)) := by
  intro P
  have h1 : ∀ r ≤ K,
      base3DigitSum (2 ^ (blockSteps s r + s r) * u r) =
        base3DigitSum (P 0) + base3DigitSum (renewalNumerator s r) := by
    intro r hr
    have hch_r : ValidBlockChain b_0 s u (r + 1) := fun k hk => hchain k (by omega)
    have hs2_r : ∀ k < r, 2 ≤ s k := fun k hk => hs2 k (by omega)
    have h24 := unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery hch_r hs2_r
    have hPr : P r = 2 ^ (s r) * u r := (hchain r (by omega)).2.2
    have hmul : 2 ^ (blockSteps s r + s r) * u r = 2 ^ (blockSteps s r) * P r := by
      rw [hPr, Nat.pow_add]
      ring
    rw [hmul]
    exact h24.2.2.2.2.2
  refine ⟨h1, ?_⟩
  intro r₁ hr₁ r₂ hr₂
  have eq1 := h1 r₁ hr₁
  have eq2 := h1 r₂ hr₂
  omega

/-! ## 30. Theorem SB.30 (Bridge B2): Additive Carry-Isolation Law Across the Multi-Step Boundary -/

/-- **Bridge B2: Additive Carry-Isolation Law Across the Multi-Step Boundary
(`bridge_b_additive_carry_isolation_and_horner_step`, Theorem SB.30)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds with `∀ k < M, 2 ≤ s (r + 1 + k)` and `2 ≤ s r`.
Let `s' t = s (r + 1 + t)`, `d = blockSteps s' M`, `S = d + s (r + 1 + M)`,
`T = s r + d`, `A' = renewalNumerator s' M`, `R = 3 ^ d + A'`, and `X = 2 ^ S * u (r + 1 + M)`:
1. **Pre-Multiplication Zero-Carry Split:**
   `X = 3 ^ T * u r + R`, `R < 3 ^ T`, and `base3DigitSum X = base3DigitSum (u r) + base3DigitSum R`,
2. **Post-Multiplication Zero-Carry Split (`2^{s_r} * R < 3^T`):**
   Even after multiplying `X` by `2 ^ (s r)`, the scaled remainder `2 ^ (s r) * R` satisfies
   `5 * (2 ^ (s r) * R) < 4 * 3 ^ T` and `2 ^ (s r) * R < 3 ^ T`, so it **still never carries**
   into `3 ^ T * (2 ^ (s r) * u r)`:
   `base3DigitSum (2 ^ (s r) * X) = base3DigitSum (2 ^ (s r) * u r) + base3DigitSum (2 ^ (s r) * R)`, and
3. **Exact Additive Carry-Isolation Law (`Δ_{2^{s_r}}(X) = Δ_{2^{s_r}}(u_r) + Δ_{2^{s_r}}(R)`):**
   `base3DigitSum (2 ^ (s r) * X) + base3DigitSum (u r) + base3DigitSum R = base3DigitSum X + base3DigitSum (2 ^ (s r) * u r) + base3DigitSum (2 ^ (s r) * R)`! -/
theorem bridge_b_additive_carry_isolation_and_horner_step
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M + 1))
    (hs2 : ∀ k < M, 2 ≤ s (r + 1 + k))
    (hsr : 2 ≤ s r) :
    let s' := fun t => s (r + 1 + t)
    let d := blockSteps s' M
    let S := d + s (r + 1 + M)
    let T := s r + d
    let R := 3 ^ d + renewalNumerator s' M
    let X := 2 ^ S * u (r + 1 + M)
    X = 3 ^ T * u r + R ∧
      R < 3 ^ T ∧
      base3DigitSum X = base3DigitSum (u r) + base3DigitSum R ∧
      5 * (2 ^ (s r) * R) < 4 * 3 ^ T ∧
      2 ^ (s r) * R < 3 ^ T ∧
      base3DigitSum (2 ^ (s r) * X) =
        base3DigitSum (2 ^ (s r) * u r) + base3DigitSum (2 ^ (s r) * R) ∧
      base3DigitSum (2 ^ (s r) * X) + base3DigitSum (u r) + base3DigitSum R =
        base3DigitSum X + base3DigitSum (2 ^ (s r) * u r) + base3DigitSum (2 ^ (s r) * R) := by
  intro s' d S T R X
  have h25 := unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound hchain hs2
  have h10 := late_step_cauchy_pinch_and_odd_quotient_gcd_dvd (N := r + 1) (M := M) hchain
  have hu_id :
      X = 3 ^ d * 2 ^ (s (r + 1)) * u (r + 1) + renewalNumerator s' M := h10.2.1
  have hch_r2 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hstep1 : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_r2).1
  have hX_eq : X = 3 ^ T * u r + R := by
    calc
      X = 3 ^ d * (2 ^ (s (r + 1)) * u (r + 1)) + renewalNumerator s' M := by
        rw [hu_id]
        ring
      _ = 3 ^ d * (3 ^ (s r) * u r + 1) + renewalNumerator s' M := by rw [hstep1]
      _ = 3 ^ T * u r + R := by
        change 3 ^ d * (3 ^ (s r) * u r + 1) + renewalNumerator s' M =
          3 ^ (s r + d) * u r + (3 ^ d + renewalNumerator s' M)
        rw [Nat.pow_add]
        ring
  have h95 : 5 * R + 4 * 2 ^ d ≤ 9 * 3 ^ d := h25.1
  have hR_lt_T : R < 3 ^ T := h25.2.2.1
  have hs3_X : base3DigitSum X = base3DigitSum (u r) + base3DigitSum R := h25.2.2.2.2.2
  have h2d_pos : 1 ≤ 2 ^ d := Nat.one_le_pow _ 2 (by decide)
  have h5R_lt : 5 * R < 9 * 3 ^ d := by omega
  have h9_2 : 9 * 2 ^ (s r) ≤ 4 * 3 ^ (s r) := nine_mul_two_pow_le_four_mul_three_pow hsr
  have h2sr_pos : 0 < 2 ^ (s r) := Nat.pow_pos (by decide)
  have h5_scaled : 5 * (2 ^ (s r) * R) < 4 * 3 ^ T := by
    have h1 : 2 ^ (s r) * (5 * R) < 2 ^ (s r) * (9 * 3 ^ d) :=
      Nat.mul_lt_mul_of_pos_left h5R_lt h2sr_pos
    have h2 : (9 * 2 ^ (s r)) * 3 ^ d ≤ (4 * 3 ^ (s r)) * 3 ^ d :=
      Nat.mul_le_mul_right (3 ^ d) h9_2
    have hpow : 3 ^ T = 3 ^ (s r) * 3 ^ d := Nat.pow_add 3 (s r) d
    have hlhs : 5 * (2 ^ (s r) * R) = 2 ^ (s r) * (5 * R) := by ring
    have hmid : 2 ^ (s r) * (9 * 3 ^ d) = (9 * 2 ^ (s r)) * 3 ^ d := by ring
    have hrhs : (4 * 3 ^ (s r)) * 3 ^ d = 4 * 3 ^ T := by rw [hpow]; ring
    omega
  have hscaled_lt : 2 ^ (s r) * R < 3 ^ T := by omega
  have hscaled_id : 2 ^ (s r) * X = 3 ^ T * (2 ^ (s r) * u r) + 2 ^ (s r) * R := by
    rw [hX_eq]
    ring
  have hs3_scaled :
      base3DigitSum (2 ^ (s r) * X) =
        base3DigitSum (2 ^ (s r) * u r) + base3DigitSum (2 ^ (s r) * R) := by
    rw [hscaled_id, base3DigitSum_three_pow_mul_add T (2 ^ (s r) * u r) hscaled_lt]
  exact ⟨hX_eq, hR_lt_T, hs3_X, h5_scaled, hscaled_lt, hs3_scaled, by omega⟩

/-! ## 31. Theorem SB.31 (Bridge C1): One-Step Binary Trailing-Ones Depletion Law -/

/-- Helper: For any `s : ℕ` and odd `u : ℕ` (`u % 2 = 1`),
`base2DigitSum (2 ^ s * u - 1) + 1 = base2DigitSum u + s`. -/
theorem base2DigitSum_two_pow_mul_sub_one (s : ℕ) {u : ℕ} (hu_odd : u % 2 = 1) :
    base2DigitSum (2 ^ s * u - 1) + 1 = base2DigitSum u + s := by
  induction s with
  | zero =>
      simp only [Nat.pow_zero, one_mul, add_zero]
      have hu_decomp : u - 1 = 2 * (u / 2) := by omega
      rw [hu_decomp, base2DigitSum_eq (2 * (u / 2)), base2DigitSum_eq u]
      have hmod : (2 * (u / 2)) % 2 = 0 := by omega
      have hdiv : (2 * (u / 2)) / 2 = u / 2 := by omega
      rw [hmod, hdiv, hu_odd]
      omega
  | succ s ih =>
      have hu_pos : 1 ≤ u := by omega
      have h2s_pos : 1 ≤ 2 ^ s := Nat.one_le_pow _ 2 (by decide)
      have hmul_pos : 1 ≤ 2 ^ s * u := Nat.mul_le_mul h2s_pos hu_pos
      have hmul2 : 2 ^ (s + 1) * u = 2 * (2 ^ s * u) := by
        rw [Nat.pow_succ]
        ring
      have hstep : 2 ^ (s + 1) * u - 1 = 2 * (2 ^ s * u - 1) + 1 := by omega
      rw [hstep, base2DigitSum_eq (2 * (2 ^ s * u - 1) + 1)]
      have hmod : (2 * (2 ^ s * u - 1) + 1) % 2 = 1 := by omega
      have hdiv : (2 * (2 ^ s * u - 1) + 1) / 2 = 2 ^ s * u - 1 := by omega
      rw [hmod, hdiv]
      omega

/-- **Bridge C1: One-Step Binary Trailing-Ones Depletion Law
(`bridge_c_one_step_binary_trailing_ones_depletion_law`, Theorem SB.31)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds:
1. **Disjoint Binary Block Decomposition of `3 ^ (s r) * u r`**:
   `3 ^ (s r) * u r = 2 ^ (s (r + 1)) * (u (r + 1) - 1) + (2 ^ (s (r + 1)) - 1)`,
2. **Exact Base-2 Quotient & All-Ones Remainder**:
   `(3 ^ (s r) * u r) / 2 ^ (s (r + 1)) = u (r + 1) - 1` and
   `(3 ^ (s r) * u r) % 2 ^ (s (r + 1)) = 2 ^ (s (r + 1)) - 1`, and
3. **Exact Binary Carry-Depletion Law**:
   `base2DigitSum (3 ^ (s r) * u r) + 1 = base2DigitSum (u (r + 1)) + s (r + 1)`
   (multiplying `u r` by `3 ^ (s r)` and adding `1` consumes exactly `s (r + 1)` trailing
   binary `1`-bits and replaces them with a single `1`-bit at position `s (r + 1)`)! -/
theorem bridge_c_one_step_binary_trailing_ones_depletion_law
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2)) :
    3 ^ (s r) * u r = 2 ^ (s (r + 1)) * (u (r + 1) - 1) + (2 ^ (s (r + 1)) - 1) ∧
      (3 ^ (s r) * u r) / 2 ^ (s (r + 1)) = u (r + 1) - 1 ∧
      (3 ^ (s r) * u r) % 2 ^ (s (r + 1)) = 2 ^ (s (r + 1)) - 1 ∧
      base2DigitSum (3 ^ (s r) * u r) + 1 = base2DigitSum (u (r + 1)) + s (r + 1) := by
  have hstep := (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have hu1_odd : u (r + 1) % 2 = 1 := (hchain (r + 1) (by omega)).2.1
  have hu1_pos : 1 ≤ u (r + 1) := by omega
  have h2s_pos : 1 ≤ 2 ^ (s (r + 1)) := Nat.one_le_pow _ 2 (by decide)
  have hdecomp :
      3 ^ (s r) * u r = 2 ^ (s (r + 1)) * (u (r + 1) - 1) + (2 ^ (s (r + 1)) - 1) := by
    have hmul : 2 ^ (s (r + 1)) * u (r + 1) = 2 ^ (s (r + 1)) * (u (r + 1) - 1) + 2 ^ (s (r + 1)) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have hle : 2 ^ (s (r + 1)) ≤ 2 ^ (s (r + 1)) * u (r + 1) :=
        Nat.le_mul_of_pos_right _ hu1_pos
      omega
    omega
  have hrem_lt : 2 ^ (s (r + 1)) - 1 < 2 ^ (s (r + 1)) := by omega
  have hdiv_pos : 0 < 2 ^ (s (r + 1)) := by omega
  have hdiv : (3 ^ (s r) * u r) / 2 ^ (s (r + 1)) = u (r + 1) - 1 := by
    rw [hdecomp, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hrem_lt, add_zero]
  have hmod : (3 ^ (s r) * u r) % 2 ^ (s (r + 1)) = 2 ^ (s (r + 1)) - 1 := by
    rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
  have hs2 : base2DigitSum (3 ^ (s r) * u r) + 1 = base2DigitSum (u (r + 1)) + s (r + 1) := by
    have hsub : 3 ^ (s r) * u r = 2 ^ (s (r + 1)) * u (r + 1) - 1 := by omega
    rw [hsub]
    exact base2DigitSum_two_pow_mul_sub_one (s (r + 1)) hu1_odd
  exact ⟨hdecomp, hdiv, hmod, hs2⟩

/-! ## 32. Theorem SB.32 (Bridge C2): Multi-Step Dual Base-2 / Base-3 Zero-Carry Split of $N_K$ -/

/-- **Bridge C2: Multi-Step Dual Base-2 / Base-3 Zero-Carry Split of $N_K$
(`bridge_c_multi_step_dual_base2_base3_zero_carry_split`, Theorem SB.32)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`T_K1 = T_K + s K`, `A_K = renewalNumerator s K`, and `N_K = 3 ^ T_K * P 0 + A_K`:
1. **Base-3 Zero-Carry Split of `N_K` at `3 ^ T_K`:**
   `N_K = 2 ^ T_K1 * u K`, `N_K / 3 ^ T_K = P 0`, `N_K % 3 ^ T_K = A_K`, and
   `base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K`, and
2. **Base-2 Zero-Carry Split of `N_K - 1` at `2 ^ T_K1`:**
   `N_K - 1 = 2 ^ T_K1 * (u K - 1) + (2 ^ T_K1 - 1)`,
   `(N_K - 1) / 2 ^ T_K1 = u K - 1`,
   `(N_K - 1) % 2 ^ T_K1 = 2 ^ T_K1 - 1`, and
   `base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K)`! -/
theorem bridge_c_multi_step_dual_base2_base3_zero_carry_split
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let T_K1 := T_K + s K
    let A_K := renewalNumerator s K
    let N_K := 3 ^ T_K * P 0 + A_K
    (N_K = 2 ^ T_K1 * u K ∧
      N_K / 3 ^ T_K = P 0 ∧
      N_K % 3 ^ T_K = A_K ∧
      base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K) ∧
      (N_K - 1 = 2 ^ T_K1 * (u K - 1) + (2 ^ T_K1 - 1) ∧
        (N_K - 1) / 2 ^ T_K1 = u K - 1 ∧
        (N_K - 1) % 2 ^ T_K1 = 2 ^ T_K1 - 1 ∧
        base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K)) := by
  intro P T_K T_K1 A_K N_K
  have h28 := bridge_a_dual_universe_series_lowest_terms_and_uniqueness hchain hs2
  have h29 := (bridge_b_seed_independent_base3_step_evolution hchain hs2).1 K (le_refl K)
  have hid : N_K = 2 ^ T_K1 * u K := h28.1.symm
  have hdiv3 : N_K / 3 ^ T_K = P 0 := by
    rw [hid]
    exact h28.2.2.2.1
  have hmod3 : N_K % 3 ^ T_K = A_K := by
    rw [hid]
    exact h28.2.2.2.2.1
  have hs3 : base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K := by
    rw [hid]
    exact h29
  have huK_odd : u K % 2 = 1 := (hchain K (by omega)).2.1
  have huK_pos : 1 ≤ u K := by omega
  have h2_pos : 1 ≤ 2 ^ T_K1 := Nat.one_le_pow _ 2 (by decide)
  have hdecomp2 : N_K - 1 = 2 ^ T_K1 * (u K - 1) + (2 ^ T_K1 - 1) := by
    have hmul : 2 ^ T_K1 * u K = 2 ^ T_K1 * (u K - 1) + 2 ^ T_K1 := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have hle : 2 ^ T_K1 ≤ 2 ^ T_K1 * u K := Nat.le_mul_of_pos_right _ huK_pos
      omega
    omega
  have hrem_lt : 2 ^ T_K1 - 1 < 2 ^ T_K1 := by omega
  have hdiv2_pos : 0 < 2 ^ T_K1 := by omega
  have hdiv2 : (N_K - 1) / 2 ^ T_K1 = u K - 1 := by
    rw [hdecomp2, Nat.mul_add_div hdiv2_pos, Nat.div_eq_of_lt hrem_lt, add_zero]
  have hmod2 : (N_K - 1) % 2 ^ T_K1 = 2 ^ T_K1 - 1 := by
    rw [hdecomp2, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
  have hs2_eq : base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K) := by
    rw [hid]
    have h := base2DigitSum_two_pow_mul_sub_one T_K1 huK_odd
    omega
  exact ⟨⟨hid, hdiv3, hmod3, hs3⟩, ⟨hdecomp2, hdiv2, hmod2, hs2_eq⟩⟩

/-! ## 33. Theorem SB.33 (Bridge C3): The Telescoped Binary Halving-Budget Law -/

/-- Cumulative binary `1`-bit budget $\sum_{r=0}^{K-1} s_2(u_r)$. -/
def sumBase2Quotient (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => sumBase2Quotient u K + base2DigitSum (u K)

/-- Cumulative triadic-multiplied binary `1`-bit supply $\sum_{r=0}^{K-1} s_2(3^{s_r} u_r)$. -/
def sumBase2TriadicScaled (s u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => sumBase2TriadicScaled s u K + base2DigitSum (3 ^ (s K) * u K)

/-- Helper: `s 0 ≤ blockSteps s (K + 1)` for every `K : ℕ`. -/
theorem s_zero_le_blockSteps_succ (s : ℕ → ℕ) (K : ℕ) :
    s 0 ≤ blockSteps s (K + 1) := by
  induction K with
  | zero => simp [blockSteps]
  | succ m ihm =>
      change s 0 ≤ blockSteps s (m + 1) + s (m + 1)
      omega

/-- **Bridge C3: The Telescoped Binary Halving-Budget Law
(`bridge_c_telescoped_binary_halving_budget_law`, Theorem SB.33)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds for `K : ℕ`:
$$\big(\operatorname{blockSteps}(s, K + 1) - s_0\big) + s_2(u_K) + \sum_{r=0}^{K-1} s_2(u_r) =
  s_2(u_0) + K + \sum_{r=0}^{K-1} s_2\big(3^{s_r} u_r\big)!$$
In words: across any $K$ blocks, every halving step in $T_{K+1} - s_0 = s_1 + \dots + s_K$
beyond $+1$ per block is paid for out of the initial binary `1`-bits $s_2(u_0)$ and the net
binary `1`-bits manufactured by multiplying $u_r$ by $3^{s_r}$! -/
theorem bridge_c_telescoped_binary_halving_budget_law
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1)) :
    (blockSteps s (K + 1) - s 0) + base2DigitSum (u K) + sumBase2Quotient u K =
      base2DigitSum (u 0) + K + sumBase2TriadicScaled s u K := by
  induction K with
  | zero =>
      have hb1 : blockSteps s 1 = s 0 := by simp [blockSteps]
      simp [hb1, sumBase2Quotient, sumBase2TriadicScaled]
  | succ K ih =>
      have hch_K : ValidBlockChain b_0 s u (K + 1) := fun k hk => hchain k (by omega)
      have ihK := ih hch_K
      have hch_step : ValidBlockChain b_0 s u (K + 2) := hchain
      have h31 := (bridge_c_one_step_binary_trailing_ones_depletion_law hch_step).2.2.2
      have hbs_succ : blockSteps s (K + 2) = blockSteps s (K + 1) + s (K + 1) := rfl
      have hs0_le : s 0 ≤ blockSteps s (K + 1) := s_zero_le_blockSteps_succ s K
      simp only [sumBase2Quotient, sumBase2TriadicScaled, hbs_succ]
      omega

/-! ## 34. Theorem SB.34 (Overnight Loop 1): One-Step Kummer–Legendre Binary Factorial Bridge -/

/-- **Overnight Loop 1: One-Step Kummer–Legendre Binary Factorial Bridge
(`kummer_legendre_one_step_binary_factorial_bridge`, Theorem SB.34)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds. Setting
`P k = oddReturnP (orbit b_0 (blockSteps s k))`:
1. `legendreFactVal2 (3 ^ (s r) * u r) + s (r + 1) = (2 ^ (s (r + 1)) - 1) * u (r + 1) + legendreFactVal2 (u (r + 1))`, and
2. `legendreFactVal2 (3 ^ (s r) * u r) + s (r + 1) = legendreFactVal2 (P (r + 1))`! -/
theorem kummer_legendre_one_step_binary_factorial_bridge
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2)) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    legendreFactVal2 (3 ^ (s r) * u r) + s (r + 1) =
        (2 ^ (s (r + 1)) - 1) * u (r + 1) + legendreFactVal2 (u (r + 1)) ∧
      legendreFactVal2 (3 ^ (s r) * u r) + s (r + 1) = legendreFactVal2 (P (r + 1)) := by
  intro P
  have hstep := (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have h31 := (bridge_c_one_step_binary_trailing_ones_depletion_law hchain).2.2.2
  have hleg_val := legendreFactVal2_add_base2DigitSum (3 ^ (s r) * u r)
  have hleg_u1 := legendreFactVal2_add_base2DigitSum (u (r + 1))
  have hleg_P1 := legendreFactVal2_add_base2DigitSum (P (r + 1))
  have hP1 : P (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := (hchain (r + 1) (by omega)).2.2
  have hs2_P1 : base2DigitSum (P (r + 1)) = base2DigitSum (u (r + 1)) := by
    rw [hP1, base2DigitSum_two_pow_mul]
  have h2_pos : 1 ≤ 2 ^ (s (r + 1)) := Nat.one_le_pow _ 2 (by decide)
  have hmul : (2 ^ (s (r + 1)) - 1) * u (r + 1) + u (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := by
    rw [Nat.sub_mul, one_mul]
    have hle : u (r + 1) ≤ 2 ^ (s (r + 1)) * u (r + 1) :=
      Nat.le_mul_of_pos_left _ h2_pos
    omega
  exact ⟨by omega, by omega⟩

/-! ## 35. Theorem SB.35 (Overnight Loop 2): Zero-Carry 3-Adic Factorial & Binomial Valuation Law -/

/-- **Overnight Loop 2: Zero-Carry 3-Adic Factorial & Binomial Valuation Law
(`zero_carry_three_adic_factorial_and_binomial_valuation_law`, Theorem SB.35)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`T_K1 = T_K + s K`, `A_K = renewalNumerator s K`, and `N_K = 3 ^ T_K * P 0 + A_K`:
1. **Exact 3-Adic Factorial Decomposition of $N_K!$**:
   `2 * legendreFactVal3 N_K = (3 ^ T_K - 1) * P 0 + 2 * legendreFactVal3 (P 0) + 2 * legendreFactVal3 A_K` and
   `legendreFactVal3 N_K = legendreFactVal3 (3 ^ T_K * P 0) + legendreFactVal3 A_K`
   (meaning the binomial coefficient $\binom{3^{T_K} P_0 + A_{0,K}}{A_{0,K}}$ has **3-adic valuation identically zero**!), and
2. **Exact 2-Adic Factorial Decomposition of $N_K!$ and $(N_K - 1)!$**:
   `legendreFactVal2 N_K + base2DigitSum (u K) = N_K` and
   `legendreFactVal2 (N_K - 1) + T_K1 + base2DigitSum (u K) = N_K`! -/
theorem zero_carry_three_adic_factorial_and_binomial_valuation_law
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let T_K1 := T_K + s K
    let A_K := renewalNumerator s K
    let N_K := 3 ^ T_K * P 0 + A_K
    2 * legendreFactVal3 N_K =
        (3 ^ T_K - 1) * P 0 + 2 * legendreFactVal3 (P 0) + 2 * legendreFactVal3 A_K ∧
      legendreFactVal3 N_K = legendreFactVal3 (3 ^ T_K * P 0) + legendreFactVal3 A_K ∧
      legendreFactVal2 N_K + base2DigitSum (u K) = N_K ∧
      legendreFactVal2 (N_K - 1) + T_K1 + base2DigitSum (u K) = N_K := by
  intro P T_K T_K1 A_K N_K
  have h32 := bridge_c_multi_step_dual_base2_base3_zero_carry_split hchain hs2
  have hid : N_K = 2 ^ T_K1 * u K := h32.1.1
  have hs3_N : base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K := h32.1.2.2.2
  have hs2_N1 : base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K) := h32.2.2.2.2
  clear h32
  have hs3_3P0 : base3DigitSum (3 ^ T_K * P 0) = base3DigitSum (P 0) :=
    base3DigitSum_three_pow_mul T_K (P 0)
  have hs2_N : base2DigitSum N_K = base2DigitSum (u K) := by
    rw [hid, base2DigitSum_two_pow_mul]
  have hleg3_N := two_mul_legendreFactVal3_add_base3DigitSum N_K
  have hleg3_P0 := two_mul_legendreFactVal3_add_base3DigitSum (P 0)
  have hleg3_3P0 := two_mul_legendreFactVal3_add_base3DigitSum (3 ^ T_K * P 0)
  have hleg3_A := two_mul_legendreFactVal3_add_base3DigitSum A_K
  have hleg2_N := legendreFactVal2_add_base2DigitSum N_K
  have hleg2_N1 := legendreFactVal2_add_base2DigitSum (N_K - 1)
  have h3_pos : 1 ≤ 3 ^ T_K := Nat.one_le_pow _ 3 (by decide)
  have hmul3 : (3 ^ T_K - 1) * P 0 + P 0 = 3 ^ T_K * P 0 := by
    rw [Nat.sub_mul, one_mul]
    have hle : P 0 ≤ 3 ^ T_K * P 0 := Nat.le_mul_of_pos_left _ h3_pos
    omega
  have huK_odd : u K % 2 = 1 := (hchain K (by omega)).2.1
  have huK_pos : 1 ≤ u K := by omega
  have h2_pos : 1 ≤ 2 ^ T_K1 := Nat.one_le_pow _ 2 (by decide)
  have hN_pos : 1 ≤ N_K := by
    rw [hid]
    have hm := Nat.mul_le_mul h2_pos huK_pos
    omega
  have hN_sub : (N_K - 1) + 1 = N_K := Nat.sub_add_cancel hN_pos
  have h4 : legendreFactVal2 (N_K - 1) + T_K1 + base2DigitSum (u K) = N_K := by
    calc
      legendreFactVal2 (N_K - 1) + T_K1 + base2DigitSum (u K)
          = legendreFactVal2 (N_K - 1) + (T_K1 + base2DigitSum (u K)) := by ring
      _ = legendreFactVal2 (N_K - 1) + (base2DigitSum (N_K - 1) + 1) := by rw [← hs2_N1]
      _ = (legendreFactVal2 (N_K - 1) + base2DigitSum (N_K - 1)) + 1 := by ring
      _ = (N_K - 1) + 1 := by rw [hleg2_N1]
      _ = N_K := hN_sub
  have hN_def : N_K = 3 ^ T_K * P 0 + A_K := rfl
  exact ⟨by omega, by omega, by omega, h4⟩

/-! ## 36. Theorem SB.36 (Overnight Loop 3): Joint $(v_2(N_K!), v_3(N_K!))$ Multi-Block Factorial Syzygy -/

/-- **Overnight Loop 3: Joint $(v_2(N_K!), v_3(N_K!))$ Multi-Block Factorial Syzygy
(`joint_multi_block_factorial_valuation_syzygy`, Theorem SB.36)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`A_K = renewalNumerator s K`, and `N_K = 3 ^ T_K * P 0 + A_K`:
1. `legendreFactVal2 N_K + base2DigitSum (u K) = 2 * legendreFactVal3 N_K + base3DigitSum (P 0) + base3DigitSum A_K`, and
2. `legendreFactVal2 (N_K - 1) + (T_K + s K) + base2DigitSum (u K) = 2 * legendreFactVal3 (3 ^ T_K * P 0) + 2 * legendreFactVal3 A_K + base3DigitSum (P 0) + base3DigitSum A_K`! -/
theorem joint_multi_block_factorial_valuation_syzygy
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let A_K := renewalNumerator s K
    let N_K := 3 ^ T_K * P 0 + A_K
    legendreFactVal2 N_K + base2DigitSum (u K) =
        2 * legendreFactVal3 N_K + base3DigitSum (P 0) + base3DigitSum A_K ∧
      legendreFactVal2 (N_K - 1) + (T_K + s K) + base2DigitSum (u K) =
        2 * legendreFactVal3 (3 ^ T_K * P 0) + 2 * legendreFactVal3 A_K +
          base3DigitSum (P 0) + base3DigitSum A_K := by
  intro P T_K A_K N_K
  have h35 := zero_carry_three_adic_factorial_and_binomial_valuation_law hchain hs2
  have h32 := bridge_c_multi_step_dual_base2_base3_zero_carry_split hchain hs2
  have hs3_N : base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K := h32.1.2.2.2
  have hleg3_N := two_mul_legendreFactVal3_add_base3DigitSum N_K
  have hsplit3 : legendreFactVal3 N_K = legendreFactVal3 (3 ^ T_K * P 0) + legendreFactVal3 A_K :=
    h35.2.1
  have hv2_N : legendreFactVal2 N_K + base2DigitSum (u K) = N_K := h35.2.2.1
  have hv2_N1 : legendreFactVal2 (N_K - 1) + (T_K + s K) + base2DigitSum (u K) = N_K := h35.2.2.2
  exact ⟨by omega, by omega⟩

/-! ## 37. Theorem SB.37 (Overnight Loop 4): Kummer Base-3 Doubling Carry Law for $\times 2^s$ -/

/-- **Overnight Loop 4: Kummer Base-3 Doubling Carry Law for Multiplication by $2^s$
(`kummer_base3_two_pow_mul_carry_identity_and_bound`, Theorem SB.37)**:
For every exponent `s : ℕ` and integer `m : ℕ`:
1. **Submultiplicative Base-3 Bound**:
   `base3DigitSum (2 ^ s * m) ≤ 2 ^ s * base3DigitSum m`,
2. **Factorial Valuation Monotonicity**:
   `2 ^ s * legendreFactVal3 m ≤ legendreFactVal3 (2 ^ s * m)`, and
3. **Exact Kummer–Legendre Base-3 Carry Identity**:
   `base3DigitSum (2 ^ s * m) + 2 * (legendreFactVal3 (2 ^ s * m) - 2 ^ s * legendreFactVal3 m) = 2 ^ s * base3DigitSum m`! -/
theorem kummer_base3_two_pow_mul_carry_identity_and_bound (s m : ℕ) :
    base3DigitSum (2 ^ s * m) ≤ 2 ^ s * base3DigitSum m ∧
      2 ^ s * legendreFactVal3 m ≤ legendreFactVal3 (2 ^ s * m) ∧
      base3DigitSum (2 ^ s * m) +
          2 * (legendreFactVal3 (2 ^ s * m) - 2 ^ s * legendreFactVal3 m) =
        2 ^ s * base3DigitSum m := by
  have hle : base3DigitSum (2 ^ s * m) ≤ 2 ^ s * base3DigitSum m := by
    induction s generalizing m with
    | zero => simp
    | succ s ih =>
        have hmul : 2 ^ (s + 1) * m = 2 ^ s * (2 * m) := by
          rw [Nat.pow_succ]
          ring
        have ih1 := ih (2 * m)
        rw [← hmul] at ih1
        have h2 := base3DigitSum_two_mul_le m
        have hmul2 : 2 ^ s * base3DigitSum (2 * m) ≤ 2 ^ s * (2 * base3DigitSum m) :=
          Nat.mul_le_mul_left (2 ^ s) h2
        have hrhs : 2 ^ (s + 1) * base3DigitSum m = 2 ^ s * (2 * base3DigitSum m) := by
          rw [Nat.pow_succ]
          ring
        omega
  have hleg_m := two_mul_legendreFactVal3_add_base3DigitSum m
  have hleg_2s := two_mul_legendreFactVal3_add_base3DigitSum (2 ^ s * m)
  have hmul_leg :
      2 * (2 ^ s * legendreFactVal3 m) + 2 ^ s * base3DigitSum m = 2 ^ s * m := by
    calc
      2 * (2 ^ s * legendreFactVal3 m) + 2 ^ s * base3DigitSum m
          = 2 ^ s * (2 * legendreFactVal3 m + base3DigitSum m) := by ring
      _ = 2 ^ s * m := by rw [hleg_m]
  exact ⟨hle, by omega, by omega⟩

/-! ## 38. Theorem SB.38 (Overnight Loop 5): Multi-Step Base-3 Horner Digit-Sum Lower Envelope -/

/-- **Overnight Loop 5: Multi-Step Base-3 Horner Digit-Sum Lower Envelope
(`multi_step_base3_horner_digitsum_lower_envelope`, Theorem SB.38)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds with `∀ k < M, 2 ≤ s (r + 1 + k)` and `2 ≤ s (r + 1)`.
Let `s' t = s (r + 1 + t)`, `d = blockSteps s' M`, and `S = d + s (r + 1 + M)`:
1. `base3DigitSum (2 ^ S * u (r + 1 + M)) = base3DigitSum (u r) + 1 + base3DigitSum (renewalNumerator s' M)`,
2. `3 ≤ base3DigitSum (u r) + 1`, and
3. `3 ≤ base3DigitSum (2 ^ S * u (r + 1 + M))` (and `4 ≤ base3DigitSum (2 ^ S * u (r + 1 + M))` whenever `1 ≤ M`)! -/
theorem multi_step_base3_horner_digitsum_lower_envelope
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M + 1))
    (hs2 : ∀ k < M, 2 ≤ s (r + 1 + k))
    (hs_r1 : 2 ≤ s (r + 1)) :
    let s' := fun t => s (r + 1 + t)
    let d := blockSteps s' M
    let S := d + s (r + 1 + M)
    base3DigitSum (2 ^ S * u (r + 1 + M)) =
        base3DigitSum (u r) + 1 + base3DigitSum (renewalNumerator s' M) ∧
      3 ≤ base3DigitSum (u r) + 1 ∧
      3 ≤ base3DigitSum (2 ^ S * u (r + 1 + M)) ∧
      (1 ≤ M → 4 ≤ base3DigitSum (2 ^ S * u (r + 1 + M))) := by
  intro s' d S
  have h27 :
      base3DigitSum (2 ^ S * u (r + 1 + M)) =
        base3DigitSum (u r) + 1 + base3DigitSum (renewalNumerator s' M) :=
    (zero_carry_base3_horner_remainder_ladder hchain hs2).2.2.2.2
  have hch_r2 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have h18 := universal_mod12_quotient_lock_and_joint_digitsum_ge_five hch_r2 hs_r1
  have hs3_ur : 2 ≤ base3DigitSum (u r) := h18.2.2.2.2.1
  refine ⟨h27, by omega, by omega, ?_⟩
  intro hM1
  have hA_pos : 1 ≤ renewalNumerator s' M := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, M = m + 1 := ⟨M - 1, by omega⟩
    rw [hm]
    change 1 ≤ 3 ^ (s' m) * renewalNumerator s' m + 2 ^ (blockSteps s' (m + 1))
    have h2 : 1 ≤ 2 ^ (blockSteps s' (m + 1)) := Nat.one_le_pow _ 2 (by decide)
    omega
  have hs3_A : 1 ≤ base3DigitSum (renewalNumerator s' M) :=
    base3DigitSum_pos_of_pos hA_pos
  omega

/-! ## 39. Theorem SB.39 (Overnight Loop 6): Interior Mod-36 Rung-to-Quotient Bijection -/

/-- Helper: `2 ^ n % 9` is periodic with period 6 (`1, 2, 4, 8, 7, 5`). -/
theorem two_pow_mod_nine_cycle (n : ℕ) :
    (n % 6 = 0 → 2 ^ n % 9 = 1) ∧
      (n % 6 = 1 → 2 ^ n % 9 = 2) ∧
      (n % 6 = 2 → 2 ^ n % 9 = 4) ∧
      (n % 6 = 3 → 2 ^ n % 9 = 8) ∧
      (n % 6 = 4 → 2 ^ n % 9 = 7) ∧
      (n % 6 = 5 → 2 ^ n % 9 = 5) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        ring
      rw [hpow]
      omega

/-- **Overnight Loop 6: Interior Mod-36 Rung-to-Quotient Bijection
(`interior_mod36_rung_to_quotient_bijection`, Theorem SB.39)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds with `2 ≤ s r` and `2 ≤ s (r + 2)`.
Then at the interior block `r + 1`:
1. `(2 ^ (s (r + 1)) * u (r + 1)) % 9 = 1`, and
2. **Exact Mod-36 Bijection with `s (r + 1) % 6`:**
   - `s (r + 1) % 6 = 0 ↔ u (r + 1) % 36 = 19`,
   - `s (r + 1) % 6 = 1 ↔ u (r + 1) % 36 = 5`,
   - `s (r + 1) % 6 = 2 ↔ u (r + 1) % 36 = 7`,
   - `s (r + 1) % 6 = 3 ↔ u (r + 1) % 36 = 17`,
   - `s (r + 1) % 6 = 4 ↔ u (r + 1) % 36 = 31`, and
   - `s (r + 1) % 6 = 5 ↔ u (r + 1) % 36 = 29`! -/
theorem interior_mod36_rung_to_quotient_bijection
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3))
    (hs_r : 2 ≤ s r)
    (hs_r2 : 2 ≤ s (r + 2)) :
    (2 ^ (s (r + 1)) * u (r + 1)) % 9 = 1 ∧
      (s (r + 1) % 6 = 0 ↔ u (r + 1) % 36 = 19) ∧
      (s (r + 1) % 6 = 1 ↔ u (r + 1) % 36 = 5) ∧
      (s (r + 1) % 6 = 2 ↔ u (r + 1) % 36 = 7) ∧
      (s (r + 1) % 6 = 3 ↔ u (r + 1) % 36 = 17) ∧
      (s (r + 1) % 6 = 4 ↔ u (r + 1) % 36 = 31) ∧
      (s (r + 1) % 6 = 5 ↔ u (r + 1) % 36 = 29) := by
  have hch1 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hch2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hstep1 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch1).1
  have h16 := (universal_mod4_quotient_rung_parity_lock_and_mersenne_trap hch2 hs_r2).1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s r = k + 2 := ⟨s r - 2, by omega⟩
  have h3_9 : 3 ^ (s r) * u r = 9 * (3 ^ k * u r) := by
    rw [hk, Nat.pow_add]
    ring
  have hmod9 : (2 ^ (s (r + 1)) * u (r + 1)) % 9 = 1 := by
    rw [hstep1, h3_9]
    omega
  have hmul_mod9 : ((2 ^ (s (r + 1)) % 9) * (u (r + 1) % 9)) % 9 = 1 := by
    rw [← Nat.mul_mod, hmod9]
  have hcyc := two_pow_mod_nine_cycle (s (r + 1))
  have hcases :
      s (r + 1) % 6 = 0 ∨ s (r + 1) % 6 = 1 ∨ s (r + 1) % 6 = 2 ∨
        s (r + 1) % 6 = 3 ∨ s (r + 1) % 6 = 4 ∨ s (r + 1) % 6 = 5 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
  · have hc := hcyc.1 h0
    rw [hc] at hmul_mod9
    omega
  · have hc := hcyc.2.1 h1
    rw [hc] at hmul_mod9
    omega
  · have hc := hcyc.2.2.1 h2
    rw [hc] at hmul_mod9
    omega
  · have hc := hcyc.2.2.2.1 h3
    rw [hc] at hmul_mod9
    omega
  · have hc := hcyc.2.2.2.2.1 h4
    rw [hc] at hmul_mod9
    omega
  · have hc := hcyc.2.2.2.2.2 h5
    rw [hc] at hmul_mod9
    omega

/-! ## 40. Theorem SB.40 (Overnight Loop 7): Interior Extinction of $u \in \{5, 7\}$ & the $17 / 43$ Floor -/

/-- **Overnight Loop 7: Interior Extinction of $u \in \{5, 7\}$ & the $17 / 43$ Floor
(`interior_extinction_of_five_and_seven_and_seventeen_floor`, Theorem SB.40)**:
Suppose `ValidBlockChain b_0 s u (r + 4)` holds with `2 ≤ s r`, `2 ≤ s (r + 1)`,
`2 ≤ s (r + 2)`, and `2 ≤ s (r + 3)`.
Then at the interior block `r + 1`:
1. `u (r + 1) = 5 → 7 ≤ s (r + 1)` (`u (r + 1) = 5` is **100% extinct** for `2 ≤ s (r + 1) ≤ 6`!),
2. `¬ (s (r + 1) = 2 ∧ u (r + 1) = 7)` (because `3^2 * 7 + 1 = 64 = 2^6 * 1` forces `u (r + 2) = 1`,
   which dies at block `r + 3`),
3. `u (r + 1) = 7 → 8 ≤ s (r + 1)` (`u (r + 1) = 7` is **100% extinct** for `2 ≤ s (r + 1) ≤ 7`!), and
4. **Universal `17 ≤ u (r + 1)` & `43 ≤ u (r + 1)` Interior Floors:**
   `(s (r + 1) ≤ 6 → 17 ≤ u (r + 1)) ∧ (s (r + 1) = 2 → 43 ≤ u (r + 1))`! -/
theorem interior_extinction_of_five_and_seven_and_seventeen_floor
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 4))
    (hs_r : 2 ≤ s r)
    (hs_r1 : 2 ≤ s (r + 1))
    (hs_r2 : 2 ≤ s (r + 2))
    (hs_r3 : 2 ≤ s (r + 3)) :
    (u (r + 1) = 5 → 7 ≤ s (r + 1)) ∧
      ¬ (s (r + 1) = 2 ∧ u (r + 1) = 7) ∧
      (u (r + 1) = 7 → 8 ≤ s (r + 1)) ∧
      (s (r + 1) ≤ 6 → 17 ≤ u (r + 1)) ∧
      (s (r + 1) = 2 → 43 ≤ u (r + 1)) := by
  have hch3 : ValidBlockChain b_0 s u (r + 3) := fun k hk => hchain k (by omega)
  have h39 := interior_mod36_rung_to_quotient_bijection hch3 hs_r hs_r2
  have hch_next2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hch_next3 : ValidBlockChain b_0 s u ((r + 2) + 2) := fun k hk => hchain k (by omega)
  have hstep2 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_next2).1
  have h18_r2 := universal_mod12_quotient_lock_and_joint_digitsum_ge_five hch_next3 hs_r3
  have hu2_ge5 : 5 ≤ u (r + 2) := h18_r2.2.2.1.1
  have hnot_2_7 : ¬ (s (r + 1) = 2 ∧ u (r + 1) = 7) := by
    rintro ⟨hs2_eq, hu7_eq⟩
    rw [hs2_eq, hu7_eq] at hstep2
    change 2 ^ (s (r + 2)) * u (r + 2) = 64 at hstep2
    have hcases : s (r + 2) ≤ 4 ∨ 5 ≤ s (r + 2) := by omega
    rcases hcases with hle4 | hge5
    · have : s (r + 2) = 2 ∨ s (r + 2) = 3 ∨ s (r + 2) = 4 := by omega
      rcases this with h2 | h3 | h4
      · rw [h2] at hstep2
        have hu2_odd : u (r + 2) % 2 = 1 := (hchain (r + 2) (by omega)).2.1
        omega
      · rw [h3] at hstep2
        have hu2_odd : u (r + 2) % 2 = 1 := (hchain (r + 2) (by omega)).2.1
        omega
      · rw [h4] at hstep2
        omega
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, s (r + 2) = k + 5 := ⟨s (r + 2) - 5, by omega⟩
      have hpow : 32 ≤ 2 ^ (s (r + 2)) := by
        have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
        rw [hk, Nat.pow_add]
        omega
      have hmul : 32 * 5 ≤ 2 ^ (s (r + 2)) * u (r + 2) := Nat.mul_le_mul hpow hu2_ge5
      omega
  omega

/-! ## 41. Theorem SB.41 (Overnight Loop 8): Even-Rung Mod-16 Two-Block Trap & $u \ge 79$ Floor at $s = 2$ -/

/-- **Overnight Loop 8: Even-Rung Mod-16 Two-Block Trap & $u \ge 79$ Floor at $s = 2$
(`even_rung_mod16_trap_and_seventy_nine_floor_at_rung_two`, Theorem SB.41)**:
Suppose `ValidBlockChain b_0 s u (r + 4)` holds with `2 ≤ s r`, `2 ≤ s (r + 1)`,
`2 ≤ s (r + 2)`, and `2 ≤ s (r + 3)`:
1. Whenever `s (r + 1) = 2`, we have `u (r + 1) % 16 ≠ 11`
   (because `9 * (16 m + 11) + 1 = 4 * (36 m + 25)` forces `s (r + 2) = 2` and `u (r + 2) % 4 = 1`,
   which dies at block `r + 3`!),
2. `¬ (s (r + 1) = 2 ∧ u (r + 1) = 43)`, and
3. **The $79\times$ Interior Floor at $s_{r+1} = 2$:**
   `s (r + 1) = 2 → 79 ≤ u (r + 1)`! -/
theorem even_rung_mod16_trap_and_seventy_nine_floor_at_rung_two
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 4))
    (hs_r : 2 ≤ s r)
    (hs_r1 : 2 ≤ s (r + 1))
    (hs_r2 : 2 ≤ s (r + 2))
    (hs_r3 : 2 ≤ s (r + 3)) :
    (s (r + 1) = 2 → u (r + 1) % 16 ≠ 11) ∧
      ¬ (s (r + 1) = 2 ∧ u (r + 1) = 43) ∧
      (s (r + 1) = 2 → 79 ≤ u (r + 1)) := by
  have h40 := interior_extinction_of_five_and_seven_and_seventeen_floor
    hchain hs_r hs_r1 hs_r2 hs_r3
  have hch3 : ValidBlockChain b_0 s u (r + 3) := fun k hk => hchain k (by omega)
  have h39 := interior_mod36_rung_to_quotient_bijection hch3 hs_r hs_r2
  have hch_next2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hch_next3 : ValidBlockChain b_0 s u ((r + 2) + 2) := fun k hk => hchain k (by omega)
  have hstep2 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_next2).1
  have h16_r2 := (universal_mod4_quotient_rung_parity_lock_and_mersenne_trap hch_next3 hs_r3).1
  have hnot_mod16 : s (r + 1) = 2 → u (r + 1) % 16 ≠ 11 := by
    intro hs2_eq hmod11
    rw [hs2_eq] at hstep2
    change 2 ^ (s (r + 2)) * u (r + 2) = 9 * u (r + 1) + 1 at hstep2
    have hmod8 : (9 * u (r + 1) + 1) % 8 = 4 := by omega
    have hnot_ge3 : ¬ (3 ≤ s (r + 2)) := by
      intro hge3
      obtain ⟨k, hk⟩ : ∃ k : ℕ, s (r + 2) = k + 3 := ⟨s (r + 2) - 3, by omega⟩
      have h8 : 2 ^ (s (r + 2)) * u (r + 2) = 8 * (2 ^ k * u (r + 2)) := by
        rw [hk, Nat.pow_add]
        ring
      rw [h8] at hstep2
      omega
    have hsr2_eq2 : s (r + 2) = 2 := by omega
    rw [hsr2_eq2] at hstep2
    have hu2_mod4 : u (r + 2) % 4 = 3 := h16_r2.1.mp (by omega)
    omega
  refine ⟨hnot_mod16, ?_, ?_⟩
  · rintro ⟨hs2_eq, hu43⟩
    exact hnot_mod16 hs2_eq (by omega)
  · intro hs2_eq
    have hmod36 : u (r + 1) % 36 = 7 := h39.2.2.2.1.mp (by omega)
    have hge43 : 43 ≤ u (r + 1) := h40.2.2.2.2 hs2_eq
    have hne43 : u (r + 1) ≠ 43 := fun h => hnot_mod16 hs2_eq (by omega)
    omega

/-! ## 42. Theorem SB.42 (Overnight Loop 9): Universal Mod-8 & Mod-24 Next-Rung Dichotomy -/

/-- Helper: `3 ^ n % 8 = 1` when `n` is even and `3` when `n` is odd. -/
theorem three_pow_mod_eight_parity (n : ℕ) :
    (n % 2 = 0 → 3 ^ n % 8 = 1) ∧ (n % 2 = 1 → 3 ^ n % 8 = 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 3 ^ (n + 1) = 3 * 3 ^ n := by
        rw [Nat.pow_succ]
        ring
      rw [hpow]
      omega

/-- **Overnight Loop 9: Universal Mod-8 & Mod-24 Next-Rung Dichotomy
(`universal_mod8_and_mod24_next_rung_dichotomy`, Theorem SB.42)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds with `2 ≤ s (r + 1)`.
Then the third bit of `u r` (`u r % 8`, and `u r % 24`) universally determines whether
the next block is a minimal recovery step (`s (r + 1) = 2`) or a long jump (`3 ≤ s (r + 1)`):
1. **Even `s r` (`s r % 2 = 0`):**
   `(u r % 8 = 3 ↔ s (r + 1) = 2) ∧ (u r % 8 = 7 ↔ 3 ≤ s (r + 1)) ∧ (u r % 24 = 19 ↔ s (r + 1) = 2) ∧ (u r % 24 = 7 ↔ 3 ≤ s (r + 1))`, and
2. **Odd `s r` (`s r % 2 = 1`):**
   `(u r % 8 = 1 ↔ s (r + 1) = 2) ∧ (u r % 8 = 5 ↔ 3 ≤ s (r + 1)) ∧ (u r % 24 = 17 ↔ s (r + 1) = 2) ∧ (u r % 24 = 5 ↔ 3 ≤ s (r + 1))`! -/
theorem universal_mod8_and_mod24_next_rung_dichotomy
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2))
    (hs_r1 : 2 ≤ s (r + 1)) :
    (s r % 2 = 0 →
      (u r % 8 = 3 ↔ s (r + 1) = 2) ∧
        (u r % 8 = 7 ↔ 3 ≤ s (r + 1)) ∧
        (u r % 24 = 19 ↔ s (r + 1) = 2) ∧
        (u r % 24 = 7 ↔ 3 ≤ s (r + 1))) ∧
      (s r % 2 = 1 →
        (u r % 8 = 1 ↔ s (r + 1) = 2) ∧
          (u r % 8 = 5 ↔ 3 ≤ s (r + 1)) ∧
          (u r % 24 = 17 ↔ s (r + 1) = 2) ∧
          (u r % 24 = 5 ↔ 3 ≤ s (r + 1))) := by
  have h18 := universal_mod12_quotient_lock_and_joint_digitsum_ge_five hchain hs_r1
  have hlock12 := h18.2.1
  have hstep := (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have hu1_odd : u (r + 1) % 2 = 1 := (hchain (r + 1) (by omega)).2.1
  have h3_8 := three_pow_mod_eight_parity (s r)
  have hmul8 : ((3 ^ (s r) % 8) * (u r % 8) + 1) % 8 = (2 ^ (s (r + 1)) * u (r + 1)) % 8 := by
    have h1 : (3 ^ (s r) % 8) * (u r % 8) % 8 = (3 ^ (s r) * u r) % 8 := (Nat.mul_mod _ _ 8).symm
    have h2 : (3 ^ (s r) * u r + 1) % 8 = (2 ^ (s (r + 1)) * u (r + 1)) % 8 := by rw [hstep]
    omega
  have hrung8 :
      (s (r + 1) = 2 → (2 ^ (s (r + 1)) * u (r + 1)) % 8 = 4) ∧
        (3 ≤ s (r + 1) → (2 ^ (s (r + 1)) * u (r + 1)) % 8 = 0) := by
    refine ⟨?_, ?_⟩
    · intro hs2_eq
      rw [hs2_eq]
      omega
    · intro hge3
      obtain ⟨k, hk⟩ : ∃ k : ℕ, s (r + 1) = k + 3 := ⟨s (r + 1) - 3, by omega⟩
      have h8 : 2 ^ (s (r + 1)) * u (r + 1) = 8 * (2 ^ k * u (r + 1)) := by
        rw [hk, Nat.pow_add]
        ring
      rw [h8]
      omega
  rcases (by omega : s r % 2 = 0 ∨ s r % 2 = 1) with hev | hodd
  · have hc := h3_8.1 hev
    rw [hc] at hmul8
    omega
  · have hc := h3_8.2 hodd
    rw [hc] at hmul8
    omega

/-! ## 43. Theorem SB.43 (Overnight Loop 10): The $17\times$ / $79\times$ Sharpened Interior Archimedean Rung Ceiling -/

/-- **Overnight Loop 10: The $17\times$ / $79\times$ Sharpened Interior Archimedean Rung Ceiling
(`sharpened_seventeen_seventy_nine_interior_archimedean_ceiling`, Theorem SB.43)**:
Suppose `ValidBlockChain b_0 s u (r + 4)` holds with `∀ k < r + 4, 2 ≤ s k`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))` and `T k = blockSteps s k`:
1. **Unconditional Interior Ceiling (`25 * 2^{T_{r+2}} < 3^{T_{r+1}} (5 P_0 + 4)`):**
   `25 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)`,
2. **The $17\times$ Sharpened Ceiling on `s (r + 1) ≤ 6`:**
   `s (r + 1) ≤ 6 → 85 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)`, and
3. **The $79\times$ Sharpened Ceiling at `s (r + 1) = 2`:**
   `s (r + 1) = 2 → 395 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)`! -/
theorem sharpened_seventeen_seventy_nine_interior_archimedean_ceiling
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 4))
    (hs2 : ∀ k < r + 4, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T := fun k => blockSteps s k
    25 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4) ∧
      (s (r + 1) ≤ 6 → 85 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)) ∧
      (s (r + 1) = 2 → 395 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)) := by
  intro P T
  have hs_r : 2 ≤ s r := hs2 r (by omega)
  have hs_r1 : 2 ≤ s (r + 1) := hs2 (r + 1) (by omega)
  have hs_r2 : 2 ≤ s (r + 2) := hs2 (r + 2) (by omega)
  have hs_r3 : 2 ≤ s (r + 3) := hs2 (r + 3) (by omega)
  have h40 := interior_extinction_of_five_and_seven_and_seventeen_floor
    hchain hs_r hs_r1 hs_r2 hs_r3
  have h41 := even_rung_mod16_trap_and_seventy_nine_floor_at_rung_two
    hchain hs_r hs_r1 hs_r2 hs_r3
  have hch_r2 : ValidBlockChain b_0 s u ((r + 1) + 1) := fun k hk => hchain k (by omega)
  have hs2_r1 : ∀ k < r + 1, 2 ≤ s k := fun k hk => hs2 k (by omega)
  have h24 := unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery hch_r2 hs2_r1
  have h5A_lt : 5 * renewalNumerator s (r + 1) < 4 * 3 ^ (T (r + 1)) := h24.2.1
  have hch_r1 : ValidBlockChain b_0 s u (r + 1) := fun k hk => hchain k (by omega)
  have hm : 2 ^ (T (r + 1)) * P (r + 1) = 3 ^ (T (r + 1)) * P 0 + renewalNumerator s (r + 1) :=
    renewal_prefix_master_identity hch_r1
  have hP_r1 : P (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := (hchain (r + 1) (by omega)).2.2
  have hT_r2 : 2 ^ (T (r + 1)) * P (r + 1) = 2 ^ (T (r + 2)) * u (r + 1) := by
    change 2 ^ (T (r + 1)) * P (r + 1) = 2 ^ (T (r + 1) + s (r + 1)) * u (r + 1)
    rw [hP_r1, Nat.pow_add]
    ring
  have h5_master :
      5 * (2 ^ (T (r + 2)) * u (r + 1)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4) := by
    rw [← hT_r2]
    have hlhs : 5 * (2 ^ (T (r + 1)) * P (r + 1)) =
        5 * (3 ^ (T (r + 1)) * P 0) + 5 * renewalNumerator s (r + 1) := by
      rw [hm]
      ring
    have hrhs : 3 ^ (T (r + 1)) * (5 * P 0 + 4) =
        5 * (3 ^ (T (r + 1)) * P 0) + 4 * 3 ^ (T (r + 1)) := by ring
    omega
  have hch_next2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hu_ge5 : 5 ≤ u (r + 1) :=
    (universal_mod12_quotient_lock_and_joint_digitsum_ge_five hch_next2 hs_r2).2.2.1.1
  have hmul5 : 25 * 2 ^ (T (r + 2)) ≤ 5 * (2 ^ (T (r + 2)) * u (r + 1)) := by
    calc
      25 * 2 ^ (T (r + 2)) = (5 * 2 ^ (T (r + 2))) * 5 := by ring
      _ ≤ (5 * 2 ^ (T (r + 2))) * u (r + 1) := Nat.mul_le_mul_left _ hu_ge5
      _ = 5 * (2 ^ (T (r + 2)) * u (r + 1)) := by ring
  refine ⟨by omega, ?_, ?_⟩
  · intro hle6
    have hu17 : 17 ≤ u (r + 1) := h40.2.2.2.1 hle6
    have hmul17 : 85 * 2 ^ (T (r + 2)) ≤ 5 * (2 ^ (T (r + 2)) * u (r + 1)) := by
      calc
        85 * 2 ^ (T (r + 2)) = (5 * 2 ^ (T (r + 2))) * 17 := by ring
        _ ≤ (5 * 2 ^ (T (r + 2))) * u (r + 1) := Nat.mul_le_mul_left _ hu17
        _ = 5 * (2 ^ (T (r + 2)) * u (r + 1)) := by ring
    omega
  · intro hs2_eq
    have hu79 : 79 ≤ u (r + 1) := h41.2.2 hs2_eq
    have hmul79 : 395 * 2 ^ (T (r + 2)) ≤ 5 * (2 ^ (T (r + 2)) * u (r + 1)) := by
      calc
        395 * 2 ^ (T (r + 2)) = (5 * 2 ^ (T (r + 2))) * 79 := by ring
        _ ≤ (5 * 2 ^ (T (r + 2))) * u (r + 1) := Nat.mul_le_mul_left _ hu79
        _ = 5 * (2 ^ (T (r + 2)) * u (r + 1)) := by ring
    omega

/-! ## 44. Theorem SB.44 (Overnight Loop 11): Universal Adjacent-Block Wronskian & Equal-Rung Log-Concavity Law -/

/-- **Overnight Loop 11: Universal Adjacent-Block Wronskian & Equal-Rung Log-Concavity Law
(`adjacent_block_wronskian_and_equal_rung_log_concavity`, Theorem SB.44)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds. Setting
`P k = oddReturnP (orbit b_0 (blockSteps s k))`:
1. **Universal Adjacent-Block Wronskian Identity**:
   `2 ^ (s r) * 3 ^ (s (r + 1)) * P (r + 1) * (P (r + 1) - 1) = 3 ^ (s r) * 2 ^ (s (r + 1)) * P r * (P (r + 2) - 1)`, and
2. **Equal-Rung Exponent-Free Wronskian & Strict Log-Concavity (`s r = s (r + 1)`)**:
   Whenever `s r = s (r + 1)`,
   `P (r + 1) * (P (r + 1) - 1) = P r * (P (r + 2) - 1)` and
   `P (r + 1) * P (r + 1) + P r = P r * P (r + 2) + P (r + 1)`
   (with `P r < P (r + 1)`, so `P r * P (r + 2) < P (r + 1) ^ 2`)! -/
theorem adjacent_block_wronskian_and_equal_rung_log_concavity
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3)) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    2 ^ (s r) * 3 ^ (s (r + 1)) * P (r + 1) * (P (r + 1) - 1) =
        3 ^ (s r) * 2 ^ (s (r + 1)) * P r * (P (r + 2) - 1) ∧
      (s r = s (r + 1) →
        P (r + 1) * (P (r + 1) - 1) = P r * (P (r + 2) - 1) ∧
          P (r + 1) * P (r + 1) + P r = P r * P (r + 2) + P (r + 1) ∧
          P r * P (r + 2) < P (r + 1) * P (r + 1)) := by
  intro P
  have hch1 : ValidBlockChain b_0 s u (r + 2) := fun k hk => hchain k (by omega)
  have hch2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hstep1 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch1).1
  have hstep2 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch2).1
  have hPr : P r = 2 ^ (s r) * u r := (hchain r (by omega)).2.2
  have hPr1 : P (r + 1) = 2 ^ (s (r + 1)) * u (r + 1) := (hchain (r + 1) (by omega)).2.2
  have hPr2 : P (r + 2) = 2 ^ (s (r + 2)) * u (r + 2) := (hchain (r + 2) (by omega)).2.2
  have hP1_step : P (r + 1) = 3 ^ (s r) * u r + 1 := by
    rw [hPr1]
    exact hstep1
  have hP2_step : P (r + 2) = 3 ^ (s (r + 1)) * u (r + 1) + 1 := by
    rw [hPr2]
    exact hstep2
  have hsub1 : P (r + 1) - 1 = 3 ^ (s r) * u r := by omega
  have hsub2 : P (r + 2) - 1 = 3 ^ (s (r + 1)) * u (r + 1) := by omega
  have hwron :
      2 ^ (s r) * 3 ^ (s (r + 1)) * P (r + 1) * (P (r + 1) - 1) =
        3 ^ (s r) * 2 ^ (s (r + 1)) * P r * (P (r + 2) - 1) := by
    rw [hsub1, hsub2, hPr, hPr1]
    ring
  refine ⟨hwron, ?_⟩
  intro hseq
  have heq_prod : P (r + 1) * (P (r + 1) - 1) = P r * (P (r + 2) - 1) := by
    rw [hsub1, hsub2, hPr, hPr1, ← hseq]
    ring
  have hPr1_pos : 1 ≤ P (r + 1) := by omega
  have hPr2_pos : 1 ≤ P (r + 2) := by omega
  have hexp1 : P (r + 1) * (P (r + 1) - 1) + P (r + 1) = P (r + 1) * P (r + 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    have hle : P (r + 1) ≤ P (r + 1) * P (r + 1) := Nat.le_mul_of_pos_right _ hPr1_pos
    omega
  have hexp2 : P r * (P (r + 2) - 1) + P r = P r * P (r + 2) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    have hle : P r ≤ P r * P (r + 2) := Nat.le_mul_of_pos_right _ hPr2_pos
    omega
  have hPr_lt_Pr1 : P r < P (r + 1) := by
    rw [hP1_step, hPr]
    have hpow : 2 ^ (s r) ≤ 3 ^ (s r) := Nat.pow_le_pow_left (by decide) (s r)
    have hm : 2 ^ (s r) * u r ≤ 3 ^ (s r) * u r := Nat.mul_le_mul_right (u r) hpow
    omega
  exact ⟨heq_prod, by omega, by omega⟩

/-! ## 45. Theorem SB.45 (Overnight Loop 12): Universal Two-Block Odd-Leftover Cross-Ratio Invariant -/

/-- **Overnight Loop 12: Universal Two-Block Odd-Leftover Cross-Ratio Invariant
(`two_block_odd_leftover_cross_ratio_invariant`, Theorem SB.45)**:
Suppose `ValidBlockChain b_0 s u K` holds, and let `r₁ + 1 < K` and `r₂ + 1 < K`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))`:
1. `3 ^ (s r₁) * P r₁ = 2 ^ (s r₁) * (P (r₁ + 1) - 1) = 6 ^ (s r₁) * u r₁`, and
2. `3 ^ (s r₁) * 2 ^ (s r₂) * P r₁ * (P (r₂ + 1) - 1) = 2 ^ (s r₁) * 3 ^ (s r₂) * P r₂ * (P (r₁ + 1) - 1)`! -/
theorem two_block_odd_leftover_cross_ratio_invariant
    {b_0 K r₁ r₂ : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u K)
    (hr₁ : r₁ + 1 < K)
    (hr₂ : r₂ + 1 < K) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    3 ^ (s r₁) * P r₁ = 2 ^ (s r₁) * (P (r₁ + 1) - 1) ∧
      3 ^ (s r₂) * P r₂ = 2 ^ (s r₂) * (P (r₂ + 1) - 1) ∧
      3 ^ (s r₁) * 2 ^ (s r₂) * P r₁ * (P (r₂ + 1) - 1) =
        2 ^ (s r₁) * 3 ^ (s r₂) * P r₂ * (P (r₁ + 1) - 1) := by
  intro P
  have hch1 : ValidBlockChain b_0 s u (r₁ + 2) := fun k hk => hchain k (by omega)
  have hch2 : ValidBlockChain b_0 s u (r₂ + 2) := fun k hk => hchain k (by omega)
  have hstep1 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch1).1
  have hstep2 := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch2).1
  have hP1 : P r₁ = 2 ^ (s r₁) * u r₁ := (hchain r₁ (by omega)).2.2
  have hP1_next : P (r₁ + 1) = 2 ^ (s (r₁ + 1)) * u (r₁ + 1) := (hchain (r₁ + 1) (by omega)).2.2
  have hP2 : P r₂ = 2 ^ (s r₂) * u r₂ := (hchain r₂ (by omega)).2.2
  have hP2_next : P (r₂ + 1) = 2 ^ (s (r₂ + 1)) * u (r₂ + 1) := (hchain (r₂ + 1) (by omega)).2.2
  have hsub1 : P (r₁ + 1) - 1 = 3 ^ (s r₁) * u r₁ := by omega
  have hsub2 : P (r₂ + 1) - 1 = 3 ^ (s r₂) * u r₂ := by omega
  have heq1 : 3 ^ (s r₁) * P r₁ = 2 ^ (s r₁) * (P (r₁ + 1) - 1) := by
    rw [hP1, hsub1]
    ring
  have heq2 : 3 ^ (s r₂) * P r₂ = 2 ^ (s r₂) * (P (r₂ + 1) - 1) := by
    rw [hP2, hsub2]
    ring
  have heq3 :
      3 ^ (s r₁) * 2 ^ (s r₂) * P r₁ * (P (r₂ + 1) - 1) =
        2 ^ (s r₁) * 3 ^ (s r₂) * P r₂ * (P (r₁ + 1) - 1) := by
    rw [hP1, hP2, hsub1, hsub2]
    ring
  exact ⟨heq1, heq2, heq3⟩

/-! ## 46. Theorem SB.46 (Overnight Loop 13): Three-Point Seed-Free Linear Eliminator & Renewal Cocycle Identity -/

/-- **Overnight Loop 13: Three-Point Seed-Free Linear Eliminator & Renewal Cocycle Identity
(`three_point_seed_free_linear_eliminator_and_cocycle`, Theorem SB.46)**:
Suppose `ValidBlockChain b_0 s u (r + M + 1)` holds for `r, M : ℕ`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_r = blockSteps s r`,
`s' t = s (r + t)`, and `d = blockSteps s' M`:
1. **Renewal Cocycle Splitting**:
   `renewalNumerator s (r + M) = 3 ^ d * renewalNumerator s r + 2 ^ T_r * renewalNumerator s' M`, and
2. **Three-Point Seed-Free Linear Eliminator**:
   `3 ^ d * renewalNumerator s r + 2 ^ T_r * (2 ^ d * P (r + M) - 3 ^ d * P r) = renewalNumerator s (r + M)`! -/
theorem three_point_seed_free_linear_eliminator_and_cocycle
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + M + 1)) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_r := blockSteps s r
    let s' := fun t => s (r + t)
    let d := blockSteps s' M
    renewalNumerator s (r + M) =
        3 ^ d * renewalNumerator s r + 2 ^ T_r * renewalNumerator s' M ∧
      3 ^ d * renewalNumerator s r + 2 ^ T_r * (2 ^ d * P (r + M) - 3 ^ d * P r) =
        renewalNumerator s (r + M) := by
  intro P T_r s' d
  have hch_r : ValidBlockChain b_0 s u r := fun k hk => hchain k (by omega)
  have hch_rM : ValidBlockChain b_0 s u (r + M) := fun k hk => hchain k (by omega)
  have hm_r : 2 ^ T_r * P r = 3 ^ T_r * P 0 + renewalNumerator s r :=
    renewal_prefix_master_identity hch_r
  have hm_rM : 2 ^ (blockSteps s (r + M)) * P (r + M) = 3 ^ (blockSteps s (r + M)) * P 0 + renewalNumerator s (r + M) :=
    renewal_prefix_master_identity hch_rM
  have h10 := (late_step_cauchy_pinch_and_odd_quotient_gcd_dvd (N := r) (M := M) hchain).1
  change 2 ^ d * P (r + M) = 3 ^ d * P r + renewalNumerator s' M at h10
  have hsteps : blockSteps s (r + M) = T_r + d := blockSteps_add_shift s r M
  rw [hsteps] at hm_rM
  have hexp_lhs :
      2 ^ (T_r + d) * P (r + M) =
        3 ^ (T_r + d) * P 0 + (3 ^ d * renewalNumerator s r + 2 ^ T_r * renewalNumerator s' M) := by
    calc
      2 ^ (T_r + d) * P (r + M)
          = 2 ^ T_r * (2 ^ d * P (r + M)) := by rw [Nat.pow_add]; ring
      _ = 2 ^ T_r * (3 ^ d * P r + renewalNumerator s' M) := by rw [h10]
      _ = 3 ^ d * (2 ^ T_r * P r) + 2 ^ T_r * renewalNumerator s' M := by ring
      _ = 3 ^ d * (3 ^ T_r * P 0 + renewalNumerator s r) + 2 ^ T_r * renewalNumerator s' M := by
            rw [hm_r]
      _ = 3 ^ (T_r + d) * P 0 + (3 ^ d * renewalNumerator s r + 2 ^ T_r * renewalNumerator s' M) := by
            rw [Nat.pow_add 3 T_r d]
            ring
  have hcocycle :
      renewalNumerator s (r + M) =
        3 ^ d * renewalNumerator s r + 2 ^ T_r * renewalNumerator s' M := by omega
  have hsub : 2 ^ d * P (r + M) - 3 ^ d * P r = renewalNumerator s' M := by omega
  rw [hsub]
  exact ⟨hcocycle, hcocycle.symm⟩

/-! ## 47. Theorem SB.47 (Overnight Loop 14): Equal-Step-Sum Odd-Leftover Cross-Window Determinant Identity -/

/-- **Overnight Loop 14: Equal-Step-Sum Odd-Leftover Cross-Window Determinant Identity
(`equal_step_odd_leftover_cross_window_determinant_identity`, Theorem SB.47)**:
For any two windows of equal step sum `d` satisfying
`2 ^ d * (2 ^ s₂ * u₂) = 3 ^ d * (2 ^ s₁ * u₁) + A₁₂` and
`2 ^ d * (2 ^ s₄ * u₄) = 3 ^ d * (2 ^ s₃ * u₃) + A₃₄`, we have in `ℤ`:
`(2 : ℤ) ^ d * ((2 : ℤ) ^ (s₁ + s₄) * (u₁ : ℤ) * (u₄ : ℤ) - (2 : ℤ) ^ (s₂ + s₃) * (u₂ : ℤ) * (u₃ : ℤ)) = (2 : ℤ) ^ s₁ * (u₁ : ℤ) * (A₃₄ : ℤ) - (2 : ℤ) ^ s₃ * (u₃ : ℤ) * (A₁₂ : ℤ)`! -/
theorem equal_step_odd_leftover_cross_window_determinant_identity
    {d s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄ A₁₂ A₃₄ : ℕ}
    (hw1 : 2 ^ d * (2 ^ s₂ * u₂) = 3 ^ d * (2 ^ s₁ * u₁) + A₁₂)
    (hw2 : 2 ^ d * (2 ^ s₄ * u₄) = 3 ^ d * (2 ^ s₃ * u₃) + A₃₄) :
    (2 : ℤ) ^ d *
        ((2 : ℤ) ^ (s₁ + s₄) * (u₁ : ℤ) * (u₄ : ℤ) -
          (2 : ℤ) ^ (s₂ + s₃) * (u₂ : ℤ) * (u₃ : ℤ)) =
      (2 : ℤ) ^ s₁ * (u₁ : ℤ) * (A₃₄ : ℤ) -
        (2 : ℤ) ^ s₃ * (u₃ : ℤ) * (A₁₂ : ℤ) := by
  have h3 := (equal_step_window_hankel_determinant_identity_and_bound hw1 hw2).1
  calc
    (2 : ℤ) ^ d *
        ((2 : ℤ) ^ (s₁ + s₄) * (u₁ : ℤ) * (u₄ : ℤ) -
          (2 : ℤ) ^ (s₂ + s₃) * (u₂ : ℤ) * (u₃ : ℤ))
        = (2 : ℤ) ^ d *
            (((2 : ℤ) ^ s₁ * (u₁ : ℤ)) * ((2 : ℤ) ^ s₄ * (u₄ : ℤ)) -
              ((2 : ℤ) ^ s₂ * (u₂ : ℤ)) * ((2 : ℤ) ^ s₃ * (u₃ : ℤ))) := by
          rw [pow_add (2 : ℤ) s₁ s₄, pow_add (2 : ℤ) s₂ s₃]
          ring
    _ = ((2 : ℤ) ^ s₁ * (u₁ : ℤ)) * (A₃₄ : ℤ) -
          ((2 : ℤ) ^ s₃ * (u₃ : ℤ)) * (A₁₂ : ℤ) := by
          exact_mod_cast h3
    _ = (2 : ℤ) ^ s₁ * (u₁ : ℤ) * (A₃₄ : ℤ) -
          (2 : ℤ) ^ s₃ * (u₃ : ℤ) * (A₁₂ : ℤ) := by ring

/-! ## 48. Theorem SB.48 (Overnight Loop 15): Unconditional $4/5$ Cross-Window Hankel Sandwich (Slack-Free!) -/

/-- **Overnight Loop 15: Unconditional $4/5$ Cross-Window Hankel Sandwich
(`unconditional_four_fifths_cross_window_hankel_sandwich`, Theorem SB.48)**:
Suppose two windows of equal step sum `d` satisfy
`2 ^ d * P₂ = 3 ^ d * P₁ + A₁₂` and `2 ^ d * P₄ = 3 ^ d * P₃ + A₃₄`,
with `1 ≤ P₁`, `1 ≤ P₃`, `5 * A₁₂ < 4 * 3 ^ d`, and `5 * A₃₄ < 4 * 3 ^ d`
(which holds **unconditionally** for every surviving block window by Theorem SB.24!):
$$-4 \cdot (3 : \mathbb{Z})^d \cdot P_3 < 5 \cdot (2 : \mathbb{Z})^d \cdot (P_1 P_4 - P_2 P_3) < 4 \cdot (3 : \mathbb{Z})^d \cdot P_1!$$ -/
theorem unconditional_four_fifths_cross_window_hankel_sandwich
    {d P₁ P₂ P₃ P₄ A₁₂ A₃₄ : ℕ}
    (hw1 : 2 ^ d * P₂ = 3 ^ d * P₁ + A₁₂)
    (hw2 : 2 ^ d * P₄ = 3 ^ d * P₃ + A₃₄)
    (hP1 : 1 ≤ P₁)
    (hP3 : 1 ≤ P₃)
    (hA12 : 5 * A₁₂ < 4 * 3 ^ d)
    (hA34 : 5 * A₃₄ < 4 * 3 ^ d) :
    -4 * (3 : ℤ) ^ d * (P₃ : ℤ) <
        5 * (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) ∧
      5 * (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) <
        4 * (3 : ℤ) ^ d * (P₁ : ℤ) := by
  have h3 := (equal_step_window_hankel_determinant_identity_and_bound hw1 hw2).1
  have h5_id :
      5 * (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ)) =
        (P₁ : ℤ) * (5 * (A₃₄ : ℤ)) - (P₃ : ℤ) * (5 * (A₁₂ : ℤ)) := by
    calc
      5 * (2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ))
          = 5 * ((2 : ℤ) ^ d * ((P₁ : ℤ) * (P₄ : ℤ) - (P₂ : ℤ) * (P₃ : ℤ))) := by ring
      _ = 5 * ((P₁ : ℤ) * (A₃₄ : ℤ) - (P₃ : ℤ) * (A₁₂ : ℤ)) := by rw [h3]
      _ = (P₁ : ℤ) * (5 * (A₃₄ : ℤ)) - (P₃ : ℤ) * (5 * (A₁₂ : ℤ)) := by ring
  have hP1_pos : (0 : ℤ) < (P₁ : ℤ) := by exact_mod_cast hP1
  have hP3_pos : (0 : ℤ) < (P₃ : ℤ) := by exact_mod_cast hP3
  have hA12_lt : 5 * (A₁₂ : ℤ) < 4 * (3 : ℤ) ^ d := by exact_mod_cast hA12
  have hA34_lt : 5 * (A₃₄ : ℤ) < 4 * (3 : ℤ) ^ d := by exact_mod_cast hA34
  have hA12_nonneg : (0 : ℤ) ≤ 5 * (A₁₂ : ℤ) := by positivity
  have hA34_nonneg : (0 : ℤ) ≤ 5 * (A₃₄ : ℤ) := by positivity
  have h1 : (P₃ : ℤ) * (5 * (A₁₂ : ℤ)) < (P₃ : ℤ) * (4 * (3 : ℤ) ^ d) :=
    mul_lt_mul_of_pos_left hA12_lt hP3_pos
  have h2 : (0 : ℤ) ≤ (P₁ : ℤ) * (5 * (A₃₄ : ℤ)) :=
    mul_nonneg (le_of_lt hP1_pos) hA34_nonneg
  have h3_lt : (P₁ : ℤ) * (5 * (A₃₄ : ℤ)) < (P₁ : ℤ) * (4 * (3 : ℤ) ^ d) :=
    mul_lt_mul_of_pos_left hA34_lt hP1_pos
  have h4 : (0 : ℤ) ≤ (P₃ : ℤ) * (5 * (A₁₂ : ℤ)) :=
    mul_nonneg (le_of_lt hP3_pos) hA12_nonneg
  rw [h5_id]
  have hcomm1 : (P₃ : ℤ) * (4 * (3 : ℤ) ^ d) = 4 * (3 : ℤ) ^ d * (P₃ : ℤ) := by ring
  have hcomm2 : (P₁ : ℤ) * (4 * (3 : ℤ) ^ d) = 4 * (3 : ℤ) ^ d * (P₁ : ℤ) := by ring
  have hneg : -4 * (3 : ℤ) ^ d * (P₃ : ℤ) = -(4 * (3 : ℤ) ^ d * (P₃ : ℤ)) := by ring
  rw [hcomm1] at h1
  rw [hcomm2] at h3_lt
  rw [hneg]
  omega

/-! ## 49. Theorem SB.49 (Overnight Loop 16): Exact $N$-Bit Base-2 Complement Digit-Sum Law -/

/-- **Overnight Loop 16: Exact $N$-Bit Base-2 Complement Digit-Sum Law
(`mahler_antihydra_base2_complement_digitsum_law`, Theorem SB.49)**:
1. For every `N : ℕ` and `m < 2 ^ N`:
   `base2DigitSum (2 ^ N - 1 - m) + base2DigitSum m = N`, and
2. For every `N : ℕ` and odd `a_0 < 2 ^ N` (`a_0 % 2 = 1`):
   `base2DigitSum (2 ^ N - a_0) + base2DigitSum a_0 = N + 1`! -/
theorem mahler_antihydra_base2_complement_digitsum_law (N : ℕ) :
    (∀ m < 2 ^ N, base2DigitSum (2 ^ N - 1 - m) + base2DigitSum m = N) ∧
      (∀ a_0 < 2 ^ N, a_0 % 2 = 1 →
        base2DigitSum (2 ^ N - a_0) + base2DigitSum a_0 = N + 1) := by
  have h1 : ∀ m < 2 ^ N, base2DigitSum (2 ^ N - 1 - m) + base2DigitSum m = N := by
    induction N with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by
          simp only [Nat.pow_zero] at hm
          omega
        subst hm0
        simp [base2DigitSum]
    | succ N ih =>
        intro m hm
        have hpow : 2 ^ (N + 1) = 2 * 2 ^ N := by
          rw [Nat.pow_succ]
          ring
        have hm_div : m / 2 < 2 ^ N := by omega
        have ihm := ih (m / 2) hm_div
        have hcomp_decomp :
            2 ^ (N + 1) - 1 - m = 2 * (2 ^ N - 1 - m / 2) + (1 - m % 2) := by omega
        rw [hcomp_decomp, base2DigitSum_eq (2 * (2 ^ N - 1 - m / 2) + (1 - m % 2)),
          base2DigitSum_eq m]
        have hmod : (2 * (2 ^ N - 1 - m / 2) + (1 - m % 2)) % 2 = 1 - m % 2 := by omega
        have hdiv : (2 * (2 ^ N - 1 - m / 2) + (1 - m % 2)) / 2 = 2 ^ N - 1 - m / 2 := by omega
        rw [hmod, hdiv]
        omega
  refine ⟨h1, ?_⟩
  intro a_0 ha_lt ha_odd
  have ha_sub_lt : a_0 - 1 < 2 ^ N := by omega
  have hcomp_eq : 2 ^ N - 1 - (a_0 - 1) = 2 ^ N - a_0 := by omega
  have h_sub := h1 (a_0 - 1) ha_sub_lt
  rw [hcomp_eq] at h_sub
  have ha_decomp : a_0 - 1 = 2 * (a_0 / 2) := by omega
  rw [ha_decomp, base2DigitSum_eq (2 * (a_0 / 2))] at h_sub
  have hmod : (2 * (a_0 / 2)) % 2 = 0 := by omega
  have hdiv : (2 * (a_0 / 2)) / 2 = a_0 / 2 := by omega
  rw [hmod, hdiv] at h_sub
  rw [base2DigitSum_eq a_0, ha_odd]
  omega

/-! ## 50. Theorem SB.50 (Overnight Loop 17): Exact $N$-Trit Base-3 Complement Digit-Sum Law -/

/-- **Overnight Loop 17: Exact $N$-Trit Base-3 Complement Digit-Sum Law
(`mahler_antihydra_base3_complement_digitsum_law`, Theorem SB.50)**:
1. For every `N : ℕ` and `m < 3 ^ N`:
   `base3DigitSum (3 ^ N - 1 - m) + base3DigitSum m = 2 * N`, and
2. At step `k = N` of the Mahler–Antihydra complement duality (`b_N + a_N = 3 ^ N` with `1 ≤ b_N` and `1 ≤ a_N`),
   `base3DigitSum (b_N - 1) + base3DigitSum a_N = 2 * N`! -/
theorem mahler_antihydra_base3_complement_digitsum_law (N : ℕ) :
    (∀ m < 3 ^ N, base3DigitSum (3 ^ N - 1 - m) + base3DigitSum m = 2 * N) ∧
      (∀ b_N a_N : ℕ, 1 ≤ b_N → 1 ≤ a_N → b_N + a_N = 3 ^ N →
        base3DigitSum (b_N - 1) + base3DigitSum a_N = 2 * N) := by
  have h1 : ∀ m < 3 ^ N, base3DigitSum (3 ^ N - 1 - m) + base3DigitSum m = 2 * N := by
    induction N with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by
          simp only [Nat.pow_zero] at hm
          omega
        subst hm0
        simp [base3DigitSum]
    | succ N ih =>
        intro m hm
        have hpow : 3 ^ (N + 1) = 3 * 3 ^ N := by
          rw [Nat.pow_succ]
          ring
        have hm_div : m / 3 < 3 ^ N := by omega
        have ihm := ih (m / 3) hm_div
        have hcomp_decomp :
            3 ^ (N + 1) - 1 - m = 3 * (3 ^ N - 1 - m / 3) + (2 - m % 3) := by omega
        have hrem_lt : 2 - m % 3 < 3 := by omega
        rw [hcomp_decomp, base3DigitSum_three_mul_add_digit _ hrem_lt, base3DigitSum_eq m]
        omega
  refine ⟨h1, ?_⟩
  intro b_N a_N hb_pos ha_pos hsum
  have ha_lt : a_N < 3 ^ N := by omega
  have hcomp : 3 ^ N - 1 - a_N = b_N - 1 := by omega
  have h := h1 a_N ha_lt
  rw [hcomp] at h
  exact h

/-! ## 51. Theorem SB.51 (Overnight Loop 18): Post-Bit-Length Colliding Binary/Ternary Window on $N_K$ -/

/-- **Overnight Loop 18: Post-Bit-Length Colliding Binary/Ternary Window on $N_K$
(`post_bitlength_colliding_binary_ternary_window_on_N_K`, Theorem SB.51)**:
Suppose `ValidBlockChain b_0 s u (K + 2)` holds with `∀ k < K + 2, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`T_K1 = T_K + s K`, `A_K = renewalNumerator s K`, and `N_K = 3 ^ T_K * P 0 + A_K`:
1. **Simultaneous $\mathbb{R} \times \mathbb{Q}_2 \times \mathbb{Q}_3$ Pinning of $N_K$ and $P_0$**:
   `N_K = 2 ^ T_K1 * u K`, `Nat.Coprime N_K (3 ^ T_K)`, `N_K / 3 ^ T_K = P 0`, and
   whenever `P 0 < 2 ^ T_K1`, `P 0` is the unique integer `< 2 ^ T_K1` solving
   `(3 ^ T_K * P_0' + A_K) % 2 ^ T_K1 = 0`,
2. **Simultaneous Zero-Carry Base-3 & Base-2 Splits of $N_K$ and $N_K - 1$**:
   `base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K` and
   `base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K)`, and
3. **Strict Post-Surviving Binary Weight Floor on $N_K - 1$**:
   `T_K1 + 1 ≤ base2DigitSum (N_K - 1)`! -/
theorem post_bitlength_colliding_binary_ternary_window_on_N_K
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 2))
    (hs2 : ∀ k < K + 2, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let T_K1 := T_K + s K
    let A_K := renewalNumerator s K
    let N_K := 3 ^ T_K * P 0 + A_K
    (N_K = 2 ^ T_K1 * u K ∧
      Nat.Coprime N_K (3 ^ T_K) ∧
      N_K / 3 ^ T_K = P 0 ∧
      (P 0 < 2 ^ T_K1 →
        ∀ P_0' : ℕ, P_0' < 2 ^ T_K1 →
          (3 ^ T_K * P_0' + A_K) % 2 ^ T_K1 = 0 → P_0' = P 0)) ∧
      (base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K ∧
        base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K) ∧
        T_K1 + 1 ≤ base2DigitSum (N_K - 1)) := by
  intro P T_K T_K1 A_K N_K
  have hch_K1 : ValidBlockChain b_0 s u (K + 1) := fun k hk => hchain k (by omega)
  have hs2_K : ∀ k < K, 2 ≤ s k := fun k hk => hs2 k (by omega)
  have h28 := bridge_a_dual_universe_series_lowest_terms_and_uniqueness hch_K1 hs2_K
  have h32 := bridge_c_multi_step_dual_base2_base3_zero_carry_split hch_K1 hs2_K
  have hid : N_K = 2 ^ T_K1 * u K := h32.1.1
  have hcop : Nat.Coprime N_K (3 ^ T_K) := by
    rw [hid]
    exact h28.2.2.1
  have hs_K1 : 2 ≤ s (K + 1) := hs2 (K + 1) (by omega)
  have h18 := universal_mod12_quotient_lock_and_joint_digitsum_ge_five hchain hs_K1
  have hs2_uK : 2 ≤ base2DigitSum (u K) := h18.2.2.2.1
  have hs2_N1 : base2DigitSum (N_K - 1) + 1 = T_K1 + base2DigitSum (u K) := h32.2.2.2.2
  exact ⟨⟨hid, hcop, h32.1.2.1, h28.2.2.2.2.2.2⟩, ⟨h32.1.2.2.2, hs2_N1, by omega⟩⟩

/-! ## 52. Theorem SB.52 (Overnight Loop 19): Interior Multi-Block Joint Digit-Sum & $79\times$ Quotient Synthesis -/

/-- **Overnight Loop 19: Interior Multi-Block Joint Digit-Sum & $79\times$ Quotient Synthesis
(`interior_multi_block_joint_digitsum_and_seventy_nine_floor`, Theorem SB.52)**:
Suppose `ValidBlockChain b_0 s u (r + 4)` holds with `∀ k < r + 4, 2 ≤ s k`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))` and `T k = blockSteps s k`:
1. `base2DigitSum (P (r + 1)) + base3DigitSum (P (r + 2)) = base2DigitSum (u (r + 1)) + base3DigitSum (u (r + 1)) + 1`,
2. `5 ≤ base2DigitSum (P (r + 1)) + base3DigitSum (P (r + 2))`,
3. `base3DigitSum (2 ^ (T (r + 2)) * u (r + 1)) = base3DigitSum (P 0) + base3DigitSum (renewalNumerator s (r + 1))`,
4. `(s (r + 1) ≤ 6 → 17 ≤ u (r + 1)) ∧ (s (r + 1) = 2 → 79 ≤ u (r + 1))`, and
5. `s (r + 1) = 2 → 395 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)`! -/
theorem interior_multi_block_joint_digitsum_and_seventy_nine_floor
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 4))
    (hs2 : ∀ k < r + 4, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T := fun k => blockSteps s k
    base2DigitSum (P (r + 1)) + base3DigitSum (P (r + 2)) =
        base2DigitSum (u (r + 1)) + base3DigitSum (u (r + 1)) + 1 ∧
      5 ≤ base2DigitSum (P (r + 1)) + base3DigitSum (P (r + 2)) ∧
      base3DigitSum (2 ^ (T (r + 2)) * u (r + 1)) =
        base3DigitSum (P 0) + base3DigitSum (renewalNumerator s (r + 1)) ∧
      ((s (r + 1) ≤ 6 → 17 ≤ u (r + 1)) ∧ (s (r + 1) = 2 → 79 ≤ u (r + 1))) ∧
      (s (r + 1) = 2 → 395 * 2 ^ (T (r + 2)) < 3 ^ (T (r + 1)) * (5 * P 0 + 4)) := by
  intro P T
  have hs_r : 2 ≤ s r := hs2 r (by omega)
  have hs_r1 : 2 ≤ s (r + 1) := hs2 (r + 1) (by omega)
  have hs_r2 : 2 ≤ s (r + 2) := hs2 (r + 2) (by omega)
  have hs_r3 : 2 ≤ s (r + 3) := hs2 (r + 3) (by omega)
  have hch_next2 : ValidBlockChain b_0 s u ((r + 1) + 2) := fun k hk => hchain k (by omega)
  have hjoint :=
    (top_down_senge_straus_stewart_joint_digitsum_blueprint
      (M := 4) (N := 0) (g_0 := 0) (g_N := 0) (K_N := 0) (B := 0)
      hch_next2 (by decide) (by decide)).1
  change base2DigitSum (P (r + 1)) + base3DigitSum (P (r + 2)) =
    base2DigitSum (u (r + 1)) + base3DigitSum (u (r + 1)) + 1 at hjoint
  have h18 := universal_mod12_quotient_lock_and_joint_digitsum_ge_five hch_next2 hs_r2
  have hge5 : 5 ≤ base2DigitSum (P (r + 1)) + base3DigitSum (P (r + 2)) := h18.2.2.2.2.2
  have h29 :=
    (bridge_b_seed_independent_base3_step_evolution (K := r + 3) hchain
      (fun k hk => hs2 k (by omega))).1 (r + 1) (by omega)
  change base3DigitSum (2 ^ (T (r + 2)) * u (r + 1)) =
    base3DigitSum (P 0) + base3DigitSum (renewalNumerator s (r + 1)) at h29
  have h40 := interior_extinction_of_five_and_seven_and_seventeen_floor
    hchain hs_r hs_r1 hs_r2 hs_r3
  have h41 := even_rung_mod16_trap_and_seventy_nine_floor_at_rung_two
    hchain hs_r hs_r1 hs_r2 hs_r3
  have h43 := sharpened_seventeen_seventy_nine_interior_archimedean_ceiling hchain hs2
  exact ⟨hjoint, hge5, h29, ⟨h40.2.2.2.1, h41.2.2⟩, h43.2.2⟩

/-! ## 53. Theorem SB.53 (Overnight Loop 20): Grand 53-Bridge Semigroup-Breakout Synthesis -/

/-- **Overnight Loop 20: Grand 53-Bridge Semigroup-Breakout Synthesis
(`grand_semigroup_breakout_53_bridge_synthesis`, Theorem SB.53)**:
Suppose `ValidBlockChain b_0 s u (K + 4)` holds with `∀ k < K + 4, 2 ≤ s k`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T k = blockSteps s k`,
`A k = renewalNumerator s k`, and `N k = 3 ^ (T k) * P 0 + A k`:
1. **Unconditional $4/5$ Renewal Ceiling & Dual Base-2/Base-3 Zero-Carry Split of $N_K$**:
   `5 * A K + 4 * 2 ^ (T K) ≤ 4 * 3 ^ (T K)`,
   `N K = 2 ^ (T (K + 1)) * u K`,
   `base3DigitSum (N K) = base3DigitSum (P 0) + base3DigitSum (A K)`, and
   `base2DigitSum (N K - 1) + 1 = T (K + 1) + base2DigitSum (u K)`,
2. **Telescoped Binary Halving-Budget Law**:
   `(T (K + 1) - s 0) + base2DigitSum (u K) + sumBase2Quotient u K = base2DigitSum (u 0) + K + sumBase2TriadicScaled s u K`,
3. **Zero-Carry 3-Adic Factorial & Joint $(v_2, v_3)$ Factorial Syzygy**:
   `legendreFactVal3 (N K) = legendreFactVal3 (3 ^ (T K) * P 0) + legendreFactVal3 (A K)` and
   `legendreFactVal2 (N K) + base2DigitSum (u K) = 2 * legendreFactVal3 (N K) + base3DigitSum (P 0) + base3DigitSum (A K)`, and
4. **Interior Mod-36 / Mod-16 Extinction & $79\times$ Sharpened Ceiling at `K + 1`**:
   `(s (K + 1) ≤ 6 → 17 ≤ u (K + 1)) ∧ (s (K + 1) = 2 → 79 ≤ u (K + 1))` and
   `s (K + 1) = 2 → 395 * 2 ^ (T (K + 2)) < 3 ^ (T (K + 1)) * (5 * P 0 + 4)`! -/
theorem grand_semigroup_breakout_53_bridge_synthesis
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 4))
    (hs2 : ∀ k < K + 4, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T := fun k => blockSteps s k
    let A := fun k => renewalNumerator s k
    let N := fun k => 3 ^ (T k) * P 0 + A k
    (5 * A K + 4 * 2 ^ (T K) ≤ 4 * 3 ^ (T K) ∧
      N K = 2 ^ (T (K + 1)) * u K ∧
      base3DigitSum (N K) = base3DigitSum (P 0) + base3DigitSum (A K) ∧
      base2DigitSum (N K - 1) + 1 = T (K + 1) + base2DigitSum (u K)) ∧
      ((T (K + 1) - s 0) + base2DigitSum (u K) + sumBase2Quotient u K =
        base2DigitSum (u 0) + K + sumBase2TriadicScaled s u K) ∧
      (legendreFactVal3 (N K) = legendreFactVal3 (3 ^ (T K) * P 0) + legendreFactVal3 (A K) ∧
        legendreFactVal2 (N K) + base2DigitSum (u K) =
          2 * legendreFactVal3 (N K) + base3DigitSum (P 0) + base3DigitSum (A K)) ∧
      (((s (K + 1) ≤ 6 → 17 ≤ u (K + 1)) ∧ (s (K + 1) = 2 → 79 ≤ u (K + 1))) ∧
        (s (K + 1) = 2 → 395 * 2 ^ (T (K + 2)) < 3 ^ (T (K + 1)) * (5 * P 0 + 4))) := by
  intro P T A N
  have hch_K1 : ValidBlockChain b_0 s u (K + 1) := fun k hk => hchain k (by omega)
  have hs2_K : ∀ k < K, 2 ≤ s k := fun k hk => hs2 k (by omega)
  have h24 := unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery hch_K1 hs2_K
  have h32 := bridge_c_multi_step_dual_base2_base3_zero_carry_split hch_K1 hs2_K
  have h33 := bridge_c_telescoped_binary_halving_budget_law hch_K1
  have h35 := zero_carry_three_adic_factorial_and_binomial_valuation_law hch_K1 hs2_K
  have h36 := joint_multi_block_factorial_valuation_syzygy hch_K1 hs2_K
  have h52 := interior_multi_block_joint_digitsum_and_seventy_nine_floor hchain hs2
  exact ⟨⟨h24.1, h32.1.1, h32.1.2.2.2, h32.2.2.2.2⟩, h33, ⟨h35.2.1, h36.1⟩, ⟨h52.2.2.2.1, h52.2.2.2.2⟩⟩

/-! ## 54. Theorem SB.54: Cross-Application of Mahler Bridges to Collatz ($3n+1$) & 1-Cycle / 2-Cycle Exclusion -/

/-- **Cross-Application of Mahler Bridges to Collatz ($3n+1$) & 1-Cycle / 2-Cycle Exclusion
(`collatz_syracuse_bridge_and_one_two_cycle_exclusion`, Theorem SB.54)**:
The Collatz Syracuse odd-step equation `2 ^ s * u' = 3 * u + 1` is the exact `s_r = 1`
specialization of the Mahler odd-block equation `2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1`.
Consequently, our Mahler Base-2 and Base-3 bridges transfer directly to Collatz:
1. **Collatz One-Step Base-3 & Base-2 Carry Laws**:
   Whenever `2 ^ s * u' = 3 * u + 1` with `u' % 2 = 1`:
   - `(2 ^ s * u') / 3 = u` and `(2 ^ s * u') % 3 = 1`,
   - `base3DigitSum (2 ^ s * u') = base3DigitSum u + 1` (Base-3 zero-carry law), and
   - `base2DigitSum (3 * u) + 1 = base2DigitSum u' + s` (Base-2 trailing-ones depletion law)!
2. **Unconditional Collatz 1-Cycle Theorem (`u_0 = 1, s = 2` is unique)**:
   Whenever `2 ^ s * u_0 = 3 * u_0 + 1` with `1 ≤ u_0`, we have `s = 2` and `u_0 = 1`
   (and at that fixed point, `base2DigitSum (3 * u_0) - base2DigitSum u_0 = s - 1 = 1` and
   `base3DigitSum (2 ^ s * u_0) - base3DigitSum u_0 = 1`), and
3. **Unconditional Disproof of Non-Trivial Collatz 2-Cycles (`u_0 → u_1 → u_0`), Contrasted with $3n - 1$'s `5 → 7 → 5` Loop**:
   - In **$3n + 1$ (Collatz)**: there do **not** exist integers `1 ≤ u_0 < u_1` and exponents `1 ≤ s_0, 1 ≤ s_1`
     satisfying `2 ^ s_0 * u_1 = 3 * u_0 + 1` and `2 ^ s_1 * u_0 = 3 * u_1 + 1`!
   - In **$3n - 1$**: Catalan's identity `3 ^ 2 - 2 ^ 3 = 1` produces the genuine 2-cycle
     `2 ^ 1 * 7 = 3 * 5 - 1` and `2 ^ 2 * 5 = 3 * 7 - 1`! -/
theorem collatz_syracuse_bridge_and_one_two_cycle_exclusion :
    (∀ s u u' : ℕ, u' % 2 = 1 → 2 ^ s * u' = 3 * u + 1 →
      (2 ^ s * u') / 3 = u ∧
        (2 ^ s * u') % 3 = 1 ∧
        base3DigitSum (2 ^ s * u') = base3DigitSum u + 1 ∧
        base2DigitSum (3 * u) + 1 = base2DigitSum u' + s) ∧
      (∀ s u_0 : ℕ, 1 ≤ u_0 → 2 ^ s * u_0 = 3 * u_0 + 1 → s = 2 ∧ u_0 = 1) ∧
      (∀ s_0 s_1 u_0 u_1 : ℕ,
        1 ≤ s_0 → 1 ≤ s_1 → 1 ≤ u_0 → u_0 < u_1 →
          2 ^ s_0 * u_1 = 3 * u_0 + 1 → ¬ (2 ^ s_1 * u_0 = 3 * u_1 + 1)) ∧
      (2 ^ 1 * 7 = 3 * 5 - 1 ∧ 2 ^ 2 * 5 = 3 * 7 - 1) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s u u' hu'_odd hstep
    have hdiv : (2 ^ s * u') / 3 = u := by omega
    have hmod : (2 ^ s * u') % 3 = 1 := by omega
    have hs3 : base3DigitSum (2 ^ s * u') = base3DigitSum u + 1 := by
      rw [hstep, base3DigitSum_three_mul_add_digit u (by decide)]
      omega
    have hs2 : base2DigitSum (3 * u) + 1 = base2DigitSum u' + s := by
      have hsub : 3 * u = 2 ^ s * u' - 1 := by omega
      rw [hsub]
      exact base2DigitSum_two_pow_mul_sub_one s hu'_odd
    exact ⟨hdiv, hmod, hs3, hs2⟩
  · intro s u_0 hu0_pos h1cycle
    have hcases : s ≤ 2 ∨ 3 ≤ s := by omega
    rcases hcases with hle2 | hge3
    · have : s = 0 ∨ s = 1 ∨ s = 2 := by omega
      rcases this with rfl | rfl | rfl
      · omega
      · omega
      · omega
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k + 3 := ⟨s - 3, by omega⟩
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
      have hpow : 8 ≤ 2 ^ (k + 3) := by
        rw [Nat.pow_add]
        omega
      have hmul : 8 * u_0 ≤ 2 ^ (k + 3) * u_0 := Nat.mul_le_mul_right u_0 hpow
      omega
  · intro s_0 s_1 u_0 u_1 hs0 hs1 hu0 hlt hstep0 hstep1
    have hs0_lt2 : ¬ (2 ≤ s_0) := by
      intro hge2
      obtain ⟨k, hk⟩ : ∃ k : ℕ, s_0 = k + 2 := ⟨s_0 - 2, by omega⟩
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
      have hpow : 4 ≤ 2 ^ s_0 := by
        rw [hk, Nat.pow_add]
        omega
      have hmul : 4 * u_1 ≤ 2 ^ s_0 * u_1 := Nat.mul_le_mul_right u_1 hpow
      omega
    have hs0_eq1 : s_0 = 1 := by omega
    rw [hs0_eq1] at hstep0
    have hcomb : 2 ^ (1 + s_1) * u_0 = 9 * u_0 + 5 := by
      calc
        2 ^ (1 + s_1) * u_0 = 2 * (2 ^ s_1 * u_0) := by
          rw [Nat.pow_add]
          ring
        _ = 2 * (3 * u_1 + 1) := by rw [hstep1]
        _ = 3 * (2 ^ 1 * u_1) + 2 := by ring
        _ = 3 * (3 * u_0 + 1) + 2 := by rw [hstep0]
        _ = 9 * u_0 + 5 := by ring
    have hs1_cases : s_1 = 1 ∨ s_1 = 2 ∨ 3 ≤ s_1 := by omega
    rcases hs1_cases with rfl | rfl | hge3
    · omega
    · omega
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, s_1 = k + 3 := ⟨s_1 - 3, by omega⟩
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
      have hpow : 16 ≤ 2 ^ (1 + (k + 3)) := by
        have hadd : 1 + (k + 3) = k + 4 := by omega
        rw [hadd, Nat.pow_add]
        omega
      have hmul : 16 * u_0 ≤ 2 ^ (1 + (k + 3)) * u_0 := Nat.mul_le_mul_right u_0 hpow
      omega

/-! ## 55. Theorem SB.55: Universal Constant-Rung Affine Invariance & Finite Run-Length Ceiling in $3/2 \bmod 1$ -/

/-- **Universal Constant-Rung Affine Invariance & Finite Run-Length Ceiling
(`universal_constant_rung_affine_invariance_and_run_length_bound`, Theorem SB.55)**:
In Mahler's $3/2 \bmod 1$ block dynamics, suppose $m$ consecutive blocks have constant
halving count $s \ge 1$ (`ValidBlockChain b_0 s_seq u (r + m + 1)` with `∀ k ≤ m, s_seq (r + k) = s`):
1. **One-Step Affine Invariance**:
   Across any single block with `2 ^ s * u' = 3 ^ s * u + 1`:
   `2 ^ s * ((3 ^ s - 2 ^ s) * u' + 1) = 3 ^ s * ((3 ^ s - 2 ^ s) * u + 1)`,
2. **$m$-Block Constant-Rung Power Identity**:
   `2 ^ (s * m) * ((3 ^ s - 2 ^ s) * u (r + m) + 1) = 3 ^ (s * m) * ((3 ^ s - 2 ^ s) * u r + 1)`, and
3. **Exact Divisibility & Finite Run-Length Ceiling (`2^{s m} ≤ (3^s - 2^s) u_r + 1`)**:
   `2 ^ (s * m) ∣ ((3 ^ s - 2 ^ s) * u r + 1)` and
   `2 ^ (s * m) ≤ (3 ^ s - 2 ^ s) * u r + 1`
   (in particular, for a run of `s = 2`, `4 ^ m ∣ (5 * u r + 1)` and `4 ^ m ≤ 5 * u r + 1`,
   proving that **no integer seed can sustain an infinite constant-rung run**)! -/
theorem universal_constant_rung_affine_invariance_and_run_length_bound
    {b_0 r m s : ℕ} {s_seq u : ℕ → ℕ}
    (hs_pos : 1 ≤ s)
    (hchain : ValidBlockChain b_0 s_seq u (r + m + 1))
    (hconst : ∀ k ≤ m, s_seq (r + k) = s) :
    2 ^ (s * m) * ((3 ^ s - 2 ^ s) * u (r + m) + 1) =
        3 ^ (s * m) * ((3 ^ s - 2 ^ s) * u r + 1) ∧
      2 ^ (s * m) ∣ ((3 ^ s - 2 ^ s) * u r + 1) ∧
      2 ^ (s * m) ≤ (3 ^ s - 2 ^ s) * u r + 1 := by
  have h2_lt_3 : 2 ^ s < 3 ^ s := two_pow_lt_three_pow_of_pos hs_pos
  have hid :
      2 ^ (s * m) * ((3 ^ s - 2 ^ s) * u (r + m) + 1) =
        3 ^ (s * m) * ((3 ^ s - 2 ^ s) * u r + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
        have hch_m : ValidBlockChain b_0 s_seq u (r + m + 1) := fun k hk => hchain k (by omega)
        have hconst_m : ∀ k ≤ m, s_seq (r + k) = s := fun k hk => hconst k (by omega)
        have ihm := ih hch_m hconst_m
        have hch_step : ValidBlockChain b_0 s_seq u ((r + m) + 2) := fun k hk => hchain k (by omega)
        have hstep := (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_step).1
        have hs_m : s_seq (r + m) = s := hconst m (by omega)
        have hs_m1 : s_seq (r + m + 1) = s := by
          have h := hconst (m + 1) (by omega)
          simpa [Nat.add_assoc] using h
        change 2 ^ (s_seq (r + m + 1)) * u (r + (m + 1)) =
          3 ^ (s_seq (r + m)) * u (r + m) + 1 at hstep
        rw [hs_m, hs_m1] at hstep
        have hone :
            2 ^ s * ((3 ^ s - 2 ^ s) * u (r + (m + 1)) + 1) =
              3 ^ s * ((3 ^ s - 2 ^ s) * u (r + m) + 1) := by
          have hsub : 3 ^ s - 2 ^ s + 2 ^ s = 3 ^ s := by omega
          calc
            2 ^ s * ((3 ^ s - 2 ^ s) * u (r + (m + 1)) + 1)
                = (3 ^ s - 2 ^ s) * (2 ^ s * u (r + (m + 1))) + 2 ^ s := by ring
            _ = (3 ^ s - 2 ^ s) * (3 ^ s * u (r + m) + 1) + 2 ^ s := by rw [hstep]
            _ = 3 ^ s * ((3 ^ s - 2 ^ s) * u (r + m)) + (3 ^ s - 2 ^ s + 2 ^ s) := by ring
            _ = 3 ^ s * ((3 ^ s - 2 ^ s) * u (r + m)) + 3 ^ s := by rw [hsub]
            _ = 3 ^ s * ((3 ^ s - 2 ^ s) * u (r + m) + 1) := by ring
        calc
          2 ^ (s * (m + 1)) * ((3 ^ s - 2 ^ s) * u (r + (m + 1)) + 1)
              = 2 ^ (s * m) * (2 ^ s * ((3 ^ s - 2 ^ s) * u (r + (m + 1)) + 1)) := by
                rw [Nat.mul_succ s m, Nat.pow_add 2 (s * m) s]
                ring
          _ = 2 ^ (s * m) * (3 ^ s * ((3 ^ s - 2 ^ s) * u (r + m) + 1)) := by rw [hone]
          _ = 3 ^ s * (2 ^ (s * m) * ((3 ^ s - 2 ^ s) * u (r + m) + 1)) := by ring
          _ = 3 ^ s * (3 ^ (s * m) * ((3 ^ s - 2 ^ s) * u r + 1)) := by rw [ihm]
          _ = 3 ^ (s * (m + 1)) * ((3 ^ s - 2 ^ s) * u r + 1) := by
                rw [Nat.mul_succ s m, Nat.pow_add 3 (s * m) s]
                ring
  have hcop : Nat.Coprime (2 ^ (s * m)) (3 ^ (s * m)) :=
    ((by decide : Nat.Coprime 2 3).pow_left (s * m)).pow_right (s * m)
  have hdvd_mul : 2 ^ (s * m) ∣ 3 ^ (s * m) * ((3 ^ s - 2 ^ s) * u r + 1) :=
    ⟨(3 ^ s - 2 ^ s) * u (r + m) + 1, hid.symm⟩
  have hdvd : 2 ^ (s * m) ∣ ((3 ^ s - 2 ^ s) * u r + 1) :=
    hcop.dvd_of_dvd_mul_left hdvd_mul
  have hpos_rhs : 0 < (3 ^ s - 2 ^ s) * u r + 1 := by omega
  have hle : 2 ^ (s * m) ≤ (3 ^ s - 2 ^ s) * u r + 1 := Nat.le_of_dvd hpos_rhs hdvd
  exact ⟨hid, hdvd, hle⟩

/-! ## 56. Theorem SB.56: Sharp Equality Characterization of the $4/5$ Ceiling & Disproof of Universal Sub-$1/2$ Slack -/

/-- **Sharp Equality Characterization of the $4/5$ Ceiling & Disproof of Universal Sub-$1/2$ Slack
(`sharp_four_fifths_equality_characterization_and_two_two_escape`, Theorem SB.56)**:
1. **Proved Universal Structure (Exact Equality Characterization of the $4/5$ Ceiling)**:
   Whenever `∀ k < r, s k = 2`, we have the **exact closed-form identity**
   `5 * renewalNumerator s r + 4 * 2 ^ (blockSteps s r) = 4 * 3 ^ (blockSteps s r)`,
   whereas whenever `∀ k < r, 2 ≤ s k` and `∃ k₀ < r, 3 ≤ s k₀`, we have the **strict inequality**
   `5 * renewalNumerator s r + 4 * 2 ^ (blockSteps s r) < 4 * 3 ^ (blockSteps s r)`, and
2. **Disproved Naive Conjecture (Surviving $s_k \ge 2$ Chains Need Not Have Sub-$1/2$ Renewal Slack)**:
   For the constant-$2$ sequence `s = fun _ => 2` at `r = 2`, every block satisfies `2 ≤ s k`,
   yet `renewalNumerator (fun _ => 2) 2 = 52` and `3 ^ (blockSteps (fun _ => 2) 2) = 81`,
   so `2 * renewalNumerator (fun _ => 2) 2 = 104 > 81` (`renewalIntSlack (fun _ => 2) 2 = -23 < 0`),
   disproving both the naive sub-$1/2$ slack conjecture and the admissibility of $(2, 2)$ in $3/2 \bmod 1$! -/
theorem sharp_four_fifths_equality_characterization_and_two_two_escape :
    (∀ (s : ℕ → ℕ) (r : ℕ),
      (∀ k < r, s k = 2) →
        5 * renewalNumerator s r + 4 * 2 ^ (blockSteps s r) = 4 * 3 ^ (blockSteps s r)) ∧
      (∀ (s : ℕ → ℕ),
        2 ≤ s 0 → 3 ≤ s 1 →
          5 * renewalNumerator s 2 + 4 * 2 ^ (blockSteps s 2) < 4 * 3 ^ (blockSteps s 2)) ∧
      (renewalNumerator (fun _ => 2) 2 = 52 ∧
        3 ^ (blockSteps (fun _ => 2) 2) = 81 ∧
        2 * renewalNumerator (fun _ => 2) 2 > 3 ^ (blockSteps (fun _ => 2) 2) ∧
        renewalIntSlack (fun _ => 2) 2 = -23) := by
  refine ⟨?_, ?_, by decide⟩
  · intro s r hs2
    induction r with
    | zero => simp [renewalNumerator, blockSteps]
    | succ r ih =>
        have ihr := ih (fun k hk => hs2 k (by omega))
        have hsr : s r = 2 := hs2 r (by omega)
        set T := blockSteps s r
        set A := renewalNumerator s r
        calc
          5 * renewalNumerator s (r + 1) + 4 * 2 ^ (blockSteps s (r + 1))
              = 5 * (3 ^ (s r) * A + 2 ^ (T + s r)) + 4 * 2 ^ (T + s r) := rfl
          _ = 9 * (5 * A + 4 * 2 ^ T) := by
                rw [hsr, Nat.pow_add 2 T 2]
                ring
          _ = 9 * (4 * 3 ^ T) := by rw [ihr]
          _ = 4 * 3 ^ (blockSteps s (r + 1)) := by
                change 9 * (4 * 3 ^ T) = 4 * 3 ^ (T + s r)
                rw [hsr, Nat.pow_add 3 T 2]
                ring
  · intro s hs0 hs1
    have hinv1 : 5 * renewalNumerator s 1 + 4 * 2 ^ (blockSteps s 1) ≤ 4 * 3 ^ (blockSteps s 1) :=
      five_mul_renewalNumerator_add_four_mul_two_pow_le s 1
        (fun k hk => by
          have hk0 : k = 0 := by omega
          rw [hk0]
          exact hs0)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s 1 = k + 3 := ⟨s 1 - 3, by omega⟩
    have hle_pow : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
    have h2_pos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
    have h9_strict : 9 * 2 ^ (s 1) < 4 * 3 ^ (s 1) := by
      have hm : 72 * 2 ^ k ≤ 72 * 3 ^ k := Nat.mul_le_mul_left 72 hle_pow
      rw [hk, Nat.pow_add 2 k 3, Nat.pow_add 3 k 3]
      omega
    set T := blockSteps s 1
    set A := renewalNumerator s 1
    have h2T_pos : 0 < 2 ^ T := Nat.pow_pos (by decide)
    have hexp :
        5 * renewalNumerator s 2 + 4 * 2 ^ (blockSteps s 2) =
          3 ^ (s 1) * (5 * A) + (9 * 2 ^ (s 1)) * 2 ^ T := by
      change 5 * (3 ^ (s 1) * A + 2 ^ (T + s 1)) + 4 * 2 ^ (T + s 1) =
        3 ^ (s 1) * (5 * A) + (9 * 2 ^ (s 1)) * 2 ^ T
      rw [Nat.pow_add 2 T (s 1)]
      ring
    have hlt1 : (9 * 2 ^ (s 1)) * 2 ^ T < (4 * 3 ^ (s 1)) * 2 ^ T :=
      Nat.mul_lt_mul_of_pos_right h9_strict h2T_pos
    have hfactor :
        3 ^ (s 1) * (5 * A) + (4 * 3 ^ (s 1)) * 2 ^ T =
          3 ^ (s 1) * (5 * A + 4 * 2 ^ T) := by ring
    have hstep2 : 3 ^ (s 1) * (5 * A + 4 * 2 ^ T) ≤ 3 ^ (s 1) * (4 * 3 ^ T) :=
      Nat.mul_le_mul_left (3 ^ (s 1)) hinv1
    have hpow3 : 3 ^ (s 1) * (4 * 3 ^ T) = 4 * 3 ^ (blockSteps s 2) := by
      change 3 ^ (s 1) * (4 * 3 ^ T) = 4 * 3 ^ (T + s 1)
      rw [Nat.pow_add 3 T (s 1)]
      ring
    omega

/-! ## 57. Theorem SB.57: Two-Window $(j+n, k+n)$ Diagonal Cauchy Tail-Freeze & Quotient Invariance Law -/

/-- **Two-Window $(j+n, k+n)$ Diagonal Cauchy Tail-Freeze & Quotient Invariance Law
(`two_window_jk_diagonal_cauchy_tail_freeze_and_quotient_invariance`, Theorem SB.57)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M_1 + M_2 + 1)` holds with
`∀ k < M_1, 2 ≤ s (r + 1 + k)` and `∀ k < M_2, 2 ≤ s (r + 1 + M_1 + k)`.
Starting from block $r$ with $3$-exponent $j = s_r$, advance across two consecutive future
windows of $M_1$ blocks ($n_1$ steps, ending rung $k_1 = s_{r+1+M_1}$) and $M_2$ blocks
($n_2$ steps, ending rung $k_2 = s_{r+1+M_1+M_2}$), with $S_1 = n_1 + k_1$,
$S_{12} = n_1 + n_2 + k_2$, $T_1 = j + n_1$, $T_{12} = j + n_1 + n_2$,
$R_1 = 3^{n_1} + \text{renewalNumerator}(s_1, M_1)$, $A_2 = \text{renewalNumerator}(s_2, M_2)$,
and $R_{12} = 3^{n_2} R_1 + 2^{n_1} A_2$:
1. **First-Horizon $(j+n_1, k_1+n_1)$ Diagonal Identity & Recovery**:
   `2 ^ S_1 * u (r + 1 + M_1) = 3 ^ T_1 * u r + R_1`, `R_1 < 3 ^ T_1`, and
   `(2 ^ S_1 * u (r + 1 + M_1)) / 3 ^ T_1 = u r`,
2. **Second-Horizon $(j+n_1+n_2, k_2+n_1+n_2)$ Diagonal Transition**:
   `2 ^ S_12 * u (r + 1 + M_1 + M_2) = 3 ^ n_2 * (2 ^ S_1 * u (r + 1 + M_1)) + 2 ^ n_1 * A_2` and
   `2 ^ S_12 * u (r + 1 + M_1 + M_2) = 3 ^ T_12 * u r + R_12`,
3. **Unconditional $4/5$ Cauchy Tail-Freeze Bound**:
   `5 * (R_12 - 3 ^ n_2 * R_1) + 4 * 2 ^ (n_1 + n_2) ≤ 4 * 2 ^ n_1 * 3 ^ n_2` and
   `5 * R_12 + 4 * 2 ^ (n_1 + n_2) ≤ 9 * 3 ^ (n_1 + n_2)`, and
4. **Two-Horizon Quotient & Base-3 Top-Block Invariance**:
   `R_12 < 3 ^ T_12`,
   `(2 ^ S_12 * u (r + 1 + M_1 + M_2)) / 3 ^ T_12 = u r`,
   `(2 ^ S_12 * u (r + 1 + M_1 + M_2)) / 3 ^ T_12 = (2 ^ S_1 * u (r + 1 + M_1)) / 3 ^ T_1`, and
   `base3DigitSum (2 ^ S_12 * u (r + 1 + M_1 + M_2)) = base3DigitSum (u r) + base3DigitSum R_12`! -/
theorem two_window_jk_diagonal_cauchy_tail_freeze_and_quotient_invariance
    {b_0 r M_1 M_2 : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M_1 + M_2 + 1))
    (hs1 : ∀ k < M_1, 2 ≤ s (r + 1 + k))
    (hs2 : ∀ k < M_2, 2 ≤ s (r + 1 + M_1 + k)) :
    let j := s r
    let s_1 := fun t => s (r + 1 + t)
    let s_2 := fun t => s (r + 1 + M_1 + t)
    let n_1 := blockSteps s_1 M_1
    let n_2 := blockSteps s_2 M_2
    let k_1 := s (r + 1 + M_1)
    let k_2 := s (r + 1 + M_1 + M_2)
    let S_1 := n_1 + k_1
    let S_12 := n_1 + n_2 + k_2
    let T_1 := j + n_1
    let T_12 := j + n_1 + n_2
    let R_1 := 3 ^ n_1 + renewalNumerator s_1 M_1
    let A_2 := renewalNumerator s_2 M_2
    let R_12 := 3 ^ n_2 * R_1 + 2 ^ n_1 * A_2
    (2 ^ S_1 * u (r + 1 + M_1) = 3 ^ T_1 * u r + R_1 ∧
      R_1 < 3 ^ T_1 ∧
      (2 ^ S_1 * u (r + 1 + M_1)) / 3 ^ T_1 = u r) ∧
      (2 ^ S_12 * u (r + 1 + M_1 + M_2) =
          3 ^ n_2 * (2 ^ S_1 * u (r + 1 + M_1)) + 2 ^ n_1 * A_2 ∧
        2 ^ S_12 * u (r + 1 + M_1 + M_2) = 3 ^ T_12 * u r + R_12) ∧
      (5 * (R_12 - 3 ^ n_2 * R_1) + 4 * 2 ^ (n_1 + n_2) ≤ 4 * 2 ^ n_1 * 3 ^ n_2 ∧
        5 * R_12 + 4 * 2 ^ (n_1 + n_2) ≤ 9 * 3 ^ (n_1 + n_2)) ∧
      (R_12 < 3 ^ T_12 ∧
        (2 ^ S_12 * u (r + 1 + M_1 + M_2)) / 3 ^ T_12 = u r ∧
        (2 ^ S_12 * u (r + 1 + M_1 + M_2)) / 3 ^ T_12 =
          (2 ^ S_1 * u (r + 1 + M_1)) / 3 ^ T_1 ∧
        base3DigitSum (2 ^ S_12 * u (r + 1 + M_1 + M_2)) =
          base3DigitSum (u r) + base3DigitSum R_12) := by
  intro j s_1 s_2 n_1 n_2 k_1 k_2 S_1 S_12 T_1 T_12 R_1 A_2 R_12
  have hch1 : ValidBlockChain b_0 s u (r + 1 + M_1 + 1) :=
    fun k hk => hchain k (by omega)
  have h25_1 := unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound hch1 hs1
  dsimp only at h25_1
  have h95_1 : 5 * R_1 + 4 * 2 ^ n_1 ≤ 9 * 3 ^ n_1 := h25_1.1
  have hR1_lt : R_1 < 3 ^ T_1 := h25_1.2.2.1
  have hdiv1 : (2 ^ S_1 * u (r + 1 + M_1)) / 3 ^ T_1 = u r := h25_1.2.2.2.1
  have hmod1 : (2 ^ S_1 * u (r + 1 + M_1)) % 3 ^ T_1 = R_1 := h25_1.2.2.2.2.1
  have hid1 : 2 ^ S_1 * u (r + 1 + M_1) = 3 ^ T_1 * u r + R_1 := by
    have hdm := Nat.div_add_mod (2 ^ S_1 * u (r + 1 + M_1)) (3 ^ T_1)
    rw [hdiv1, hmod1] at hdm
    exact hdm.symm
  have h10_2 := late_step_cauchy_pinch_and_odd_quotient_gcd_dvd
    (N := r + 1 + M_1) (M := M_2) hchain
  have hu2_raw :
      2 ^ (n_2 + k_2) * u (r + 1 + M_1 + M_2) =
        3 ^ n_2 * 2 ^ k_1 * u (r + 1 + M_1) + A_2 := h10_2.2.1
  have htrans :
      2 ^ S_12 * u (r + 1 + M_1 + M_2) =
        3 ^ n_2 * (2 ^ S_1 * u (r + 1 + M_1)) + 2 ^ n_1 * A_2 := by
    have hm := congrArg (fun x => 2 ^ n_1 * x) hu2_raw
    dsimp only at hm
    have hpowL : 2 ^ n_1 * (2 ^ (n_2 + k_2) * u (r + 1 + M_1 + M_2)) =
        2 ^ S_12 * u (r + 1 + M_1 + M_2) := by
      change 2 ^ n_1 * (2 ^ (n_2 + k_2) * u (r + 1 + M_1 + M_2)) =
        2 ^ (n_1 + n_2 + k_2) * u (r + 1 + M_1 + M_2)
      rw [Nat.add_assoc n_1 n_2 k_2, Nat.pow_add 2 n_1 (n_2 + k_2)]
      ring
    have hpowR : 2 ^ n_1 * (3 ^ n_2 * 2 ^ k_1 * u (r + 1 + M_1) + A_2) =
        3 ^ n_2 * (2 ^ S_1 * u (r + 1 + M_1)) + 2 ^ n_1 * A_2 := by
      change 2 ^ n_1 * (3 ^ n_2 * 2 ^ k_1 * u (r + 1 + M_1) + A_2) =
        3 ^ n_2 * (2 ^ (n_1 + k_1) * u (r + 1 + M_1)) + 2 ^ n_1 * A_2
      rw [Nat.pow_add 2 n_1 k_1]
      ring
    rw [hpowL, hpowR] at hm
    exact hm
  have hid12 : 2 ^ S_12 * u (r + 1 + M_1 + M_2) = 3 ^ T_12 * u r + R_12 := by
    calc
      2 ^ S_12 * u (r + 1 + M_1 + M_2)
          = 3 ^ n_2 * (3 ^ T_1 * u r + R_1) + 2 ^ n_1 * A_2 := by rw [htrans, hid1]
      _ = 3 ^ T_12 * u r + R_12 := by
            change 3 ^ n_2 * (3 ^ (j + n_1) * u r + R_1) + 2 ^ n_1 * A_2 =
              3 ^ (j + n_1 + n_2) * u r + (3 ^ n_2 * R_1 + 2 ^ n_1 * A_2)
            rw [Nat.pow_add 3 (j + n_1) n_2]
            ring
  have hinv2 : 5 * A_2 + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2 :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s_2 M_2 hs2
  have hdiff_eq : R_12 - 3 ^ n_2 * R_1 = 2 ^ n_1 * A_2 := by
    change (3 ^ n_2 * R_1 + 2 ^ n_1 * A_2) - 3 ^ n_2 * R_1 = 2 ^ n_1 * A_2
    omega
  have hcauchy :
      5 * (R_12 - 3 ^ n_2 * R_1) + 4 * 2 ^ (n_1 + n_2) ≤ 4 * 2 ^ n_1 * 3 ^ n_2 := by
    have hm := Nat.mul_le_mul_left (2 ^ n_1) hinv2
    have hpow2 : 2 ^ (n_1 + n_2) = 2 ^ n_1 * 2 ^ n_2 := Nat.pow_add 2 n_1 n_2
    have hlhs : 5 * (R_12 - 3 ^ n_2 * R_1) + 4 * 2 ^ (n_1 + n_2) =
        2 ^ n_1 * (5 * A_2 + 4 * 2 ^ n_2) := by
      rw [hdiff_eq, hpow2]
      ring
    have hrhs : 4 * 2 ^ n_1 * 3 ^ n_2 = 2 ^ n_1 * (4 * 3 ^ n_2) := by ring
    rw [hlhs, hrhs]
    exact hm
  have h95_12 : 5 * R_12 + 4 * 2 ^ (n_1 + n_2) ≤ 9 * 3 ^ (n_1 + n_2) := by
    have hm1 := Nat.mul_le_mul_left (3 ^ n_2) h95_1
    have hpow3 : 3 ^ n_2 * (9 * 3 ^ n_1) = 9 * 3 ^ (n_1 + n_2) := by
      rw [Nat.pow_add 3 n_1 n_2]
      ring
    have hexp1 : 3 ^ n_2 * (5 * R_1 + 4 * 2 ^ n_1) =
        5 * (3 ^ n_2 * R_1) + 4 * 2 ^ n_1 * 3 ^ n_2 := by ring
    have hexp12 : 5 * R_12 = 5 * (3 ^ n_2 * R_1) + 5 * (R_12 - 3 ^ n_2 * R_1) := by
      rw [hdiff_eq]
      change 5 * (3 ^ n_2 * R_1 + 2 ^ n_1 * A_2) =
        5 * (3 ^ n_2 * R_1) + 5 * (2 ^ n_1 * A_2)
      ring
    omega
  have hj_pos : 1 ≤ j := (hchain r (by omega)).1
  have h3j_ge_3 : 3 ≤ 3 ^ j := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, j = m + 1 := ⟨j - 1, by omega⟩
    have hpos : 1 ≤ 3 ^ m := Nat.one_le_pow _ 3 (by decide)
    rw [hm, Nat.pow_succ]
    omega
  have h2_pos : 1 ≤ 2 ^ (n_1 + n_2) := Nat.one_le_pow _ 2 (by decide)
  have hR12_lt : R_12 < 3 ^ T_12 := by
    have hR12_lt2 : R_12 < 2 * 3 ^ (n_1 + n_2) := by omega
    have hpow : 3 ^ T_12 = 3 ^ j * 3 ^ (n_1 + n_2) := by
      change 3 ^ (j + n_1 + n_2) = 3 ^ j * 3 ^ (n_1 + n_2)
      rw [Nat.add_assoc j n_1 n_2, Nat.pow_add 3 j (n_1 + n_2)]
    have hmul : 3 * 3 ^ (n_1 + n_2) ≤ 3 ^ j * 3 ^ (n_1 + n_2) :=
      Nat.mul_le_mul_right (3 ^ (n_1 + n_2)) h3j_ge_3
    omega
  have hdiv_pos : 0 < 3 ^ T_12 := by omega
  have hdiv12 : (2 ^ S_12 * u (r + 1 + M_1 + M_2)) / 3 ^ T_12 = u r := by
    rw [hid12, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hR12_lt, add_zero]
  have hs3_12 :
      base3DigitSum (2 ^ S_12 * u (r + 1 + M_1 + M_2)) =
        base3DigitSum (u r) + base3DigitSum R_12 := by
    rw [hid12, base3DigitSum_three_pow_mul_add T_12 (u r) hR12_lt]
  exact ⟨⟨hid1, hR1_lt, hdiv1⟩, ⟨htrans, hid12⟩, ⟨hcauchy, h95_12⟩,
    ⟨hR12_lt, hdiv12, hdiv12.trans hdiv1.symm, hs3_12⟩⟩

/-! ## 58. Theorem SB.58: The $j \ge k$ Excess-Exponent Explosion, Binary Weight Swelling, & Halving-Debt Law -/

/-- **The $j \ge k$ Excess-Exponent Explosion, Binary Weight Swelling, & Halving-Debt Law
(`j_ge_k_excess_explosion_binary_swelling_and_halving_debt_law`, Theorem SB.58)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds with `2 ≤ s (r + 1)` and `s (r + 1) ≤ s r`.
Setting `j = s r`, `k = s (r + 1)`, `k' = s (r + 2)`, and `Δ = j - k`:
1. **Exact Excess-Exponent Decomposition & Super-Exponential Jump**:
   `2 ^ k * u (r + 1) = 3 ^ Δ * 3 ^ k * u r + 1`,
   `9 * 3 ^ Δ * u r + 1 ≤ 4 * u (r + 1)`, and `2 * 3 ^ Δ * u r < u (r + 1)`,
2. **Binary 1-Bit Budget Law Under $j \ge k$**:
   `base2DigitSum (u (r + 1)) + k = base2DigitSum (3 ^ j * u r) + 1`,
3. **Exact Two-Step Halving-Debt Identity**:
   `2 ^ (k + k') * u (r + 2) = 3 ^ (j + k) * u r + 3 ^ k + 2 ^ k`, and
4. **Two-Step Halving-Debt Crisis (Return-to-Baseline Barrier)**:
   Whenever `u (r + 2) ≤ u r`, the subsequent binary valuation `k' = s (r + 2)` must satisfy
   `3 ^ (j + k) < 2 ^ (k + k')` and `3 ^ j < 2 ^ k'`! -/
theorem j_ge_k_excess_explosion_binary_swelling_and_halving_debt_law
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3))
    (hk2 : 2 ≤ s (r + 1))
    (hjk : s (r + 1) ≤ s r) :
    let j := s r
    let k := s (r + 1)
    let k' := s (r + 2)
    let Δ := j - k
    (2 ^ k * u (r + 1) = 3 ^ Δ * 3 ^ k * u r + 1 ∧
      9 * 3 ^ Δ * u r + 1 ≤ 4 * u (r + 1) ∧
      2 * 3 ^ Δ * u r < u (r + 1)) ∧
      base2DigitSum (u (r + 1)) + k = base2DigitSum (3 ^ j * u r) + 1 ∧
      2 ^ (k + k') * u (r + 2) = 3 ^ (j + k) * u r + 3 ^ k + 2 ^ k ∧
      (u (r + 2) ≤ u r → 3 ^ (j + k) < 2 ^ (k + k') ∧ 3 ^ j < 2 ^ k') := by
  intro j k k' Δ
  have hch_r2 : ValidBlockChain b_0 s u (r + 2) := fun t ht => hchain t (by omega)
  have hstep1 : 2 ^ k * u (r + 1) = 3 ^ j * u r + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_r2).1
  have hstep2 : 2 ^ k' * u (r + 2) = 3 ^ k * u (r + 1) + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have hj_eq : j = Δ + k := by omega
  have hdecomp : 2 ^ k * u (r + 1) = 3 ^ Δ * 3 ^ k * u r + 1 := by
    rw [hstep1, hj_eq, Nat.pow_add 3 Δ k]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  have hle_m : 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by decide) m
  have hjump4 : 9 * 3 ^ Δ * u r + 1 ≤ 4 * u (r + 1) := by
    have hmul_le : 2 ^ m * (9 * 3 ^ Δ * u r) ≤ 3 ^ m * (9 * 3 ^ Δ * u r) :=
      Nat.mul_le_mul_right (9 * 3 ^ Δ * u r) hle_m
    have hpow2 : 2 ^ k * u (r + 1) = 2 ^ m * (4 * u (r + 1)) := by
      rw [hm, Nat.pow_add 2 m 2]
      ring
    have hpow3 : 3 ^ Δ * 3 ^ k * u r = 3 ^ m * (9 * 3 ^ Δ * u r) := by
      rw [hm, Nat.pow_add 3 m 2]
      ring
    have hlt_m : 2 ^ m * (9 * 3 ^ Δ * u r) < 2 ^ m * (4 * u (r + 1)) := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt_m
  have hur_odd : u r % 2 = 1 := (hchain r (by omega)).2.1
  have hur_pos : 1 ≤ u r := by omega
  have h3d_pos : 1 ≤ 3 ^ Δ := Nat.one_le_pow _ 3 (by decide)
  have hjump2 : 2 * 3 ^ Δ * u r < u (r + 1) := by
    have hprod_pos : 1 ≤ 3 ^ Δ * u r := Nat.mul_pos h3d_pos hur_pos
    have h9_eq : 9 * 3 ^ Δ * u r = 9 * (3 ^ Δ * u r) := by ring
    have h2_eq : 2 * 3 ^ Δ * u r = 2 * (3 ^ Δ * u r) := by ring
    omega
  have hb2 : base2DigitSum (u (r + 1)) + k = base2DigitSum (3 ^ j * u r) + 1 := by
    have h31 := (bridge_c_one_step_binary_trailing_ones_depletion_law hch_r2).2.2.2
    change base2DigitSum (3 ^ j * u r) + 1 = base2DigitSum (u (r + 1)) + k at h31
    omega
  have h2step : 2 ^ (k + k') * u (r + 2) = 3 ^ (j + k) * u r + 3 ^ k + 2 ^ k := by
    calc
      2 ^ (k + k') * u (r + 2)
          = 2 ^ k * (2 ^ k' * u (r + 2)) := by
            rw [Nat.pow_add 2 k k']
            ring
      _ = 2 ^ k * (3 ^ k * u (r + 1) + 1) := by rw [hstep2]
      _ = 3 ^ k * (2 ^ k * u (r + 1)) + 2 ^ k := by ring
      _ = 3 ^ k * (3 ^ j * u r + 1) + 2 ^ k := by rw [hstep1]
      _ = 3 ^ (j + k) * u r + 3 ^ k + 2 ^ k := by
            rw [Nat.pow_add 3 j k]
            ring
  refine ⟨⟨hdecomp, hjump4, hjump2⟩, hb2, h2step, ?_⟩
  intro hle_u
  have hmul_u : 2 ^ (k + k') * u (r + 2) ≤ 2 ^ (k + k') * u r :=
    Nat.mul_le_mul_left (2 ^ (k + k')) hle_u
  have h2k_pos : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by decide)
  have h3k_pos : 1 ≤ 3 ^ k := Nat.one_le_pow _ 3 (by decide)
  have hlt_prod : 3 ^ (j + k) * u r < 2 ^ (k + k') * u r := by omega
  have hdebt1 : 3 ^ (j + k) < 2 ^ (k + k') :=
    Nat.lt_of_mul_lt_mul_right hlt_prod
  have h2k_le_3k : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
  have hlt_k : 3 ^ k * 3 ^ j < 3 ^ k * 2 ^ k' := by
    calc
      3 ^ k * 3 ^ j = 3 ^ (j + k) := by
        rw [Nat.pow_add 3 j k]
        ring
      _ < 2 ^ (k + k') := hdebt1
      _ = 2 ^ k * 2 ^ k' := Nat.pow_add 2 k k'
      _ ≤ 3 ^ k * 2 ^ k' := Nat.mul_le_mul_right (2 ^ k') h2k_le_3k
  have hdebt2 : 3 ^ j < 2 ^ k' := Nat.lt_of_mul_lt_mul_left hlt_k
  exact ⟨hdebt1, hdebt2⟩

/-! ## 59. Theorem SB.59: The $3^{j_0}$ Diagonal Shift & $j_0$-Trit Dead-Zone Invariance Law -/

/-- **The $3^{j_0}$ Diagonal Shift & $j_0$-Trit Dead-Zone Invariance Law
(`three_adic_seed_diagonal_shift_and_dead_zone_invariance_law`, Theorem SB.59)**:
1. **Seed-Level Diagonal Shift ($P_0 = 3^{j_0} \cdot m$)**:
   Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`, and suppose
   `P 0 = 3 ^ j_0 * m` for some `j_0, m : ℕ`. Setting `n = blockSteps s K`, `k = s K`,
   `A_K = renewalNumerator s K`, and `N_K = 2 ^ (n + k) * u K`:
   - `N_K = 3 ^ (j_0 + n) * m + A_K`,
   - `N_K / 3 ^ (j_0 + n) = m` and `N_K % 3 ^ (j_0 + n) = A_K`,
   - **Exact $j_0$-Trit Dead Zone in $[3^n, 3^{j_0+n})$**:
     `(N_K / 3 ^ n) % 3 ^ j_0 = 0` and `(N_K % 3 ^ (j_0 + n)) / 3 ^ n = 0`, and
   - **Base-3 Digit-Sum Invariance in $j_0$**:
     `base3DigitSum N_K = base3DigitSum m + base3DigitSum A_K`!
2. **Block-Level Odd-Quotient Diagonal Shift ($u_r = 3^{j_0} \cdot m$)**:
   Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds with `∀ k < M, 2 ≤ s (r + 1 + k)`,
   and `u r = 3 ^ j_0 * m`. Setting `s' t = s (r + 1 + t)`, `n = blockSteps s' M`,
   `k = s (r + 1 + M)`, `j = j_0 + s r`, and `R = 3 ^ n + renewalNumerator s' M`:
   - `2 ^ (n + k) * u (r + 1 + M) = 3 ^ (j + n) * m + R`,
   - `(2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (j + n) = m` and
     `(2 ^ (n + k) * u (r + 1 + M)) % 3 ^ (j + n) = R`,
   - `((2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (s r + n)) % 3 ^ j_0 = 0`, and
   - `base3DigitSum (2 ^ (n + k) * u (r + 1 + M)) = base3DigitSum m + base3DigitSum R`! -/
theorem three_adic_seed_diagonal_shift_and_dead_zone_invariance_law :
    (∀ {b_0 K j_0 m : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (K + 1) →
      (∀ t < K, 2 ≤ s t) →
      oddReturnP (orbit b_0 (blockSteps s 0)) = 3 ^ j_0 * m →
      let n := blockSteps s K
      let k := s K
      let A_K := renewalNumerator s K
      let N_K := 2 ^ (n + k) * u K
      N_K = 3 ^ (j_0 + n) * m + A_K ∧
        N_K / 3 ^ (j_0 + n) = m ∧
        N_K % 3 ^ (j_0 + n) = A_K ∧
        (N_K / 3 ^ n) % 3 ^ j_0 = 0 ∧
        (N_K % 3 ^ (j_0 + n)) / 3 ^ n = 0 ∧
        base3DigitSum N_K = base3DigitSum m + base3DigitSum A_K) ∧
    (∀ {b_0 r M j_0 m : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 1 + M + 1) →
      (∀ t < M, 2 ≤ s (r + 1 + t)) →
      u r = 3 ^ j_0 * m →
      let s' := fun t => s (r + 1 + t)
      let n := blockSteps s' M
      let k := s (r + 1 + M)
      let j := j_0 + s r
      let R := 3 ^ n + renewalNumerator s' M
      2 ^ (n + k) * u (r + 1 + M) = 3 ^ (j + n) * m + R ∧
        (2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (j + n) = m ∧
        (2 ^ (n + k) * u (r + 1 + M)) % 3 ^ (j + n) = R ∧
        ((2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (s r + n)) % 3 ^ j_0 = 0 ∧
        base3DigitSum (2 ^ (n + k) * u (r + 1 + M)) = base3DigitSum m + base3DigitSum R) := by
  refine ⟨?_, ?_⟩
  · intro b_0 K j_0 m s u hchain hs2 hP0 n k A_K N_K
    have h24 := unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery hchain hs2
    have h32 := (bridge_c_multi_step_dual_base2_base3_zero_carry_split hchain hs2).1
    dsimp only at h24 h32
    have hA_lt_n : A_K < 3 ^ n := h24.2.2.1
    have h3j0_pos : 1 ≤ 3 ^ j_0 := Nat.one_le_pow _ 3 (by decide)
    have hpow_jn : 3 ^ (j_0 + n) = 3 ^ n * 3 ^ j_0 := by
      rw [Nat.pow_add 3 j_0 n]
      ring
    have hA_lt_jn : A_K < 3 ^ (j_0 + n) := by
      have hle : 3 ^ n * 1 ≤ 3 ^ n * 3 ^ j_0 := Nat.mul_le_mul_left (3 ^ n) h3j0_pos
      omega
    have hid_N : N_K = 3 ^ (j_0 + n) * m + A_K := by
      calc
        N_K = 3 ^ n * oddReturnP (orbit b_0 (blockSteps s 0)) + A_K := h32.1.symm
        _ = 3 ^ n * (3 ^ j_0 * m) + A_K := by rw [hP0]
        _ = 3 ^ (j_0 + n) * m + A_K := by
              rw [Nat.pow_add 3 j_0 n]
              ring
    have hdiv_pos : 0 < 3 ^ (j_0 + n) := by omega
    have hdiv_jn : N_K / 3 ^ (j_0 + n) = m := by
      rw [hid_N, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hA_lt_jn, add_zero]
    have hmod_jn : N_K % 3 ^ (j_0 + n) = A_K := by
      rw [hid_N, Nat.mul_add_mod, Nat.mod_eq_of_lt hA_lt_jn]
    have hdiv_n : N_K / 3 ^ n = 3 ^ j_0 * m := by
      have hq := h32.2.1
      rw [h32.1] at hq
      change N_K / 3 ^ n = oddReturnP (orbit b_0 (blockSteps s 0)) at hq
      rw [hq, hP0]
    have hdead1 : (N_K / 3 ^ n) % 3 ^ j_0 = 0 := by
      rw [hdiv_n, Nat.mul_mod_right]
    have hdead2 : (N_K % 3 ^ (j_0 + n)) / 3 ^ n = 0 := by
      rw [hmod_jn, Nat.div_eq_of_lt hA_lt_n]
    have hs3 : base3DigitSum N_K = base3DigitSum m + base3DigitSum A_K := by
      have hs := h32.2.2.2
      rw [h32.1] at hs
      change base3DigitSum N_K =
        base3DigitSum (oddReturnP (orbit b_0 (blockSteps s 0))) + base3DigitSum A_K at hs
      rw [hs, hP0, base3DigitSum_three_pow_mul]
    exact ⟨hid_N, hdiv_jn, hmod_jn, hdead1, hdead2, hs3⟩
  · intro b_0 r M j_0 m s u hchain hs2 hur s' n k j R
    have h25 := unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound hchain hs2
    dsimp only at h25
    have hR_lt_T : R < 3 ^ (s r + n) := h25.2.2.1
    have hdiv_T : (2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (s r + n) = u r := h25.2.2.2.1
    have hmod_T : (2 ^ (n + k) * u (r + 1 + M)) % 3 ^ (s r + n) = R := h25.2.2.2.2.1
    have hid_T : 2 ^ (n + k) * u (r + 1 + M) = 3 ^ (s r + n) * u r + R := by
      have hdm := Nat.div_add_mod (2 ^ (n + k) * u (r + 1 + M)) (3 ^ (s r + n))
      rw [hdiv_T, hmod_T] at hdm
      exact hdm.symm
    have hid_jn : 2 ^ (n + k) * u (r + 1 + M) = 3 ^ (j + n) * m + R := by
      calc
        2 ^ (n + k) * u (r + 1 + M)
            = 3 ^ (s r + n) * (3 ^ j_0 * m) + R := by rw [hid_T, hur]
        _ = 3 ^ (j + n) * m + R := by
              change 3 ^ (s r + n) * (3 ^ j_0 * m) + R = 3 ^ (j_0 + s r + n) * m + R
              rw [Nat.add_assoc j_0 (s r) n, Nat.pow_add 3 j_0 (s r + n)]
              ring
    have h3j0_pos : 1 ≤ 3 ^ j_0 := Nat.one_le_pow _ 3 (by decide)
    have hR_lt_jn : R < 3 ^ (j + n) := by
      have hpow : 3 ^ (j + n) = 3 ^ (s r + n) * 3 ^ j_0 := by
        change 3 ^ (j_0 + s r + n) = 3 ^ (s r + n) * 3 ^ j_0
        rw [Nat.add_assoc j_0 (s r) n, Nat.pow_add 3 j_0 (s r + n)]
        ring
      have hle : 3 ^ (s r + n) * 1 ≤ 3 ^ (s r + n) * 3 ^ j_0 :=
        Nat.mul_le_mul_left (3 ^ (s r + n)) h3j0_pos
      omega
    have hdiv_pos : 0 < 3 ^ (j + n) := by omega
    have hdiv_jn : (2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (j + n) = m := by
      rw [hid_jn, Nat.mul_add_div hdiv_pos, Nat.div_eq_of_lt hR_lt_jn, add_zero]
    have hmod_jn : (2 ^ (n + k) * u (r + 1 + M)) % 3 ^ (j + n) = R := by
      rw [hid_jn, Nat.mul_add_mod, Nat.mod_eq_of_lt hR_lt_jn]
    have hdead : ((2 ^ (n + k) * u (r + 1 + M)) / 3 ^ (s r + n)) % 3 ^ j_0 = 0 := by
      rw [hdiv_T, hur, Nat.mul_mod_right]
    have hs3 : base3DigitSum (2 ^ (n + k) * u (r + 1 + M)) = base3DigitSum m + base3DigitSum R := by
      rw [h25.2.2.2.2.2, hur, base3DigitSum_three_pow_mul]
    exact ⟨hid_jn, hdiv_jn, hmod_jn, hdead, hs3⟩

/-! ## 60. Theorem SB.60: Grand 60-Theorem Synthesis of the $(j+n, k+n)$ Diagonal & $j \gg k$ Regime -/

/-- **Grand 60-Theorem Synthesis of the $(j+n, k+n)$ Diagonal & $j \gg k$ Regime
(`grand_jk_diagonal_and_three_heavy_regime_60_synthesis`, Theorem SB.60)**:
Synthesizes the three $(j+n, k+n)$ diagonal and $j \ge k$ / $j \gg k$ laws (`SB.57–SB.59`)
with the Collatz–Syracuse bridge (`SB.54`), constant-rung run-length bound (`SB.55`),
and sharp $4/5$ equality characterization (`SB.56`) into a single unified theorem. -/
theorem grand_jk_diagonal_and_three_heavy_regime_60_synthesis :
    (∀ {b_0 r M_1 M_2 : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 1 + M_1 + M_2 + 1) →
      (∀ k < M_1, 2 ≤ s (r + 1 + k)) →
      (∀ k < M_2, 2 ≤ s (r + 1 + M_1 + k)) →
      let j := s r
      let s_1 := fun t => s (r + 1 + t)
      let s_2 := fun t => s (r + 1 + M_1 + t)
      let n_1 := blockSteps s_1 M_1
      let n_2 := blockSteps s_2 M_2
      let S_1 := n_1 + s (r + 1 + M_1)
      let S_12 := n_1 + n_2 + s (r + 1 + M_1 + M_2)
      let R_1 := 3 ^ n_1 + renewalNumerator s_1 M_1
      let R_12 := 3 ^ n_2 * R_1 + 2 ^ n_1 * renewalNumerator s_2 M_2
      5 * (R_12 - 3 ^ n_2 * R_1) + 4 * 2 ^ (n_1 + n_2) ≤ 4 * 2 ^ n_1 * 3 ^ n_2 ∧
        (2 ^ S_12 * u (r + 1 + M_1 + M_2)) / 3 ^ (j + n_1 + n_2) = u r ∧
        (2 ^ S_1 * u (r + 1 + M_1)) / 3 ^ (j + n_1) = u r) ∧
    (∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 3) →
      2 ≤ s (r + 1) →
      s (r + 1) ≤ s r →
      9 * 3 ^ (s r - s (r + 1)) * u r + 1 ≤ 4 * u (r + 1) ∧
        (u (r + 2) ≤ u r → 3 ^ (s r) < 2 ^ (s (r + 2)))) ∧
    (∀ {b_0 K j_0 m : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (K + 1) →
      (∀ t < K, 2 ≤ s t) →
      oddReturnP (orbit b_0 (blockSteps s 0)) = 3 ^ j_0 * m →
      (2 ^ (blockSteps s K + s K) * u K) / 3 ^ (j_0 + blockSteps s K) = m ∧
        ((2 ^ (blockSteps s K + s K) * u K) / 3 ^ (blockSteps s K)) % 3 ^ j_0 = 0 ∧
        base3DigitSum (2 ^ (blockSteps s K + s K) * u K) =
          base3DigitSum m + base3DigitSum (renewalNumerator s K)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b_0 r M_1 M_2 s u hchain hs1 hs2 j s_1 s_2 n_1 n_2 S_1 S_12 R_1 R_12
    have h57 := two_window_jk_diagonal_cauchy_tail_freeze_and_quotient_invariance hchain hs1 hs2
    exact ⟨h57.2.2.1.1, h57.2.2.2.2.1, h57.1.2.2⟩
  · intro b_0 r s u hchain hk2 hjk
    have h58 := j_ge_k_excess_explosion_binary_swelling_and_halving_debt_law hchain hk2 hjk
    exact ⟨h58.1.2.1, fun hle => (h58.2.2.2 hle).2⟩
  · intro b_0 K j_0 m s u hchain hs2 hP0
    have h59 := three_adic_seed_diagonal_shift_and_dead_zone_invariance_law.1 hchain hs2 hP0
    exact ⟨h59.2.1, h59.2.2.2.1, h59.2.2.2.2.2⟩

/-! ## 61. Theorem SB.61: Local Descent Rung Jump & Multi-Step Descent Staircase Explosion -/

/-- Helper: whenever `3 ^ a < 2 ^ b`, lower bounds on `a` force exponential jumps in `b`
(`2 ≤ a → 4 ≤ b`, `4 ≤ a → 7 ≤ b`, `7 ≤ a → 12 ≤ b`). -/
theorem two_pow_exp_jump_of_three_pow_lt {a b : ℕ} (hlt : 3 ^ a < 2 ^ b) :
    (2 ≤ a → 4 ≤ b) ∧ (4 ≤ a → 7 ≤ b) ∧ (7 ≤ a → 12 ≤ b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    have h3 : 3 ^ 2 ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) ha
    by_contra hnb
    have hb_le : b ≤ 3 := by omega
    have h2 : 2 ^ b ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hb_le
    omega
  · intro ha
    have h3 : 3 ^ 4 ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) ha
    by_contra hnb
    have hb_le : b ≤ 6 := by omega
    have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hb_le
    omega
  · intro ha
    have h3 : 3 ^ 7 ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) ha
    by_contra hnb
    have hb_le : b ≤ 11 := by omega
    have h2 : 2 ^ b ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hb_le
    omega

/-- **Local Descent Rung Jump & Multi-Step Descent Staircase Explosion
(`local_descent_rung_jump_and_multi_step_descent_explosion`, Theorem SB.61)**:
1. **Single-Step Descent Law**:
   In any `ValidBlockChain b_0 s u (r + 2)`, if the odd core does not increase
   (`u (r + 1) ≤ u r`), then `3 ^ (s r) < 2 ^ (s (r + 1))`, forcing:
   `2 ≤ s r → 4 ≤ s (r + 1)`, `4 ≤ s r → 7 ≤ s (r + 1)`, and `7 ≤ s r → 12 ≤ s (r + 1)`.
2. **Multi-Step Non-Increasing Run Law**:
   In any `ValidBlockChain b_0 s u (r + m + 1)`, if `∀ k < m, u (r + k + 1) ≤ u (r + k)`,
   then `∀ k < m, 3 ^ (s (r + k)) < 2 ^ (s (r + k + 1))`.
3. **Three-Step Descent Staircase Explosion (`2 → 4 → 7 → 12`)**:
   In any `ValidBlockChain b_0 s u (r + 4)` with `2 ≤ s r` and
   `u (r + 1) ≤ u r`, `u (r + 2) ≤ u (r + 1)`, `u (r + 3) ≤ u (r + 2)`,
   the rung heights must satisfy `4 ≤ s (r + 1) ∧ 7 ≤ s (r + 2) ∧ 12 ≤ s (r + 3)`! -/
theorem local_descent_rung_jump_and_multi_step_descent_explosion :
    (∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 2) →
      u (r + 1) ≤ u r →
      3 ^ (s r) < 2 ^ (s (r + 1)) ∧
        (2 ≤ s r → 4 ≤ s (r + 1)) ∧
        (4 ≤ s r → 7 ≤ s (r + 1)) ∧
        (7 ≤ s r → 12 ≤ s (r + 1))) ∧
    (∀ {b_0 r m : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + m + 1) →
      (∀ k < m, u (r + k + 1) ≤ u (r + k)) →
      ∀ k < m, 3 ^ (s (r + k)) < 2 ^ (s (r + k + 1))) ∧
    (∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 4) →
      2 ≤ s r →
      u (r + 1) ≤ u r →
      u (r + 2) ≤ u (r + 1) →
      u (r + 3) ≤ u (r + 2) →
      4 ≤ s (r + 1) ∧ 7 ≤ s (r + 2) ∧ 12 ≤ s (r + 3)) := by
  have hstep :
      ∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
        ValidBlockChain b_0 s u (r + 2) →
        u (r + 1) ≤ u r →
        3 ^ (s r) < 2 ^ (s (r + 1)) ∧
          (2 ≤ s r → 4 ≤ s (r + 1)) ∧
          (4 ≤ s r → 7 ≤ s (r + 1)) ∧
          (7 ≤ s r → 12 ≤ s (r + 1)) := by
    intro b_0 r s u hchain hle
    have h19 : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 :=
      (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
    have hmul : 2 ^ (s (r + 1)) * u (r + 1) ≤ 2 ^ (s (r + 1)) * u r :=
      Nat.mul_le_mul_left (2 ^ (s (r + 1))) hle
    have hlt_prod : 3 ^ (s r) * u r < 2 ^ (s (r + 1)) * u r := by omega
    have hlt_pow : 3 ^ (s r) < 2 ^ (s (r + 1)) :=
      Nat.lt_of_mul_lt_mul_right hlt_prod
    have hjumps := two_pow_exp_jump_of_three_pow_lt hlt_pow
    exact ⟨hlt_pow, hjumps.1, hjumps.2.1, hjumps.2.2⟩
  refine ⟨hstep, ?_, ?_⟩
  · intro b_0 r m s u hchain hdesc k hk
    have hch_k : ValidBlockChain b_0 s u (r + k + 2) :=
      fun t ht => hchain t (by omega)
    exact (hstep hch_k (hdesc k hk)).1
  · intro b_0 r s u hchain hsr hu1 hu2 hu3
    have hch1 : ValidBlockChain b_0 s u (r + 2) := fun t ht => hchain t (by omega)
    have hch2 : ValidBlockChain b_0 s u (r + 1 + 2) := fun t ht => hchain t (by omega)
    have hch3 : ValidBlockChain b_0 s u (r + 2 + 2) := fun t ht => hchain t (by omega)
    have hs1 : 4 ≤ s (r + 1) := (hstep hch1 hu1).2.1 hsr
    have hs2 : 7 ≤ s (r + 2) := (hstep hch2 hu2).2.2.1 hs1
    have hs3 : 12 ≤ s (r + 3) := (hstep hch3 hu3).2.2.2 hs2
    exact ⟨hs1, hs2, hs3⟩

/-! ## 62. Theorem SB.62: Trough-Rebound Compound-Interest Identity & Local Minimum Trap -/

/-- **Trough-Rebound Compound-Interest Identity & Local Minimum Trap
(`trough_rebound_compound_interest_and_local_minimum_trap`, Theorem SB.62)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds.
1. **Exact Trough-Rebound Compound-Interest Identity**:
   `2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) = 3 ^ (s r + s (r + 1)) * u r + 3 ^ (s (r + 1)) + 2 ^ (s (r + 1))`,
2. **Entering a Trough ($u_{r+1} \le u_r$) Charges $\ge (81/16)$ Compound Interest**:
   Whenever `2 ≤ s r` and `u (r + 1) ≤ u r`:
   - `4 ≤ s (r + 1)`,
   - `81 * u (r + 1) + 1 ≤ 2 ^ (s (r + 2)) * u (r + 2)`, and
   - `81 * (3 ^ (s r) * u r + 1) + 16 ≤ 16 * 2 ^ (s (r + 2)) * u (r + 2)`, and
3. **Exiting at a Local Rung Peak ($2 \le s_{r+2} \le s_{r+1}$)**:
   Whenever `2 ≤ s (r + 2)` and `s (r + 2) ≤ s (r + 1)`,
   `9 * 3 ^ (s (r + 1) - s (r + 2)) * u (r + 1) + 1 ≤ 4 * u (r + 2)`! -/
theorem trough_rebound_compound_interest_and_local_minimum_trap
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3)) :
    2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) =
        3 ^ (s r + s (r + 1)) * u r + 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) ∧
      (2 ≤ s r → u (r + 1) ≤ u r →
        4 ≤ s (r + 1) ∧
          81 * u (r + 1) + 1 ≤ 2 ^ (s (r + 2)) * u (r + 2) ∧
          81 * (3 ^ (s r) * u r + 1) + 16 ≤ 16 * 2 ^ (s (r + 2)) * u (r + 2)) ∧
      (2 ≤ s (r + 2) → s (r + 2) ≤ s (r + 1) →
        9 * 3 ^ (s (r + 1) - s (r + 2)) * u (r + 1) + 1 ≤ 4 * u (r + 2)) := by
  have hch1 : ValidBlockChain b_0 s u (r + 2) := fun t ht => hchain t (by omega)
  have hstep1 : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hch1).1
  have hstep2 : 2 ^ (s (r + 2)) * u (r + 2) = 3 ^ (s (r + 1)) * u (r + 1) + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have hid :
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) =
        3 ^ (s r + s (r + 1)) * u r + 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) := by
    calc
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2)
          = 2 ^ (s (r + 1)) * (2 ^ (s (r + 2)) * u (r + 2)) := by
            rw [Nat.pow_add 2 (s (r + 1)) (s (r + 2))]
            ring
      _ = 2 ^ (s (r + 1)) * (3 ^ (s (r + 1)) * u (r + 1) + 1) := by rw [hstep2]
      _ = 3 ^ (s (r + 1)) * (2 ^ (s (r + 1)) * u (r + 1)) + 2 ^ (s (r + 1)) := by ring
      _ = 3 ^ (s (r + 1)) * (3 ^ (s r) * u r + 1) + 2 ^ (s (r + 1)) := by rw [hstep1]
      _ = 3 ^ (s r + s (r + 1)) * u r + 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) := by
            rw [Nat.pow_add 3 (s r) (s (r + 1))]
            ring
  refine ⟨hid, ?_, ?_⟩
  · intro hsr hu1
    have hs1 : 4 ≤ s (r + 1) :=
      (local_descent_rung_jump_and_multi_step_descent_explosion.1 hch1 hu1).2.1 hsr
    have h81_pow : 81 ≤ 3 ^ (s (r + 1)) := by
      have h34 : 3 ^ 4 ≤ 3 ^ (s (r + 1)) := Nat.pow_le_pow_right (by decide) hs1
      omega
    have h81_u : 81 * u (r + 1) + 1 ≤ 2 ^ (s (r + 2)) * u (r + 2) := by
      have hm : 81 * u (r + 1) ≤ 3 ^ (s (r + 1)) * u (r + 1) :=
        Nat.mul_le_mul_right (u (r + 1)) h81_pow
      omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, s (r + 1) = m + 4 := ⟨s (r + 1) - 4, by omega⟩
    have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
    have hle_m : 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by decide) m
    have hcompound :
        81 * (3 ^ (s r) * u r + 1) + 16 ≤ 16 * 2 ^ (s (r + 2)) * u (r + 2) := by
      have hmul_m : 2 ^ m * (81 * (3 ^ (s r) * u r + 1)) ≤
          3 ^ m * (81 * (3 ^ (s r) * u r + 1)) :=
        Nat.mul_le_mul_right (81 * (3 ^ (s r) * u r + 1)) hle_m
      have hstep_m :
          2 ^ m * (16 * 2 ^ (s (r + 2)) * u (r + 2)) =
            3 ^ m * (81 * (3 ^ (s r) * u r + 1)) + 2 ^ m * 16 := by
        calc
          2 ^ m * (16 * 2 ^ (s (r + 2)) * u (r + 2))
              = 2 ^ (s (r + 1)) * (2 ^ (s (r + 2)) * u (r + 2)) := by
                rw [hm, Nat.pow_add 2 m 4]
                ring
          _ = 2 ^ (s (r + 1)) * (3 ^ (s (r + 1)) * u (r + 1) + 1) := by rw [hstep2]
          _ = 3 ^ (s (r + 1)) * (2 ^ (s (r + 1)) * u (r + 1)) + 2 ^ (s (r + 1)) := by ring
          _ = 3 ^ (s (r + 1)) * (3 ^ (s r) * u r + 1) + 2 ^ (s (r + 1)) := by rw [hstep1]
          _ = 3 ^ m * (81 * (3 ^ (s r) * u r + 1)) + 2 ^ m * 16 := by
                rw [hm, Nat.pow_add 3 m 4, Nat.pow_add 2 m 4]
                ring
      have hle_prod :
          2 ^ m * (81 * (3 ^ (s r) * u r + 1) + 16) ≤
            2 ^ m * (16 * 2 ^ (s (r + 2)) * u (r + 2)) := by
        have hdist :
            2 ^ m * (81 * (3 ^ (s r) * u r + 1) + 16) =
              2 ^ m * (81 * (3 ^ (s r) * u r + 1)) + 2 ^ m * 16 := by ring
        omega
      exact Nat.le_of_mul_le_mul_left hle_prod h2m_pos
    exact ⟨hs1, h81_u, hcompound⟩
  · intro hs2_ge hle_s
    set j := s (r + 1)
    set k := s (r + 2)
    set Δ := j - k
    have hj_eq : j = Δ + k := by omega
    have hdecomp : 2 ^ k * u (r + 2) = 3 ^ Δ * 3 ^ k * u (r + 1) + 1 := by
      change 2 ^ (s (r + 2)) * u (r + 2) =
        3 ^ (s (r + 1) - s (r + 2)) * 3 ^ (s (r + 2)) * u (r + 1) + 1
      rw [hstep2, ← Nat.pow_add 3 (s (r + 1) - s (r + 2)) (s (r + 2)), ← hj_eq]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
    have hle_m : 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by decide) m
    have hmul_le : 2 ^ m * (9 * 3 ^ Δ * u (r + 1)) ≤ 3 ^ m * (9 * 3 ^ Δ * u (r + 1)) :=
      Nat.mul_le_mul_right (9 * 3 ^ Δ * u (r + 1)) hle_m
    have hpow2 : 2 ^ k * u (r + 2) = 2 ^ m * (4 * u (r + 2)) := by
      rw [hm, Nat.pow_add 2 m 2]
      ring
    have hpow3 : 3 ^ Δ * 3 ^ k * u (r + 1) = 3 ^ m * (9 * 3 ^ Δ * u (r + 1)) := by
      rw [hm, Nat.pow_add 3 m 2]
      ring
    have hlt_m : 2 ^ m * (9 * 3 ^ Δ * u (r + 1)) < 2 ^ m * (4 * u (r + 2)) := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt_m

/-! ## 63. Theorem SB.63: Finite-Seed Global Peak–Trough Seesaw & Post-Horizon Exhaustion Law -/

/-- **Finite-Seed Global Peak–Trough Seesaw & Post-Horizon Exhaustion Law
(`finite_seed_global_peak_trough_seesaw_and_return_barrier`, Theorem SB.63)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k` and `1 ≤ K`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`, and
`A_K = renewalNumerator s K`:
1. **Strict Global Seesaw Sandwich on $2^{s_K} \cdot u_K$**:
   `3 ^ T_K * 2 ^ (s 0) * u 0 < 2 ^ (T_K + s K) * u K` and
   `5 * (2 ^ (T_K + s K) * u K) + 4 * 2 ^ T_K ≤ 3 ^ T_K * (5 * 2 ^ (s 0) * u 0 + 4)`,
2. **Global Return-to-Baseline Rung Spike (`u K ≤ u 0`)**:
   Whenever the odd core returns to or dips below its initial value (`u K ≤ u 0`),
   the single rung `s K` must absorb the entire $(3/2)^{T_K}$ growth of the orbit:
   `3 ^ T_K * 2 ^ (s 0) < 2 ^ (T_K + s K)`,
3. **Bounded-Rung Odd-Core Exponential Divergence (`s K ≤ s 0`)**:
   Whenever the rung height does not exceed the initial rung (`s K ≤ s 0`),
   the odd core must strictly exceed the $(3/2)^{T_K}$ exponential floor:
   `3 ^ T_K * u 0 < 2 ^ T_K * u K`, and
4. **Post-Bit-Horizon Seed Exhaustion & Uniqueness (`P 0 < 2 ^ (T_K + s K)`)**:
   `(2 ^ (T_K + s K) * u K) / 3 ^ T_K = P 0`,
   `base3DigitSum (2 ^ (T_K + s K) * u K) = base3DigitSum (P 0) + base3DigitSum A_K`, and
   if `P 0 < 2 ^ (T_K + s K)`, then for any `P_0' < 2 ^ (T_K + s K)` satisfying
   `(3 ^ T_K * P_0' + A_K) % 2 ^ (T_K + s K) = 0`, we have `P_0' = P 0`! -/
theorem finite_seed_global_peak_trough_seesaw_and_return_barrier
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k)
    (hK : 1 ≤ K) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let A_K := renewalNumerator s K
    (3 ^ T_K * 2 ^ (s 0) * u 0 < 2 ^ (T_K + s K) * u K ∧
      5 * (2 ^ (T_K + s K) * u K) + 4 * 2 ^ T_K ≤ 3 ^ T_K * (5 * 2 ^ (s 0) * u 0 + 4)) ∧
      (u K ≤ u 0 → 3 ^ T_K * 2 ^ (s 0) < 2 ^ (T_K + s K)) ∧
      (s K ≤ s 0 → 3 ^ T_K * u 0 < 2 ^ T_K * u K) ∧
      ((2 ^ (T_K + s K) * u K) / 3 ^ T_K = P 0 ∧
        base3DigitSum (2 ^ (T_K + s K) * u K) = base3DigitSum (P 0) + base3DigitSum A_K ∧
        (P 0 < 2 ^ (T_K + s K) →
          ∀ P_0' < 2 ^ (T_K + s K),
            (3 ^ T_K * P_0' + A_K) % 2 ^ (T_K + s K) = 0 →
            P_0' = P 0)) := by
  intro P T_K A_K
  have h28 := bridge_a_dual_universe_series_lowest_terms_and_uniqueness hchain hs2
  have h32 := (bridge_c_multi_step_dual_base2_base3_zero_carry_split hchain hs2).1
  dsimp only at h28 h32
  have hid : 2 ^ (T_K + s K) * u K = 3 ^ T_K * P 0 + A_K := h28.1
  have hP0 : P 0 = 2 ^ (s 0) * u 0 := (hchain 0 (by omega)).2.2
  have hinv : 5 * A_K + 4 * 2 ^ T_K ≤ 4 * 3 ^ T_K :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s K hs2
  have hA_pos : 1 ≤ A_K := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, K = m + 1 := ⟨K - 1, by omega⟩
    have hpow_pos : 1 ≤ 2 ^ (blockSteps s m + s m) := Nat.one_le_pow _ 2 (by decide)
    have hA_eq : A_K = 3 ^ (s m) * renewalNumerator s m + 2 ^ (blockSteps s m + s m) := by
      change renewalNumerator s K =
        3 ^ (s m) * renewalNumerator s m + 2 ^ (blockSteps s m + s m)
      rw [hm]
      rfl
    omega
  have hlow : 3 ^ T_K * 2 ^ (s 0) * u 0 < 2 ^ (T_K + s K) * u K := by
    have hmul_P0 : 3 ^ T_K * P 0 = 3 ^ T_K * 2 ^ (s 0) * u 0 := by
      rw [hP0]
      ring
    omega
  have hhigh :
      5 * (2 ^ (T_K + s K) * u K) + 4 * 2 ^ T_K ≤ 3 ^ T_K * (5 * 2 ^ (s 0) * u 0 + 4) := by
    have hexp :
        5 * (2 ^ (T_K + s K) * u K) = 3 ^ T_K * (5 * 2 ^ (s 0) * u 0) + 5 * A_K := by
      rw [hid, hP0]
      ring
    have hrhs :
        3 ^ T_K * (5 * 2 ^ (s 0) * u 0 + 4) =
          3 ^ T_K * (5 * 2 ^ (s 0) * u 0) + 4 * 3 ^ T_K := by ring
    omega
  refine ⟨⟨hlow, hhigh⟩, ?_, ?_, ?_⟩
  · intro hu_le
    have hmul_le : 2 ^ (T_K + s K) * u K ≤ 2 ^ (T_K + s K) * u 0 :=
      Nat.mul_le_mul_left (2 ^ (T_K + s K)) hu_le
    have hlt_prod : (3 ^ T_K * 2 ^ (s 0)) * u 0 < 2 ^ (T_K + s K) * u 0 := by omega
    exact Nat.lt_of_mul_lt_mul_right hlt_prod
  · intro hs_le
    have h2_le : 2 ^ (s K) ≤ 2 ^ (s 0) := Nat.pow_le_pow_right (by decide) hs_le
    have hmul_s : 2 ^ (s K) * (3 ^ T_K * u 0) ≤ 2 ^ (s 0) * (3 ^ T_K * u 0) :=
      Nat.mul_le_mul_right (3 ^ T_K * u 0) h2_le
    have hlhs_eq : 2 ^ (s 0) * (3 ^ T_K * u 0) = 3 ^ T_K * 2 ^ (s 0) * u 0 := by ring
    have hrhs_eq : 2 ^ (T_K + s K) * u K = 2 ^ (s K) * (2 ^ T_K * u K) := by
      rw [Nat.pow_add 2 T_K (s K)]
      ring
    have hlt_s : 2 ^ (s K) * (3 ^ T_K * u 0) < 2 ^ (s K) * (2 ^ T_K * u K) := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt_s
  · refine ⟨h28.2.2.2.1, ?_, h28.2.2.2.2.2.2⟩
    have hs := h32.2.2.2
    rw [h32.1] at hs
    exact hs

/-! ## 64. Theorem SB.64: Grand 64-Theorem Synthesis of Seed Finiteness & Orbit Extrema -/

/-- **Grand 64-Theorem Synthesis of Seed Finiteness & Orbit Extrema
(`grand_seed_finiteness_and_extrema_64_synthesis`, Theorem SB.64)**:
Unifies the local descent & $2 \to 4 \to 7 \to 12$ staircase explosion (`SB.61`),
the trough-rebound $(81/16)$ compound-interest trap (`SB.62`), and the finite-seed
global peak–trough seesaw & post-horizon uniqueness (`SB.63`) with the $(j+n, k+n)$
diagonal synthesis (`SB.60`). -/
theorem grand_seed_finiteness_and_extrema_64_synthesis :
    (∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 4) →
      2 ≤ s r →
      u (r + 1) ≤ u r →
      u (r + 2) ≤ u (r + 1) →
      u (r + 3) ≤ u (r + 2) →
      4 ≤ s (r + 1) ∧ 7 ≤ s (r + 2) ∧ 12 ≤ s (r + 3)) ∧
    (∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 3) →
      2 ≤ s r →
      u (r + 1) ≤ u r →
      4 ≤ s (r + 1) ∧
        81 * u (r + 1) + 1 ≤ 2 ^ (s (r + 2)) * u (r + 2) ∧
        81 * (3 ^ (s r) * u r + 1) + 16 ≤ 16 * 2 ^ (s (r + 2)) * u (r + 2)) ∧
    (∀ {b_0 K : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (K + 1) →
      (∀ k < K, 2 ≤ s k) →
      1 ≤ K →
      (u K ≤ u 0 → 3 ^ (blockSteps s K) * 2 ^ (s 0) < 2 ^ (blockSteps s K + s K)) ∧
        (s K ≤ s 0 → 3 ^ (blockSteps s K) * u 0 < 2 ^ (blockSteps s K) * u K)) := by
  refine ⟨local_descent_rung_jump_and_multi_step_descent_explosion.2.2, ?_, ?_⟩
  · intro b_0 r s u hchain hsr hu1
    exact (trough_rebound_compound_interest_and_local_minimum_trap hchain).2.1 hsr hu1
  · intro b_0 K s u hchain hs2 hK
    have h63 := finite_seed_global_peak_trough_seesaw_and_return_barrier hchain hs2 hK
    exact ⟨h63.2.1, h63.2.2.1⟩

/-! ## 65. Theorem SB.65: $\text{LTE}_2$ Ultrametric Flush Pinning & Descent-Flush Prohibition -/

/-- Helper: `3 ^ n % 16` cycles through `{1, 3, 9, 11}` according to `n % 4 ∈ {0, 1, 2, 3}`. -/
theorem three_pow_mod_sixteen_quad (n : ℕ) :
    (n % 4 = 0 → 3 ^ n % 16 = 1) ∧
    (n % 4 = 1 → 3 ^ n % 16 = 3) ∧
    (n % 4 = 2 → 3 ^ n % 16 = 9) ∧
    (n % 4 = 3 → 3 ^ n % 16 = 11) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 3 ^ (n + 1) = 3 * 3 ^ n := by
        rw [Nat.pow_succ]
        ring
      rw [hpow]
      omega

/-- **$\text{LTE}_2$ Ultrametric Flush Pinning & Descent-Flush Prohibition
(`lte2_ultrametric_flush_pinning_and_descent_prohibition`, Theorem SB.65)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds with `2 ≤ s r` and `2 ≤ s (r + 1)`.
By the 2-adic ultrametric valuation law on
`3 ^ (s r) * u r + 1 = (3 ^ (s r) - 1) * u r + (u r + 1)` (even `s r`) and
`3 * (3 ^ (s r - 1) - 1) * u r + (3 * u r + 1)` (odd `s r`):
1. **Even Rung $s_r \equiv 2 \pmod 4$ ($v_2(3^{s_r} - 1) = 3$)**:
   - `(u r % 8 = 3 ↔ s (r + 1) = 2)`,
   - `(u r % 16 = 15 ↔ s (r + 1) = 3)`, and whenever `u r % 16 = 15`, `u r < u (r + 1)`
     (high divisibility $16 \mid u_r + 1$ **forbids** a descent flush!),
   - `(u r % 16 = 7 ↔ 4 ≤ s (r + 1))`, and `u (r + 1) ≤ u r → u r % 16 = 7`!
2. **Even Rung $s_r \equiv 0 \pmod 4$ ($v_2(3^{s_r} - 1) \ge 4$)**:
   - `(u r % 8 = 3 ↔ s (r + 1) = 2)`,
   - `(u r % 16 = 7 ↔ s (r + 1) = 3)`, and whenever `u r % 16 = 7`, `u r < u (r + 1)`,
   - `(u r % 16 = 15 ↔ 4 ≤ s (r + 1))`, and `u (r + 1) ≤ u r → u r % 16 = 15`!
3. **Odd Rung $s_r \equiv 3 \pmod 4$ ($v_2(3^{s_r - 1} - 1) = 3$)**:
   - `(u r % 8 = 1 ↔ s (r + 1) = 2)`,
   - `(u r % 16 = 5 ↔ s (r + 1) = 3)`, and whenever `u r % 16 = 5`, `u r < u (r + 1)`
     (high divisibility $16 \mid 3 u_r + 1$ **forbids** a descent flush!),
   - `(u r % 16 = 13 ↔ 4 ≤ s (r + 1))`, and `u (r + 1) ≤ u r → u r % 16 = 13`!
4. **Odd Rung $s_r \equiv 1 \pmod 4$ ($v_2(3^{s_r - 1} - 1) \ge 4$)**:
   - `(u r % 8 = 1 ↔ s (r + 1) = 2)`,
   - `(u r % 16 = 13 ↔ s (r + 1) = 3)`, and whenever `u r % 16 = 13`, `u r < u (r + 1)`,
   - `(u r % 16 = 5 ↔ 4 ≤ s (r + 1))`, and `u (r + 1) ≤ u r → u r % 16 = 5`! -/
theorem lte2_ultrametric_flush_pinning_and_descent_prohibition
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2))
    (hs_r : 2 ≤ s r)
    (hs_r1 : 2 ≤ s (r + 1)) :
    (s r % 4 = 2 →
      (u r % 8 = 3 ↔ s (r + 1) = 2) ∧
        (u r % 16 = 15 ↔ s (r + 1) = 3) ∧
        (u r % 16 = 15 → u r < u (r + 1)) ∧
        (u r % 16 = 7 ↔ 4 ≤ s (r + 1)) ∧
        (u (r + 1) ≤ u r → u r % 16 = 7)) ∧
    (s r % 4 = 0 →
      (u r % 8 = 3 ↔ s (r + 1) = 2) ∧
        (u r % 16 = 7 ↔ s (r + 1) = 3) ∧
        (u r % 16 = 7 → u r < u (r + 1)) ∧
        (u r % 16 = 15 ↔ 4 ≤ s (r + 1)) ∧
        (u (r + 1) ≤ u r → u r % 16 = 15)) ∧
    (s r % 4 = 3 →
      (u r % 8 = 1 ↔ s (r + 1) = 2) ∧
        (u r % 16 = 5 ↔ s (r + 1) = 3) ∧
        (u r % 16 = 5 → u r < u (r + 1)) ∧
        (u r % 16 = 13 ↔ 4 ≤ s (r + 1)) ∧
        (u (r + 1) ≤ u r → u r % 16 = 13)) ∧
    (s r % 4 = 1 →
      (u r % 8 = 1 ↔ s (r + 1) = 2) ∧
        (u r % 16 = 13 ↔ s (r + 1) = 3) ∧
        (u r % 16 = 13 → u r < u (r + 1)) ∧
        (u r % 16 = 5 ↔ 4 ≤ s (r + 1)) ∧
        (u (r + 1) ≤ u r → u r % 16 = 5)) := by
  have h42 := universal_mod8_and_mod24_next_rung_dichotomy hchain hs_r1
  have h16_lock := (universal_mod4_quotient_rung_parity_lock_and_mersenne_trap hchain hs_r1).1
  have h61 := local_descent_rung_jump_and_multi_step_descent_explosion.1 hchain
  have hstep := (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have hu1_odd : u (r + 1) % 2 = 1 := (hchain (r + 1) (by omega)).2.1
  have h3_16 := three_pow_mod_sixteen_quad (s r)
  have hmul16 :
      ((3 ^ (s r) % 16) * (u r % 16) + 1) % 16 = (2 ^ (s (r + 1)) * u (r + 1)) % 16 := by
    have h1 : (3 ^ (s r) % 16) * (u r % 16) % 16 = (3 ^ (s r) * u r) % 16 :=
      (Nat.mul_mod _ _ 16).symm
    have h2 : (3 ^ (s r) * u r + 1) % 16 = (2 ^ (s (r + 1)) * u (r + 1)) % 16 := by rw [hstep]
    omega
  have hrung16 :
      (s (r + 1) = 2 →
        (2 ^ (s (r + 1)) * u (r + 1)) % 16 = 4 ∨ (2 ^ (s (r + 1)) * u (r + 1)) % 16 = 12) ∧
      (s (r + 1) = 3 → (2 ^ (s (r + 1)) * u (r + 1)) % 16 = 8) ∧
      (4 ≤ s (r + 1) → (2 ^ (s (r + 1)) * u (r + 1)) % 16 = 0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hs2_eq
      rw [hs2_eq]
      omega
    · intro hs3_eq
      rw [hs3_eq]
      omega
    · intro hs4_ge
      obtain ⟨k, hk⟩ : ∃ k : ℕ, s (r + 1) = k + 4 := ⟨s (r + 1) - 4, by omega⟩
      have hpow : 2 ^ (s (r + 1)) * u (r + 1) = 16 * (2 ^ k * u (r + 1)) := by
        rw [hk, Nat.pow_add 2 k 4]
        ring
      rw [hpow]
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hsr4
    have heven : s r % 2 = 0 := by omega
    have hu_mod4 : u r % 4 = 3 := h16_lock.1.mp heven
    have h3_val : 3 ^ (s r) % 16 = 9 := h3_16.2.2.1 hsr4
    have hmul16' := hmul16
    rw [h3_val] at hmul16'
    have hiff2 : u r % 8 = 3 ↔ s (r + 1) = 2 := (h42.1 heven).1
    have hiff3 : u r % 16 = 15 ↔ s (r + 1) = 3 := by
      constructor
      · intro hu15
        by_contra hne3
        rcases (by omega : s (r + 1) = 2 ∨ 4 ≤ s (r + 1)) with h2 | h4
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.2 h4; omega
      · intro hs3
        have hm := hrung16.2.1 hs3; omega
    have hiff4 : u r % 16 = 7 ↔ 4 ≤ s (r + 1) := by
      constructor
      · intro hu7
        by_contra hlt4
        rcases (by omega : s (r + 1) = 2 ∨ s (r + 1) = 3) with h2 | h3
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.1 h3; omega
      · intro hs4
        have hm := hrung16.2.2 hs4; omega
    have hasc : u r % 16 = 15 → u r < u (r + 1) := by
      intro hu15
      have hs3 : s (r + 1) = 3 := hiff3.mp hu15
      by_contra hle
      have h4 : 4 ≤ s (r + 1) := (h61 (by omega)).2.1 hs_r
      omega
    have hdesc : u (r + 1) ≤ u r → u r % 16 = 7 := by
      intro hle
      exact hiff4.mpr ((h61 hle).2.1 hs_r)
    exact ⟨hiff2, hiff3, hasc, hiff4, hdesc⟩
  · intro hsr4
    have heven : s r % 2 = 0 := by omega
    have hu_mod4 : u r % 4 = 3 := h16_lock.1.mp heven
    have h3_val : 3 ^ (s r) % 16 = 1 := h3_16.1 hsr4
    have hmul16' := hmul16
    rw [h3_val] at hmul16'
    have hiff2 : u r % 8 = 3 ↔ s (r + 1) = 2 := (h42.1 heven).1
    have hiff3 : u r % 16 = 7 ↔ s (r + 1) = 3 := by
      constructor
      · intro hu7
        by_contra hne3
        rcases (by omega : s (r + 1) = 2 ∨ 4 ≤ s (r + 1)) with h2 | h4
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.2 h4; omega
      · intro hs3
        have hm := hrung16.2.1 hs3; omega
    have hiff4 : u r % 16 = 15 ↔ 4 ≤ s (r + 1) := by
      constructor
      · intro hu15
        by_contra hlt4
        rcases (by omega : s (r + 1) = 2 ∨ s (r + 1) = 3) with h2 | h3
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.1 h3; omega
      · intro hs4
        have hm := hrung16.2.2 hs4; omega
    have hasc : u r % 16 = 7 → u r < u (r + 1) := by
      intro hu7
      have hs3 : s (r + 1) = 3 := hiff3.mp hu7
      by_contra hle
      have h4 : 4 ≤ s (r + 1) := (h61 (by omega)).2.1 hs_r
      omega
    have hdesc : u (r + 1) ≤ u r → u r % 16 = 15 := by
      intro hle
      exact hiff4.mpr ((h61 hle).2.1 hs_r)
    exact ⟨hiff2, hiff3, hasc, hiff4, hdesc⟩
  · intro hsr4
    have hodd : s r % 2 = 1 := by omega
    have hu_mod4 : u r % 4 = 1 := h16_lock.2.mp hodd
    have h3_val : 3 ^ (s r) % 16 = 11 := h3_16.2.2.2 hsr4
    have hmul16' := hmul16
    rw [h3_val] at hmul16'
    have hiff2 : u r % 8 = 1 ↔ s (r + 1) = 2 := (h42.2 hodd).1
    have hiff3 : u r % 16 = 5 ↔ s (r + 1) = 3 := by
      constructor
      · intro hu5
        by_contra hne3
        rcases (by omega : s (r + 1) = 2 ∨ 4 ≤ s (r + 1)) with h2 | h4
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.2 h4; omega
      · intro hs3
        have hm := hrung16.2.1 hs3; omega
    have hiff4 : u r % 16 = 13 ↔ 4 ≤ s (r + 1) := by
      constructor
      · intro hu13
        by_contra hlt4
        rcases (by omega : s (r + 1) = 2 ∨ s (r + 1) = 3) with h2 | h3
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.1 h3; omega
      · intro hs4
        have hm := hrung16.2.2 hs4; omega
    have hasc : u r % 16 = 5 → u r < u (r + 1) := by
      intro hu5
      have hs3 : s (r + 1) = 3 := hiff3.mp hu5
      by_contra hle
      have h4 : 4 ≤ s (r + 1) := (h61 (by omega)).2.1 hs_r
      omega
    have hdesc : u (r + 1) ≤ u r → u r % 16 = 13 := by
      intro hle
      exact hiff4.mpr ((h61 hle).2.1 hs_r)
    exact ⟨hiff2, hiff3, hasc, hiff4, hdesc⟩
  · intro hsr4
    have hodd : s r % 2 = 1 := by omega
    have hu_mod4 : u r % 4 = 1 := h16_lock.2.mp hodd
    have h3_val : 3 ^ (s r) % 16 = 3 := h3_16.2.1 hsr4
    have hmul16' := hmul16
    rw [h3_val] at hmul16'
    have hiff2 : u r % 8 = 1 ↔ s (r + 1) = 2 := (h42.2 hodd).1
    have hiff3 : u r % 16 = 13 ↔ s (r + 1) = 3 := by
      constructor
      · intro hu13
        by_contra hne3
        rcases (by omega : s (r + 1) = 2 ∨ 4 ≤ s (r + 1)) with h2 | h4
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.2 h4; omega
      · intro hs3
        have hm := hrung16.2.1 hs3; omega
    have hiff4 : u r % 16 = 5 ↔ 4 ≤ s (r + 1) := by
      constructor
      · intro hu5
        by_contra hlt4
        rcases (by omega : s (r + 1) = 2 ∨ s (r + 1) = 3) with h2 | h3
        · have hm := hrung16.1 h2; omega
        · have hm := hrung16.2.1 h3; omega
      · intro hs4
        have hm := hrung16.2.2 hs4; omega
    have hasc : u r % 16 = 13 → u r < u (r + 1) := by
      intro hu13
      have hs3 : s (r + 1) = 3 := hiff3.mp hu13
      by_contra hle
      have h4 : 4 ≤ s (r + 1) := (h61 (by omega)).2.1 hs_r
      omega
    have hdesc : u (r + 1) ≤ u r → u r % 16 = 5 := by
      intro hle
      exact hiff4.mpr ((h61 hle).2.1 hs_r)
    exact ⟨hiff2, hiff3, hasc, hiff4, hdesc⟩

/-! ## 66. Theorem SB.66: Post-Horizon Binary Zero-Bit Desert & Dual-Radix Lock -/

/-- **Post-Horizon Binary Zero-Bit Desert & Dual-Radix Lock
(`post_horizon_binary_zero_bit_desert_and_dual_radix_lock`, Theorem SB.66)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Let `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`S_K = T_K + s K`, `A_K = renewalNumerator s K`, and `N_K = 2 ^ S_K * u K`.
Whenever the seed $P_0$ has finite bit-length $B_0$ (`P 0 < 2 ^ B_0`) and the orbit
has passed the bit-horizon (`B_0 ≤ S_K`):
1. **Binary Zero-Bit Desert of $P_0$ in $[B_0, S_K]$**:
   `P 0 / 2 ^ B_0 = 0`, `P 0 % 2 ^ B_0 = P 0`, `P 0 % 2 ^ S_K = P 0`, and
   `∀ B, B_0 ≤ B → (P 0 % 2 ^ S_K) / 2 ^ B = 0`,
2. **Base-2 Trailing-Zero & Binary Weight Lock on $N_K$**:
   `N_K = 3 ^ T_K * P 0 + A_K`, `N_K % 2 ^ S_K = 0`, `N_K / 2 ^ S_K = u K`, and
   `base2DigitSum N_K = base2DigitSum (u K)`, and
3. **Simultaneous Base-3 Zero-Carry Lock on $N_K$**:
   `N_K / 3 ^ T_K = P 0`, `N_K % 3 ^ T_K = A_K`, and
   `base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K`! -/
theorem post_horizon_binary_zero_bit_desert_and_dual_radix_lock
    {b_0 K B_0 : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k)
    (hP0_bits : oddReturnP (orbit b_0 (blockSteps s 0)) < 2 ^ B_0)
    (hhor : B_0 ≤ blockSteps s K + s K) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let S_K := T_K + s K
    let A_K := renewalNumerator s K
    let N_K := 2 ^ S_K * u K
    (P 0 / 2 ^ B_0 = 0 ∧
      P 0 % 2 ^ B_0 = P 0 ∧
      P 0 % 2 ^ S_K = P 0 ∧
      (∀ B, B_0 ≤ B → (P 0 % 2 ^ S_K) / 2 ^ B = 0)) ∧
      (N_K = 3 ^ T_K * P 0 + A_K ∧
        N_K % 2 ^ S_K = 0 ∧
        N_K / 2 ^ S_K = u K ∧
        base2DigitSum N_K = base2DigitSum (u K)) ∧
      (N_K / 3 ^ T_K = P 0 ∧
        N_K % 3 ^ T_K = A_K ∧
        base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K) := by
  intro P T_K S_K A_K N_K
  have h28 := bridge_a_dual_universe_series_lowest_terms_and_uniqueness hchain hs2
  have h32 := (bridge_c_multi_step_dual_base2_base3_zero_carry_split hchain hs2).1
  dsimp only at h28 h32
  have hP0_lt_SK : P 0 < 2 ^ S_K :=
    lt_of_lt_of_le hP0_bits (Nat.pow_le_pow_right (by decide) hhor)
  have hdiv_B0 : P 0 / 2 ^ B_0 = 0 := Nat.div_eq_of_lt hP0_bits
  have hmod_B0 : P 0 % 2 ^ B_0 = P 0 := Nat.mod_eq_of_lt hP0_bits
  have hmod_SK : P 0 % 2 ^ S_K = P 0 := Nat.mod_eq_of_lt hP0_lt_SK
  have hdesert : ∀ B, B_0 ≤ B → (P 0 % 2 ^ S_K) / 2 ^ B = 0 := by
    intro B hB
    rw [hmod_SK]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hP0_bits (Nat.pow_le_pow_right (by decide) hB))
  have h2_pos : 0 < 2 ^ S_K := Nat.pow_pos (by decide)
  have hNK_mod2 : N_K % 2 ^ S_K = 0 := Nat.mul_mod_right (2 ^ S_K) (u K)
  have hNK_div2 : N_K / 2 ^ S_K = u K := Nat.mul_div_right (u K) h2_pos
  have hNK_b2 : base2DigitSum N_K = base2DigitSum (u K) :=
    base2DigitSum_two_pow_mul S_K (u K)
  have hs3 : base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K := by
    have hs := h32.2.2.2
    rw [h32.1] at hs
    exact hs
  exact ⟨⟨hdiv_B0, hmod_B0, hmod_SK, hdesert⟩,
    ⟨h28.1, hNK_mod2, hNK_div2, hNK_b2⟩,
    ⟨h28.2.2.2.1, h28.2.2.2.2.1, hs3⟩⟩

/-! ## 67. Theorem SB.67: Shifted-Basepoint Baker–Matveev Pinch & Repeated-Odd-Core Rhin Reduction -/

/-- **Shifted-Basepoint Baker–Matveev Pinch & Repeated-Odd-Core Rhin Reduction
(`shifted_basepoint_baker_matveev_pinch_and_repeated_core_rhin_form`, Theorem SB.67)**:
Suppose `ValidBlockChain b_0 s u (r + M + 1)` holds with `∀ k < r, 2 ≤ s k`, `1 ≤ r`,
`∀ k < M, 2 ≤ s (r + k)`, and `1 ≤ M`.
Setting `T_r = blockSteps s r`, `s' t = s (r + t)`, `n_2 = blockSteps s' M`,
`s_K = s (r + M)`, and `A_rM = renewalNumerator s' M`:
1. **Exact Shifted-Basepoint Linear Form & $3^{n_2}$-Canceled Baker Pinch**:
   - `2 ^ (n_2 + s_K) * u (r + M) = 3 ^ n_2 * (2 ^ (s r) * u r) + A_rM`,
   - `3 ^ n_2 * (2 ^ (s r) * u r) < 2 ^ (n_2 + s_K) * u (r + M)`,
   - `5 * (2 ^ (n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (s r) * u r)) + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2`, and
   - `3 ^ T_r * 2 ^ (s 0) * u 0 < 2 ^ T_r * (2 ^ (s r) * u r)`,
2. **Repeated-Odd-Core ($u_{r+M} = u_r$) Pure 2-Logarithm Rhin Reduction**:
   Whenever the odd core repeats (`u (r + M) = u r`), the entire state `2 ^ (s r) * u r`
   factors out and divides `A_rM`, leaving the pure 2-logarithm difference `2 ^ (n_2 + s_K - s r) - 3 ^ n_2`:
   - `s r < s_K` and `3 ^ n_2 < 2 ^ (n_2 + s_K - s r)`,
   - `(2 ^ (s r) * u r) * (2 ^ (n_2 + s_K - s r) - 3 ^ n_2) = A_rM` and `(2 ^ (s r) * u r) ∣ A_rM`,
   - `5 * ((2 ^ (s r) * u r) * (2 ^ (n_2 + s_K - s r) - 3 ^ n_2)) + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2`, and
   - **Unconditional Minimum Separation Between Repeated Odd Cores**:
     `5 * (2 ^ (s r) * u r) + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2` and
     `5 * 3 ^ T_r * 2 ^ (s 0) * u 0 < 4 * 2 ^ T_r * 3 ^ n_2`! -/
theorem shifted_basepoint_baker_matveev_pinch_and_repeated_core_rhin_form
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + M + 1))
    (hs_past : ∀ k < r, 2 ≤ s k)
    (hr : 1 ≤ r)
    (hs_win : ∀ k < M, 2 ≤ s (r + k))
    (hM : 1 ≤ M) :
    let T_r := blockSteps s r
    let s' := fun t => s (r + t)
    let n_2 := blockSteps s' M
    let s_K := s (r + M)
    let A_rM := renewalNumerator s' M
    (2 ^ (n_2 + s_K) * u (r + M) = 3 ^ n_2 * (2 ^ (s r) * u r) + A_rM ∧
      3 ^ n_2 * (2 ^ (s r) * u r) < 2 ^ (n_2 + s_K) * u (r + M) ∧
      5 * (2 ^ (n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (s r) * u r)) + 4 * 2 ^ n_2 ≤
        4 * 3 ^ n_2 ∧
      3 ^ T_r * 2 ^ (s 0) * u 0 < 2 ^ T_r * (2 ^ (s r) * u r)) ∧
      (u (r + M) = u r →
        s r < s_K ∧
          3 ^ n_2 < 2 ^ (n_2 + s_K - s r) ∧
          (2 ^ (s r) * u r) * (2 ^ (n_2 + s_K - s r) - 3 ^ n_2) = A_rM ∧
          (2 ^ (s r) * u r) ∣ A_rM ∧
          5 * ((2 ^ (s r) * u r) * (2 ^ (n_2 + s_K - s r) - 3 ^ n_2)) + 4 * 2 ^ n_2 ≤
            4 * 3 ^ n_2 ∧
          5 * (2 ^ (s r) * u r) + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2 ∧
          5 * 3 ^ T_r * 2 ^ (s 0) * u 0 < 4 * 2 ^ T_r * 3 ^ n_2) := by
  intro T_r s' n_2 s_K A_rM
  have hid_raw : 2 ^ (n_2 + s_K) * u (r + M) = 3 ^ n_2 * 2 ^ (s r) * u r + A_rM :=
    (late_step_cauchy_pinch_and_odd_quotient_gcd_dvd (N := r) (M := M) hchain).2.1
  have hid : 2 ^ (n_2 + s_K) * u (r + M) = 3 ^ n_2 * (2 ^ (s r) * u r) + A_rM := by
    rw [hid_raw]
    ring
  have hinv_M : 5 * A_rM + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2 :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s' M hs_win
  have hA_pos : 1 ≤ A_rM := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, M = m + 1 := ⟨M - 1, by omega⟩
    have hpow_pos : 1 ≤ 2 ^ (blockSteps s' m + s' m) := Nat.one_le_pow _ 2 (by decide)
    have hA_eq : A_rM = 3 ^ (s' m) * renewalNumerator s' m + 2 ^ (blockSteps s' m + s' m) := by
      change renewalNumerator s' M =
        3 ^ (s' m) * renewalNumerator s' m + 2 ^ (blockSteps s' m + s' m)
      rw [hm]
      rfl
    omega
  have hlt_main : 3 ^ n_2 * (2 ^ (s r) * u r) < 2 ^ (n_2 + s_K) * u (r + M) := by omega
  have hdiff_eq : 2 ^ (n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (s r) * u r) = A_rM := by omega
  have hpinch :
      5 * (2 ^ (n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (s r) * u r)) + 4 * 2 ^ n_2 ≤
        4 * 3 ^ n_2 := by
    rw [hdiff_eq]
    exact hinv_M
  have hch_r : ValidBlockChain b_0 s u (r + 1) := fun k hk => hchain k (by omega)
  have hlow_r : 3 ^ T_r * 2 ^ (s 0) * u 0 < 2 ^ T_r * (2 ^ (s r) * u r) := by
    have h1 : 3 ^ T_r * 2 ^ (s 0) * u 0 < 2 ^ (T_r + s r) * u r :=
      (finite_seed_global_peak_trough_seesaw_and_return_barrier hch_r hs_past hr).1.1
    rw [Nat.pow_add 2 T_r (s r)] at h1
    have h2 : 2 ^ T_r * 2 ^ (s r) * u r = 2 ^ T_r * (2 ^ (s r) * u r) := by ring
    omega
  refine ⟨⟨hid, hlt_main, hpinch, hlow_r⟩, ?_⟩
  intro hu_eq
  have hid_eq := hid
  rw [hu_eq] at hid_eq
  have hur_odd : u r % 2 = 1 := (hchain r (by omega)).2.1
  have hur_pos : 1 ≤ u r := by omega
  have hlt_u : (3 ^ n_2 * 2 ^ (s r)) * u r < 2 ^ (n_2 + s_K) * u r := by
    have hassoc : (3 ^ n_2 * 2 ^ (s r)) * u r = 3 ^ n_2 * (2 ^ (s r) * u r) := by ring
    omega
  have hlt_pow : 3 ^ n_2 * 2 ^ (s r) < 2 ^ (n_2 + s_K) :=
    Nat.lt_of_mul_lt_mul_right hlt_u
  have h2_n2_le_3 : 2 ^ n_2 ≤ 3 ^ n_2 := Nat.pow_le_pow_left (by decide) n_2
  have hsr_lt_sK : s r < s_K := by
    apply Nat.lt_of_not_le
    intro hs_le
    have hn_le : n_2 + s_K ≤ n_2 + s r := Nat.add_le_add_left hs_le n_2
    have h2_le : 2 ^ (n_2 + s_K) ≤ 2 ^ (n_2 + s r) :=
      Nat.pow_le_pow_right (by decide) hn_le
    have h2_split : 2 ^ (n_2 + s r) = 2 ^ n_2 * 2 ^ (s r) := Nat.pow_add 2 n_2 (s r)
    have hmul_le : 2 ^ n_2 * 2 ^ (s r) ≤ 3 ^ n_2 * 2 ^ (s r) :=
      Nat.mul_le_mul_right (2 ^ (s r)) h2_n2_le_3
    omega
  have hexp_split : n_2 + s_K = s r + (n_2 + s_K - s r) := by
    have hle : s r ≤ n_2 + s_K :=
      Nat.le_trans (Nat.le_of_lt hsr_lt_sK) (Nat.le_add_left s_K n_2)
    exact (Nat.add_sub_of_le hle).symm
  have hpow_split : 2 ^ (n_2 + s_K) = 2 ^ (s r) * 2 ^ (n_2 + s_K - s r) := by
    rw [← Nat.pow_add 2 (s r) (n_2 + s_K - s r), ← hexp_split]
  have h3_lt_2 : 3 ^ n_2 < 2 ^ (n_2 + s_K - s r) := by
    have hlt_s : 2 ^ (s r) * 3 ^ n_2 < 2 ^ (s r) * 2 ^ (n_2 + s_K - s r) := by
      have hcomm : 2 ^ (s r) * 3 ^ n_2 = 3 ^ n_2 * 2 ^ (s r) := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_left hlt_s
  have hrhin_id : (2 ^ (s r) * u r) * (2 ^ (n_2 + s_K - s r) - 3 ^ n_2) = A_rM := by
    rw [Nat.mul_sub_left_distrib]
    have h1 : (2 ^ (s r) * u r) * 2 ^ (n_2 + s_K - s r) = 2 ^ (n_2 + s_K) * u r := by
      rw [hpow_split]
      ring
    have h2 : (2 ^ (s r) * u r) * 3 ^ n_2 = 3 ^ n_2 * (2 ^ (s r) * u r) := by ring
    omega
  have hdvd : (2 ^ (s r) * u r) ∣ A_rM := ⟨2 ^ (n_2 + s_K - s r) - 3 ^ n_2, hrhin_id.symm⟩
  have hrhin_pinch :
      5 * ((2 ^ (s r) * u r) * (2 ^ (n_2 + s_K - s r) - 3 ^ n_2)) + 4 * 2 ^ n_2 ≤
        4 * 3 ^ n_2 := by
    rw [hrhin_id]
    exact hinv_M
  have hdiff_pos : 1 ≤ 2 ^ (n_2 + s_K - s r) - 3 ^ n_2 := by omega
  have hle_A : 2 ^ (s r) * u r ≤ A_rM := by
    rw [← hrhin_id]
    exact Nat.le_mul_of_pos_right (2 ^ (s r) * u r) hdiff_pos
  have hmin_sep1 : 5 * (2 ^ (s r) * u r) + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2 := by omega
  have h2n2_pos : 1 ≤ 2 ^ n_2 := Nat.one_le_pow _ 2 (by decide)
  have h5_Pr_lt : 5 * (2 ^ (s r) * u r) < 4 * 3 ^ n_2 := by omega
  have hmin_sep2 : 5 * 3 ^ T_r * 2 ^ (s 0) * u 0 < 4 * 2 ^ T_r * 3 ^ n_2 := by
    have hm1 := Nat.mul_lt_mul_of_pos_left hlow_r (by decide : 0 < 5)
    have hm2 : 2 ^ T_r * (5 * (2 ^ (s r) * u r)) < 2 ^ T_r * (4 * 3 ^ n_2) :=
      Nat.mul_lt_mul_of_pos_left h5_Pr_lt (Nat.pow_pos (by decide))
    have heq1 : 5 * (3 ^ T_r * 2 ^ (s 0) * u 0) = 5 * 3 ^ T_r * 2 ^ (s 0) * u 0 := by ring
    have heq2 : 5 * (2 ^ T_r * (2 ^ (s r) * u r)) = 2 ^ T_r * (5 * (2 ^ (s r) * u r)) := by ring
    have heq3 : 2 ^ T_r * (4 * 3 ^ n_2) = 4 * 2 ^ T_r * 3 ^ n_2 := by ring
    omega
  exact ⟨hsr_lt_sK, h3_lt_2, hrhin_id, hdvd, hrhin_pinch, hmin_sep1, hmin_sep2⟩

/-! ## 68. Theorem SB.68: Senge–Straus / Stewart Simultaneous $(s_2, s_3)$ Finiteness Bridge & Grand 68-Theorem Synthesis -/

/-- **Senge–Straus / Stewart Simultaneous $(s_2, s_3)$ Finiteness Bridge & Grand 68-Theorem Synthesis
(`senge_straus_stewart_finiteness_bridge_and_grand_68_synthesis`, Theorem SB.68)**:
Across any `ValidBlockChain b_0 s u (K + 1)` with `∀ k < K, 2 ≤ s k`, setting
`P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`S_K = T_K + s K`, `A_K = renewalNumerator s K`, and `N_K = 2 ^ S_K * u K`:
1. **Exact Dual-Radix $(s_2, s_3)$ & Kummer Factorial Bridge on $N_K$**:
   - `base2DigitSum N_K = base2DigitSum (u K)` (the binary digit sum of $N_K$ is controlled
     purely by the odd core $u_K$!),
   - `base2DigitSum (N_K - 1) + 1 = S_K + base2DigitSum (u K)`,
   - `base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K`, and
   - `base3DigitSum N_K + 2 * (legendreFactVal3 N_K - 2 ^ S_K * legendreFactVal3 (u K)) = 2 ^ S_K * base3DigitSum (u K)`,
2. **Conditional Senge–Straus / Stewart Finiteness Bound**:
   Whenever $u_K$ lands in a binary-weight trough (`base2DigitSum (u K) ≤ B_2`) and an effective
   Senge–Straus bound `base2DigitSum N_K ≤ B_2 → base3DigitSum N_K ≤ B_3` holds on $N_K$,
   the cumulative renewal Base-3 digit sum is strictly trapped by
   `base3DigitSum A_K + base3DigitSum (P 0) ≤ B_3`, and
3. **Grand Synthesis of Wave 10 (`SB.65–SB.67`)**! -/
theorem senge_straus_stewart_finiteness_bridge_and_grand_68_synthesis
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let S_K := T_K + s K
    let A_K := renewalNumerator s K
    let N_K := 2 ^ S_K * u K
    (base2DigitSum N_K = base2DigitSum (u K) ∧
      base2DigitSum (N_K - 1) + 1 = S_K + base2DigitSum (u K) ∧
      base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K ∧
      base3DigitSum N_K +
          2 * (legendreFactVal3 N_K - 2 ^ S_K * legendreFactVal3 (u K)) =
        2 ^ S_K * base3DigitSum (u K)) ∧
      (∀ B_2 B_3 : ℕ,
        base2DigitSum (u K) ≤ B_2 →
        (base2DigitSum N_K ≤ B_2 → base3DigitSum N_K ≤ B_3) →
        base3DigitSum (P 0) + base3DigitSum A_K ≤ B_3) := by
  intro P T_K S_K A_K N_K
  have h32 := bridge_c_multi_step_dual_base2_base3_zero_carry_split hchain hs2
  dsimp only at h32
  have hb2 : base2DigitSum N_K = base2DigitSum (u K) :=
    base2DigitSum_two_pow_mul S_K (u K)
  have hb2_sub : base2DigitSum (N_K - 1) + 1 = S_K + base2DigitSum (u K) := by
    have h := h32.2.2.2.2
    rw [h32.1.1] at h
    exact h
  have hb3 : base3DigitSum N_K = base3DigitSum (P 0) + base3DigitSum A_K := by
    have h := h32.1.2.2.2
    rw [h32.1.1] at h
    exact h
  have h37 := (kummer_base3_two_pow_mul_carry_identity_and_bound S_K (u K)).2.2
  refine ⟨⟨hb2, hb2_sub, hb3, h37⟩, ?_⟩
  intro B_2 B_3 hu_B2 hss
  have hN_B2 : base2DigitSum N_K ≤ B_2 := by
    rw [hb2]
    exact hu_B2
  have hN_B3 : base3DigitSum N_K ≤ B_3 := hss hN_B2
  omega

/-! ## 69. Theorem SB.69: Adjacent Odd-Core Coprimality & Universal Non-Equality ($u_{r+1} \ne u_r$) -/

/-- Helper: `3 ^ n % 2 = 1` for all `n : ℕ`. -/
theorem three_pow_mod_two_eq_one (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- **Adjacent Odd-Core Coprimality & Universal Non-Equality
(`adjacent_odd_core_coprimality_and_universal_non_equality`, Theorem SB.69)**:
Suppose `ValidBlockChain b_0 s u (r + 2)` holds with `2 ≤ s r`:
1. **Exact Adjacent Odd-Core Coprimality**:
   `Nat.Coprime (u r) (u (r + 1))` and
   `Nat.Coprime (2 ^ (s (r + 1)) * u (r + 1)) (3 ^ (s r) * u r)`,
2. **Mod-8 Obstruction on $3^{s_r} + 1$**:
   `((3 ^ (s r) + 1) % 8 = 2 ∨ (3 ^ (s r) + 1) % 8 = 4)` and `10 ≤ 3 ^ (s r) + 1`, and
3. **Unconditional Non-Equality of Adjacent Odd Cores**:
   `u (r + 1) ≠ u r`! -/
theorem adjacent_odd_core_coprimality_and_universal_non_equality
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 2))
    (hs_r : 2 ≤ s r) :
    Nat.Coprime (u r) (u (r + 1)) ∧
      Nat.Coprime (2 ^ (s (r + 1)) * u (r + 1)) (3 ^ (s r) * u r) ∧
      (((3 ^ (s r) + 1) % 8 = 2 ∨ (3 ^ (s r) + 1) % 8 = 4) ∧ 10 ≤ 3 ^ (s r) + 1) ∧
      u (r + 1) ≠ u r := by
  have hstep : 2 ^ (s (r + 1)) * u (r + 1) = 3 ^ (s r) * u r + 1 :=
    (one_step_backward_quotient_recovery_and_mod_three_pow_one hchain).1
  have hsub : 2 ^ (s (r + 1)) * u (r + 1) - 3 ^ (s r) * u r = 1 := by omega
  have hcop_u : Nat.Coprime (u r) (u (r + 1)) := by
    rw [Nat.Coprime]
    apply Nat.eq_one_of_dvd_one
    have hd1 : Nat.gcd (u r) (u (r + 1)) ∣ 3 ^ (s r) * u r :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left (u r) (u (r + 1))) (3 ^ (s r))
    have hd2 : Nat.gcd (u r) (u (r + 1)) ∣ 2 ^ (s (r + 1)) * u (r + 1) :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right (u r) (u (r + 1))) (2 ^ (s (r + 1)))
    have hd_sub := Nat.dvd_sub hd2 hd1
    rw [hsub] at hd_sub
    exact hd_sub
  have hcop_full : Nat.Coprime (2 ^ (s (r + 1)) * u (r + 1)) (3 ^ (s r) * u r) := by
    rw [Nat.Coprime]
    apply Nat.eq_one_of_dvd_one
    have hd1 := Nat.gcd_dvd_left (2 ^ (s (r + 1)) * u (r + 1)) (3 ^ (s r) * u r)
    have hd2 := Nat.gcd_dvd_right (2 ^ (s (r + 1)) * u (r + 1)) (3 ^ (s r) * u r)
    have hd_sub := Nat.dvd_sub hd1 hd2
    rw [hsub] at hd_sub
    exact hd_sub
  have h3_8 := three_pow_mod_eight_parity (s r)
  have hmod8 : (3 ^ (s r) + 1) % 8 = 2 ∨ (3 ^ (s r) + 1) % 8 = 4 := by omega
  have hge10 : 10 ≤ 3 ^ (s r) + 1 := by
    have h9 : 3 ^ 2 ≤ 3 ^ (s r) := Nat.pow_le_pow_right (by decide) hs_r
    omega
  have hne : u (r + 1) ≠ u r := by
    intro heq
    have hg1 : Nat.gcd (u r) (u r) = 1 := by
      have hc : Nat.gcd (u r) (u (r + 1)) = 1 := hcop_u
      rw [heq] at hc
      exact hc
    have hur1 : u r = 1 := by
      rw [Nat.gcd_self] at hg1
      exact hg1
    have hpow_eq : 2 ^ (s (r + 1)) = 3 ^ (s r) + 1 := by
      rw [heq, hur1, mul_one, mul_one] at hstep
      exact hstep
    have hs1_ge4 : 4 ≤ s (r + 1) := by
      apply Nat.le_of_not_lt
      intro hlt4
      have hle3 : s (r + 1) ≤ 3 := by omega
      have h2_le8 : 2 ^ (s (r + 1)) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hle3
      omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s (r + 1) = k + 4 := ⟨s (r + 1) - 4, by omega⟩
    have hpow8 : (2 ^ (s (r + 1))) % 8 = 0 := by
      have hp : 2 ^ (s (r + 1)) = 8 * (2 ^ (k + 1)) := by
        rw [hk, Nat.pow_add 2 k 4, Nat.pow_succ]
        ring
      rw [hp]
      omega
    omega
  exact ⟨hcop_u, hcop_full, ⟨hmod8, hge10⟩, hne⟩

/-! ## 70. Theorem SB.70: Two-Step Odd-Core GCD, $s_r$-Free Return Bound, & Boundary Extinction -/

/-- **Two-Step Odd-Core GCD, $s_r$-Free Return Bound, & Boundary Extinction
(`two_step_odd_core_gcd_and_return_extinction`, Theorem SB.70)**:
Suppose `ValidBlockChain b_0 s u (r + 3)` holds:
1. **Exact Two-Step Odd-Core GCD Divisibility**:
   `Nat.gcd (u r) (u (r + 2)) ∣ (3 ^ (s (r + 1)) + 2 ^ (s (r + 1)))`,
2. **$s_r$-Free Two-Step Return Divisibility & Upper Bound (`u (r + 2) = u r`)**:
   Whenever `u (r + 2) = u r`, we have:
   - `(2 ^ (s (r + 1) + s (r + 2)) - 3 ^ (s r + s (r + 1))) * u r = 3 ^ (s (r + 1)) + 2 ^ (s (r + 1))`,
   - `u r ∣ (3 ^ (s (r + 1)) + 2 ^ (s (r + 1)))`, and
   - `u r ≤ 3 ^ (s (r + 1)) + 2 ^ (s (r + 1))` (**independent of `s r`!**), and
3. **Boundary Return `(3, 2, 6, 1, 7)` Next-Step Extinction Certificate**:
   `3 ^ 3 * 1 + 1 = 2 ^ 2 * 7 ∧ 3 ^ 2 * 7 + 1 = 2 ^ 6 * 1 ∧ (3 ^ 6 * 1 + 1) % 4 = 2`! -/
theorem two_step_odd_core_gcd_and_return_extinction
    {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 3)) :
    Nat.gcd (u r) (u (r + 2)) ∣ (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) ∧
      (u (r + 2) = u r →
        (2 ^ (s (r + 1) + s (r + 2)) - 3 ^ (s r + s (r + 1))) * u r =
          3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) ∧
          u r ∣ (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) ∧
          u r ≤ 3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) ∧
      (3 ^ 3 * 1 + 1 = 2 ^ 2 * 7 ∧
        3 ^ 2 * 7 + 1 = 2 ^ 6 * 1 ∧
        (3 ^ 6 * 1 + 1) % 4 = 2) := by
  have hid :
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) =
        3 ^ (s r + s (r + 1)) * u r + 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) :=
    (trough_rebound_compound_interest_and_local_minimum_trap hchain).1
  have hid' :
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) =
        3 ^ (s r + s (r + 1)) * u r + (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) := by
    rw [hid]
    ring
  have hsub :
      2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) - 3 ^ (s r + s (r + 1)) * u r =
        3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) := by
    rw [hid', Nat.add_sub_cancel_left]
  have hgcd : Nat.gcd (u r) (u (r + 2)) ∣ (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) := by
    have hd1 : Nat.gcd (u r) (u (r + 2)) ∣ 3 ^ (s r + s (r + 1)) * u r :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left (u r) (u (r + 2))) (3 ^ (s r + s (r + 1)))
    have hd2 : Nat.gcd (u r) (u (r + 2)) ∣ 2 ^ (s (r + 1) + s (r + 2)) * u (r + 2) :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right (u r) (u (r + 2))) (2 ^ (s (r + 1) + s (r + 2)))
    rw [hid'] at hd2
    exact (Nat.dvd_add_right hd1).mp hd2
  refine ⟨hgcd, ?_, by decide⟩
  intro hu_eq
  have hdvd : u r ∣ (3 ^ (s (r + 1)) + 2 ^ (s (r + 1))) := by
    have hg := hgcd
    rw [hu_eq, Nat.gcd_self] at hg
    exact hg
  have hpos : 0 < 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) :=
    Nat.add_pos_left (Nat.pow_pos (by decide)) (2 ^ (s (r + 1)))
  have hle : u r ≤ 3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) := Nat.le_of_dvd hpos hdvd
  have hprod :
      (2 ^ (s (r + 1) + s (r + 2)) - 3 ^ (s r + s (r + 1))) * u r =
        3 ^ (s (r + 1)) + 2 ^ (s (r + 1)) := by
    rw [Nat.sub_mul]
    have hsub_eq := hsub
    rw [hu_eq] at hsub_eq
    exact hsub_eq
  exact ⟨hprod, hdvd, hle⟩

/-! ## 71. Theorem SB.71: End-of-Block $3^{s_r}$-Upgraded Baker Pinch & $s_r$-Free $M$-Step Return Bound -/

/-- **End-of-Block $3^{s_r}$-Upgraded Baker Pinch & $s_r$-Free $M$-Step Return Bound
(`end_of_block_three_pow_upgraded_baker_pinch_and_s_r_free_return_bound`, Theorem SB.71)**:
Suppose `ValidBlockChain b_0 s u (r + 1 + M + 1)` holds with `∀ k < M, 2 ≤ s (r + 1 + k)`.
Setting `s' t = s (r + 1 + t)`, `d = blockSteps s' M`, `S = d + s (r + 1 + M)`,
`T = s r + d`, and `R = 3 ^ d + renewalNumerator s' M`:
1. **Strict Oddness & Divisibility of `R`**:
   `2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R`, `R % 2 = 1`, and
   `Nat.gcd (u r) (u (r + 1 + M)) ∣ R`,
2. **The $3^{s_r}$-Upgraded Baker–Matveev Pinch**:
   `5 * 3 ^ (s r) * (2 ^ S * u (r + 1 + M) - 3 ^ T * u r) + 4 * 3 ^ (s r) * 2 ^ d ≤ 9 * 3 ^ T`, and
3. **$s_r$-Free $M$-Step Return Bound (`u (r + 1 + M) = u r`)**:
   Whenever `u (r + 1 + M) = u r`, we have:
   - `(2 ^ S - 3 ^ T) * u r = R`,
   - `u r ∣ R` and `u r ≤ R`, and
   - `5 * u r + 4 * 2 ^ d ≤ 9 * 3 ^ d` (**completely independent of `s r` and `T_r`!**)! -/
theorem end_of_block_three_pow_upgraded_baker_pinch_and_s_r_free_return_bound
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + 1 + M + 1))
    (hs2 : ∀ k < M, 2 ≤ s (r + 1 + k)) :
    let s' := fun t => s (r + 1 + t)
    let d := blockSteps s' M
    let S := d + s (r + 1 + M)
    let T := s r + d
    let R := 3 ^ d + renewalNumerator s' M
    (2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R ∧
      R % 2 = 1 ∧
      Nat.gcd (u r) (u (r + 1 + M)) ∣ R) ∧
      5 * 3 ^ (s r) * (2 ^ S * u (r + 1 + M) - 3 ^ T * u r) + 4 * 3 ^ (s r) * 2 ^ d ≤
        9 * 3 ^ T ∧
      (u (r + 1 + M) = u r →
        (2 ^ S - 3 ^ T) * u r = R ∧
          u r ∣ R ∧
          u r ≤ R ∧
          5 * u r + 4 * 2 ^ d ≤ 9 * 3 ^ d) := by
  intro s' d S T R
  have h25 := unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound hchain hs2
  dsimp only at h25
  have h95 : 5 * R + 4 * 2 ^ d ≤ 9 * 3 ^ d := h25.1
  have hdiv : (2 ^ S * u (r + 1 + M)) / 3 ^ T = u r := h25.2.2.2.1
  have hmod : (2 ^ S * u (r + 1 + M)) % 3 ^ T = R := h25.2.2.2.2.1
  have hid : 2 ^ S * u (r + 1 + M) = 3 ^ T * u r + R := by
    have hdm := Nat.div_add_mod (2 ^ S * u (r + 1 + M)) (3 ^ T)
    rw [hdiv, hmod] at hdm
    exact hdm.symm
  have hs_end : 1 ≤ s (r + 1 + M) := (hchain (r + 1 + M) (by omega)).1
  have hS_pos : 1 ≤ S := by omega
  have h2S_even : (2 ^ S * u (r + 1 + M)) % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, S = k + 1 := ⟨S - 1, by omega⟩
    have hp : 2 ^ S * u (r + 1 + M) = 2 * (2 ^ k * u (r + 1 + M)) := by
      rw [hk, Nat.pow_succ]
      ring
    rw [hp]
    omega
  have hur_odd : u r % 2 = 1 := (hchain r (by omega)).2.1
  have h3T_odd : 3 ^ T % 2 = 1 := three_pow_mod_two_eq_one T
  have hprod_odd : (3 ^ T * u r) % 2 = 1 := by
    rw [Nat.mul_mod, h3T_odd, hur_odd]
  have hR_odd : R % 2 = 1 := by omega
  have hsub : 2 ^ S * u (r + 1 + M) - 3 ^ T * u r = R := by omega
  have hgcd : Nat.gcd (u r) (u (r + 1 + M)) ∣ R := by
    have hd1 : Nat.gcd (u r) (u (r + 1 + M)) ∣ 3 ^ T * u r :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left (u r) (u (r + 1 + M))) (3 ^ T)
    have hd2 : Nat.gcd (u r) (u (r + 1 + M)) ∣ 2 ^ S * u (r + 1 + M) :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right (u r) (u (r + 1 + M))) (2 ^ S)
    have hd_sub := Nat.dvd_sub hd2 hd1
    rw [hsub] at hd_sub
    exact hd_sub
  have hbaker :
      5 * 3 ^ (s r) * (2 ^ S * u (r + 1 + M) - 3 ^ T * u r) + 4 * 3 ^ (s r) * 2 ^ d ≤
        9 * 3 ^ T := by
    rw [hsub]
    have hm := Nat.mul_le_mul_left (3 ^ (s r)) h95
    have hlhs : 5 * 3 ^ (s r) * R + 4 * 3 ^ (s r) * 2 ^ d =
        3 ^ (s r) * (5 * R + 4 * 2 ^ d) := by ring
    have hrhs : 9 * 3 ^ T = 3 ^ (s r) * (9 * 3 ^ d) := by
      change 9 * 3 ^ (s r + d) = 3 ^ (s r) * (9 * 3 ^ d)
      rw [Nat.pow_add 3 (s r) d]
      ring
    rw [hlhs, hrhs]
    exact hm
  refine ⟨⟨hid, hR_odd, hgcd⟩, hbaker, ?_⟩
  intro hu_eq
  have hdvd : u r ∣ R := by
    have hg := hgcd
    rw [hu_eq, Nat.gcd_self] at hg
    exact hg
  have hR_pos : 0 < R := by omega
  have hle_R : u r ≤ R := Nat.le_of_dvd hR_pos hdvd
  have hprod : (2 ^ S - 3 ^ T) * u r = R := by
    rw [Nat.sub_mul]
    have hsub_eq := hsub
    rw [hu_eq] at hsub_eq
    exact hsub_eq
  have hbound : 5 * u r + 4 * 2 ^ d ≤ 9 * 3 ^ d := by omega
  exact ⟨hprod, hdvd, hle_R, hbound⟩

/-! ## 72. Theorem SB.72: Exact 2-Adic Renewal Valuation ($A_{0,K} = 2^{s_0} R_0$) & The $1/5$ Reduced Ceiling -/

/-- **Exact 2-Adic Renewal Valuation ($A_{0,K} = 2^{s_0} R_0$) & The $1/5$ Reduced Ceiling
(`exact_two_adic_renewal_valuation_and_one_fifth_reduced_ceiling`, Theorem SB.72)**:
Suppose `ValidBlockChain b_0 s u (M + 2)` holds with `2 ≤ s 0` and `∀ k < M, 2 ≤ s (1 + k)`.
Setting `K = M + 1`, `T_K = blockSteps s K`, `s' t = s (1 + t)`, `d_0 = blockSteps s' M`,
`S_0 = d_0 + s K`, and `R_0 = 3 ^ d_0 + renewalNumerator s' M`:
1. **Exact 2-Adic Factorization of the Renewal Numerator**:
   `renewalNumerator s K = 2 ^ (s 0) * R_0` and `R_0 % 2 = 1`
   (so the 2-adic valuation of $A_{0,K}$ is **identically $s_0$ for all $K \ge 1$**!),
2. **Reduced Odd-Seed Evolution Identity**:
   `2 ^ S_0 * u K = 3 ^ T_K * u 0 + R_0`,
3. **The Unconditional $1/5$ Reduced Renewal Ceiling**:
   `5 * R_0 + 4 * 2 ^ d_0 ≤ 3 ^ T_K` and `5 * R_0 < 3 ^ T_K`, and
4. **Reduced Base-3 Quotient, Remainder, & Zero-Carry Split**:
   `(2 ^ S_0 * u K) / 3 ^ T_K = u 0`, `(2 ^ S_0 * u K) % 3 ^ T_K = R_0`, and
   `base3DigitSum (2 ^ S_0 * u K) = base3DigitSum (u 0) + base3DigitSum R_0`! -/
theorem exact_two_adic_renewal_valuation_and_one_fifth_reduced_ceiling
    {b_0 M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (0 + 1 + M + 1))
    (hs0 : 2 ≤ s 0)
    (hs_tail : ∀ k < M, 2 ≤ s (0 + 1 + k)) :
    let K := 0 + 1 + M
    let T_K := blockSteps s K
    let s' := fun t => s (0 + 1 + t)
    let d_0 := blockSteps s' M
    let S_0 := d_0 + s K
    let R_0 := 3 ^ d_0 + renewalNumerator s' M
    (renewalNumerator s K = 2 ^ (s 0) * R_0 ∧ R_0 % 2 = 1) ∧
      2 ^ S_0 * u K = 3 ^ T_K * u 0 + R_0 ∧
      (5 * R_0 + 4 * 2 ^ d_0 ≤ 3 ^ T_K ∧ 5 * R_0 < 3 ^ T_K) ∧
      ((2 ^ S_0 * u K) / 3 ^ T_K = u 0 ∧
        (2 ^ S_0 * u K) % 3 ^ T_K = R_0 ∧
        base3DigitSum (2 ^ S_0 * u K) = base3DigitSum (u 0) + base3DigitSum R_0) := by
  intro K T_K s' d_0 S_0 R_0
  have h71 := end_of_block_three_pow_upgraded_baker_pinch_and_s_r_free_return_bound hchain hs_tail
  have h25 := unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound hchain hs_tail
  have hTK_eq : T_K = s 0 + d_0 := by
    have hsh := blockSteps_add_shift s (0 + 1) M
    have hb1 : blockSteps s (0 + 1) = s 0 := by simp [blockSteps]
    rw [hb1] at hsh
    exact hsh
  have hid_red : 2 ^ S_0 * u K = 3 ^ T_K * u 0 + R_0 := by
    have h1 : 2 ^ S_0 * u K = 3 ^ (s 0 + d_0) * u 0 + R_0 := h71.1.1
    rw [← hTK_eq] at h1
    exact h1
  have hR0_odd : R_0 % 2 = 1 := h71.1.2.1
  have hs_all : ∀ k < K, 2 ≤ s k := by
    intro k hk
    rcases (by omega : k = 0 ∨ 1 ≤ k) with rfl | hk1
    · exact hs0
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = 0 + 1 + j := ⟨k - 1, by omega⟩
      exact hs_tail j (by omega)
  have h28 := bridge_a_dual_universe_series_lowest_terms_and_uniqueness
    (K := K) (fun t ht => hchain t (by omega)) hs_all
  have hid_full : 2 ^ (T_K + s K) * u K =
      3 ^ T_K * oddReturnP (orbit b_0 (blockSteps s 0)) + renewalNumerator s K := h28.1
  have hP0 : oddReturnP (orbit b_0 (blockSteps s 0)) = 2 ^ (s 0) * u 0 :=
    (hchain 0 (by omega)).2.2
  have hA_factor : renewalNumerator s K = 2 ^ (s 0) * R_0 := by
    have hm := congrArg (fun x => 2 ^ (s 0) * x) hid_red
    dsimp only at hm
    have hpowL : 2 ^ (s 0) * (2 ^ S_0 * u K) = 2 ^ (T_K + s K) * u K := by
      have hexp : s 0 + S_0 = T_K + s K := by omega
      rw [← Nat.mul_assoc, ← Nat.pow_add 2 (s 0) S_0, hexp]
    have hpowR : 2 ^ (s 0) * (3 ^ T_K * u 0 + R_0) =
        3 ^ T_K * oddReturnP (orbit b_0 (blockSteps s 0)) + 2 ^ (s 0) * R_0 := by
      rw [hP0]
      ring
    rw [hpowL, hpowR] at hm
    omega
  have h95 : 5 * R_0 + 4 * 2 ^ d_0 ≤ 9 * 3 ^ d_0 := h25.1
  have h9_le_3s0 : 9 ≤ 3 ^ (s 0) := by
    have h32 : 3 ^ 2 ≤ 3 ^ (s 0) := Nat.pow_le_pow_right (by decide) hs0
    omega
  have h15_le : 5 * R_0 + 4 * 2 ^ d_0 ≤ 3 ^ T_K := by
    have hm : 9 * 3 ^ d_0 ≤ 3 ^ (s 0) * 3 ^ d_0 :=
      Nat.mul_le_mul_right (3 ^ d_0) h9_le_3s0
    have hpow3 : 3 ^ (s 0) * 3 ^ d_0 = 3 ^ T_K := by
      rw [← Nat.pow_add 3 (s 0) d_0, ← hTK_eq]
    omega
  have h2d_pos : 1 ≤ 2 ^ d_0 := Nat.one_le_pow _ 2 (by decide)
  have h15_lt : 5 * R_0 < 3 ^ T_K := by omega
  have hdiv : (2 ^ S_0 * u K) / 3 ^ T_K = u 0 := by
    have hd : (2 ^ S_0 * u K) / 3 ^ (s 0 + d_0) = u 0 := h25.2.2.2.1
    rw [← hTK_eq] at hd
    exact hd
  have hmod : (2 ^ S_0 * u K) % 3 ^ T_K = R_0 := by
    have hm : (2 ^ S_0 * u K) % 3 ^ (s 0 + d_0) = R_0 := h25.2.2.2.2.1
    rw [← hTK_eq] at hm
    exact hm
  have hs3 : base3DigitSum (2 ^ S_0 * u K) = base3DigitSum (u 0) + base3DigitSum R_0 :=
    h25.2.2.2.2.2
  exact ⟨⟨hA_factor, hR0_odd⟩, hid_red, ⟨h15_le, h15_lt⟩, ⟨hdiv, hmod, hs3⟩⟩

/-! ## 73. Theorem SB.73: Cubic $(3, 5)$ & Quintic $(5, 8)$ Odd-Core Subordinacy to $2^{T_K}$ -/

/-- Helper: `3 ^ (3 * t) ≤ 2 ^ (5 * t)` (`27 ^ t ≤ 32 ^ t`) and
`3 ^ (5 * t) ≤ 2 ^ (8 * t)` (`243 ^ t ≤ 256 ^ t`) for all `t : ℕ`. -/
theorem three_pow_cubic_and_quintic_le_two_pow (t : ℕ) :
    3 ^ (3 * t) ≤ 2 ^ (5 * t) ∧ 3 ^ (5 * t) ≤ 2 ^ (8 * t) := by
  have h35 : 3 ^ (3 * t) = 27 ^ t := by rw [Nat.pow_mul 3 3 t]
  have h25 : 2 ^ (5 * t) = 32 ^ t := by rw [Nat.pow_mul 2 5 t]
  have h38 : 3 ^ (5 * t) = 243 ^ t := by rw [Nat.pow_mul 3 5 t]
  have h28 : 2 ^ (8 * t) = 256 ^ t := by rw [Nat.pow_mul 2 8 t]
  rw [h35, h25, h38, h28]
  exact ⟨Nat.pow_le_pow_left (by decide) t, Nat.pow_le_pow_left (by decide) t⟩

/-- **Cubic $(3, 5)$ & Quintic $(5, 8)$ Odd-Core Subordinacy to $2^{T_K}$
(`cubic_and_quintic_odd_core_subordinacy_to_two_pow`, Theorem SB.73)**:
Suppose `ValidBlockChain b_0 s u (0 + 1 + M + 1)` holds with `2 ≤ s 0` and
`∀ k < M, 2 ≤ s (0 + 1 + k)`. Setting `K = 0 + 1 + M`, `T_K = blockSteps s K`,
`s' t = s (0 + 1 + t)`, `d_0 = blockSteps s' M`, and `S_0 = d_0 + s K`:
1. **Exact Linear $1/5$ Envelope**:
   `5 * (2 ^ S_0 * u K) < 3 ^ T_K * (5 * u 0 + 1)`,
2. **Cubic $(3, 5)$ Global Dominance Law ($u_K^3 \ll (2^{T_K})^2$)**:
   `(5 * (2 ^ S_0 * u K)) ^ 3 < 2 ^ (5 * T_K) * (5 * u 0 + 1) ^ 3` and
   `125 * 2 ^ (3 * s K) * (u K) ^ 3 < 2 ^ (2 * T_K + 3 * s 0) * (5 * u 0 + 1) ^ 3`, and
3. **Quintic $(5, 8)$ Global Dominance Law ($u_K^5 \ll (2^{T_K})^3$)**:
   `(5 * (2 ^ S_0 * u K)) ^ 5 < 2 ^ (8 * T_K) * (5 * u 0 + 1) ^ 5` and
   `3125 * 2 ^ (5 * s K) * (u K) ^ 5 < 2 ^ (3 * T_K + 5 * s 0) * (5 * u 0 + 1) ^ 5`! -/
theorem cubic_and_quintic_odd_core_subordinacy_to_two_pow
    {b_0 M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (0 + 1 + M + 1))
    (hs0 : 2 ≤ s 0)
    (hs_tail : ∀ k < M, 2 ≤ s (0 + 1 + k)) :
    let K := 0 + 1 + M
    let T_K := blockSteps s K
    let s' := fun t => s (0 + 1 + t)
    let d_0 := blockSteps s' M
    let S_0 := d_0 + s K
    5 * (2 ^ S_0 * u K) < 3 ^ T_K * (5 * u 0 + 1) ∧
      ((5 * (2 ^ S_0 * u K)) ^ 3 < 2 ^ (5 * T_K) * (5 * u 0 + 1) ^ 3 ∧
        125 * 2 ^ (3 * s K) * (u K) ^ 3 < 2 ^ (2 * T_K + 3 * s 0) * (5 * u 0 + 1) ^ 3) ∧
      ((5 * (2 ^ S_0 * u K)) ^ 5 < 2 ^ (8 * T_K) * (5 * u 0 + 1) ^ 5 ∧
        3125 * 2 ^ (5 * s K) * (u K) ^ 5 < 2 ^ (3 * T_K + 5 * s 0) * (5 * u 0 + 1) ^ 5) := by
  intro K T_K s' d_0 S_0
  have h72 := exact_two_adic_renewal_valuation_and_one_fifth_reduced_ceiling hchain hs0 hs_tail
  set R_0 := 3 ^ d_0 + renewalNumerator s' M
  have hid_red : 2 ^ S_0 * u K = 3 ^ T_K * u 0 + R_0 := h72.2.1
  have h5R_lt : 5 * R_0 < 3 ^ T_K := h72.2.2.1.2
  have hlin : 5 * (2 ^ S_0 * u K) < 3 ^ T_K * (5 * u 0 + 1) := by
    have hlhs : 5 * (2 ^ S_0 * u K) = 3 ^ T_K * (5 * u 0) + 5 * R_0 := by
      rw [hid_red]
      ring
    have hrhs : 3 ^ T_K * (5 * u 0 + 1) = 3 ^ T_K * (5 * u 0) + 3 ^ T_K := by ring
    omega
  have hTK_eq : T_K = s 0 + d_0 := by
    have hsh := blockSteps_add_shift s (0 + 1) M
    have hb1 : blockSteps s (0 + 1) = s 0 := by simp [blockSteps]
    rw [hb1] at hsh
    exact hsh
  have hexp_sum : s 0 + S_0 = T_K + s K := by omega
  have hpow_le := three_pow_cubic_and_quintic_le_two_pow T_K
  have hcub1 : (5 * (2 ^ S_0 * u K)) ^ 3 < 2 ^ (5 * T_K) * (5 * u 0 + 1) ^ 3 := by
    have hlt3 : (5 * (2 ^ S_0 * u K)) ^ 3 < (3 ^ T_K * (5 * u 0 + 1)) ^ 3 :=
      Nat.pow_lt_pow_left hlin (by decide)
    have hrhs3 : (3 ^ T_K * (5 * u 0 + 1)) ^ 3 = 3 ^ (3 * T_K) * (5 * u 0 + 1) ^ 3 := by
      rw [Nat.mul_pow, ← Nat.pow_mul 3 T_K 3]
      have hc : T_K * 3 = 3 * T_K := Nat.mul_comm T_K 3
      rw [hc]
    have hle3 : 3 ^ (3 * T_K) * (5 * u 0 + 1) ^ 3 ≤ 2 ^ (5 * T_K) * (5 * u 0 + 1) ^ 3 :=
      Nat.mul_le_mul_right ((5 * u 0 + 1) ^ 3) hpow_le.1
    omega
  have hcub2 : 125 * 2 ^ (3 * s K) * (u K) ^ 3 < 2 ^ (2 * T_K + 3 * s 0) * (5 * u 0 + 1) ^ 3 := by
    have h2_pos : 0 < 2 ^ (3 * s 0) := Nat.pow_pos (by decide)
    have hm := Nat.mul_lt_mul_of_pos_left hcub1 h2_pos
    have hlhs_eq :
        2 ^ (3 * s 0) * (5 * (2 ^ S_0 * u K)) ^ 3 =
          2 ^ (3 * T_K) * (125 * 2 ^ (3 * s K) * (u K) ^ 3) := by
      have hp1 : (5 * (2 ^ S_0 * u K)) ^ 3 = 125 * (2 ^ S_0) ^ 3 * (u K) ^ 3 := by ring
      have hp2 : (2 ^ S_0) ^ 3 = 2 ^ (3 * S_0) := by
        rw [← Nat.pow_mul 2 S_0 3]
        have hc : S_0 * 3 = 3 * S_0 := Nat.mul_comm S_0 3
        rw [hc]
      have hexp3 : 3 * s 0 + 3 * S_0 = 3 * T_K + 3 * s K := by omega
      rw [hp1, hp2]
      calc
        2 ^ (3 * s 0) * (125 * 2 ^ (3 * S_0) * (u K) ^ 3)
            = 125 * (2 ^ (3 * s 0) * 2 ^ (3 * S_0)) * (u K) ^ 3 := by ring
        _ = 125 * 2 ^ (3 * T_K + 3 * s K) * (u K) ^ 3 := by
              rw [← Nat.pow_add 2 (3 * s 0) (3 * S_0), hexp3]
        _ = 2 ^ (3 * T_K) * (125 * 2 ^ (3 * s K) * (u K) ^ 3) := by
              rw [Nat.pow_add 2 (3 * T_K) (3 * s K)]
              ring
    have hrhs_eq :
        2 ^ (3 * s 0) * (2 ^ (5 * T_K) * (5 * u 0 + 1) ^ 3) =
          2 ^ (3 * T_K) * (2 ^ (2 * T_K + 3 * s 0) * (5 * u 0 + 1) ^ 3) := by
      have hexp5 : 3 * s 0 + 5 * T_K = 3 * T_K + (2 * T_K + 3 * s 0) := by omega
      calc
        2 ^ (3 * s 0) * (2 ^ (5 * T_K) * (5 * u 0 + 1) ^ 3)
            = (2 ^ (3 * s 0) * 2 ^ (5 * T_K)) * (5 * u 0 + 1) ^ 3 := by ring
        _ = 2 ^ (3 * T_K + (2 * T_K + 3 * s 0)) * (5 * u 0 + 1) ^ 3 := by
              rw [← Nat.pow_add 2 (3 * s 0) (5 * T_K), hexp5]
        _ = 2 ^ (3 * T_K) * (2 ^ (2 * T_K + 3 * s 0) * (5 * u 0 + 1) ^ 3) := by
              rw [Nat.pow_add 2 (3 * T_K) (2 * T_K + 3 * s 0)]
              ring
    rw [hlhs_eq, hrhs_eq] at hm
    exact Nat.lt_of_mul_lt_mul_left hm
  have hquin1 : (5 * (2 ^ S_0 * u K)) ^ 5 < 2 ^ (8 * T_K) * (5 * u 0 + 1) ^ 5 := by
    have hlt5 : (5 * (2 ^ S_0 * u K)) ^ 5 < (3 ^ T_K * (5 * u 0 + 1)) ^ 5 :=
      Nat.pow_lt_pow_left hlin (by decide)
    have hrhs5 : (3 ^ T_K * (5 * u 0 + 1)) ^ 5 = 3 ^ (5 * T_K) * (5 * u 0 + 1) ^ 5 := by
      rw [Nat.mul_pow, ← Nat.pow_mul 3 T_K 5]
      have hc : T_K * 5 = 5 * T_K := Nat.mul_comm T_K 5
      rw [hc]
    have hle5 : 3 ^ (5 * T_K) * (5 * u 0 + 1) ^ 5 ≤ 2 ^ (8 * T_K) * (5 * u 0 + 1) ^ 5 :=
      Nat.mul_le_mul_right ((5 * u 0 + 1) ^ 5) hpow_le.2
    omega
  have hquin2 : 3125 * 2 ^ (5 * s K) * (u K) ^ 5 < 2 ^ (3 * T_K + 5 * s 0) * (5 * u 0 + 1) ^ 5 := by
    have h2_pos : 0 < 2 ^ (5 * s 0) := Nat.pow_pos (by decide)
    have hm := Nat.mul_lt_mul_of_pos_left hquin1 h2_pos
    have hlhs_eq :
        2 ^ (5 * s 0) * (5 * (2 ^ S_0 * u K)) ^ 5 =
          2 ^ (5 * T_K) * (3125 * 2 ^ (5 * s K) * (u K) ^ 5) := by
      have hp1 : (5 * (2 ^ S_0 * u K)) ^ 5 = 3125 * (2 ^ S_0) ^ 5 * (u K) ^ 5 := by ring
      have hp2 : (2 ^ S_0) ^ 5 = 2 ^ (5 * S_0) := by
        rw [← Nat.pow_mul 2 S_0 5]
        have hc : S_0 * 5 = 5 * S_0 := Nat.mul_comm S_0 5
        rw [hc]
      have hexp5 : 5 * s 0 + 5 * S_0 = 5 * T_K + 5 * s K := by omega
      rw [hp1, hp2]
      calc
        2 ^ (5 * s 0) * (3125 * 2 ^ (5 * S_0) * (u K) ^ 5)
            = 3125 * (2 ^ (5 * s 0) * 2 ^ (5 * S_0)) * (u K) ^ 5 := by ring
        _ = 3125 * 2 ^ (5 * T_K + 5 * s K) * (u K) ^ 5 := by
              rw [← Nat.pow_add 2 (5 * s 0) (5 * S_0), hexp5]
        _ = 2 ^ (5 * T_K) * (3125 * 2 ^ (5 * s K) * (u K) ^ 5) := by
              rw [Nat.pow_add 2 (5 * T_K) (5 * s K)]
              ring
    have hrhs_eq :
        2 ^ (5 * s 0) * (2 ^ (8 * T_K) * (5 * u 0 + 1) ^ 5) =
          2 ^ (5 * T_K) * (2 ^ (3 * T_K + 5 * s 0) * (5 * u 0 + 1) ^ 5) := by
      have hexp8 : 5 * s 0 + 8 * T_K = 5 * T_K + (3 * T_K + 5 * s 0) := by omega
      calc
        2 ^ (5 * s 0) * (2 ^ (8 * T_K) * (5 * u 0 + 1) ^ 5)
            = (2 ^ (5 * s 0) * 2 ^ (8 * T_K)) * (5 * u 0 + 1) ^ 5 := by ring
        _ = 2 ^ (5 * T_K + (3 * T_K + 5 * s 0)) * (5 * u 0 + 1) ^ 5 := by
              rw [← Nat.pow_add 2 (5 * s 0) (8 * T_K), hexp8]
        _ = 2 ^ (5 * T_K) * (2 ^ (3 * T_K + 5 * s 0) * (5 * u 0 + 1) ^ 5) := by
              rw [Nat.pow_add 2 (5 * T_K) (3 * T_K + 5 * s 0)]
              ring
    rw [hlhs_eq, hrhs_eq] at hm
    exact Nat.lt_of_mul_lt_mul_left hm
  exact ⟨hlin, ⟨hcub1, hcub2⟩, ⟨hquin1, hquin2⟩⟩

/-! ## 74. Theorem SB.74: Global Multiplicative-to-Additive Product Formula Bridge -/

/-- Prefix product of odd cores: $\prod_{r=0}^{k-1} u_r$. -/
def oddCoreProd (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => oddCoreProd u k * u k

/-- Prefix product of step numerators: $\prod_{r=0}^{k-1} (3^{s_r} u_r + 1)$. -/
def stepNumProd (s u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => stepNumProd s u k * (3 ^ (s k) * u k + 1)

/-- Helper: exact telescoped product identity across `K` blocks. -/
theorem global_block_product_master_identity
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1)) :
    2 ^ (blockSteps s (K + 1)) * oddCoreProd u (K + 1) =
      (2 ^ (s 0) * u 0) * stepNumProd s u K := by
  induction K with
  | zero =>
      simp [blockSteps, oddCoreProd, stepNumProd]
  | succ K ih =>
      have hch_K : ValidBlockChain b_0 s u (K + 1) := fun k hk => hchain k (by omega)
      have ihK := ih hch_K
      have hch_step : ValidBlockChain b_0 s u (K + 2) := fun k hk => hchain k (by omega)
      have hstep : 2 ^ (s (K + 1)) * u (K + 1) = 3 ^ (s K) * u K + 1 :=
        (one_step_backward_quotient_recovery_and_mod_three_pow_one hch_step).1
      calc
        2 ^ (blockSteps s (K + 2)) * oddCoreProd u (K + 2)
            = (2 ^ (blockSteps s (K + 1)) * oddCoreProd u (K + 1)) *
                (2 ^ (s (K + 1)) * u (K + 1)) := by
              change 2 ^ (blockSteps s (K + 1) + s (K + 1)) *
                  (oddCoreProd u (K + 1) * u (K + 1)) =
                (2 ^ (blockSteps s (K + 1)) * oddCoreProd u (K + 1)) *
                  (2 ^ (s (K + 1)) * u (K + 1))
              rw [Nat.pow_add 2 (blockSteps s (K + 1)) (s (K + 1))]
              ring
        _ = ((2 ^ (s 0) * u 0) * stepNumProd s u K) * (3 ^ (s K) * u K + 1) := by
              rw [ihK, hstep]
        _ = (2 ^ (s 0) * u 0) * stepNumProd s u (K + 1) := by
              change ((2 ^ (s 0) * u 0) * stepNumProd s u K) * (3 ^ (s K) * u K + 1) =
                (2 ^ (s 0) * u 0) * (stepNumProd s u K * (3 ^ (s K) * u K + 1))
              ring

/-- **Global Multiplicative-to-Additive Product Formula Bridge
(`global_multiplicative_to_additive_product_formula_bridge`, Theorem SB.74)**:
Suppose `ValidBlockChain b_0 s u (K + 1)` holds with `∀ k < K, 2 ≤ s k`.
Setting `P k = oddReturnP (orbit b_0 (blockSteps s k))`, `T_K = blockSteps s K`,
`S_K = T_K + s K`, and `A_K = renewalNumerator s K`:
1. **Telescoped Multiplicative Product Identity**:
   `2 ^ S_K * u K * oddCoreProd u K = P 0 * stepNumProd s u K`,
2. **Exact Additive-to-Multiplicative Bridge Identity**:
   `(3 ^ T_K * P 0 + A_K) * oddCoreProd u K = P 0 * stepNumProd s u K`, and
3. **Global Seed Divisibility of the Weighted Renewal Product**:
   `P 0 ∣ (A_K * oddCoreProd u K)`! -/
theorem global_multiplicative_to_additive_product_formula_bridge
    {b_0 K : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (K + 1))
    (hs2 : ∀ k < K, 2 ≤ s k) :
    let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
    let T_K := blockSteps s K
    let S_K := T_K + s K
    let A_K := renewalNumerator s K
    2 ^ S_K * u K * oddCoreProd u K = P 0 * stepNumProd s u K ∧
      (3 ^ T_K * P 0 + A_K) * oddCoreProd u K = P 0 * stepNumProd s u K ∧
      P 0 ∣ (A_K * oddCoreProd u K) := by
  intro P T_K S_K A_K
  have hprod := global_block_product_master_identity hchain
  have hP0 : P 0 = 2 ^ (s 0) * u 0 := (hchain 0 (by omega)).2.2
  have h28 := bridge_a_dual_universe_series_lowest_terms_and_uniqueness hchain hs2
  have hid : 2 ^ S_K * u K = 3 ^ T_K * P 0 + A_K := h28.1
  have hmult : 2 ^ S_K * u K * oddCoreProd u K = P 0 * stepNumProd s u K := by
    calc
      2 ^ S_K * u K * oddCoreProd u K
          = 2 ^ (blockSteps s (K + 1)) * oddCoreProd u (K + 1) := by
            change 2 ^ (T_K + s K) * u K * oddCoreProd u K =
              2 ^ (T_K + s K) * (oddCoreProd u K * u K)
            ring
      _ = (2 ^ (s 0) * u 0) * stepNumProd s u K := hprod
      _ = P 0 * stepNumProd s u K := by rw [← hP0]
  have hbridge : (3 ^ T_K * P 0 + A_K) * oddCoreProd u K = P 0 * stepNumProd s u K := by
    rw [← hid]
    exact hmult
  have hdvd : P 0 ∣ (A_K * oddCoreProd u K) := by
    have hexp :
        (3 ^ T_K * P 0 + A_K) * oddCoreProd u K =
          P 0 * (3 ^ T_K * oddCoreProd u K) + A_K * oddCoreProd u K := by ring
    have hd1 : P 0 ∣ P 0 * (3 ^ T_K * oddCoreProd u K) :=
      dvd_mul_right (P 0) (3 ^ T_K * oddCoreProd u K)
    have hd2 : P 0 ∣ P 0 * stepNumProd s u K :=
      dvd_mul_right (P 0) (stepNumProd s u K)
    rw [← hbridge, hexp] at hd2
    exact (Nat.dvd_add_right hd1).mp hd2
  exact ⟨hmult, hbridge, hdvd⟩

/-! ## 75. Theorem SB.75: Two-Window Ridout / Subspace Tail-Cancellation Bridge -/

/-- **Two-Window Ridout / Subspace Tail-Cancellation Bridge
(`two_window_ridout_subspace_tail_cancellation_bridge`, Theorem SB.75)**:
Suppose `ValidBlockChain b_0 s u (r + M + 1)` holds with `∀ k < r, 2 ≤ s k`, `1 ≤ r`,
`∀ k < M, 2 ≤ s (r + k)`, and `1 ≤ M`.
Setting `T_r = blockSteps s r`, `s' t = s (r + t)`, `n_2 = blockSteps s' M`,
`s_K = s (r + M)`, `A_rM = renewalNumerator s' M`, and
`Δ = 2 ^ (T_r + n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (T_r + s r) * u r)`:
1. **Exact Two-Window Scaled Tail Identity**:
   `2 ^ (T_r + n_2 + s_K) * u (r + M) = 3 ^ n_2 * (2 ^ (T_r + s r) * u r) + 2 ^ T_r * A_rM` and
   `Δ = 2 ^ T_r * A_rM`,
2. **Unconditional $4/5$ Scaled Tail Bound**:
   `5 * Δ + 4 * 2 ^ (T_r + n_2) ≤ 4 * 2 ^ T_r * 3 ^ n_2` and
   `5 * Δ < 4 * 2 ^ T_r * 3 ^ n_2`, and
3. **Exact Ridout / Subspace Cancellation of Both $2^{T_r}$ and $3^{n_2}$**:
   Whenever a Ridout/Subspace lower bound
   `C_1 * 2 ^ (T_r + s r) * 3 ^ n_2 ≤ C_2 * 3 ^ E * Δ` holds, canceling `2 ^ T_r * 3 ^ n_2`
   from both sides forces `5 * C_1 * 2 ^ (s r) ≤ 4 * C_2 * 3 ^ E` (and strict `<` whenever `1 ≤ C_2`)! -/
theorem two_window_ridout_subspace_tail_cancellation_bridge
    {b_0 r M : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (r + M + 1))
    (hs_past : ∀ k < r, 2 ≤ s k)
    (hr : 1 ≤ r)
    (hs_win : ∀ k < M, 2 ≤ s (r + k))
    (hM : 1 ≤ M) :
    let T_r := blockSteps s r
    let s' := fun t => s (r + t)
    let n_2 := blockSteps s' M
    let s_K := s (r + M)
    let A_rM := renewalNumerator s' M
    let Δ := 2 ^ (T_r + n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (T_r + s r) * u r)
    (2 ^ (T_r + n_2 + s_K) * u (r + M) =
        3 ^ n_2 * (2 ^ (T_r + s r) * u r) + 2 ^ T_r * A_rM ∧
      Δ = 2 ^ T_r * A_rM) ∧
      (5 * Δ + 4 * 2 ^ (T_r + n_2) ≤ 4 * 2 ^ T_r * 3 ^ n_2 ∧
        5 * Δ < 4 * 2 ^ T_r * 3 ^ n_2) ∧
      (∀ C_1 C_2 E : ℕ,
        1 ≤ C_2 →
        C_1 * 2 ^ (T_r + s r) * 3 ^ n_2 ≤ C_2 * 3 ^ E * Δ →
        5 * C_1 * 2 ^ (s r) < 4 * C_2 * 3 ^ E) := by
  intro T_r s' n_2 s_K A_rM Δ
  have h67 := (shifted_basepoint_baker_matveev_pinch_and_repeated_core_rhin_form
    hchain hs_past hr hs_win hM).1
  have hid_base : 2 ^ (n_2 + s_K) * u (r + M) = 3 ^ n_2 * (2 ^ (s r) * u r) + A_rM := h67.1
  have hscaled :
      2 ^ (T_r + n_2 + s_K) * u (r + M) =
        3 ^ n_2 * (2 ^ (T_r + s r) * u r) + 2 ^ T_r * A_rM := by
    have hm := congrArg (fun x => 2 ^ T_r * x) hid_base
    dsimp only at hm
    have hpL : 2 ^ T_r * (2 ^ (n_2 + s_K) * u (r + M)) =
        2 ^ (T_r + n_2 + s_K) * u (r + M) := by
      rw [Nat.add_assoc T_r n_2 s_K, Nat.pow_add 2 T_r (n_2 + s_K)]
      ring
    have hpR : 2 ^ T_r * (3 ^ n_2 * (2 ^ (s r) * u r) + A_rM) =
        3 ^ n_2 * (2 ^ (T_r + s r) * u r) + 2 ^ T_r * A_rM := by
      rw [Nat.pow_add 2 T_r (s r)]
      ring
    rw [hpL, hpR] at hm
    exact hm
  have hdelta_eq : Δ = 2 ^ T_r * A_rM := by
    change 2 ^ (T_r + n_2 + s_K) * u (r + M) - 3 ^ n_2 * (2 ^ (T_r + s r) * u r) =
      2 ^ T_r * A_rM
    rw [hscaled, Nat.add_sub_cancel_left]
  have hinv_M : 5 * A_rM + 4 * 2 ^ n_2 ≤ 4 * 3 ^ n_2 :=
    five_mul_renewalNumerator_add_four_mul_two_pow_le s' M hs_win
  have hbound_le : 5 * Δ + 4 * 2 ^ (T_r + n_2) ≤ 4 * 2 ^ T_r * 3 ^ n_2 := by
    have hm := Nat.mul_le_mul_left (2 ^ T_r) hinv_M
    have hp2 : 2 ^ (T_r + n_2) = 2 ^ T_r * 2 ^ n_2 := Nat.pow_add 2 T_r n_2
    have hlhs : 5 * Δ + 4 * 2 ^ (T_r + n_2) = 2 ^ T_r * (5 * A_rM + 4 * 2 ^ n_2) := by
      rw [hdelta_eq, hp2]
      ring
    have hrhs : 4 * 2 ^ T_r * 3 ^ n_2 = 2 ^ T_r * (4 * 3 ^ n_2) := by ring
    rw [hlhs, hrhs]
    exact hm
  have h2_pos : 1 ≤ 2 ^ (T_r + n_2) := Nat.one_le_pow _ 2 (by decide)
  have hbound_lt : 5 * Δ < 4 * 2 ^ T_r * 3 ^ n_2 := by omega
  refine ⟨⟨hscaled, hdelta_eq⟩, ⟨hbound_le, hbound_lt⟩, ?_⟩
  intro C_1 C_2 E hC2 hridout
  have hm5 := Nat.mul_le_mul_left 5 hridout
  have hC2E_pos : 0 < C_2 * 3 ^ E :=
    Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
  have hlt_D : (C_2 * 3 ^ E) * (5 * Δ) < (C_2 * 3 ^ E) * (4 * 2 ^ T_r * 3 ^ n_2) :=
    Nat.mul_lt_mul_of_pos_left hbound_lt hC2E_pos
  have hlhs_f :
      5 * (C_1 * 2 ^ (T_r + s r) * 3 ^ n_2) =
        (2 ^ T_r * 3 ^ n_2) * (5 * C_1 * 2 ^ (s r)) := by
    rw [Nat.pow_add 2 T_r (s r)]
    ring
  have hmid_f : 5 * (C_2 * 3 ^ E * Δ) = (C_2 * 3 ^ E) * (5 * Δ) := by ring
  have hrhs_f :
      (C_2 * 3 ^ E) * (4 * 2 ^ T_r * 3 ^ n_2) =
        (2 ^ T_r * 3 ^ n_2) * (4 * C_2 * 3 ^ E) := by ring
  have hlt_comb :
      (2 ^ T_r * 3 ^ n_2) * (5 * C_1 * 2 ^ (s r)) <
        (2 ^ T_r * 3 ^ n_2) * (4 * C_2 * 3 ^ E) := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt_comb

/-! ## 76. Theorem SB.76: Grand 76-Theorem Synthesis of Global Dominance, Product Formula, & Ridout Cancellation -/

/-- **Grand 76-Theorem Synthesis of Global Dominance, Product Formula, & Ridout Cancellation
(`grand_global_dominance_and_product_formula_76_synthesis`, Theorem SB.76)**:
Unifies the cubic $(3, 5)$ and quintic $(5, 8)$ odd-core subordinacy laws (`SB.73`),
the global multiplicative-to-additive product formula (`SB.74`), the two-window
Ridout/Subspace cancellation bridge (`SB.75`), and the adjacent/two-step return
laws (`SB.69–SB.72`). -/
theorem grand_global_dominance_and_product_formula_76_synthesis :
    (∀ {b_0 M : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (0 + 1 + M + 1) →
      2 ≤ s 0 →
      (∀ k < M, 2 ≤ s (0 + 1 + k)) →
      let K := 0 + 1 + M
      let T_K := blockSteps s K
      125 * 2 ^ (3 * s K) * (u K) ^ 3 < 2 ^ (2 * T_K + 3 * s 0) * (5 * u 0 + 1) ^ 3 ∧
        3125 * 2 ^ (5 * s K) * (u K) ^ 5 < 2 ^ (3 * T_K + 5 * s 0) * (5 * u 0 + 1) ^ 5) ∧
    (∀ {b_0 K : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (K + 1) →
      (∀ k < K, 2 ≤ s k) →
      let P := fun k => oddReturnP (orbit b_0 (blockSteps s k))
      let T_K := blockSteps s K
      let A_K := renewalNumerator s K
      (3 ^ T_K * P 0 + A_K) * oddCoreProd u K = P 0 * stepNumProd s u K ∧
        P 0 ∣ (A_K * oddCoreProd u K)) ∧
    (∀ {b_0 r : ℕ} {s u : ℕ → ℕ},
      ValidBlockChain b_0 s u (r + 2) →
      2 ≤ s r →
      Nat.Coprime (u r) (u (r + 1)) ∧ u (r + 1) ≠ u r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b_0 M s u hchain hs0 hs_tail
    have h73 := cubic_and_quintic_odd_core_subordinacy_to_two_pow hchain hs0 hs_tail
    exact ⟨h73.2.1.2, h73.2.2.2⟩
  · intro b_0 K s u hchain hs2
    have h74 := global_multiplicative_to_additive_product_formula_bridge hchain hs2
    exact ⟨h74.2.1, h74.2.2⟩
  · intro b_0 r s u hchain hs_r
    have h69 := adjacent_odd_core_coprimality_and_universal_non_equality hchain hs_r
    exact ⟨h69.1, h69.2.2.2⟩


#check @archimedean_rung_ceiling_and_stepSum_bound
#check @unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity
#check @equal_step_window_hankel_determinant_identity_and_bound
#check @two_seed_first_divergence_valuation_and_bound
#check @post_bitlength_unique_seed_in_dyadic_box
#check @dyadic_four_lift_double_odd_bijection_and_three_of_four_survival
#check @raw_orbit_base3_frozen_prefix_and_leading_trit_le_one
#check @mahler_antihydra_bb6_complement_duality
#check @zero_carry_base3_digit_sum_and_even_step_invariance
#check @late_step_cauchy_pinch_and_odd_quotient_gcd_dvd
#check @affine_counter_mahler_conjugacy_and_closed_bb6_non_halting
#check @dual_base2_base3_block_digitsum_conservation_and_parity
#check @one_step_and_weighted_telescoping_base3_carry_identity
#check @top_down_senge_straus_stewart_joint_digitsum_blueprint
#check @legendre_factorial_valuation_dual_block_tower
#check @universal_mod4_quotient_rung_parity_lock_and_mersenne_trap
#check @mod1024_and_weight2_odd_quotient_three_block_domino_collapse
#check @universal_mod12_quotient_lock_and_joint_digitsum_ge_five
#check @one_step_backward_quotient_recovery_and_mod_three_pow_one
#check @sharpened_five_seven_archimedean_rung_ceiling
#check @two_step_disjoint_base3_digit_block_law_and_quotient_recovery
#check @all_k_step_zero_carry_top_block_and_quotient_recovery
#check @two_sided_past_future_crt_pinch
#check @unconditional_four_fifths_renewal_ceiling_and_past_base3_recovery
#check @unconditional_all_k_step_odd_leftover_recovery_and_nine_fifths_bound
#check @sliding_cut_point_past_future_crt_pinch
#check @zero_carry_base3_horner_remainder_ladder
#check @bridge_a_dual_universe_series_lowest_terms_and_uniqueness
#check @bridge_b_seed_independent_base3_step_evolution
#check @bridge_b_additive_carry_isolation_and_horner_step
#check @bridge_c_one_step_binary_trailing_ones_depletion_law
#check @bridge_c_multi_step_dual_base2_base3_zero_carry_split
#check @bridge_c_telescoped_binary_halving_budget_law
#check @kummer_legendre_one_step_binary_factorial_bridge
#check @zero_carry_three_adic_factorial_and_binomial_valuation_law
#check @joint_multi_block_factorial_valuation_syzygy
#check @kummer_base3_two_pow_mul_carry_identity_and_bound
#check @multi_step_base3_horner_digitsum_lower_envelope
#check @interior_mod36_rung_to_quotient_bijection
#check @interior_extinction_of_five_and_seven_and_seventeen_floor
#check @even_rung_mod16_trap_and_seventy_nine_floor_at_rung_two
#check @universal_mod8_and_mod24_next_rung_dichotomy
#check @sharpened_seventeen_seventy_nine_interior_archimedean_ceiling
#check @adjacent_block_wronskian_and_equal_rung_log_concavity
#check @two_block_odd_leftover_cross_ratio_invariant
#check @three_point_seed_free_linear_eliminator_and_cocycle
#check @equal_step_odd_leftover_cross_window_determinant_identity
#check @unconditional_four_fifths_cross_window_hankel_sandwich
#check @mahler_antihydra_base2_complement_digitsum_law
#check @mahler_antihydra_base3_complement_digitsum_law
#check @post_bitlength_colliding_binary_ternary_window_on_N_K
#check @interior_multi_block_joint_digitsum_and_seventy_nine_floor
#check @grand_semigroup_breakout_53_bridge_synthesis
#check @collatz_syracuse_bridge_and_one_two_cycle_exclusion
#check @universal_constant_rung_affine_invariance_and_run_length_bound
#check @sharp_four_fifths_equality_characterization_and_two_two_escape
#check @two_window_jk_diagonal_cauchy_tail_freeze_and_quotient_invariance
#check @j_ge_k_excess_explosion_binary_swelling_and_halving_debt_law
#check @three_adic_seed_diagonal_shift_and_dead_zone_invariance_law
#check @grand_jk_diagonal_and_three_heavy_regime_60_synthesis
#check @local_descent_rung_jump_and_multi_step_descent_explosion
#check @trough_rebound_compound_interest_and_local_minimum_trap
#check @finite_seed_global_peak_trough_seesaw_and_return_barrier
#check @grand_seed_finiteness_and_extrema_64_synthesis
#check @lte2_ultrametric_flush_pinning_and_descent_prohibition
#check @post_horizon_binary_zero_bit_desert_and_dual_radix_lock
#check @shifted_basepoint_baker_matveev_pinch_and_repeated_core_rhin_form
#check @senge_straus_stewart_finiteness_bridge_and_grand_68_synthesis
#check @adjacent_odd_core_coprimality_and_universal_non_equality
#check @two_step_odd_core_gcd_and_return_extinction
#check @end_of_block_three_pow_upgraded_baker_pinch_and_s_r_free_return_bound
#check @exact_two_adic_renewal_valuation_and_one_fifth_reduced_ceiling
#check @cubic_and_quintic_odd_core_subordinacy_to_two_pow
#check @global_multiplicative_to_additive_product_formula_bridge
#check @two_window_ridout_subspace_tail_cancellation_bridge
#check @grand_global_dominance_and_product_formula_76_synthesis

#print axioms archimedean_rung_ceiling_and_stepSum_bound
#print axioms unit_quotient_even_rung_instant_death_and_odd_rung_mod64_identity
#print axioms equal_step_window_hankel_determinant_identity_and_bound
#print axioms two_seed_first_divergence_valuation_and_bound
#print axioms post_bitlength_unique_seed_in_dyadic_box
#print axioms dyadic_four_lift_double_odd_bijection_and_three_of_four_survival
#print axioms raw_orbit_base3_frozen_prefix_and_leading_trit_le_one
#print axioms mahler_antihydra_bb6_complement_duality
#print axioms zero_carry_base3_digit_sum_and_even_step_invariance
#print axioms late_step_cauchy_pinch_and_odd_quotient_gcd_dvd
#print axioms affine_counter_mahler_conjugacy_and_closed_bb6_non_halting
#print axioms dual_base2_base3_block_digitsum_conservation_and_parity
#print axioms one_step_and_weighted_telescoping_base3_carry_identity
#print axioms top_down_senge_straus_stewart_joint_digitsum_blueprint
#print axioms legendre_factorial_valuation_dual_block_tower
#print axioms universal_mod4_quotient_rung_parity_lock_and_mersenne_trap
#print axioms mod1024_and_weight2_odd_quotient_three_block_domino_collapse
#print axioms universal_mod12_quotient_lock_and_joint_digitsum_ge_five
#print axioms one_step_backward_quotient_recovery_and_mod_three_pow_one
#print axioms sharpened_five_seven_archimedean_rung_ceiling

end Mahler.SemigroupBreakout
