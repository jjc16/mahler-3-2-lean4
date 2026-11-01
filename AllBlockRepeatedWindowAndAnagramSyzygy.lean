import RenewalCocycleAndBellmanSandwich

/-!
# All-Block Repeated-Window $(6 \cdot 2^d)$ Super-Divisibility, Mod-6 Anagram Invariance & Survivor $(p, q)$ Cutoffs

This module formalizes **Outer Loop 2 / 10 (Part VI, Sections O2.1–O2.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O2.1 (Inner Loop 1 / 3) — All-Block Repeated Gap-Window $(6 \cdot 2^d)$ Super-Divisibility
   (`allBlock_repeated_window_six_mul_two_pow_dvd`)**:
   - Whenever an $L$-block gap window repeats at $r_1 < r_2$ (`∀ t < L, s (r₁ + t) = s (r₂ + t)`)
     along a valid all-block trajectory (`ValidBlockChain b_0 s u N`, including $s = 2$ recovery blocks),
     with local window step sum $d = \operatorname{blockSteps} (fun t \Rightarrow s(r_1 + t)) L$:
     - `2 ^ d * (P (r₂ + L) - P (r₁ + L)) = 3 ^ d * (P r₂ - P r₁)`,
     - `P r₁ < P r₂` and `P (r₁ + L) < P (r₂ + L)` automatically (`no_infinite_oddReturnQ_chain_with_finite_prime_support`),
     - When $1 \le r_1$ and $1 \le L$, all four boundary states $b_{r_1}, b_{r_2}, b_{r_1+L}, b_{r_2+L}$
       are odd, so $6 \mid (P_{r_2} - P_{r_1})$ and $6 \mid (P_{r_2+L} - P_{r_1+L})$, upgrading the
       divisibility to **$(6 \cdot 2^d) \mid (P_{r_2} - P_{r_1})$** and **$(6 \cdot 3^d) \mid (P_{r_2+L} - P_{r_1+L})$**!

2. **Section O2.2 (Inner Loop 2 / 3) — Universal Mod-6 Step-Sum Determination of $A_{0,L}$ & Anagram Syzygy
   (`renewalNumerator_even_and_mod_three_law`, `allBlock_anagram_mod_six_congruence_and_pinch_gap`)**:
   - For every valid $L$-block sequence ($1 \le L$, $\forall k < L, 1 \le s_k$) with step sum $d = T_L \ge 1$:
     `renewalNumerator s L % 2 = 0` and `(renewalNumerator s L + (3 ^ d - 2 ^ d)) % 3 = 0`.
   - Consequently, any two valid block sequences $s_1, s_2$ with the same total step sum $d$ satisfy
     `renewalNumerator s₁ L₁ % 6 = renewalNumerator s₂ L₂ % 6` (`6 ∣ |A₂ - A₁|`), and if both
     survive the finite escape bound ($2 A_i < 3^d$), then $2 |A_2 - A_1| < 3^d$.

3. **Section O2.3 (Inner Loop 3 / 3) — All-Block Survivor State Upper Bound & $(p, q)$ Complexity Cutoff
   (`allBlock_survivor_P_upper_bound`, `allBlock_repeated_window_survivor_pq_cutoff`)**:
   - Whenever $2 A_{0,r} < 3^{T_r}$, the state $P_r = 3 b_r + 1$ satisfies
     `2 ^ (T_r + 1) * P_r < 3 ^ T_r * (2 * P_0 + 1)`.
   - Combining $(6 \cdot 2^d) \mid (P_{r_2} - P_{r_1})$ ($6 \cdot 2^d \le P_{r_2}$) with this upper
     bound yields `3 * 2 ^ (T_{r_2} + d + 2) < 3 ^ T_{r_2} * (2 * P_0 + 1)`, and for
     `2 * P_0 + 1 ≤ 3 * 2 ^ B`, `1 ≤ q`, and `3 ^ q ≤ 2 ^ (p + q)`:
     `q * (d + 2) < p * T_{r_2} + q * B`.
-/

namespace Mahler.AllBlockRepeatedWindow

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames
open Mahler.TransferJSRAndFourier
open Mahler.UniversalOrbitBijection
open Mahler.BetaShiftDictionary
open Mahler.GeneralizedDefectAllRung
open Mahler.BoundedOddPartAndSieve
open Mahler.AllRungConstantOfMotion
open Mahler.ArchimedeanPinningAndRenewal
open Mahler.ConsecutiveGCDAndPillai
open Mahler.OctadicDeathAnatomy
open Mahler.RenewalCocycleAndSandwich

/-! ## 1. Section O2.1: All-Block Repeated Gap-Window $(6 \cdot 2^d)$ Super-Divisibility -/

/-- Shifting a `ValidBlockChain b_0 s u N` to start at block `r` (`r + L ≤ N`) produces a valid
`L`-block chain from `orbit b_0 (blockSteps s r)`. -/
theorem validBlockChain_shift {b_0 : ℕ} {s u : ℕ → ℕ} {N r L : ℕ}
    (hrL : r + L ≤ N) (hchain : ValidBlockChain b_0 s u N) :
    ValidBlockChain (orbit b_0 (blockSteps s r)) (fun t => s (r + t)) (fun t => u (r + t)) L := by
  intro t ht
  rcases hchain (r + t) (by omega) with ⟨hst, hut, hdecomp⟩
  have hshift := blockSteps_add_shift s r t
  refine ⟨hst, hut, ?_⟩
  rw [← orbit_add, ← hshift]
  exact hdecomp

/-- If two gap sequences agree on `t < L`, their `blockSteps` and `renewalNumerator` at `L` are equal. -/
theorem blockSteps_and_renewalNumerator_congr {s₁ s₂ : ℕ → ℕ} {L : ℕ}
    (hmatch : ∀ t < L, s₁ t = s₂ t) :
    blockSteps s₁ L = blockSteps s₂ L ∧
      renewalNumerator s₁ L = renewalNumerator s₂ L := by
  induction L with
  | zero => simp [blockSteps, renewalNumerator]
  | succ L ih =>
      rcases ih (fun t ht => hmatch t (by omega)) with ⟨hT, hA⟩
      have hL := hmatch L (by omega)
      simp only [blockSteps, renewalNumerator, hT, hA, hL, and_self]

/-- **All-Block Repeated Gap-Window $(6 \cdot 2^d)$ Super-Divisibility
(`allBlock_repeated_window_six_mul_two_pow_dvd`, Section O2.1)**:
Suppose `ValidBlockChain b_0 s u (r₂ + L)` holds with `1 ≤ r₁`, `r₁ < r₂`, `1 ≤ L`, and
`∀ t < L, s (r₁ + t) = s (r₂ + t)`. Let `P r = oddReturnP (orbit b_0 (blockSteps s r))` and
`d = blockSteps (fun t => s (r₁ + t)) L`. Then:
1. `P r₁ < P r₂` and `P (r₁ + L) < P (r₂ + L)`,
2. `2 ^ d * (P (r₂ + L) - P (r₁ + L)) = 3 ^ d * (P r₂ - P r₁)`, and
3. `(6 * 2 ^ d) ∣ (P r₂ - P r₁)` and `(6 * 3 ^ d) ∣ (P (r₂ + L) - P (r₁ + L))`. -/
theorem allBlock_repeated_window_six_mul_two_pow_dvd
    {b_0 r₁ r₂ L : ℕ} {s u : ℕ → ℕ}
    (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ < r₂) (hL : 1 ≤ L)
    (hchain : ValidBlockChain b_0 s u (r₂ + L))
    (hmatch : ∀ t < L, s (r₁ + t) = s (r₂ + t)) :
    let P := fun r => oddReturnP (orbit b_0 (blockSteps s r))
    let d := blockSteps (fun t => s (r₁ + t)) L
    P r₁ < P r₂ ∧
      P (r₁ + L) < P (r₂ + L) ∧
      2 ^ d * (P (r₂ + L) - P (r₁ + L)) = 3 ^ d * (P r₂ - P r₁) ∧
      (6 * 2 ^ d ∣ (P r₂ - P r₁)) ∧
      (6 * 3 ^ d ∣ (P (r₂ + L) - P (r₁ + L))) := by
  intro P d
  have hmonoP := no_infinite_oddReturnQ_chain_with_finite_prime_support (N_max := r₂ + L - 1)
    (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ r₂ + L)] using hchain)
  have hlt1 : P r₁ < P r₂ := hmonoP r₁ (by omega) r₂ (by omega) hr₁₂
  have hch1 := validBlockChain_shift (r := r₁) (L := L) (by omega) hchain
  have hch2 := validBlockChain_shift (r := r₂) (L := L) (by omega) hchain
  have hm1 := renewal_prefix_master_identity hch1
  have hm2 := renewal_prefix_master_identity hch2
  dsimp only at hm1 hm2
  rcases blockSteps_and_renewalNumerator_congr hmatch with ⟨hd_eq, hA_eq⟩
  have hshift1 := blockSteps_add_shift s r₁ L
  have hshift2 := blockSteps_add_shift s r₂ L
  rw [← orbit_add, ← hshift1] at hm1
  rw [← orbit_add, ← hshift2, ← hd_eq, ← hA_eq] at hm2
  change 2 ^ d * P (r₁ + L) = 3 ^ d * P r₁ + renewalNumerator (fun t => s (r₁ + t)) L at hm1
  change 2 ^ d * P (r₂ + L) = 3 ^ d * P r₂ + renewalNumerator (fun t => s (r₁ + t)) L at hm2
  have h3_pos : 0 < 3 ^ d := Nat.pow_pos (by decide)
  have h2_pos : 0 < 2 ^ d := Nat.pow_pos (by decide)
  have hmul_lt : 2 ^ d * P (r₁ + L) < 2 ^ d * P (r₂ + L) := by
    have h3_lt : 3 ^ d * P r₁ < 3 ^ d * P r₂ := (Nat.mul_lt_mul_left h3_pos).mpr hlt1
    omega
  have hlt2 : P (r₁ + L) < P (r₂ + L) := (Nat.mul_lt_mul_left h2_pos).mp hmul_lt
  have hdiff : 2 ^ d * (P (r₂ + L) - P (r₁ + L)) = 3 ^ d * (P r₂ - P r₁) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  have hodd_r1 : orbit b_0 (blockSteps s r₁) % 2 = 1 :=
    mixed_block_return_odd hr₁ (fun k hk => hchain k (by omega))
  have hodd_r2 : orbit b_0 (blockSteps s r₂) % 2 = 1 :=
    mixed_block_return_odd (by omega) (fun k hk => hchain k (by omega))
  have hodd_r1L : orbit b_0 (blockSteps s (r₁ + L)) % 2 = 1 :=
    mixed_block_return_odd (by omega) (fun k hk => hchain k (by omega))
  have hodd_r2L : orbit b_0 (blockSteps s (r₂ + L)) % 2 = 1 :=
    mixed_block_return_odd (by omega) (fun k hk => hchain k (by omega))
  have h6_start : 6 ∣ (P r₂ - P r₁) := by
    dsimp [P, oddReturnP]
    omega
  have h6_end : 6 ∣ (P (r₂ + L) - P (r₁ + L)) := by
    dsimp [P, oddReturnP]
    omega
  rcases h6_start with ⟨q₁, hq₁⟩
  rcases h6_end with ⟨q₂, hq₂⟩
  have hdiff_q : 6 * (2 ^ d * q₂) = 6 * (3 ^ d * q₁) := by
    calc
      6 * (2 ^ d * q₂) = 2 ^ d * (6 * q₂) := by ring
      _ = 2 ^ d * (P (r₂ + L) - P (r₁ + L)) := by rw [← hq₂]
      _ = 3 ^ d * (P r₂ - P r₁) := hdiff
      _ = 3 ^ d * (6 * q₁) := by rw [hq₁]
      _ = 6 * (3 ^ d * q₁) := by ring
  have hq_rel : 2 ^ d * q₂ = 3 ^ d * q₁ :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 6) hdiff_q
  have hcop : Nat.Coprime (2 ^ d) (3 ^ d) :=
    (Nat.Coprime.pow_left d (by decide)).pow_right d
  have hdvd_q1 : 2 ^ d ∣ q₁ := hcop.dvd_of_dvd_mul_left ⟨q₂, hq_rel.symm⟩
  have hdvd_q2 : 3 ^ d ∣ q₂ := hcop.symm.dvd_of_dvd_mul_left ⟨q₁, hq_rel⟩
  rcases hdvd_q1 with ⟨k₁, rfl⟩
  rcases hdvd_q2 with ⟨k₂, rfl⟩
  refine ⟨hlt1, hlt2, hdiff, ⟨k₁, by linarith⟩, ⟨k₂, by linarith⟩⟩

/-! ## 2. Section O2.2: Universal Mod-6 Step-Sum Determination of $A_{0,L}$ & Anagram Syzygy -/

/-- **Universal Parity and Mod-6 Law of $A_{0,L}$ (`renewalNumerator_even_and_mod_three_law`,
Section O2.2)**:
For every `1 ≤ L` and `∀ k < L, 1 ≤ s k`, setting `d = blockSteps s L`:
1. `1 ≤ d`,
2. `renewalNumerator s L % 2 = 0`,
3. `(renewalNumerator s L + (3 ^ d - 2 ^ d)) % 3 = 0`, and
4. `renewalNumerator s L % 6 = 2 ^ d % 6`. -/
theorem renewalNumerator_even_and_mod_three_law {s : ℕ → ℕ} {L : ℕ}
    (hL : 1 ≤ L) (hs : ∀ k < L, 1 ≤ s k) :
    let d := blockSteps s L
    1 ≤ d ∧
      renewalNumerator s L % 2 = 0 ∧
      (renewalNumerator s L + (3 ^ d - 2 ^ d)) % 3 = 0 ∧
      renewalNumerator s L % 6 = 2 ^ d % 6 := by
  have heven : renewalNumerator s L % 2 = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, L = m + 1 := ⟨L - 1, by omega⟩
    induction m with
    | zero =>
        simp only [renewalNumerator, blockSteps, Nat.zero_add, Nat.mul_zero]
        have hs0 : 1 ≤ s 0 := hs 0 (by omega)
        have hsub : s 0 = (s 0 - 1) + 1 := by omega
        rw [hsub, Nat.pow_succ]
        omega
    | succ m ih =>
        have ihm := ih (by omega) (fun k hk => hs k (by omega))
        have hd_m2 : 1 ≤ blockSteps s (m + 2) := blockSteps_pos (by omega) hs
        have hsub : blockSteps s (m + 2) = (blockSteps s (m + 2) - 1) + 1 := by omega
        have hpow_even : 2 ^ (blockSteps s (m + 2)) % 2 = 0 := by
          rw [hsub, Nat.pow_succ]
          omega
        have hstep : renewalNumerator s (m + 2) =
            3 ^ (s (m + 1)) * renewalNumerator s (m + 1) + 2 ^ (blockSteps s (m + 2)) := rfl
        rw [hstep, Nat.add_mod, hpow_even, Nat.mul_mod, ihm]
        omega
  intro d
  have hd_pos : 1 ≤ d := blockSteps_pos hL hs
  have hbridge := three_mul_blockKernel_eq_pow_diff_add_renewalNumerator hs
  change 3 * blockKernel s L = (3 ^ d - 2 ^ d) + renewalNumerator s L at hbridge
  have hle_d : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
  have h3_div : 3 ∣ 3 ^ d := by
    have hsub : d = (d - 1) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    exact ⟨3 ^ (d - 1), by ring⟩
  rcases h3_div with ⟨q3, hq3⟩
  have hpow2_even : 2 ^ d % 2 = 0 := by
    have hsub : d = (d - 1) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    omega
  refine ⟨hd_pos, heven, by omega, by omega⟩

/-- **All-Block Anagram Mod-6 Congruence & Survivor Gap Bound
(`allBlock_anagram_mod_six_congruence_and_pinch_gap`, Section O2.2)**:
If two valid block sequences `s₁` (length `L₁ ≥ 1`) and `s₂` (length `L₂ ≥ 1`) have the same
total step sum `blockSteps s₁ L₁ = blockSteps s₂ L₂ = d`:
1. `renewalNumerator s₁ L₁ % 6 = renewalNumerator s₂ L₂ % 6`, and
2. if `2 * renewalNumerator s₁ L₁ < 3 ^ d`, `2 * renewalNumerator s₂ L₂ < 3 ^ d`, and
   `renewalNumerator s₁ L₁ ≤ renewalNumerator s₂ L₂`, then
   `6 ∣ (renewalNumerator s₂ L₂ - renewalNumerator s₁ L₁)` and
   `2 * (renewalNumerator s₂ L₂ - renewalNumerator s₁ L₁) < 3 ^ d`. -/
theorem allBlock_anagram_mod_six_congruence_and_pinch_gap
    {s₁ s₂ : ℕ → ℕ} {L₁ L₂ d : ℕ}
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hs₁ : ∀ k < L₁, 1 ≤ s₁ k) (hs₂ : ∀ k < L₂, 1 ≤ s₂ k)
    (hd₁ : blockSteps s₁ L₁ = d) (hd₂ : blockSteps s₂ L₂ = d) :
    renewalNumerator s₁ L₁ % 6 = renewalNumerator s₂ L₂ % 6 ∧
      (2 * renewalNumerator s₁ L₁ < 3 ^ d →
        2 * renewalNumerator s₂ L₂ < 3 ^ d →
        renewalNumerator s₁ L₁ ≤ renewalNumerator s₂ L₂ →
          6 ∣ (renewalNumerator s₂ L₂ - renewalNumerator s₁ L₁) ∧
            2 * (renewalNumerator s₂ L₂ - renewalNumerator s₁ L₁) < 3 ^ d) := by
  have hm1 := (renewalNumerator_even_and_mod_three_law hL₁ hs₁).2.2.2
  have hm2 := (renewalNumerator_even_and_mod_three_law hL₂ hs₂).2.2.2
  change renewalNumerator s₁ L₁ % 6 = 2 ^ (blockSteps s₁ L₁) % 6 at hm1
  change renewalNumerator s₂ L₂ % 6 = 2 ^ (blockSteps s₂ L₂) % 6 at hm2
  rw [hd₁] at hm1
  rw [hd₂] at hm2
  have hmod_eq : renewalNumerator s₁ L₁ % 6 = renewalNumerator s₂ L₂ % 6 := by
    rw [hm1, hm2]
  refine ⟨hmod_eq, ?_⟩
  intro hlt1 hlt2 hle
  exact ⟨by omega, by omega⟩

/-! ## 3. Section O2.3: All-Block Survivor State Upper Bound & $(p, q)$ Complexity Cutoff -/

/-- **All-Block Survivor State Upper Bound (`allBlock_survivor_P_upper_bound`, Section O2.3)**:
Along any valid `r`-block prefix (`ValidBlockChain b_0 s u r`), if the prefix satisfies the
finite survival condition `2 * renewalNumerator s r < 3 ^ (blockSteps s r)`, then:
`2 ^ (blockSteps s r + 1) * oddReturnP (orbit b_0 (blockSteps s r)) < 3 ^ (blockSteps s r) * (2 * oddReturnP b_0 + 1)`. -/
theorem allBlock_survivor_P_upper_bound {b_0 r : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u r)
    (hsurv : 2 * renewalNumerator s r < 3 ^ (blockSteps s r)) :
    let T_r := blockSteps s r
    2 ^ (T_r + 1) * oddReturnP (orbit b_0 T_r) <
      3 ^ T_r * (2 * oddReturnP b_0 + 1) := by
  intro T_r
  have hm := renewal_prefix_master_identity hchain
  change 2 ^ T_r * oddReturnP (orbit b_0 T_r) = 3 ^ T_r * oddReturnP b_0 + renewalNumerator s r at hm
  change 2 * renewalNumerator s r < 3 ^ T_r at hsurv
  have h2_T1 : 2 ^ (T_r + 1) * oddReturnP (orbit b_0 T_r) =
      2 * (2 ^ T_r * oddReturnP (orbit b_0 T_r)) := by
    rw [Nat.pow_succ']
    ring
  have hrhs : 3 ^ T_r * (2 * oddReturnP b_0 + 1) =
      2 * (3 ^ T_r * oddReturnP b_0) + 3 ^ T_r := by ring
  omega

/-- **All-Block Survivor Repeated-Window $(p, q)$ Cutoff (`allBlock_repeated_window_survivor_pq_cutoff`,
Section O2.3)**:
Suppose `ValidBlockChain b_0 s u (r₂ + L)` holds with `1 ≤ r₁`, `r₁ < r₂`, `1 ≤ L`, and
`∀ t < L, s (r₁ + t) = s (r₂ + t)`. If `2 * renewalNumerator s r₂ < 3 ^ (blockSteps s r₂)`
(so the orbit has not yet escaped at block `r₂`), `2 * oddReturnP b_0 + 1 ≤ 3 * 2 ^ B`,
`1 ≤ q`, and `3 ^ q ≤ 2 ^ (p + q)`, then setting `d = blockSteps (fun t => s (r₁ + t)) L` and
`T_r₂ = blockSteps s r₂`:
`q * (d + 2) < p * T_r₂ + q * B`. -/
theorem allBlock_repeated_window_survivor_pq_cutoff
    {b_0 r₁ r₂ L p q B : ℕ} {s u : ℕ → ℕ}
    (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ < r₂) (hL : 1 ≤ L)
    (hchain : ValidBlockChain b_0 s u (r₂ + L))
    (hmatch : ∀ t < L, s (r₁ + t) = s (r₂ + t))
    (hsurv : 2 * renewalNumerator s r₂ < 3 ^ (blockSteps s r₂))
    (hP0 : 2 * oddReturnP b_0 + 1 ≤ 3 * 2 ^ B)
    (hq : 1 ≤ q) (hpq : 3 ^ q ≤ 2 ^ (p + q)) :
    let d := blockSteps (fun t => s (r₁ + t)) L
    let T₂ := blockSteps s r₂
    q * (d + 2) < p * T₂ + q * B := by
  intro d T₂
  have hrep := allBlock_repeated_window_six_mul_two_pow_dvd hr₁ hr₁₂ hL hchain hmatch
  set P := fun r => oddReturnP (orbit b_0 (blockSteps s r))
  have hlt1 : P r₁ < P r₂ := hrep.1
  have hdvd6 : 6 * 2 ^ d ∣ (P r₂ - P r₁) := hrep.2.2.2.1
  have hdiff_pos : 0 < P r₂ - P r₁ := by omega
  have h6_le : 6 * 2 ^ d ≤ P r₂ - P r₁ := Nat.le_of_dvd hdiff_pos hdvd6
  have h6_le_P2 : 6 * 2 ^ d ≤ P r₂ := by omega
  have hup := allBlock_survivor_P_upper_bound (fun k hk => hchain k (by omega)) hsurv
  change 2 ^ (T₂ + 1) * P r₂ < 3 ^ T₂ * (2 * oddReturnP b_0 + 1) at hup
  have h2_comb : 3 * 2 ^ (T₂ + d + 2) < 3 ^ T₂ * (3 * 2 ^ B) := by
    have hmul_lhs : 3 * 2 ^ (T₂ + d + 2) = 2 ^ (T₂ + 1) * (6 * 2 ^ d) := by
      rw [show T₂ + d + 2 = (T₂ + 1) + d + 1 by omega, Nat.pow_add, Nat.pow_add]
      ring
    have hle1 : 2 ^ (T₂ + 1) * (6 * 2 ^ d) ≤ 2 ^ (T₂ + 1) * P r₂ :=
      Nat.mul_le_mul_left (2 ^ (T₂ + 1)) h6_le_P2
    have hle2 : 3 ^ T₂ * (2 * oddReturnP b_0 + 1) ≤ 3 ^ T₂ * (3 * 2 ^ B) :=
      Nat.mul_le_mul_left (3 ^ T₂) hP0
    omega
  have h2_lt : 2 ^ (T₂ + d + 2) < 3 ^ T₂ * 2 ^ B := by
    have h3_rearrange : 3 ^ T₂ * (3 * 2 ^ B) = 3 * (3 ^ T₂ * 2 ^ B) := by ring
    rw [h3_rearrange] at h2_comb
    exact (Nat.mul_lt_mul_left (by decide : 0 < 3)).mp h2_comb
  have hpow_q : (2 ^ (T₂ + d + 2)) ^ q < (3 ^ T₂ * 2 ^ B) ^ q :=
    Nat.pow_lt_pow_left h2_lt (by omega)
  have hlhs : (2 ^ (T₂ + d + 2)) ^ q = 2 ^ (q * (T₂ + d + 2)) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have hrhs_le : (3 ^ T₂ * 2 ^ B) ^ q ≤ 2 ^ ((p + q) * T₂ + q * B) := by
    calc
      (3 ^ T₂ * 2 ^ B) ^ q = (3 ^ q) ^ T₂ * 2 ^ (q * B) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm T₂ q, Nat.mul_comm B q,
          Nat.pow_mul]
      _ ≤ (2 ^ (p + q)) ^ T₂ * 2 ^ (q * B) :=
        Nat.mul_le_mul_right (2 ^ (q * B)) (Nat.pow_le_pow_left hpq T₂)
      _ = 2 ^ ((p + q) * T₂ + q * B) := by
        rw [← Nat.pow_mul, ← Nat.pow_add]
  have hpow2_lt : 2 ^ (q * (T₂ + d + 2)) < 2 ^ ((p + q) * T₂ + q * B) := by
    rw [← hlhs]
    exact lt_of_lt_of_le hpow_q hrhs_le
  have hexp_lt : q * (T₂ + d + 2) < (p + q) * T₂ + q * B :=
    (Nat.pow_lt_pow_iff_right (by decide)).mp hpow2_lt
  have hring1 : q * (T₂ + d + 2) = q * T₂ + q * (d + 2) := by ring
  have hring2 : (p + q) * T₂ + q * B = p * T₂ + q * T₂ + q * B := by ring
  omega

end Mahler.AllBlockRepeatedWindow
