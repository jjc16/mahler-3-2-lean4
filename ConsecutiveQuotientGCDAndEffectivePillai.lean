import ArchimedeanPinningAndMahlerBridge

/-!
# Consecutive Odd-Quotient GCD Laws, Effective Baker–Pillai Cutoff & Smooth $S$-Unit Prime Diversification

This module formalizes **Part I Track 2**, **Part II Section F4.4**, and **Part III Section A5**
of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Track 2.1 — Consecutive Odd-Quotient GCD Divisibility Law (`consecutive_V_gcd_dvd_defectCore`)**:
   - In every long-rung epoch transition $2^c V_1 + (3^{s-3} - 2^{s-3}) = 3^a V_0$,
     `Nat.gcd V_0 V_1 ∣ (3 ^ (s - 3) - 2 ^ (s - 3))`.
   - If $V_1 = V_0 = V$ and $4 \le s$, then $V \mid (3^{s-3} - 2^{s-3})$, $2^c < 3^a$, and
     $3^a - 2^c \le 3^{s-3} - 2^{s-3}$.

2. **Track 2.2 — Dense-Core Coprimality & Elementary Non-Stationarity (`dense_core_consecutive_V_coprime_and_ne`)**:
   - When $s = 4$ ($2^c V_1 + 1 = 3^a V_0$), $\gcd(V_0, V_1) = 1$.
   - For $1 \le a$ and $4 \le c$, the Catalan equation $2^c + 1 = 3^a$ has no solutions by an
     elementary mod-16 and mod-5 argument (`two_pow_add_one_ne_three_pow_of_four_le`), proving
     unconditionally that $V_0 \ne V_1$ whenever $1 \le V_0, V_1$, $1 \le a$, and $4 \le c$.

3. **Track 2.3, Track 2.4 & Section F4.4 — Bounded-Height Pillai–Baker Squeeze & Conditional Cutoff
   (`bounded_V_and_s_rational_pillai_squeeze`, `effective_pillai_cutoff_excludes_bounded_V_and_s`)**:
   - Proves the exact rational Pillai squeeze
     $0 < \frac{3^a V_0}{2^c V_1} - 1 < \frac{3^{S_{\max} - 3}}{2^c}$ for $4 \le s \le S_{\max}$.
   - Given the explicit `EffectivePillaiHypothesis` (bounding $a_r = 3 j_r + s_r \le A_{\max}$ when
     $1 \le V_r, V_{r+1} \le M$ and $4 \le s_r \le S_{\max}$), proves that no strictly increasing
     boundary chain can keep $V_r \le M$ and $4 \le s_r \le S_{\max}$ for $(A_{\max} + 1)(M + 1)$ epochs.

4. **Section A5.1 — All-Block Consecutive Quotient Coprimality & Exact $P$-GCD Law
   (`consecutive_oddReturnQ_coprime_and_P_gcd`)**:
   - Across any two consecutive odd blocks $P_r = 2^{s_r} Q_r$ and $P_{r+1} = 2^{s_{r+1}} Q_{r+1}$,
     $2^{s_{r+1}} Q_{r+1} = 3^{s_r} Q_r + 1$, forcing $\gcd(Q_r, Q_{r+1}) = 1$ and
     $\gcd(P_r, P_{r+1}) = 2^{\min(s_r, s_{r+1})}$.

5. **Sections A5.2, A5.3 & A5.4 — Smooth $S$-Unit Prime Diversification Beyond Bounded $V$
   (`allLong_normalized_three_term_sunit_nondegenerate_and_injective`,
   `no_infinite_allLong_chain_with_finite_V_prime_support`,
   `no_infinite_oddReturnQ_chain_with_finite_prime_support`)**:
   - Normalizing the all-long recurrence by $3^{s-3}$ yields the 3-term rational $S$-unit equation
     $x_1 - x_2 + x_3 = 1$ with $x_1 = 3^{3 j + 3} V$, $x_2 = 2^{3 j' + s} V' / 3^{s - 3}$, and
     $x_3 = (2/3)^{s - 3}$.
   - Proves that all proper subsums are non-vanishing, that $x_1$ uniquely determines $(j, V)$
     when $3 \nmid V$, and that `allRung_W_strictMono` makes the state sequence $W_r = 2^{3 j_r} V_r$
     pairwise distinct, excluding infinite fixed-prime-support chains conditionally on $S$-unit finiteness.
-/

namespace Mahler.ConsecutiveGCDAndPillai

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

/-! ## 1. Track 2.1: Consecutive Odd-Quotient GCD Divisibility Law -/

/-- **Consecutive Odd-Quotient GCD Divisibility Law (`consecutive_V_gcd_dvd_defectCore`, Track 2.1)**:
Whenever `2 ^ c * V₁ + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ a * V₀`:
1. `Nat.gcd V₀ V₁ ∣ (3 ^ (s - 3) - 2 ^ (s - 3))`, and
2. if `V₁ = V₀` (`1 ≤ V₀`) and `4 ≤ s`, then `V₀ ∣ (3 ^ (s - 3) - 2 ^ (s - 3))`, `2 ^ c < 3 ^ a`,
   and `3 ^ a - 2 ^ c ≤ 3 ^ (s - 3) - 2 ^ (s - 3)`. -/
theorem consecutive_V_gcd_dvd_defectCore {a c s V₀ V₁ : ℕ}
    (hrec : 2 ^ c * V₁ + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ a * V₀) :
    Nat.gcd V₀ V₁ ∣ (3 ^ (s - 3) - 2 ^ (s - 3)) ∧
      (V₁ = V₀ → 1 ≤ V₀ → 4 ≤ s →
        V₀ ∣ (3 ^ (s - 3) - 2 ^ (s - 3)) ∧
          2 ^ c < 3 ^ a ∧
          3 ^ a - 2 ^ c ≤ 3 ^ (s - 3) - 2 ^ (s - 3)) := by
  have hdvd0 : Nat.gcd V₀ V₁ ∣ 3 ^ a * V₀ :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_left V₀ V₁) (3 ^ a)
  have hdvd1 : Nat.gcd V₀ V₁ ∣ 2 ^ c * V₁ :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right V₀ V₁) (2 ^ c)
  rw [← hrec] at hdvd0
  have hdvd_def : Nat.gcd V₀ V₁ ∣ (3 ^ (s - 3) - 2 ^ (s - 3)) :=
    (Nat.dvd_add_right hdvd1).mp hdvd0
  refine ⟨hdvd_def, ?_⟩
  intro hEq hV0_pos hs4
  rw [hEq] at hrec hdvd_def
  have hgcd_self : Nat.gcd V₀ V₀ = V₀ := Nat.gcd_self V₀
  rw [hgcd_self] at hdvd_def
  have hdef_pos : 1 ≤ 3 ^ (s - 3) - 2 ^ (s - 3) :=
    (three_pow_sub_two_pow_coprime_six (by omega)).1.2
  have hlt_mul : 2 ^ c * V₀ < 3 ^ a * V₀ := by omega
  have h2c_lt_3a : 2 ^ c < 3 ^ a := by
    by_contra hge
    push_neg at hge
    have hmul_ge : 3 ^ a * V₀ ≤ 2 ^ c * V₀ := Nat.mul_le_mul_right V₀ hge
    omega
  have hsub_mul : (3 ^ a - 2 ^ c) * V₀ = 3 ^ (s - 3) - 2 ^ (s - 3) := by
    rw [Nat.sub_mul]
    omega
  have hdiff_le : 3 ^ a - 2 ^ c ≤ 3 ^ (s - 3) - 2 ^ (s - 3) := by
    calc
      3 ^ a - 2 ^ c = (3 ^ a - 2 ^ c) * 1 := (Nat.mul_one _).symm
      _ ≤ (3 ^ a - 2 ^ c) * V₀ := Nat.mul_le_mul_left _ hV0_pos
      _ = 3 ^ (s - 3) - 2 ^ (s - 3) := hsub_mul
  exact ⟨hdvd_def, h2c_lt_3a, hdiff_le⟩

/-! ## 2. Track 2.2: Dense-Core Coprimality & Elementary Non-Stationarity (`s = 4`) -/

/-- Auxiliary periodicity of $3^a \bmod 16$: `3 ^ a % 16 = 1 → a % 4 = 0`. -/
theorem three_pow_mod_sixteen_eq_one_imp_four_dvd :
    ∀ q r : ℕ, r < 4 → 3 ^ (4 * q + r) % 16 = 1 → r = 0 := by
  intro q
  induction q with
  | zero =>
      intro r hr hmod
      simp only [Nat.mul_zero, Nat.zero_add] at hmod
      rcases r with _ | _ | _ | _ | r
      · rfl
      · revert hmod; decide
      · revert hmod; decide
      · revert hmod; decide
      · omega
  | succ q ih =>
      intro r hr hmod
      have hsplit : 3 ^ (4 * (q + 1) + r) = 81 * 3 ^ (4 * q + r) := by
        rw [show 4 * (q + 1) + r = 4 + (4 * q + r) by omega, Nat.pow_add]
      have hmod' : 3 ^ (4 * q + r) % 16 = 1 := by
        rw [hsplit, Nat.mul_mod] at hmod
        omega
      exact ih r hr hmod'

/-- Auxiliary fact: $3^{4 m} \equiv 1 \pmod 5$ and $2^c \not\equiv 0 \pmod 5$. -/
theorem three_pow_four_mul_mod_five_and_two_pow_mod_five :
    (∀ m : ℕ, 3 ^ (4 * m) % 5 = 1) ∧ (∀ c : ℕ, 2 ^ c % 5 ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [show 4 * (m + 1) = 4 * m + 4 by omega, Nat.pow_add, Nat.mul_mod, ih]
  · intro c
    induction c with
    | zero => decide
    | succ c ih =>
        rw [Nat.pow_succ, Nat.mul_mod]
        omega

/-- **Elementary Proof That $2^c + 1 \ne 3^a$ for All $a \ge 1, c \ge 4$
(`two_pow_add_one_ne_three_pow_of_four_le`, Track 2.2 & Section A0.1)**:
For `c ≥ 4`, $16 \mid 2^c$, so $2^c + 1 = 3^a$ forces $3^a \equiv 1 \pmod{16}$, hence $4 \mid a$.
Then $3^a = 3^{4 m} \equiv 1 \pmod 5$, forcing $5 \mid 2^c$, a contradiction. -/
theorem two_pow_add_one_ne_three_pow_of_four_le {a c : ℕ} (hc : 4 ≤ c) :
    2 ^ c + 1 ≠ 3 ^ a := by
  intro heq
  have h16 : 2 ^ c % 16 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = k + 4 := ⟨c - 4, by omega⟩
    rw [Nat.pow_add]
    change (2 ^ k * 16) % 16 = 0
    omega
  have h3_16 : 3 ^ a % 16 = 1 := by
    rw [← heq]
    omega
  have hdiv4 : a = 4 * (a / 4) + a % 4 := (Nat.div_add_mod a 4).symm
  have hr_lt : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hr0 : a % 4 = 0 := by
    apply three_pow_mod_sixteen_eq_one_imp_four_dvd (a / 4) (a % 4) hr_lt
    rw [← hdiv4]
    exact h3_16
  have ha_eq : a = 4 * (a / 4) := by omega
  have hmod5 := three_pow_four_mul_mod_five_and_two_pow_mod_five
  have h3_5 : 3 ^ a % 5 = 1 := by
    rw [ha_eq]
    exact hmod5.1 (a / 4)
  have h2_5 : 2 ^ c % 5 = 0 := by
    have h := congrArg (fun x => x % 5) heq
    dsimp at h
    omega
  exact hmod5.2 c h2_5

/-- **Dense-Core Consecutive Coprimality & Non-Stationarity (`dense_core_consecutive_V_coprime_and_ne`,
Track 2.2)**:
Whenever `2 ^ c * V₁ + 1 = 3 ^ a * V₀`:
1. `Nat.Coprime V₀ V₁`, and
2. if `1 ≤ V₀`, `1 ≤ V₁`, `1 ≤ a`, and `4 ≤ c`, then `V₀ ≠ V₁`. -/
theorem dense_core_consecutive_V_coprime_and_ne {a c V₀ V₁ : ℕ}
    (hrec : 2 ^ c * V₁ + 1 = 3 ^ a * V₀) :
    Nat.Coprime V₀ V₁ ∧
      (1 ≤ V₀ → 1 ≤ V₁ → 1 ≤ a → 4 ≤ c → V₀ ≠ V₁) := by
  have hrec4 : 2 ^ c * V₁ + (3 ^ (4 - 3) - 2 ^ (4 - 3)) = 3 ^ a * V₀ := by
    simpa using hrec
  have hdvd1 := (consecutive_V_gcd_dvd_defectCore hrec4).1
  change Nat.gcd V₀ V₁ ∣ 1 at hdvd1
  have hcop : Nat.Coprime V₀ V₁ := Nat.dvd_one.mp hdvd1
  refine ⟨hcop, ?_⟩
  intro _ _ _ hc hEq
  subst hEq
  have hV1_eq : V₀ = 1 := by
    have hself : Nat.gcd V₀ V₀ = V₀ := Nat.gcd_self V₀
    have h1 : Nat.gcd V₀ V₀ = 1 := hcop
    omega
  subst hV1_eq
  simp only [Nat.mul_one] at hrec
  exact two_pow_add_one_ne_three_pow_of_four_le hc hrec

/-! ## 3. Track 2.3, Track 2.4 & Section F4.4: Pillai–Baker Squeeze & Conditional Cutoff -/

/-- **Bounded-Height Pillai–Baker Rational Squeeze (`bounded_V_and_s_rational_pillai_squeeze`,
Track 2.3)**:
For any epoch transition `2 ^ c * V₁ + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ a * V₀` with
`4 ≤ s ≤ S_max` and `1 ≤ V₁`:
`0 < ((3 : ℚ) ^ a * V₀) / ((2 : ℚ) ^ c * V₁) - 1` and
`((3 : ℚ) ^ a * V₀) / ((2 : ℚ) ^ c * V₁) - 1 < (3 : ℚ) ^ (S_max - 3) / (2 : ℚ) ^ c`. -/
theorem bounded_V_and_s_rational_pillai_squeeze {a c s S_max V₀ V₁ : ℕ}
    (hs4 : 4 ≤ s) (hs_max : s ≤ S_max) (hV1 : 1 ≤ V₁)
    (hrec : 2 ^ c * V₁ + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ a * V₀) :
    0 < ((3 : ℚ) ^ a * (V₀ : ℚ)) / ((2 : ℚ) ^ c * (V₁ : ℚ)) - 1 ∧
      ((3 : ℚ) ^ a * (V₀ : ℚ)) / ((2 : ℚ) ^ c * (V₁ : ℚ)) - 1 <
        (3 : ℚ) ^ (S_max - 3) / (2 : ℚ) ^ c := by
  have hdef_pos : 1 ≤ 3 ^ (s - 3) - 2 ^ (s - 3) :=
    (three_pow_sub_two_pow_coprime_six (by omega)).1.2
  have hle_s : 2 ^ (s - 3) ≤ 3 ^ (s - 3) := Nat.pow_le_pow_left (by decide) (s - 3)
  have hdef_lt : 3 ^ (s - 3) - 2 ^ (s - 3) < 3 ^ (S_max - 3) := by
    have hpow_le : 3 ^ (s - 3) ≤ 3 ^ (S_max - 3) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2_pos : 0 < 2 ^ (s - 3) := Nat.pow_pos (by decide)
    omega
  set D := 3 ^ (s - 3) - 2 ^ (s - 3)
  have hrec_q : (2 : ℚ) ^ c * (V₁ : ℚ) + (D : ℚ) = (3 : ℚ) ^ a * (V₀ : ℚ) := by
    exact_mod_cast hrec
  have h2c_pos : (0 : ℚ) < (2 : ℚ) ^ c := pow_pos (by norm_num) c
  have hV1_pos : (0 : ℚ) < (V₁ : ℚ) := by exact_mod_cast hV1
  have hden_pos : (0 : ℚ) < (2 : ℚ) ^ c * (V₁ : ℚ) := mul_pos h2c_pos hV1_pos
  have hden_ne : (2 : ℚ) ^ c * (V₁ : ℚ) ≠ 0 := ne_of_gt hden_pos
  have hdiff_eq :
      ((3 : ℚ) ^ a * (V₀ : ℚ)) / ((2 : ℚ) ^ c * (V₁ : ℚ)) - 1 =
        (D : ℚ) / ((2 : ℚ) ^ c * (V₁ : ℚ)) := by
    rw [← hrec_q, add_div, div_self hden_ne]
    ring
  rw [hdiff_eq]
  have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hdef_pos
  refine ⟨div_pos hD_pos_q hden_pos, ?_⟩
  rw [div_lt_div_iff₀ hden_pos h2c_pos]
  have hD_lt_q : (D : ℚ) < (3 : ℚ) ^ (S_max - 3) := by exact_mod_cast hdef_lt
  have hV1_ge1 : (1 : ℚ) ≤ (V₁ : ℚ) := by exact_mod_cast hV1
  have hmul_lt : (D : ℚ) * (2 : ℚ) ^ c < (3 : ℚ) ^ (S_max - 3) * (2 : ℚ) ^ c :=
    mul_lt_mul_of_pos_right hD_lt_q h2c_pos
  have hmul_le :
      (3 : ℚ) ^ (S_max - 3) * (2 : ℚ) ^ c ≤
        (3 : ℚ) ^ (S_max - 3) * ((2 : ℚ) ^ c * (V₁ : ℚ)) := by
    calc
      (3 : ℚ) ^ (S_max - 3) * (2 : ℚ) ^ c =
          (3 : ℚ) ^ (S_max - 3) * ((2 : ℚ) ^ c * 1) := by ring
      _ ≤ (3 : ℚ) ^ (S_max - 3) * ((2 : ℚ) ^ c * (V₁ : ℚ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hV1_ge1 (le_of_lt h2c_pos)) (by positivity)
  linarith

/-- Explicit conditional hypothesis encapsulating an effective Pillai/Matveev exponent bound
for bounded coefficients $1 \le V, V' \le M$ and bounded defect rung $4 \le s \le S_{\max}$. -/
def EffectivePillaiHypothesis (M S_max A_max : ℕ) : Prop :=
  ∀ a c s V V' : ℕ,
    1 ≤ V → V ≤ M → 1 ≤ V' → V' ≤ M → 4 ≤ s → s ≤ S_max →
      2 ^ c * V' + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ a * V →
        a ≤ A_max

/-- **Conditional Effective Pillai Cutoff (`effective_pillai_cutoff_excludes_bounded_V_and_s`,
Track 2.4 & Section F4.4)**:
Assuming `EffectivePillaiHypothesis M S_max A_max`, no strictly increasing normalized boundary
trajectory can keep `1 ≤ V r ≤ M` and `4 ≤ s r ≤ S_max` across `(A_max + 1) * (M + 1)` epochs. -/
theorem effective_pillai_cutoff_excludes_bounded_V_and_s
    {b j V s : ℕ → ℕ} {M S_max A_max : ℕ}
    (hpillai : EffectivePillaiHypothesis M S_max A_max)
    (hmono : StrictMono b)
    (hbound : ∀ r : ℕ, 19 * b r + 9 = 72 * 2 ^ (3 * j r) * V r)
    (hV_pos : ∀ r : ℕ, 1 ≤ V r)
    (hV_le : ∀ r : ℕ, V r ≤ M)
    (hs_bounds : ∀ r : ℕ, 4 ≤ s r ∧ s r ≤ S_max) :
    ¬ (∀ r : ℕ,
      2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * V r) := by
  intro hrec
  have hj_le : ∀ r < (A_max + 1) * (M + 1) + 1, j r ≤ A_max ∧ V r ≤ M := by
    intro r _
    have ha_le : 3 * j r + s r ≤ A_max :=
      hpillai (3 * j r + s r) (3 * j (r + 1) + s r) (s r) (V r) (V (r + 1))
        (hV_pos r) (hV_le r) (hV_pos (r + 1)) (hV_le (r + 1))
        (hs_bounds r).1 (hs_bounds r).2 (hrec r)
    exact ⟨by omega, hV_le r⟩
  exact no_simultaneously_bounded_j_and_V_along_strictMono_boundaries A_max M hmono hbound hj_le

/-! ## 4. Section A5.1: All-Block Consecutive Quotient Coprimality & Exact $P$-GCD Law -/

/-- **All-Block Consecutive Quotient Coprimality & Exact $P$-GCD Law
(`consecutive_oddReturnQ_coprime_and_P_gcd`, Section A5.1)**:
Across any two consecutive odd blocks `3 * b₀ + 1 = 2 ^ s₀ * Q₀` and
`3 * (orbit b₀ s₀) + 1 = 2 ^ s₁ * Q₁` (`1 ≤ s₀`, `Q₀ % 2 = 1`, `Q₁ % 2 = 1`):
1. `2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1`,
2. `Nat.Coprime Q₀ Q₁`, and
3. `Nat.gcd (oddReturnP b₀) (oddReturnP (orbit b₀ s₀)) = 2 ^ (min s₀ s₁)`. -/
theorem consecutive_oddReturnQ_coprime_and_P_gcd {b₀ s₀ s₁ Q₀ Q₁ : ℕ}
    (hs₀ : 1 ≤ s₀) (hQ₀_odd : Q₀ % 2 = 1) (hQ₁_odd : Q₁ % 2 = 1)
    (hdecomp₀ : 3 * b₀ + 1 = 2 ^ s₀ * Q₀)
    (hdecomp₁ : 3 * orbit b₀ s₀ + 1 = 2 ^ s₁ * Q₁) :
    2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1 ∧
      Nat.Coprime Q₀ Q₁ ∧
      Nat.gcd (oddReturnP b₀) (oddReturnP (orbit b₀ s₀)) = 2 ^ (min s₀ s₁) := by
  have hP1 := (oddReturnP_recurrence_and_strictMono hs₀ hdecomp₀).1
  unfold oddReturnP at hP1
  have hrel : 2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1 := by
    rw [← hdecomp₁, hP1]
  have hdvd1 : Nat.gcd Q₀ Q₁ ∣ 1 := by
    have hd0 : Nat.gcd Q₀ Q₁ ∣ 3 ^ s₀ * Q₀ :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left Q₀ Q₁) (3 ^ s₀)
    have hd1 : Nat.gcd Q₀ Q₁ ∣ 2 ^ s₁ * Q₁ :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right Q₀ Q₁) (2 ^ s₁)
    rw [hrel] at hd1
    exact (Nat.dvd_add_right hd0).mp hd1
  have hcop : Nat.Coprime Q₀ Q₁ := Nat.dvd_one.mp hdvd1
  have hcop2_Q0 : ∀ k : ℕ, Nat.Coprime Q₀ (2 ^ k) := by
    intro k
    refine Nat.Coprime.pow_right k ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]
    exact hQ₀_odd
  have hcop2_Q1 : ∀ k : ℕ, Nat.Coprime (2 ^ k) Q₁ := by
    intro k
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.coprime_two_left, Nat.odd_iff]
    exact hQ₁_odd
  refine ⟨hrel, hcop, ?_⟩
  unfold oddReturnP
  rw [hdecomp₀, hdecomp₁]
  rcases le_total s₀ s₁ with hle | hle
  · have hmin : min s₀ s₁ = s₀ := min_eq_left hle
    have hsplit : 2 ^ s₁ * Q₁ = 2 ^ s₀ * (2 ^ (s₁ - s₀) * Q₁) := by
      rw [← mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hle]
    rw [hmin, hsplit, Nat.gcd_mul_left]
    have hcop_prod : Nat.Coprime Q₀ (2 ^ (s₁ - s₀) * Q₁) :=
      (hcop2_Q0 (s₁ - s₀)).mul_right hcop
    rw [hcop_prod.gcd_eq_one, Nat.mul_one]
  · have hmin : min s₀ s₁ = s₁ := min_eq_right hle
    have hsplit : 2 ^ s₀ * Q₀ = 2 ^ s₁ * (2 ^ (s₀ - s₁) * Q₀) := by
      rw [← mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hle]
    rw [hmin, hsplit, Nat.gcd_mul_left]
    have hcop_prod : Nat.Coprime (2 ^ (s₀ - s₁) * Q₀) Q₁ :=
      Nat.Coprime.mul (hcop2_Q1 (s₀ - s₁)) hcop
    rw [hcop_prod.gcd_eq_one, Nat.mul_one]

/-! ## 5. Sections A5.2–A5.4: Smooth $S$-Unit Equations & Conditional Prime Diversification -/

/-- Unique recovery of `(j, V)` from `3 ^ (3 * j + 3) * V` when `¬ (3 ∣ V)` and `1 ≤ V`. -/
theorem three_pow_mul_V_injective {j₁ j₂ V₁ V₂ : ℕ}
    (hV₁_pos : 1 ≤ V₁) (hV₂_pos : 1 ≤ V₂)
    (hnot3_1 : ¬ (3 ∣ V₁)) (hnot3_2 : ¬ (3 ∣ V₂))
    (heq : 3 ^ (3 * j₁ + 3) * V₁ = 3 ^ (3 * j₂ + 3) * V₂) :
    j₁ = j₂ ∧ V₁ = V₂ := by
  have hfact := congrArg (fun n => n.factorization 3) heq
  dsimp at hfact
  have h3_ne1 : (3 : ℕ) ^ (3 * j₁ + 3) ≠ 0 := pow_ne_zero _ (by decide)
  have h3_ne2 : (3 : ℕ) ^ (3 * j₂ + 3) ≠ 0 := pow_ne_zero _ (by decide)
  have hV1_ne : V₁ ≠ 0 := by omega
  have hV2_ne : V₂ ≠ 0 := by omega
  rw [Nat.factorization_mul h3_ne1 hV1_ne, Nat.factorization_mul h3_ne2 hV2_ne,
    Finsupp.add_apply, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hnot3_1,
    Nat.factorization_eq_zero_of_not_dvd hnot3_2,
    Nat.add_zero, Nat.add_zero] at hfact
  have hj : j₁ = j₂ := by omega
  subst hj
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq⟩

/-- **Normalized 3-Term Rational $S$-Unit Equation, Nondegeneracy & State Injectivity
(`allLong_normalized_three_term_sunit_nondegenerate_and_injective`, Section A5.3)**:
Whenever `2 ^ (3 * j' + s) * V' + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ (3 * j + s) * V` with
`4 ≤ s`, `1 ≤ V`, and `1 ≤ V'`, setting
`x₁ = (3 : ℚ) ^ (3 * j + 3) * V`,
`x₂ = ((2 : ℚ) ^ (3 * j' + s) * V') / (3 : ℚ) ^ (s - 3)`, and
`x₃ = (2 / 3 : ℚ) ^ (s - 3)` satisfies:
1. `x₁ - x₂ + x₃ = 1`,
2. Every proper subsum is non-zero (`x₁ ≠ 0`, `x₂ ≠ 0`, `x₃ ≠ 0`, `x₁ - x₂ ≠ 0`, `x₁ + x₃ ≠ 0`, `-x₂ + x₃ ≠ 0`), and
3. If two epochs have `x₁` equal (`3 ^ (3 * j₁ + 3) * V₁ = 3 ^ (3 * j₂ + 3) * V₂`) with `¬ (3 ∣ V₁)`
   and `¬ (3 ∣ V₂)`, then `j₁ = j₂ ∧ V₁ = V₂`. -/
theorem allLong_normalized_three_term_sunit_nondegenerate_and_injective
    {j j' s V V' : ℕ} (hs : 4 ≤ s) (hV : 1 ≤ V) (hV' : 1 ≤ V')
    (hrec : 2 ^ (3 * j' + s) * V' + (3 ^ (s - 3) - 2 ^ (s - 3)) = 3 ^ (3 * j + s) * V) :
    let x₁ : ℚ := (3 : ℚ) ^ (3 * j + 3) * (V : ℚ)
    let x₂ : ℚ := ((2 : ℚ) ^ (3 * j' + s) * (V' : ℚ)) / (3 : ℚ) ^ (s - 3)
    let x₃ : ℚ := (2 / 3 : ℚ) ^ (s - 3)
    x₁ - x₂ + x₃ = 1 ∧
      x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ x₃ ≠ 0 ∧
      x₁ - x₂ ≠ 0 ∧ x₁ + x₃ ≠ 0 ∧ -x₂ + x₃ ≠ 0 := by
  intro x₁ x₂ x₃
  have hle_s : 2 ^ (s - 3) ≤ 3 ^ (s - 3) := Nat.pow_le_pow_left (by decide) (s - 3)
  have h3a_split : 3 ^ (3 * j + s) = 3 ^ (s - 3) * 3 ^ (3 * j + 3) := by
    rw [← Nat.pow_add, show (s - 3) + (3 * j + 3) = 3 * j + s by omega]
  have hrec_q :
      (2 : ℚ) ^ (3 * j' + s) * (V' : ℚ) + ((3 : ℚ) ^ (s - 3) - (2 : ℚ) ^ (s - 3)) =
        (3 : ℚ) ^ (s - 3) * ((3 : ℚ) ^ (3 * j + 3) * (V : ℚ)) := by
    have hrec' := hrec
    rw [h3a_split, mul_assoc] at hrec'
    zify [hle_s] at hrec'
    exact_mod_cast hrec'
  have h3s_pos : (0 : ℚ) < (3 : ℚ) ^ (s - 3) := pow_pos (by norm_num) (s - 3)
  have h3s_ne : (3 : ℚ) ^ (s - 3) ≠ 0 := ne_of_gt h3s_pos
  have heq1 : x₁ - x₂ + x₃ = 1 := by
    dsimp [x₁, x₂, x₃]
    rw [div_pow]
    have hmul :
        ((3 : ℚ) ^ (3 * j + 3) * (V : ℚ) -
          (2 : ℚ) ^ (3 * j' + s) * (V' : ℚ) / (3 : ℚ) ^ (s - 3) +
          (2 : ℚ) ^ (s - 3) / (3 : ℚ) ^ (s - 3)) * (3 : ℚ) ^ (s - 3) =
          1 * (3 : ℚ) ^ (s - 3) := by
      calc
        ((3 : ℚ) ^ (3 * j + 3) * (V : ℚ) -
            (2 : ℚ) ^ (3 * j' + s) * (V' : ℚ) / (3 : ℚ) ^ (s - 3) +
            (2 : ℚ) ^ (s - 3) / (3 : ℚ) ^ (s - 3)) * (3 : ℚ) ^ (s - 3) =
            (3 : ℚ) ^ (s - 3) * ((3 : ℚ) ^ (3 * j + 3) * (V : ℚ)) -
              (2 : ℚ) ^ (3 * j' + s) * (V' : ℚ) / (3 : ℚ) ^ (s - 3) * (3 : ℚ) ^ (s - 3) +
              (2 : ℚ) ^ (s - 3) / (3 : ℚ) ^ (s - 3) * (3 : ℚ) ^ (s - 3) := by ring
        _ = (3 : ℚ) ^ (s - 3) * ((3 : ℚ) ^ (3 * j + 3) * (V : ℚ)) -
              (2 : ℚ) ^ (3 * j' + s) * (V' : ℚ) + (2 : ℚ) ^ (s - 3) := by
          rw [div_mul_cancel₀ _ h3s_ne, div_mul_cancel₀ _ h3s_ne]
        _ = 1 * (3 : ℚ) ^ (s - 3) := by linarith
    exact mul_right_cancel₀ h3s_ne hmul
  have hx1_gt1 : 1 < x₁ := by
    dsimp [x₁]
    have h3_ge : (27 : ℚ) ≤ (3 : ℚ) ^ (3 * j + 3) := by
      have hnat : 3 ^ 3 ≤ 3 ^ (3 * j + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast hnat
    have hV_ge : (1 : ℚ) ≤ (V : ℚ) := by exact_mod_cast hV
    have hprod : (27 : ℚ) * 1 ≤ (3 : ℚ) ^ (3 * j + 3) * (V : ℚ) :=
      mul_le_mul h3_ge hV_ge (by norm_num) (by positivity)
    linarith
  have hx2_pos : 0 < x₂ := by
    dsimp [x₂]
    have h2_pos : (0 : ℚ) < (2 : ℚ) ^ (3 * j' + s) := pow_pos (by norm_num) _
    have hV'_pos : (0 : ℚ) < (V' : ℚ) := by exact_mod_cast hV'
    exact div_pos (mul_pos h2_pos hV'_pos) h3s_pos
  have hx3_bounds : 0 < x₃ ∧ x₃ < 1 := by
    dsimp [x₃]
    refine ⟨pow_pos (by norm_num) (s - 3), ?_⟩
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  refine ⟨heq1, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Conditional Exclusion of Infinite All-Long Chains with Finite Prime Support
(`no_infinite_allLong_chain_with_finite_V_prime_support`, Section A5.3)**:
Along any positive all-long chain (`1 ≤ V 0`, `∀ r, 4 ≤ s r`), `W r = 2 ^ (3 * j r) * V r` is
strictly increasing (`r₁ < r₂ → W r₁ < W r₂`), so the state pairs `(j r, V r)` are pairwise distinct.
Therefore any finite bound `N_max` on the number of distinct states `(j r, V r)` permitted by
fixed prime support $\mathcal{P}$ (via the Evertse–Schlickewei–Schmidt 3-term $S$-unit theorem)
is contradicted at horizon `N_max + 1`. -/
theorem no_infinite_allLong_chain_with_finite_V_prime_support
    {V j s : ℕ → ℕ} {N_max : ℕ}
    (hV0 : 1 ≤ V 0) (hs : ∀ r : ℕ, 4 ≤ s r)
    (hrec : ∀ r : ℕ,
      2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * V r)
    (hsunit_cap : ¬ (∀ r₁ < N_max + 1, ∀ r₂ < N_max + 1, r₁ < r₂ →
      2 ^ (3 * j r₁) * V r₁ < 2 ^ (3 * j r₂) * V r₂)) :
    False := by
  set W := fun r => 2 ^ (3 * j r) * V r
  have hW0 : 1 ≤ W 0 := by
    dsimp [W]
    exact Nat.mul_le_mul (Nat.one_le_pow _ 2 (by decide)) hV0
  have hrecW : ∀ r : ℕ,
      2 ^ (3 * j r + s r) * W (r + 1) + 2 ^ (3 * j r) * (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * W r :=
    fun r => allRung_W_recurrence (hrec r)
  have hstrict : ∀ r₁ r₂ : ℕ, r₁ < r₂ → W r₁ < W r₂ := by
    intro r₁ r₂ hlt
    have hm := (allRung_W_strictMono (K := r₂) hW0 (fun r _ => hs r) (fun r _ => hrecW r)).2
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, r₂ = r₁ + (d + 1) := ⟨r₂ - r₁ - 1, by omega⟩
    induction d with
    | zero => exact hm r₁ (by omega)
    | succ d ih =>
        have h1 := ih (by omega) (fun r hr => hm r (by omega))
        have h2 := hm (r₁ + (d + 1)) (by omega)
        rw [show r₁ + (d + 1 + 1) = r₁ + (d + 1) + 1 by omega]
        exact lt_trans h1 h2
  exact hsunit_cap (fun r₁ _ r₂ _ hlt => hstrict r₁ r₂ hlt)

/-- **Conditional Two-Term $S$-Unit Prime Diversification for All-Block Odd Trajectories
(`no_infinite_oddReturnQ_chain_with_finite_prime_support`, Section A5.2)**:
Along any valid odd-block trajectory (`ValidBlockChain b_0 s u N`), `oddReturnP (orbit b_0 (blockSteps s r))`
is strictly increasing (`r₁ < r₂ → P r₁ < P r₂`), so the solutions $(P_{r+1}, P_{r+1} - 1) = (2^{s_{r+1}} Q_{r+1}, 3^{s_r} Q_r)$
to $x - y = 1$ are pairwise distinct and cannot remain inside a finite $S$-unit solution set of size `N_max`. -/
theorem no_infinite_oddReturnQ_chain_with_finite_prime_support
    {b_0 N_max : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (N_max + 1)) :
    ∀ r₁ < N_max + 1, ∀ r₂ < N_max + 1, r₁ < r₂ →
      oddReturnP (orbit b_0 (blockSteps s r₁)) <
        oddReturnP (orbit b_0 (blockSteps s r₂)) := by
  have hstep : ∀ r < N_max + 1,
      oddReturnP (orbit b_0 (blockSteps s r)) <
        oddReturnP (orbit b_0 (blockSteps s (r + 1))) := by
    intro r hr
    rcases hchain r hr with ⟨hsr, _, hdecomp⟩
    have hlt := (oddReturnP_recurrence_and_strictMono hsr hdecomp).2.2
    simp only [blockSteps]
    rw [orbit_add]
    exact hlt
  intro r₁ _ r₂ hr2 hlt
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, r₂ = r₁ + (d + 1) := ⟨r₂ - r₁ - 1, by omega⟩
  induction d with
  | zero =>
      rw [Nat.add_one]
      exact hstep r₁ (by omega)
  | succ d ih =>
      have h1 := ih (by omega) (by omega)
      have h2 := hstep (r₁ + (d + 1)) (by omega)
      rw [show r₁ + (d + 1 + 1) = r₁ + (d + 1) + 1 by omega]
      exact lt_trans h1 h2

end Mahler.ConsecutiveGCDAndPillai
