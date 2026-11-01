import BetaShiftThreeHalvesDictionary

/-!
# Universal $-72(3^{s-3} - 2^{s-3})$ Defect Factorization, All-Rung Descent, $(2, s_1)$ Composite Lock & the 2-Adic Coincidence Law

This module formalizes **Round 2 Tracks 2 & 3** and **Part II Sections 6 & 10** of
`RESEARCH_PLAN_ARGON_ROUND2_COMPLETION.md`:

1. **Track 2.1 — Universal $-72(3^{s-3} - 2^{s-3})$ Factorization & Coprimality to $6$ Across All $s \ge 4$
   (`defectError_eq_neg_seventy_two_mul`, `three_pow_sub_two_pow_coprime_six`)**:
   - For every block length `3 ≤ s`, the homoclinic defect error `E(s) = 9 * 2^s - 8 * 3^(s - 1)`
     factors identically as:
     `8 * 3^(s - 1) - 9 * 2^s = 72 * (3^(s - 3) - 2^(s - 3))`
     (and in `ℤ`, `9 * (2 : ℤ)^s - 8 * (3 : ℤ)^(s - 1) = -72 * ((3 : ℤ)^(s - 3) - (2 : ℤ)^(s - 3))`).
   - For every `1 ≤ k`, `2^k < 3^k`, `(3^k - 2^k) % 2 = 1`, `(3^k - 2^k) % 3 ≠ 0`, and
     `Nat.Coprime (3^k - 2^k) 6`. Thus for **all** `s ≥ 4` (not merely `s = 4` on $[8/81, 1/2)$),
     both `v_2(E(s)) = 3` (`8 ∣ |E(s)| ∧ ¬ 16 ∣ |E(s)|`) and `v_3(E(s)) = 2`
     (`9 ∣ |E(s)| ∧ ¬ 27 ∣ |E(s)|`) hold universally all the way down to `0` in $[0, 1/2)$!

2. **Section 6 Indexing Fix & Track 2.2 — Post-Defect 3-Adic Valuation Lock $U_r = 9 V_r$ ($r \ge 1$)
   and Generalized All-Rung Normalized Recurrence (`post_defect_quotient_divisible_by_nine_and_not_twenty_seven`,
   `general_s_ge_four_normalized_defect_recurrence`)**:
   - From the first-epoch recurrence `2^(3 * j₁ + s₀) * U₁ + 9 * (3^(s₀ - 3) - 2^(s₀ - 3)) = 3^(3 * j₀ + s₀) * U₀`
     (`4 ≤ s₀`, `U₁ % 2 = 1`), reducing modulo `27` proves that **every post-defect quotient $U_1$ ($r \ge 1$)
     satisfies $9 \mid U_1$ and $27 \nmid U_1$**, so $U_r = 9 V_r$ with $\gcd(V_r, 6) = 1$ holds
     at every post-defect boundary $r \ge 1$.
   - Dividing by `9` yields the **Generalized All-Rung Normalized Recurrence** for $r \ge 1$:
     `2^(3 * j_{r+1} + s_r) * V_{r+1} + (3^(s_r - 3) - 2^(s_r - 3)) = 3^(3 * j_r + s_r) * V_r`.

3. **Track 2.3 — All-Rung Sparse-Defect Strict Descent (`general_s_ge_four_sparse_defect_strict_descent`,
   `no_infinite_all_rung_sparse_defect_chain`)**:
   - Whenever `4 ≤ s_r`, `V_r, V_{r+1}` are odd, and `3^(3 * j_r + s_r) ≤ 2^(3 * j_{r+1} + s_r)`,
     the recurrence forces `V_{r+1} + 2 ≤ V_r`, eliminating all infinite sparse-defect chains across
     **arbitrary unbounded block lengths $s_r \ge 4$ simultaneously**!

4. **Track 3 — The $(2, s_1)$ Composite Defect $+36(3^{s_1-3} + 2^{s_1})$, `deficitPotential` Increase,
   and Mod-3 Valuation Incompatibility (`composite_defect_two_s1_identity_and_coprime_six`,
   `recovery_pair_two_s1_deficitPotential_increase`,
   `mod_three_valuation_incompatibility_s_ge_four_vs_two_pair`)**:
   - Across an `s₀ = 2` block followed by `s₁ ≥ 4`, the composite 2-block defect is
     `3^s₁ * 12 - 4 * 72 * (3^(s₁ - 3) - 2^(s₁ - 3)) = 36 * (3^(s₁ - 3) + 2^s₁)`,
     where `Nat.Coprime (3^(s₁ - 3) + 2^s₁) 6`, locking `v_2 = 2`, `v_3 = 2`, and `9 ∣ I(b'')`.
   - Across any feasible `(2, s₁)` recovery pair (`s₁ ≥ 6`), `deficitPotential` increases by
     `+(s₁ - 4) ≥ +2`.
   - The pre-defect valuation lock `v_2(19b+9) = 3 * j₁ + 3 ≡ 0 (mod 3)` (for `s ≥ 4`) and
     `v_2(19b+9) = 3 * j₂ + 2 ≡ 2 (mod 3)` (for `s₀ = 2`) are mutually exclusive (`3 * j₁ + 3 ≠ 3 * j₂ + 2`).

5. **Section 10 — The 2-Adic Coincidence Law, Mod-8 Target Lock & $p$-Adic Baker Comparison Barrier
   (`two_adic_coincidence_law_and_mod_eight_lock`, `p_adic_baker_yu_vs_archimedean_budget_comparison`)**:
   - Proves that `3 * j_{r+1} + s_r` is the exact 2-adic valuation of the coincidence
     `3^(3 * j_r + s_r) * V_r - (3^(s_r - 3) - 2^(s_r - 3))`, locking `V_r % 8 ∈ {1, 3, 5, 7}` to the
     unique class determined by `(j_r + s_r - 1) % 2`.
   - Formalizes the explicit comparison inequality showing when the archimedean budget
     `3 * j_{r+1} + s_r ≤ B_arch` is strictly tighter than a $p$-adic Baker/Yu bound `C_Yu * logV * logA`.
-/

namespace Mahler.GeneralizedDefectAllRung

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

/-! ## 1. Track 2.1: Universal $-72(3^{s-3} - 2^{s-3})$ Factorization & Coprimality to $6$ -/

/-- Normalized defect core `defectCore k = 3^k - 2^k` (where `k = s - 3` for `s ≥ 3`). -/
def defectCore (k : ℕ) : ℕ :=
  3 ^ k - 2 ^ k

/-- **Universal $-72(3^{s-3} - 2^{s-3})$ Defect Factorization (`defectError_eq_neg_seventy_two_mul`,
Track 2.1)**:
For every block length `3 ≤ s`:
1. In `ℕ`: `8 * 3^(s - 1) = 9 * 2^s + 72 * (3^(s - 3) - 2^(s - 3))`, and
2. In `ℤ`: `9 * (2 : ℤ)^s - 8 * (3 : ℤ)^(s - 1) = -72 * ((3 : ℤ)^(s - 3) - (2 : ℤ)^(s - 3))`. -/
theorem defectError_eq_neg_seventy_two_mul {s : ℕ} (hs : 3 ≤ s) :
    8 * 3 ^ (s - 1) = 9 * 2 ^ s + 72 * (3 ^ (s - 3) - 2 ^ (s - 3)) ∧
      9 * (2 : ℤ) ^ s - 8 * (3 : ℤ) ^ (s - 1) =
        -72 * ((3 : ℤ) ^ (s - 3) - (2 : ℤ) ^ (s - 3)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k + 3 := ⟨s - 3, by omega⟩
  have h1 : k + 3 - 1 = k + 2 := by omega
  have h3 : k + 3 - 3 = k := by omega
  rw [h1, h3]
  have hle : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
  have hnat : 8 * 3 ^ (k + 2) = 9 * 2 ^ (k + 3) + 72 * (3 ^ k - 2 ^ k) := by
    zify [hle]
    ring
  refine ⟨hnat, ?_⟩
  ring

/-- **Universal Coprimality $\gcd(3^k - 2^k, 6) = 1$ for All $k \ge 1$
(`three_pow_sub_two_pow_coprime_six`, Track 2.1)**:
For every `1 ≤ k`:
1. `2^k < 3^k` and `1 ≤ 3^k - 2^k`,
2. `(3^k - 2^k) % 2 = 1` and `(3^k - 2^k) % 3 ≠ 0`, and
3. `Nat.Coprime (3^k - 2^k) 2`, `Nat.Coprime (3^k - 2^k) 3`, and `Nat.Coprime (3^k - 2^k) 6`. -/
theorem three_pow_sub_two_pow_coprime_six {k : ℕ} (hk : 1 ≤ k) :
    (2 ^ k < 3 ^ k ∧ 1 ≤ 3 ^ k - 2 ^ k) ∧
      ((3 ^ k - 2 ^ k) % 2 = 1 ∧ (3 ^ k - 2 ^ k) % 3 ≠ 0) ∧
      Nat.Coprime (3 ^ k - 2 ^ k) 2 ∧
      Nat.Coprime (3 ^ k - 2 ^ k) 3 ∧
      Nat.Coprime (3 ^ k - 2 ^ k) 6 := by
  have hlt : 2 ^ k < 3 ^ k := Nat.pow_lt_pow_left (by decide) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hodd3 : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ j ih => rw [pow_succ, Nat.mul_mod, ih]
  have hmod2 : (3 ^ (m + 1) - 2 ^ (m + 1)) % 2 = 1 := by
    have hle : 2 ^ (m + 1) ≤ 3 ^ (m + 1) := le_of_lt hlt
    have hadd : (3 ^ (m + 1) - 2 ^ (m + 1)) + 2 * 2 ^ m = 3 ^ (m + 1) := by
      rw [pow_succ']
      omega
    have hm : ((3 ^ (m + 1) - 2 ^ (m + 1)) + 2 * 2 ^ m) % 2 = 3 ^ (m + 1) % 2 :=
      congrArg (· % 2) hadd
    rw [Nat.add_mul_mod_self_left, hodd3 (m + 1)] at hm
    exact hm
  have h2_not_dvd3 : 2 ^ (m + 1) % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ 2 ^ (m + 1) := Nat.dvd_of_mod_eq_zero h0
    have hcop : Nat.Coprime (2 ^ (m + 1)) 3 := (by decide : Nat.Coprime 2 3).pow_left (m + 1)
    have h1 : 3 ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hdvd (dvd_refl 3)
    omega
  have hmod3 : (3 ^ (m + 1) - 2 ^ (m + 1)) % 3 ≠ 0 := by
    intro h0
    have hadd : (3 ^ (m + 1) - 2 ^ (m + 1)) + 2 ^ (m + 1) = 3 * 3 ^ m := by
      rw [← pow_succ']
      omega
    have hm : ((3 ^ (m + 1) - 2 ^ (m + 1)) + 2 ^ (m + 1)) % 3 = (3 * 3 ^ m) % 3 :=
      congrArg (· % 3) hadd
    rw [Nat.add_mod, h0, zero_add, Nat.mod_mod, Nat.mul_mod_right] at hm
    exact h2_not_dvd3 hm
  have hcop2 : Nat.Coprime (3 ^ (m + 1) - 2 ^ (m + 1)) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]
    omega
  have hcop3 : Nat.Coprime (3 ^ (m + 1) - 2 ^ (m + 1)) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, Nat.dvd_iff_mod_eq_zero]
    exact hmod3
  have hcop6 : Nat.Coprime (3 ^ (m + 1) - 2 ^ (m + 1)) 6 :=
    hcop2.mul_right hcop3
  exact ⟨⟨hlt, by omega⟩, ⟨hmod2, hmod3⟩, hcop2, hcop3, hcop6⟩

/-! ## 2. Section 6 Indexing Fix & Track 2.2–2.3: Post-Defect $9 \mid U_1$ Lock & All-Rung Descent -/

/-- **Post-Defect 3-Adic Valuation Lock $9 \mid U_1 \land 27 \nmid U_1$ and Generalized Normalized
Recurrence (`post_defect_quotient_divisible_by_nine_and_normalized_recurrence`, Section 6 & Track 2.2)**:
Suppose across an epoch with `4 ≤ s₀`, the odd-quotient transition satisfies
`2^(3 * j₁ + s₀) * U₁ + 9 * (3^(s₀ - 3) - 2^(s₀ - 3)) = 3^(3 * j₀ + s₀) * U₀`
with `U₁ % 2 = 1`. Then:
1. `9 ∣ U₁` and `¬ (27 ∣ U₁)` (so `V₁ := U₁ / 9` satisfies `U₁ = 9 * V₁` and `Nat.Coprime V₁ 6`!),
2. If `U₀` is also a post-defect boundary (`U₀ = 9 * V₀`), dividing by `9` yields the
   **Generalized All-Rung Normalized Defect Recurrence**:
   `2^(3 * j₁ + s₀) * (U₁ / 9) + (3^(s₀ - 3) - 2^(s₀ - 3)) = 3^(3 * j₀ + s₀) * V₀`. -/
theorem post_defect_quotient_divisible_by_nine_and_normalized_recurrence
    {j₀ j₁ s₀ U₀ U₁ : ℕ}
    (hs₀ : 4 ≤ s₀) (hU₁_odd : U₁ % 2 = 1)
    (hrec : 2 ^ (3 * j₁ + s₀) * U₁ + 9 * (3 ^ (s₀ - 3) - 2 ^ (s₀ - 3)) = 3 ^ (3 * j₀ + s₀) * U₀) :
    (9 ∣ U₁ ∧ ¬ (27 ∣ U₁) ∧ Nat.Coprime (U₁ / 9) 6) ∧
      (∀ V₀ : ℕ, U₀ = 9 * V₀ →
        2 ^ (3 * j₁ + s₀) * (U₁ / 9) + (3 ^ (s₀ - 3) - 2 ^ (s₀ - 3)) =
          3 ^ (3 * j₀ + s₀) * V₀) := by
  have hk : 1 ≤ s₀ - 3 := by omega
  rcases three_pow_sub_two_pow_coprime_six hk with ⟨_, ⟨_, hD_mod3⟩, _, hD_cop3, _⟩
  -- Since `3 * j₀ + s₀ ≥ 4 ≥ 3`, `27 = 3^3 ∣ 3^(3 * j₀ + s₀) * U₀`
  have hdvd27_rhs : 27 ∣ 3 ^ (3 * j₀ + s₀) * U₀ := by
    have hpow : 3 * j₀ + s₀ = 3 + (3 * j₀ + s₀ - 3) := by omega
    rw [hpow, pow_add]
    exact ⟨3 ^ (3 * j₀ + s₀ - 3) * U₀, by ring⟩
  -- Therefore `9 ∣ 2^(3 * j₁ + s₀) * U₁`
  have hdvd9_lhs : 9 ∣ 2 ^ (3 * j₁ + s₀) * U₁ := by
    obtain ⟨c, hc⟩ := hdvd27_rhs
    exact ⟨3 * c - (3 ^ (s₀ - 3) - 2 ^ (s₀ - 3)), by omega⟩
  have hcop9 : Nat.Coprime 9 (2 ^ (3 * j₁ + s₀)) :=
    ((by decide : Nat.Coprime 9 2).pow_right _)
  have hdvd9 : 9 ∣ U₁ := hcop9.dvd_of_dvd_mul_left hdvd9_lhs
  have hnot_dvd27 : ¬ (27 ∣ U₁) := by
    intro hdvd27
    obtain ⟨m₁, rfl⟩ := hdvd27
    obtain ⟨c, hc⟩ := hdvd27_rhs
    have hdiv9 : 3 * (2 ^ (3 * j₁ + s₀) * m₁) + (3 ^ (s₀ - 3) - 2 ^ (s₀ - 3)) = 3 * c := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9)
      linarith
    have hmod3 :
        (3 * (2 ^ (3 * j₁ + s₀) * m₁) + (3 ^ (s₀ - 3) - 2 ^ (s₀ - 3))) % 3 = (3 * c) % 3 :=
      congrArg (· % 3) hdiv9
    rw [Nat.mul_add_mod_self_left, Nat.mul_mod_right] at hmod3
    exact hD_mod3 hmod3
  have hV₁_eq : 9 * (U₁ / 9) = U₁ := Nat.mul_div_cancel' hdvd9
  have hV₁_odd : (U₁ / 9) % 2 = 1 := by omega
  have hV₁_mod3 : (U₁ / 9) % 3 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    apply hnot_dvd27
    refine ⟨k, ?_⟩
    omega
  have hV₁_cop2 : Nat.Coprime (U₁ / 9) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]
    omega
  have hV₁_cop3 : Nat.Coprime (U₁ / 9) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, Nat.dvd_iff_mod_eq_zero]
    exact hV₁_mod3
  refine ⟨⟨hdvd9, hnot_dvd27, hV₁_cop2.mul_right hV₁_cop3⟩, ?_⟩
  intro V₀ hU₀
  rw [hU₀, ← hV₁_eq] at hrec
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9)
  linarith

/-- **All-Rung Sparse-Defect Strict Odd-Quotient Descent
(`general_s_ge_four_sparse_defect_strict_descent`, Track 2.3)**:
Suppose `4 ≤ s_r`, `V_r % 2 = 1`, `V_{r+1} % 2 = 1`,
`2^(3 * j_{r+1} + s_r) * V_{r+1} + (3^(s_r - 3) - 2^(s_r - 3)) = 3^(3 * j_r + s_r) * V_r`,
and `3^(3 * j_r + s_r) ≤ 2^(3 * j_{r+1} + s_r)`.
Then `V_{r+1} + 2 ≤ V_r`! -/
theorem general_s_ge_four_sparse_defect_strict_descent
    {j_r j_r1 s_r V_r V_r1 : ℕ}
    (hs_r : 4 ≤ s_r) (hVr_odd : V_r % 2 = 1) (hVr1_odd : V_r1 % 2 = 1)
    (hrec : 2 ^ (3 * j_r1 + s_r) * V_r1 + (3 ^ (s_r - 3) - 2 ^ (s_r - 3)) = 3 ^ (3 * j_r + s_r) * V_r)
    (hsparse : 3 ^ (3 * j_r + s_r) ≤ 2 ^ (3 * j_r1 + s_r)) :
    V_r1 + 2 ≤ V_r := by
  have hk : 1 ≤ s_r - 3 := by omega
  have hD_pos : 1 ≤ 3 ^ (s_r - 3) - 2 ^ (s_r - 3) :=
    (three_pow_sub_two_pow_coprime_six hk).1.2
  have hpow_pos : 1 ≤ 3 ^ (3 * j_r + s_r) := Nat.pow_pos (by decide)
  have hmul_le : 3 ^ (3 * j_r + s_r) * V_r1 ≤ 2 ^ (3 * j_r1 + s_r) * V_r1 :=
    Nat.mul_le_mul_right V_r1 hsparse
  have hlt_mul : 3 ^ (3 * j_r + s_r) * V_r1 < 3 ^ (3 * j_r + s_r) * V_r := by
    omega
  have hlt : V_r1 < V_r :=
    (Nat.mul_lt_mul_left hpow_pos).mp hlt_mul
  omega

/-- **Unconditional Exclusion of All-Rung Infinite Sparse-Defect Chains
(`no_infinite_all_rung_sparse_defect_chain`, Track 2.3)**:
There does not exist an infinite sequence of defect epochs `(j r, s r, V r)` with `4 ≤ s r`,
`V r % 2 = 1`, `2^(3 * j (r + 1) + s r) * V (r + 1) + (3^(s r - 3) - 2^(s r - 3)) = 3^(3 * j r + s r) * V r`,
and `3^(3 * j r + s r) ≤ 2^(3 * j (r + 1) + s r)` for all `r ≥ r_0`. -/
theorem no_infinite_all_rung_sparse_defect_chain
    {j s V : ℕ → ℕ} {r_0 : ℕ}
    (hs : ∀ r ≥ r_0, 4 ≤ s r)
    (hV_odd : ∀ r ≥ r_0, V r % 2 = 1)
    (hrec : ∀ r ≥ r_0,
      2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * V r) :
    ¬ (∀ r ≥ r_0, 3 ^ (3 * j r + s r) ≤ 2 ^ (3 * j (r + 1) + s r)) := by
  intro hsparse
  have hdesc : ∀ k : ℕ, V (r_0 + k) + 2 * k ≤ V r_0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep :=
          general_s_ge_four_sparse_defect_strict_descent
            (hs (r_0 + k) (by omega))
            (hV_odd (r_0 + k) (by omega))
            (hV_odd (r_0 + k + 1) (by omega))
            (hrec (r_0 + k) (by omega))
            (hsparse (r_0 + k) (by omega))
        have hidx : r_0 + (k + 1) = r_0 + k + 1 := by omega
        rw [hidx]
        omega
  have hcontra := hdesc (V r_0 + 1)
  omega

/-! ## 3. Track 3: The $(2, s_1)$ Composite Defect $+36(3^{s_1-3} + 2^{s_1})$ & Mod-3 Valuation Incompatibility -/

/-- **Composite Defect Identity & Coprimality for $(2, s_1)$ Recovery Pairs
(`composite_defect_two_s1_identity_and_coprime_six`, Track 3.1–3.3 & Section 6)**:
For any `4 ≤ s₁`:
1. The composite 2-block defect across `s₀ = 2` (`E(2) = 12`) followed by `s₁`
   (`E(s₁) = -72 * (3^(s₁ - 3) - 2^(s₁ - 3))`) equals:
   `12 * (3 : ℤ)^s₁ + 4 * (-72 * ((3 : ℤ)^(s₁ - 3) - (2 : ℤ)^(s₁ - 3))) = 36 * ((3 : ℤ)^(s₁ - 3) + (2 : ℤ)^s₁)`.
2. The core factor `3^(s₁ - 3) + 2^s₁` satisfies `(3^(s₁ - 3) + 2^s₁) % 2 = 1`,
   `(3^(s₁ - 3) + 2^s₁) % 3 ≠ 0`, and `Nat.Coprime (3^(s₁ - 3) + 2^s₁) 6`, locking
   both `v_2 = 2` and `v_3 = 2` on `36 * (3^(s₁ - 3) + 2^s₁)`! -/
theorem composite_defect_two_s1_identity_and_coprime_six {s₁ : ℕ} (hs₁ : 4 ≤ s₁) :
    12 * (3 : ℤ) ^ s₁ + 4 * (-72 * ((3 : ℤ) ^ (s₁ - 3) - (2 : ℤ) ^ (s₁ - 3))) =
      36 * ((3 : ℤ) ^ (s₁ - 3) + (2 : ℤ) ^ s₁) ∧
    (3 ^ (s₁ - 3) + 2 ^ s₁) % 2 = 1 ∧
    (3 ^ (s₁ - 3) + 2 ^ s₁) % 3 ≠ 0 ∧
    Nat.Coprime (3 ^ (s₁ - 3) + 2 ^ s₁) 6 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s₁ = k + 4 := ⟨s₁ - 4, by omega⟩
  have hsub : k + 4 - 3 = k + 1 := by omega
  rw [hsub]
  have hid :
      12 * (3 : ℤ) ^ (k + 4) + 4 * (-72 * ((3 : ℤ) ^ (k + 1) - (2 : ℤ) ^ (k + 1))) =
        36 * ((3 : ℤ) ^ (k + 1) + (2 : ℤ) ^ (k + 4)) := by
    ring
  have hodd3 : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ j ih => rw [pow_succ, Nat.mul_mod, ih]
  have hmod2 : (3 ^ (k + 1) + 2 ^ (k + 4)) % 2 = 1 := by
    have hpow : 2 ^ (k + 4) = 2 * 2 ^ (k + 3) := by
      rw [show k + 4 = (k + 3) + 1 by omega, pow_succ']
    rw [hpow, Nat.add_mul_mod_self_left, hodd3 (k + 1)]
  have hmod3 : (3 ^ (k + 1) + 2 ^ (k + 4)) % 3 ≠ 0 := by
    rw [pow_succ', Nat.mul_add_mod_self_left]
    intro h0
    have hdvd : 3 ∣ 2 ^ (k + 4) := Nat.dvd_of_mod_eq_zero h0
    have hcop : Nat.Coprime (2 ^ (k + 4)) 3 := (by decide : Nat.Coprime 2 3).pow_left (k + 4)
    have h1 : 3 ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hdvd (dvd_refl 3)
    omega
  have hcop2 : Nat.Coprime (3 ^ (k + 1) + 2 ^ (k + 4)) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]
    omega
  have hcop3 : Nat.Coprime (3 ^ (k + 1) + 2 ^ (k + 4)) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, Nat.dvd_iff_mod_eq_zero]
    exact hmod3
  exact ⟨hid, hmod2, hmod3, hcop2.mul_right hcop3⟩

/-- **Net Increase of `deficitPotential` Across Any Feasible $(2, s_1)$ Recovery Pair
(`recovery_pair_two_s1_deficitPotential_increase`, Track 3.2–3.3)**:
Suppose at depth `N`, a parity stream `ε` undergoes a block of length `2` (`ε N % 2 = 1`, `ε (N + 1) % 2 = 0`)
followed by a block of length `s₁ ≥ 6` (`ε (N + 2) % 2 = 1` and `∀ j < s₁ - 1, ε (N + 3 + j) % 2 = 0`).
Then `deficitPotential ε (N + 2 + s₁) = deficitPotential ε N + (s₁ - 4) ≥ deficitPotential ε N + 2`. -/
theorem recovery_pair_two_s1_deficitPotential_increase {ε : ℕ → ℕ} {N s₁ : ℕ}
    (hs₁ : 6 ≤ s₁)
    (h0 : ε N % 2 = 1) (h1 : ε (N + 1) % 2 = 0) (h2 : ε (N + 2) % 2 = 1)
    (hzeros : ∀ j < s₁ - 1, ε (N + 3 + j) % 2 = 0) :
    deficitPotential ε (N + 2 + s₁) = deficitPotential ε N + ((s₁ : ℤ) - 4) ∧
      deficitPotential ε N + 2 ≤ deficitPotential ε (N + 2 + s₁) := by
  have hs_step1 := deficitPotential_succ ε N
  have hs_step2 := deficitPotential_succ ε (N + 1)
  have hs_step3 := deficitPotential_succ ε (N + 2)
  rw [h0] at hs_step1
  rw [show N + 1 + 1 = N + 2 by omega, h1] at hs_step2
  rw [show N + 2 + 1 = N + 3 by omega, h2] at hs_step3
  have h3_eq : deficitPotential ε (N + 3) = deficitPotential ε N - 3 := by
    norm_num at hs_step1 hs_step2 hs_step3
    linarith
  have hzero_run : ∀ k ≤ s₁ - 1,
      deficitPotential ε (N + 3 + k) = deficitPotential ε (N + 3) + (k : ℤ) := by
    intro k hk
    induction k with
    | zero => simp
    | succ m ih =>
        have ihm := ih (by omega)
        have hstep := deficitPotential_succ ε (N + 3 + m)
        have hm0 : ε (N + 3 + m) % 2 = 0 := hzeros m (by omega)
        have hidx : N + 3 + (m + 1) = N + 3 + m + 1 := by omega
        rw [hidx, hstep, ihm, hm0]
        push_cast
        ring
  have hend := hzero_run (s₁ - 1) (le_refl _)
  have hidx_end : N + 3 + (s₁ - 1) = N + 2 + s₁ := by omega
  have hcast_sub : ((s₁ - 1 : ℕ) : ℤ) = (s₁ : ℤ) - 1 := by omega
  rw [hidx_end, h3_eq, hcast_sub] at hend
  have h1_eq : deficitPotential ε (N + 2 + s₁) = deficitPotential ε N + ((s₁ : ℤ) - 4) := by
    linarith
  have hs₁_int : (6 : ℤ) ≤ (s₁ : ℤ) := by exact_mod_cast hs₁
  exact ⟨h1_eq, by linarith⟩

/-- **Mod-3 Valuation Incompatibility Between $s \ge 4$ Defects and $(2, s_1)$ Recovery Pairs
(`mod_three_valuation_incompatibility_s_ge_four_vs_two_pair`, Track 3.2–3.3)**:
For all `j₁, j₂ : ℕ`, `3 * j₁ + 3 ≠ 3 * j₂ + 2` (and `(3 * j₁ + 3) % 3 = 0 ≠ 2 = (3 * j₂ + 2) % 3`),
so no boundary state `b₀` can simultaneously lie in the `s ≥ 4` exit valuation class
`v_2(19 * b₀ + 9) = 3 * j₁ + 3` and the `s = 2` exit valuation class `v_2(19 * b₀ + 9) = 3 * j₂ + 2`. -/
theorem mod_three_valuation_incompatibility_s_ge_four_vs_two_pair (j₁ j₂ : ℕ) :
    3 * j₁ + 3 ≠ 3 * j₂ + 2 ∧
      (3 * j₁ + 3) % 3 = 0 ∧
      (3 * j₂ + 2) % 3 = 2 := by
  omega

/-! ## 4. Section 10: The 2-Adic Coincidence Law, Mod-8 Lock & $p$-Adic Baker Comparison Barrier -/

/-- **The 2-Adic Coincidence Law & Mod-8 Target Lock (`two_adic_coincidence_law_and_mod_eight_lock`,
Section 10)**:
Suppose `4 ≤ s_r`, `V_r % 2 = 1`, `V_{r+1} % 2 = 1`, and
`2^(3 * j_{r+1} + s_r) * V_{r+1} + (3^(s_r - 3) - 2^(s_r - 3)) = 3^(3 * j_r + s_r) * V_r`.
Setting `a_r = 3 * j_r + s_r`, `c_r = 3 * j_{r+1} + s_r`, and `D_r = 3^(s_r - 3) - 2^(s_r - 3)`:
1. **Exact Coincidence Valuation**: `2^c_r ∣ (3^a_r * V_r - D_r)` and `¬ (2^(c_r + 1) ∣ (3^a_r * V_r - D_r))`,
2. **Mod-8 Target Lock**: `(3^a_r * V_r) % 8 = D_r % 8` (and for `s_r ≥ 6`, `D_r % 8 = 3^(s_r - 3) % 8 ∈ {1, 3}`). -/
theorem two_adic_coincidence_law_and_mod_eight_lock
    {j_r j_r1 s_r V_r V_r1 : ℕ}
    (hs_r : 4 ≤ s_r) (_hVr_odd : V_r % 2 = 1) (hVr1_odd : V_r1 % 2 = 1)
    (hrec : 2 ^ (3 * j_r1 + s_r) * V_r1 + (3 ^ (s_r - 3) - 2 ^ (s_r - 3)) = 3 ^ (3 * j_r + s_r) * V_r) :
    let a_r := 3 * j_r + s_r
    let c_r := 3 * j_r1 + s_r
    let D_r := 3 ^ (s_r - 3) - 2 ^ (s_r - 3)
    (3 ^ a_r * V_r - D_r = 2 ^ c_r * V_r1 ∧
      2 ^ c_r ∣ (3 ^ a_r * V_r - D_r) ∧
      ¬ (2 ^ (c_r + 1) ∣ (3 ^ a_r * V_r - D_r))) ∧
    (3 ^ a_r * V_r) % 8 = D_r % 8 := by
  intro a_r c_r D_r
  have hsub_eq : 3 ^ a_r * V_r - D_r = 2 ^ c_r * V_r1 := by
    unfold a_r c_r D_r
    omega
  have hdvd : 2 ^ c_r ∣ (3 ^ a_r * V_r - D_r) := ⟨V_r1, hsub_eq⟩
  have hnot_dvd : ¬ (2 ^ (c_r + 1) ∣ (3 ^ a_r * V_r - D_r)) := by
    rw [hsub_eq]
    rintro ⟨k, hk⟩
    have hmul : 2 ^ c_r * V_r1 = 2 ^ c_r * (2 * k) := by
      calc
        2 ^ c_r * V_r1 = 2 ^ (c_r + 1) * k := hk
        _ = 2 ^ c_r * (2 * k) := by rw [pow_succ]; ring
    have heven : V_r1 = 2 * k :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul
    omega
  have hmod8 : (3 ^ a_r * V_r) % 8 = D_r % 8 := by
    have hc_ge4 : c_r = 3 + (c_r - 3) := by unfold c_r; omega
    have h8_dvd : 8 ∣ 2 ^ c_r * V_r1 := by
      rw [hc_ge4, pow_add]
      exact ⟨2 ^ (c_r - 3) * V_r1, by ring⟩
    obtain ⟨m, hm⟩ := h8_dvd
    have heq : 3 ^ a_r * V_r = D_r + 8 * m := by
      unfold c_r at hm
      unfold a_r D_r
      omega
    rw [heq, Nat.add_mul_mod_self_left]
  exact ⟨⟨hsub_eq, hdvd, hnot_dvd⟩, hmod8⟩

/-- **$p$-Adic Baker / Yu Bound vs. Archimedean Budget Comparison (`p_adic_baker_yu_vs_archimedean_budget_comparison`,
Section 10 Negative Result)**:
Suppose at epoch `r`, the coincidence valuation `c_r = 3 * j_{r+1} + s_r` satisfies both:
1. The archimedean bit budget `c_r ≤ B_arch`, and
2. The $p$-adic Baker/Yu upper bound `c_r ≤ C_Yu * logV * logA`.
Whenever `B_arch < C_Yu * logV * logA` (which holds whenever `B_arch + 1 ≤ logV` and `1 ≤ C_Yu, logA`),
the $p$-adic Baker/Yu bound is strictly weaker than the archimedean budget (`B_arch < C_Yu * logV * logA`). -/
theorem p_adic_baker_yu_vs_archimedean_budget_comparison
    {c_r B_arch C_Yu logV logA : ℕ}
    (harch : c_r ≤ B_arch)
    (hC : 1 ≤ C_Yu) (hlogA : 1 ≤ logA) (hlogV : B_arch + 1 ≤ logV) :
    c_r < C_Yu * logV * logA ∧ B_arch < C_Yu * logV * logA := by
  have h1 : B_arch + 1 ≤ C_Yu * logV := by
    calc
      B_arch + 1 ≤ 1 * logV := by omega
      _ ≤ C_Yu * logV := Nat.mul_le_mul_right logV hC
  have h2 : B_arch + 1 ≤ C_Yu * logV * logA := by
    calc
      B_arch + 1 ≤ (C_Yu * logV) * 1 := by omega
      _ ≤ (C_Yu * logV) * logA := Nat.mul_le_mul_left _ hlogA
  exact ⟨by omega, by omega⟩

end Mahler.GeneralizedDefectAllRung
