import SignedCocycleRenewalBridgeAndTwoBlockFormula

/-!
# Distance-2 Fermat Quotient GCD Law, Universal $m$-Step Odd-Quotient Master Equation & All-Block $Q$-Descent

This module formalizes **Outer Loop 4 / 10 (Part VIII, Sections O4.1–O4.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O4.1 (Inner Loop 1 / 3) — Distance-2 Odd-Quotient Fermat Identity & GCD Law
   (`two_step_oddReturnQ_fermat_identity_and_gcd`)**:
   - From $2^{s_1} Q_1 = 3^{s_0} Q_0 + 1$ and $2^{s_2} Q_2 = 3^{s_1} Q_1 + 1$, eliminating $Q_1$ gives
     `2 ^ (s₁ + s₂) * Q₂ = 3 ^ (s₀ + s₁) * Q₀ + (3 ^ s₁ + 2 ^ s₁)`.
   - Consequently, `Nat.gcd Q₀ Q₂ ∣ (3 ^ s₁ + 2 ^ s₁)`, which depends **only on the middle gap $s_1$**
     ($13$ at $s_1 = 2$, $35$ at $s_1 = 3$, $97$ at $s_1 = 4$).

2. **Section O4.2 (Inner Loop 2 / 3) — Universal $m$-Step Odd-Quotient Master Equation & Interior GCD Law
   (`renewalNumerator_succ_eq_two_pow_mul_interior`,
   `multi_step_oddReturnQ_master_identity_and_interior_gcd`)**:
   - For any gap sequence $s$ and $m \ge 0$, setting $s'(t) = s(1 + t)$ and $d = \operatorname{blockSteps} s' m$:
     `renewalNumerator s (m + 1) = 2 ^ (s 0) * (3 ^ d + renewalNumerator s' m)`.
   - Across $m + 1$ blocks from $b_0$ (`ValidBlockChain b_0 s u (m + 1)`), if
     `oddReturnP (orbit b_0 (blockSteps s (m + 1))) = 2 ^ s_end * Q_end`, then dividing the renewal
     master identity by $2^{s_0}$ yields:
     `2 ^ (d + s_end) * Q_end = 3 ^ (s 0 + d) * u 0 + (3 ^ d + renewalNumerator s' m)`,
     forcing `Nat.gcd (u 0) Q_end ∣ (3 ^ d + renewalNumerator s' m)`.

3. **Section O4.3 (Inner Loop 3 / 3) — Elementary Impossibility of $2^c = 3^a + 1$ ($a \ge 2$) & All-Block $Q$-Descent
   (`three_pow_add_one_not_dvd_eight`, `two_pow_ne_three_pow_add_one_of_two_le`,
   `allBlock_oddReturnQ_strict_descent`, `no_infinite_allBlock_rapid_growth_Q_chain`)**:
   - Proves modulo $8$ that $8 \nmid (3^a + 1)$ for all $a \in \mathbb{N}$, so $2^c \ne 3^a + 1$ whenever
     $a \ge 2$.
   - Proves that whenever $2^{s_1} Q_1 = 3^{s_0} Q_0 + 1$ with $2 \le s_0$, $3^{s_0} \le 2^{s_1}$,
     and $Q_0, Q_1$ odd ($1 \le Q_0$), we have $Q_1 + 2 \le Q_0$, ruling out infinite rapid-growth
     $Q$-chains across all block lengths $s_r \ge 2$.
-/

namespace Mahler.MultiStepQuotientAndFermatGCD

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.SparseDefectCocycle
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
open Mahler.AllBlockRepeatedWindow
open Mahler.SignedCocycleRenewalBridge

/-! ## 1. Section O4.1: Distance-2 Odd-Quotient Fermat Identity & GCD Law -/

/-- **Two-Step Odd-Quotient Fermat Identity & GCD Law
(`two_step_oddReturnQ_fermat_identity_and_gcd`, Section O4.1)**:
Whenever `2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1` and `2 ^ s₂ * Q₂ = 3 ^ s₁ * Q₁ + 1`:
1. `2 ^ (s₁ + s₂) * Q₂ = 3 ^ (s₀ + s₁) * Q₀ + (3 ^ s₁ + 2 ^ s₁)`,
2. `Nat.gcd Q₀ Q₂ ∣ (3 ^ s₁ + 2 ^ s₁)`, and
3. Specializations: at `s₁ = 2`, `Nat.gcd Q₀ Q₂ ∣ 13`; at `s₁ = 3`, `Nat.gcd Q₀ Q₂ ∣ 35`;
   at `s₁ = 4`, `Nat.gcd Q₀ Q₂ ∣ 97`. -/
theorem two_step_oddReturnQ_fermat_identity_and_gcd {s₀ s₁ s₂ Q₀ Q₁ Q₂ : ℕ}
    (hstep1 : 2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1)
    (hstep2 : 2 ^ s₂ * Q₂ = 3 ^ s₁ * Q₁ + 1) :
    2 ^ (s₁ + s₂) * Q₂ = 3 ^ (s₀ + s₁) * Q₀ + (3 ^ s₁ + 2 ^ s₁) ∧
      Nat.gcd Q₀ Q₂ ∣ (3 ^ s₁ + 2 ^ s₁) ∧
      (s₁ = 2 → Nat.gcd Q₀ Q₂ ∣ 13) ∧
      (s₁ = 3 → Nat.gcd Q₀ Q₂ ∣ 35) ∧
      (s₁ = 4 → Nat.gcd Q₀ Q₂ ∣ 97) := by
  have hid : 2 ^ (s₁ + s₂) * Q₂ = 3 ^ (s₀ + s₁) * Q₀ + (3 ^ s₁ + 2 ^ s₁) := by
    calc
      2 ^ (s₁ + s₂) * Q₂ = 2 ^ s₁ * (2 ^ s₂ * Q₂) := by
        rw [Nat.pow_add]
        ring
      _ = 2 ^ s₁ * (3 ^ s₁ * Q₁ + 1) := by rw [hstep2]
      _ = 3 ^ s₁ * (2 ^ s₁ * Q₁) + 2 ^ s₁ := by ring
      _ = 3 ^ s₁ * (3 ^ s₀ * Q₀ + 1) + 2 ^ s₁ := by rw [hstep1]
      _ = 3 ^ (s₀ + s₁) * Q₀ + (3 ^ s₁ + 2 ^ s₁) := by
        rw [Nat.pow_add]
        ring
  have hdvd : Nat.gcd Q₀ Q₂ ∣ (3 ^ s₁ + 2 ^ s₁) := by
    have hd0 : Nat.gcd Q₀ Q₂ ∣ 3 ^ (s₀ + s₁) * Q₀ :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left Q₀ Q₂) (3 ^ (s₀ + s₁))
    have hd2 : Nat.gcd Q₀ Q₂ ∣ 2 ^ (s₁ + s₂) * Q₂ :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right Q₀ Q₂) (2 ^ (s₁ + s₂))
    rw [hid] at hd2
    exact (Nat.dvd_add_right hd0).mp hd2
  refine ⟨hid, hdvd, ?_, ?_, ?_⟩
  · rintro rfl; simpa using hdvd
  · rintro rfl; simpa using hdvd
  · rintro rfl; simpa using hdvd

/-! ## 2. Section O4.2: Universal $m$-Step Odd-Quotient Master Equation & Interior GCD Law -/

/-- Exact factorization of $2^{s_0}$ from `renewalNumerator s (m + 1)`:
`renewalNumerator s (m + 1) = 2 ^ (s 0) * (3 ^ d + renewalNumerator (fun t => s (1 + t)) m)`
where `d = blockSteps (fun t => s (1 + t)) m`. -/
theorem renewalNumerator_succ_eq_two_pow_mul_interior (s : ℕ → ℕ) (m : ℕ) :
    let s' := fun t => s (1 + t)
    let d := blockSteps s' m
    renewalNumerator s (m + 1) =
      2 ^ (s 0) * (3 ^ d + renewalNumerator s' m) := by
  intro s' d
  have hcomp := renewalNumerator_cocycle_composition s 1 m
  have h1 : blockSteps s 1 = s 0 := by simp [blockSteps]
  have hA1 : renewalNumerator s 1 = 2 ^ (s 0) := by simp [renewalNumerator, h1]
  have hm_eq : 1 + m = m + 1 := by omega
  change renewalNumerator s (1 + m) =
    3 ^ d * renewalNumerator s 1 + 2 ^ (blockSteps s 1) * renewalNumerator s' m at hcomp
  rw [hm_eq, h1, hA1] at hcomp
  rw [hcomp]
  ring

/-- **Universal $m$-Step Odd-Quotient Master Identity & Interior GCD Law
(`multi_step_oddReturnQ_master_identity_and_interior_gcd`, Section O4.2)**:
Suppose `ValidBlockChain b_0 s u (m + 1)` holds, and at the terminal boundary
`b_end = orbit b_0 (blockSteps s (m + 1))` we have `oddReturnP b_end = 2 ^ s_end * Q_end`.
Set `s' t = s (1 + t)` and `d = blockSteps s' m`. Then:
1. `blockSteps s (m + 1) = s 0 + d`,
2. `2 ^ (d + s_end) * Q_end = 3 ^ (s 0 + d) * u 0 + (3 ^ d + renewalNumerator s' m)`, and
3. `Nat.gcd (u 0) Q_end ∣ (3 ^ d + renewalNumerator s' m)` (which depends **only** on the
   interior block lengths $s_1, \dots, s_m$). -/
theorem multi_step_oddReturnQ_master_identity_and_interior_gcd
    {b_0 m s_end Q_end : ℕ} {s u : ℕ → ℕ}
    (hchain : ValidBlockChain b_0 s u (m + 1))
    (hend : oddReturnP (orbit b_0 (blockSteps s (m + 1))) = 2 ^ s_end * Q_end) :
    let s' := fun t => s (1 + t)
    let d := blockSteps s' m
    blockSteps s (m + 1) = s 0 + d ∧
      2 ^ (d + s_end) * Q_end =
        3 ^ (s 0 + d) * u 0 + (3 ^ d + renewalNumerator s' m) ∧
      Nat.gcd (u 0) Q_end ∣ (3 ^ d + renewalNumerator s' m) := by
  intro s' d
  have hshift := blockSteps_add_shift s 1 m
  have h1 : blockSteps s 1 = s 0 := by simp [blockSteps]
  have hm_eq : 1 + m = m + 1 := by omega
  rw [hm_eq, h1] at hshift
  change blockSteps s (m + 1) = s 0 + d at hshift
  have hmaster := renewal_prefix_master_identity hchain
  dsimp only at hmaster
  have h0_decomp : oddReturnP b_0 = 2 ^ (s 0) * u 0 := (hchain 0 (by omega)).2.2
  have hA_fact := renewalNumerator_succ_eq_two_pow_mul_interior s m
  change renewalNumerator s (m + 1) = 2 ^ (s 0) * (3 ^ d + renewalNumerator s' m) at hA_fact
  rw [hend, h0_decomp, hA_fact, hshift] at hmaster
  have hmul_eq :
      2 ^ (s 0) * (2 ^ (d + s_end) * Q_end) =
        2 ^ (s 0) * (3 ^ (s 0 + d) * u 0 + (3 ^ d + renewalNumerator s' m)) := by
    calc
      2 ^ (s 0) * (2 ^ (d + s_end) * Q_end) =
          2 ^ (s 0 + d) * (2 ^ s_end * Q_end) := by
        simp only [Nat.pow_add]
        ring
      _ = 3 ^ (s 0 + d) * (2 ^ (s 0) * u 0) + 2 ^ (s 0) * (3 ^ d + renewalNumerator s' m) :=
        hmaster
      _ = 2 ^ (s 0) * (3 ^ (s 0 + d) * u 0 + (3 ^ d + renewalNumerator s' m)) := by ring
  have hquot_id :
      2 ^ (d + s_end) * Q_end = 3 ^ (s 0 + d) * u 0 + (3 ^ d + renewalNumerator s' m) :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul_eq
  have hdvd : Nat.gcd (u 0) Q_end ∣ (3 ^ d + renewalNumerator s' m) := by
    have hd0 : Nat.gcd (u 0) Q_end ∣ 3 ^ (s 0 + d) * u 0 :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left (u 0) Q_end) (3 ^ (s 0 + d))
    have hd_end : Nat.gcd (u 0) Q_end ∣ 2 ^ (d + s_end) * Q_end :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right (u 0) Q_end) (2 ^ (d + s_end))
    rw [hquot_id] at hd_end
    exact (Nat.dvd_add_right hd0).mp hd_end
  exact ⟨hshift, hquot_id, hdvd⟩

/-! ## 3. Section O4.3: Elementary Impossibility of $2^c = 3^a + 1$ ($a \ge 2$) & All-Block $Q$-Descent -/

/-- For every `a : ℕ`, `(3 ^ a + 1) % 8 = 2 ∨ (3 ^ a + 1) % 8 = 4`, so `¬ (8 ∣ (3 ^ a + 1))`. -/
theorem three_pow_add_one_not_dvd_eight (a : ℕ) :
    ((3 ^ a + 1) % 8 = 2 ∨ (3 ^ a + 1) % 8 = 4) ∧ ¬ (8 ∣ (3 ^ a + 1)) := by
  have h3 := three_pow_mod_eight_eq_one_or_three a
  rcases h3 with h | h <;> refine ⟨by omega, by omega⟩

/-- **Elementary Proof That $2^c \ne 3^a + 1$ for All $a \ge 2$
(`two_pow_ne_three_pow_add_one_of_two_le`, Section O4.3)**:
If $a \ge 2$, then $3^a + 1 \ge 10 > 4$, so $2^c = 3^a + 1$ forces $c \ge 3$ and $8 \mid 2^c$,
contradicting `three_pow_add_one_not_dvd_eight`. -/
theorem two_pow_ne_three_pow_add_one_of_two_le {a c : ℕ} (ha : 2 ≤ a) :
    2 ^ c ≠ 3 ^ a + 1 := by
  intro heq
  have ha_ge9 : 9 ≤ 3 ^ a := by
    calc
      9 = 3 ^ 2 := by decide
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) ha
  have hc_ge3 : 3 ≤ c := by
    rcases c with _ | _ | _ | c
    · omega
    · omega
    · omega
    · omega
  have hdvd8 : 8 ∣ 2 ^ c := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = k + 3 := ⟨c - 3, by omega⟩
    rw [Nat.pow_add]
    exact ⟨2 ^ k, by ring⟩
  rw [heq] at hdvd8
  exact (three_pow_add_one_not_dvd_eight a).2 hdvd8

/-- **All-Block Odd-Quotient Strict Descent (`allBlock_oddReturnQ_strict_descent`, Section O4.3)**:
Whenever `2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1` with `2 ≤ s₀`, `3 ^ s₀ ≤ 2 ^ s₁`, `1 ≤ Q₀`,
`Q₀ % 2 = 1`, and `Q₁ % 2 = 1`, we have `Q₁ + 2 ≤ Q₀`. -/
theorem allBlock_oddReturnQ_strict_descent {s₀ s₁ Q₀ Q₁ : ℕ}
    (hs₀ : 2 ≤ s₀) (hpow : 3 ^ s₀ ≤ 2 ^ s₁)
    (hQ₀_pos : 1 ≤ Q₀) (hQ₀_odd : Q₀ % 2 = 1) (hQ₁_odd : Q₁ % 2 = 1)
    (hrel : 2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1) :
    Q₁ + 2 ≤ Q₀ := by
  have h3_odd : 3 ^ s₀ % 2 = 1 := by
    rcases three_pow_mod_eight_eq_one_or_three s₀ with h | h <;> omega
  have h2_even : 2 ^ s₁ % 2 = 0 := by
    have hs1_pos : 1 ≤ s₁ := by
      have h9 : 9 ≤ 3 ^ s₀ := by
        calc
          9 = 3 ^ 2 := by decide
          _ ≤ 3 ^ s₀ := Nat.pow_le_pow_right (by decide) hs₀
      rcases s₁ with _ | s₁ <;> omega
    have hsub : s₁ = (s₁ - 1) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    omega
  have hpow_strict : 3 ^ s₀ + 1 ≤ 2 ^ s₁ := by omega
  have hmul : 2 ^ s₁ * Q₁ ≤ 2 ^ s₁ * Q₀ := by
    calc
      2 ^ s₁ * Q₁ = 3 ^ s₀ * Q₀ + 1 := hrel
      _ ≤ 3 ^ s₀ * Q₀ + Q₀ := by omega
      _ = (3 ^ s₀ + 1) * Q₀ := by ring
      _ ≤ 2 ^ s₁ * Q₀ := Nat.mul_le_mul_right Q₀ hpow_strict
  have hQ_le : Q₁ ≤ Q₀ :=
    Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by decide))
  have hQ_ne : Q₁ ≠ Q₀ := by
    intro hEq
    subst hEq
    have hdvd1 : Q₁ ∣ 1 := by
      have hd0 : Q₁ ∣ 3 ^ s₀ * Q₁ := ⟨3 ^ s₀, by ring⟩
      have hd1 : Q₁ ∣ 2 ^ s₁ * Q₁ := ⟨2 ^ s₁, by ring⟩
      rw [hrel] at hd1
      exact (Nat.dvd_add_right hd0).mp hd1
    have hQ1 : Q₁ = 1 := Nat.dvd_one.mp hdvd1
    subst hQ1
    simp only [Nat.mul_one] at hrel
    exact two_pow_ne_three_pow_add_one_of_two_le hs₀ hrel
  omega

/-- **Impossibility of Infinite Rapid-Growth $Q$-Chains (`no_infinite_allBlock_rapid_growth_Q_chain`,
Section O4.3)**:
No infinite sequence $(s_r, Q_r)$ with $2 \le s_r$, $1 \le Q_r$, $Q_r \bmod 2 = 1$, and
$2^{s_{r+1}} Q_{r+1} = 3^{s_r} Q_r + 1$ can satisfy $3^{s_r} \le 2^{s_{r+1}}$ for all $r \in \mathbb{N}$. -/
theorem no_infinite_allBlock_rapid_growth_Q_chain {s Q : ℕ → ℕ}
    (hs : ∀ r : ℕ, 2 ≤ s r)
    (hQ_pos : ∀ r : ℕ, 1 ≤ Q r)
    (hQ_odd : ∀ r : ℕ, Q r % 2 = 1)
    (hrel : ∀ r : ℕ, 2 ^ (s (r + 1)) * Q (r + 1) = 3 ^ (s r) * Q r + 1) :
    ¬ (∀ r : ℕ, 3 ^ (s r) ≤ 2 ^ (s (r + 1))) := by
  intro hrapid
  have hdesc : ∀ k : ℕ, Q k + 2 * k ≤ Q 0 := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        have hstep := allBlock_oddReturnQ_strict_descent (hs k) (hrapid k)
          (hQ_pos k) (hQ_odd k) (hQ_odd (k + 1)) (hrel k)
        omega
  have hbad := hdesc (Q 0)
  have hpos := hQ_pos (Q 0)
  omega

end Mahler.MultiStepQuotientAndFermatGCD
