import ConsecutiveQuotientGCDAndEffectivePillai

/-!
# The `4 : 2 : 1 : 1` Octadic Death-Class Anatomy, Raw-Power vs. $\beta$-Map Counterexample & Correlated Survival Model

This module formalizes **Part I Track 3**, **Part II Sections F4.1, F4.2, F4.3**, and
**Part III Phase 5** of `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Track 3.1 & F4.3 — The `4 : 2 : 1 : 1` Octadic Triad Partition & Exact Class Counts
   (`octadic_triad_exit_partition`, `octadic_density_counts`)**:
   - For every quotient $Q \in \mathbb{N}$:
     - $Q \bmod 2 = 1 \iff Q \bmod 8 \in \{1, 3, 5, 7\}$ ($4$ classes, $v_2(Q) = 0$),
     - $(2 \mid Q \land \neg(4 \mid Q)) \iff Q \bmod 8 \in \{2, 6\}$ ($2$ classes, $v_2(Q) = 1$, Mod-3 Death Class),
     - $(4 \mid Q \land \neg(8 \mid Q)) \iff Q \bmod 8 = 4$ ($1$ class, $v_2(Q) = 2$, $s = 2$ Class),
     - $8 \mid Q \iff Q \bmod 8 = 0$ ($1$ class, advances to triad $k + 1$).
   - Proves that the death classes $\{2, 6\}$ form $2/8 = 1/4$ of all octadic classes and $2/4 = 1/2$
     of the $4$ even continuation classes $\{0, 2, 4, 6\}$.

2. **Track 3.2 — Bijection of the 8 Dyadic Lifts onto `Fin 8` (`coincidence_quotient_bijection_mod_eight`)**:
   - Whenever $2^E Q_{\text{base}} + D = 3^a V_{\text{base}}$, the $8$ lifts
     $V_m = V_{\text{base}} + 2^E m$ and $Q_m = Q_{\text{base}} + 3^a m$ ($m \in \text{Fin } 8$)
     satisfy $2^E Q_m + D = 3^a V_m$ and map bijectively onto the $8$ residue classes modulo $8$,
     with exact class counts $4, 2, 1, 1$.

3. **Track 3.3 — Mod-4 Death-Class Avoidance Criterion (`death_class_avoidance_mod_four_condition`)**:
   - A quotient $Q$ avoids the $v_2(Q) = 1$ death class if and only if $Q \bmod 4 \ne 2$
     (equivalently $Q \bmod 2 = 1 \lor 4 \mid Q$).

4. **Section F4.1 — Finite-State Eventual Periodicity of Carry and $2^n \bmod M$ Under Periodic Forcing
   (`periodic_parity_forces_eventually_periodic_carry_mod`)**:
   - Without invoking Skolem–Mahler–Lech, proves directly via finite-state pigeonhole on
     $\text{Fin } M \times \text{Fin } M \times \text{Fin } P$ that if a parity word $e$ has period $P \ge 1$,
     then $(C_n \bmod M, 2^n \bmod M, n \bmod P)$ repeats within $M^2 P$ steps and is eventually periodic.

5. **Section F4.2 — Counterexample to Identifying Raw Fractional Powers with $\beta = 3/2$ Iterates
   (`raw_power_fract_ne_betaMap_iterate_at_three_fourths`)**:
   - At $x = 3/4$, $T_{3/2}(3/4) = 1/8$ and $T_{3/2}^2(3/4) = 3/16$, whereas
     $\{(3/2)^2 (3/4)\} = 11/16 \ne 3/16$.

6. **Section F4.3 — Correlated Diagonal Countermodel to the Independent Product Heuristic
   (`correlated_diagonal_draw_beats_independent_product_bound`)**:
   - Formalizes the diagonal model on $\text{Fin } 8$ where a single draw $\omega \in \text{Fin } 8$
     is reused across $N \ge 2$ epochs: each marginal death share is $2/8 = 1/4$ (marginal survival $3/4$),
     yet the joint $N$-step survival share is still $6/8 = 3/4 > (3/4)^N$.
-/

namespace Mahler.OctadicDeathAnatomy

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

/-! ## 1. Track 3.1 & Track 3.3: The `4 : 2 : 1 : 1` Octadic Partition & Mod-4 Avoidance -/

/-- **The `4 : 2 : 1 : 1` Octadic Triad Exit Partition (`octadic_triad_exit_partition`, Track 3.1)**:
For every natural number `Q : ℕ`:
1. `Q % 2 = 1 ↔ (Q % 8 = 1 ∨ Q % 8 = 3 ∨ Q % 8 = 5 ∨ Q % 8 = 7)`,
2. `(2 ∣ Q ∧ ¬ (4 ∣ Q)) ↔ (Q % 8 = 2 ∨ Q % 8 = 6)`,
3. `(4 ∣ Q ∧ ¬ (8 ∣ Q)) ↔ Q % 8 = 4`, and
4. `8 ∣ Q ↔ Q % 8 = 0`. -/
theorem octadic_triad_exit_partition (Q : ℕ) :
    (Q % 2 = 1 ↔ (Q % 8 = 1 ∨ Q % 8 = 3 ∨ Q % 8 = 5 ∨ Q % 8 = 7)) ∧
      ((2 ∣ Q ∧ ¬ (4 ∣ Q)) ↔ (Q % 8 = 2 ∨ Q % 8 = 6)) ∧
      ((4 ∣ Q ∧ ¬ (8 ∣ Q)) ↔ Q % 8 = 4) ∧
      (8 ∣ Q ↔ Q % 8 = 0) := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Exact Octadic Class Counts (`octadic_density_counts`, Track 3.1 & Section F4.3)**:
On `Fin 8`:
- $4$ classes are odd (`r.val % 2 = 1`),
- $4$ classes are even (`r.val % 2 = 0`),
- $2$ classes are Mod-3 Death Classes (`r.val % 4 = 2`, i.e. $\{2, 6\}$, which is $2/8 = 1/4$ of all
  classes and $2/4 = 1/2$ of the $4$ even classes),
- $1$ class is the $s = 2$ exit class (`r.val = 4`), and
- $1$ class advances to the next triad (`r.val = 0`). -/
theorem octadic_density_counts :
    (Finset.univ.filter (fun r : Fin 8 => r.val % 2 = 1)).card = 4 ∧
      (Finset.univ.filter (fun r : Fin 8 => r.val % 2 = 0)).card = 4 ∧
      (Finset.univ.filter (fun r : Fin 8 => r.val % 4 = 2)).card = 2 ∧
      (Finset.univ.filter (fun r : Fin 8 => r.val = 4)).card = 1 ∧
      (Finset.univ.filter (fun r : Fin 8 => r.val = 0)).card = 1 ∧
      (2 : ℚ) / 8 = 1 / 4 ∧
      (2 : ℚ) / 4 = 1 / 2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by norm_num, by norm_num⟩

/-- **Mod-4 Death-Class Avoidance Condition (`death_class_avoidance_mod_four_condition`, Track 3.3)**:
A quotient `Q : ℕ` avoids the scale-$k$ death class `2 ∣ Q ∧ ¬ (4 ∣ Q)` if and only if
`Q % 4 ≠ 2`, which holds if and only if `Q % 2 = 1 ∨ 4 ∣ Q`. -/
theorem death_class_avoidance_mod_four_condition (Q : ℕ) :
    (¬ (2 ∣ Q ∧ ¬ (4 ∣ Q)) ↔ Q % 4 ≠ 2) ∧
      (Q % 4 ≠ 2 ↔ (Q % 2 = 1 ∨ 4 ∣ Q)) := by
  refine ⟨by omega, by omega⟩

/-! ## 2. Track 3.2: Bijection of the 8 Dyadic Lifts onto `Fin 8` -/

/-- Auxiliary lemma: for every `a : ℕ`, `3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3`. -/
theorem three_pow_mod_eight_eq_one_or_three (a : ℕ) :
    3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
  induction a with
  | zero => left; rfl
  | succ a ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide

/-- Auxiliary finite-domain verification on `Fin 8` for multiplier `c ∈ {1, 3}`. -/
theorem octadic_affine_bijection_and_counts (r0 : Fin 8) {c : ℕ} (hc : c = 1 ∨ c = 3) :
    Function.Bijective
      (fun m : Fin 8 => (⟨(r0.val + c * m.val) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)) ∧
      (Finset.univ.filter (fun m : Fin 8 => ((r0.val + c * m.val) % 8) % 2 = 1)).card = 4 ∧
      (Finset.univ.filter (fun m : Fin 8 => ((r0.val + c * m.val) % 8) % 4 = 2)).card = 2 ∧
      (Finset.univ.filter (fun m : Fin 8 => (r0.val + c * m.val) % 8 = 4)).card = 1 ∧
      (Finset.univ.filter (fun m : Fin 8 => (r0.val + c * m.val) % 8 = 0)).card = 1 := by
  rcases hc with rfl | rfl
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨⟨by revert r0; decide, rfl⟩, by revert r0; decide, by revert r0; decide,
      by revert r0; decide, by revert r0; decide⟩
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨⟨by revert r0; decide, rfl⟩, by revert r0; decide, by revert r0; decide,
      by revert r0; decide, by revert r0; decide⟩

/-- **Bijection and Exact `4 : 2 : 1 : 1` Counts of the 8 Dyadic Lifts
(`coincidence_quotient_bijection_mod_eight`, Track 3.2)**:
Whenever `2 ^ E * Q_base + D = 3 ^ a * V_base`, setting `V_lift m = V_base + 2 ^ E * m` and
`Q_lift m = Q_base + 3 ^ a * m`:
1. For every `m : ℕ`, `2 ^ E * Q_lift m + D = 3 ^ a * V_lift m`,
2. The residue map `m : Fin 8 ↦ ⟨Q_lift m.val % 8, ...⟩ : Fin 8` is bijective, and
3. Among the 8 lifts `m ∈ (Finset.univ : Finset (Fin 8))`:
   - Exactly **4** satisfy `Q_lift m.val % 2 = 1`,
   - Exactly **2** satisfy `Q_lift m.val % 4 = 2` (Mod-3 Death Class),
   - Exactly **1** satisfies `Q_lift m.val % 8 = 4` ($s = 2$ Class), and
   - Exactly **1** satisfies `Q_lift m.val % 8 = 0` (Advances to triad $k + 1$). -/
theorem coincidence_quotient_bijection_mod_eight {E a D V_base Q_base : ℕ}
    (hbase : 2 ^ E * Q_base + D = 3 ^ a * V_base) :
    let V_lift := fun m : ℕ => V_base + 2 ^ E * m
    let Q_lift := fun m : ℕ => Q_base + 3 ^ a * m
    (∀ m : ℕ, 2 ^ E * Q_lift m + D = 3 ^ a * V_lift m) ∧
      Function.Bijective
        (fun m : Fin 8 => (⟨Q_lift m.val % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)) ∧
      (Finset.univ.filter (fun m : Fin 8 => Q_lift m.val % 2 = 1)).card = 4 ∧
      (Finset.univ.filter (fun m : Fin 8 => Q_lift m.val % 4 = 2)).card = 2 ∧
      (Finset.univ.filter (fun m : Fin 8 => Q_lift m.val % 8 = 4)).card = 1 ∧
      (Finset.univ.filter (fun m : Fin 8 => Q_lift m.val % 8 = 0)).card = 1 := by
  intro V_lift Q_lift
  have hlift_eq : ∀ m : ℕ, 2 ^ E * Q_lift m + D = 3 ^ a * V_lift m := by
    intro m
    dsimp [V_lift, Q_lift]
    calc
      2 ^ E * (Q_base + 3 ^ a * m) + D =
          (2 ^ E * Q_base + D) + 2 ^ E * 3 ^ a * m := by ring
      _ = 3 ^ a * V_base + 2 ^ E * 3 ^ a * m := by rw [hbase]
      _ = 3 ^ a * (V_base + 2 ^ E * m) := by ring
  let r0 : Fin 8 := ⟨Q_base % 8, Nat.mod_lt _ (by decide)⟩
  have hQ_mod8 : ∀ m : Fin 8, Q_lift m.val % 8 = (r0.val + (3 ^ a % 8) * m.val) % 8 := by
    intro m
    dsimp [Q_lift, r0]
    rw [Nat.add_mod, Nat.mul_mod (3 ^ a) m.val, Nat.mod_eq_of_lt m.isLt]
    omega
  have hQ_mod2 : ∀ m : Fin 8, Q_lift m.val % 2 = ((r0.val + (3 ^ a % 8) * m.val) % 8) % 2 := by
    intro m
    rw [← hQ_mod8 m, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
  have hQ_mod4 : ∀ m : Fin 8, Q_lift m.val % 4 = ((r0.val + (3 ^ a % 8) * m.val) % 8) % 4 := by
    intro m
    rw [← hQ_mod8 m, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 8)]
  have hfun_eq :
      (fun m : Fin 8 => (⟨Q_lift m.val % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)) =
        (fun m : Fin 8 => ⟨(r0.val + (3 ^ a % 8) * m.val) % 8, Nat.mod_lt _ (by decide)⟩) := by
    funext m
    ext
    exact hQ_mod8 m
  rw [hfun_eq]
  simp only [hQ_mod2, hQ_mod4, hQ_mod8]
  exact ⟨hlift_eq, octadic_affine_bijection_and_counts r0 (three_pow_mod_eight_eq_one_or_three a)⟩

/-! ## 3. Section F4.1: Finite-State Eventual Periodicity Under Periodic Parity Forcing -/

/-- Augmented finite state `(wordCarry ε n % M, 2 ^ n % M, n % P)` in `Fin M × Fin M × Fin P`. -/
def periodicCarryModState (ε : ℕ → ℕ) (M P : ℕ) (hM : 1 ≤ M) (hP : 1 ≤ P) (n : ℕ) :
    Fin M × Fin M × Fin P :=
  (⟨wordCarry ε n % M, Nat.mod_lt _ hM⟩,
   ⟨2 ^ n % M, Nat.mod_lt _ hM⟩,
   ⟨n % P, Nat.mod_lt _ hP⟩)

/-- Deterministic one-step transition on `Fin M × Fin M × Fin P` when `ε` has period `P`. -/
def periodicCarryModStep (ε : ℕ → ℕ) (M P : ℕ) (hM : 1 ≤ M) (hP : 1 ≤ P)
    (st : Fin M × Fin M × Fin P) : Fin M × Fin M × Fin P :=
  (⟨(3 * st.1.val + st.2.1.val * (ε st.2.2.val % 2)) % M, Nat.mod_lt _ hM⟩,
   ⟨(st.2.1.val * 2) % M, Nat.mod_lt _ hM⟩,
   ⟨(st.2.2.val + 1) % P, Nat.mod_lt _ hP⟩)

/-- If `ε` has period `P` (`∀ n, ε (n + P) = ε n`), then `ε n = ε (n % P)` for all `n`. -/
theorem periodic_eq_mod_period {ε : ℕ → ℕ} {P : ℕ}
    (hper : ∀ n : ℕ, ε (n + P) = ε n) (n : ℕ) :
    ε n = ε (n % P) := by
  have hdiv : n = P * (n / P) + n % P := (Nat.div_add_mod n P).symm
  conv_lhs => rw [hdiv]
  generalize n / P = q
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show P * (q + 1) + n % P = (P * q + n % P) + P by ring, hper, ih]

/-- **Section F4.1 Finite-State Theorem (`periodic_parity_forces_eventually_periodic_carry_mod`,
Section F4.1)**:
If `1 ≤ M`, `1 ≤ P`, and `∀ n, ε (n + P) = ε n`, then:
1. `periodicCarryModState ε M P hM hP (n + 1) = periodicCarryModStep ε M P hM hP (periodicCarryModState ε M P hM hP n)`,
2. By finite-state pigeonhole, there exist `n₁ < n₂ ≤ M * M * P` with
   `periodicCarryModState ε M P hM hP n₁ = periodicCarryModState ε M P hM hP n₂`, and
3. For every `k : ℕ`, `wordCarry ε (n₁ + k) % M = wordCarry ε (n₂ + k) % M`. -/
theorem periodic_parity_forces_eventually_periodic_carry_mod
    {ε : ℕ → ℕ} {M P : ℕ} (hM : 1 ≤ M) (hP : 1 ≤ P)
    (hper : ∀ n : ℕ, ε (n + P) = ε n) :
    let st := periodicCarryModState ε M P hM hP
    let stepFn := periodicCarryModStep ε M P hM hP
    (∀ n : ℕ, st (n + 1) = stepFn (st n)) ∧
      (∃ n₁ n₂ : ℕ, n₁ < n₂ ∧ n₂ ≤ M * M * P ∧
        ∀ k : ℕ, wordCarry ε (n₁ + k) % M = wordCarry ε (n₂ + k) % M) := by
  intro st stepFn
  have hstep : ∀ n : ℕ, st (n + 1) = stepFn (st n) := by
    intro n
    dsimp [st, stepFn, periodicCarryModState, periodicCarryModStep]
    ext
    · simp only [wordCarry]
      have hε : ε n = ε (n % P) := periodic_eq_mod_period hper n
      rw [hε]
      conv_rhs =>
        rw [Nat.add_mod, Nat.mul_mod 3, Nat.mod_mod, ← Nat.mul_mod,
          Nat.mul_mod (2 ^ n % M), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    · simp only [Nat.pow_succ, Nat.mul_mod, Nat.mod_mod]
    · simp only [Nat.add_mod, Nat.mod_mod]
  refine ⟨hstep, ?_⟩
  have hcard : Fintype.card (Fin M × Fin M × Fin P) < M * M * P + 1 := by
    simp only [Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc]
    omega
  let f : Fin (M * M * P + 1) → Fin M × Fin M × Fin P := fun i => st i.val
  have hnot_inj : ¬ Function.Injective f := by
    intro hinj
    have hle := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at hle
    omega
  rw [Function.not_injective_iff] at hnot_inj
  rcases hnot_inj with ⟨i, j, hij_eq, hij_ne⟩
  have hiter : ∀ n₁ n₂ : ℕ, st n₁ = st n₂ → ∀ k : ℕ, st (n₁ + k) = st (n₂ + k) := by
    intro n₁ n₂ h0 k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
        rw [← Nat.add_assoc, ← Nat.add_assoc, hstep (n₁ + k), hstep (n₂ + k), ih]
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · refine ⟨i.val, j.val, hlt, by omega, ?_⟩
    intro k
    have hk := congrArg (fun x => x.1.val) (hiter i.val j.val hij_eq k)
    exact hk
  · exfalso; exact hij_ne (Fin.ext heq)
  · refine ⟨j.val, i.val, hgt, by omega, ?_⟩
    intro k
    have hk := congrArg (fun x => x.1.val) (hiter j.val i.val hij_eq.symm k)
    exact hk

/-! ## 4. Section F4.2: Counterexample to Identifying Raw Powers with $\beta = 3/2$ Iterates -/

/-- **Raw Fractional Powers vs. Greedy $\beta = 3/2$ Map Counterexample
(`raw_power_fract_ne_betaMap_iterate_at_three_fourths`, Section F4.2)**:
At $x = 3/4$:
1. `betaDigit (3 / 4) = 1` and `betaMap (3 / 4) = 1 / 8`,
2. `betaDigit (1 / 8) = 0` and `betaMap (betaMap (3 / 4)) = 3 / 16`,
3. `Int.fract ((3 / 2 : ℝ) ^ 2 * (3 / 4)) = 11 / 16`, and
4. `betaMap (betaMap (3 / 4)) ≠ Int.fract ((3 / 2 : ℝ) ^ 2 * (3 / 4))`. -/
theorem raw_power_fract_ne_betaMap_iterate_at_three_fourths :
    betaDigit (3 / 4 : ℝ) = 1 ∧
      betaMap (3 / 4 : ℝ) = 1 / 8 ∧
      betaDigit (1 / 8 : ℝ) = 0 ∧
      betaMap (betaMap (3 / 4 : ℝ)) = 3 / 16 ∧
      Int.fract ((3 / 2 : ℝ) ^ 2 * (3 / 4 : ℝ)) = 11 / 16 ∧
      betaMap (betaMap (3 / 4 : ℝ)) ≠ Int.fract ((3 / 2 : ℝ) ^ 2 * (3 / 4 : ℝ)) := by
  have hd1 : betaDigit (3 / 4 : ℝ) = 1 := by
    unfold betaDigit
    rw [Int.floor_eq_iff]
    norm_num
  have hm1 : betaMap (3 / 4 : ℝ) = 1 / 8 := by
    unfold betaMap
    rw [hd1]
    norm_num
  have hd2 : betaDigit (1 / 8 : ℝ) = 0 := by
    unfold betaDigit
    rw [Int.floor_eq_iff]
    norm_num
  have hm2 : betaMap (betaMap (3 / 4 : ℝ)) = 3 / 16 := by
    rw [hm1]
    unfold betaMap
    rw [hd2]
    norm_num
  have hfl : ⌊(3 / 2 : ℝ) ^ 2 * (3 / 4 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    norm_num
  have hfr : Int.fract ((3 / 2 : ℝ) ^ 2 * (3 / 4 : ℝ)) = 11 / 16 := by
    rw [Int.fract, hfl]
    norm_num
  refine ⟨hd1, hm1, hd2, hm2, hfr, ?_⟩
  rw [hm2, hfr]
  norm_num

/-! ## 5. Section F4.3: Correlated Diagonal Countermodel to the Independent Product Heuristic -/

/-- **Correlated Diagonal Countermodel on `Fin 8` (`correlated_diagonal_draw_beats_independent_product_bound`,
Section F4.3)**:
If a single octadic state $\omega \in \text{Fin } 8$ is drawn and reused across $N \ge 2$ steps:
1. At every individual time $t$, the death event $\omega.\text{val} \bmod 4 = 2$ has cardinality $2$
   and the survival event $\omega.\text{val} \bmod 4 \ne 2$ has cardinality $6$ (fraction $6/8 = 3/4$),
2. Across all $t < N$ ($N \ge 1$), the joint survival event $\forall t < N, \omega.\text{val} \bmod 4 \ne 2$
   still has cardinality $6$ (fraction $6/8 = 3/4$), and
3. For every $N \ge 2$, the independent product heuristic $(3/4)^N$ is strictly smaller than the
   correlated joint survival fraction $3/4$: `(3 / 4 : ℚ) ^ N < 3 / 4`. -/
theorem correlated_diagonal_draw_beats_independent_product_bound {N : ℕ} (hN : 2 ≤ N) :
    (Finset.univ.filter (fun ω : Fin 8 => ω.val % 4 ≠ 2)).card = 6 ∧
      (Finset.univ.filter (fun ω : Fin 8 => ∀ t < N, ω.val % 4 ≠ 2)).card = 6 ∧
      ((6 : ℚ) / 8 = 3 / 4) ∧
      (3 / 4 : ℚ) ^ N < 3 / 4 := by
  have hfilter_eq :
      Finset.univ.filter (fun ω : Fin 8 => ∀ t < N, ω.val % 4 ≠ 2) =
        Finset.univ.filter (fun ω : Fin 8 => ω.val % 4 ≠ 2) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h 0 (by omega)
    · intro h _ _
      exact h
  have hcard6 : (Finset.univ.filter (fun ω : Fin 8 => ω.val % 4 ≠ 2)).card = 6 := by decide
  rw [hfilter_eq]
  have hpow_lt : (3 / 4 : ℚ) ^ N < (3 / 4 : ℚ) ^ 1 :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  simp only [pow_one] at hpow_lt
  exact ⟨hcard6, hcard6, by norm_num, hpow_lt⟩

end Mahler.OctadicDeathAnatomy
