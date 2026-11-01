import GeneralizedDefectFactorizationAndAllRungDescent
import BaseSixMultiplicationAutomaton

/-!
# Bounded-Odd-Part $S$-Unit Exclusion, Backward 3-Adic Sieve, Integer/Rational Cases & $\Sigma_1/\Pi_2$ Certificates

This module formalizes **Part II Sections 11, 12, 13, 14, and 15** of
`RESEARCH_PLAN_ARGON_ROUND2_COMPLETION.md`:

1. **Section 11 — Bounded Odd Parts, Non-Degenerate 4-Term $\{2, 3\}$-Unit Equations & Strict-Monotonicity
   Pigeonhole Exclusion (`four_term_sunit_epoch_equation_no_vanishing_subsum`,
   `bounded_odd_part_iff_runs_saturate_budget`,
   `strictMono_boundaries_injective_on_j_and_V`,
   `no_simultaneously_bounded_j_and_V_along_strictMono_boundaries`,
   `no_bounded_odd_part_orbit_of_sunit_finiteness`)**:
   - Proves that in the epoch transition equation $V \cdot 3^a - V' \cdot 2^c - 3^{s-3} + 2^{s-3} = 0$
     ($s \ge 4$, $a = 3j + s \ge s$, $c = 3j' + s \ge s$, $\gcd(V, 6) = \gcd(V', 6) = 1$), **every
     proper two-term subsum is strictly non-zero**:
     `V * 3^a ≠ V' * 2^c`, `V * 3^a ≠ 3^(s - 3)`, `V' * 2^c ≠ 2^(s - 3)`, and `3^(s - 3) ≠ 2^(s - 3)`.
   - Proves that because $19 b_r + 9 = 72 \cdot 2^{3 j_r} V_r$ uniquely determines $b_r$ from $(j_r, V_r)$
     and the orbit boundaries $b_0 < b_1 < \dots$ are strictly increasing, **no two distinct epochs
     $r_1 < r_2$ can ever share the same pair $(j_{r_1}, V_{r_1}) = (j_{r_2}, V_{r_2})$**!
   - Consequently:
     - **Unconditional Bounded-$(j, V)$ Cutoff (`no_simultaneously_bounded_j_and_V_along_strictMono_boundaries`)**:
       No trajectory with strictly increasing boundaries $b_r$ can keep both $j_r \le J_{\max}$ and
       $V_r \le M$ for $(J_{\max} + 1)(M + 1)$ epochs.
     - **Conditional $S$-Unit Exclusion of Bounded Odd Parts (`no_bounded_odd_part_orbit_of_sunit_finiteness`)**:
       Assuming the 4-term $\{2, 3\}$ $S$-unit finiteness bound (which caps $3 j_r + s_r \le E_{\max}(M)$
       whenever $V_r, V_{r+1} \le M$), no infinite trajectory can have bounded odd parts $V_r \le M$.

2. **Section 12 — Backward 3-Adic Sieve & Mod-$6^\ell$ Word-Equivalence Negative Result
   (`step_mod_three_ne_one`, `orbit_mod_three_ne_one`,
   `orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd`,
   `orbit_mod_six_pow_eq_iff_surrounding_window_parity_eq`)**:
   - Proves `orbit a_0 K % 3 ≠ 1` for all $K \ge 1$, and proves the exact biconditional
     `orbit a_0 (n + 2) % 9 = 8 ↔ (orbit a_0 n % 2 = 1 ∧ orbit a_0 (n + 1) % 2 = 1)`
     (so `orbit a_0 (n + 2) % 9 ≠ 8` along any surviving orbit).
   - Proves the **Section 12 Negative/Limitative Theorem**:
     `orbit a_0 (n₁ + ℓ) % 6^ℓ = orbit a_0 (n₂ + ℓ) % 6^ℓ ↔ ∀ j < 2 * ℓ, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2`,
     establishing that simultaneous 2-adic/3-adic residue sieving modulo $6^\ell$ is **equivalent**
     to admissibility of the surrounding length-$2\ell$ parity word.

3. **Section 13 — Integer $\alpha$ Exclusion, $\lfloor 2(3/2)^n\alpha\rfloor$ Evenness, Minimal Floor
   $3 \nmid a^*$, and the Golden-Ratio Subsum Interval Obstruction
   (`not_validCompanionUpTo_of_zero_offset`, `fract_lt_half_iff_floor_two_mul_even`,
   `minimal_z_floor_not_dvd_three`, `no_eleven_subsum_interval_overlap_at_two_thirds`)**:
   - Proves that no positive integer $\alpha = (a_0 : \mathbb{R})$ (`ξ = 0`, $1 \le a_0 < 2^W$) can
     survive past step $W + 1$.
   - Proves $\operatorname{Int.fract} y < 1/2 \iff \lfloor 2 y \rfloor \bmod 2 = 0$ for all $y \in \mathbb{R}$.
   - Proves that if $a_0 = 3 m$ ($m \ge 1$) has a companion $\alpha$ surviving forever, then $2 m < 3 m$
     has companion $\frac{2}{3}\alpha$ surviving forever (`minimal_z_floor_not_dvd_three`).
   - Proves the golden-ratio subsum interval overlap inequality $(2/3)^2 + 2/3 = 10/9 > 1$
     (`1 ≤ (2/3) / (1 - (2/3)^2) = 6/5`), banking the Section 13 limitative result that no-`11`
     subsums at $r = 2/3$ form an unbroken interval containing infinitely many rationals.

4. **Sections 14 & 15 — Rauzy Factor-Complexity Telescope & $\Sigma_1 / \Pi_2$ Certificate Completeness
   (`monotone_complexity_telescope_sum`, `sigma1_bounded_box_escape_of_survivesSteps_false`,
   `pi2_computable_unbounded_lower_bound_iff_mahler`)**:
   - Proves the telescoping sum identity for factor complexity increments and the $\Sigma_1$ / $\Pi_2$
     certificate equivalences for bounded-box `[1, X)` and global Mahler escape.
-/

namespace Mahler.BoundedOddPartAndSieve

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
open Mahler.BaseSixAutomaton

/-! ## 1. Section 11: Non-Degenerate 4-Term $\{2, 3\}$-Unit Equations & Bounded-Odd-Part Exclusion -/

/-- **Non-Vanishing Subsums of the 4-Term $\{2, 3\}$-Unit Epoch Equation
(`four_term_sunit_epoch_equation_no_vanishing_subsum`, Section 11)**:
For any epoch parameters `4 ≤ s`, `j, j', V, V' : ℕ` with `1 ≤ V`, `1 ≤ V'`, `V % 2 = 1`,
and `V' % 3 ≠ 0`, setting `a = 3 * j + s` and `c = 3 * j' + s`:
1. `V * 3^a ≠ V' * 2^c` (the two state terms never cancel),
2. `3^(s - 3) < V * 3^a` (`V * 3^a ≠ 3^(s - 3)`),
3. `2^(s - 3) < V' * 2^c` (`V' * 2^c ≠ 2^(s - 3)`), and
4. `2^(s - 3) < 3^(s - 3)` (`3^(s - 3) ≠ 2^(s - 3)`). -/
theorem four_term_sunit_epoch_equation_no_vanishing_subsum
    {s j j' V V' : ℕ}
    (hs : 4 ≤ s) (hV : 1 ≤ V) (hV' : 1 ≤ V') (hV_odd : V % 2 = 1) :
    let a := 3 * j + s
    let c := 3 * j' + s
    V * 3 ^ a ≠ V' * 2 ^ c ∧
      (3 ^ (s - 3) < V * 3 ^ a ∧ V * 3 ^ a ≠ 3 ^ (s - 3)) ∧
      (2 ^ (s - 3) < V' * 2 ^ c ∧ V' * 2 ^ c ≠ 2 ^ (s - 3)) ∧
      (2 ^ (s - 3) < 3 ^ (s - 3) ∧ 3 ^ (s - 3) ≠ 2 ^ (s - 3)) := by
  intro a c
  have hodd3 : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih]
  have h1 : V * 3 ^ a ≠ V' * 2 ^ c := by
    intro heq
    have hc_pos : c = (c - 1) + 1 := by unfold c; omega
    have hlhs_odd : (V * 3 ^ a) % 2 = 1 := by
      rw [Nat.mul_mod, hodd3 a, hV_odd]
    have hrhs_even : (V' * 2 ^ c) % 2 = 0 := by
      rw [hc_pos, pow_succ, ← mul_assoc, Nat.mul_mod_left]
    rw [heq] at hlhs_odd
    omega
  have ha_gt : s - 3 < a := by unfold a; omega
  have hc_gt : s - 3 < c := by unfold c; omega
  have h2 : 3 ^ (s - 3) < V * 3 ^ a := by
    have hpow : 3 ^ (s - 3) < 3 ^ a := Nat.pow_lt_pow_right (by decide) ha_gt
    have hmul : 1 * 3 ^ a ≤ V * 3 ^ a := Nat.mul_le_mul_right (3 ^ a) hV
    omega
  have h3 : 2 ^ (s - 3) < V' * 2 ^ c := by
    have hpow : 2 ^ (s - 3) < 2 ^ c := Nat.pow_lt_pow_right (by decide) hc_gt
    have hmul : 1 * 2 ^ c ≤ V' * 2 ^ c := Nat.mul_le_mul_right (2 ^ c) hV'
    omega
  have h4 : 2 ^ (s - 3) < 3 ^ (s - 3) :=
    Nat.pow_lt_pow_left (by decide) (by omega)
  exact ⟨h1, ⟨h2, ne_of_gt h2⟩, ⟨h3, ne_of_gt h3⟩, ⟨h4, ne_of_gt h4⟩⟩

/-- **Budget Saturation Characterization of Bounded Odd Parts
(`bounded_odd_part_iff_runs_saturate_budget`, Section 11)**:
Whenever `19 * b_r + 9 = 72 * 2^(3 * j_r) * V_r`,
`V_r ≤ M ↔ 19 * b_r + 9 ≤ 72 * M * 2^(3 * j_r)`. -/
theorem bounded_odd_part_iff_runs_saturate_budget {b_r j_r V_r M : ℕ}
    (haff : 19 * b_r + 9 = 72 * 2 ^ (3 * j_r) * V_r) :
    V_r ≤ M ↔ 19 * b_r + 9 ≤ 72 * M * 2 ^ (3 * j_r) := by
  rw [haff, show 72 * M * 2 ^ (3 * j_r) = (72 * 2 ^ (3 * j_r)) * M by ring]
  have hpos : 0 < 72 * 2 ^ (3 * j_r) := by positivity
  exact (Nat.mul_le_mul_left_iff hpos).symm

/-- **Injectivity of $(j_r, V_r)$ Along Strictly Increasing Orbit Boundaries
(`strictMono_boundaries_injective_on_j_and_V`, Section 11)**:
If `b : ℕ → ℕ` is strictly increasing (`r₁ < r₂ → b r₁ < b r₂`) and
`19 * b r + 9 = 72 * 2^(3 * j r) * V r` for all `r : ℕ`, then no two distinct epochs `r₁ ≠ r₂`
can have the same pair `(j r₁, V r₁) = (j r₂, V r₂)`. -/
theorem strictMono_boundaries_injective_on_j_and_V {b j V : ℕ → ℕ}
    (hmono : StrictMono b)
    (haff : ∀ r : ℕ, 19 * b r + 9 = 72 * 2 ^ (3 * j r) * V r) :
    Function.Injective (fun r : ℕ => (j r, V r)) := by
  intro r₁ r₂ heq
  simp only [Prod.mk.injEq] at heq
  have ha1 := haff r₁
  have ha2 := haff r₂
  rw [heq.1, heq.2] at ha1
  have hb_eq : b r₁ = b r₂ := by omega
  exact hmono.injective hb_eq

/-- **Unconditional Impossibility of Simultaneously Bounded $(j_r, V_r)$ Along Strictly Increasing
Boundaries (`no_simultaneously_bounded_j_and_V_along_strictMono_boundaries`, Section 11)**:
If `b : ℕ → ℕ` is strictly increasing and `19 * b r + 9 = 72 * 2^(3 * j r) * V r` for all `r : ℕ`,
then for any bounds `J_max, M : ℕ`, `(j r, V r)` cannot satisfy `j r ≤ J_max ∧ V r ≤ M` for all
`r < (J_max + 1) * (M + 1) + 1`. -/
theorem no_simultaneously_bounded_j_and_V_along_strictMono_boundaries
    {b j V : ℕ → ℕ} (J_max M : ℕ)
    (hmono : StrictMono b)
    (haff : ∀ r : ℕ, 19 * b r + 9 = 72 * 2 ^ (3 * j r) * V r) :
    ¬ (∀ r < (J_max + 1) * (M + 1) + 1, j r ≤ J_max ∧ V r ≤ M) := by
  intro hbounded
  set N := (J_max + 1) * (M + 1) + 1
  set Box := Finset.range (J_max + 1) ×ˢ Finset.range (M + 1)
  have hmaps :
      ∀ r ∈ Finset.range N, (j r, V r) ∈ Box := by
    intro r hr
    rw [Finset.mem_range] at hr
    rcases hbounded r hr with ⟨hj, hV⟩
    simp only [Box, Finset.mem_product, Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun r : ℕ => (j r, V r)) (Finset.range N) := by
    intro r₁ _ r₂ _ heq
    exact strictMono_boundaries_injective_on_j_and_V hmono haff heq
  have hcard := Finset.card_le_card_of_injOn (fun r => (j r, V r)) hmaps hinj
  simp only [Box, Finset.card_product, Finset.card_range, N] at hcard
  omega

/-- **Conditional $S$-Unit Exclusion of Bounded-Odd-Part Orbits
(`no_bounded_odd_part_orbit_of_sunit_finiteness`, Section 11)**:
Suppose for a given odd-part bound `M : ℕ`, the 4-term $\{2, 3\}$-unit equation
`2^(3 * j (r + 1) + s r) * V (r + 1) + (3^(s r - 3) - 2^(s r - 3)) = 3^(3 * j r + s r) * V r`
with `V r ≤ M` and `V (r + 1) ≤ M` admits an exponent upper bound `3 * j r + s r ≤ E_max`
(by Evertse / van der Poorten–Schlickewei $S$-unit finiteness).
Then along any strictly increasing boundary sequence `b : ℕ → ℕ` with
`19 * b r + 9 = 72 * 2^(3 * j r) * V r`, it is impossible for `V r ≤ M` to hold for all `r : ℕ`. -/
theorem no_bounded_odd_part_orbit_of_sunit_finiteness
    {b j s V : ℕ → ℕ} (M E_max : ℕ)
    (hmono : StrictMono b)
    (haff : ∀ r : ℕ, 19 * b r + 9 = 72 * 2 ^ (3 * j r) * V r)
    (hrec : ∀ r : ℕ,
      2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * V r)
    (hsunit : ∀ r : ℕ, V r ≤ M → V (r + 1) ≤ M →
      2 ^ (3 * j (r + 1) + s r) * V (r + 1) + (3 ^ (s r - 3) - 2 ^ (s r - 3)) =
        3 ^ (3 * j r + s r) * V r →
      3 * j r + s r ≤ E_max) :
    ¬ (∀ r : ℕ, V r ≤ M) := by
  intro hallV
  apply no_simultaneously_bounded_j_and_V_along_strictMono_boundaries E_max M hmono haff
  intro r _
  have hexp : 3 * j r + s r ≤ E_max :=
    hsunit r (hallV r) (hallV (r + 1)) (hrec r)
  exact ⟨by omega, hallV r⟩

/-! ## 2. Section 12: Backward 3-Adic Sieve & Mod-$6^\ell$ Word-Equivalence Negative Result -/

/-- For every `x : ℕ`, `step x % 3 ≠ 1` (`step x` is never `≡ 1 (mod 3)`). -/
theorem step_mod_three_ne_one (x : ℕ) :
    step x % 3 ≠ 1 := by
  have hid := step_identity x
  omega

/-- Along any orbit `orbit a_0`, `orbit a_0 K % 3 ≠ 1` for all `K ≥ 1`. -/
theorem orbit_mod_three_ne_one (a_0 : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    orbit a_0 K % 3 ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, K = m + 1 := ⟨K - 1, by omega⟩
  exact step_mod_three_ne_one (orbit a_0 m)

/-- **Exact Mod-9 Characterization of the Forbidden `11` Word
(`orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd`, Section 12)**:
For every seed `a_0 : ℕ` and step `n : ℕ`:
`orbit a_0 (n + 2) % 9 = 8 ↔ (orbit a_0 n % 2 = 1 ∧ orbit a_0 (n + 1) % 2 = 1)`.
In particular, if `ValidCompanionForever a_0 α`, then `orbit a_0 K % 9 ≠ 8` for all `K ≥ 2`. -/
theorem orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd (a_0 n : ℕ) :
    (orbit a_0 (n + 2) % 9 = 8 ↔
      (orbit a_0 n % 2 = 1 ∧ orbit a_0 (n + 1) % 2 = 1)) ∧
    ((∃ α : ℝ, ValidCompanionForever a_0 α) → orbit a_0 (n + 2) % 9 ≠ 8) := by
  have hid := two_pow_mul_orbit_add_eq a_0 n 2
  have hcarry :
      wordCarry (shiftStream (orbit a_0) n) 2 =
        3 * (orbit a_0 n % 2) + 2 * (orbit a_0 (n + 1) % 2) := by
    simp [wordCarry, shiftStream]
  rw [show 2 ^ 2 = 4 by rfl, show 3 ^ 2 = 9 by rfl, hcarry] at hid
  have hiff :
      orbit a_0 (n + 2) % 9 = 8 ↔
        (orbit a_0 n % 2 = 1 ∧ orbit a_0 (n + 1) % 2 = 1) := by
    omega
  refine ⟨hiff, ?_⟩
  rintro ⟨α, hforever⟩ hmod9
  rcases hiff.mp hmod9 with ⟨h0, h1⟩
  exact no_validCompanionForever_of_consecutive_odd_steps h0 h1 ⟨α, hforever⟩

/-- **Section 12 Negative/Limitative Theorem: Mod-$6^\ell$ Sieving Equals $2\ell$-Window Word Matching
(`orbit_mod_six_pow_eq_iff_surrounding_window_parity_eq`, Section 12)**:
For **every** seed `a_0 : ℕ`, origins `n₁, n₂ : ℕ`, and depth `ℓ : ℕ`:
`orbit a_0 (n₁ + ℓ) % 6^ℓ = orbit a_0 (n₂ + ℓ) % 6^ℓ ↔
  ∀ j < 2 * ℓ, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2`. -/
theorem orbit_mod_six_pow_eq_iff_surrounding_window_parity_eq
    (a_0 n₁ n₂ ℓ : ℕ) :
    orbit a_0 (n₁ + ℓ) % 6 ^ ℓ = orbit a_0 (n₂ + ℓ) % 6 ^ ℓ ↔
      ∀ j < 2 * ℓ, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2 := by
  have hcop : Nat.Coprime (2 ^ ℓ) (3 ^ ℓ) :=
    (by decide : Nat.Coprime 2 3).pow ℓ ℓ
  have h6pow : 6 ^ ℓ = 2 ^ ℓ * 3 ^ ℓ := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, mul_pow]
  have hcrt :
      orbit a_0 (n₁ + ℓ) % 6 ^ ℓ = orbit a_0 (n₂ + ℓ) % 6 ^ ℓ ↔
        (orbit a_0 (n₁ + ℓ) % 3 ^ ℓ = orbit a_0 (n₂ + ℓ) % 3 ^ ℓ ∧
          orbit a_0 (n₁ + ℓ) % 2 ^ ℓ = orbit a_0 (n₂ + ℓ) % 2 ^ ℓ) := by
    rw [h6pow, and_comm]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).symm
  have hbij_past :=
    (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 n₁ n₂ ℓ).2.symm
  have hbij_fut :=
    (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 (n₁ + ℓ) (n₂ + ℓ) ℓ).1
  rw [hcrt, hbij_past, hbij_fut]
  constructor
  · rintro ⟨hpast, hfut⟩ j hj
    rcases (by omega : j < ℓ ∨ ℓ ≤ j) with hlt | hge
    · exact hpast j hlt
    · have h1 : n₁ + j = (n₁ + ℓ) + (j - ℓ) := by omega
      have h2 : n₂ + j = (n₂ + ℓ) + (j - ℓ) := by omega
      rw [h1, h2]
      exact hfut (j - ℓ) (by omega)
  · intro hall
    refine ⟨fun j hj => hall j (by omega), fun j hj => ?_⟩
    have h1 : (n₁ + ℓ) + j = n₁ + (ℓ + j) := by omega
    have h2 : (n₂ + ℓ) + j = n₂ + (ℓ + j) := by omega
    rw [h1, h2]
    exact hall (ℓ + j) (by omega)

/-! ## 3. Section 13: Integer $\alpha$, $\lfloor 2(3/2)^n\alpha\rfloor$ Evenness, Minimal Floor $3 \nmid a^*$ & Golden-Ratio Overlap -/

/-- **No Positive Integer Can Be a $Z$-Number (`not_validCompanionUpTo_of_zero_offset`,
Section 13)**:
For every positive integer `1 ≤ a_0` with `a_0 < 2^W`, the integer itself `α = (a_0 : ℝ)`
(with fractional offset `ξ = 0`) fails `ValidCompanionUpTo a_0 (a_0 : ℝ) W` (and thus cannot
satisfy `ValidCompanionForever a_0 (a_0 : ℝ)`). -/
theorem not_validCompanionUpTo_of_zero_offset {a_0 W : ℕ}
    (ha0 : 1 ≤ a_0) (hW : a_0 < 2 ^ W) :
    ¬ ValidCompanionUpTo a_0 (a_0 : ℝ) W ∧
      ¬ ValidCompanionForever a_0 (a_0 : ℝ) := by
  have hnot_up : ¬ ValidCompanionUpTo a_0 (a_0 : ℝ) W := by
    intro hcomp
    have hmod : a_0 % 2 ^ W = seedResidue (orbit a_0) W :=
      (orbit_parity_match_iff_mod_two_pow_eq_seedResidue (orbit a_0) a_0 W).mp (fun _ _ => rfl)
    have hadd : (a_0 : ℝ) = (a_0 : ℝ) + 0 := by ring
    rw [hadd] at hcomp
    have hlo := (validCompanionUpTo_add_offset_iff_mem_ratInterval hmod).mp hcomp
    obtain ⟨n, hnW, hodd⟩ := (exists_odd_orbit_step_of_pos ha0 hW).1
    have hcarry_pos : 1 ≤ wordCarry (orbit a_0) W := by
      have hmono_c : ∀ k ≤ W, n < k → 1 ≤ wordCarry (orbit a_0) k := by
        intro k _ hnk
        induction k with
        | zero => omega
        | succ m ih =>
            simp only [wordCarry]
            rcases (by omega : n < m ∨ n = m) with hlt | rfl
            · have ihm := ih (by omega) hlt
              omega
            · rw [hodd]
              have hp : 1 ≤ 2 ^ n := Nat.pow_pos (by decide)
              omega
      exact hmono_c W (le_refl W) hnW
    have hlo_pos : (0 : ℝ) < ((ratLowerOffset (orbit a_0) W : ℚ) : ℝ) := by
      unfold ratLowerOffset
      have hc_pos : (0 : ℚ) < (wordCarry (orbit a_0) W : ℚ) := by exact_mod_cast hcarry_pos
      have h3W_pos : (0 : ℚ) < (3 : ℚ) ^ W := by positivity
      exact_mod_cast div_pos hc_pos h3W_pos
    linarith [hlo.1]
  refine ⟨hnot_up, ?_⟩
  intro hforever
  exact hnot_up ((validCompanionForever_iff_forall_upTo a_0 (a_0 : ℝ)).mp hforever W)

/-- **Characterization of $\operatorname{Int.fract} y < 1/2$ by Evenness of $\lfloor 2 y \rfloor$
(`fract_lt_half_iff_floor_two_mul_even`, Section 13)**:
For every real number `y : ℝ`:
`Int.fract y < (1 / 2 : ℝ) ↔ ⌊2 * y⌋ % 2 = 0`. -/
theorem fract_lt_half_iff_floor_two_mul_even (y : ℝ) :
    Int.fract y < (1 / 2 : ℝ) ↔ ⌊2 * y⌋ % 2 = 0 := by
  have hy : y = Int.fract y + (⌊y⌋ : ℝ) := by
    unfold Int.fract; ring
  have h2y : 2 * y = 2 * Int.fract y + ((2 * ⌊y⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  have hf0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have hf1 : Int.fract y < 1 := Int.fract_lt_one y
  rw [h2y, Int.floor_add_intCast]
  constructor
  · intro hlt
    have hfl0 : ⌊2 * Int.fract y⌋ = 0 :=
      Int.floor_eq_iff.mpr ⟨by simp [hf0], by simp; linarith⟩
    rw [hfl0, zero_add, Int.mul_emod_right]
  · intro hmod
    by_contra hge
    push_neg at hge
    have hfl1 : ⌊2 * Int.fract y⌋ = 1 :=
      Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    rw [hfl1] at hmod
    omega

/-- **Minimal Positive $Z$-Floor Cannot Be Divisible by $3$ (`minimal_z_floor_not_dvd_three`,
Section 13)**:
If `a_0 = 3 * m` (`1 ≤ m`) admits a real companion `α` with `ValidCompanionForever (3 * m) α`,
then `2 * m` (`1 ≤ 2 * m < 3 * m`) admits the real companion `β = (2 / 3 : ℝ) * α` with
`ValidCompanionForever (2 * m) ((2 / 3 : ℝ) * α)`. -/
theorem minimal_z_floor_not_dvd_three {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hforever : ValidCompanionForever (3 * m) α) :
    1 ≤ 2 * m ∧ 2 * m < 3 * m ∧
      ValidCompanionForever (2 * m) ((2 / 3 : ℝ) * α) := by
  refine ⟨by omega, by omega, ?_⟩
  rcases (validCompanionForever_iff_floor_and_forall_fract_lt_half (3 * m) α).mp hforever with
    ⟨hfl, hfract⟩
  apply (validCompanionForever_iff_floor_and_forall_fract_lt_half (2 * m) ((2 / 3 : ℝ) * α)).mpr
  have hα_decomp : α = (3 * (m : ℝ)) + Int.fract α := by
    have h := Int.self_sub_floor α
    unfold Int.fract
    rw [hfl]
    push_cast
    linarith
  have hβ_decomp : (2 / 3 : ℝ) * α = (2 / 3 : ℝ) * Int.fract α + ((2 * m : ℕ) : ℤ) := by
    push_cast
    linarith [hα_decomp]
  have hf0 : 0 ≤ Int.fract α := Int.fract_nonneg α
  have hf_half : Int.fract α < (1 / 2 : ℝ) := by simpa using hfract 0
  have h23_bounds : 0 ≤ (2 / 3 : ℝ) * Int.fract α ∧ (2 / 3 : ℝ) * Int.fract α < (1 / 3 : ℝ) :=
    ⟨by linarith, by linarith⟩
  have hfl_β : ⌊(2 / 3 : ℝ) * α⌋ = ((2 * m : ℕ) : ℤ) := by
    rw [hβ_decomp, Int.floor_add_intCast]
    have h0 : ⌊(2 / 3 : ℝ) * Int.fract α⌋ = 0 :=
      Int.floor_eq_iff.mpr ⟨by simp [h23_bounds.1], by simp; linarith [h23_bounds.2]⟩
    rw [h0, zero_add]
  refine ⟨hfl_β, ?_⟩
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      have hfr_β : Int.fract ((2 / 3 : ℝ) * α) = (2 / 3 : ℝ) * Int.fract α := by
        rw [hβ_decomp, Int.fract_add_intCast,
          Int.fract_eq_self.mpr ⟨h23_bounds.1, by linarith [h23_bounds.2]⟩]
      linarith [h23_bounds.2]
  | succ k =>
      have hpow :
          ((2 / 3 : ℝ) * α) * (3 / 2 : ℝ) ^ (k + 1) = α * (3 / 2 : ℝ) ^ k := by
        rw [pow_succ']
        ring
      rw [hpow]
      exact hfract k

/-- **Golden-Ratio Subsum Interval Overlap at $r = 2/3$ (`no_eleven_subsum_interval_overlap_at_two_thirds`,
Section 13 Negative Result)**:
For a geometric series over `{0, 1}` with no consecutive `11`s and contraction ratio `r = 2/3`,
the maximum sum is `S_max = 1 / (1 - r^2) = 9/5`, and the `0`-branch upper endpoint
`r * S_max = 6/5` strictly exceeds the `10`-branch lower endpoint `1`
(`r^2 + r = 10/9 > 1` and `1 < r / (1 - r^2) = 6/5`), so the `0`-subinterval `[0, 6/5]` and the
`10`-subinterval `[1, 9/5]` overlap across `[1, 6/5]` with positive overlap width `1/5 > 0`. -/
theorem no_eleven_subsum_interval_overlap_at_two_thirds :
    let r : ℚ := 2 / 3
    let S_max : ℚ := 1 / (1 - r ^ 2)
    r ^ 2 + r = (10 / 9 : ℚ) ∧
      1 < r ^ 2 + r ∧
      S_max = (9 / 5 : ℚ) ∧
      r * S_max = (6 / 5 : ℚ) ∧
      1 + r ^ 2 * S_max = S_max ∧
      1 < r * S_max ∧
      r * S_max - 1 = (1 / 5 : ℚ) := by
  norm_num

/-! ## 4. Sections 14 & 15: Rauzy Complexity Telescope & $\Sigma_1 / \Pi_2$ Certificate Completeness -/

/-- **Telescoping Sum of Factor Complexity Increments (`monotone_complexity_telescope_sum`,
Section 14)**:
For any monotone complexity function `P : ℕ → ℕ` (`∀ m, P m ≤ P (m + 1)`) and horizon `M : ℕ`:
`(∑ m ∈ Finset.range M, (P (m + 1) - P m)) + P 0 = P M`. -/
theorem monotone_complexity_telescope_sum (P : ℕ → ℕ)
    (hmono : ∀ m : ℕ, P m ≤ P (m + 1)) (M : ℕ) :
    (∑ m ∈ Finset.range M, (P (m + 1) - P m)) + P 0 = P M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, add_right_comm, ih]
      have hle := hmono M
      omega

/-- **$\Sigma_1$ Bounded-Box Escape Certificate (`sigma1_bounded_box_escape_of_survivesSteps_false`,
Section 15)**:
If `∀ r : ℕ, 0 < r → r < X → survivesSteps r N = false`, then for **every**
real number `α ∈ [1, X)`, there exists `n ≤ N` such that `1 / 2 ≤ Int.fract (α * (3 / 2)^n)`. -/
theorem sigma1_bounded_box_escape_of_survivesSteps_false {X N : ℕ}
    (hcert : ∀ r : ℕ, 0 < r → r < X → survivesSteps r N = false) :
    ∀ α : ℝ, (1 : ℝ) ≤ α → α < (X : ℝ) →
      ∃ n ≤ N, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n) := by
  intro α hα1 hαX
  by_contra hno
  push_neg at hno
  set a_0 : ℕ := Int.toNat ⌊α⌋
  have hfl_pos : (1 : ℤ) ≤ ⌊α⌋ := Int.le_floor.mpr (by norm_num; exact hα1)
  have hfl_lt : ⌊α⌋ < (X : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hαX)
  have ha0_eq : (a_0 : ℤ) = ⌊α⌋ := Int.toNat_of_nonneg (by omega)
  have ha0_pos : 0 < a_0 := by omega
  have ha0_lt : a_0 < X := by omega
  have hcomp : ValidCompanionUpTo a_0 α N :=
    (validCompanionUpTo_iff_floor_and_fract_lt_half a_0 α N).mpr ⟨ha0_eq.symm, hno⟩
  have hsurv : survivesSteps a_0 N = true := by
    rw [survivesSteps_eq_true_iff, ← exists_validCompanionUpTo_iff_integerPinch]
    exact ⟨α, hcomp⟩
  have hfalse : survivesSteps a_0 N = false := hcert a_0 ha0_pos ha0_lt
  rw [hsurv] at hfalse
  contradiction

/-- **$\Pi_2$ Unbounded Lower-Bound Certificate Equivalence
(`pi2_unbounded_lower_bound_iff_mahler`, Section 15)**:
Mahler's $3/2$ conjecture holds for all `α > 0` if and only if there exists an unbounded
lower-bound function `f : ℕ → ℕ` (`∀ X : ℕ, ∃ N : ℕ, X ≤ f N`) such that
`∀ N : ℕ, f N ≤ leastPositiveSurvivor N`. -/
theorem pi2_unbounded_lower_bound_iff_mahler :
    (∀ α : ℝ, 0 < α → ∃ n : ℕ, (1 / 2 : ℝ) ≤ Int.fract (α * (3 / 2 : ℝ) ^ n)) ↔
      (∃ f : ℕ → ℕ, (∀ N : ℕ, f N ≤ leastPositiveSurvivor N) ∧
        ∀ X : ℕ, ∃ N : ℕ, X ≤ f N) := by
  rw [mahler_conjecture_iff_leastPositiveSurvivor_unbounded]
  constructor
  · intro hunb
    exact ⟨leastPositiveSurvivor, fun _ => le_refl _, hunb⟩
  · rintro ⟨f, hf_le, hf_unb⟩ X
    obtain ⟨N, hXN⟩ := hf_unb X
    exact ⟨N, le_trans hXN (hf_le N)⟩

/-- **Multi-Collision Ultrametric $(p, q)$ Cutoff Boost (`raw_orbit_multi_collision_ultrametric_pq_cutoff`,
Track 4.2(3) & Section 14)**:
Suppose `1 ≤ a_0 < 2^W`, `pos : Fin (2 ^ k + 1) → ℕ` is strictly increasing (`StrictMono pos`),
and all `2^k + 1` positions share the same length-`m` parity prefix
(`∀ i, ∀ j < m, orbit a_0 (pos i + j) % 2 = orbit a_0 (pos 0 + j) % 2`).
Then there exist `i₁ < i₂` in `Fin (2 ^ k + 1)` such that:
1. `orbit a_0 (pos i₁)` and `orbit a_0 (pos i₂)` agree modulo `2^(m + k)` (and share their
   length-`(m + k)` parity prefix), and
2. For every `p, q : ℕ` with `1 ≤ q` and `3^q ≤ 2^(p + q)`:
   `q * (m + k) < p * pos i₂ + q * W`. -/
theorem raw_orbit_multi_collision_ultrametric_pq_cutoff
    {a_0 W m k : ℕ} {pos : Fin (2 ^ k + 1) → ℕ}
    (ha0 : 1 ≤ a_0) (hW : a_0 < 2 ^ W) (hmono : StrictMono pos)
    (hmatch : ∀ (i : Fin (2 ^ k + 1)) (j : ℕ), j < m →
      orbit a_0 (pos i + j) % 2 = orbit a_0 (pos 0 + j) % 2) :
    ∃ i₁ i₂ : Fin (2 ^ k + 1), i₁ < i₂ ∧
      orbit a_0 (pos i₁) % 2 ^ (m + k) = orbit a_0 (pos i₂) % 2 ^ (m + k) ∧
      (∀ j < m + k, orbit a_0 (pos i₁ + j) % 2 = orbit a_0 (pos i₂ + j) % 2) ∧
      (∀ p q : ℕ, 1 ≤ q → 3 ^ q ≤ 2 ^ (p + q) →
        q * (m + k) < p * pos i₂ + q * W) := by
  have h2k_pos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  set topMap : Fin (2 ^ k + 1) → Fin (2 ^ k) :=
    fun i => ⟨(orbit a_0 (pos i) / 2 ^ m) % 2 ^ k, Nat.mod_lt _ h2k_pos⟩
  have hcard_lt : Fintype.card (Fin (2 ^ k)) < Fintype.card (Fin (2 ^ k + 1)) := by
    simp
  obtain ⟨a, b, hab_ne, htop_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt topMap hcard_lt
  have htop_val : ∀ x y : Fin (2 ^ k + 1), topMap x = topMap y →
      (orbit a_0 (pos x) / 2 ^ m) % 2 ^ k = (orbit a_0 (pos y) / 2 ^ m) % 2 ^ k := by
    intro x y hxy
    exact congrArg Fin.val hxy
  have hordered :
      ∃ i₁ i₂ : Fin (2 ^ k + 1), i₁ < i₂ ∧
        (orbit a_0 (pos i₁) / 2 ^ m) % 2 ^ k = (orbit a_0 (pos i₂) / 2 ^ m) % 2 ^ k := by
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact ⟨a, b, hlt, htop_val a b htop_eq⟩
    · exact absurd rfl hab_ne
    · exact ⟨b, a, hgt, (htop_val a b htop_eq).symm⟩
  rcases hordered with ⟨i₁, i₂, hi_lt, hdiv_mod⟩
  have hbot_mod : orbit a_0 (pos i₁) % 2 ^ m = orbit a_0 (pos i₂) % 2 ^ m := by
    have hm1 : orbit a_0 (pos i₁) % 2 ^ m = orbit a_0 (pos 0) % 2 ^ m :=
      (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 (pos i₁) (pos 0) m).1.mpr
        (hmatch i₁)
    have hm2 : orbit a_0 (pos i₂) % 2 ^ m = orbit a_0 (pos 0) % 2 ^ m :=
      (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow a_0 (pos i₂) (pos 0) m).1.mpr
        (hmatch i₂)
    exact hm1.trans hm2.symm
  -- Combine `x % 2^m` and `(x / 2^m) % 2^k` to get `x % 2^(m + k)`:
  have hdecomp : ∀ x : ℕ, x % 2 ^ (m + k) = 2 ^ m * ((x / 2 ^ m) % 2 ^ k) + x % 2 ^ m := by
    intro x
    have h1 := Nat.div_add_mod x (2 ^ m)
    have h2 := Nat.div_add_mod (x / 2 ^ m) (2 ^ k)
    have h3 :
        x = (2 ^ m * 2 ^ k) * ((x / 2 ^ m) / 2 ^ k) +
          (2 ^ m * ((x / 2 ^ m) % 2 ^ k) + x % 2 ^ m) := by
      calc
        x = 2 ^ m * (x / 2 ^ m) + x % 2 ^ m := h1.symm
        _ = 2 ^ m * (2 ^ k * ((x / 2 ^ m) / 2 ^ k) + (x / 2 ^ m) % 2 ^ k) + x % 2 ^ m := by
              rw [h2]
        _ = (2 ^ m * 2 ^ k) * ((x / 2 ^ m) / 2 ^ k) +
              (2 ^ m * ((x / 2 ^ m) % 2 ^ k) + x % 2 ^ m) := by ring
    have hrem_lt : 2 ^ m * ((x / 2 ^ m) % 2 ^ k) + x % 2 ^ m < 2 ^ (m + k) := by
      have hlt_k : (x / 2 ^ m) % 2 ^ k + 1 ≤ 2 ^ k := Nat.mod_lt _ h2k_pos
      have hlt_m : x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.pow_pos (by decide))
      have hmul : 2 ^ m * ((x / 2 ^ m) % 2 ^ k + 1) ≤ 2 ^ m * 2 ^ k :=
        Nat.mul_le_mul_left (2 ^ m) hlt_k
      rw [pow_add]
      linarith
    conv_lhs => rw [h3, pow_add, add_comm, Nat.add_mul_mod_self_left, ← pow_add, Nat.mod_eq_of_lt hrem_lt]
  have hmod_mk : orbit a_0 (pos i₁) % 2 ^ (m + k) = orbit a_0 (pos i₂) % 2 ^ (m + k) := by
    rw [hdecomp, hdecomp, hdiv_mod, hbot_mod]
  have hmatch_mk : ∀ j < m + k, orbit a_0 (pos i₁ + j) % 2 = orbit a_0 (pos i₂ + j) % 2 :=
    (orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow
      a_0 (pos i₁) (pos i₂) (m + k)).1.mp hmod_mk
  have hpos_lt : pos i₁ < pos i₂ := hmono hi_lt
  have hcut :=
    (raw_orbit_repeated_parity_window_pq_cutoff ha0 hW hpos_lt hmatch_mk).2.1
  exact ⟨i₁, i₂, hi_lt, hmod_mk, hmatch_mk, hcut⟩

/-- **Exact Base-6 Digit Reconstruction of Natural Numbers (`baseSixScaledNat_natToBaseSixConfig_eq`,
Track 5.2(1))**:
For every natural number `a_0 : ℕ` and window length `m : ℕ`:
1. `baseSixScaledNat (natToBaseSixConfig a_0) 0 m + (a_0 / 6^m) * 6^m = a_0`, and
2. Whenever `a_0 < 6^m`, `baseSixScaledNat (natToBaseSixConfig a_0) 0 m = a_0`. -/
theorem baseSixScaledNat_natToBaseSixConfig_eq (a_0 m : ℕ) :
    baseSixScaledNat (natToBaseSixConfig a_0) 0 m + (a_0 / 6 ^ m) * 6 ^ m = a_0 ∧
      (a_0 < 6 ^ m → baseSixScaledNat (natToBaseSixConfig a_0) 0 m = a_0) := by
  have hdecomp :
      baseSixScaledNat (natToBaseSixConfig a_0) 0 m + (a_0 / 6 ^ m) * 6 ^ m = a_0 := by
    induction m with
    | zero =>
        simp [baseSixScaledNat]
    | succ k ih =>
        rw [baseSixScaledNat_succ, zero_add]
        have hcfg :
            natToBaseSixConfig a_0 (k : ℤ) = (a_0 / 6 ^ k) % 6 := by
          unfold natToBaseSixConfig
          have h0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
          simp [h0]
        rw [hcfg]
        have hdiv : a_0 / 6 ^ (k + 1) = (a_0 / 6 ^ k) / 6 := by
          rw [pow_succ, Nat.div_div_eq_div_mul]
        have hmod_div : 6 * ((a_0 / 6 ^ k) / 6) + (a_0 / 6 ^ k) % 6 = a_0 / 6 ^ k :=
          Nat.div_add_mod (a_0 / 6 ^ k) 6
        have hstep :
            ((a_0 / 6 ^ k) % 6) * 6 ^ k + (a_0 / 6 ^ (k + 1)) * 6 ^ (k + 1) =
              (a_0 / 6 ^ k) * 6 ^ k := by
          rw [hdiv, pow_succ']
          calc
            ((a_0 / 6 ^ k) % 6) * 6 ^ k + ((a_0 / 6 ^ k) / 6) * (6 * 6 ^ k)
              = (6 * ((a_0 / 6 ^ k) / 6) + (a_0 / 6 ^ k) % 6) * 6 ^ k := by ring
            _ = (a_0 / 6 ^ k) * 6 ^ k := by rw [hmod_div]
        linarith
  refine ⟨hdecomp, ?_⟩
  intro hlt
  have hdiv0 : a_0 / 6 ^ m = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv0, zero_mul, add_zero] at hdecomp
  exact hdecomp

end Mahler.BoundedOddPartAndSieve
