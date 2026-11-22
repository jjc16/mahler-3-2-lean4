import SubCeilingKneadingAutomatonAndGrandSynthesis54
import Mathlib.Data.Real.Irrational

/-!
# Split-Approximation & Recurrence No-Go Theorems for $e + \pi$ (`EP.1–EP.4`)

Formalizes the structural obstructions encountered when attacking the irrationality of $\xi = e + \pi$
via coupled Apéry/Beukers/Hermite integral forms $L = C(e + \pi) + M$:

1. **`EP.1` (`quadratic_sum_prod_irrational_disjunction`)**:
   If $\alpha \in \mathbb{R}$ satisfies no nontrivial integer quadratic equation
   (`∀ A B C : ℤ, A ≠ 0 → A * α ^ 2 + B * α + C ≠ 0`), then for every $\beta \in \mathbb{R}$,
   at least one of $\alpha + \beta$ and $\alpha \cdot \beta$ is irrational
   (`Irrational (α + β) ∨ Irrational (α * β)`).
2. **`EP.2` (`split_integer_offset_nearest_int_floor_no_go`)**:
   Any additive split $L = (C \alpha + B_1) + (C \beta + B_2)$ with **separate** integer offsets
   $B_1, B_2 \in \mathbb{Z}$ and $|C \beta + B_2| \le \varepsilon$ satisfies the universal lower bound
   `distToInt ((C : ℝ) * α) - ε ≤ |(C : ℝ) * (α + β) + ((B_1 + B_2 : ℤ) : ℝ)|`
   across **all** $B_1 \in \mathbb{Z}$ simultaneously, where `0 < distToInt ((C : ℝ) * α)` whenever
   `Irrational α` and `C ≠ 0`.
3. **`EP.3` (`second_order_recurrence_two_generator_span_collapse`)**:
   For any integer sequence $A : \mathbb{N} \to \mathbb{Z}$ satisfying a second-order recurrence
   `A (n + 2) = c n * A (n + 1) + d n * A n` (such as Hermite's $A_{s+2} = -(4s + 6) A_{s+1} + A_s$),
   every $L$-term combination $\sum_{j < L} u_j A(s + j)$ collapses into the rank-2 $\mathbb{Z}$-span
   `v_0 * A s + v_1 * A (s + 1)`, so adding higher basis terms never enlarges the multiplier lattice.
4. **`EP.4` (`denominator_divisible_multiplier_forces_exact_vanishing`)**:
   Under a rationality hypothesis $\xi = p / q$ (`1 ≤ q`), any candidate linear form $C \xi + M$
   whose multiplier $C$ is divisible by $q$ (e.g., $C$ containing $\operatorname{lcm}(1, \dots, N)$
   for $N \ge q$) and satisfies $|C \xi + M| < 1$ **must vanish identically** (`C * (p / q) + M = 0`),
   producing no contradiction unless strict non-vanishing is independently certified.
-/

namespace IrrationalityProbes.EPlusPi

/-- Distance from a real number `x` to the nearest integer: `min {x} (1 - {x})`. -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- **EP.1 (Algebraic Sum-Product Disjunction):**
If `α : ℝ` satisfies no nonzero integer quadratic equation (`∀ A B C : ℤ, A ≠ 0 → A * α^2 + B * α + C ≠ 0`),
then for every `β : ℝ`, `Irrational (α + β) ∨ Irrational (α * β)`. -/
theorem quadratic_sum_prod_irrational_disjunction
    {α : ℝ} (hno_quad : ∀ A B C : ℤ, A ≠ 0 → (A : ℝ) * α ^ 2 + (B : ℝ) * α + (C : ℝ) ≠ 0)
    (β : ℝ) :
    Irrational (α + β) ∨ Irrational (α * β) := by
  by_contra hboth
  have hs_not : ¬ Irrational (α + β) := fun h => hboth (Or.inl h)
  have hp_not : ¬ Irrational (α * β) := fun h => hboth (Or.inr h)
  unfold Irrational at hs_not hp_not
  rw [Classical.not_not] at hs_not hp_not
  rcases hs_not with ⟨qs, hqs⟩
  rcases hp_not with ⟨qp, hqp⟩
  have hqs_den_pos : (0 : ℤ) < (qs.den : ℤ) := by exact_mod_cast qs.pos
  have hqp_den_pos : (0 : ℤ) < (qp.den : ℤ) := by exact_mod_cast qp.pos
  set A : ℤ := (qs.den : ℤ) * (qp.den : ℤ)
  set B : ℤ := - qs.num * (qp.den : ℤ)
  set C : ℤ := (qs.den : ℤ) * qp.num
  have hA_ne : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (ne_of_gt hqs_den_pos) (ne_of_gt hqp_den_pos)
  have hqs_cast : (qs : ℝ) = (qs.num : ℝ) / (qs.den : ℝ) := by exact_mod_cast Rat.num_div_den qs |>.symm
  have hqp_cast : (qp : ℝ) = (qp.num : ℝ) / (qp.den : ℝ) := by exact_mod_cast Rat.num_div_den qp |>.symm
  have hsum_eq : (qs.den : ℝ) * (α + β) = (qs.num : ℝ) := by
    have hd_ne : (qs.den : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt qs.pos
    rw [← hqs, hqs_cast]
    field_simp
  have hprod_eq : (qp.den : ℝ) * (α * β) = (qp.num : ℝ) := by
    have hd_ne : (qp.den : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt qp.pos
    rw [← hqp, hqp_cast]
    field_simp
  have hquad_zero : (A : ℝ) * α ^ 2 + (B : ℝ) * α + (C : ℝ) = 0 := by
    dsimp [A, B, C]
    push_cast
    calc
      ((qs.den : ℝ) * (qp.den : ℝ)) * α ^ 2 + (-(qs.num : ℝ) * (qp.den : ℝ)) * α +
          (qs.den : ℝ) * (qp.num : ℝ)
          = (qp.den : ℝ) * α * ((qs.den : ℝ) * (α + β) - (qs.num : ℝ)) +
              (qs.den : ℝ) * ((qp.num : ℝ) - (qp.den : ℝ) * (α * β)) := by ring
      _ = (qp.den : ℝ) * α * ((qs.num : ℝ) - (qs.num : ℝ)) +
            (qs.den : ℝ) * ((qp.num : ℝ) - (qp.num : ℝ)) := by rw [hsum_eq, hprod_eq]
      _ = 0 := by ring
  exact hno_quad A B C hA_ne hquad_zero


/-- **EP.2 (Split-Offset Nearest-Integer Floor No-Go Theorem):**
1. `0 ≤ distToInt x ∧ distToInt x ≤ 1 / 2` for all `x : ℝ`.
2. `distToInt x ≤ |x + (B : ℝ)|` for **every** integer `B : ℤ`.
3. If `Irrational α` and `C ≠ 0`, then `0 < distToInt ((C : ℝ) * α)`.
4. For any split form `L = (C * α + B₁) + (C * β + B₂)` with `|C * β + B₂| ≤ ε`,
   `distToInt ((C : ℝ) * α) - ε ≤ |(C : ℝ) * (α + β) + ((B₁ + B₂ : ℤ) : ℝ)|`
   regardless of the integer choice `B₁ : ℤ`. -/
theorem split_integer_offset_nearest_int_floor_no_go :
    (∀ x : ℝ, 0 ≤ distToInt x ∧ distToInt x ≤ 1 / 2) ∧
    (∀ (x : ℝ) (B : ℤ), distToInt x ≤ |x + (B : ℝ)|) ∧
    (∀ (α : ℝ) (C : ℤ), Irrational α → C ≠ 0 → 0 < distToInt ((C : ℝ) * α)) ∧
    (∀ (α β ε : ℝ) (C B₁ B₂ : ℤ),
      |(C : ℝ) * β + (B₂ : ℝ)| ≤ ε →
      distToInt ((C : ℝ) * α) - ε ≤ |(C : ℝ) * (α + β) + ((B₁ + B₂ : ℤ) : ℝ)|) := by
  have hbounds : ∀ x : ℝ, 0 ≤ distToInt x ∧ distToInt x ≤ 1 / 2 := by
    intro x
    unfold distToInt
    have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have h1 : Int.fract x < 1 := Int.fract_lt_one x
    refine ⟨le_min h0 (by linarith), ?_⟩
    by_cases hhalf : Int.fract x ≤ 1 / 2
    · exact le_trans (min_le_left _ _) hhalf
    · exact le_trans (min_le_right _ _) (by linarith)
  have hfloor : ∀ (x : ℝ) (B : ℤ), distToInt x ≤ |x + (B : ℝ)| := by
    intro x B
    unfold distToInt
    have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have h1 : Int.fract x < 1 := Int.fract_lt_one x
    set k : ℤ := ⌊x⌋ + B
    have hxB : x + (B : ℝ) = Int.fract x + (k : ℝ) := by
      dsimp [k]
      have hf : Int.fract x = x - (⌊x⌋ : ℝ) := Int.self_sub_floor x
      push_cast
      linarith
    rw [hxB]
    rcases (by omega : k ≤ -1 ∨ k = 0 ∨ 1 ≤ k) with hk_neg | hk_zero | hk_pos
    · have hk_r : (k : ℝ) ≤ -1 := by exact_mod_cast hk_neg
      have hneg : Int.fract x + (k : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      exact le_trans (min_le_right _ _) (by linarith)
    · rw [hk_zero]
      simp only [Int.cast_zero, add_zero]
      rw [abs_of_nonneg h0]
      exact min_le_left _ _
    · have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      have hpos : 0 ≤ Int.fract x + (k : ℝ) := by linarith
      rw [abs_of_nonneg hpos]
      exact le_trans (min_le_right _ _) (by linarith)
  have hpos_irr : ∀ (α : ℝ) (C : ℤ), Irrational α → C ≠ 0 → 0 < distToInt ((C : ℝ) * α) := by
    intro α C hirr hC
    have hnonneg := (hbounds ((C : ℝ) * α)).1
    by_contra hnot
    have heq0 : distToInt ((C : ℝ) * α) = 0 := le_antisymm (not_lt.mp hnot) hnonneg
    unfold distToInt at heq0
    have h1 : Int.fract ((C : ℝ) * α) < 1 := Int.fract_lt_one ((C : ℝ) * α)
    rcases min_eq_iff.mp heq0 with ⟨hf0, _⟩ | ⟨hf1, _⟩
    · have hsub : (C : ℝ) * α - (⌊(C : ℝ) * α⌋ : ℝ) = 0 := by
        rw [Int.self_sub_floor ((C : ℝ) * α), hf0]
      have hC_r : (C : ℝ) ≠ 0 := by exact_mod_cast hC
      set q : ℚ := (⌊(C : ℝ) * α⌋ : ℚ) / (C : ℚ)
      have hq_eq : (q : ℝ) = α := by
        dsimp [q]
        push_cast
        field_simp
        linarith
      exact hirr ⟨q, hq_eq⟩
    · linarith
  refine ⟨hbounds, hfloor, hpos_irr, ?_⟩
  · intro α β ε C B₁ B₂ hβ
    set X : ℝ := (C : ℝ) * α + (B₁ : ℝ)
    set Y : ℝ := (C : ℝ) * β + (B₂ : ℝ)
    have hX_ge : distToInt ((C : ℝ) * α) ≤ |X| := hfloor ((C : ℝ) * α) B₁
    have hsum_eq : (C : ℝ) * (α + β) + ((B₁ + B₂ : ℤ) : ℝ) = X + Y := by
      dsimp [X, Y]
      push_cast
      ring
    rw [hsum_eq]
    have htri : |X| ≤ |X + Y| + |Y| := by
      have h := abs_add_le (X + Y) (-Y)
      have hcancel : X + Y + -Y = X := by ring
      rw [hcancel, abs_neg] at h
      exact h
    linarith


/-- **EP.3 (Second-Order Recurrence Rank-2 Span Collapse):**
If `A : ℕ → ℤ` satisfies `∀ n, A (n + 2) = c n * A (n + 1) + d n * A n`, then for every base
index `s : ℕ`, length `L : ℕ`, and weights `u : ℕ → ℤ`, there exist integers `v₀, v₁ : ℤ` such that
`∑ j ∈ Finset.range L, u j * A (s + j) = v₀ * A s + v₁ * A (s + 1)`. -/
theorem second_order_recurrence_two_generator_span_collapse
    (A c d : ℕ → ℤ)
    (hrec : ∀ n : ℕ, A (n + 2) = c n * A (n + 1) + d n * A n) :
    (∀ s k : ℕ, ∃ a₀ a₁ : ℤ, A (s + k) = a₀ * A s + a₁ * A (s + 1)) ∧
    (∀ (s L : ℕ) (u : ℕ → ℤ),
      ∃ v₀ v₁ : ℤ,
        (Finset.range L).sum (fun j => u j * A (s + j)) = v₀ * A s + v₁ * A (s + 1)) := by
  have hterm : ∀ s k : ℕ, ∃ a₀ a₁ : ℤ, A (s + k) = a₀ * A s + a₁ * A (s + 1) := by
    intro s k
    induction k using Nat.strong_induction_on with
    | h m ih =>
        rcases m with _ | m₁
        · exact ⟨1, 0, by simp⟩
        · rcases m₁ with _ | m₂
          · exact ⟨0, 1, by simp⟩
          · rcases ih m₂ (by omega) with ⟨p₀, p₁, hp⟩
            rcases ih (m₂ + 1) (by omega) with ⟨q₀, q₁, hq⟩
            have hidx : s + (m₂ + 2) = (s + m₂) + 2 := by omega
            have hidx1 : (s + m₂) + 1 = s + (m₂ + 1) := by omega
            refine ⟨c (s + m₂) * q₀ + d (s + m₂) * p₀, c (s + m₂) * q₁ + d (s + m₂) * p₁, ?_⟩
            rw [hidx, hrec (s + m₂), hidx1, hq, hp]
            ring
  refine ⟨hterm, ?_⟩
  intro s L u
  induction L with
  | zero =>
      exact ⟨0, 0, by simp⟩
  | succ m ih =>
      rcases ih with ⟨v₀, v₁, hv⟩
      rcases hterm s m with ⟨a₀, a₁, ha⟩
      refine ⟨v₀ + u m * a₀, v₁ + u m * a₁, ?_⟩
      rw [Finset.sum_range_succ, hv, ha]
      ring


/-- **EP.4 (Denominator-Divisible Multiplier Forces Exact Vanishing Under Rationality):**
If `ξ = (p : ℝ) / (q : ℝ)` (`1 ≤ q`) and `(q : ℤ) ∣ C`, then any linear form with
`|(C : ℝ) * ξ + (M : ℝ)| < 1` satisfies `(C : ℝ) * ξ + (M : ℝ) = 0` identically. -/
theorem denominator_divisible_multiplier_forces_exact_vanishing
    {p C M : ℤ} {q : ℕ} (hq : 1 ≤ q) (hdvd : (q : ℤ) ∣ C)
    (hsmall : |(C : ℝ) * ((p : ℝ) / (q : ℝ)) + (M : ℝ)| < 1) :
    (C : ℝ) * ((p : ℝ) / (q : ℝ)) + (M : ℝ) = 0 := by
  rcases hdvd with ⟨k, rfl⟩
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hint_eq : (((q : ℤ) * k : ℤ) : ℝ) * ((p : ℝ) / (q : ℝ)) + (M : ℝ) = ((k * p + M : ℤ) : ℝ) := by
    push_cast
    field_simp [hq_ne]
    ring
  rw [hint_eq] at hsmall ⊢
  set N : ℤ := k * p + M
  have habs_int : |(N : ℝ)| < (1 : ℝ) := hsmall
  have hlt1 : N < 1 := by
    have h := (abs_lt.mp habs_int).2
    exact_mod_cast h
  have hgt_neg1 : -1 < N := by
    have h := (abs_lt.mp habs_int).1
    exact_mod_cast h
  have hN0 : N = 0 := by omega
  rw [hN0]
  norm_num

#check @quadratic_sum_prod_irrational_disjunction
#check @split_integer_offset_nearest_int_floor_no_go
#check @second_order_recurrence_two_generator_span_collapse
#check @denominator_divisible_multiplier_forces_exact_vanishing

#print axioms quadratic_sum_prod_irrational_disjunction
#print axioms split_integer_offset_nearest_int_floor_no_go
#print axioms second_order_recurrence_two_generator_span_collapse
#print axioms denominator_divisible_multiplier_forces_exact_vanishing

end IrrationalityProbes.EPlusPi
