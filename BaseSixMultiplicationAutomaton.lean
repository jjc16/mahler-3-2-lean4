import ExactSeedResidueTreeAndStabilization
import ParitySurplusPotentialsAndSafetyGame

/-!
# Exact Base-6 Multiplication Cellular Automaton (`Π_{3/2, 6}`), Canonical Trace Bridge & Boundary Forcing

This module formalizes **Phase B (Sections B1, B2, B3)** and **Section 10.1–10.2** of the
general-proof research plan (`RESEARCH_PLAN_ARGON_GENERAL_PROOF.md`), building the exact
Kari–Kopra base-6 fractional multiplication cellular automaton $\Pi_{3/2, 6}$ (Kari 2012;
Kopra 2020, `arXiv:2005.05112`):

1. **The Base-6 Multiplication Cellular Automaton (`mulThreeCA`, `mulThreeHalvesCA`)**:
   - A base-6 configuration is a map `d : ℤ → ℕ` satisfying `IsBaseSixConfig d : ∀ i : ℤ, d i < 6`,
     where index `i : ℤ` carries weight `6^i`.
   - `mulThreeCA d i = 3 * (d i % 2) + d (i - 1) / 2` implements exact base-6 multiplication by `3`
     with a 2-cell local rule; `mulThreeHalvesCA d i = mulThreeCA (mulThreeCA d) (i + 1)` composes
     two `×3` steps with a left shift (`÷6`) to implement exact multiplication by `9/6 = 3/2`.
   - We prove digit-range preservation (`isBaseSixConfig_mulThreeCA`, `isBaseSixConfig_mulThreeHalvesCA`,
     `isBaseSixConfig_iterate_mulThreeHalvesCA`), the explicit radius-1 three-cell formula
     (`mulThreeHalvesCA_eq_local_rule`), and causal-cone locality over `n` steps
     (`mulThreeHalvesCA_iterate_causal_cone_congr`).

2. **Exact Flux Conservation & Rational Value Homomorphism (`baseSixScaledNat_mulThreeCA_flux`,
   `baseSixScaledNat_mulThreeHalvesCA_eq`, `baseSixWindowVal_mulThreeHalvesCA`,
   `baseSixWindowVal_iterate_mulThreeHalvesCA`)**:
   - For any finite window `[a, a + L)` in `ℤ`, `baseSixScaledNat d a L = ∑ k ∈ range L, d (a + k) * 6^k`
     satisfies the unconditional flux identity:
     `baseSixScaledNat (mulThreeCA d) a L + (d (a + L - 1) / 2) * 6^L = 3 * baseSixScaledNat d a L + d (a - 1) / 2`.
   - When `d` vanishes outside `[a, a + L)`, one step of `mulThreeHalvesCA` satisfies the exact integer
     homomorphism `2 * baseSixScaledNat (mulThreeHalvesCA d) (a - 1) (L + 2) = 3 * baseSixScaledNat d a L`
     and the rational value identity `baseSixWindowVal (mulThreeHalvesCA d) (a - 1) (L + 2) = (3/2) * baseSixWindowVal d a L`
     (and `(3/2)^n` after `n` steps).

3. **Canonical Base-6 Fractional-Part & Digit-`(-1)` Trace Equivalence (`fract_lt_half_iff_digit_neg_one_lt_three`,
   `noncanonical_tail_endpoint_counterexample`)**:
   - Decomposing any real/rational value at the radix point into integer part `I : ℕ`, first fractional
     digit `d_neg1 < 6`, and canonical tail `0 ≤ r < 1/6` (which excludes the all-`5` tail `r = 1/6`),
     we prove `Int.fract (I + (d_neg1 / 6 + r)) < 1 / 2 ↔ d_neg1 < 3` (`d_neg1 ∈ {0, 1, 2}`).
   - We also formalize the exact **Endpoint Counterexample** (`noncanonical_tail_endpoint_counterexample`):
     when the non-canonical all-`5` tail `r = 1/6` (`0.2555..._6 = 0.3_6 = 1/2`) is permitted,
     `d_neg1 = 2 < 3` even though `Int.fract (I + (2/6 + 1/6)) = 1/2 ≮ 1/2`.

4. **Integer-Side Left-Boundary Propagation, Finite Causal-Cone Escape Witnesses & The 2-Adic Ghost
   Trace Obstruction (`left_zero_boundary_mulThreeHalvesCA_iterate`, `seed_one_and_eight_base_six_trace_escape`,
   `zero_and_two_adic_ghost_trace_obstruction`)**:
   - Proves how the integer-side zero boundary `∀ i ≥ m, d i = 0` propagates across `n` steps.
   - Certifies concrete space-time trace escapes for `x = 1` (escapes at step `1` with `d_1(-1) = 3`)
     and `x = 8` (survives steps `0..4` in `{0, 1, 2}` and escapes at step `5` with `d_5(-1) = 4`,
     matching Kopra Figure 2's column-escape mechanism).
   - Formalizes the **Phase B3 Negative/Limitative Theorem**: the unconstrained `{0, 1, 2}` trace
     subshift contains both the all-zero configuration (`d ≡ 0`) and 2-adic ghost solutions (whose
     seed residues `seedResidue periodicThreeParity N` grow unboundedly with `N`, violating
     finite integer-side support `d i = 0` for `i ≥ m`). Thus no argument operating purely on the
     unconstrained trace subshift without the left-finite boundary can prove emptiness of Z-numbers.
-/

namespace Mahler.BaseSixAutomaton

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.InfiniteZNumberBridge
open Mahler.SeedResidueTree
open Mahler.ParitySurplusAndGames

/-! ## 1. The Base-6 Multiplication Cellular Automaton (`mulThreeCA` and `mulThreeHalvesCA`) -/

/-- A bi-infinite sequence `d : ℤ → ℕ` is a valid base-6 configuration if every cell lies in `{0, ..., 5}`. -/
def IsBaseSixConfig (d : ℤ → ℕ) : Prop :=
  ∀ i : ℤ, d i < 6

/-- Local cellular-automaton rule for multiplication by `3` in base `6`:
`mulThreeCA d i = 3 * (d i % 2) + d (i - 1) / 2`. -/
def mulThreeCA (d : ℤ → ℕ) (i : ℤ) : ℕ :=
  3 * (d i % 2) + d (i - 1) / 2

/-- Local cellular-automaton rule for multiplication by `3/2 = 9/6` in base `6` (`Π_{3/2, 6}`):
two applications of `mulThreeCA` followed by a left shift `i ↦ i + 1` (division by `6`). -/
def mulThreeHalvesCA (d : ℤ → ℕ) (i : ℤ) : ℕ :=
  mulThreeCA (mulThreeCA d) (i + 1)

/-- `mulThreeCA` preserves the base-6 digit alphabet `{0, ..., 5}`. -/
theorem isBaseSixConfig_mulThreeCA {d : ℤ → ℕ} (hd : IsBaseSixConfig d) :
    IsBaseSixConfig (mulThreeCA d) := by
  intro i
  unfold mulThreeCA
  have h1 : d i % 2 < 2 := Nat.mod_lt _ (by decide)
  have h2 : d (i - 1) < 6 := hd (i - 1)
  omega

/-- `mulThreeHalvesCA` preserves the base-6 digit alphabet `{0, ..., 5}`. -/
theorem isBaseSixConfig_mulThreeHalvesCA {d : ℤ → ℕ} (hd : IsBaseSixConfig d) :
    IsBaseSixConfig (mulThreeHalvesCA d) := by
  intro i
  exact isBaseSixConfig_mulThreeCA (isBaseSixConfig_mulThreeCA hd) (i + 1)

/-- Every iterate `mulThreeHalvesCA^[n] d` preserves the base-6 digit alphabet `{0, ..., 5}`. -/
theorem isBaseSixConfig_iterate_mulThreeHalvesCA {d : ℤ → ℕ} (hd : IsBaseSixConfig d) (n : ℕ) :
    IsBaseSixConfig (mulThreeHalvesCA^[n] d) := by
  induction n with
  | zero => exact hd
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact isBaseSixConfig_mulThreeHalvesCA ih

/-- **Explicit Radius-1 Local Rule for `mulThreeHalvesCA` (`mulThreeHalvesCA_eq_local_rule`)**:
`mulThreeHalvesCA d i` depends only on `(d (i - 1), d i, d (i + 1))`. -/
theorem mulThreeHalvesCA_eq_local_rule (d : ℤ → ℕ) (i : ℤ) :
    mulThreeHalvesCA d i =
      3 * ((3 * (d (i + 1) % 2) + d i / 2) % 2) +
        (3 * (d i % 2) + d (i - 1) / 2) / 2 := by
  unfold mulThreeHalvesCA mulThreeCA
  have hidx : i + 1 - 1 = i := by ring
  rw [hidx]

/-- **One-Step Radius-1 Locality (`mulThreeHalvesCA_local_congr`)**:
If `d₁` and `d₂` agree on `{i - 1, i, i + 1}`, then `mulThreeHalvesCA d₁ i = mulThreeHalvesCA d₂ i`. -/
theorem mulThreeHalvesCA_local_congr {d₁ d₂ : ℤ → ℕ} {i : ℤ}
    (hm1 : d₁ (i - 1) = d₂ (i - 1))
    (h0 : d₁ i = d₂ i)
    (hp1 : d₁ (i + 1) = d₂ (i + 1)) :
    mulThreeHalvesCA d₁ i = mulThreeHalvesCA d₂ i := by
  rw [mulThreeHalvesCA_eq_local_rule, mulThreeHalvesCA_eq_local_rule, hm1, h0, hp1]

/-- **`n`-Step Causal-Cone Locality (`mulThreeHalvesCA_iterate_causal_cone_congr`, Section B2)**:
The cell `(mulThreeHalvesCA^[n] d) i` at time `n` and position `i` is uniquely determined by
the initial configuration `d` on the causal interval `[i - n, i + n]`. -/
theorem mulThreeHalvesCA_iterate_causal_cone_congr {d₁ d₂ : ℤ → ℕ} (n : ℕ) :
    ∀ {i : ℤ}, (∀ j : ℤ, i - (n : ℤ) ≤ j → j ≤ i + (n : ℤ) → d₁ j = d₂ j) →
      (mulThreeHalvesCA^[n] d₁) i = (mulThreeHalvesCA^[n] d₂) i := by
  induction n with
  | zero =>
      intro i hcone
      exact hcone i (by omega) (by omega)
  | succ n ih =>
      intro i hcone
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply mulThreeHalvesCA_local_congr
      · exact ih (fun j hj1 hj2 => hcone j (by omega) (by omega))
      · exact ih (fun j hj1 hj2 => hcone j (by omega) (by omega))
      · exact ih (fun j hj1 hj2 => hcone j (by omega) (by omega))

/-! ## 2. Exact Flux Conservation & Rational Value Homomorphism (Section B1) -/

/-- Scaled natural-number value of `d` on the window `[a, a + L)` at base unit `6^a`:
`baseSixScaledNat d a L = ∑ k ∈ Finset.range L, d (a + k) * 6^k`. -/
def baseSixScaledNat (d : ℤ → ℕ) (a : ℤ) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, d (a + (k : ℤ)) * 6 ^ k

@[simp]
theorem baseSixScaledNat_zero (d : ℤ → ℕ) (a : ℤ) :
    baseSixScaledNat d a 0 = 0 := by
  simp [baseSixScaledNat]

theorem baseSixScaledNat_succ (d : ℤ → ℕ) (a : ℤ) (L : ℕ) :
    baseSixScaledNat d a (L + 1) =
      baseSixScaledNat d a L + d (a + (L : ℤ)) * 6 ^ L := by
  unfold baseSixScaledNat
  rw [Finset.sum_range_succ]

/-- **Unconditional Finite-Window Flux Identity for `mulThreeCA` (`baseSixScaledNat_mulThreeCA_flux`)**:
For every configuration `d : ℤ → ℕ`, origin `a : ℤ`, and window length `L : ℕ`:
`baseSixScaledNat (mulThreeCA d) a L + (d (a + L - 1) / 2) * 6^L = 3 * baseSixScaledNat d a L + d (a - 1) / 2`. -/
theorem baseSixScaledNat_mulThreeCA_flux (d : ℤ → ℕ) (a : ℤ) (L : ℕ) :
    baseSixScaledNat (mulThreeCA d) a L + (d (a + (L : ℤ) - 1) / 2) * 6 ^ L =
      3 * baseSixScaledNat d a L + d (a - 1) / 2 := by
  induction L with
  | zero =>
      simp [baseSixScaledNat]
  | succ L ih =>
      rw [baseSixScaledNat_succ, baseSixScaledNat_succ]
      have hm3 : mulThreeCA d (a + (L : ℤ)) = 3 * (d (a + (L : ℤ)) % 2) + d (a + (L : ℤ) - 1) / 2 := rfl
      rw [hm3]
      have hidx : a + ((L + 1 : ℕ) : ℤ) - 1 = a + (L : ℤ) := by push_cast; ring
      rw [hidx]
      have hdivmod : 2 * (d (a + (L : ℤ)) / 2) + d (a + (L : ℤ)) % 2 = d (a + (L : ℤ)) :=
        Nat.div_add_mod (d (a + (L : ℤ))) 2
      have hpow : 6 ^ (L + 1) = 6 * 6 ^ L := by rw [pow_succ']
      have hcell :
          (3 * (d (a + (L : ℤ)) % 2) + d (a + (L : ℤ) - 1) / 2) * 6 ^ L +
              (d (a + (L : ℤ)) / 2) * 6 ^ (L + 1) =
            (d (a + (L : ℤ) - 1) / 2) * 6 ^ L + 3 * (d (a + (L : ℤ)) * 6 ^ L) := by
        rw [hpow]
        calc
          (3 * (d (a + (L : ℤ)) % 2) + d (a + (L : ℤ) - 1) / 2) * 6 ^ L +
              (d (a + (L : ℤ)) / 2) * (6 * 6 ^ L)
            = (d (a + (L : ℤ) - 1) / 2) * 6 ^ L +
                3 * (2 * (d (a + (L : ℤ)) / 2) + d (a + (L : ℤ)) % 2) * 6 ^ L := by ring
          _ = (d (a + (L : ℤ) - 1) / 2) * 6 ^ L + 3 * (d (a + (L : ℤ)) * 6 ^ L) := by
                rw [hdivmod]; ring
      linarith

/-- When `d (a - 1) = 0` and `d (a + L) = 0`, `mulThreeCA` triples `baseSixScaledNat` on `[a, a + L + 1)`. -/
theorem baseSixScaledNat_mulThreeCA_eq {d : ℤ → ℕ} {a : ℤ} {L : ℕ}
    (hleft : d (a - 1) = 0) (hright : d (a + (L : ℤ)) = 0) :
    baseSixScaledNat (mulThreeCA d) a (L + 1) = 3 * baseSixScaledNat d a L := by
  have hflux := baseSixScaledNat_mulThreeCA_flux d a (L + 1)
  have hidx : a + ((L + 1 : ℕ) : ℤ) - 1 = a + (L : ℤ) := by push_cast; ring
  rw [hidx, hright, hleft] at hflux
  have hsucc := baseSixScaledNat_succ d a L
  rw [hright] at hsucc
  simp only [Nat.zero_div, zero_mul, add_zero] at hflux hsucc
  rw [hsucc] at hflux
  exact hflux

/-- Shifting the indexing origin left by `1` multiplies `baseSixScaledNat` by `6` when `d (a - 1) = 0`. -/
theorem baseSixScaledNat_shift_left_one {d : ℤ → ℕ} {a : ℤ} {L : ℕ}
    (hleft : d (a - 1) = 0) :
    baseSixScaledNat d (a - 1) (L + 1) = 6 * baseSixScaledNat d a L := by
  induction L with
  | zero =>
      simp [baseSixScaledNat, hleft]
  | succ L ih =>
      rw [baseSixScaledNat_succ d (a - 1) (L + 1), ih, baseSixScaledNat_succ d a L]
      have hidx : a - 1 + ((L + 1 : ℕ) : ℤ) = a + (L : ℤ) := by push_cast; ring
      rw [hidx, pow_succ']
      ring

/-- Relating `baseSixScaledNat (mulThreeHalvesCA d) (a - 1) M` to `baseSixScaledNat (mulThreeCA (mulThreeCA d)) a M`. -/
theorem baseSixScaledNat_mulThreeHalvesCA_eq_double_mulThreeCA (d : ℤ → ℕ) (a : ℤ) (M : ℕ) :
    baseSixScaledNat (mulThreeHalvesCA d) (a - 1) M =
      baseSixScaledNat (mulThreeCA (mulThreeCA d)) a M := by
  unfold baseSixScaledNat mulThreeHalvesCA
  apply Finset.sum_congr rfl
  intro k _
  have hidx : a - 1 + (k : ℤ) + 1 = a + (k : ℤ) := by ring
  rw [hidx]

/-- **Exact Integer Value Identity for `mulThreeHalvesCA` (`baseSixScaledNat_mulThreeHalvesCA_eq`)**:
If `d` vanishes outside `[a, a + L)` (specifically `d (a - 2) = d (a - 1) = 0` and
`d (a + L) = d (a + L + 1) = 0`), then:
`baseSixScaledNat (mulThreeHalvesCA d) (a - 1) (L + 2) = 9 * baseSixScaledNat d a L`,
and relative to the shifted base unit `6^(a - 1)`:
`2 * baseSixScaledNat (mulThreeHalvesCA d) (a - 1) (L + 2) = 3 * (6 * baseSixScaledNat d a L)`. -/
theorem baseSixScaledNat_mulThreeHalvesCA_eq {d : ℤ → ℕ} {a : ℤ} {L : ℕ}
    (hleft2 : d (a - 2) = 0) (hleft1 : d (a - 1) = 0)
    (hright0 : d (a + (L : ℤ)) = 0) (hright1 : d (a + (L : ℤ) + 1) = 0) :
    baseSixScaledNat (mulThreeHalvesCA d) (a - 1) (L + 2) =
      9 * baseSixScaledNat d a L := by
  rw [baseSixScaledNat_mulThreeHalvesCA_eq_double_mulThreeCA]
  have hm1_left : mulThreeCA d (a - 1) = 0 := by
    unfold mulThreeCA
    have hidx : a - 1 - 1 = a - 2 := by ring
    rw [hidx, hleft1, hleft2]
  have hm1_right : mulThreeCA d (a + ((L + 1 : ℕ) : ℤ)) = 0 := by
    unfold mulThreeCA
    have hidx1 : a + ((L + 1 : ℕ) : ℤ) = a + (L : ℤ) + 1 := by push_cast; ring
    have hidx0 : a + (L : ℤ) + 1 - 1 = a + (L : ℤ) := by ring
    rw [hidx1, hidx0, hright1, hright0]
  have hstep2 := baseSixScaledNat_mulThreeCA_eq hm1_left hm1_right
  have hstep1 := baseSixScaledNat_mulThreeCA_eq hleft1 hright0
  rw [show L + 1 + 1 = L + 2 by omega] at hstep2
  rw [hstep2, hstep1]
  ring

/-- Exact rational value of `d` on the window `[a, a + L)`:
`baseSixWindowVal d a L = (baseSixScaledNat d a L : ℚ) * (6 : ℚ)^a`. -/
def baseSixWindowVal (d : ℤ → ℕ) (a : ℤ) (L : ℕ) : ℚ :=
  (baseSixScaledNat d a L : ℚ) * (6 : ℚ) ^ a

/-- **Exact Rational `(3/2)` Multiplication Identity (`baseSixWindowVal_mulThreeHalvesCA`, Section B1)**:
Whenever `d (a - 2) = d (a - 1) = 0` and `d (a + L) = d (a + L + 1) = 0`,
`baseSixWindowVal (mulThreeHalvesCA d) (a - 1) (L + 2) = (3 / 2 : ℚ) * baseSixWindowVal d a L`. -/
theorem baseSixWindowVal_mulThreeHalvesCA {d : ℤ → ℕ} {a : ℤ} {L : ℕ}
    (hleft2 : d (a - 2) = 0) (hleft1 : d (a - 1) = 0)
    (hright0 : d (a + (L : ℤ)) = 0) (hright1 : d (a + (L : ℤ) + 1) = 0) :
    baseSixWindowVal (mulThreeHalvesCA d) (a - 1) (L + 2) =
      (3 / 2 : ℚ) * baseSixWindowVal d a L := by
  unfold baseSixWindowVal
  rw [baseSixScaledNat_mulThreeHalvesCA_eq hleft2 hleft1 hright0 hright1]
  have hzpow : (6 : ℚ) ^ a = 6 * (6 : ℚ) ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]
    ring
  rw [hzpow]
  push_cast
  ring

/-! ## 3. Canonical Base-6 Fractional-Part & Digit-`(-1)` Trace Equivalence (Section B1) -/

/-- **Canonical Base-6 Fractional-Part & Digit-`(-1)` Trace Equivalence
(`fract_lt_half_iff_digit_neg_one_lt_three`, Section B1)**:
Let `x : ℝ` be decomposed at the base-6 radix point as `x = (I : ℝ) + ((d_neg1 : ℝ) / 6 + r)`
where `I : ℕ` is the nonnegative integer part (`d_0, d_1, ...`), `d_neg1 < 6` is the digit at
position `-1` (`6⁻¹`), and `0 ≤ r < 1/6` is the canonical tail of positions `≤ -2` (excluding
the non-canonical all-`5` tail `r = 1/6`). Then:
1. `0 ≤ (d_neg1 : ℝ) / 6 + r < 1`,
2. `Int.fract x = (d_neg1 : ℝ) / 6 + r`, and
3. `Int.fract x < 1 / 2 ↔ d_neg1 < 3` (`d_neg1 ∈ {0, 1, 2}`). -/
theorem fract_lt_half_iff_digit_neg_one_lt_three (I d_neg1 : ℕ) (r : ℝ)
    (hd : d_neg1 < 6) (hr0 : 0 ≤ r) (hr1 : r < (1 / 6 : ℝ)) :
    let f : ℝ := (d_neg1 : ℝ) / 6 + r
    (0 ≤ f ∧ f < 1) ∧
      Int.fract ((I : ℝ) + f) = f ∧
      (Int.fract ((I : ℝ) + f) < (1 / 2 : ℝ) ↔ d_neg1 < 3) := by
  intro f
  have hd_le5 : (d_neg1 : ℝ) ≤ 5 := by exact_mod_cast (by omega : d_neg1 ≤ 5)
  have hd_nonneg : (0 : ℝ) ≤ (d_neg1 : ℝ) := by positivity
  have hf0 : 0 ≤ f := by unfold f; linarith
  have hf1 : f < 1 := by unfold f; linarith
  have hfract : Int.fract ((I : ℝ) + f) = f := by
    have hshift : (I : ℝ) + f = f + ((I : ℤ) : ℝ) := by push_cast; ring
    rw [hshift, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hf0, hf1⟩]
  refine ⟨⟨hf0, hf1⟩, hfract, ?_⟩
  rw [hfract]
  constructor
  · intro hlt
    by_contra hge3
    have hd_ge3 : (3 : ℝ) ≤ (d_neg1 : ℝ) := by exact_mod_cast (by omega : 3 ≤ d_neg1)
    unfold f at hlt
    linarith
  · intro hlt3
    have hd_le2 : (d_neg1 : ℝ) ≤ 2 := by exact_mod_cast (by omega : d_neg1 ≤ 2)
    unfold f
    linarith

/-- **Non-Canonical All-`5` Tail Endpoint Counterexample
(`noncanonical_tail_endpoint_counterexample`, Section B1)**:
If the non-canonical tail `r = 1/6` (`0.05555..._6 = 1/6`, so `0.25555..._6 = 2/6 + 1/6 = 1/2`)
is not excluded, then `d_neg1 = 2 < 3` (`d_neg1 ∈ {0, 1, 2}`) even though
`Int.fract ((I : ℝ) + ((2 : ℝ) / 6 + 1 / 6)) = 1 / 2 ≮ 1 / 2`. -/
theorem noncanonical_tail_endpoint_counterexample (I : ℕ) :
    (2 : ℕ) < 3 ∧
      Int.fract ((I : ℝ) + ((2 : ℝ) / 6 + (1 / 6 : ℝ))) = (1 / 2 : ℝ) ∧
      ¬ (Int.fract ((I : ℝ) + ((2 : ℝ) / 6 + (1 / 6 : ℝ))) < (1 / 2 : ℝ)) := by
  have hhalf : (2 : ℝ) / 6 + (1 / 6 : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hfract : Int.fract ((I : ℝ) + (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
    have hshift : (I : ℝ) + (1 / 2 : ℝ) = (1 / 2 : ℝ) + ((I : ℤ) : ℝ) := by push_cast; ring
    rw [hshift, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  rw [hhalf, hfract]
  exact ⟨by decide, rfl, by norm_num⟩

/-! ## 4. Integer-Side Left-Boundary Propagation, Finite Causal-Cone Witnesses & 2-Adic Ghost Obstruction -/

/-- If `d i = 0` for all `i ≥ m` (finite integer-side support), then after one step of
`mulThreeHalvesCA`, `mulThreeHalvesCA d i = 0` for all `i ≥ m + 1`. -/
theorem left_zero_boundary_mulThreeHalvesCA {d : ℤ → ℕ} {m : ℤ}
    (hzero : ∀ i : ℤ, m ≤ i → d i = 0) :
    ∀ i : ℤ, m + 1 ≤ i → mulThreeHalvesCA d i = 0 := by
  intro i hi
  rw [mulThreeHalvesCA_eq_local_rule]
  have hm1 : d (i - 1) = 0 := hzero (i - 1) (by omega)
  have h0 : d i = 0 := hzero i (by omega)
  have hp1 : d (i + 1) = 0 := hzero (i + 1) (by omega)
  rw [hm1, h0, hp1]

/-- Across `n` steps of `mulThreeHalvesCA`, the integer-side zero boundary `∀ i ≥ m, d i = 0`
propagates at speed at most `1` cell per step: `(mulThreeHalvesCA^[n] d) i = 0` for all `i ≥ m + n`. -/
theorem left_zero_boundary_mulThreeHalvesCA_iterate {d : ℤ → ℕ} {m : ℤ}
    (hzero : ∀ i : ℤ, m ≤ i → d i = 0) (n : ℕ) :
    ∀ i : ℤ, m + (n : ℤ) ≤ i → (mulThreeHalvesCA^[n] d) i = 0 := by
  induction n with
  | zero =>
      intro i hi
      exact hzero i (by omega)
  | succ n ih =>
      intro i hi
      rw [Function.iterate_succ_apply']
      apply left_zero_boundary_mulThreeHalvesCA ih
      omega

/-- Base-6 configuration of a single natural number `a : ℕ`:
`natToBaseSixConfig a i = (a / 6^i) % 6` for `i ≥ 0` and `0` for `i < 0`. -/
def natToBaseSixConfig (a : ℕ) (i : ℤ) : ℕ :=
  if 0 ≤ i then (a / 6 ^ i.toNat) % 6 else 0

theorem isBaseSixConfig_natToBaseSixConfig (a : ℕ) :
    IsBaseSixConfig (natToBaseSixConfig a) := by
  intro i
  unfold natToBaseSixConfig
  split_ifs
  · exact Nat.mod_lt _ (by decide)
  · decide

/-- **Concrete Space-Time Trace Escapes for `x = 1` and `x = 8` (`seed_one_and_eight_base_six_trace_escape`,
Section B2 & Kopra Figure 1/2 Mechanism)**:
1. Starting from `d = natToBaseSixConfig 1`, at step `0` the fractional digit is `d(-1) = 0 < 3`,
   and at step `1` (`1.5 = 1.3_6`) the column `-1` trace digit hits `3 ≥ 3` (immediate escape).
2. Starting from `d = natToBaseSixConfig 8` (`8 = 12_6`), the column `-1` trace digit stays in
   `{0, 1, 2}` for steps `n = 0, 1, 2, 3, 4` (`[0, 0, 0, 0, 3]` at step 4 since `8 * (3/2)^4 = 81/2 = 40.5 = 104.3_6`!
   And at step 5, `8 * (3/2)^5 = 243/4 = 60.75 = 140.43_6` has digit `4` at position `-1`). -/
theorem seed_one_and_eight_base_six_trace_escape :
    (mulThreeHalvesCA^[0] (natToBaseSixConfig 1)) (-1) = 0 ∧
      (mulThreeHalvesCA^[1] (natToBaseSixConfig 1)) (-1) = 3 ∧
      (mulThreeHalvesCA^[0] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[1] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[2] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[3] (natToBaseSixConfig 8)) (-1) = 0 ∧
      (mulThreeHalvesCA^[4] (natToBaseSixConfig 8)) (-1) = 3 ∧
      (mulThreeHalvesCA^[5] (natToBaseSixConfig 8)) (-1) = 4 := by
  decide

/-- **Phase B3 Negative/Limitative Theorem: Unconstrained `{0, 1, 2}` Traces & 2-Adic Ghost Obstruction
(`zero_and_two_adic_ghost_trace_obstruction`, Section B3 Stop Gate & Section 21 Type 2/3)**:
1. **Zero Configuration Witness**: The all-zero base-6 configuration `fun _ => 0` is a fixed point of
   `mulThreeHalvesCA` whose column `-1` trace is `0 ∈ {0, 1, 2}` forever, proving that non-emptiness
   of `{i ≥ 0 | d i ≠ 0}` (positivity) is essential.
2. **Perpetual Local/Archimedean Feasibility Without Left-Finiteness (`periodicThreeParity`)**:
   The period-3 parity stream `periodicThreeParity` (`100100...`) satisfies `signedMargin periodicThreeParity (3 * m) = 2^(3 * m) > 0`
   at every horizon `3 * m` (so every finite-horizon local trace/companion constraint is satisfiable),
   yet its canonical integer seed residues `seedResidue periodicThreeParity N` never stabilize at any
   finite nonnegative integer (`∀ a_0 : ℕ, ¬ ∀ N, ...`), forcing infinitely many nonzero binary/base-6
   integer-side extensions. Thus no proof that discards the left-finite boundary condition
   (`∃ m, ∀ i ≥ m, d i = 0`) can establish the non-existence of Z-numbers. -/
theorem zero_and_two_adic_ghost_trace_obstruction :
    (∀ n : ℕ, (mulThreeHalvesCA^[n] (fun _ : ℤ => 0)) (-1) = 0) ∧
      (∀ m : ℕ, signedMargin periodicThreeParity (3 * m) = (2 : ℤ) ^ (3 * m) ∧
        0 < signedMargin periodicThreeParity (3 * m)) ∧
      (∀ a_0 : ℕ, ¬ ∃ N_0 : ℕ, ∀ N ≥ N_0, seedResidue periodicThreeParity N = a_0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hzero : mulThreeHalvesCA (fun _ : ℤ => 0) = (fun _ : ℤ => 0) := by
          funext i
          simp [mulThreeHalvesCA, mulThreeCA]
        rw [Function.iterate_succ_apply, hzero, ih]
  · intro m
    induction m with
    | zero => simp [signedMargin]
    | succ m ih =>
        have hcap : signedMargin periodicThreeParity (3 * m) = (2 : ℤ) ^ (3 * m) := ih.1
        have h0 : periodicThreeParity (3 * m) % 2 = 1 := by
          unfold periodicThreeParity
          have hmod : (3 * m) % 3 = 0 := Nat.mul_mod_right 3 m
          simp [hmod]
        have h1 : periodicThreeParity (3 * m + 1) % 2 = 0 := by
          unfold periodicThreeParity
          have hmod : (3 * m + 1) % 3 = 1 := by omega
          simp [hmod]
        have h2 : periodicThreeParity (3 * m + 2) % 2 = 0 := by
          unfold periodicThreeParity
          have hmod : (3 * m + 2) % 3 = 2 := by omega
          simp [hmod]
        have hrec := (signedMargin_100_ceiling_recovery hcap h0 h1 h2).2.2
        have hidx : 3 * (m + 1) = 3 * m + 3 := by ring
        rw [hidx, hrec]
        exact ⟨rfl, by positivity⟩
  · intro a_0 hstab
    exact constant_three_seedResidue_never_stabilizes a_0
      ((exists_nonneg_seed_iff_seedResidue_stabilizes periodicThreeParity a_0).mpr hstab)

end Mahler.BaseSixAutomaton
