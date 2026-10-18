import MultiOriginSubspaceSyzygy

/-!
# The Repeated-Subword Divisibility Barrier, Strict Aperiodicity & Subword Complexity Bounds

This module formalizes Path 1: the combinatorial and Diophantine rigidity of
repeated subwords `(s (r1 + 0), ..., s (r1 + L - 1)) = (s (r2 + 0), ..., s (r2 + L - 1))`
at two origins `r1 < r2` along any `ValidBlockChain a_0 s u K`:

1. **Finite-Window Congruence Laws (`blockSteps_congr`, `tailSteps_congr`,
   `coprimeRemainder_congr`, `integerSlack_congr`)**:
   - `blockSteps s d` and `coprimeRemainder s d` depend only on `s i` for `i < d`.
   - `tailSteps s d` depends only on `s i` for `i ≤ d`.
2. **Strict Monotonicity & Aperiodicity of Quotients (`validBlockChain_a0_pos`,
   `orbit_blockSteps_strict_mono`, `u_lt_of_lt_of_eq_block`)**:
   - Every non-empty `ValidBlockChain a_0 s u K` (`0 < K`) automatically satisfies
     `0 < a_0`.
   - For `r1 < r2 ≤ K`, `orbit a_0 (blockSteps s r1) < orbit a_0 (blockSteps s r2)`.
   - Whenever `r1 < r2 < K` and `s r1 = s r2`, canceling `2^(s r1)` from
     `2^(s r1) * u r1 = 3 * b_{r1} + 1 < 3 * b_{r2} + 1 = 2^(s r2) * u r2` proves
     strict quotient growth `u r1 < u r2` (ruling out any periodic repetition).
3. **Exact Remainder Cancellation & Simultaneous 2-adic / 3-adic Divisibility
   (`repeated_subword_quotient_diff_eq`, `repeated_subword_simultaneous_divisibility`)**:
   - Whenever `r1 < r2`, `r2 + d < K`, and `∀ i ≤ d, s (r1 + i) = s (r2 + i)`,
     subtracting the `d`-step quotient identities at `r1` and `r2` cancels
     `coprimeRemainder (shiftSeq s r1) d` identically:
     `2^(tailSteps (shiftSeq s r1) d) * (u (r2 + d) - u (r1 + d)) =
       3^(blockSteps (shiftSeq s r1) d) * (u r2 - u r1)`.
   - By coprimality of `2` and `3`, this forces simultaneous 2-adic and 3-adic
     divisibility of the positive differences `u r2 - u r1` and
     `u (r2 + d) - u (r1 + d)`:
     `2^(tailSteps (shiftSeq s r1) d) ∣ (u r2 - u r1)` and
     `3^(blockSteps (shiftSeq s r1) d) ∣ (u (r2 + d) - u (r1 + d))`.
4. **Exponential Barrier & Explicit Linear Subword-Complexity Cutoffs
   (`repeated_subword_exponential_barrier`, `repeated_subword_linear_step_cutoff`,
   `repeated_subword_block_count_bound`)**:
   - For any `1 ≤ L`-block subword match `∀ i < L, s (r1 + i) = s (r2 + i)` at
     `r1 < r2` with `r2 + (L - 1) < K` and `0 < integerSlack s r2`:
     `2^(blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1) <
       2^(blockSteps s (r2 + 1) + 1) * u r2 < 3^(blockSteps s r2 + 1) * (2 * a_0 + 1)`.
   - When `a_0 < 2^W`, this yields the logarithm-free linear step cutoff
     `blockSteps (shiftSeq s r1) L < blockSteps s r2 + W + 2`,
     and when `0 < minSlack s (K - 1)` it bounds the repeated block count by
     `3 * L ≤ blockSteps s r2 + W + 2`.
-/

namespace Mahler.SubwordComplexity

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.SplitPinch
open Mahler.ProductGraph
open Mahler.BridgeOne
open Mahler.BridgeTwo
open Mahler.BridgeThree
open Mahler.FormulationB
open Mahler.JumpValuation
open Mahler.EscapeBranchCap
open Mahler.PhaseLock
open Mahler.MasterReduction
open Mahler.ModEightClassifier
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.KernelDuality
open Mahler.Coasting
open Mahler.TwoSidedSqueeze
open Mahler.SharpenedSqueezes
open Mahler.AperiodicCocycle
open Mahler.MinSlackSystem
open Mahler.GlobalStepRate
open Mahler.BaseTwoLock
open Mahler.CeilingSynthesis
open Mahler.TelescopingDuality
open Mahler.ConverseReconstruction
open Mahler.ExplicitCutoffs
open Mahler.DeficitAmplification
open Mahler.TwoVisitSeparation
open Mahler.MonotonicSeparation
open Mahler.CeilingModTraps
open Mahler.TwoAdicLTE
open Mahler.FullStepValuation
open Mahler.RemainderAdditionLaw
open Mahler.TwoAdicCauchy
open Mahler.AllHistoryRecovery
open Mahler.ParametricCorridor
open Mahler.AperiodicBoundedSqueeze
open Mahler.TimeIndependentSqueeze
open Mahler.SlackDeadEnds
open Mahler.GrandSynthesis
open Mahler.Mod256Sieve
open Mahler.UnitRigidity
open Mahler.DeterminantCollapse
open Mahler.BakerMatveev
open Mahler.RidoutSubspace
open Mahler.MultiOriginSyzygy

/-! ## 1. Finite-Window Congruence Laws for `blockSteps`, `tailSteps`, and `coprimeRemainder` -/

/-- `blockSteps s d` depends only on `s i` for `i < d`. -/
theorem blockSteps_congr {s1 s2 : ℕ → ℕ} {d : ℕ}
    (h : ∀ i < d, s1 i = s2 i) :
    blockSteps s1 d = blockSteps s2 d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [blockSteps]
      rw [ih (fun i hi => h i (by omega)), h d (by omega)]

/-- `tailSteps s d` depends only on `s i` for `i ≤ d` (specifically `1 ≤ i ≤ d`). -/
theorem tailSteps_congr {s1 s2 : ℕ → ℕ} {d : ℕ}
    (h : ∀ i ≤ d, s1 i = s2 i) :
    tailSteps s1 d = tailSteps s2 d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [tailSteps]
      rw [ih (fun i hi => h i (by omega)), h (d + 1) (by omega)]

/-- `coprimeRemainder s d` depends only on `s i` for `i < d`. -/
theorem coprimeRemainder_congr {s1 s2 : ℕ → ℕ} {d : ℕ}
    (h : ∀ i < d, s1 i = s2 i) :
    coprimeRemainder s1 d = coprimeRemainder s2 d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [coprimeRemainder]
      rw [ih (fun i hi => h i (by omega)), h d (by omega),
        tailSteps_congr (fun i hi => h i (by omega))]

/-- `integerSlack s d` (`1 ≤ d`) depends only on `s i` for `i < d`. -/
theorem integerSlack_congr {s1 s2 : ℕ → ℕ} {d : ℕ}
    (hd : 1 ≤ d) (h : ∀ i < d, s1 i = s2 i) :
    integerSlack s1 d = integerSlack s2 d := by
  unfold integerSlack
  rw [blockSteps_congr h, coprimeRemainder_congr h, h 0 (by omega)]

/-! ## 2. Strict Monotonicity of Orbit & Quotients at Equal Block Lengths -/

/-- Every non-empty `ValidBlockChain a_0 s u K` (`0 < K`) automatically satisfies `0 < a_0`. -/
theorem validBlockChain_a0_pos {a_0 : ℕ} {s u : ℕ → ℕ} {K : ℕ}
    (hK : 0 < K) (hchain : ValidBlockChain a_0 s u K) :
    0 < a_0 := by
  rcases hchain 0 hK with ⟨hs0, hu0_odd, horb0⟩
  have h2_ge : 2 ≤ 2 ^ (s 0) := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hs0
    simpa using hpow
  have hu0_pos : 1 ≤ u 0 := by omega
  have hprod_ge : 2 ≤ 2 ^ (s 0) * u 0 := by nlinarith
  have horb_zero : orbit a_0 (blockSteps s 0) = a_0 := rfl
  rw [horb_zero] at horb0
  omega

/-- For `r1 < r2 ≤ K` along a `ValidBlockChain a_0 s u K`,
`blockSteps s r1 < blockSteps s r2` and
`orbit a_0 (blockSteps s r1) < orbit a_0 (blockSteps s r2)`. -/
theorem orbit_blockSteps_strict_mono {a_0 : ℕ} {s u : ℕ → ℕ} {K r1 r2 : ℕ}
    (hr12 : r1 < r2) (hr2K : r2 ≤ K) (hchain : ValidBlockChain a_0 s u K) :
    blockSteps s r1 < blockSteps s r2 ∧
      orbit a_0 (blockSteps s r1) < orbit a_0 (blockSteps s r2) := by
  have ha0 : 0 < a_0 := validBlockChain_a0_pos (by omega) hchain
  have hsr1 : 1 ≤ s r1 := (hchain r1 (by omega)).1
  have hstep1 : blockSteps s (r1 + 1) = blockSteps s r1 + s r1 := rfl
  have hmono : blockSteps s (r1 + 1) ≤ blockSteps s r2 :=
    Mahler.BridgeThree.blockSteps_mono s (by omega)
  have hT_lt : blockSteps s r1 < blockSteps s r2 := by omega
  exact ⟨hT_lt, orbit_lt_of_lt ha0 hT_lt⟩

/-- **Strict Quotient Growth at Equal Block Lengths (`u_lt_of_lt_of_eq_block`)**:
Whenever `r1 < r2 < K` along `ValidBlockChain a_0 s u K` and `s r1 = s r2`,
we have `u r1 < u r2`. In particular, `u r1 ≠ u r2` (strict aperiodicity). -/
theorem u_lt_of_lt_of_eq_block {a_0 : ℕ} {s u : ℕ → ℕ} {K r1 r2 : ℕ}
    (hr12 : r1 < r2) (hr2K : r2 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs_eq : s r1 = s r2) :
    u r1 < u r2 := by
  have horb_lt := (orbit_blockSteps_strict_mono hr12 (by omega) hchain).2
  have hb1 := (hchain r1 (by omega)).2.2
  have hb2 := (hchain r2 hr2K).2.2
  rw [← hs_eq] at hb2
  have hmul_lt : 2 ^ (s r1) * u r1 < 2 ^ (s r1) * u r2 := by omega
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

/-! ## 3. Exact Remainder Cancellation & Simultaneous 2-adic / 3-adic Divisibility -/

/-- **Repeated-Subword Remainder Cancellation Identity (`repeated_subword_quotient_diff_eq`)**:
If `r1 < r2`, `r2 + d < K`, `ValidBlockChain a_0 s u K`, and the `(d + 1)`-block
subwords match (`∀ i ≤ d, s (r1 + i) = s (r2 + i)`), then:
1. `u r1 < u r2` and `u (r1 + d) < u (r2 + d)`, and
2. `2^(tailSteps (shiftSeq s r1) d) * (u (r2 + d) - u (r1 + d)) =
     3^(blockSteps (shiftSeq s r1) d) * (u r2 - u r1)`. -/
theorem repeated_subword_quotient_diff_eq
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r1 r2 d : ℕ}
    (hr12 : r1 < r2) (hr2d : r2 + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hmatch : ∀ i ≤ d, s (r1 + i) = s (r2 + i)) :
    u r1 < u r2 ∧
      u (r1 + d) < u (r2 + d) ∧
      2 ^ (tailSteps (shiftSeq s r1) d) * (u (r2 + d) - u (r1 + d)) =
        3 ^ (blockSteps (shiftSeq s r1) d) * (u r2 - u r1) := by
  have hu_start : u r1 < u r2 :=
    u_lt_of_lt_of_eq_block hr12 (by omega) hchain (by simpa using hmatch 0 (by omega))
  have hu_end : u (r1 + d) < u (r2 + d) :=
    u_lt_of_lt_of_eq_block (by omega) hr2d hchain (hmatch d le_rfl)
  have hid1 := shifted_coprime_quotient_m_step_identity (by omega : r1 + d < K) hchain
  have hid2 := shifted_coprime_quotient_m_step_identity hr2d hchain
  have hshift_le : ∀ i ≤ d, shiftSeq s r1 i = shiftSeq s r2 i := by
    intro i hi
    simpa [shiftSeq] using hmatch i hi
  have hshift_lt : ∀ i < d, shiftSeq s r1 i = shiftSeq s r2 i :=
    fun i hi => hshift_le i (by omega)
  rw [← tailSteps_congr hshift_le, ← blockSteps_congr hshift_lt,
    ← coprimeRemainder_congr hshift_lt] at hid2
  have hdiff :
      2 ^ (tailSteps (shiftSeq s r1) d) * (u (r2 + d) - u (r1 + d)) =
        3 ^ (blockSteps (shiftSeq s r1) d) * (u r2 - u r1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  exact ⟨hu_start, hu_end, hdiff⟩

/-- **Simultaneous 2-adic and 3-adic Divisibility Across a Repeated Subword
(`repeated_subword_simultaneous_divisibility`)**:
Under the hypotheses of `repeated_subword_quotient_diff_eq`,
`2^(tailSteps (shiftSeq s r1) d) ∣ (u r2 - u r1)`,
`3^(blockSteps (shiftSeq s r1) d) ∣ (u (r2 + d) - u (r1 + d))`, and
`2^(tailSteps (shiftSeq s r1) d) ≤ u r2 - u r1`. -/
theorem repeated_subword_simultaneous_divisibility
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r1 r2 d : ℕ}
    (hr12 : r1 < r2) (hr2d : r2 + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hmatch : ∀ i ≤ d, s (r1 + i) = s (r2 + i)) :
    2 ^ (tailSteps (shiftSeq s r1) d) ∣ (u r2 - u r1) ∧
      3 ^ (blockSteps (shiftSeq s r1) d) ∣ (u (r2 + d) - u (r1 + d)) ∧
      2 ^ (tailSteps (shiftSeq s r1) d) ≤ u r2 - u r1 := by
  rcases repeated_subword_quotient_diff_eq hr12 hr2d hchain hmatch with
    ⟨hu_start, _, hdiff⟩
  have hcop23 :
      Nat.Coprime (2 ^ (tailSteps (shiftSeq s r1) d))
        (3 ^ (blockSteps (shiftSeq s r1) d)) :=
    Nat.Coprime.pow _ _ (by decide)
  have hdvd2_mul :
      2 ^ (tailSteps (shiftSeq s r1) d) ∣
        3 ^ (blockSteps (shiftSeq s r1) d) * (u r2 - u r1) :=
    ⟨u (r2 + d) - u (r1 + d), hdiff.symm⟩
  have hdvd2 : 2 ^ (tailSteps (shiftSeq s r1) d) ∣ (u r2 - u r1) :=
    hcop23.dvd_of_dvd_mul_left hdvd2_mul
  have hdvd3_mul :
      3 ^ (blockSteps (shiftSeq s r1) d) ∣
        2 ^ (tailSteps (shiftSeq s r1) d) * (u (r2 + d) - u (r1 + d)) :=
    ⟨u r2 - u r1, hdiff⟩
  have hdvd3 : 3 ^ (blockSteps (shiftSeq s r1) d) ∣ (u (r2 + d) - u (r1 + d)) :=
    hcop23.symm.dvd_of_dvd_mul_left hdvd3_mul
  have hle : 2 ^ (tailSteps (shiftSeq s r1) d) ≤ u r2 - u r1 :=
    Nat.le_of_dvd (by omega) hdvd2
  exact ⟨hdvd2, hdvd3, hle⟩

/-! ## 4. Exponential Barrier & Explicit Linear Subword-Complexity Cutoffs -/

/-- **Repeated-Subword Exponential Barrier (`repeated_subword_exponential_barrier`)**:
For any `1 ≤ L`-block subword match `∀ i < L, s (r1 + i) = s (r2 + i)` at
`r1 < r2` with `r2 + (L - 1) < K` and `0 < integerSlack s r2`:
`2^(blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1) <
  2^(blockSteps s (r2 + 1) + 1) * u r2`
and
`2^(blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1) <
  3^(blockSteps s r2 + 1) * (2 * a_0 + 1)`. -/
theorem repeated_subword_exponential_barrier
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    2 ^ (blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1) <
        2 ^ (blockSteps s (r2 + 1) + 1) * u r2 ∧
      2 ^ (blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1) <
        3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) := by
  have hmatch_le : ∀ i ≤ L - 1, s (r1 + i) = s (r2 + i) :=
    fun i hi => hmatch i (by omega)
  have hu_lt : u r1 < u r2 :=
    (repeated_subword_quotient_diff_eq hr12 hr2L hchain hmatch_le).1
  have hdiv :=
    (repeated_subword_simultaneous_divisibility hr12 hr2L hchain hmatch_le).2.2
  have hu1_pos : 1 ≤ u r1 := by
    have hodd := (hchain r1 (by omega)).2.1
    omega
  have hlt_ur2 : 2 ^ (tailSteps (shiftSeq s r1) (L - 1)) < u r2 := by omega
  have hpow_pos : 0 < 2 ^ (blockSteps s (r2 + 1) + 1) := Nat.pow_pos (by decide)
  have hmul_lt := Nat.mul_lt_mul_of_pos_left hlt_ur2 hpow_pos
  have hs0_eq : s r1 = s r2 := by simpa using hmatch 0 hL
  have htail_add := add_tailSteps_eq_blockSteps_succ (shiftSeq s r1) (L - 1)
  have hL_eq : L - 1 + 1 = L := by omega
  rw [hL_eq] at htail_add
  have hexp_eq :
      (blockSteps s (r2 + 1) + 1) + tailSteps (shiftSeq s r1) (L - 1) =
        blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1 := by
    have hstep_r2 : blockSteps s (r2 + 1) = blockSteps s r2 + s r2 := rfl
    have hshift0 : shiftSeq s r1 0 = s r1 := rfl
    rw [hshift0] at htail_add
    omega
  rw [← Nat.pow_add, hexp_eq] at hmul_lt
  have horbit := integerSlack_eq_orbit_slack (by omega : r2 < K) hchain
  have horbit' :
      integerSlack s r2 =
        ((3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (r2 + 1) + 1) * u r2 : ℕ) : ℤ) := by
    rw [horbit]
    push_cast
    rfl
  have hur2_lt :
      2 ^ (blockSteps s (r2 + 1) + 1) * u r2 <
        3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) := by
    omega
  exact ⟨hmul_lt, lt_trans hmul_lt hur2_lt⟩

/-- **Logarithm-Free Linear Step Cutoff on Repeated Subwords
(`repeated_subword_linear_step_cutoff`)**:
Under the hypotheses of `repeated_subword_exponential_barrier`, if `a_0 < 2^W`,
then the step sum `blockSteps (shiftSeq s r1) L` of the repeated `L`-block subword
satisfies the explicit linear bound:
`blockSteps (shiftSeq s r1) L < blockSteps s r2 + W + 2`. -/
theorem repeated_subword_linear_step_cutoff
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    blockSteps (shiftSeq s r1) L < blockSteps s r2 + W + 2 := by
  have hbar :=
    (repeated_subword_exponential_barrier hL hr12 hr2L hchain hslack hmatch).2
  have h3_lt :
      3 ^ (blockSteps s r2 + 1) < 2 ^ (2 * (blockSteps s r2 + 1)) :=
    three_pow_lt_two_pow_two_mul (by omega)
  have ha0_lt : 2 * a_0 + 1 < 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hrhs_lt :
      3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) <
        2 ^ (2 * (blockSteps s r2 + 1) + (W + 1)) := by
    rw [Nat.pow_add 2 (2 * (blockSteps s r2 + 1)) (W + 1)]
    exact Nat.mul_lt_mul'' h3_lt ha0_lt
  have hpow_lt := lt_trans hbar hrhs_lt
  by_contra hge
  have hexp_ge :
      2 * (blockSteps s r2 + 1) + (W + 1) ≤
        blockSteps s r2 + blockSteps (shiftSeq s r1) L + 1 := by
    omega
  have hpow_ge := Nat.pow_le_pow_right (by decide : 0 < 2) hexp_ge
  exact absurd hpow_lt (not_lt_of_ge hpow_ge)

/-- **Explicit Block-Count Cutoff on Repeated Subwords
(`repeated_subword_block_count_bound`)**:
If in addition the `L`-block window at `r1` satisfies the surviving step-rate
conditions `∀ k < L, 2 ≤ s (r1 + k)` and `∀ k < L, s (r1 + k) = 2 → 6 ≤ s (r1 + k + 1)`
(which yields `3 * L ≤ blockSteps (shiftSeq s r1) L + 1` by
`three_mul_le_blockSteps_add_one`), then the number of blocks `L` in the repeated
subword satisfies:
`3 * L ≤ blockSteps s r2 + W + 2`. -/
theorem repeated_subword_block_count_bound
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hge2 : ∀ k < L, 2 ≤ s (r1 + k))
    (h2to6 : ∀ k < L, s (r1 + k) = 2 → 6 ≤ s (r1 + k + 1))
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    3 * L ≤ blockSteps s r2 + W + 2 := by
  have hlin :=
    repeated_subword_linear_step_cutoff hL hr12 hr2L ha0 hchain hslack hmatch
  have hrate :=
    (three_mul_le_blockSteps_add_one (shiftSeq s r1) L
      (fun k hk => by simpa [shiftSeq] using hge2 k hk)
      (fun k hk hsk => by
        have h := h2to6 k hk (by simpa [shiftSeq] using hsk)
        simpa [shiftSeq, Nat.add_assoc] using h)).1
  omega

/-! ## 5. Parity-Enhanced Common Even Multiplier & Sharpened `T(r2) + W` Cutoff -/

/-- **Parity-Enhanced Common Even Multiplier Law (`repeated_subword_common_even_multiplier`)**:
Because `u (r1 + d)` and `u (r2 + d)` are both odd (`% 2 = 1`) with
`u (r1 + d) < u (r2 + d)`, their difference `u (r2 + d) - u (r1 + d)` is a positive
even integer. Combining this with `repeated_subword_quotient_diff_eq` proves that
there exists a positive integer `K0 ≥ 1` such that simultaneously:
1. `u r2 - u r1 = 2^(tailSteps (shiftSeq s r1) d + 1) * K0`, and
2. `u (r2 + d) - u (r1 + d) = 2 * 3^(blockSteps (shiftSeq s r1) d) * K0`. -/
theorem repeated_subword_common_even_multiplier
    {a_0 : ℕ} {s u : ℕ → ℕ} {K r1 r2 d : ℕ}
    (hr12 : r1 < r2) (hr2d : r2 + d < K)
    (hchain : ValidBlockChain a_0 s u K)
    (hmatch : ∀ i ≤ d, s (r1 + i) = s (r2 + i)) :
    ∃ K0 : ℕ,
      1 ≤ K0 ∧
        u r2 - u r1 = 2 ^ (tailSteps (shiftSeq s r1) d + 1) * K0 ∧
        u (r2 + d) - u (r1 + d) =
          2 * 3 ^ (blockSteps (shiftSeq s r1) d) * K0 := by
  rcases repeated_subword_quotient_diff_eq hr12 hr2d hchain hmatch with
    ⟨hu_start, hu_end, hdiff⟩
  rcases repeated_subword_simultaneous_divisibility hr12 hr2d hchain hmatch with
    ⟨_, ⟨M, hM_eq⟩, _⟩
  have hodd1 : u (r1 + d) % 2 = 1 := (hchain (r1 + d) (by omega)).2.1
  have hodd2 : u (r2 + d) % 2 = 1 := (hchain (r2 + d) hr2d).2.1
  have heven_diff : (u (r2 + d) - u (r1 + d)) % 2 = 0 := by omega
  have h3_odd : 3 ^ (blockSteps (shiftSeq s r1) d) % 2 = 1 := by
    induction (blockSteps (shiftSeq s r1) d) with
    | zero => rfl
    | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hM_even : M % 2 = 0 := by
    have hmod : (3 ^ (blockSteps (shiftSeq s r1) d) * M) % 2 = 0 := by
      rw [← hM_eq, heven_diff]
    rw [Nat.mul_mod, h3_odd] at hmod
    omega
  have hM_pos : 1 ≤ M := by
    by_contra h0
    have hM0 : M = 0 := by omega
    rw [hM0, mul_zero] at hM_eq
    omega
  obtain ⟨K0, rfl⟩ : ∃ K0, M = 2 * K0 := ⟨M / 2, by omega⟩
  refine ⟨K0, by omega, ?_, ?_⟩
  · rw [hM_eq] at hdiff
    have h3_pos : 0 < 3 ^ (blockSteps (shiftSeq s r1) d) := Nat.pow_pos (by decide)
    have hmul_eq :
        3 ^ (blockSteps (shiftSeq s r1) d) * (u r2 - u r1) =
          3 ^ (blockSteps (shiftSeq s r1) d) *
            (2 ^ (tailSteps (shiftSeq s r1) d + 1) * K0) := by
      calc
        3 ^ (blockSteps (shiftSeq s r1) d) * (u r2 - u r1) =
            2 ^ (tailSteps (shiftSeq s r1) d) *
              (3 ^ (blockSteps (shiftSeq s r1) d) * (2 * K0)) := hdiff.symm
        _ = 3 ^ (blockSteps (shiftSeq s r1) d) *
              (2 ^ (tailSteps (shiftSeq s r1) d + 1) * K0) := by
          rw [Nat.pow_succ]
          ring
    exact Nat.eq_of_mul_eq_mul_left h3_pos hmul_eq
  · rw [hM_eq]
    ring

/-- **Sharpened Repeated-Subword Step Cutoff (`sharpened_repeated_subword_linear_cutoff`)**:
Using the extra factor of `2` from `repeated_subword_common_even_multiplier`, any
`1 ≤ L`-block subword repeating at `r1 < r2` (`r2 + (L - 1) < K`) along a
`ValidBlockChain a_0 s u K` with `a_0 < 2^W` and `0 < integerSlack s r2` satisfies:
`2^(blockSteps s r2 + blockSteps (shiftSeq s r1) L + 2) <
  3^(blockSteps s r2 + 1) * (2 * a_0 + 1)`
and
`blockSteps (shiftSeq s r1) L ≤ blockSteps s r2 + W`. -/
theorem sharpened_repeated_subword_linear_cutoff
    {a_0 W : ℕ} {s u : ℕ → ℕ} {K r1 r2 L : ℕ}
    (hL : 1 ≤ L) (hr12 : r1 < r2) (hr2L : r2 + (L - 1) < K)
    (ha0 : a_0 < 2 ^ W)
    (hchain : ValidBlockChain a_0 s u K)
    (hslack : 0 < integerSlack s r2)
    (hmatch : ∀ i < L, s (r1 + i) = s (r2 + i)) :
    2 ^ (blockSteps s r2 + blockSteps (shiftSeq s r1) L + 2) <
        3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) ∧
      blockSteps (shiftSeq s r1) L ≤ blockSteps s r2 + W := by
  have hmatch_le : ∀ i ≤ L - 1, s (r1 + i) = s (r2 + i) :=
    fun i hi => hmatch i (by omega)
  have hu_lt : u r1 < u r2 :=
    (repeated_subword_quotient_diff_eq hr12 hr2L hchain hmatch_le).1
  rcases repeated_subword_common_even_multiplier hr12 hr2L hchain hmatch_le with
    ⟨K0, hK0_pos, hdiff_u, _⟩
  have hu1_pos : 1 ≤ u r1 := by
    have hodd := (hchain r1 (by omega)).2.1
    omega
  have hge_pow :
      2 ^ (tailSteps (shiftSeq s r1) (L - 1) + 1) ≤ u r2 - u r1 := by
    rw [hdiff_u]
    exact Nat.le_mul_of_pos_right _ hK0_pos
  have hlt_ur2 : 2 ^ (tailSteps (shiftSeq s r1) (L - 1) + 1) < u r2 := by omega
  have hpow_pos : 0 < 2 ^ (blockSteps s (r2 + 1) + 1) := Nat.pow_pos (by decide)
  have hmul_lt := Nat.mul_lt_mul_of_pos_left hlt_ur2 hpow_pos
  have hs0_eq : s r1 = s r2 := by simpa using hmatch 0 hL
  have htail_add := add_tailSteps_eq_blockSteps_succ (shiftSeq s r1) (L - 1)
  have hL_eq : L - 1 + 1 = L := by omega
  rw [hL_eq] at htail_add
  have hexp_eq :
      (blockSteps s (r2 + 1) + 1) + (tailSteps (shiftSeq s r1) (L - 1) + 1) =
        blockSteps s r2 + blockSteps (shiftSeq s r1) L + 2 := by
    have hstep_r2 : blockSteps s (r2 + 1) = blockSteps s r2 + s r2 := rfl
    have hshift0 : shiftSeq s r1 0 = s r1 := rfl
    rw [hshift0] at htail_add
    omega
  rw [← Nat.pow_add, hexp_eq] at hmul_lt
  have horbit := integerSlack_eq_orbit_slack (by omega : r2 < K) hchain
  have horbit' :
      integerSlack s r2 =
        ((3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (r2 + 1) + 1) * u r2 : ℕ) : ℤ) := by
    rw [horbit]
    push_cast
    rfl
  have hur2_lt :
      2 ^ (blockSteps s (r2 + 1) + 1) * u r2 <
        3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) := by
    omega
  have hbar := lt_trans hmul_lt hur2_lt
  refine ⟨hbar, ?_⟩
  have h3_lt :
      3 ^ (blockSteps s r2 + 1) < 2 ^ (2 * (blockSteps s r2 + 1)) :=
    three_pow_lt_two_pow_two_mul (by omega)
  have ha0_lt : 2 * a_0 + 1 < 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hrhs_lt :
      3 ^ (blockSteps s r2 + 1) * (2 * a_0 + 1) <
        2 ^ (2 * (blockSteps s r2 + 1) + (W + 1)) := by
    rw [Nat.pow_add 2 (2 * (blockSteps s r2 + 1)) (W + 1)]
    exact Nat.mul_lt_mul'' h3_lt ha0_lt
  have hpow_lt := lt_trans hbar hrhs_lt
  by_contra hgt
  have hexp_ge :
      2 * (blockSteps s r2 + 1) + (W + 1) ≤
        blockSteps s r2 + blockSteps (shiftSeq s r1) L + 2 := by
    omega
  have hpow_ge := Nat.pow_le_pow_right (by decide : 0 < 2) hexp_ge
  exact absurd hpow_lt (not_lt_of_ge hpow_ge)

end Mahler.SubwordComplexity
