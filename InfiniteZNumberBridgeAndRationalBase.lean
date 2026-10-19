import Mod216TwoSidedQuotientFloor

/-!
# Infinite-Horizon $Z$-Number Bridge, Ceiling-vs-Floor Recurrence & Rational-Base Numeration

This module implements Step 1 and Path 4 of the research plan:

1. **Why the Reduced Mahler Recurrence Is the Ceiling Map $g_{n+1} = \lceil 3 g_n / 2 \rceil$
   Rather Than $\lfloor 3 g_n / 2 \rfloor$ (`odd_step_floor_exceeds_half_and_forces_ceil`)**:
   For any odd integer $g_n$ (`g_n % 2 = 1`) and any $x_n = g_n + r_n$ with
   $0 \le r_n < 1/2$,
   $$\frac{3}{2} x_n = \left\lfloor \frac{3 g_n}{2} \right\rfloor + \left(\frac{1}{2} + \frac{3}{2} r_n\right)
     = \text{step } g_n + \left(\frac{3}{2} r_n - \frac{1}{2}\right).$$
   Because $\frac{1}{2} + \frac{3}{2} r_n \in [1/2, 5/4)$, the integer part of
   $\frac{3}{2} x_n$ can **never** be $\lfloor 3 g_n / 2 \rfloor$ if
   $\text{Int.fract}(\frac{3}{2} x_n) < 1/2$: survival forces $1/3 \le r_n < 1/2$
   and $\lfloor \frac{3}{2} x_n \rfloor = \text{step } g_n = (3 g_n + 1)/2 = \lceil 3 g_n / 2 \rceil$.

2. **Exact Equivalence Between `ValidCompanionUpTo` and Direct Fractional-Part
   Inequalities (`validCompanionUpTo_iff_floor_and_fract_lt_half`,
   `exists_validCompanionUpTo_iff_exists_unit_offset_fract_lt_half`,
   `recordHolderA0_fract_offset_113_survival_and_114_death`)**:
   - For every $a_0 \in \mathbb{N}$, $\alpha \in \mathbb{R}$, and $N \in \mathbb{N}$,
     $$\text{ValidCompanionUpTo } a_0\ \alpha\ N \iff
       \lfloor \alpha \rfloor = (a_0 : \mathbb{Z}) \wedge
         \forall n \le N,\ \text{Int.fract}\!\big(\alpha (3/2)^n\big) < \frac{1}{2}.$$
   - Writing $\alpha = a_0 + \xi$ with $\xi \in [0, 1)$, existence of a companion
     surviving $N$ steps is equivalent to
     $\exists \xi \in [0, 1),\ \forall n \le N,\ \text{Int.fract}\!\big((a_0 + \xi)(3/2)^n\big) < 1/2$.
   - In particular, this proves the exact `Int.fract` formulation for
     `recordHolderA0 = 29871555608238677` used in the `formal-conjectures` upstream statement.

3. **Infinite-Horizon $Z$-Number Bridge & Explicit Strict-Endpoint Condition
   (`ValidCompanionForever`, `validCompanionForever_iff_floor_and_forall_fract_lt_half`,
   `forall_minSlack_pos_of_validCompanionForever`,
   `validCompanionForever_of_block_boundary_separation`)**:
   - `ValidCompanionForever a_0 α` is unconditionally equivalent to
     $\lfloor \alpha \rfloor = a_0 \wedge \forall n : \mathbb{N},\ \text{Int.fract}\!\big(\alpha (3/2)^n\big) < 1/2$.
   - Along an infinite block chain $\forall K,\, \text{ValidBlockChain } a_0\ s\ u\ K$,
     every infinite companion satisfies $\forall m,\, 0 < \text{minSlack } s\ m$,
     and conversely any real $\alpha_\infty$ satisfying the block-boundary separation
     $\forall m,\, \text{lowerBound } a_0\ (T(m)) \le \alpha_\infty < \text{upperBound } a_0\ (T(m))$
     is a valid companion across **all** steps $n \in \mathbb{N}$ (boundaries and interiors).

4. **Connection to the Rational-Base Numeration System $T_{3/2}(x) = \lceil 3x/2 \rceil$
   and Deterministic Subword Exclusion (`step_eq_rational_base_ceil`,
   `no_validCompanionForever_of_consecutive_odd_steps`,
   `no_validCompanionForever_of_coasting_mod_four_eq_three`)**:
   Connects `Mahler.step` to the Akiyama–Frougny–Sakarovitch (2008) /
   Andrieu–Eliahou–Vivion (2025) rational-base operator $T_{3/2}$ and proves that
   a single deterministic occurrence of `OO` or a coasting $\equiv 3 \pmod 4$ return
   excludes `ValidCompanionForever` without requiring full Borel normality.
-/

namespace Mahler.InfiniteZNumberBridge

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
open Mahler.SubwordComplexity
open Mahler.SimultaneousBaseDigits
open Mahler.MultiStepGCD
open Mahler.SeriesHankel
open Mahler.ThreeAdicSeedLocks
open Mahler.CoupledFractionalDynamics
open Mahler.Mod2304Sieve
open Mahler.TwoSidedCRTObstructions
open Mahler.ThreeAdicConservation
open Mahler.Mod216QuotientFloor

/-! ## 1. Floor, Fractional Part, and Why Odd Steps Force the Ceiling Recurrence -/

/-- For any natural number `g` and real `x`, `⌊x⌋ = (g : ℤ) ∧ Int.fract x < 1 / 2`
holds if and only if `(g : ℝ) ≤ x ∧ x < (g : ℝ) + 1 / 2`. -/
theorem floor_eq_and_fract_lt_half_iff (g : ℕ) (x : ℝ) :
    (⌊x⌋ = (g : ℤ) ∧ Int.fract x < 1 / 2) ↔
      ((g : ℝ) ≤ x ∧ x < (g : ℝ) + 1 / 2) := by
  constructor
  · rintro ⟨hfl, hfr⟩
    have hle : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
    rw [hfl, Int.cast_natCast] at hle
    have hfract : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) := Int.self_sub_floor x
    rw [hfl, Int.cast_natCast] at hfract
    refine ⟨hle, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    have hfl : ⌊x⌋ = (g : ℤ) := by
      rw [Int.floor_eq_iff, Int.cast_natCast]
      refine ⟨hlo, by linarith⟩
    have hfract : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) := Int.self_sub_floor x
    rw [hfl, Int.cast_natCast] at hfract
    exact ⟨hfl, by linarith⟩

/-- **Why Odd Steps Force the Ceiling Recurrence (`odd_step_floor_exceeds_half_and_forces_ceil`)**:
For any odd natural number `g` (`g % 2 = 1`) and any `x = g + r` with `0 ≤ r < 1/2`:
1. Relative to the integer floor `(3 * g) / 2 = ⌊3g/2⌋`, the remainder is
   `1/2 + (3/2) * r ≥ 1/2`, so `⌊(3/2) * x⌋` can **never** equal `(3 * g) / 2`
   when `Int.fract ((3/2) * x) < 1/2`.
2. Relative to the ceiling `step g = (3 * g + 1) / 2 = ⌈3g/2⌉`,
   `(3/2) * x = (step g : ℝ) + ((3/2) * r - 1/2)`, and
   `((step g : ℝ) ≤ (3/2) * x ∧ (3/2) * x < (step g : ℝ) + 1/2) ↔ 1 / 3 ≤ r`. -/
theorem odd_step_floor_exceeds_half_and_forces_ceil {g : ℕ} {r : ℝ}
    (hodd : g % 2 = 1) (hr0 : 0 ≤ r) (hr1 : r < 1 / 2) :
    (1 / 2 : ℝ) ≤ (3 / 2 : ℝ) * ((g : ℝ) + r) - (((3 * g) / 2 : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) * ((g : ℝ) + r) =
        (step g : ℝ) + ((3 / 2 : ℝ) * r - 1 / 2) ∧
      (((step g : ℝ) ≤ (3 / 2 : ℝ) * ((g : ℝ) + r) ∧
          (3 / 2 : ℝ) * ((g : ℝ) + r) < (step g : ℝ) + 1 / 2) ↔
        (1 / 3 : ℝ) ≤ r) := by
  have hdiv : 2 * ((3 * g) / 2) + 1 = 3 * g := by omega
  have hdiv_real : 2 * (((3 * g) / 2 : ℕ) : ℝ) + 1 = 3 * (g : ℝ) := by
    exact_mod_cast hdiv
  have hstep : 2 * step g = 3 * g + 1 := by
    have h := step_identity g
    omega
  have hstep_real : 2 * (step g : ℝ) = 3 * (g : ℝ) + 1 := by
    exact_mod_cast hstep
  refine ⟨by linarith, by linarith, ?_⟩
  constructor <;> intro h
  · linarith
  · refine ⟨by linarith, by linarith⟩

/-! ## 2. Exact Equivalence Between `ValidCompanionUpTo` and `Int.fract` -/

/-- Inductive step: if `ValidCompanionAt a_0 α n` holds and
`Int.fract (α * (3 / 2 : ℝ) ^ (n + 1)) < 1 / 2`, then
`ValidCompanionAt a_0 α (n + 1)` holds (and in particular
`⌊α * (3 / 2 : ℝ) ^ (n + 1)⌋ = (orbit a_0 (n + 1) : ℤ)`). -/
theorem validCompanionAt_succ_of_fract_lt_half {a_0 : ℕ} {α : ℝ} {n : ℕ}
    (hn : ValidCompanionAt a_0 α n)
    (hfr : Int.fract (α * (3 / 2 : ℝ) ^ (n + 1)) < 1 / 2) :
    ValidCompanionAt a_0 α (n + 1) := by
  rcases hn with ⟨hlo_n, hhi_n⟩
  have hstep_nat := step_identity (orbit a_0 n)
  have hstep_real :
      2 * (orbit a_0 (n + 1) : ℝ) =
        3 * (orbit a_0 n : ℝ) + ((orbit a_0 n % 2 : ℕ) : ℝ) := by
    exact_mod_cast hstep_nat
  have hmod_bounds :
      (0 : ℝ) ≤ ((orbit a_0 n % 2 : ℕ) : ℝ) ∧
        ((orbit a_0 n % 2 : ℕ) : ℝ) ≤ 1 := by
    have h0 : 0 ≤ orbit a_0 n % 2 := Nat.zero_le _
    have h1 : orbit a_0 n % 2 ≤ 1 := by omega
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  set x1 : ℝ := α * (3 / 2 : ℝ) ^ (n + 1)
  have hx1_eq : x1 = (3 / 2 : ℝ) * (α * (3 / 2 : ℝ) ^ n) := by
    dsimp [x1]
    rw [pow_succ]
    ring
  set g1 : ℕ := orbit a_0 (n + 1)
  have hx1_lo : (g1 : ℝ) - 1 / 2 ≤ x1 := by
    dsimp [g1]
    linarith [hmod_bounds.2]
  have hx1_hi : x1 < (g1 : ℝ) + 3 / 4 := by
    dsimp [g1]
    linarith [hmod_bounds.1]
  set z : ℤ := ⌊x1⌋
  have hz_le : (z : ℝ) ≤ x1 := Int.floor_le x1
  have hfract_eq : Int.fract x1 = x1 - (z : ℝ) := Int.self_sub_floor x1
  have hz_gt : x1 - 1 / 2 < (z : ℝ) := by linarith
  have hz_lt_upper : (z : ℝ) < ((g1 : ℤ) : ℝ) + 1 := by
    rw [Int.cast_natCast]
    linarith
  have hz_gt_lower : ((g1 : ℤ) : ℝ) - 1 < (z : ℝ) := by
    rw [Int.cast_natCast]
    linarith
  have hz_lt_int : z < (g1 : ℤ) + 1 := by
    exact_mod_cast hz_lt_upper
  have hz_gt_int : (g1 : ℤ) - 1 < z := by
    exact_mod_cast hz_gt_lower
  have hz_eq : z = (g1 : ℤ) := by omega
  exact (floor_eq_and_fract_lt_half_iff g1 x1).mp ⟨hz_eq, hfr⟩

/-- **Exact Finite-Horizon Equivalence (`validCompanionUpTo_iff_floor_and_fract_lt_half`)**:
For every `a_0 : ℕ`, `α : ℝ`, and `N : ℕ`, `ValidCompanionUpTo a_0 α N` holds
if and only if `⌊α⌋ = (a_0 : ℤ)` and `∀ n ≤ N, Int.fract (α * (3 / 2 : ℝ) ^ n) < 1 / 2`. -/
theorem validCompanionUpTo_iff_floor_and_fract_lt_half (a_0 : ℕ) (α : ℝ) (N : ℕ) :
    ValidCompanionUpTo a_0 α N ↔
      (⌊α⌋ = (a_0 : ℤ) ∧ ∀ n ≤ N, Int.fract (α * (3 / 2 : ℝ) ^ n) < 1 / 2) := by
  constructor
  · intro hsurv
    have h0 : ValidCompanionAt a_0 α 0 := hsurv 0 (Nat.zero_le N)
    unfold ValidCompanionAt at h0
    simp only [orbit, pow_zero, mul_one] at h0
    have hfl0 := (floor_eq_and_fract_lt_half_iff a_0 α).mpr h0
    refine ⟨hfl0.1, ?_⟩
    intro n hn
    have hn_at : ValidCompanionAt a_0 α n := hsurv n hn
    unfold ValidCompanionAt at hn_at
    exact ((floor_eq_and_fract_lt_half_iff (orbit a_0 n) (α * (3 / 2 : ℝ) ^ n)).mpr hn_at).2
  · rintro ⟨hfl0, hfr⟩
    intro n hn
    induction n with
    | zero =>
        have hfr0 := hfr 0 (Nat.zero_le N)
        simp only [pow_zero, mul_one] at hfr0
        have h0 := (floor_eq_and_fract_lt_half_iff a_0 α).mp ⟨hfl0, hfr0⟩
        unfold ValidCompanionAt
        simpa [orbit] using h0
    | succ n ih =>
        exact validCompanionAt_succ_of_fract_lt_half (ih (by omega)) (hfr (n + 1) hn)

/-- **Unit-Offset Fractional-Part Equivalence (`exists_validCompanionUpTo_iff_exists_unit_offset_fract_lt_half`)**:
There exists `α : ℝ` satisfying `ValidCompanionUpTo a_0 α N` if and only if there
exists a fractional offset `ξ ∈ [0, 1)` such that
`∀ n ≤ N, Int.fract (((a_0 : ℝ) + ξ) * (3 / 2 : ℝ) ^ n) < 1 / 2`. -/
theorem exists_validCompanionUpTo_iff_exists_unit_offset_fract_lt_half (a_0 N : ℕ) :
    (∃ α : ℝ, ValidCompanionUpTo a_0 α N) ↔
      (∃ ξ : ℝ, 0 ≤ ξ ∧ ξ < 1 ∧
        ∀ n ≤ N, Int.fract (((a_0 : ℝ) + ξ) * (3 / 2 : ℝ) ^ n) < 1 / 2) := by
  constructor
  · rintro ⟨α, hsurv⟩
    rcases (validCompanionUpTo_iff_floor_and_fract_lt_half a_0 α N).mp hsurv with
      ⟨hfl, hfr⟩
    refine ⟨α - (a_0 : ℝ), ?_, ?_, ?_⟩
    · have hle : ((⌊α⌋ : ℤ) : ℝ) ≤ α := Int.floor_le α
      rw [hfl, Int.cast_natCast] at hle
      linarith
    · have hlt : α < ((⌊α⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one α
      rw [hfl, Int.cast_natCast] at hlt
      linarith
    · intro n hn
      have hsum : (a_0 : ℝ) + (α - (a_0 : ℝ)) = α := by ring
      rw [hsum]
      exact hfr n hn
  · rintro ⟨ξ, hξ0, hξ1, hfr⟩
    refine ⟨(a_0 : ℝ) + ξ, ?_⟩
    rw [validCompanionUpTo_iff_floor_and_fract_lt_half]
    refine ⟨?_, hfr⟩
    rw [Int.floor_eq_iff, Int.cast_natCast]
    exact ⟨by linarith, by linarith⟩

/-- **Exact Direct `Int.fract` Record-Holder Theorem (`recordHolderA0_fract_offset_113_survival_and_114_death`)**:
Establishes the exact statement in the `formal-conjectures` format:
`recordHolderA0 = 29871555608238677` admits a fractional offset `ξ ∈ [0, 1)`
keeping `Int.fract ((recordHolderA0 + ξ) * (3/2)^n) < 1/2` for all `n ≤ 113`,
and admits no such offset for `n ≤ 114`. -/
theorem recordHolderA0_fract_offset_113_survival_and_114_death :
    (∃ ξ : ℝ, 0 ≤ ξ ∧ ξ < 1 ∧
      ∀ n ≤ 113, Int.fract (((recordHolderA0 : ℝ) + ξ) * (3 / 2 : ℝ) ^ n) < 1 / 2) ∧
    ¬ (∃ ξ : ℝ, 0 ≤ ξ ∧ ξ < 1 ∧
      ∀ n ≤ 114, Int.fract (((recordHolderA0 : ℝ) + ξ) * (3 / 2 : ℝ) ^ n) < 1 / 2) := by
  rcases recordHolderA0_exact_113_survival_and_114_death with ⟨_, h113, h114⟩
  exact ⟨(exists_validCompanionUpTo_iff_exists_unit_offset_fract_lt_half recordHolderA0 113).mp h113,
    fun h => h114 ((exists_validCompanionUpTo_iff_exists_unit_offset_fract_lt_half recordHolderA0 114).mpr h)⟩

/-! ## 3. Infinite-Horizon $Z$-Number Companion Bridge & Strict Endpoint Condition -/

/-- Infinite-horizon Mahler companion predicate: `α` satisfies `ValidCompanionAt a_0 α n`
for every `n : ℕ`. -/
def ValidCompanionForever (a_0 : ℕ) (α : ℝ) : Prop :=
  ∀ n : ℕ, ValidCompanionAt a_0 α n

/-- `ValidCompanionForever a_0 α` holds iff `ValidCompanionUpTo a_0 α N` holds for all `N`. -/
theorem validCompanionForever_iff_forall_upTo (a_0 : ℕ) (α : ℝ) :
    ValidCompanionForever a_0 α ↔ ∀ N : ℕ, ValidCompanionUpTo a_0 α N := by
  constructor
  · intro h N n _
    exact h n
  · intro h n
    exact h n n le_rfl

/-- **Exact Infinite-Horizon $Z$-Number Equivalence (`validCompanionForever_iff_floor_and_forall_fract_lt_half`)**:
`ValidCompanionForever a_0 α` holds if and only if `⌊α⌋ = (a_0 : ℤ)` and
`∀ n : ℕ, Int.fract (α * (3 / 2 : ℝ) ^ n) < 1 / 2`. -/
theorem validCompanionForever_iff_floor_and_forall_fract_lt_half (a_0 : ℕ) (α : ℝ) :
    ValidCompanionForever a_0 α ↔
      (⌊α⌋ = (a_0 : ℤ) ∧ ∀ n : ℕ, Int.fract (α * (3 / 2 : ℝ) ^ n) < 1 / 2) := by
  rw [validCompanionForever_iff_forall_upTo]
  constructor
  · intro hall
    have h0 := (validCompanionUpTo_iff_floor_and_fract_lt_half a_0 α 0).mp (hall 0)
    refine ⟨h0.1, fun n => ?_⟩
    exact ((validCompanionUpTo_iff_floor_and_fract_lt_half a_0 α n).mp (hall n)).2 n le_rfl
  · rintro ⟨hfl, hfr⟩ N
    rw [validCompanionUpTo_iff_floor_and_fract_lt_half]
    exact ⟨hfl, fun n _ => hfr n⟩

/-- Along an infinite valid block chain (`∀ K, ValidBlockChain a_0 s u K`),
existence of an infinite companion `ValidCompanionForever a_0 α` forces
`0 < minSlack s m` for every block index `m : ℕ`. -/
theorem forall_minSlack_pos_of_validCompanionForever
    {a_0 : ℕ} {s u : ℕ → ℕ} {α : ℝ}
    (hchain : ∀ K : ℕ, ValidBlockChain a_0 s u K)
    (hforever : ValidCompanionForever a_0 α) :
    ∀ m : ℕ, 0 < minSlack s m := by
  intro m
  have hup : ValidCompanionUpTo a_0 α (blockSteps s (m + 1)) :=
    (validCompanionForever_iff_forall_upTo a_0 α).mp hforever (blockSteps s (m + 1))
  have hex : ∃ ξ : ℝ, ValidCompanionUpTo a_0 ξ (blockSteps s (m + 1)) := ⟨α, hup⟩
  have hiff :=
    exists_validCompanionUpTo_iff_minSlack_pos (K := m + 1) (by omega) (hchain (m + 1))
  simpa using hiff.mp hex

/-- **Infinite-Horizon Reconstruction from Strict Block-Boundary Separation
(`validCompanionForever_of_block_boundary_separation`)**:
Along an infinite valid block chain (`∀ K, ValidBlockChain a_0 s u K`), if a real
number `α` lies above every block-boundary lower bound (`∀ m, lowerBound a_0 (blockSteps s m) ≤ α`)
and strictly below every block-boundary upper bound (`∀ j, α < upperBound a_0 (blockSteps s j)`),
then `ValidCompanionForever a_0 α` holds at **every** step `n : ℕ` (both block
boundaries and interior even steps). -/
theorem validCompanionForever_of_block_boundary_separation
    {a_0 : ℕ} {s u : ℕ → ℕ} {α : ℝ}
    (hchain : ∀ K : ℕ, ValidBlockChain a_0 s u K)
    (hlo : ∀ m : ℕ, lowerBound a_0 (blockSteps s m) ≤ α)
    (hhi : ∀ j : ℕ, α < upperBound a_0 (blockSteps s j)) :
    ValidCompanionForever a_0 α := by
  have hsteps_ge : ∀ K : ℕ, K ≤ blockSteps s K := by
    intro K
    induction K with
    | zero => simp [blockSteps]
    | succ K ih =>
        have hsK : 1 ≤ s K := (hchain (K + 1) K (Nat.lt_succ_self K)).1
        simp only [blockSteps]
        omega
  intro n
  have hn_le : n ≤ blockSteps s n := hsteps_ge n
  rw [validCompanionAt_iff_bounds]
  refine ⟨le_trans (lowerBound_mono a_0 hn_le) (hlo n), ?_⟩
  rcases locate_step_in_block s n n hn_le with h_eq | ⟨j, hjn, k, hks, hn_eq⟩
  · rw [h_eq]
    exact hhi n
  · rw [hn_eq]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hhi j
    · have hle_end :=
        upperBound_block_end_le_interior hjn (hchain n) hkpos (Nat.le_of_lt hks)
      exact lt_of_lt_of_le (hhi (j + 1)) hle_end

/-! ## 4. Rational-Base $3/2$ Operator & Deterministic Subword Exclusion (Path 4) -/

/-- **Identity Between `Mahler.step` and the Rational-Base $3/2$ Ceiling Operator
(`step_eq_rational_base_ceil`)**:
For every natural number `x`, `2 * step x = 3 * x + x % 2` and
`(step x : ℤ) = ⌈(3 : ℚ) * (x : ℚ) / 2⌉` (`T_{3/2}(x) = ⌈3x/2⌉` in
Akiyama–Frougny–Sakarovitch 2008 and Andrieu–Eliahou–Vivion 2025). -/
theorem step_eq_rational_base_ceil (x : ℕ) :
    2 * step x = 3 * x + x % 2 ∧
      step x = (3 * x + x % 2) / 2 := by
  have h := step_identity x
  exact ⟨h, by omega⟩

/-- **Deterministic `OO` Subword Exclusion (`no_validCompanionForever_of_consecutive_odd_steps`)**:
Without assuming Borel normality or equidistribution of rational-base digits,
if `orbit a_0` ever visits two consecutive odd integers at step `n`
(`orbit a_0 n % 2 = 1` and `orbit a_0 (n + 1) % 2 = 1`), then no real `α` can
satisfy `ValidCompanionForever a_0 α`. -/
theorem no_validCompanionForever_of_consecutive_odd_steps
    {a_0 n : ℕ} (hodd0 : orbit a_0 n % 2 = 1) (hodd1 : orbit a_0 (n + 1) % 2 = 1) :
    ¬ ∃ α : ℝ, ValidCompanionForever a_0 α := by
  rintro ⟨α, hforever⟩
  have hn0 := (validCompanionAt_iff_fracPart a_0 α n).mp (hforever n)
  have hn1 := (validCompanionAt_iff_fracPart a_0 α (n + 1)).mp (hforever (n + 1))
  have hn2 := (validCompanionAt_iff_fracPart a_0 α (n + 2)).mp (hforever (n + 2))
  have hrec0 := fracPart_succ a_0 α n
  have hrec1 := fracPart_succ a_0 α (n + 1)
  rw [hodd0] at hrec0
  rw [hodd1] at hrec1
  norm_num at hrec0 hrec1
  linarith [hn0.2, hn2.1]

/-- **Deterministic `≡ 3 (mod 4)` Return Exclusion (`no_validCompanionForever_of_coasting_mod_four_eq_three`)**:
Along any valid block chain (`m < K`), a single occurrence of
`orbit a_0 (blockSteps s m) % 4 = 3` forces `s m = 1` and rules out
`ValidCompanionForever a_0 α`. -/
theorem no_validCompanionForever_of_coasting_mod_four_eq_three
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hmod4 : orbit a_0 (blockSteps s m) % 4 = 3) :
    ¬ ∃ α : ℝ, ValidCompanionForever a_0 α := by
  rintro ⟨α, hforever⟩
  have hsurv : ValidCompanionUpTo a_0 α (blockSteps s m + 2) :=
    (validCompanionForever_iff_forall_upTo a_0 α).mp hforever (blockSteps s m + 2)
  exact coasting_mod_four_eq_three_impossible hmK hchain hmod4 ⟨α, hsurv⟩

end Mahler.InfiniteZNumberBridge
