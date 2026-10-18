import Mod2304CombinedSieve

/-!
# The Global Two-Sided Chinese Remainder Bound & Backward Predecessor Obstructions (`11 ≤ u k`)

This module formalizes Paths 9 & 10 (Modules 109–110):

1. **Path 9 — Global Two-Sided (`3^(T(k)) × 2^(T(K) - T(k + 1))`) CRT Bound
   (`two_sided_crt_exponential_bound`, `coasting_u_lt_two_sided_crt_modulus`)**:
   Along any `ValidBlockChain a_0 s u K` (`k < K`) with `0 < integerSlack s k`:
   - Looking `k` blocks backward (`0 → k`) locks `2^(tailSteps s k) * u k` modulo `3^(blockSteps s k)`.
   - Looking `K - 1 - k` blocks forward (`k → K - 1`) locks
     `3^(blockSteps (shiftSeq s k) (K - 1 - k)) * u k + coprimeRemainder (shiftSeq s k) (K - 1 - k)`
     modulo `2^(tailSteps (shiftSeq s k) (K - 1 - k))`.
   - Multiplying the orbit bound `2^(T(k + 1) + 1) * u k < 3^(T(k) + 1) * (2 * a_0 + 1)`
     by `2^(tailSteps (shiftSeq s k) (K - 1 - k))` yields the global two-sided CRT bound:
     `2^(blockSteps s K + 1) * u k <
       3 * (2 * a_0 + 1) * (3^(blockSteps s k) * 2^(tailSteps (shiftSeq s k) (K - 1 - k)))`.
   - In the coasting regime (`3 * (2 * a_0 + 1) ≤ 2^(blockSteps s K + 1)`), every
     intermediate quotient `u k` is strictly smaller than its two-sided CRT modulus:
     `u k < 3^(blockSteps s k) * 2^(tailSteps (shiftSeq s k) (K - 1 - k))`.
2. **Path 10 — Unconditional Impossibility of `u k = 1` for `k ≥ 1` Along Surviving Orbits
   (`u_eq_one_forces_even_block_and_next_one`, `u_ne_one_of_pos_index_and_two_le_next`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ k`, `k + 1 < K`):
   - If `u k = 1`, then the backward Mod-3 lock (`u k % 3 = s k % 2 + 1`) forces
     `s k % 2 = 0` (`s k` is even), and the forward recurrence
     `2^(s (k + 1)) * u (k + 1) = 3^(s k) + 1 ≡ 2 (mod 4)` forces `s (k + 1) = 1`!
   - Thus whenever `2 ≤ s (k + 1)`, `u k ≠ 1` holds unconditionally for all `k ≥ 1`.
3. **Path 10 — Mod-9 Backward Obstructions for `u k ∈ {5, 7}` & the `11 ≤ u k` Floor
   (`u_eq_five_or_seven_mod_six_locks`, `eleven_le_u_on_bounded_blocks`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ k`, `k + 1 < K`) with `2 ≤ s (k - 1)`:
   - `u k = 5 → s k % 6 = 1` (impossible for `2 ≤ s k ≤ 6`).
   - `u k = 7 → s k % 6 = 2` (impossible for `3 ≤ s k ≤ 7`).
   - Combining `u k ≠ 1`, `u k ≠ 5`, `u k ≠ 7` with `Nat.Coprime (u k) 6` (and
     `post_two_u_ne_seven_of_pos_index` when `s k = 2` and `3 ≤ s (k - 1)` for `k ≥ 2`)
     proves that **`11 ≤ u k`** whenever `3 ≤ s k ≤ 6` (for `k ≥ 1`) or `2 ≤ s k ≤ 6`
     (for `k ≥ 2` with `3 ≤ s (k - 1)`).
-/

namespace Mahler.TwoSidedCRTObstructions

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

/-! ## 1. Path 9: Global Two-Sided (`3^(T(k)) × 2^(T(K) - T(k + 1))`) CRT Bound -/

/-- Exact step-sum decomposition at pivot block `k < K`:
`(blockSteps s (k + 1) + 1) + tailSteps (shiftSeq s k) (K - 1 - k) = blockSteps s K + 1`. -/
theorem pivot_step_sum_add_forward_tailSteps {s : ℕ → ℕ} {K k : ℕ} (hkK : k < K) :
    (blockSteps s (k + 1) + 1) + tailSteps (shiftSeq s k) (K - 1 - k) =
      blockSteps s K + 1 := by
  have htail := add_tailSteps_eq_blockSteps_succ (shiftSeq s k) (K - 1 - k)
  have hshift0 : shiftSeq s k 0 = s k := rfl
  have hK_idx : K - 1 - k + 1 = K - k := by omega
  rw [hshift0, hK_idx] at htail
  have hadd := blockSteps_add s k (K - k)
  have hk_add : k + (K - k) = K := by omega
  rw [hk_add] at hadd
  have hstep_k1 : blockSteps s (k + 1) = blockSteps s k + s k := rfl
  omega

/-- **Global Two-Sided CRT Exponential Bound (`two_sided_crt_exponential_bound`)**:
Along any `ValidBlockChain a_0 s u K` (`k < K`) with `0 < integerSlack s k`,
`2^(blockSteps s K + 1) * u k <
  3 * (2 * a_0 + 1) * (3^(blockSteps s k) * 2^(tailSteps (shiftSeq s k) (K - 1 - k)))`. -/
theorem two_sided_crt_exponential_bound
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hkK : k < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s k) :
    2 ^ (blockSteps s K + 1) * u k <
      3 * (2 * a_0 + 1) *
        (3 ^ (blockSteps s k) *
          2 ^ (tailSteps (shiftSeq s k) (K - 1 - k))) := by
  have horbit := integerSlack_eq_orbit_slack hkK hchain
  have horbit' :
      integerSlack s k =
        ((3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) : ℕ) : ℤ) -
          ((2 ^ (blockSteps s (k + 1) + 1) * u k : ℕ) : ℤ) := by
    rw [horbit]
    push_cast
    rfl
  have hlt_base :
      2 ^ (blockSteps s (k + 1) + 1) * u k <
        3 ^ (blockSteps s k + 1) * (2 * a_0 + 1) := by
    omega
  have h2_pos : 0 < 2 ^ (tailSteps (shiftSeq s k) (K - 1 - k)) :=
    Nat.pow_pos (by decide)
  have hmul := Nat.mul_lt_mul_of_pos_right hlt_base h2_pos
  have hexp := pivot_step_sum_add_forward_tailSteps (s := s) hkK
  have hlhs :
      (2 ^ (blockSteps s (k + 1) + 1) * u k) *
          2 ^ (tailSteps (shiftSeq s k) (K - 1 - k)) =
        2 ^ (blockSteps s K + 1) * u k := by
    calc
      (2 ^ (blockSteps s (k + 1) + 1) * u k) *
          2 ^ (tailSteps (shiftSeq s k) (K - 1 - k)) =
        (2 ^ (blockSteps s (k + 1) + 1) *
          2 ^ (tailSteps (shiftSeq s k) (K - 1 - k))) * u k := by ring
      _ = 2 ^ (blockSteps s K + 1) * u k := by rw [← Nat.pow_add, hexp]
  have hrhs :
      (3 ^ (blockSteps s k + 1) * (2 * a_0 + 1)) *
          2 ^ (tailSteps (shiftSeq s k) (K - 1 - k)) =
        3 * (2 * a_0 + 1) *
          (3 ^ (blockSteps s k) *
            2 ^ (tailSteps (shiftSeq s k) (K - 1 - k))) := by
    rw [Nat.pow_succ]
    ring
  rw [hlhs, hrhs] at hmul
  exact hmul

/-- **Coasting Two-Sided CRT Uniqueness Bound (`coasting_u_lt_two_sided_crt_modulus`)**:
In the coasting regime (`3 * (2 * a_0 + 1) ≤ 2^(blockSteps s K + 1)`), every
intermediate quotient `u k` (`k < K`, `0 < integerSlack s k`) is strictly smaller
than its two-sided Chinese Remainder modulus:
`u k < 3^(blockSteps s k) * 2^(tailSteps (shiftSeq s k) (K - 1 - k))`. -/
theorem coasting_u_lt_two_sided_crt_modulus
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hkK : k < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s k)
    (hcoast : 3 * (2 * a_0 + 1) ≤ 2 ^ (blockSteps s K + 1)) :
    u k <
      3 ^ (blockSteps s k) *
        2 ^ (tailSteps (shiftSeq s k) (K - 1 - k)) := by
  have hbound := two_sided_crt_exponential_bound hkK hchain hpos
  have hle :
      3 * (2 * a_0 + 1) *
          (3 ^ (blockSteps s k) *
            2 ^ (tailSteps (shiftSeq s k) (K - 1 - k))) ≤
        2 ^ (blockSteps s K + 1) *
          (3 ^ (blockSteps s k) *
            2 ^ (tailSteps (shiftSeq s k) (K - 1 - k))) :=
    Nat.mul_le_mul_right _ hcoast
  exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hbound hle)

/-! ## 2. Path 10: Unconditional Impossibility of `u k = 1` for `k ≥ 1` -/

private theorem three_pow_even_mod_four {n : ℕ} (heven : n % 2 = 0) :
    3 ^ n % 4 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, Nat.pow_add, Nat.mul_mod, ih (by omega)]

/-- **Backward + Forward Lock at `u k = 1` (`u_eq_one_forces_even_block_and_next_one`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ k`, `k + 1 < K`), if `u k = 1`, then:
1. `s k % 2 = 0` (from the backward Mod-3 lock `k - 1 → k`), and
2. `s (k + 1) = 1` (from the forward Mod-4 lock `2^(s (k + 1)) * u (k + 1) = 3^(s k) + 1 ≡ 2 (mod 4)`). -/
theorem u_eq_one_forces_even_block_and_next_one
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hu1 : u k = 1) :
    s k % 2 = 0 ∧ s (k + 1) = 1 := by
  have hmod3 :=
    (u_succ_mod_three_and_nine_locks (k := k - 1) (by omega) hchain).1
  have hk_idx : k - 1 + 1 = k := by omega
  rw [hk_idx, hu1] at hmod3
  have hsk_even : s k % 2 = 0 := by omega
  have hrec := coprime_quotient_recurrence hk1 hchain
  rw [hu1, mul_one] at hrec
  have h3_mod4 := three_pow_even_mod_four hsk_even
  have hsum_mod4 : (3 ^ (s k) + 1) % 4 = 2 := by omega
  rw [← hrec] at hsum_mod4
  have hsk1_ge1 : 1 ≤ s (k + 1) := (hchain (k + 1) hk1).1
  have hsk1_eq1 : s (k + 1) = 1 := by
    by_contra hne1
    have hge2 : 2 ≤ s (k + 1) := by omega
    have hdvd4 : 4 ∣ 2 ^ (s (k + 1)) * u (k + 1) :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge2) (u (k + 1))
    have h0 := Nat.mod_eq_zero_of_dvd hdvd4
    omega
  exact ⟨hsk_even, hsk1_eq1⟩

/-- **Unconditional Impossibility of `u k = 1` for `k ≥ 1` (`u_ne_one_of_pos_index_and_two_le_next`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ k`, `k + 1 < K`) with `2 ≤ s (k + 1)`,
we have `u k ≠ 1`. -/
theorem u_ne_one_of_pos_index_and_two_le_next
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs_next : 2 ≤ s (k + 1)) :
    u k ≠ 1 := by
  intro hu1
  have h1 := (u_eq_one_forces_even_block_and_next_one hk_pos hk1 hchain hu1).2
  omega

/-! ## 3. Path 10: Mod-9 Backward Obstructions for `u k ∈ {5, 7}` & the `11 ≤ u k` Floor -/

private theorem five_pow_mod_nine_periodic (n : ℕ) :
    5 ^ n % 9 = 5 ^ (n % 6) % 9 := by
  have hdiv : n = 6 * (n / 6) + n % 6 := (Nat.div_add_mod n 6).symm
  conv_lhs => rw [hdiv, Nat.pow_add, Nat.mul_mod]
  have h6 : 5 ^ (6 * (n / 6)) % 9 = 1 := by
    induction (n / 6) with
    | zero => rfl
    | succ q ih =>
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih]
  rw [h6, one_mul, Nat.mod_mod]

/-- **Mod-9 Backward Obstructions for `u k ∈ {5, 7}` (`u_eq_five_or_seven_mod_six_locks`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ k < K`) with `2 ≤ s (k - 1)`:
1. `u k = 5 → s k % 6 = 1`, and
2. `u k = 7 → s k % 6 = 2`. -/
theorem u_eq_five_or_seven_mod_six_locks
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hkK : k < K) (hchain : ValidBlockChain a_0 s u K)
    (hs_prev : 2 ≤ s (k - 1)) :
    (u k = 5 → s k % 6 = 1) ∧
      (u k = 7 → s k % 6 = 2) := by
  have hmod9 :=
    (u_succ_mod_three_and_nine_locks (k := k - 1) (by omega) hchain).2 hs_prev
  have hk_idx : k - 1 + 1 = k := by omega
  rw [hk_idx, five_pow_mod_nine_periodic (s k)] at hmod9
  have hcases :
      s k % 6 = 0 ∨ s k % 6 = 1 ∨ s k % 6 = 2 ∨
      s k % 6 = 3 ∨ s k % 6 = 4 ∨ s k % 6 = 5 := by omega
  constructor
  · intro hu5
    rw [hu5] at hmod9
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0] at hmod9; norm_num at hmod9
    · exact h1
    · rw [h2] at hmod9; norm_num at hmod9
    · rw [h3] at hmod9; norm_num at hmod9
    · rw [h4] at hmod9; norm_num at hmod9
    · rw [h5] at hmod9; norm_num at hmod9
  · intro hu7
    rw [hu7] at hmod9
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0] at hmod9; norm_num at hmod9
    · rw [h1] at hmod9; norm_num at hmod9
    · exact h2
    · rw [h3] at hmod9; norm_num at hmod9
    · rw [h4] at hmod9; norm_num at hmod9
    · rw [h5] at hmod9; norm_num at hmod9

/-- **The `11 ≤ u k` Bounded-Block Quotient Floor (`eleven_le_u_on_bounded_blocks`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ k`, `k + 1 < K`) with `2 ≤ s (k - 1)`,
`2 ≤ s (k + 1)`, and `3 ≤ s k ≤ 6`, we have `11 ≤ u k`. -/
theorem eleven_le_u_on_bounded_blocks
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk_pos : 1 ≤ k) (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K)
    (hs_prev : 2 ≤ s (k - 1)) (hs_next : 2 ≤ s (k + 1))
    (hsk_lo : 3 ≤ s k) (hsk_hi : s k ≤ 6) :
    11 ≤ u k := by
  have hne1 := u_ne_one_of_pos_index_and_two_le_next hk_pos hk1 hchain hs_next
  rcases u_eq_five_or_seven_mod_six_locks hk_pos (by omega) hchain hs_prev with
    ⟨h5, h7⟩
  have hne5 : u k ≠ 5 := by
    intro hu5
    have := h5 hu5
    omega
  have hne7 : u k ≠ 7 := by
    intro hu7
    have := h7 hu7
    omega
  have hcop6 := u_coprime_six_of_validBlockChain (by omega : k < K) hchain
  have hodd : u k % 2 = 1 := hcop6.1
  have hmod3 : u k % 3 ≠ 0 := hcop6.2.1
  omega

end Mahler.TwoSidedCRTObstructions
