import MahlerSeriesHankelFramework

/-!
# The `(2 * a_0 + 1)`-Adic Seed/Slack GCD Locks & 3-Adic (`ℤ_3`) Primitive-Root Orbit Factorization

This module formalizes Paths 5 & 6 (Modules 103–104):

1. **Path 5 — Exact Three-Way Seed–Quotient–Slack GCD Identity
   (`seed_quotient_slack_gcd_eq`)**:
   Along any `ValidBlockChain a_0 s u K` (`1 ≤ m < K`) with `0 < integerSlack s m`,
   because both `u m` and `Δ_m = (integerSlack s m).toNat` are coprime to `6`, the
   orbit equation `2^(T(m + 1) + 1) * u m + Δ_m = 3^(T(m) + 1) * (2 * a_0 + 1)`
   yields the exact three-way GCD equality:
   `Nat.gcd (u m) (integerSlack s m).toNat = Nat.gcd (u m) (2 * a_0 + 1)`
   and
   `Nat.gcd (u m) (integerSlack s m).toNat = Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1)`.
2. **Path 5 — Intrinsic Multi-Step Slack GCD Identity & Consecutive Slack Coprimality
   (`multi_step_slack_gcd_eq_gcd_coprimeRemainder`,
   `consecutive_integerSlack_coprime`)**:
   For any sequence `s : ℕ → ℕ` with `1 ≤ r`, `∀ k < r + d, 1 ≤ s k`, and
   `0 < integerSlack s (r + d)`:
   `Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat =
     Nat.gcd (integerSlack s r).toNat (coprimeRemainder (shiftSeq s r) d)`.
   In particular, for `d = 1`, consecutive positive integer slacks are always
   pairwise coprime:
   `Nat.Coprime (integerSlack s r).toNat (integerSlack s (r + 1)).toNat`.
3. **Path 6 — Exact 3-Adic Factorization & Valuation of Block-Boundary Orbit Values
   (`orbit_succ_eq_three_pow_mul_u`, `orbit_succ_exact_three_adic_valuation`)**:
   Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`), equating
   `3 * orbit a_0 (blockSteps s (k + 1)) + 1 = 2^(s (k + 1)) * u (k + 1)` with
   `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1` proves the exact factorization:
   `orbit a_0 (blockSteps s (k + 1)) = 3^(s k - 1) * u k`.
   Since `Nat.Coprime (u k) 6`, the exact 3-adic valuation of
   `orbit a_0 (blockSteps s (k + 1))` is `s k - 1` and its 3-free part is `u k`.
4. **Path 6 — Closed-Form 3-Adic Residue Lock & Mod-3 / Mod-9 Classifiers
   (`u_succ_mod_three_pow_eq`, `u_succ_mod_three_and_nine_locks`)**:
   Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`):
   - `u (k + 1) % 3^(s k) = (((3^(s k) + 1) / 2)^(s (k + 1))) % 3^(s k)`.
   - `u (k + 1) % 3 = s (k + 1) % 2 + 1` (even block length forces `u ≡ 1 (mod 3)`,
     odd block length forces `u ≡ 2 (mod 3)`).
   - Whenever `2 ≤ s k`, `u (k + 1) % 9 = (5^(s (k + 1))) % 9`.
-/

namespace Mahler.ThreeAdicSeedLocks

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

/-! ## 1. Path 5: Exact Three-Way Seed–Quotient–Slack GCD Identity -/

/-- **Exact Three-Way Seed–Quotient–Slack GCD Identity (`seed_quotient_slack_gcd_eq`)**:
Along any `ValidBlockChain a_0 s u K` (`1 ≤ m < K`) with `0 < integerSlack s m`,
`Nat.gcd (u m) (integerSlack s m).toNat = Nat.gcd (u m) (2 * a_0 + 1)`
and
`Nat.gcd (u m) (integerSlack s m).toNat = Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1)`. -/
theorem seed_quotient_slack_gcd_eq
    {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K)
    (hpos : 0 < integerSlack s m) :
    Nat.gcd (u m) (integerSlack s m).toNat =
        Nat.gcd (u m) (2 * a_0 + 1) ∧
      Nat.gcd (u m) (integerSlack s m).toNat =
        Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1) := by
  have hdecomp := base_two_slack_decomposition hmK hchain hpos
  have hpow2 :
      2 ^ (blockSteps s m) * (2 ^ (s m + 1) * u m) =
        2 ^ (blockSteps s (m + 1) + 1) * u m := by
    have hstep : blockSteps s (m + 1) + 1 = blockSteps s m + (s m + 1) := by
      change blockSteps s m + s m + 1 = blockSteps s m + (s m + 1)
      omega
    rw [hstep, Nat.pow_add 2 (blockSteps s m) (s m + 1), mul_assoc]
  rw [hpow2] at hdecomp
  have hs_ge1 : ∀ k < m, 1 ≤ s k := fun k hk => (hchain k (by omega)).1
  have hDelta_cop6 := integerSlack_toNat_coprime_six hm1 hs_ge1 hpos
  have hu_cop6 := u_coprime_six_of_validBlockChain hmK hchain
  have hu_cop2 : Nat.Coprime (u m) (2 ^ (blockSteps s (m + 1) + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)))
  have hu_cop3 : Nat.Coprime (u m) (3 ^ (blockSteps s m + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)))
  have hDelta_cop2 :
      Nat.Coprime (integerSlack s m).toNat (2 ^ (blockSteps s (m + 1) + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)))
  have hDelta_cop3 :
      Nat.Coprime (integerSlack s m).toNat (3 ^ (blockSteps s m + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)))
  have ha0_cop2 : Nat.Coprime (2 * a_0 + 1) (2 ^ (blockSteps s (m + 1) + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)))
  constructor
  · apply Nat.dvd_antisymm
    · have hdvd_u : Nat.gcd (u m) (integerSlack s m).toNat ∣
          2 ^ (blockSteps s (m + 1) + 1) * u m :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
      have hdvd_D : Nat.gcd (u m) (integerSlack s m).toNat ∣
          (integerSlack s m).toNat :=
        Nat.gcd_dvd_right _ _
      have hdvd_sum : Nat.gcd (u m) (integerSlack s m).toNat ∣
          3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
        rw [hdecomp]
        exact Nat.dvd_add hdvd_u hdvd_D
      have hcop : Nat.Coprime (Nat.gcd (u m) (integerSlack s m).toNat)
          (3 ^ (blockSteps s m + 1)) :=
        hu_cop3.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (hcop.dvd_of_dvd_mul_left hdvd_sum)
    · have hdvd_u : Nat.gcd (u m) (2 * a_0 + 1) ∣
          2 ^ (blockSteps s (m + 1) + 1) * u m :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
      have hdvd_rhs : Nat.gcd (u m) (2 * a_0 + 1) ∣
          3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
      rw [hdecomp] at hdvd_rhs
      have hdvd_D : Nat.gcd (u m) (2 * a_0 + 1) ∣ (integerSlack s m).toNat :=
        (Nat.dvd_add_right hdvd_u).mp hdvd_rhs
      exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hdvd_D
  · apply Nat.dvd_antisymm
    · have hdvd_u : Nat.gcd (u m) (integerSlack s m).toNat ∣
          2 ^ (blockSteps s (m + 1) + 1) * u m :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
      have hdvd_D : Nat.gcd (u m) (integerSlack s m).toNat ∣
          (integerSlack s m).toNat :=
        Nat.gcd_dvd_right _ _
      have hdvd_sum : Nat.gcd (u m) (integerSlack s m).toNat ∣
          3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) := by
        rw [hdecomp]
        exact Nat.dvd_add hdvd_u hdvd_D
      have hcop : Nat.Coprime (Nat.gcd (u m) (integerSlack s m).toNat)
          (3 ^ (blockSteps s m + 1)) :=
        hu_cop3.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      exact Nat.dvd_gcd hdvd_D (hcop.dvd_of_dvd_mul_left hdvd_sum)
    · have hdvd_D : Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1) ∣
          (integerSlack s m).toNat :=
        Nat.gcd_dvd_left _ _
      have hdvd_rhs : Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1) ∣
          3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
      rw [hdecomp] at hdvd_rhs
      have hdvd_2u : Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1) ∣
          2 ^ (blockSteps s (m + 1) + 1) * u m :=
        (Nat.dvd_add_left hdvd_D).mp hdvd_rhs
      have hcop : Nat.Coprime (Nat.gcd (integerSlack s m).toNat (2 * a_0 + 1))
          (2 ^ (blockSteps s (m + 1) + 1)) :=
        hDelta_cop2.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      exact Nat.dvd_gcd (hcop.dvd_of_dvd_mul_left hdvd_2u) hdvd_D

/-! ## 2. Intrinsic Multi-Step Slack GCD Identity & Consecutive Slack Coprimality -/

/-- **Intrinsic Multi-Step Slack GCD Identity (`multi_step_slack_gcd_eq_gcd_coprimeRemainder`)**:
For any sequence `s : ℕ → ℕ` with `1 ≤ r`, `∀ k < r + d, 1 ≤ s k`, and
`0 < integerSlack s (r + d)`:
`Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat =
  Nat.gcd (integerSlack s r).toNat (coprimeRemainder (shiftSeq s r) d)`. -/
theorem multi_step_slack_gcd_eq_gcd_coprimeRemainder
    {s : ℕ → ℕ} {r d : ℕ}
    (hr1 : 1 ≤ r) (hs : ∀ k < r + d, 1 ≤ s k)
    (hpos_rd : 0 < integerSlack s (r + d)) :
    Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat =
      Nat.gcd (integerSlack s r).toNat (coprimeRemainder (shiftSeq s r) d) := by
  have hdepl := slack_depletion_eq_two_pow_mul_remainder s r d
  have h3_pos : (0 : ℤ) < (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) :=
    pow_pos (by decide) _
  have h2R_nonneg :
      (0 : ℤ) ≤
        (2 : ℤ) ^ (blockSteps s r + s r + 1) *
          (coprimeRemainder (shiftSeq s r) d : ℤ) := by
    positivity
  have h3Dr_pos :
      (0 : ℤ) < (3 : ℤ) ^ (blockSteps (shiftSeq s r) d) * integerSlack s r := by
    linarith
  have hpos_r : 0 < integerSlack s r :=
    pos_of_mul_pos_right h3Dr_pos (le_of_lt h3_pos)
  have hnat_eq :
      (integerSlack s (r + d)).toNat +
          2 ^ (blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d =
        3 ^ (blockSteps (shiftSeq s r) d) * (integerSlack s r).toNat := by
    have hto_r : ((integerSlack s r).toNat : ℤ) = integerSlack s r :=
      Int.toNat_of_nonneg (le_of_lt hpos_r)
    have hto_rd : ((integerSlack s (r + d)).toNat : ℤ) = integerSlack s (r + d) :=
      Int.toNat_of_nonneg (le_of_lt hpos_rd)
    have hcast :
        (((integerSlack s (r + d)).toNat +
            2 ^ (blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d : ℕ) : ℤ) =
          ((3 ^ (blockSteps (shiftSeq s r) d) * (integerSlack s r).toNat : ℕ) : ℤ) := by
      push_cast
      rw [hto_r, hto_rd]
      linarith
    exact_mod_cast hcast
  have hDr_cop6 :=
    integerSlack_toNat_coprime_six hr1 (fun k hk => hs k (by omega)) hpos_r
  have hDr_cop2 :
      Nat.Coprime (integerSlack s r).toNat (2 ^ (blockSteps s r + s r + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)))
  apply Nat.dvd_antisymm
  · have hdvd_r :
        Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat ∣
          3 ^ (blockSteps (shiftSeq s r) d) * (integerSlack s r).toNat :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
    have hdvd_rd :
        Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat ∣
          (integerSlack s (r + d)).toNat :=
      Nat.gcd_dvd_right _ _
    rw [← hnat_eq] at hdvd_r
    have hdvd_2R :
        Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat ∣
          2 ^ (blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d :=
      (Nat.dvd_add_right hdvd_rd).mp hdvd_r
    have hcop :
        Nat.Coprime
          (Nat.gcd (integerSlack s r).toNat (integerSlack s (r + d)).toNat)
          (2 ^ (blockSteps s r + s r + 1)) :=
      hDr_cop2.coprime_dvd_left (Nat.gcd_dvd_left _ _)
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (hcop.dvd_of_dvd_mul_left hdvd_2R)
  · have hdvd_r :
        Nat.gcd (integerSlack s r).toNat (coprimeRemainder (shiftSeq s r) d) ∣
          3 ^ (blockSteps (shiftSeq s r) d) * (integerSlack s r).toNat :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
    have hdvd_2R :
        Nat.gcd (integerSlack s r).toNat (coprimeRemainder (shiftSeq s r) d) ∣
          2 ^ (blockSteps s r + s r + 1) * coprimeRemainder (shiftSeq s r) d :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
    rw [← hnat_eq] at hdvd_r
    have hdvd_rd :
        Nat.gcd (integerSlack s r).toNat (coprimeRemainder (shiftSeq s r) d) ∣
          (integerSlack s (r + d)).toNat :=
      (Nat.dvd_add_left hdvd_2R).mp hdvd_r
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hdvd_rd

/-- **Pairwise Coprimality of Consecutive Integer Slacks (`consecutive_integerSlack_coprime`)**:
For any sequence `s : ℕ → ℕ` with `1 ≤ r`, `∀ k < r + 1, 1 ≤ s k`, and
`0 < integerSlack s (r + 1)`, consecutive integer slacks are coprime:
`Nat.Coprime (integerSlack s r).toNat (integerSlack s (r + 1)).toNat`. -/
theorem consecutive_integerSlack_coprime
    {s : ℕ → ℕ} {r : ℕ}
    (hr1 : 1 ≤ r) (hs : ∀ k < r + 1, 1 ≤ s k)
    (hpos : 0 < integerSlack s (r + 1)) :
    Nat.Coprime (integerSlack s r).toNat (integerSlack s (r + 1)).toNat := by
  rw [Nat.Coprime, multi_step_slack_gcd_eq_gcd_coprimeRemainder hr1 hs hpos]
  simp [coprimeRemainder, tailSteps]

/-! ## 3. Path 6: Exact 3-Adic Factorization & Valuation of Block-Boundary Orbit Values -/

/-- **Exact 3-Adic Factorization of Block-Boundary Orbit Values (`orbit_succ_eq_three_pow_mul_u`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`),
`orbit a_0 (blockSteps s (k + 1)) = 3^(s k - 1) * u k`,
and the exact 3-adic valuation of `orbit a_0 (blockSteps s (k + 1))` is `s k - 1`. -/
theorem orbit_succ_eq_three_pow_mul_u
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    orbit a_0 (blockSteps s (k + 1)) = 3 ^ (s k - 1) * u k ∧
      3 ^ (s k - 1) ∣ orbit a_0 (blockSteps s (k + 1)) ∧
      ¬ (3 ^ (s k) ∣ orbit a_0 (blockSteps s (k + 1))) := by
  have hrec := coprime_quotient_recurrence hk1 hchain
  have horb := (hchain (k + 1) hk1).2.2
  have hsk : 1 ≤ s k := (hchain k (by omega)).1
  have hpow3 : 3 ^ (s k) = 3 * 3 ^ (s k - 1) := by
    conv_lhs => rw [show s k = (s k - 1) + 1 by omega, Nat.pow_succ]
    ring
  have heq : orbit a_0 (blockSteps s (k + 1)) = 3 ^ (s k - 1) * u k := by
    rw [← horb, hpow3, mul_assoc] at hrec
    omega
  refine ⟨heq, ⟨u k, heq⟩, ?_⟩
  rw [heq, hpow3]
  rintro ⟨q, hq⟩
  have hpos : 0 < 3 ^ (s k - 1) := Nat.pow_pos (by decide)
  have hsplit : 3 * 3 ^ (s k - 1) * q = 3 ^ (s k - 1) * (3 * q) := by ring
  rw [hsplit] at hq
  have hu_eq : u k = 3 * q := Nat.eq_of_mul_eq_mul_left hpos hq
  have hu_mod3 := (u_coprime_six_of_validBlockChain (by omega : k < K) hchain).2.1
  omega

/-! ## 4. Path 6: Closed-Form 3-Adic Residue Lock & Mod-3 / Mod-9 Classifiers -/

/-- For every `n ≥ 1`, `2 * ((3^n + 1) / 2) = 3^n + 1`. -/
private theorem two_mul_three_pow_add_one_div_two (n : ℕ) :
    2 * ((3 ^ n + 1) / 2) = 3 ^ n + 1 := by
  have hodd : 3 ^ n % 2 = 1 := by
    induction n with
    | zero => rfl
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  omega

/-- For every `n` and `m`, `(2 * ((3^n + 1) / 2))^m % 3^n = 1 % 3^n`. -/
private theorem two_mul_inv_pow_mod_three_pow (n m : ℕ) :
    (2 * ((3 ^ n + 1) / 2)) ^ m % (3 ^ n) = 1 % (3 ^ n) := by
  rw [two_mul_three_pow_add_one_div_two]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
      have hmod : (3 ^ n + 1) % (3 ^ n) = 1 % (3 ^ n) := by
        rw [Nat.add_comm, Nat.add_mod_right]
      rw [hmod, ← Nat.mul_mod, mul_one]

/-- **Closed-Form 3-Adic Residue Lock (`u_succ_mod_three_pow_eq`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`),
`u (k + 1) % 3^(s k) = (((3^(s k) + 1) / 2)^(s (k + 1))) % 3^(s k)`. -/
theorem u_succ_mod_three_pow_eq
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    u (k + 1) % (3 ^ (s k)) =
      (((3 ^ (s k) + 1) / 2) ^ (s (k + 1))) % (3 ^ (s k)) := by
  have hrec := coprime_quotient_recurrence hk1 hchain
  have hsk : 1 ≤ s k := (hchain k (by omega)).1
  have h3_gt1 : 1 < 3 ^ (s k) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 3) hsk
    omega
  have h1_mod : 1 % (3 ^ (s k)) = 1 := Nat.mod_eq_of_lt h3_gt1
  have hrec_mod :
      (2 ^ (s (k + 1)) * u (k + 1)) % (3 ^ (s k)) = 1 := by
    rw [hrec, Nat.add_comm, Nat.add_mul_mod_self_left, h1_mod]
  set inv2 := (3 ^ (s k) + 1) / 2
  have hinv_pow := two_mul_inv_pow_mod_three_pow (s k) (s (k + 1))
  rw [Nat.mul_pow] at hinv_pow
  calc
    u (k + 1) % (3 ^ (s k)) =
        (1 * u (k + 1)) % (3 ^ (s k)) := by rw [one_mul]
    _ = (((2 ^ (s (k + 1)) * inv2 ^ (s (k + 1))) % (3 ^ (s k))) *
          (u (k + 1) % (3 ^ (s k)))) % (3 ^ (s k)) := by
      rw [hinv_pow, ← Nat.mul_mod, one_mul]
    _ = ((2 ^ (s (k + 1)) * inv2 ^ (s (k + 1))) * u (k + 1)) % (3 ^ (s k)) := by
      rw [← Nat.mul_mod]
    _ = ((2 ^ (s (k + 1)) * u (k + 1)) * inv2 ^ (s (k + 1))) % (3 ^ (s k)) := by
      ring_nf
    _ = (((2 ^ (s (k + 1)) * u (k + 1)) % (3 ^ (s k))) *
          (inv2 ^ (s (k + 1)) % (3 ^ (s k)))) % (3 ^ (s k)) := by
      rw [Nat.mul_mod]
    _ = inv2 ^ (s (k + 1)) % (3 ^ (s k)) := by
      rw [hrec_mod, one_mul, Nat.mod_mod]

private theorem two_pow_mod_three_eq_parity (n : ℕ) :
    2 ^ n % 3 = n % 2 + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · have hsucc : (n + 1) % 2 = 1 := by omega
        rw [h0, hsucc]
      · have hsucc : (n + 1) % 2 = 0 := by omega
        rw [h1, hsucc]

/-- **Explicit Mod-3 Parity Law and Mod-9 Primitive-Root Law (`u_succ_mod_three_and_nine_locks`)**:
Along any `ValidBlockChain a_0 s u K` (`k + 1 < K`):
1. `u (k + 1) % 3 = s (k + 1) % 2 + 1`.
2. Whenever `2 ≤ s k`, `u (k + 1) % 9 = (5^(s (k + 1))) % 9`. -/
theorem u_succ_mod_three_and_nine_locks
    {a_0 : ℕ} {s u : ℕ → ℕ} {K k : ℕ}
    (hk1 : k + 1 < K) (hchain : ValidBlockChain a_0 s u K) :
    u (k + 1) % 3 = s (k + 1) % 2 + 1 ∧
      (2 ≤ s k → u (k + 1) % 9 = (5 ^ (s (k + 1))) % 9) := by
  have hsk : 1 ≤ s k := (hchain k (by omega)).1
  have hlock := u_succ_mod_three_pow_eq hk1 hchain
  refine ⟨?_, ?_⟩
  · have h3_dvd : 3 ∣ 3 ^ (s k) := by
      have h := Nat.pow_dvd_pow 3 hsk
      simpa using h
    have hmod3 :
        u (k + 1) % 3 = (((3 ^ (s k) + 1) / 2) ^ (s (k + 1))) % 3 := by
      have h1 := Nat.mod_mod_of_dvd (u (k + 1)) h3_dvd
      have h2 :=
        Nat.mod_mod_of_dvd (((3 ^ (s k) + 1) / 2) ^ (s (k + 1))) h3_dvd
      rw [← h1, hlock, h2]
    have hinv_mod3 : ((3 ^ (s k) + 1) / 2) % 3 = 2 := by
      have htwo := two_mul_three_pow_add_one_div_two (s k)
      rcases h3_dvd with ⟨q, hq⟩
      omega
    rw [hmod3, Nat.pow_mod, hinv_mod3, two_pow_mod_three_eq_parity]
  · intro hsk2
    have h9_dvd : 9 ∣ 3 ^ (s k) := by
      have h := Nat.pow_dvd_pow 3 hsk2
      simpa using h
    have hmod9 :
        u (k + 1) % 9 = (((3 ^ (s k) + 1) / 2) ^ (s (k + 1))) % 9 := by
      have h1 := Nat.mod_mod_of_dvd (u (k + 1)) h9_dvd
      have h2 :=
        Nat.mod_mod_of_dvd (((3 ^ (s k) + 1) / 2) ^ (s (k + 1))) h9_dvd
      rw [← h1, hlock, h2]
    have hinv_mod9 : ((3 ^ (s k) + 1) / 2) % 9 = 5 := by
      have htwo := two_mul_three_pow_add_one_div_two (s k)
      rcases h9_dvd with ⟨q, hq⟩
      omega
    rw [hmod9, Nat.pow_mod, hinv_mod9]

end Mahler.ThreeAdicSeedLocks
