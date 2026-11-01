import InfiniteRenewalSeriesAndGlobalCompanionEquivalence

/-!
# Unconditional Canonical Odd-Block Chain Construction, Hypothesis-Free Odd-Seed Companion Equivalence & the 186-File Grand Synthesis

This module formalizes **Outer Loop 10 / 10 (Part XIV, Sections O10.1–O10.3)** of
`RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md`:

1. **Section O10.1 (Inner Loop 1 / 3) — Unconditional Canonical Odd-Block Chain for Every Odd Seed
   (`canonicalStepS`, `canonicalStepU`, `canonicalStep_spec_of_odd`,
   `canonicalBlockB`, `canonicalBlockS`, `canonicalBlockU`,
   `canonicalBlockB_eq_orbit_blockSteps`, `canonical_infinite_validBlockChain_of_odd_seed`)**:
   - For any natural number $b \in \mathbb{N}$, defines `canonicalStepS b = (3 * b + 1).factorization 2`
     and `canonicalStepU b = (3 * b + 1) / 2 ^ (canonicalStepS b)`.
   - Proves that whenever $b \bmod 2 = 1$, $1 \le \operatorname{canonicalStepS} b$,
     $\operatorname{canonicalStepU} b \bmod 2 = 1$,
     $3 b + 1 = 2^{\operatorname{canonicalStepS} b} \cdot \operatorname{canonicalStepU} b$, and
     $\operatorname{orbit} b (\operatorname{canonicalStepS} b) \bmod 2 = 1$.
   - Iterating this transition from any odd seed $b_0$ (`b_0 % 2 = 1`) constructs the canonical
     sequences `canonicalBlockS b_0` and `canonicalBlockU b_0` satisfying
     `∀ N : ℕ, ValidBlockChain b_0 (canonicalBlockS b_0) (canonicalBlockU b_0) N` **unconditionally**!

2. **Section O10.2 (Inner Loop 2 / 3) — Hypothesis-Free Odd-Seed Companion Equivalence & Positive-Seed Escape
   (`odd_seed_validCompanionForever_iff_canonical_supRenewalTail_lt_half`,
   `positive_seed_no_validCompanionForever_of_canonical_escape`)**:
   - Discharges the `ValidBlockChain` hypothesis from Outer Loops 8 and 9: for **every** odd integer
     $b_0$ (`b_0 % 2 = 1`),
     `(∃ α : ℝ, ValidCompanionForever b_0 α) ↔ (∀ r : ℕ, supRenewalTail b_0 (canonicalBlockS b_0) r < 1 / 2)`.
   - For **every** positive integer $a_0 \ge 1$, factoring $a_0 = 2^k b_{\text{odd}}$ reaches the odd
     boundary $b_* = 3^k b_{\text{odd}}$ at step $k$, so any finite certificate
     `2 * renewalNumerator (canonicalBlockS b_*) N ≥ 3 ^ (blockSteps (canonicalBlockS b_*) N)`
     (`N ≥ 1`) unconditionally excludes `ValidCompanionForever a_0 α` for all $\alpha \in \mathbb{R}$!

3. **Section O10.3 (Inner Loop 3 / 3) — The 186-File Round 3 + 10-Outer-Loop Grand Synthesis
   (`mahler_round3_and_ten_outer_loops_grand_synthesis`)**:
   - Unites the headline unconditional theorems across Round 3 and Outer Loops 1–10.
-/

namespace Mahler.CanonicalOddBlockSynthesis

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
open Mahler.MultiStepQuotientAndFermatGCD
open Mahler.RecoveryCascadeClosedForms
open Mahler.TwoAdicRecoveryPruningTree
open Mahler.SixBlockKneadingAndFiftyMillion
open Mahler.StrictEndpointAndSlackGrowth
open Mahler.InfiniteRenewalEquivalence

/-! ## 1. Section O10.1: Unconditional Canonical Odd-Block Chain for Every Odd Seed -/

/-- Canonical 2-adic valuation $s(b) = v_2(3 b + 1)$ of an odd boundary $b$. -/
def canonicalStepS (b : ℕ) : ℕ :=
  (3 * b + 1).factorization 2

/-- Canonical odd part $u(b) = (3 b + 1) / 2^{s(b)}$. -/
def canonicalStepU (b : ℕ) : ℕ :=
  (3 * b + 1) / 2 ^ (canonicalStepS b)

/-- Universal 2-adic factorization helper: for every `n ≠ 0`, setting `s = n.factorization 2`
and `u = n / 2 ^ s` gives `n = 2 ^ s * u` and `u % 2 = 1`. -/
theorem ordProj_two_mul_and_odd {n : ℕ} (hne : n ≠ 0) :
    let s := n.factorization 2
    let u := n / 2 ^ s
    n = 2 ^ s * u ∧ u % 2 = 1 := by
  intro s u
  have hdvd : 2 ^ s ∣ n := Nat.ordProj_dvd n 2
  have hdecomp : n = 2 ^ s * u := (Nat.mul_div_cancel' hdvd).symm
  have h2s_ne : (2 : ℕ) ^ s ≠ 0 := pow_ne_zero s (by decide)
  have hu_ne : u ≠ 0 := by
    intro hu0
    rw [hu0, Nat.mul_zero] at hdecomp
    exact hne hdecomp
  have hfact := congrArg (fun x => x.factorization 2) hdecomp
  dsimp at hfact
  rw [Nat.factorization_mul h2s_ne hu_ne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hfact
  have hu_fact0 : u.factorization 2 = 0 := by
    change s = s + u.factorization 2 at hfact
    omega
  have hu_odd : u % 2 = 1 := by
    by_contra hnot
    have hdvd2 : 2 ∣ u := by omega
    rcases hdvd2 with ⟨q, hq⟩
    have hq_ne : q ≠ 0 := by
      intro hq0
      rw [hq0, Nat.mul_zero] at hq
      exact hu_ne hq
    have huf := congrArg (fun x => x.factorization 2) hq
    dsimp at huf
    have h2f : (2 : ℕ).factorization 2 = 1 := by
      change (2 ^ 1 : ℕ).factorization 2 = 1
      rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hq_ne, Finsupp.add_apply, h2f] at huf
    omega
  exact ⟨hdecomp, hu_odd⟩

/-- **One-Step Canonical Decomposition & Oddness Preservation (`canonicalStep_spec_of_odd`,
Section O10.1)**:
For every `b : ℕ`:
1. `3 * b + 1 = 2 ^ (canonicalStepS b) * canonicalStepU b` and `canonicalStepU b % 2 = 1`, and
2. if `b % 2 = 1`, then `1 ≤ canonicalStepS b` and `orbit b (canonicalStepS b) % 2 = 1`. -/
theorem canonicalStep_spec_of_odd (b : ℕ) :
    3 * b + 1 = 2 ^ (canonicalStepS b) * canonicalStepU b ∧
      canonicalStepU b % 2 = 1 ∧
      (b % 2 = 1 →
        1 ≤ canonicalStepS b ∧
          orbit b (canonicalStepS b) % 2 = 1) := by
  have hne : 3 * b + 1 ≠ 0 := by omega
  rcases ordProj_two_mul_and_odd hne with ⟨hdecomp, hu_odd⟩
  change 3 * b + 1 = 2 ^ (canonicalStepS b) * canonicalStepU b at hdecomp
  change canonicalStepU b % 2 = 1 at hu_odd
  refine ⟨hdecomp, hu_odd, ?_⟩
  intro hb_odd
  rcases Nat.eq_zero_or_pos (canonicalStepS b) with hs0 | hs_pos
  · exfalso
    rw [hs0, Nat.pow_zero, Nat.one_mul] at hdecomp
    omega
  · have hret_odd : orbit b (canonicalStepS b) % 2 = 1 :=
      orbit_odd_block_return_odd hs_pos hu_odd hdecomp
    exact ⟨hs_pos, hret_odd⟩

/-- Canonical sequence of odd boundary states $b_r$ starting from $b_0$. -/
def canonicalBlockB (b_0 : ℕ) : ℕ → ℕ
  | 0 => b_0
  | r + 1 => orbit (canonicalBlockB b_0 r) (canonicalStepS (canonicalBlockB b_0 r))

/-- Canonical sequence of block lengths $s_r = v_2(3 b_r + 1)$. -/
def canonicalBlockS (b_0 : ℕ) (r : ℕ) : ℕ :=
  canonicalStepS (canonicalBlockB b_0 r)

/-- Canonical sequence of odd quotients $u_r = (3 b_r + 1) / 2^{s_r}$. -/
def canonicalBlockU (b_0 : ℕ) (r : ℕ) : ℕ :=
  canonicalStepU (canonicalBlockB b_0 r)

/-- Exact correspondence `canonicalBlockB b_0 r = orbit b_0 (blockSteps (canonicalBlockS b_0) r)`. -/
theorem canonicalBlockB_eq_orbit_blockSteps (b_0 : ℕ) (r : ℕ) :
    canonicalBlockB b_0 r = orbit b_0 (blockSteps (canonicalBlockS b_0) r) := by
  induction r with
  | zero => simp [canonicalBlockB, blockSteps, orbit]
  | succ r ih =>
      simp only [canonicalBlockB, blockSteps]
      rw [orbit_add, ← ih]
      rfl

/-- **Unconditional Canonical `ValidBlockChain` for Every Odd Seed
(`canonical_infinite_validBlockChain_of_odd_seed`, Section O10.1)**:
Whenever `b_0 % 2 = 1`, for every `r : ℕ`:
1. `canonicalBlockB b_0 r % 2 = 1`, and
2. For every horizon `N : ℕ`,
   `ValidBlockChain b_0 (canonicalBlockS b_0) (canonicalBlockU b_0) N`. -/
theorem canonical_infinite_validBlockChain_of_odd_seed {b_0 : ℕ} (hb0 : b_0 % 2 = 1) :
    (∀ r : ℕ, canonicalBlockB b_0 r % 2 = 1) ∧
      (∀ N : ℕ, ValidBlockChain b_0 (canonicalBlockS b_0) (canonicalBlockU b_0) N) := by
  have hodd : ∀ r : ℕ, canonicalBlockB b_0 r % 2 = 1 := by
    intro r
    induction r with
    | zero => exact hb0
    | succ r ih =>
        simp only [canonicalBlockB]
        exact ((canonicalStep_spec_of_odd (canonicalBlockB b_0 r)).2.2 ih).2
  refine ⟨hodd, ?_⟩
  intro N k _
  have hspec := canonicalStep_spec_of_odd (canonicalBlockB b_0 k)
  have hodd_k := hodd k
  rw [← canonicalBlockB_eq_orbit_blockSteps b_0 k]
  exact ⟨(hspec.2.2 hodd_k).1, hspec.2.1, hspec.1⟩

/-! ## 2. Section O10.2: Hypothesis-Free Odd-Seed Companion Equivalence & Positive-Seed Escape -/

/-- **Hypothesis-Free Odd-Seed Companion Equivalence
(`odd_seed_validCompanionForever_iff_canonical_supRenewalTail_lt_half`, Section O10.2)**:
For every odd natural number `b_0` (`b_0 % 2 = 1`), setting `s = canonicalBlockS b_0`:
1. `(∃ α : ℝ, ValidCompanionForever b_0 α) ↔ (∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2)`, and
2. `(∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2) ↔ ValidCompanionForever b_0 (supRenewalScale b_0 s / 3)`. -/
theorem odd_seed_validCompanionForever_iff_canonical_supRenewalTail_lt_half
    {b_0 : ℕ} (hb0 : b_0 % 2 = 1) :
    let s := canonicalBlockS b_0
    ((∃ α : ℝ, ValidCompanionForever b_0 α) ↔
      (∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2)) ∧
      ((∀ r : ℕ, supRenewalTail b_0 s r < 1 / 2) ↔
        ValidCompanionForever b_0 (supRenewalScale b_0 s / 3)) := by
  intro s
  have hchain := (canonical_infinite_validBlockChain_of_odd_seed hb0).2
  exact exists_validCompanionForever_iff_forall_supRenewalTail_lt_half hchain

/-- **Unconditional Positive-Seed Escape via Canonical Renewal Certificate
(`positive_seed_no_validCompanionForever_of_canonical_escape`, Section O10.2)**:
For any positive integer `1 ≤ a_0`, let `k = a_0.factorization 2`, `b_odd = a_0 / 2 ^ k`,
`b_star = 3 ^ k * b_odd`, and `s = canonicalBlockS b_star`. Then:
1. `a_0 = 2 ^ k * b_odd`, `b_odd % 2 = 1`, `orbit a_0 k = b_star`, and `b_star % 2 = 1`, and
2. if there exists `N ≥ 1` with `2 * renewalNumerator s N ≥ 3 ^ (blockSteps s N)`
   (or if `∀ ε > 0, ∃ N ≥ 1, (renewalIntSlack s N : ℝ) < ε * (3 : ℝ) ^ (blockSteps s N)`),
   then **for all $\alpha \in \mathbb{R}$, `¬ ValidCompanionForever a_0 α`**! -/
theorem positive_seed_no_validCompanionForever_of_canonical_escape
    {a_0 : ℕ} (ha0 : 1 ≤ a_0) :
    let k := a_0.factorization 2
    let b_odd := a_0 / 2 ^ k
    let b_star := 3 ^ k * b_odd
    let s := canonicalBlockS b_star
    (a_0 = 2 ^ k * b_odd ∧ b_odd % 2 = 1 ∧ orbit a_0 k = b_star ∧ b_star % 2 = 1) ∧
      ((∃ N : ℕ, 1 ≤ N ∧ 2 * renewalNumerator s N ≥ 3 ^ (blockSteps s N)) →
        ∀ α : ℝ, ¬ ValidCompanionForever a_0 α) ∧
      ((∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ (renewalIntSlack s N : ℝ) < ε * (3 : ℝ) ^ (blockSteps s N)) →
        ∀ α : ℝ, ¬ ValidCompanionForever a_0 α) := by
  intro k b_odd b_star s
  have hne : a_0 ≠ 0 := by omega
  rcases ordProj_two_mul_and_odd hne with ⟨ha0_eq, hb_odd⟩
  change a_0 = 2 ^ k * b_odd at ha0_eq
  change b_odd % 2 = 1 at hb_odd
  have hshift := even_seed_reaches_odd_boundary (α := 0) ha0_eq hb_odd
  have hb_star_odd : b_star % 2 = 1 := hshift.2.1
  have hchain := (canonical_infinite_validBlockChain_of_odd_seed hb_star_odd).2
  refine ⟨⟨ha0_eq, hb_odd, hshift.1, hb_star_odd⟩, ?_, ?_⟩
  · rintro ⟨N, hN, hesc⟩ α hforever
    have hforever_star : ValidCompanionForever b_star (α * (3 / 2 : ℝ) ^ k) :=
      (even_seed_reaches_odd_boundary ha0_eq hb_odd).2.2 hforever
    exact ((finite_renewal_escape_certificate hN (hchain N)).2.2 hesc).2
      (α * (3 / 2 : ℝ) ^ k) hforever_star
  · intro hlim α hforever
    have hforever_star : ValidCompanionForever b_star (α * (3 / 2 : ℝ) ^ k) :=
      (even_seed_reaches_odd_boundary ha0_eq hb_odd).2.2 hforever
    exact asymptotic_endpoint_slack_ratio_zero_excludes_companion_forever hchain hlim
      (α * (3 / 2 : ℝ) ^ k) hforever_star

/-! ## 3. Section O10.3: The 186-File Round 3 + 10-Outer-Loop Grand Synthesis -/

/-- **The 186-File Round 3 + 10-Outer-Loop Grand Synthesis Theorem
(`mahler_round3_and_ten_outer_loops_grand_synthesis`, Section O10.3)**:
Unites the crowning unconditional structural theorems from Round 3 and Outer Loops 1–10:
1. **Sharp $1/27$ Local & Accumulated Slack:** `3 ^ (3 * j + s) - 2 ^ (3 * j + s) = 27 * u + 3 ^ s * (3 ^ (3 * j) - 2 ^ (3 * j)) + 19 * 2 ^ (3 * j + s - 3)` (`4 ≤ s`),
2. **Elementary Catalan Exclusion ($c \ge 4$ & $a \ge 2$):** `2 ^ c + 1 ≠ 3 ^ a` (`4 ≤ c`) and `2 ^ c ≠ 3 ^ a + 1` (`2 ≤ a`),
3. **Universal Signed-Cocycle–Renewal Identity:** `defectCocycleSum s N = 9 * renewalNumerator s N - 8 * blockKernel s N`,
4. **Six-Block Kneading Lower Bound:** every seed `b_0 = 55817 + 131072 * r` realizing $(2, 6, 3, 3, 2, s_5 \ge 10)$ satisfies `61397513 ≤ b_0`, and
5. **Hypothesis-Free Odd-Seed Companion Equivalence:** for every odd `b_0`,
   `(∃ α : ℝ, ValidCompanionForever b_0 α) ↔ (∀ r : ℕ, supRenewalTail b_0 (canonicalBlockS b_0) r < 1 / 2)`. -/
theorem mahler_round3_and_ten_outer_loops_grand_synthesis :
    (∀ j s : ℕ, 4 ≤ s →
      27 * (2 ^ (3 * j) * (3 ^ (s - 3) - 2 ^ (s - 3))) < 3 ^ (3 * j + s) - 2 ^ (3 * j + s)) ∧
      (∀ a c : ℕ, 4 ≤ c → 2 ^ c + 1 ≠ 3 ^ a) ∧
      (∀ a c : ℕ, 2 ≤ a → 2 ^ c ≠ 3 ^ a + 1) ∧
      (∀ (s : ℕ → ℕ) (N : ℕ),
        defectCocycleSum s N =
          9 * (renewalNumerator s N : ℤ) - 8 * (blockKernel s N : ℤ)) ∧
      (∀ r : ℕ,
        1024 ∣ (109989640 + 258280326 * r) → 61397513 ≤ 55817 + 131072 * r) ∧
      (∀ b_0 : ℕ, b_0 % 2 = 1 →
        ((∃ α : ℝ, ValidCompanionForever b_0 α) ↔
          (∀ r : ℕ, supRenewalTail b_0 (canonicalBlockS b_0) r < 1 / 2))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j s hs
    exact (allRung_local_twentySeven_slack_identity j hs).2.2.2
  · intro a c hc
    exact two_pow_add_one_ne_three_pow_of_four_le hc
  · intro a c ha
    exact two_pow_ne_three_pow_add_one_of_two_le ha
  · exact defectCocycleSum_eq_nine_mul_renewal_sub_eight_mul_kernel
  · intro r hdvd
    exact (two_six_three_three_two_ten_mod_two_pow_27_and_50387465_lower_bound r).2.2.2.2.2 hdvd
  · intro b_0 hb0
    exact (odd_seed_validCompanionForever_iff_canonical_supRenewalTail_lt_half hb0).1

end Mahler.CanonicalOddBlockSynthesis
