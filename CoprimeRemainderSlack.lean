import ModEightPhaseClassifier

/-!
# The Coprime Remainder Polynomial, Unconditional `u_0` Recovery, and the `a_0`-Free Slack Law

This module formalizes the multi-step elimination of the coprime quotient
recurrence `2^(s (k + 1)) * u (k + 1) = 3^(s k) * u k + 1`:

1. **The Coprime Remainder Polynomial `coprimeRemainder s m` (`coprime_quotient_m_step_identity`)**:
   Define `tailSteps s m = s 1 + ... + s m` and
   - `coprimeRemainder s 0 = 0`,
   - `coprimeRemainder s (m + 1) = 3^(s m) * coprimeRemainder s m + 2^(tailSteps s m)`.
   Across `m` transitions (`m < K`) of any valid block chain `ValidBlockChain a_0 s u K`,
   `2^(tailSteps s m) * u m = 3^(blockSteps s m) * u 0 + coprimeRemainder s m`.
2. **Unconditional Bound & Recovery of `u 0` and `R(s, m)`
   (`coprimeRemainder_lt_three_pow`, `unconditional_u0_div_recovery`,
   `unconditional_coprimeRemainder_mod_recovery`)**:
   Whenever `1 ≤ s k` for all `k < m` (`1 ≤ m`),
   `coprimeRemainder s m + 2 * 2^(tailSteps s (m - 1)) ≤ 3^(blockSteps s m)`.
   Thus `coprimeRemainder s m < 3^(blockSteps s m)` holds **unconditionally**
   (without any real-companion or `IntegerPinch` hypothesis!), so at every
   block `m ≥ 1`:
   - `(2^(tailSteps s m) * u m) / 3^(blockSteps s m) = u 0`, and
   - `(2^(tailSteps s m) * u m) % 3^(blockSteps s m) = coprimeRemainder s m`.
3. **The Exact `a_0`-Free Slack Identity & Tail Budget Inequality
   (`archimedean_slack_addition_identity`, `tail_budget_iff_archimedean_cap`,
   `tail_budget_of_validCompanionUpTo`)**:
   Using `2^(s 0 + 1) * u 0 + 1 = 3 * (2 * a_0 + 1)`, we obtain the exact
   subtraction-free identity in `ℕ`:
   `2^(blockSteps s (m + 1) + 1) * u m + 3^(blockSteps s m) =
     3^(blockSteps s m + 1) * (2 * a_0 + 1) + 2^(s 0 + 1) * coprimeRemainder s m`.
   Consequently, the Archimedean half-corridor bound at block `m` is equivalent
   to the purely block-determined tail budget inequality
   `2^(s 0 + 1) * coprimeRemainder s m < 3^(blockSteps s m)`.
-/

namespace Mahler.CoprimeSlack

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

/-! ## 1. `tailSteps`, `coprimeRemainder`, and the `m`-Step Quotient Identity -/

/-- Sum of block lengths `s 1 + s 2 + ... + s m`. -/
def tailSteps (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => tailSteps s m + s (m + 1)

theorem add_tailSteps_eq_blockSteps_succ (s : ℕ → ℕ) (m : ℕ) :
    s 0 + tailSteps s m = blockSteps s (m + 1) := by
  induction m with
  | zero => simp [tailSteps, blockSteps]
  | succ m ih =>
      change s 0 + (tailSteps s m + s (m + 1)) = blockSteps s (m + 1) + s (m + 1)
      omega

/-- The multi-step coprime remainder polynomial `R(s, m)`. -/
def coprimeRemainder (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 3 ^ (s m) * coprimeRemainder s m + 2 ^ (tailSteps s m)

/-- **The `m`-Step Coprime Quotient Identity (`coprime_quotient_m_step_identity`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` with `m < K`,
`2^(tailSteps s m) * u m = 3^(blockSteps s m) * u 0 + coprimeRemainder s m`. -/
theorem coprime_quotient_m_step_identity {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (tailSteps s m) * u m =
      3 ^ (blockSteps s m) * u 0 + coprimeRemainder s m := by
  induction m with
  | zero => simp [tailSteps, blockSteps, coprimeRemainder]
  | succ m ih =>
      have ihm := ih (by omega)
      have hrec := coprime_quotient_recurrence hm hchain
      calc
        2 ^ (tailSteps s (m + 1)) * u (m + 1) =
            2 ^ (tailSteps s m) * (2 ^ (s (m + 1)) * u (m + 1)) := by
              simp only [tailSteps, Nat.pow_add]
              ring
        _ = 2 ^ (tailSteps s m) * (3 ^ (s m) * u m + 1) := by rw [hrec]
        _ = 3 ^ (s m) * (2 ^ (tailSteps s m) * u m) + 2 ^ (tailSteps s m) := by ring
        _ = 3 ^ (s m) * (3 ^ (blockSteps s m) * u 0 + coprimeRemainder s m) +
              2 ^ (tailSteps s m) := by rw [ihm]
        _ = 3 ^ (blockSteps s (m + 1)) * u 0 + coprimeRemainder s (m + 1) := by
              simp only [blockSteps, coprimeRemainder, Nat.pow_add]
              ring

/-! ## 2. Unconditional Upper Bound and Recovery of `u 0` and `R(s, m)` -/

private theorem three_mul_two_pow_le_two_mul_three_pow {n : ℕ} (hn : 1 ≤ n) :
    3 * 2 ^ n ≤ 2 * 3 ^ n := by
  have hsub : n = (n - 1) + 1 := by omega
  have h23 : 2 ^ (n - 1) ≤ 3 ^ (n - 1) := Nat.pow_le_pow_left (by decide) (n - 1)
  have h6 : 6 * 2 ^ (n - 1) ≤ 6 * 3 ^ (n - 1) := Nat.mul_le_mul_left 6 h23
  calc
    3 * 2 ^ n = 6 * 2 ^ (n - 1) := by
      conv_lhs => rw [hsub, Nat.pow_succ]
      ring
    _ ≤ 6 * 3 ^ (n - 1) := h6
    _ = 2 * 3 ^ n := by
      conv_rhs => rw [hsub, Nat.pow_succ]
      ring

/-- Unconditional inductive bound: for any `m ≥ 1` with `1 ≤ s k` (`k < m`),
`coprimeRemainder s m + 2 * 2^(tailSteps s (m - 1)) ≤ 3^(blockSteps s m)`. -/
theorem coprimeRemainder_add_two_pow_le {s : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hs : ∀ k < m, 1 ≤ s k) :
    coprimeRemainder s m + 2 * 2 ^ (tailSteps s (m - 1)) ≤
      3 ^ (blockSteps s m) := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          have hs0 : 1 ≤ s 0 := hs 0 (by omega)
          have h3 : 3 ^ 1 ≤ 3 ^ (s 0) := Nat.pow_le_pow_right (by decide) hs0
          simpa [coprimeRemainder, tailSteps, blockSteps] using h3
      | succ m =>
          have ihm := ih (by omega) (fun k hk => hs k (by omega))
          have hsm : 1 ≤ s (m + 1) := hs (m + 1) (by omega)
          have hstep := three_mul_two_pow_le_two_mul_three_pow hsm
          have htail :
              tailSteps s (m + 1) = tailSteps s m + s (m + 1) := rfl
          calc
            coprimeRemainder s (m + 2) + 2 * 2 ^ (tailSteps s (m + 1)) =
                3 ^ (s (m + 1)) * coprimeRemainder s (m + 1) +
                  3 * 2 ^ (tailSteps s (m + 1)) := by
                  simp only [coprimeRemainder]
                  ring
            _ = 3 ^ (s (m + 1)) * coprimeRemainder s (m + 1) +
                  2 ^ (tailSteps s m) * (3 * 2 ^ (s (m + 1))) := by
                  rw [htail, Nat.pow_add]
                  ring
            _ ≤ 3 ^ (s (m + 1)) * coprimeRemainder s (m + 1) +
                  2 ^ (tailSteps s m) * (2 * 3 ^ (s (m + 1))) :=
                  Nat.add_le_add_left
                    (Nat.mul_le_mul_left (2 ^ (tailSteps s m)) hstep) _
            _ = 3 ^ (s (m + 1)) *
                  (coprimeRemainder s (m + 1) + 2 * 2 ^ (tailSteps s m)) := by ring
            _ ≤ 3 ^ (s (m + 1)) * 3 ^ (blockSteps s (m + 1)) :=
                  Nat.mul_le_mul_left (3 ^ (s (m + 1))) ihm
            _ = 3 ^ (blockSteps s (m + 2)) := by
                  simp only [blockSteps, Nat.pow_add]
                  ring

/-- Unconditional strict bound `coprimeRemainder s m < 3^(blockSteps s m)` for `m ≥ 1`. -/
theorem coprimeRemainder_lt_three_pow {s : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hs : ∀ k < m, 1 ≤ s k) :
    coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  have hle := coprimeRemainder_add_two_pow_le hm hs
  have hpos : 0 < 2 ^ (tailSteps s (m - 1)) := Nat.pow_pos (by decide)
  omega

/-- **Unconditional Quotient & Remainder Recovery (`unconditional_u0_div_mod_recovery`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` with `1 ≤ m < K`
(with no real companion or `IntegerPinch` assumption!), dividing
`2^(tailSteps s m) * u m` by `3^(blockSteps s m)` recovers quotient `u 0`
and remainder `coprimeRemainder s m`. -/
theorem unconditional_u0_div_mod_recovery {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hm1 : 1 ≤ m) (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    (2 ^ (tailSteps s m) * u m) / 3 ^ (blockSteps s m) = u 0 ∧
      (2 ^ (tailSteps s m) * u m) % 3 ^ (blockSteps s m) = coprimeRemainder s m := by
  have hid := coprime_quotient_m_step_identity hmK hchain
  have hlt : coprimeRemainder s m < 3 ^ (blockSteps s m) :=
    coprimeRemainder_lt_three_pow hm1 (fun k hk => (hchain k (by omega)).1)
  have hpos : 0 < 3 ^ (blockSteps s m) := Nat.pow_pos (by decide)
  have hdiv : (2 ^ (tailSteps s m) * u m) / 3 ^ (blockSteps s m) = u 0 := by
    apply Nat.le_antisymm
    · have hhi : 2 ^ (tailSteps s m) * u m < (u 0 + 1) * 3 ^ (blockSteps s m) := by
        rw [hid]
        have : (u 0 + 1) * 3 ^ (blockSteps s m) =
            3 ^ (blockSteps s m) * u 0 + 3 ^ (blockSteps s m) := by ring
        omega
      exact (Nat.div_lt_iff_lt_mul hpos).mpr hhi |> Nat.le_of_lt_succ
    · have hlo : u 0 * 3 ^ (blockSteps s m) ≤ 2 ^ (tailSteps s m) * u m := by
        rw [hid]
        have : u 0 * 3 ^ (blockSteps s m) = 3 ^ (blockSteps s m) * u 0 := by ring
        omega
      exact (Nat.le_div_iff_mul_le hpos).mpr hlo
  have hdm := Nat.div_add_mod (2 ^ (tailSteps s m) * u m) (3 ^ (blockSteps s m))
  rw [hdiv] at hdm
  exact ⟨hdiv, by omega⟩

/-! ## 3. The Exact `a_0`-Free Slack Identity & Tail Budget Inequality -/

/-- **Subtraction-Free Archimedean Slack Identity (`archimedean_slack_addition_identity`)**:
Along any valid block chain `ValidBlockChain a_0 s u K` with `m < K`,
`2^(blockSteps s (m + 1) + 1) * u m + 3^(blockSteps s m) =
  3^(blockSteps s m + 1) * (2 * a_0 + 1) + 2^(s 0 + 1) * coprimeRemainder s m`. -/
theorem archimedean_slack_addition_identity {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (blockSteps s (m + 1) + 1) * u m + 3 ^ (blockSteps s m) =
      3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) +
        2 ^ (s 0 + 1) * coprimeRemainder s m := by
  have hid := coprime_quotient_m_step_identity hmK hchain
  have h0_pos : 0 < K := by omega
  rcases hchain 0 h0_pos with ⟨_, _, hdecomp0⟩
  simp only [blockSteps, orbit] at hdecomp0
  have hu0 : 2 ^ (s 0 + 1) * u 0 + 1 = 3 * (2 * a_0 + 1) := by
    rw [Nat.pow_succ]
    have : 2 ^ (s 0) * 2 * u 0 = 2 * (2 ^ (s 0) * u 0) := by ring
    rw [this, ← hdecomp0]
    ring
  have hsteps : s 0 + 1 + tailSteps s m = blockSteps s (m + 1) + 1 := by
    have h := add_tailSteps_eq_blockSteps_succ s m
    omega
  calc
    2 ^ (blockSteps s (m + 1) + 1) * u m + 3 ^ (blockSteps s m) =
        2 ^ (s 0 + 1) * (2 ^ (tailSteps s m) * u m) + 3 ^ (blockSteps s m) := by
          rw [← hsteps, Nat.pow_add]
          ring
    _ = 2 ^ (s 0 + 1) * (3 ^ (blockSteps s m) * u 0 + coprimeRemainder s m) +
          3 ^ (blockSteps s m) := by rw [hid]
    _ = 3 ^ (blockSteps s m) * (2 ^ (s 0 + 1) * u 0 + 1) +
          2 ^ (s 0 + 1) * coprimeRemainder s m := by ring
    _ = 3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) +
          2 ^ (s 0 + 1) * coprimeRemainder s m := by
          rw [hu0, Nat.pow_succ]
          ring

/-- Equivalence between the Archimedean cap `2^(T(m+1) + 1) * u m < 3^(T(m) + 1) * (2 a_0 + 1)`
and the `a_0`-free tail budget inequality `2^(s 0 + 1) * coprimeRemainder s m < 3^(blockSteps s m)`. -/
theorem tail_budget_iff_archimedean_cap {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) :
    2 ^ (blockSteps s (m + 1) + 1) * u m <
        3 ^ (blockSteps s m + 1) * (2 * a_0 + 1) ↔
      2 ^ (s 0 + 1) * coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  have hslack := archimedean_slack_addition_identity hmK hchain
  omega

/-- **The `a_0`-Free Tail Budget Theorem (`tail_budget_of_validCompanionUpTo`)**:
If `ValidBlockChain a_0 s u K` holds (`m < K`) and `a_0` survives through step
`blockSteps s (m + 1)`, then the block lengths `s` must satisfy the purely
combinatorial tail budget inequality:
`2^(s 0 + 1) * coprimeRemainder s m < 3^(blockSteps s m)`. -/
theorem tail_budget_of_validCompanionUpTo {a_0 : ℕ} {s u : ℕ → ℕ} {K m : ℕ}
    (hmK : m < K) (hchain : ValidBlockChain a_0 s u K) {ξ : ℝ}
    (hsurv : ValidCompanionUpTo a_0 ξ (blockSteps s m + s m)) :
    2 ^ (s 0 + 1) * coprimeRemainder s m < 3 ^ (blockSteps s m) := by
  have hcap := (block_length_archimedean_cap hmK hchain hsurv).1
  exact (tail_budget_iff_archimedean_cap hmK hchain).mp hcap

end Mahler.CoprimeSlack
