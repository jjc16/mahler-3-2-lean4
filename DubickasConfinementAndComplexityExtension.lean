import ThueMorseMahlerFunctionalEquation
import SparseDefectCocycleAndValuationLock

/-!
# Quantitative Extensions of Dubickas (2008 / 2009): Shifted Carry Words, Sharp Sub-Critical Complexity & Explicit $O(\log \xi)$ Confinement Escape Bounds

This module extends the interval- and union-confinement relaxations of Mahler's $3/2$
problem introduced by Artūras Dubickas (*Math. Nachr.* **281** (2008), 951–958;
*Acta Arith.* **137** (2009), 233–239, received March 2008):

1. **Shifted Carry Words $s_n = 2 x_{n+1} - 3 x_n$, Multi-Step Summation & Finite-Horizon Divisibility
   (`dubX`, `dubY`, `dubCarry`, `dubCarry_eq_fract_linear`, `dubCarryAcc`,
   `dubX_multi_step_carry_identity`, `dubY_multi_step_carry_identity`,
   `dubX_repeat_factor_cancellation`, `dubX_strict_step_growth`,
   `dubX_repeated_window_exp_bound`, `dubX_repeated_window_pq_cutoff`)**:
   - For any real $\xi > 0$ and shift $\theta \in \mathbb{R}$, defines
     $x_n = \lfloor \xi (3/2)^n + \theta \rfloor$, $y_n = \{\xi (3/2)^n + \theta\}$,
     and the shifted carry word $s_n = 2 x_{n+1} - 3 x_n = 3 y_n - 2 y_{n+1} - \theta \in \mathbb{Z}$.
   - Proves the exact multi-step identities:
     $$2^L x_{n+L} = 3^L x_n + \operatorname{dubCarryAcc}(s, n, L),$$
     $$2^L y_{n+L} = 3^L y_n - \operatorname{dubCarryAcc}(s, n, L) - (3^L - 2^L)\theta.$$
   - Proves that whenever a length-$L$ factor of $s_n$ repeats at $2 \le i < j$ for
     $\xi \in [1, 2^W)$ and $\theta \in [-1, 0]$, the carry accumulator cancels identically,
     forcing $2^L \mid (x_j - x_i)$, $1 \le x_j - x_i$, and the **explicit finite-horizon
     exponential and $(p, q)$ bounds**:
     $$2^{L + j} < 3^j \cdot 2^W, \qquad q L + 1 \le p j + q W \quad (\text{whenever } 3^q < 2^{p+q}).$$

2. **Strengthening Dubickas's Sturmian Carry Endgame ($\kappa = 1$) to the Sharp Threshold
   $\kappa < \log 2 / \log(3/2) \approx 1.709511$ (`dubCarryNat`,
   `dubCarry_subcritical_pq_finite_cutoff`,
   `no_subcritical_log_threshold_dubCarry`)**:
   - Upgrades Dubickas's Sturmian carry-word contradiction ($\kappa = 1$) to **every**
     complexity slope $\kappa$ satisfying $\kappa \log(3/2) < \log 2$, proving both explicit
     finite-horizon cutoffs and infinite-horizon impossibility for any $\xi > 0$ and $\theta \in [-1, 0]$.

3. **Shifted $1/3$-Windows $[s, s + 1/3]$ ($s \in [0, 2/3]$, Dubickas 2009): $\{0, 1\}$ Confinement,
   No-Bispecial-Pair Property & Explicit $O(W)$ Escape Bounds
   (`dubCarry_shifted_third_mem_zero_one`,
   `dubCarry_shifted_third_no_bispecial_pair`,
   `shifted_third_sturmian_explicit_escape_bound`)**:
   - Proves that whenever $0 \le \{\xi (3/2)^n - s\} \le 1/3$ ($s \in [0, 2/3]$), the shifted
     carry word takes values in the universal two-letter alphabet $\{0, 1\}$ and admits no
     bispecial pair $0 u 0$ and $1 u 1$ of any length $m \ge 1$.
   - Combines the resulting $L + 1$ factor bound with `dubX_repeated_window_pq_cutoff` at
     $(p, q) = (3, 5)$ ($3^5 < 2^8$) to prove the explicit linear escape bound $2 L \le 5 W + 11$.

4. **Explicit $O(W)$ Escape Bounds & Infinite-Horizon Emptiness for Union and Beyond-$1/3$
   Confinement Sets (`nearest_int_fifth_explicit_escape`, `nearest_int_fifth_infinite_escape`,
   `window_three_eighths_explicit_escape`, `window_three_eighths_infinite_escape`,
   `dubickas2008_open_union_explicit_escape`, `dubickas2008_closed_union_explicit_escape`,
   `dubickas2008_closed_union_infinite_escape`)**:
   - **Nearest-Integer Arc $\|\xi (3/2)^n\| < 1/5$ ($[0, 1/5) \cup [4/5, 1)$, length $2/5$):**
     Proves that $y_n, y_{n+1} \in [0, 1/5) \cup [4/5, 1)$ forces $s_{n+1} = s_n$ (period 1),
     so **every $\xi \in [1, 2^W)$ escapes within $N = W + 5$ steps**, and for every $\xi > 0$,
     $\{\xi (3/2)^n\} \notin [0, 1/5) \cup [4/5, 1)$ infinitely often.
   - **Beyond-$1/3$ Single Window $[1/6, 13/24)$ (length $3/8 = 0.375 > 1/3$):**
     Gives a human-readable 5-inequality proof that `11`, `000`, `10101`, `101001010`, and
     `101001001` are forbidden on $[1/6, 13/24)$, forcing $s_{k+3} = s_k$ (period 3) and proving
     that **every $\xi \in [1, 2^W)$ escapes $[1/6, 13/24)$ within $N = W + 14$ steps** (and
     infinitely often for all $\xi > 0$).
   - **Dubickas's 2008 Closed Union $[8/39, 18/39] \cup [21/39, 31/39]$ (length $20/39 > 1/2$,
     *Math. Nachr.* 2008, Cor. 1.2):**
     Proves that `00` locks $y_k = 8/39 \to 4/13 \to 6/13 \to 9/13 \to 7/13 \to 4/13$ and `11`
     locks $y_k = 31/39 \to 9/13 \to 7/13 \to 4/13 \to 6/13$, while avoiding `00` and `11` forces
     period-2 alternation `0101...`. Consequently, **every $\xi \in [1, 2^W)$ escapes the open
     union in $W + 6$ steps and the closed union in $2 W + 18$ steps**, and every $\xi > 0$
     escapes the closed union infinitely often.
-/

namespace Mahler.DubickasExtension

open Mahler
open Mahler.Pinch
open Mahler.OddBlock
open Mahler.BridgeThree
open Mahler.CoprimeSlack
open Mahler.ShiftSlack
open Mahler.CeilingSynthesis
open Mahler.MinSlackSystem
open Mahler.SharpenedSqueezes
open Mahler.InfiniteZNumberBridge
open Mahler.EndpointAndBalancedExclusion
open Mahler.SeedResidueTree
open Mahler.ThueMorseMahler
open Mahler.SparseDefectCocycle

/-! ## 1. Shifted Carry Words $s_n = 2 x_{n+1} - 3 x_n$, Multi-Step Summation & Finite-Horizon Divisibility -/

/-- Shifted integer part $x_n = \lfloor \xi (3/2)^n + \theta \rfloor$. -/
noncomputable def dubX (ξ θ : ℝ) (n : ℕ) : ℤ :=
  ⌊ξ * (3 / 2 : ℝ) ^ n + θ⌋

/-- Shifted fractional part $y_n = \{\xi (3/2)^n + \theta\} \in [0, 1)$. -/
noncomputable def dubY (ξ θ : ℝ) (n : ℕ) : ℝ :=
  Int.fract (ξ * (3 / 2 : ℝ) ^ n + θ)

/-- Shifted carry word $s_n = 2 x_{n+1} - 3 x_n \in \mathbb{Z}$ (Dubickas 2008/2009). -/
noncomputable def dubCarry (ξ θ : ℝ) (n : ℕ) : ℤ :=
  2 * dubX ξ θ (n + 1) - 3 * dubX ξ θ n

theorem dubX_add_dubY (ξ θ : ℝ) (n : ℕ) :
    (dubX ξ θ n : ℝ) + dubY ξ θ n = ξ * (3 / 2 : ℝ) ^ n + θ := by
  unfold dubX dubY
  have h := Int.self_sub_floor (ξ * (3 / 2 : ℝ) ^ n + θ)
  linarith

theorem dubY_bounds (ξ θ : ℝ) (n : ℕ) :
    0 ≤ dubY ξ θ n ∧ dubY ξ θ n < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **Exact Fractional-Part Formula for the Shifted Carry Word (`dubCarry_eq_fract_linear`)**:
For every $\xi, \theta \in \mathbb{R}$ and $n \in \mathbb{N}$:
`(dubCarry ξ θ n : ℝ) = 3 * dubY ξ θ n - 2 * dubY ξ θ (n + 1) - θ`. -/
theorem dubCarry_eq_fract_linear (ξ θ : ℝ) (n : ℕ) :
    (dubCarry ξ θ n : ℝ) = 3 * dubY ξ θ n - 2 * dubY ξ θ (n + 1) - θ := by
  unfold dubCarry
  push_cast
  have h0 := dubX_add_dubY ξ θ n
  have h1 := dubX_add_dubY ξ θ (n + 1)
  rw [pow_succ] at h1
  linarith

/-- Multi-step carry accumulator $\sum_{t=0}^{m-1} 3^{m-1-t} 2^t w(n + t)$. -/
def dubCarryAcc (w : ℕ → ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => 3 * dubCarryAcc w n m + (2 : ℤ) ^ m * w (n + m)

/-- If two integer words agree on $[i, i + L)$ and $[j, j + L)$, their length-$L$
carry accumulators are equal. -/
theorem dubCarryAcc_eq_of_window_eq {w : ℕ → ℤ} {i j L : ℕ}
    (hmatch : ∀ t < L, w (i + t) = w (j + t)) :
    dubCarryAcc w i L = dubCarryAcc w j L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      simp only [dubCarryAcc]
      rw [ih (fun t ht => hmatch t (by omega)), hmatch L (Nat.lt_succ_self L)]

/-- **Exact Multi-Step Integer-Part Summation Identity (`dubX_multi_step_carry_identity`)**:
For all $n, m \in \mathbb{N}$:
`2^m * dubX ξ θ (n + m) = 3^m * dubX ξ θ n + dubCarryAcc (dubCarry ξ θ) n m`. -/
theorem dubX_multi_step_carry_identity (ξ θ : ℝ) (n m : ℕ) :
    (2 : ℤ) ^ m * dubX ξ θ (n + m) =
      (3 : ℤ) ^ m * dubX ξ θ n + dubCarryAcc (dubCarry ξ θ) n m := by
  induction m with
  | zero => simp [dubCarryAcc]
  | succ m ih =>
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      have hstep :
          2 * dubX ξ θ ((n + m) + 1) = 3 * dubX ξ θ (n + m) + dubCarry ξ θ (n + m) := by
        unfold dubCarry
        ring
      calc
        (2 : ℤ) ^ (m + 1) * dubX ξ θ (n + (m + 1)) =
            (2 : ℤ) ^ m * (2 * dubX ξ θ ((n + m) + 1)) := by
          rw [hidx, pow_succ]
          ring
        _ = (2 : ℤ) ^ m * (3 * dubX ξ θ (n + m) + dubCarry ξ θ (n + m)) := by
          rw [hstep]
        _ = 3 * ((2 : ℤ) ^ m * dubX ξ θ (n + m)) + (2 : ℤ) ^ m * dubCarry ξ θ (n + m) := by
          ring
        _ = 3 * ((3 : ℤ) ^ m * dubX ξ θ n + dubCarryAcc (dubCarry ξ θ) n m) +
              (2 : ℤ) ^ m * dubCarry ξ θ (n + m) := by
          rw [ih]
        _ = (3 : ℤ) ^ (m + 1) * dubX ξ θ n + dubCarryAcc (dubCarry ξ θ) n (m + 1) := by
          simp only [dubCarryAcc, pow_succ]
          ring

/-- **Exact Multi-Step Fractional-Part Summation Identity (`dubY_multi_step_carry_identity`)**:
For all $n, m \in \mathbb{N}$:
`(2 : ℝ)^m * dubY ξ θ (n + m) = (3 : ℝ)^m * dubY ξ θ n - (dubCarryAcc (dubCarry ξ θ) n m : ℝ) - ((3 : ℝ)^m - (2 : ℝ)^m) * θ`. -/
theorem dubY_multi_step_carry_identity (ξ θ : ℝ) (n m : ℕ) :
    (2 : ℝ) ^ m * dubY ξ θ (n + m) =
      (3 : ℝ) ^ m * dubY ξ θ n -
        (dubCarryAcc (dubCarry ξ θ) n m : ℝ) - ((3 : ℝ) ^ m - (2 : ℝ) ^ m) * θ := by
  induction m with
  | zero => simp [dubCarryAcc]
  | succ m ih =>
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      have hstep := dubCarry_eq_fract_linear ξ θ (n + m)
      rw [hidx]
      push_cast [dubCarryAcc]
      rw [pow_succ (2 : ℝ) m, pow_succ (3 : ℝ) m]
      linear_combination (3 : ℝ) * ih + (2 : ℝ) ^ m * hstep

/-- **Repeated Carry-Factor Cancellation & $2^L$-Divisibility (`dubX_repeat_factor_cancellation`)**:
Whenever a length-$L$ factor of `dubCarry ξ θ` repeats at origins $i$ and $j$:
1. `(2 : ℤ)^L * (dubX ξ θ (j + L) - dubX ξ θ (i + L)) = (3 : ℤ)^L * (dubX ξ θ j - dubX ξ θ i)`, and
2. `(2 : ℤ)^L ∣ (dubX ξ θ j - dubX ξ θ i)`. -/
theorem dubX_repeat_factor_cancellation {ξ θ : ℝ} {i j L : ℕ}
    (hmatch : ∀ t < L, dubCarry ξ θ (i + t) = dubCarry ξ θ (j + t)) :
    (2 : ℤ) ^ L * (dubX ξ θ (j + L) - dubX ξ θ (i + L)) =
      (3 : ℤ) ^ L * (dubX ξ θ j - dubX ξ θ i) ∧
    (2 : ℤ) ^ L ∣ (dubX ξ θ j - dubX ξ θ i) := by
  have hi := dubX_multi_step_carry_identity ξ θ i L
  have hj := dubX_multi_step_carry_identity ξ θ j L
  have hacc := dubCarryAcc_eq_of_window_eq hmatch
  have heq :
      (2 : ℤ) ^ L * (dubX ξ θ (j + L) - dubX ξ θ (i + L)) =
        (3 : ℤ) ^ L * (dubX ξ θ j - dubX ξ θ i) := by
    linarith
  refine ⟨heq, ?_⟩
  have hdvd_nat : 2 ^ L ∣ 3 ^ L * (dubX ξ θ j - dubX ξ θ i).natAbs := by
    have habs :
        ((2 : ℤ) ^ L * (dubX ξ θ (j + L) - dubX ξ θ (i + L))).natAbs =
          ((3 : ℤ) ^ L * (dubX ξ θ j - dubX ξ θ i)).natAbs := by
      rw [heq]
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at habs
    exact ⟨(dubX ξ θ (j + L) - dubX ξ θ (i + L)).natAbs, habs.symm⟩
  have hcop : Nat.Coprime (2 ^ L) (3 ^ L) :=
    ( (by decide : Nat.Coprime 2 3).pow_left L ).pow_right L
  have hdvd_abs : 2 ^ L ∣ (dubX ξ θ j - dubX ξ θ i).natAbs :=
    hcop.dvd_of_dvd_mul_left hdvd_nat
  simpa [Nat.cast_pow] using Int.ofNat_dvd_left.mpr hdvd_abs

private theorem three_halves_pow_ge_nine_fourths {n : ℕ} (hn : 2 ≤ n) :
    (9 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  rw [pow_add]
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  nlinarith

private theorem three_halves_pow_mono {i j : ℕ} (hij : i < j) :
    (3 / 2 : ℝ) ^ i * (3 / 2 : ℝ) ≤ (3 / 2 : ℝ) ^ j := by
  obtain ⟨k, hk⟩ : ∃ k, j = (i + 1) + k := ⟨j - (i + 1), by omega⟩
  rw [hk, pow_add, pow_succ]
  have hpos : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ i * (3 / 2 : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  nlinarith

/-- **Strict Monotonicity & Positive Lower Bound on `dubX` for $n \ge 2$ (`dubX_strict_step_growth`)**:
For any $\xi \in [1, 2^W)$ and shift $\theta \in [-1, 0]$, whenever $2 \le i < j$:
1. $1 \le \operatorname{dubX} \xi \theta i$,
2. $1 \le \operatorname{dubX} \xi \theta j - \operatorname{dubX} \xi \theta i$, and
3. $(\operatorname{dubX} \xi \theta j - \operatorname{dubX} \xi \theta i : \mathbb{R}) < 2^W (3 / 2)^j$. -/
theorem dubX_strict_step_growth {ξ θ : ℝ} {W i j : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hi2 : 2 ≤ i) (hij : i < j) :
    1 ≤ dubX ξ θ i ∧
      1 ≤ dubX ξ θ j - dubX ξ θ i ∧
      ((dubX ξ θ j - dubX ξ θ i : ℤ) : ℝ) < (2 : ℝ) ^ W * (3 / 2 : ℝ) ^ j := by
  have hpow_i := three_halves_pow_ge_nine_fourths hi2
  have hpow_i_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ i := by positivity
  have hpow_j_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ j := by positivity
  have hval_i : (5 / 4 : ℝ) ≤ ξ * (3 / 2 : ℝ) ^ i + θ := by nlinarith
  have hxi_ge1 : 1 ≤ dubX ξ θ i := by
    unfold dubX
    exact Int.le_floor.mpr (by norm_num; linarith)
  have hstep_ij := three_halves_pow_mono hij
  have hdiff_real :
      (9 / 8 : ℝ) ≤ (ξ * (3 / 2 : ℝ) ^ j + θ) - (ξ * (3 / 2 : ℝ) ^ i + θ) := by
    have h1 : (3 / 2 : ℝ) ^ i * (3 / 2 : ℝ) - (3 / 2 : ℝ) ^ i = (1 / 2 : ℝ) * (3 / 2 : ℝ) ^ i := by
      ring
    have h2 : (9 / 8 : ℝ) ≤ ξ * ((3 / 2 : ℝ) ^ i * (1 / 2 : ℝ)) := by nlinarith
    have h3 : ξ * ((3 / 2 : ℝ) ^ i * (3 / 2 : ℝ)) ≤ ξ * (3 / 2 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hstep_ij (by linarith)
    linarith
  have hfl_i_le : (dubX ξ θ i : ℝ) ≤ ξ * (3 / 2 : ℝ) ^ i + θ := Int.floor_le _
  have hfl_j_gt : ξ * (3 / 2 : ℝ) ^ j + θ - 1 < (dubX ξ θ j : ℝ) := by
    have h := Int.lt_floor_add_one (ξ * (3 / 2 : ℝ) ^ j + θ)
    unfold dubX
    linarith
  have hdiff_gt_zero : (0 : ℝ) < (dubX ξ θ j : ℝ) - (dubX ξ θ i : ℝ) := by linarith
  have hdiff_int_pos : 0 < dubX ξ θ j - dubX ξ θ i := by
    have hcast : ((0 : ℤ) : ℝ) < ((dubX ξ θ j - dubX ξ θ i : ℤ) : ℝ) := by
      push_cast
      exact hdiff_gt_zero
    exact_mod_cast hcast
  have hfl_j_le : (dubX ξ θ j : ℝ) ≤ ξ * (3 / 2 : ℝ) ^ j + θ := Int.floor_le _
  have hxi_real_ge1 : (1 : ℝ) ≤ (dubX ξ θ i : ℝ) := by exact_mod_cast hxi_ge1
  have hupper : ((dubX ξ θ j - dubX ξ θ i : ℤ) : ℝ) < (2 : ℝ) ^ W * (3 / 2 : ℝ) ^ j := by
    push_cast
    have hlt : ξ * (3 / 2 : ℝ) ^ j < (2 : ℝ) ^ W * (3 / 2 : ℝ) ^ j :=
      mul_lt_mul_of_pos_right hξW hpow_j_pos
    linarith
  exact ⟨hxi_ge1, by omega, hupper⟩

/-- **Explicit Finite-Horizon Exponential Bound for Repeated Shifted Carry Windows
(`dubX_repeated_window_exp_bound`)**:
If $\xi \in [1, 2^W)$, $\theta \in [-1, 0]$, $2 \le i < j$, and `dubCarry ξ θ` has a
repeated length-$L$ factor at $i$ and $j$, then:
$$2^{L + j} < 3^j \cdot 2^W.$$ -/
theorem dubX_repeated_window_exp_bound {ξ θ : ℝ} {W i j L : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hi2 : 2 ≤ i) (hij : i < j)
    (hmatch : ∀ t < L, dubCarry ξ θ (i + t) = dubCarry ξ θ (j + t)) :
    2 ^ (L + j) < 3 ^ j * 2 ^ W := by
  rcases dubX_strict_step_growth hξ1 hξW hθ_lo hθ_hi hi2 hij with ⟨_, hpos, hupper⟩
  have hdvd := (dubX_repeat_factor_cancellation hmatch).2
  have hle_int : (2 : ℤ) ^ L ≤ dubX ξ θ j - dubX ξ θ i :=
    Int.le_of_dvd (by omega) hdvd
  have hle_real : (2 : ℝ) ^ L ≤ ((dubX ξ θ j - dubX ξ θ i : ℤ) : ℝ) := by
    exact_mod_cast hle_int
  have hlt_real : (2 : ℝ) ^ L < (2 : ℝ) ^ W * ((3 : ℝ) ^ j / (2 : ℝ) ^ j) := by
    rw [← div_pow]
    exact lt_of_le_of_lt hle_real hupper
  have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hmul : (2 : ℝ) ^ L * (2 : ℝ) ^ j < (3 : ℝ) ^ j * (2 : ℝ) ^ W := by
    have h := (lt_div_iff₀ h2j_pos).mp (by
      calc
        (2 : ℝ) ^ L < (2 : ℝ) ^ W * ((3 : ℝ) ^ j / (2 : ℝ) ^ j) := hlt_real
        _ = ((3 : ℝ) ^ j * (2 : ℝ) ^ W) / (2 : ℝ) ^ j := by ring)
    exact h
  rw [← pow_add] at hmul
  exact_mod_cast hmul

/-- **Parameterized $(p, q)$ Linear Cutoff for Shifted Carry Repetitions
(`dubX_repeated_window_pq_cutoff`)**:
Whenever $1 \le q$, $3^q < 2^{p+q}$, $\xi \in [1, 2^W)$, $\theta \in [-1, 0]$, $2 \le i < j$,
and `dubCarry ξ θ` repeats a length-$L$ window at $i$ and $j$:
$$q L + 1 \le p j + q W.$$ -/
theorem dubX_repeated_window_pq_cutoff {ξ θ : ℝ} {p q W i j L : ℕ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hi2 : 2 ≤ i) (hij : i < j)
    (hmatch : ∀ t < L, dubCarry ξ θ (i + t) = dubCarry ξ θ (j + t)) :
    q * L + 1 ≤ p * j + q * W := by
  have hexp := dubX_repeated_window_exp_bound hξ1 hξW hθ_lo hθ_hi hi2 hij hmatch
  have hpow_q : (2 ^ (L + j)) ^ q < (3 ^ j * 2 ^ W) ^ q := by
    exact Nat.pow_lt_pow_left hexp (by omega)
  have h3q : (3 ^ j) ^ q ≤ (2 ^ (p + q)) ^ j := by
    have hcomm : (3 ^ j) ^ q = (3 ^ q) ^ j := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    rw [hcomm]
    exact Nat.pow_le_pow_left (le_of_lt hpq) j
  have hrhs : (3 ^ j * 2 ^ W) ^ q ≤ 2 ^ ((p + q) * j + W * q) := by
    calc
      (3 ^ j * 2 ^ W) ^ q = (3 ^ j) ^ q * (2 ^ W) ^ q := Nat.mul_pow _ _ _
      _ ≤ (2 ^ (p + q)) ^ j * (2 ^ W) ^ q := Nat.mul_le_mul_right _ h3q
      _ = 2 ^ ((p + q) * j + W * q) := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
  have hlt2 : 2 ^ ((L + j) * q) < 2 ^ ((p + q) * j + W * q) := by
    rw [← Nat.pow_mul] at hpow_q
    exact lt_of_lt_of_le hpow_q hrhs
  have hexp_lt : (L + j) * q < (p + q) * j + W * q := by
    by_contra hge
    have hle : 2 ^ ((p + q) * j + W * q) ≤ 2 ^ ((L + j) * q) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hring1 : (L + j) * q = q * L + q * j := by ring
  have hring2 : (p + q) * j + W * q = p * j + q * j + q * W := by ring
  omega

/-! ## 2. Sharp $\log 2 / \log(3/2)$ Sub-Critical Complexity Exclusion for Shifted Carry Words -/

/-- Natural-number shifted carry word `dubCarryNat ξ θ n = Int.toNat (dubCarry ξ θ n + 2)`
shifted by $+2$ so every symbol in $[-2, 3]$ is injectively represented in $\mathbb{N}$. -/
noncomputable def dubCarryNat (ξ θ : ℝ) (n : ℕ) : ℕ :=
  Int.toNat (dubCarry ξ θ n + 2)

theorem dubCarry_nonneg_add_two (ξ : ℝ) {θ : ℝ} (hθ_hi : θ ≤ 0) (n : ℕ) :
    0 ≤ dubCarry ξ θ n + 2 := by
  have hy0 := (dubY_bounds ξ θ n).1
  have hy1 := (dubY_bounds ξ θ (n + 1)).2
  have hlin := dubCarry_eq_fract_linear ξ θ n
  have hreal : (-2 : ℝ) < (dubCarry ξ θ n : ℝ) := by linarith
  have hint : -2 < dubCarry ξ θ n := by exact_mod_cast hreal
  omega

theorem dubCarryNat_eq_iff {ξ θ : ℝ} (hθ_hi : θ ≤ 0) (m n : ℕ) :
    dubCarryNat ξ θ m = dubCarryNat ξ θ n ↔ dubCarry ξ θ m = dubCarry ξ θ n := by
  unfold dubCarryNat
  have hm := dubCarry_nonneg_add_two ξ hθ_hi m
  have hn := dubCarry_nonneg_add_two ξ hθ_hi n
  constructor
  · intro h
    have hcast : (Int.toNat (dubCarry ξ θ m + 2) : ℤ) = (Int.toNat (dubCarry ξ θ n + 2) : ℤ) := by
      rw [h]
    rw [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg hn] at hcast
    omega
  · intro h
    rw [h]

/-- **Explicit Finite-Horizon Cutoff for Sub-Critical Shifted Carry Complexity
(`dubCarry_subcritical_pq_finite_cutoff`)**:
For any $1 \le q$, $3^q < 2^{p+q}$, $\xi \in [1, 2^W)$, and $\theta \in [-1, 0]$,
if the shifted carry word from offset $2$ (`shiftSeq (dubCarryNat ξ θ) 2`) has
`prefixFactorCount (shiftSeq (dubCarryNat ξ θ) 2) L C ≤ C`, then:
$$q L + 1 \le p (C + 2) + q W.$$ -/
theorem dubCarry_subcritical_pq_finite_cutoff {ξ θ : ℝ} {p q W L C : ℕ}
    (hq : 1 ≤ q) (hpq : 3 ^ q < 2 ^ (p + q))
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hcard : prefixFactorCount (shiftSeq (dubCarryNat ξ θ) 2) L C ≤ C) :
    q * L + 1 ≤ p * (C + 2) + q * W := by
  obtain ⟨r1, r2, hr12, hr2C, hmatch_nat⟩ :=
    exists_repeated_subword_of_prefixFactorCount_le
      (shiftSeq (dubCarryNat ξ θ) 2) L C hcard
  have hmatch : ∀ t < L, dubCarry ξ θ ((2 + r1) + t) = dubCarry ξ θ ((2 + r2) + t) := by
    intro t ht
    have h := hmatch_nat t ht
    simp only [shiftSeq] at h
    have hidx1 : 2 + (r1 + t) = (2 + r1) + t := by omega
    have hidx2 : 2 + (r2 + t) = (2 + r2) + t := by omega
    rw [hidx1, hidx2] at h
    exact (dubCarryNat_eq_iff hθ_hi ((2 + r1) + t) ((2 + r2) + t)).mp h
  have hcut :=
    dubX_repeated_window_pq_cutoff hq hpq hξ1 hξW hθ_lo hθ_hi
      (i := 2 + r1) (j := 2 + r2) (by omega) (by omega) hmatch
  have hp_le : p * (2 + r2) ≤ p * (C + 2) := Nat.mul_le_mul_left p (by omega)
  omega

/-- **Global Forward-Shift Helper for Arbitrary Positive Reals $\xi > 0$ (`exists_pow_shift_ge_one_and_lt_two_pow`)**:
For every real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$, there exist $k \ge N_0$ and
$W \ge 1$ such that $1 \le \xi (3/2)^k < 2^W$. -/
theorem exists_pow_shift_ge_one_and_lt_two_pow {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ (k W : ℕ), N_0 ≤ k ∧ 1 ≤ W ∧
      (1 : ℝ) ≤ ξ * (3 / 2 : ℝ) ^ k ∧ ξ * (3 / 2 : ℝ) ^ k < (2 : ℝ) ^ W := by
  obtain ⟨k0, hk0⟩ := exists_nat_gt (2 / ξ)
  set k := max N_0 (k0 + 2)
  have hk_ge : N_0 ≤ k := le_max_left _ _
  have hk0_le : k0 + 2 ≤ k := le_max_right _ _
  have hpow_ge : (1 : ℝ) + (k : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ k := by
    clear hk_ge hk0_le
    induction k with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        have hpos : (0 : ℝ) ≤ (m : ℝ) / 4 := by positivity
        nlinarith
  have h1 : 2 < (k0 : ℝ) * ξ := (div_lt_iff₀ hξ).mp hk0
  have h2 : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k0 ≤ k)
  have h3 : 2 < (k : ℝ) * ξ := by nlinarith
  have h4 : ξ * (1 + (k : ℝ) / 2) ≤ ξ * (3 / 2 : ℝ) ^ k :=
    mul_le_mul_of_nonneg_left hpow_ge (le_of_lt hξ)
  have hge1 : (1 : ℝ) ≤ ξ * (3 / 2 : ℝ) ^ k := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (ξ * (3 / 2 : ℝ) ^ k)
  set W := max M 1
  have hW1 : 1 ≤ W := le_max_right M 1
  have hMW : M ≤ W := le_max_left M 1
  have hlt_pow : (W : ℝ) < (2 : ℝ) ^ W := by
    have hnat : W < 2 ^ W := by
      clear hW1 hMW
      induction W with
      | zero => decide
      | succ n ih =>
          have hpos : 1 ≤ 2 ^ n := Nat.pow_pos (by decide)
          rw [Nat.pow_succ]
          omega
    exact_mod_cast hnat
  have hMW_real : (M : ℝ) ≤ (W : ℝ) := by exact_mod_cast hMW
  exact ⟨k, W, hk_ge, hW1, hge1, by linarith⟩

/-- **Sharp $\log 2 / \log(3/2)$ Sub-Critical Complexity Exclusion for Shifted Carry Words
(`no_subcritical_log_threshold_dubCarry`)**:
Strengthens Dubickas's Sturmian carry theorem ($\kappa = 1$) to the full critical slope
$\kappa < \log 2 / \log(3/2) \approx 1.709511$: for **every** $\xi \ge 1$, $\theta \in [-1, 0]$,
and $\kappa \log(3/2) < \log 2$, the shifted carry word `shiftSeq (dubCarryNat ξ θ) 2`
cannot satisfy `prefixFactorCount ... L (C L) ≤ C L ≤ kappa * L + C_0` at arbitrarily large
lengths $L$. -/
theorem no_subcritical_log_threshold_dubCarry
    {ξ θ kappa C_0 : ℝ} {C : ℕ → ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ)) :
    ¬ (∀ L_min : ℕ, ∃ L ≥ L_min,
      prefixFactorCount (shiftSeq (dubCarryNat ξ θ) 2) L (C L) ≤ C L ∧
        (C L : ℝ) ≤ kappa * (L : ℝ) + C_0) := by
  intro hliminf
  obtain ⟨p, q, hq, hpq, hsub⟩ := exists_pq_of_lt_log_threshold hlog
  obtain ⟨W, hW⟩ := exists_nat_gt ξ
  have hlt_pow : (W : ℝ) < (2 : ℝ) ^ W := by
    have hnat : W < 2 ^ W := by
      clear hW
      induction W with
      | zero => decide
      | succ n ih =>
          have hpos : 1 ≤ 2 ^ n := Nat.pow_pos (by decide)
          rw [Nat.pow_succ]
          omega
    exact_mod_cast hnat
  have hξW : ξ < (2 : ℝ) ^ W := lt_trans hW hlt_pow
  set gap : ℝ := (q : ℝ) - (p : ℝ) * kappa
  have hgap_pos : 0 < gap := by unfold gap; linarith
  set RHS : ℝ := (p : ℝ) * (C_0 + 2) + (q : ℝ) * (W : ℝ)
  have hRHS_nonneg : 0 ≤ RHS := by unfold RHS; positivity
  obtain ⟨L_min, hL_min⟩ := exists_nat_gt (RHS / gap + 1)
  obtain ⟨L, hL_ge, hcard, hC_bound⟩ := hliminf L_min
  have hcut :=
    dubCarry_subcritical_pq_finite_cutoff hq hpq hξ1 hξW hθ_lo hθ_hi hcard
  have hcut_real :
      (q : ℝ) * (L : ℝ) + 1 ≤ (p : ℝ) * ((C L : ℝ) + 2) + (q : ℝ) * (W : ℝ) := by
    exact_mod_cast hcut
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hp_mul :
      (p : ℝ) * ((C L : ℝ) + 2) ≤ (p : ℝ) * (kappa * (L : ℝ) + C_0 + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hp_nonneg
  have hgap_le : gap * (L : ℝ) + 1 ≤ RHS := by
    unfold gap RHS
    linarith
  have hL_real : (L_min : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge
  have h1 : RHS / gap < (L : ℝ) := by linarith
  have h2 : RHS < (L : ℝ) * gap := (div_lt_iff₀ hgap_pos).mp h1
  linarith

/-! ## 3. Shifted $1/3$-Windows $[s, s + 1/3]$ ($s \in [0, 2/3]$, Dubickas 2009): $\{0, 1\}$ Alphabet, No Bispecial Pairs & Explicit $O(W)$ Cutoff -/

/-- **Universal $\{0, 1\}$ Carry Alphabet on Shifted $1/3$-Windows (`dubCarry_shifted_third_mem_zero_one`)**:
For **every** shift $s \in [0, 2/3]$, if $y_n = \{\xi (3/2)^n - s\} \le 1/3$ and
$y_{n+1} = \{\xi (3/2)^{n+1} - s\} \le 1/3$, then `dubCarry ξ (-s) n` lies in $\{0, 1\}$
(`0 ≤ dubCarry ξ (-s) n ≤ 1`). -/
theorem dubCarry_shifted_third_mem_zero_one {ξ s : ℝ} {n : ℕ}
    (hs0 : 0 ≤ s) (hs23 : s ≤ (2 / 3 : ℝ))
    (hyn : dubY ξ (-s) n ≤ (1 / 3 : ℝ))
    (hyn1 : dubY ξ (-s) (n + 1) ≤ (1 / 3 : ℝ)) :
    (0 ≤ dubCarry ξ (-s) n ∧ dubCarry ξ (-s) n ≤ 1) ∧
      (dubCarry ξ (-s) n = 0 ∨ dubCarry ξ (-s) n = 1) := by
  have hy0 := (dubY_bounds ξ (-s) n).1
  have hy1 := (dubY_bounds ξ (-s) (n + 1)).1
  have hlin := dubCarry_eq_fract_linear ξ (-s) n
  have hlo_real : (-1 : ℝ) < (dubCarry ξ (-s) n : ℝ) := by linarith
  have hhi_real : (dubCarry ξ (-s) n : ℝ) < (2 : ℝ) := by linarith
  have hlo_int : -1 < dubCarry ξ (-s) n := by exact_mod_cast hlo_real
  have hhi_int : dubCarry ξ (-s) n < 2 := by exact_mod_cast hhi_real
  exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- **Dubickas's No-Bispecial-Pair Theorem on Shifted $1/3$-Windows (`dubCarry_shifted_third_no_bispecial_pair`)**:
For any $s \in \mathbb{R}$, if $y_i, y_{i+m}, y_j, y_{j+m} \in [0, 1/3]$ (with $m \ge 2$),
then `dubCarry ξ (-s)` cannot have a bispecial pair of length $m$ at $i$ and $j$
(`dubCarry ξ (-s) j = dubCarry ξ (-s) i + 1`, matching middle $m - 2$ symbols, and
`dubCarry ξ (-s) (j + m - 1) = dubCarry ξ (-s) (i + m - 1) + 1`). -/
theorem dubCarry_shifted_third_no_bispecial_pair {ξ s : ℝ} {i j m : ℕ}
    (hm : 2 ≤ m)
    (_hyi : dubY ξ (-s) i ≤ (1 / 3 : ℝ))
    (hyim : dubY ξ (-s) (i + m) ≤ (1 / 3 : ℝ))
    (hyj : dubY ξ (-s) j ≤ (1 / 3 : ℝ))
    (hyjm : dubY ξ (-s) (j + m) ≤ (1 / 3 : ℝ))
    (hfirst : dubCarry ξ (-s) j = dubCarry ξ (-s) i + 1)
    (hmid : ∀ t : ℕ, 1 ≤ t → t + 1 < m → dubCarry ξ (-s) (j + t) = dubCarry ξ (-s) (i + t))
    (hlast : dubCarry ξ (-s) (j + (m - 1)) = dubCarry ξ (-s) (i + (m - 1)) + 1) :
    False := by
  have hi_id := dubY_multi_step_carry_identity ξ (-s) i m
  have hj_id := dubY_multi_step_carry_identity ξ (-s) j m
  have hyi0 := (dubY_bounds ξ (-s) i).1
  have hyim0 := (dubY_bounds ξ (-s) (i + m)).1
  have hyj0 := (dubY_bounds ξ (-s) j).1
  have hyjm0 := (dubY_bounds ξ (-s) (j + m)).1
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hmid_eq :
      ∀ r ≤ k + 1, 1 ≤ r →
        dubCarryAcc (dubCarry ξ (-s)) j r - dubCarryAcc (dubCarry ξ (-s)) i r =
          (3 : ℤ) ^ (r - 1) := by
    intro r hr_hi hr_lo
    induction r with
    | zero => omega
    | succ r ih =>
        rcases Nat.eq_zero_or_pos r with rfl | hr_pos
        · simp only [dubCarryAcc, pow_zero, mul_zero, zero_add, one_mul, Nat.add_zero]
          omega
        · have ihr := ih (by omega) hr_pos
          have hmid_r := hmid r hr_pos (by omega)
          change (3 * dubCarryAcc (dubCarry ξ (-s)) j r + (2 : ℤ) ^ r * dubCarry ξ (-s) (j + r)) -
            (3 * dubCarryAcc (dubCarry ξ (-s)) i r + (2 : ℤ) ^ r * dubCarry ξ (-s) (i + r)) =
            (3 : ℤ) ^ r
          rw [hmid_r]
          have hr_eq : r = (r - 1) + 1 := by omega
          have hpow3 : 3 * (3 : ℤ) ^ (r - 1) = (3 : ℤ) ^ r := by
            conv_rhs => rw [hr_eq, pow_succ']
          linarith [ihr, hpow3]
  have hk1 := hmid_eq (k + 1) le_rfl (by omega)
  simp only [Nat.add_sub_cancel] at hk1
  have hlast_k :
      dubCarry ξ (-s) (j + (k + 1)) = dubCarry ξ (-s) (i + (k + 1)) + 1 := hlast
  have hacc_diff :
      dubCarryAcc (dubCarry ξ (-s)) j (k + 2) -
        dubCarryAcc (dubCarry ξ (-s)) i (k + 2) =
        (3 : ℤ) ^ (k + 1) + (2 : ℤ) ^ (k + 1) := by
    change (3 * dubCarryAcc (dubCarry ξ (-s)) j (k + 1) +
        (2 : ℤ) ^ (k + 1) * dubCarry ξ (-s) (j + (k + 1))) -
      (3 * dubCarryAcc (dubCarry ξ (-s)) i (k + 1) +
        (2 : ℤ) ^ (k + 1) * dubCarry ξ (-s) (i + (k + 1))) =
      (3 : ℤ) ^ (k + 1) + (2 : ℤ) ^ (k + 1)
    rw [hlast_k]
    have hpow3 : 3 * (3 : ℤ) ^ k = (3 : ℤ) ^ (k + 1) := by rw [pow_succ']
    linarith [hk1, hpow3]
  have hacc_real :
      (dubCarryAcc (dubCarry ξ (-s)) j (k + 2) : ℝ) -
        (dubCarryAcc (dubCarry ξ (-s)) i (k + 2) : ℝ) =
        (3 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hacc_diff
  have hpow3_pos : (0 : ℝ) ≤ (3 : ℝ) ^ (k + 1) := by positivity
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have h3j_hi : (3 : ℝ) ^ (k + 2) * dubY ξ (-s) j ≤ (3 : ℝ) ^ (k + 1) := by
    have hp : (3 : ℝ) ^ (k + 2) = 3 * (3 : ℝ) ^ (k + 1) := by rw [pow_succ']
    rw [hp]
    nlinarith
  have h3i_lo : (0 : ℝ) ≤ (3 : ℝ) ^ (k + 2) * dubY ξ (-s) i := by positivity
  have h2im_hi :
      (2 : ℝ) ^ (k + 2) * dubY ξ (-s) (i + (k + 2)) ≤ (2 / 3 : ℝ) * (2 : ℝ) ^ (k + 1) := by
    have hp : (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) := by rw [pow_succ']
    rw [hp]
    nlinarith
  have h2jm_lo : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 2) * dubY ξ (-s) (j + (k + 2)) := by positivity
  linarith

/-- **Explicit $O(W)$ Escape Bound for Sturmian / $(L + 1)$-Complexity Shifted Carry Words
(`shifted_third_sturmian_explicit_escape_bound`)**:
If $\xi \in [1, 2^W)$, $s \in [0, 2/3]$, and the shifted carry word from step $2$ has
Sturmian/balanced prefix complexity `prefixFactorCount (shiftSeq (dubCarryNat ξ (-s)) 2) L (L + 1) ≤ L + 1`,
then $2 L \le 5 W + 8$ (so $L \le \lfloor (5 W + 8) / 2 \rfloor$). -/
theorem shifted_third_sturmian_explicit_escape_bound {ξ s : ℝ} {W L : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hs0 : 0 ≤ s) (hs23 : s ≤ (2 / 3 : ℝ))
    (hcard : prefixFactorCount (shiftSeq (dubCarryNat ξ (-s)) 2) L (L + 1) ≤ L + 1) :
    2 * L ≤ 5 * W + 8 := by
  have hcut :=
    dubCarry_subcritical_pq_finite_cutoff
      (p := 3) (q := 5) (C := L + 1)
      (by decide : 1 ≤ 5) (by decide : 3 ^ 5 < 2 ^ (3 + 5))
      hξ1 hξW (by linarith) (by linarith) hcard
  omega

/-- Truncate a length-`(k + 1)` factor to its length-`k` prefix. -/
def factorInit {k : ℕ} (f : Fin (k + 1) → ℕ) : Fin k → ℕ :=
  fun i => f ⟨i.val, by omega⟩

private theorem factorInit_factorWindow (w : ℕ → ℕ) (k r : ℕ) :
    factorInit (factorWindow w (k + 1) r) = factorWindow w k r := by
  funext i
  rfl

private theorem factor_eq_of_init_and_last {k : ℕ} {f1 f2 : Fin (k + 1) → ℕ}
    (hinit : factorInit f1 = factorInit f2)
    (hlast : f1 ⟨k, Nat.lt_succ_self k⟩ = f2 ⟨k, Nat.lt_succ_self k⟩) :
    f1 = f2 := by
  funext i
  rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ i.isLt) with heq | hlt
  · have hi : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
    rw [hi, hlast]
  · exact congrFun hinit ⟨i.val, hlt⟩

private theorem prefixFactorCount_zero_le_one (w : ℕ → ℕ) (C : ℕ) :
    prefixFactorCount w 0 C ≤ 1 := by
  unfold prefixFactorCount
  apply Finset.card_le_one.mpr
  intro f1 _ f2 _
  funext i
  exact Fin.elim0 i

/-- **Finite Bispecial-Free Complexity Step (`prefixFactorCount_succ_le_of_no_bispecial`)**:
If a word $w : \mathbb{N} \to \mathbb{N}$ takes values in $\{c_0, c_1\}$ ($c_1 = c_0 + 1$)
on $[0, C + k]$ and has no bispecial pair of length $2 \le m \le k + 1$ at origins
$i, j$ with $i + m \le C + k + 1$ and $j + m \le C + k + 1$, then at most one length-$k$
factor in `prefixFactorSet w k C` can extend by both $c_0$ and $c_1$, so:
`prefixFactorCount w (k + 1) C ≤ prefixFactorCount w k C + 1`. -/
theorem prefixFactorCount_succ_le_of_no_bispecial
    {w : ℕ → ℕ} {c0 k C : ℕ}
    (hbin : ∀ n ≤ C + k, w n = c0 ∨ w n = c0 + 1)
    (hnobisp : ∀ i j m : ℕ, 2 ≤ m → i + m ≤ C + k + 1 → j + m ≤ C + k + 1 →
      w j = w i + 1 →
      (∀ t : ℕ, 1 ≤ t → t + 1 < m → w (j + t) = w (i + t)) →
      w (j + (m - 1)) = w (i + (m - 1)) + 1 → False) :
    prefixFactorCount w (k + 1) C ≤ prefixFactorCount w k C + 1 := by
  classical
  set A := prefixFactorSet w (k + 1) C
  set B := prefixFactorSet w k C
  set lastIdx : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  set A0 := A.filter (fun f => f lastIdx = c0)
  set A1 := A.filter (fun f => f lastIdx = c0 + 1)
  have hsub_A : A ⊆ A0 ∪ A1 := by
    intro f hf
    simp only [A, prefixFactorSet, Finset.mem_image, Finset.mem_range] at hf
    rcases hf with ⟨r, hr, rfl⟩
    simp only [A0, A1, Finset.mem_union, Finset.mem_filter]
    have hmem : factorWindow w (k + 1) r ∈ A := by
      simp only [A, prefixFactorSet, Finset.mem_image, Finset.mem_range]
      exact ⟨r, hr, rfl⟩
    rcases hbin (r + k) (by omega) with h0 | h1
    · exact Or.inl ⟨hmem, h0⟩
    · exact Or.inr ⟨hmem, h1⟩
  have hinj0 : Set.InjOn (factorInit (k := k)) (A0 : Set (Fin (k + 1) → ℕ)) := by
    intro f1 hf1 f2 hf2 hinit
    simp only [A0, Finset.mem_coe, Finset.mem_filter] at hf1 hf2
    exact factor_eq_of_init_and_last hinit (hf1.2.trans hf2.2.symm)
  have hinj1 : Set.InjOn (factorInit (k := k)) (A1 : Set (Fin (k + 1) → ℕ)) := by
    intro f1 hf1 f2 hf2 hinit
    simp only [A1, Finset.mem_coe, Finset.mem_filter] at hf1 hf2
    exact factor_eq_of_init_and_last hinit (hf1.2.trans hf2.2.symm)
  set I0 := A0.image factorInit
  set I1 := A1.image factorInit
  have hcard0 : I0.card = A0.card := Finset.card_image_of_injOn hinj0
  have hcard1 : I1.card = A1.card := Finset.card_image_of_injOn hinj1
  have hunion_sub : I0 ∪ I1 ⊆ B := by
    intro u hu
    simp only [I0, I1, A0, A1, A, B, prefixFactorSet, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hu ⊢
    rcases hu with ⟨f, ⟨⟨r, hr, rfl⟩, _⟩, rfl⟩ | ⟨f, ⟨⟨r, hr, rfl⟩, _⟩, rfl⟩
    · exact ⟨r, hr, factorInit_factorWindow w k r⟩
    · exact ⟨r, hr, factorInit_factorWindow w k r⟩
  have hinter_le_one : (I0 ∩ I1).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    by_contra huv
    simp only [I0, I1, A0, A1, A, prefixFactorSet, Finset.mem_inter,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hu hv
    rcases hu with ⟨⟨_, ⟨⟨a0, ha0, rfl⟩, ha0_last⟩, rfl⟩, ⟨_, ⟨⟨a1, ha1, rfl⟩, ha1_last⟩, ha1_eq⟩⟩
    rcases hv with ⟨⟨_, ⟨⟨b0, hb0, rfl⟩, hb0_last⟩, rfl⟩, ⟨_, ⟨⟨b1, hb1, rfl⟩, hb1_last⟩, hb1_eq⟩⟩
    simp only [factorInit_factorWindow] at ha1_eq hb1_eq huv
    have ha_agree : ∀ t < k, w (a1 + t) = w (a0 + t) :=
      (factorWindow_eq_iff w k a1 a0).mp ha1_eq
    have hb_agree : ∀ t < k, w (b1 + t) = w (b0 + t) :=
      (factorWindow_eq_iff w k b1 b0).mp hb1_eq
    set D := (Finset.range k).filter (fun t => w (a0 + t) ≠ w (b0 + t))
    have hD_nonempty : D.Nonempty := by
      by_contra hD_empty
      rw [Finset.not_nonempty_iff_eq_empty] at hD_empty
      apply huv
      rw [factorWindow_eq_iff]
      intro t ht
      by_contra hne
      have hmem : t ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hne⟩
      rw [hD_empty] at hmem
      exact Finset.not_mem_empty t hmem
    set t0 := D.max' hD_nonempty
    have ht0_mem : t0 ∈ D := Finset.max'_mem D hD_nonempty
    simp only [D, Finset.mem_filter, Finset.mem_range] at ht0_mem
    rcases ht0_mem with ⟨ht0_lt, ht0_ne⟩
    have hafter_eq : ∀ t : ℕ, 1 ≤ t → t + 1 < k - t0 + 1 →
        w (a0 + t0 + t) = w (b0 + t0 + t) := by
      intro t ht1 ht2
      by_contra hne
      have hidx_a : a0 + t0 + t = a0 + (t0 + t) := by omega
      have hidx_b : b0 + t0 + t = b0 + (t0 + t) := by omega
      rw [hidx_a, hidx_b] at hne
      have hmem : t0 + t ∈ D :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne⟩
      have hle := Finset.le_max' D (t0 + t) hmem
      omega
    change w (a0 + k) = c0 at ha0_last
    change w (a1 + k) = c0 + 1 at ha1_last
    change w (b0 + k) = c0 at hb0_last
    change w (b1 + k) = c0 + 1 at hb1_last
    rcases hbin (a0 + t0) (by omega) with ha_c0 | ha_c1 <;>
      rcases hbin (b0 + t0) (by omega) with hb_c0 | hb_c1
    · omega
    · apply hnobisp (a0 + t0) (b1 + t0) (k - t0 + 1) (by omega) (by omega) (by omega)
      · rw [hb_agree t0 ht0_lt, hb_c1, ha_c0]
      · intro t ht1 ht2
        have hb_t : w (b1 + t0 + t) = w (b0 + t0 + t) := by
          have h1 : b1 + t0 + t = b1 + (t0 + t) := by omega
          have h2 : b0 + t0 + t = b0 + (t0 + t) := by omega
          rw [h1, h2]
          exact hb_agree (t0 + t) (by omega)
        rw [hb_t, hafter_eq t ht1 ht2]
      · have h1 : b1 + t0 + (k - t0 + 1 - 1) = b1 + k := by omega
        have h2 : a0 + t0 + (k - t0 + 1 - 1) = a0 + k := by omega
        rw [h1, h2, hb1_last, ha0_last]
    · apply hnobisp (b0 + t0) (a1 + t0) (k - t0 + 1) (by omega) (by omega) (by omega)
      · rw [ha_agree t0 ht0_lt, ha_c1, hb_c0]
      · intro t ht1 ht2
        have ha_t : w (a1 + t0 + t) = w (a0 + t0 + t) := by
          have h1 : a1 + t0 + t = a1 + (t0 + t) := by omega
          have h2 : a0 + t0 + t = a0 + (t0 + t) := by omega
          rw [h1, h2]
          exact ha_agree (t0 + t) (by omega)
        rw [ha_t, hafter_eq t ht1 ht2]
      · have h1 : a1 + t0 + (k - t0 + 1 - 1) = a1 + k := by omega
        have h2 : b0 + t0 + (k - t0 + 1 - 1) = b0 + k := by omega
        rw [h1, h2, ha1_last, hb0_last]
    · omega
  have hcard_A : A.card ≤ A0.card + A1.card :=
    le_trans (Finset.card_le_card hsub_A) (Finset.card_union_le A0 A1)
  have hcard_union : (I0 ∪ I1).card + (I0 ∩ I1).card = I0.card + I1.card :=
    Finset.card_union_add_card_inter I0 I1
  have hcard_B : (I0 ∪ I1).card ≤ B.card := Finset.card_le_card hunion_sub
  change A.card ≤ B.card + 1
  omega

/-- **Finite Bispecial-Free Complexity Bound $\le L + 1$ (`prefixFactorCount_le_add_one_of_no_bispecial`)**:
By induction on $L$, any `{c0, c0 + 1}`-valued word $w$ on $[0, C + L)$ with no bispecial
pair satisfies `prefixFactorCount w L C ≤ L + 1`. -/
theorem prefixFactorCount_le_add_one_of_no_bispecial
    {w : ℕ → ℕ} {c0 L C : ℕ}
    (hbin : ∀ n < C + L, w n = c0 ∨ w n = c0 + 1)
    (hnobisp : ∀ i j m : ℕ, 2 ≤ m → i + m ≤ C + L → j + m ≤ C + L →
      w j = w i + 1 →
      (∀ t : ℕ, 1 ≤ t → t + 1 < m → w (j + t) = w (i + t)) →
      w (j + (m - 1)) = w (i + (m - 1)) + 1 → False) :
    prefixFactorCount w L C ≤ L + 1 := by
  induction L with
  | zero => exact prefixFactorCount_zero_le_one w C
  | succ k ih =>
      have ihk := ih (fun n hn => hbin n (by omega))
        (fun i j m hm hi hj => hnobisp i j m hm (by omega) (by omega))
      have hstep := prefixFactorCount_succ_le_of_no_bispecial (w := w) (c0 := c0) (k := k) (C := C)
        (fun n hn => hbin n (by omega))
        (fun i j m hm hi hj => hnobisp i j m hm (by omega) (by omega))
      omega

/-- **Derived Factor Complexity $\le L + 1$ for Shifted $1/3$-Window Carry Words
(`dubCarryNat_shifted_third_prefixFactorCount_le`)**:
Whenever $s \in [0, 2/3]$ and `dubY ξ (-s) n ≤ 1 / 3` for all $2 \le n \le C + L + 2$,
the shifted carry word `shiftSeq (dubCarryNat ξ (-s)) 2` has at most $L + 1$ distinct
length-$L$ factors on $0 \le r \le C$:
`prefixFactorCount (shiftSeq (dubCarryNat ξ (-s)) 2) L C ≤ L + 1`. -/
theorem dubCarryNat_shifted_third_prefixFactorCount_le
    {ξ s : ℝ} {L C : ℕ}
    (hs0 : 0 ≤ s) (hs23 : s ≤ (2 / 3 : ℝ))
    (hy : ∀ n, 2 ≤ n → n ≤ C + L + 2 → dubY ξ (-s) n ≤ (1 / 3 : ℝ)) :
    prefixFactorCount (shiftSeq (dubCarryNat ξ (-s)) 2) L C ≤ L + 1 := by
  set w := shiftSeq (dubCarryNat ξ (-s)) 2
  have hw_cast : ∀ n < C + L, (w n : ℤ) = dubCarry ξ (-s) (2 + n) + 2 := by
    intro n _
    unfold w shiftSeq dubCarryNat
    exact Int.toNat_of_nonneg (dubCarry_nonneg_add_two ξ (by linarith) (2 + n))
  apply prefixFactorCount_le_add_one_of_no_bispecial (c0 := 2)
  · intro n hn
    have h01 := (dubCarry_shifted_third_mem_zero_one hs0 hs23
      (hy (2 + n) (by omega) (by omega))
      (hy (2 + n + 1) (by omega) (by omega))).2
    have hcast := hw_cast n hn
    rcases h01 with h0 | h1 <;> omega
  · intro i j m hm hi hj hfirst hmid hlast
    have hcast_i := hw_cast i (by omega)
    have hcast_j := hw_cast j (by omega)
    have hcast_im := hw_cast (i + (m - 1)) (by omega)
    have hcast_jm := hw_cast (j + (m - 1)) (by omega)
    have hidx_im : 2 + (i + (m - 1)) = (2 + i) + (m - 1) := by omega
    have hidx_jm : 2 + (j + (m - 1)) = (2 + j) + (m - 1) := by omega
    apply dubCarry_shifted_third_no_bispecial_pair (ξ := ξ) (s := s)
      (i := 2 + i) (j := 2 + j) (m := m) hm
      (hy (2 + i) (by omega) (by omega))
      (hy ((2 + i) + m) (by omega) (by omega))
      (hy (2 + j) (by omega) (by omega))
      (hy ((2 + j) + m) (by omega) (by omega))
    · omega
    · intro t ht1 ht2
      have hmid_t := hmid t ht1 ht2
      have hci := hw_cast (i + t) (by omega)
      have hcj := hw_cast (j + t) (by omega)
      have hi_t : 2 + (i + t) = (2 + i) + t := by omega
      have hj_t : 2 + (j + t) = (2 + j) + t := by omega
      rw [hi_t] at hci
      rw [hj_t] at hcj
      omega
    · rw [hidx_im] at hcast_im
      rw [hidx_jm] at hcast_jm
      omega

/-- **Unconditional Explicit $5 W + 14$ Escape Bound for Every Shifted $1/3$-Window $[s, s + 1/3]$
(`shifted_third_unconditional_explicit_escape`)**:
For **every** $\xi \in [1, 2^W)$ and **every** real shift $s \in [0, 2/3]$, there exists
$n \le 5 W + 14$ such that $\{\xi (3/2)^n - s\} > 1/3$ (and in particular,
$\{\xi (3/2)^n\} \notin [s, s + 1/3]$). -/
theorem shifted_third_unconditional_explicit_escape {ξ s : ℝ} {W : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W)
    (hs0 : 0 ≤ s) (hs23 : s ≤ (2 / 3 : ℝ)) :
    (∃ n ≤ 5 * W + 14, (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n - s)) ∧
      (∃ n ≤ 5 * W + 14,
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < s ∨
          s + (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
  have h1 : ∃ n ≤ 5 * W + 14, (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n - s) := by
    by_contra hno
    push_neg at hno
    set L := (5 * W + 8) / 2 + 1
    have hcard : prefixFactorCount (shiftSeq (dubCarryNat ξ (-s)) 2) L (L + 1) ≤ L + 1 := by
      apply dubCarryNat_shifted_third_prefixFactorCount_le hs0 hs23
      intro n _ hn_hi
      unfold dubY
      have hsub : ξ * (3 / 2 : ℝ) ^ n + -s = ξ * (3 / 2 : ℝ) ^ n - s := by ring
      rw [hsub]
      exact hno n (by omega)
    have hbound := shifted_third_sturmian_explicit_escape_bound hξ1 hξW hs0 hs23 hcard
    omega
  refine ⟨h1, ?_⟩
  rcases h1 with ⟨n, hn_le, hn_gt⟩
  refine ⟨n, hn_le, ?_⟩
  by_contra hmem
  push_neg at hmem
  set f := Int.fract (ξ * (3 / 2 : ℝ) ^ n)
  have hf_lt1 : f < 1 := Int.fract_lt_one _
  have hdiff_eq :
      ξ * (3 / 2 : ℝ) ^ n - s =
        (⌊ξ * (3 / 2 : ℝ) ^ n⌋ : ℝ) + (f - s) := by
    unfold f
    have h := Int.self_sub_floor (ξ * (3 / 2 : ℝ) ^ n)
    linarith
  have hfl_eq : ⌊ξ * (3 / 2 : ℝ) ^ n - s⌋ = ⌊ξ * (3 / 2 : ℝ) ^ n⌋ := by
    rw [Int.floor_eq_iff]
    exact ⟨by linarith [hmem.1], by linarith [hf_lt1, hs0]⟩
  have hfract_eq : Int.fract (ξ * (3 / 2 : ℝ) ^ n - s) = f - s := by
    have h := Int.self_sub_floor (ξ * (3 / 2 : ℝ) ^ n - s)
    rw [hfl_eq] at h
    linarith
  linarith [hmem.2, hfract_eq, hn_gt]

/-- **Unconditional Dubickas (2009) Theorem 1 for Base $3/2$ (`shifted_third_unconditional_infinite_escape`)**:
For **every** real $\xi > 0$, **every** shift $s \in [0, 2/3]$, and **every** threshold
$N_0 \in \mathbb{N}$, there exists $n \ge N_0$ with $\{\xi (3/2)^n - s\} > 1/3$ and
$\{\xi (3/2)^n\} \notin [s, s + 1/3]$ (in particular, $Z_{3/2}(s, s + 1/3) = \emptyset$). -/
theorem shifted_third_unconditional_infinite_escape {ξ s : ℝ}
    (hξ : 0 < ξ) (hs0 : 0 ≤ s) (hs23 : s ≤ (2 / 3 : ℝ)) (N_0 : ℕ) :
    (∃ n ≥ N_0, (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n - s)) ∧
      (∃ n ≥ N_0,
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < s ∨
          s + (1 / 3 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  rcases shifted_third_unconditional_explicit_escape hge1 hltW hs0 hs23 with
    ⟨⟨m1, _, hm1⟩, ⟨m2, _, hm2⟩⟩
  have hmul1 : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m1 = ξ * (3 / 2 : ℝ) ^ (k + m1) := by
    rw [pow_add, mul_assoc]
  have hmul2 : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m2 = ξ * (3 / 2 : ℝ) ^ (k + m2) := by
    rw [pow_add, mul_assoc]
  exact ⟨⟨k + m1, by omega, by rwa [← hmul1]⟩, ⟨k + m2, by omega, by rwa [← hmul2]⟩⟩

/-- **Exact Dictionary Between Floor Residues $\lfloor t \rfloor \bmod m$ and Fractional Cells
(`floor_emod_eq_iff_fract_div_mem_cell`)**:
For every real $t \in \mathbb{R}$, modulus $m \ge 1$, and residue $0 \le r < m$:
`Int.fract (t / m) = ((⌊t⌋ % m : ℤ) : ℝ + Int.fract t) / m`, and
`⌊t⌋ % (m : ℤ) = (r : ℤ) ↔ (r : ℝ) / (m : ℝ) ≤ Int.fract (t / (m : ℝ)) ∧ Int.fract (t / (m : ℝ)) < (r + 1 : ℝ) / (m : ℝ)`. -/
theorem floor_emod_eq_iff_fract_div_mem_cell (t : ℝ) {m r : ℕ}
    (hm : 1 ≤ m) (_hr : r < m) :
    Int.fract (t / (m : ℝ)) =
      (((⌊t⌋ % (m : ℤ) : ℤ) : ℝ) + Int.fract t) / (m : ℝ) ∧
    (⌊t⌋ % (m : ℤ) = (r : ℤ) ↔
      ((r : ℝ) / (m : ℝ) ≤ Int.fract (t / (m : ℝ)) ∧
        Int.fract (t / (m : ℝ)) < ((r : ℝ) + 1) / (m : ℝ))) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hm_int_pos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  set q : ℤ := ⌊t⌋ / (m : ℤ)
  set rem : ℤ := ⌊t⌋ % (m : ℤ)
  have hdiv_mod : (m : ℤ) * q + rem = ⌊t⌋ := Int.ediv_add_emod ⌊t⌋ (m : ℤ)
  have hrem_lo : 0 ≤ rem := Int.emod_nonneg ⌊t⌋ (ne_of_gt hm_int_pos)
  have hrem_hi : rem < (m : ℤ) := Int.emod_lt_of_pos ⌊t⌋ hm_int_pos
  have hrem_le_m1 : (rem : ℝ) ≤ (m : ℝ) - 1 := by
    have h : rem ≤ (m : ℤ) - 1 := by omega
    exact_mod_cast h
  have hrem_real_lo : (0 : ℝ) ≤ (rem : ℝ) := by exact_mod_cast hrem_lo
  have hfr_lo : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hfr_hi : Int.fract t < 1 := Int.fract_lt_one t
  have ht_decomp : t = ((m : ℤ) * q + rem : ℤ) + Int.fract t := by
    rw [hdiv_mod]
    have h := Int.self_sub_floor t
    linarith
  have ht_div :
      t / (m : ℝ) = (q : ℝ) + ((rem : ℝ) + Int.fract t) / (m : ℝ) := by
    conv_lhs => rw [ht_decomp]
    push_cast
    field_simp [hm_ne]
    ring
  have hquot_bounds :
      0 ≤ ((rem : ℝ) + Int.fract t) / (m : ℝ) ∧
        ((rem : ℝ) + Int.fract t) / (m : ℝ) < 1 := by
    refine ⟨div_nonneg (by linarith) (le_of_lt hm_pos), ?_⟩
    rw [div_lt_iff₀ hm_pos]
    linarith
  have hfl_div : ⌊t / (m : ℝ)⌋ = q := by
    rw [Int.floor_eq_iff]
    exact ⟨by linarith [ht_div, hquot_bounds.1], by linarith [ht_div, hquot_bounds.2]⟩
  have hfract_div :
      Int.fract (t / (m : ℝ)) = ((rem : ℝ) + Int.fract t) / (m : ℝ) := by
    have h := Int.self_sub_floor (t / (m : ℝ))
    rw [hfl_div] at h
    linarith [ht_div, h]
  refine ⟨hfract_div, ?_⟩
  rw [hfract_div]
  constructor
  · intro hrem_eq
    have hcast : (rem : ℝ) = (r : ℝ) := by exact_mod_cast hrem_eq
    rw [hcast, div_le_div_iff_of_pos_right hm_pos, div_lt_div_iff_of_pos_right hm_pos]
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    rw [div_le_div_iff_of_pos_right hm_pos] at hlo
    rw [div_lt_div_iff_of_pos_right hm_pos] at hhi
    have h1 : (r : ℝ) - 1 < (rem : ℝ) := by linarith
    have h2 : (rem : ℝ) < (r : ℝ) + 1 := by linarith
    have hz1 : (r : ℤ) - 1 < rem := by exact_mod_cast h1
    have hz2 : rem < (r : ℤ) + 1 := by exact_mod_cast h2
    omega

/-- **Quantitative & Infinite-Horizon Non-Stabilization of Floor Residues $\lfloor \xi(3/2)^n \rfloor \bmod m$ for $m \ge 3$
(`floor_mod_non_stabilization_of_three_le`)**:
For every modulus $m \ge 3$ and residue $r \in \mathbb{Z}$:
1. **Quantitative $5 W + 14$ Escape Bound:** Whenever $0 \le r < m$ and $1 \le \xi / m < 2^W$,
   there exists $n \le 5 W + 14$ with $\lfloor \xi (3/2)^n \rfloor \bmod m \ne r$.
2. **Unconditional Infinite-Horizon Non-Stabilization:** For every real $\xi > 0$ and
   threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$ with
   $\lfloor \xi (3/2)^n \rfloor \bmod m \ne \lfloor \xi (3/2)^{N_0} \rfloor \bmod m$. -/
theorem floor_mod_non_stabilization_of_three_le {m : ℕ} (hm3 : 3 ≤ m) :
    (∀ {ξ : ℝ} {r W : ℕ}, r < m → (1 : ℝ) ≤ ξ / (m : ℝ) → ξ / (m : ℝ) < (2 : ℝ) ^ W →
      ∃ n ≤ 5 * W + 14, ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) ≠ (r : ℤ)) ∧
    (∀ {ξ : ℝ}, 0 < ξ → ∀ N_0 : ℕ,
      ∃ n ≥ N_0,
        ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) ≠ ⌊ξ * (3 / 2 : ℝ) ^ N_0⌋ % (m : ℤ)) := by
  have hm1 : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm3_real : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have h1 :
      ∀ {ξ : ℝ} {r W : ℕ}, r < m → (1 : ℝ) ≤ ξ / (m : ℝ) → ξ / (m : ℝ) < (2 : ℝ) ^ W →
        ∃ n ≤ 5 * W + 14, ⌊ξ * (3 / 2 : ℝ) ^ n⌋ % (m : ℤ) ≠ (r : ℤ) := by
    intro ξ r W hr hξ1 hξW
    set s : ℝ := min ((r : ℝ) / (m : ℝ)) (2 / 3 : ℝ)
    have hs0 : 0 ≤ s := le_min (div_nonneg (Nat.cast_nonneg r) (le_of_lt hm_pos)) (by norm_num)
    have hs23 : s ≤ (2 / 3 : ℝ) := min_le_right _ _
    have hs_le_rm : s ≤ (r : ℝ) / (m : ℝ) := min_le_left _ _
    have hrm1_le : ((r : ℝ) + 1) / (m : ℝ) ≤ s + (1 / 3 : ℝ) := by
      by_cases hlt : (r : ℝ) / (m : ℝ) ≤ (2 / 3 : ℝ)
      · have hs_eq : s = (r : ℝ) / (m : ℝ) := min_eq_left hlt
        rw [hs_eq, add_div]
        have hinv : (1 : ℝ) / (m : ℝ) ≤ (1 / 3 : ℝ) := by
          rw [div_le_iff₀ hm_pos]
          linarith
        linarith
      · push_neg at hlt
        have hs_eq : s = (2 / 3 : ℝ) := min_eq_right (le_of_lt hlt)
        have hr_le : (r : ℝ) + 1 ≤ (m : ℝ) := by
          have h : r + 1 ≤ m := by omega
          exact_mod_cast h
        have hdiv_le1 : ((r : ℝ) + 1) / (m : ℝ) ≤ 1 :=
          (div_le_iff₀ hm_pos).mpr (by linarith)
        rw [hs_eq]
        linarith
    obtain ⟨n, hn_le, hout⟩ :=
      (shifted_third_unconditional_explicit_escape hξ1 hξW hs0 hs23).2
    refine ⟨n, hn_le, ?_⟩
    intro hmod_eq
    have hdiv_eq : (ξ * (3 / 2 : ℝ) ^ n) / (m : ℝ) = (ξ / (m : ℝ)) * (3 / 2 : ℝ) ^ n := by
      ring
    have hcell :=
      (floor_emod_eq_iff_fract_div_mem_cell (ξ * (3 / 2 : ℝ) ^ n) hm1 hr).2.mp hmod_eq
    rw [hdiv_eq] at hcell
    rcases hout with hlt | hgt <;> linarith [hcell.1, hcell.2]
  refine ⟨h1, ?_⟩
  intro ξ hξ N_0
  have hξm_pos : 0 < ξ / (m : ℝ) := div_pos hξ hm_pos
  set rem0 : ℤ := ⌊ξ * (3 / 2 : ℝ) ^ N_0⌋ % (m : ℤ)
  set r : ℕ := Int.toNat rem0
  have hm_int_pos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm1
  have hrem0_lo : 0 ≤ rem0 := Int.emod_nonneg _ (ne_of_gt hm_int_pos)
  have hrem0_hi : rem0 < (m : ℤ) := Int.emod_lt_of_pos _ hm_int_pos
  have hr_cast : (r : ℤ) = rem0 := Int.toNat_of_nonneg hrem0_lo
  have hr_lt : r < m := by
    have h : (r : ℤ) < (m : ℤ) := by omega
    exact_mod_cast h
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξm_pos N_0
  have hge1' : (1 : ℝ) ≤ (ξ * (3 / 2 : ℝ) ^ k) / (m : ℝ) := by
    have h : (ξ * (3 / 2 : ℝ) ^ k) / (m : ℝ) = (ξ / (m : ℝ)) * (3 / 2 : ℝ) ^ k := by ring
    rwa [h]
  have hltW' : (ξ * (3 / 2 : ℝ) ^ k) / (m : ℝ) < (2 : ℝ) ^ W := by
    have h : (ξ * (3 / 2 : ℝ) ^ k) / (m : ℝ) = (ξ / (m : ℝ)) * (3 / 2 : ℝ) ^ k := by ring
    rwa [h]
  obtain ⟨d, _, hne⟩ := h1 hr_lt hge1' hltW'
  refine ⟨k + d, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ d = ξ * (3 / 2 : ℝ) ^ (k + d) := by
    rw [pow_add, mul_assoc]
  rw [← hmul, ← hr_cast]
  exact hne

/-! ## 4. Explicit $O(\log \xi)$ Escape Bounds for Union & Beyond-$1/3$ Confinement Sets -/

/-- **1-Step Periodicity of `dubCarry` on the Nearest-Integer Arc $[0, 1/5) \cup [4/5, 1)$
(`nearest_int_fifth_carry_const`)**:
Whenever $y_n = \{\xi (3/2)^n\} \in [0, 1/5) \cup [4/5, 1)$ and
$y_{n+1} = \{\xi (3/2)^{n+1}\} \in [0, 1/5) \cup [4/5, 1)$:
1. If $y_n < 1/5$, then `dubCarry ξ 0 n = 0` and $y_{n+1} < 1/5$.
2. If $4/5 \le y_n$, then `dubCarry ξ 0 n = 1` and $4/5 \le y_{n+1}$.
Consequently, if $y_k \in [0, 1/5) \cup [4/5, 1)$ for all $n \le k \le n + 2$, then
`dubCarry ξ 0 (n + 1) = dubCarry ξ 0 n`. -/
theorem nearest_int_fifth_carry_step {ξ : ℝ} {n : ℕ}
    (_hn : dubY ξ 0 n < (1 / 5 : ℝ) ∨ (4 / 5 : ℝ) ≤ dubY ξ 0 n)
    (hn1 : dubY ξ 0 (n + 1) < (1 / 5 : ℝ) ∨ (4 / 5 : ℝ) ≤ dubY ξ 0 (n + 1)) :
    (dubY ξ 0 n < (1 / 5 : ℝ) → dubCarry ξ 0 n = 0 ∧ dubY ξ 0 (n + 1) < (1 / 5 : ℝ)) ∧
      ((4 / 5 : ℝ) ≤ dubY ξ 0 n → dubCarry ξ 0 n = 1 ∧ (4 / 5 : ℝ) ≤ dubY ξ 0 (n + 1)) := by
  have hy0_lo := (dubY_bounds ξ 0 n).1
  have hy0_hi := (dubY_bounds ξ 0 n).2
  have hy1_lo := (dubY_bounds ξ 0 (n + 1)).1
  have hy1_hi := (dubY_bounds ξ 0 (n + 1)).2
  have hlin := dubCarry_eq_fract_linear ξ 0 n
  refine ⟨?_, ?_⟩
  · intro hlt0
    have hlt_one : (dubCarry ξ 0 n : ℝ) < 1 := by linarith
    have hint_lt1 : dubCarry ξ 0 n < 1 := by exact_mod_cast hlt_one
    rcases hn1 with hlt1 | hge1
    · have hgt_neg1 : (-1 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
      have hint_gt : -1 < dubCarry ξ 0 n := by exact_mod_cast hgt_neg1
      exact ⟨by omega, hlt1⟩
    · have hlt_neg1 : (dubCarry ξ 0 n : ℝ) < -1 := by linarith
      have hgt_neg2 : (-2 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
      have hint1 : dubCarry ξ 0 n < -1 := by exact_mod_cast hlt_neg1
      have hint2 : -2 < dubCarry ξ 0 n := by exact_mod_cast hgt_neg2
      omega
  · intro hge0
    have hgt_zero : (0 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
    have hint_gt0 : 0 < dubCarry ξ 0 n := by exact_mod_cast hgt_zero
    rcases hn1 with hlt1 | hge1
    · have hgt_two : (2 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
      have hlt_three : (dubCarry ξ 0 n : ℝ) < 3 := by linarith
      have hint1 : 2 < dubCarry ξ 0 n := by exact_mod_cast hgt_two
      have hint2 : dubCarry ξ 0 n < 3 := by exact_mod_cast hlt_three
      omega
    · have hlt_two : (dubCarry ξ 0 n : ℝ) < 2 := by linarith
      have hint_lt2 : dubCarry ξ 0 n < 2 := by exact_mod_cast hlt_two
      exact ⟨by omega, hge1⟩

/-- **Explicit $W + 5$ Finite-Horizon Escape Bound for $[0, 1/5) \cup [4/5, 1)$
(`nearest_int_fifth_explicit_escape`)**:
For **every** $\xi \in [1, 2^W)$, there exists an index $n \le W + 5$ such that
$\frac{1}{5} \le \{\xi (3/2)^n\} < \frac{4}{5}$ (in particular, $\|\xi (3/2)^n\| \ge 1/5$). -/
theorem nearest_int_fifth_explicit_escape {ξ : ℝ} {W : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    ∃ n ≤ W + 5,
      (1 / 5 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) ∧
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (4 / 5 : ℝ) := by
  by_contra hno
  have hmem : ∀ n ≤ W + 5, dubY ξ 0 n < (1 / 5 : ℝ) ∨ (4 / 5 : ℝ) ≤ dubY ξ 0 n := by
    intro n hn
    unfold dubY
    rw [add_zero]
    by_contra hmid
    push_neg at hmid
    exact hno ⟨n, hn, hmid.1, hmid.2⟩
  have hstep_eq : ∀ k ≤ W + 3, dubCarry ξ 0 (k + 1) = dubCarry ξ 0 k := by
    intro k hk
    have hk0 := hmem k (by omega)
    have hk1 := hmem (k + 1) (by omega)
    have hk2 := hmem (k + 2) (by omega)
    have hs0 := nearest_int_fifth_carry_step hk0 hk1
    have hs1 := nearest_int_fifth_carry_step hk1 hk2
    rcases hk0 with hlt | hge
    · rcases hs0.1 hlt with ⟨hc0, hlt1⟩
      rcases hs1.1 hlt1 with ⟨hc1, _⟩
      omega
    · rcases hs0.2 hge with ⟨hc0, hge1⟩
      rcases hs1.2 hge1 with ⟨hc1, _⟩
      omega
  have hmatch : ∀ t < W + 2, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (3 + t) := by
    intro t ht
    have hidx : 3 + t = (2 + t) + 1 := by omega
    rw [hidx, hstep_eq (2 + t) (by omega)]
  have hexp :=
    dubX_repeated_window_exp_bound (i := 2) (j := 3) (L := W + 2)
      hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
  have hpow : 3 ^ 3 * 2 ^ W < 2 ^ ((W + 2) + 3) := by
    calc
      3 ^ 3 * 2 ^ W = 27 * 2 ^ W := by ring
      _ < 32 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
      _ = 2 ^ ((W + 2) + 3) := by
        have h : (W + 2) + 3 = 5 + W := by omega
        rw [h, Nat.pow_add]
  omega

/-- **Infinite-Horizon Nearest-Integer Escape (`nearest_int_fifth_infinite_escape`)**:
For **every** real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$
with $\frac{1}{5} \le \{\xi (3/2)^n\} < \frac{4}{5}$. -/
theorem nearest_int_fifth_infinite_escape {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ n ≥ N_0,
      (1 / 5 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) ∧
        Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (4 / 5 : ℝ) := by
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  obtain ⟨m, _, hm_mid⟩ := nearest_int_fifth_explicit_escape hge1 hltW
  refine ⟨k + m, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = ξ * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-- **Human-Readable 5-Inequality Proof of Period-3 Carry Locking on $[1/6, 13/24)$
(`window_three_eighths_carry_period_three`)**:
Whenever $\frac{1}{6} \le y_n < \frac{13}{24}$ for all $0 \le n \le N$:
1. $s_n \in \{0, 1\}$ for all $n < N$,
2. `11` (`s_k = 1 ∧ s_{k+1} = 1`) is impossible for $k + 2 \le N$,
3. `000` (`s_k = 0 ∧ s_{k+1} = 0 ∧ s_{k+2} = 0`) is impossible for $k + 3 \le N$,
4. `101` (`s_k = 1 ∧ s_{k+1} = 0 ∧ s_{k+2} = 1`) is impossible for $k + 9 \le N$
   (via `10101`, `101001010`, and `101001001`), and
5. Therefore $s_{k+3} = s_k$ for all $k + 9 \le N$. -/
theorem window_three_eighths_carry_period_three {ξ : ℝ} {N : ℕ}
    (hmem : ∀ n ≤ N, (1 / 6 : ℝ) ≤ dubY ξ 0 n ∧ dubY ξ 0 n < (13 / 24 : ℝ)) :
    ∀ k, k + 10 ≤ N → dubCarry ξ 0 (k + 3) = dubCarry ξ 0 k := by
  have hbit : ∀ n < N, dubCarry ξ 0 n = 0 ∨ dubCarry ξ 0 n = 1 := by
    intro n hn
    have h0 := hmem n (by omega)
    have h1 := hmem (n + 1) (by omega)
    have hlin := dubCarry_eq_fract_linear ξ 0 n
    have hlo : (-1 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
    have hhi : (dubCarry ξ 0 n : ℝ) < (2 : ℝ) := by linarith
    have hlo_z : -1 < dubCarry ξ 0 n := by exact_mod_cast hlo
    have hhi_z : dubCarry ξ 0 n < 2 := by exact_mod_cast hhi
    omega
  have hno_11 : ∀ n, n + 2 ≤ N → ¬ (dubCarry ξ 0 n = 1 ∧ dubCarry ξ 0 (n + 1) = 1) := by
    intro n hn ⟨hs0, hs1⟩
    have hy0 := hmem n (by omega)
    have hy2 := hmem (n + 2) (by omega)
    have hl0 := dubCarry_eq_fract_linear ξ 0 n
    have hl1 := dubCarry_eq_fract_linear ξ 0 (n + 1)
    have hc0 : (dubCarry ξ 0 n : ℝ) = 1 := by exact_mod_cast hs0
    have hc1 : (dubCarry ξ 0 (n + 1) : ℝ) = 1 := by exact_mod_cast hs1
    linarith
  have hno_000 :
      ∀ n, n + 3 ≤ N →
        ¬ (dubCarry ξ 0 n = 0 ∧ dubCarry ξ 0 (n + 1) = 0 ∧ dubCarry ξ 0 (n + 2) = 0) := by
    intro n hn ⟨hs0, hs1, hs2⟩
    have hy0 := hmem n (by omega)
    have hy3 := hmem (n + 3) (by omega)
    have hl0 := dubCarry_eq_fract_linear ξ 0 n
    have hl1 := dubCarry_eq_fract_linear ξ 0 (n + 1)
    have hl2 := dubCarry_eq_fract_linear ξ 0 (n + 2)
    have hc0 : (dubCarry ξ 0 n : ℝ) = 0 := by exact_mod_cast hs0
    have hc1 : (dubCarry ξ 0 (n + 1) : ℝ) = 0 := by exact_mod_cast hs1
    have hc2 : (dubCarry ξ 0 (n + 2) : ℝ) = 0 := by exact_mod_cast hs2
    linarith
  have hno_101 :
      ∀ n, n + 9 ≤ N →
        ¬ (dubCarry ξ 0 n = 1 ∧ dubCarry ξ 0 (n + 1) = 0 ∧ dubCarry ξ 0 (n + 2) = 1) := by
    intro n hn ⟨hs0, hs1, hs2⟩
    have hs3 : dubCarry ξ 0 (n + 3) = 0 := by
      rcases hbit (n + 3) (by omega) with h0 | h1
      · exact h0
      · exfalso; exact hno_11 (n + 2) (by omega) ⟨hs2, h1⟩
    have hl0 := dubCarry_eq_fract_linear ξ 0 n
    have hl1 := dubCarry_eq_fract_linear ξ 0 (n + 1)
    have hl2 := dubCarry_eq_fract_linear ξ 0 (n + 2)
    have hl3 := dubCarry_eq_fract_linear ξ 0 (n + 3)
    have hl4 := dubCarry_eq_fract_linear ξ 0 (n + 4)
    have hc0 : (dubCarry ξ 0 n : ℝ) = 1 := by exact_mod_cast hs0
    have hc1 : (dubCarry ξ 0 (n + 1) : ℝ) = 0 := by exact_mod_cast hs1
    have hc2 : (dubCarry ξ 0 (n + 2) : ℝ) = 1 := by exact_mod_cast hs2
    have hc3 : (dubCarry ξ 0 (n + 3) : ℝ) = 0 := by exact_mod_cast hs3
    have hs4 : dubCarry ξ 0 (n + 4) = 0 := by
      rcases hbit (n + 4) (by omega) with h0 | h1
      · exact h0
      · exfalso
        have hc4 : (dubCarry ξ 0 (n + 4) : ℝ) = 1 := by exact_mod_cast h1
        have hy0 := hmem n (by omega)
        have hy5 := hmem (n + 5) (by omega)
        linarith
    have hs5 : dubCarry ξ 0 (n + 5) = 1 := by
      rcases hbit (n + 5) (by omega) with h0 | h1
      · exfalso; exact hno_000 (n + 3) (by omega) ⟨hs3, hs4, h0⟩
      · exact h1
    have hs6 : dubCarry ξ 0 (n + 6) = 0 := by
      rcases hbit (n + 6) (by omega) with h0 | h1
      · exact h0
      · exfalso; exact hno_11 (n + 5) (by omega) ⟨hs5, h1⟩
    have hl5 := dubCarry_eq_fract_linear ξ 0 (n + 5)
    have hl6 := dubCarry_eq_fract_linear ξ 0 (n + 6)
    have hl7 := dubCarry_eq_fract_linear ξ 0 (n + 7)
    have hl8 := dubCarry_eq_fract_linear ξ 0 (n + 8)
    have hc4 : (dubCarry ξ 0 (n + 4) : ℝ) = 0 := by exact_mod_cast hs4
    have hc5 : (dubCarry ξ 0 (n + 5) : ℝ) = 1 := by exact_mod_cast hs5
    have hc6 : (dubCarry ξ 0 (n + 6) : ℝ) = 0 := by exact_mod_cast hs6
    have hy0 := hmem n (by omega)
    have hy9 := hmem (n + 9) (by omega)
    rcases hbit (n + 7) (by omega) with hs7_0 | hs7_1
    · have hs8 : dubCarry ξ 0 (n + 8) = 1 := by
        rcases hbit (n + 8) (by omega) with h0 | h1
        · exfalso; exact hno_000 (n + 6) (by omega) ⟨hs6, hs7_0, h0⟩
        · exact h1
      have hc7 : (dubCarry ξ 0 (n + 7) : ℝ) = 0 := by exact_mod_cast hs7_0
      have hc8 : (dubCarry ξ 0 (n + 8) : ℝ) = 1 := by exact_mod_cast hs8
      linarith
    · have hs8 : dubCarry ξ 0 (n + 8) = 0 := by
        rcases hbit (n + 8) (by omega) with h0 | h1
        · exact h0
        · exfalso; exact hno_11 (n + 7) (by omega) ⟨hs7_1, h1⟩
      have hc7 : (dubCarry ξ 0 (n + 7) : ℝ) = 1 := by exact_mod_cast hs7_1
      have hc8 : (dubCarry ξ 0 (n + 8) : ℝ) = 0 := by exact_mod_cast hs8
      linarith
  intro k hk
  rcases hbit k (by omega) with hk0 | hk1
  · rcases hbit (k + 1) (by omega) with hk1_0 | hk1_1
    · have hk2_1 : dubCarry ξ 0 (k + 2) = 1 := by
        rcases hbit (k + 2) (by omega) with h0 | h1
        · exfalso; exact hno_000 k (by omega) ⟨hk0, hk1_0, h0⟩
        · exact h1
      rcases hbit (k + 3) (by omega) with hk3_0 | hk3_1
      · omega
      · exfalso; exact hno_11 (k + 2) (by omega) ⟨hk2_1, hk3_1⟩
    · have hk2_0 : dubCarry ξ 0 (k + 2) = 0 := by
        rcases hbit (k + 2) (by omega) with h0 | h1
        · exact h0
        · exfalso; exact hno_11 (k + 1) (by omega) ⟨hk1_1, h1⟩
      rcases hbit (k + 3) (by omega) with hk3_0 | hk3_1
      · omega
      · exfalso; exact hno_101 (k + 1) (by omega) ⟨hk1_1, hk2_0, hk3_1⟩
  · have hk1_0 : dubCarry ξ 0 (k + 1) = 0 := by
      rcases hbit (k + 1) (by omega) with h0 | h1
      · exact h0
      · exfalso; exact hno_11 k (by omega) ⟨hk1, h1⟩
    have hk2_0 : dubCarry ξ 0 (k + 2) = 0 := by
      rcases hbit (k + 2) (by omega) with h0 | h1
      · exact h0
      · exfalso; exact hno_101 k (by omega) ⟨hk1, hk1_0, h1⟩
    rcases hbit (k + 3) (by omega) with hk3_0 | hk3_1
    · exfalso; exact hno_000 (k + 1) (by omega) ⟨hk1_0, hk2_0, hk3_0⟩
    · omega

/-- **Explicit $W + 15$ Finite-Horizon Escape Bound for $[1/6, 13/24)$ (Length $3/8 > 1/3$)
(`window_three_eighths_explicit_escape`)**:
For **every** $\xi \in [1, 2^W)$, there exists an index $n \le W + 15$ such that
$\{\xi (3/2)^n\} \notin [1/6, 13/24)$. -/
theorem window_three_eighths_explicit_escape {ξ : ℝ} {W : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    ∃ n ≤ W + 15,
      Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (1 / 6 : ℝ) ∨
        (13 / 24 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) := by
  by_contra hno
  have hmem : ∀ n ≤ W + 15, (1 / 6 : ℝ) ≤ dubY ξ 0 n ∧ dubY ξ 0 n < (13 / 24 : ℝ) := by
    intro n hn
    unfold dubY
    rw [add_zero]
    by_contra h_out
    rcases lt_or_ge (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) (1 / 6 : ℝ) with hlt | hge
    · exact hno ⟨n, hn, Or.inl hlt⟩
    · have hge2 : (13 / 24 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) := by
        by_contra hlt2
        exact h_out ⟨hge, not_le.mp hlt2⟩
      exact hno ⟨n, hn, Or.inr hge2⟩
  have hper := window_three_eighths_carry_period_three hmem
  have hmatch : ∀ t < W + 3, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (5 + t) := by
    intro t ht
    have hidx : 5 + t = (2 + t) + 3 := by omega
    rw [hidx, hper (2 + t) (by omega)]
  have hexp :=
    dubX_repeated_window_exp_bound (i := 2) (j := 5) (L := W + 3)
      hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
  have hpow : 3 ^ 5 * 2 ^ W < 2 ^ ((W + 3) + 5) := by
    calc
      3 ^ 5 * 2 ^ W = 243 * 2 ^ W := by ring
      _ < 256 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
      _ = 2 ^ ((W + 3) + 5) := by
        have h : (W + 3) + 5 = 8 + W := by omega
        rw [h, Nat.pow_add]
  omega

/-- **Infinite-Horizon Emptiness of $Z_{3/2}(1/6, 13/24)$ (`window_three_eighths_infinite_escape`)**:
For **every** real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$
such that $\{\xi (3/2)^n\} \notin [1/6, 13/24)$. -/
theorem window_three_eighths_infinite_escape {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ n ≥ N_0,
      Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (1 / 6 : ℝ) ∨
        (13 / 24 : ℝ) ≤ Int.fract (ξ * (3 / 2 : ℝ) ^ n) := by
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  obtain ⟨m, _, hm_out⟩ := window_three_eighths_explicit_escape hge1 hltW
  refine ⟨k + m, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = ξ * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-- Predicate for membership in Dubickas's 2008 closed union
$[8/39, 18/39] \cup [21/39, 31/39]$ (total length $20/39 > 1/2$). -/
def InDubickas2008ClosedUnion (y : ℝ) : Prop :=
  ((8 / 39 : ℝ) ≤ y ∧ y ≤ (18 / 39 : ℝ)) ∨
    ((21 / 39 : ℝ) ≤ y ∧ y ≤ (31 / 39 : ℝ))

/-- **Single-Step Dichotomy on Dubickas's 2008 Closed Union (`dubickas2008_step_dichotomy`)**:
Whenever $y_k, y_{k+1} \in [8/39, 18/39] \cup [21/39, 31/39]$:
1. If $y_k \in [8/39, 18/39]$, then `dubCarry ξ 0 k = 0` and $2 y_{k+1} = 3 y_k$.
2. If $y_k \in [21/39, 31/39]$, then `dubCarry ξ 0 k = 1` and $2 y_{k+1} = 3 y_k - 1$. -/
theorem dubickas2008_step_dichotomy {ξ : ℝ} {k : ℕ}
    (_hk0 : InDubickas2008ClosedUnion (dubY ξ 0 k))
    (hk1 : InDubickas2008ClosedUnion (dubY ξ 0 (k + 1))) :
    (((8 / 39 : ℝ) ≤ dubY ξ 0 k ∧ dubY ξ 0 k ≤ (18 / 39 : ℝ)) →
      dubCarry ξ 0 k = 0 ∧ 2 * dubY ξ 0 (k + 1) = 3 * dubY ξ 0 k) ∧
    (((21 / 39 : ℝ) ≤ dubY ξ 0 k ∧ dubY ξ 0 k ≤ (31 / 39 : ℝ)) →
      dubCarry ξ 0 k = 1 ∧ 2 * dubY ξ 0 (k + 1) = 3 * dubY ξ 0 k - 1) := by
  have hlin := dubCarry_eq_fract_linear ξ 0 k
  have hy1_lo : (8 / 39 : ℝ) ≤ dubY ξ 0 (k + 1) := by
    rcases hk1 with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hy1_hi : dubY ξ 0 (k + 1) ≤ (31 / 39 : ℝ) := by
    rcases hk1 with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  refine ⟨?_, ?_⟩
  · rintro ⟨hlo, hhi⟩
    have h1 : (-1 : ℝ) < (dubCarry ξ 0 k : ℝ) := by linarith
    have h2 : (dubCarry ξ 0 k : ℝ) < (1 : ℝ) := by linarith
    have hz1 : -1 < dubCarry ξ 0 k := by exact_mod_cast h1
    have hz2 : dubCarry ξ 0 k < 1 := by exact_mod_cast h2
    have hc0 : dubCarry ξ 0 k = 0 := by omega
    have hc0_real : (dubCarry ξ 0 k : ℝ) = 0 := by exact_mod_cast hc0
    exact ⟨hc0, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    have h1 : (0 : ℝ) < (dubCarry ξ 0 k : ℝ) := by linarith
    have h2 : (dubCarry ξ 0 k : ℝ) < (2 : ℝ) := by linarith
    have hz1 : 0 < dubCarry ξ 0 k := by exact_mod_cast h1
    have hz2 : dubCarry ξ 0 k < 2 := by exact_mod_cast h2
    have hc1 : dubCarry ξ 0 k = 1 := by omega
    have hc1_real : (dubCarry ξ 0 k : ℝ) = 1 := by exact_mod_cast hc1
    exact ⟨hc1, by linarith⟩

/-- **Double-Zero / Double-One Endpoint Lock into the Rational 4-Cycle
(`dubickas2008_double_zero_or_one_locks_four_cycle`)**:
Whenever $y_{k-1}, y_k, y_{k+1}, y_{k+2} \in [8/39, 18/39] \cup [21/39, 31/39]$:
1. First, one step from $y_{k-1}$ confines $y_k$ to $[4/13, 9/13]$.
2. If $s_k = 0$ and $s_{k+1} = 0$, then $y_k = 4/13$ and $y_{k+1} = 6/13$.
3. If $s_k = 1$ and $s_{k+1} = 1$, then $y_k = 9/13$ and $y_{k+1} = 7/13$. -/
theorem dubickas2008_double_zero_or_one_locks_four_cycle {ξ : ℝ} {k : ℕ}
    (hkm1 : InDubickas2008ClosedUnion (dubY ξ 0 k))
    (hk0 : InDubickas2008ClosedUnion (dubY ξ 0 (k + 1)))
    (hk1 : InDubickas2008ClosedUnion (dubY ξ 0 (k + 2)))
    (hk2 : InDubickas2008ClosedUnion (dubY ξ 0 (k + 3))) :
    ((4 / 13 : ℝ) ≤ dubY ξ 0 (k + 1) ∧ dubY ξ 0 (k + 1) ≤ (9 / 13 : ℝ)) ∧
    (dubCarry ξ 0 (k + 1) = 0 ∧ dubCarry ξ 0 (k + 2) = 0 →
      dubY ξ 0 (k + 1) = (4 / 13 : ℝ) ∧ dubY ξ 0 (k + 2) = (6 / 13 : ℝ)) ∧
    (dubCarry ξ 0 (k + 1) = 1 ∧ dubCarry ξ 0 (k + 2) = 1 →
      dubY ξ 0 (k + 1) = (9 / 13 : ℝ) ∧ dubY ξ 0 (k + 2) = (7 / 13 : ℝ)) := by
  have hdm1 := dubickas2008_step_dichotomy hkm1 hk0
  have hd0 := dubickas2008_step_dichotomy hk0 hk1
  have hd1 := dubickas2008_step_dichotomy hk1 hk2
  have hyk1_bounds : (4 / 13 : ℝ) ≤ dubY ξ 0 (k + 1) ∧ dubY ξ 0 (k + 1) ≤ (9 / 13 : ℝ) := by
    rcases hkm1 with hleft | hright
    · have heq := (hdm1.1 hleft).2
      exact ⟨by linarith [hleft.1, heq], by linarith [hleft.2, heq]⟩
    · have heq := (hdm1.2 hright).2
      exact ⟨by linarith [hright.1, heq], by linarith [hright.2, heq]⟩
  refine ⟨hyk1_bounds, ?_, ?_⟩
  · rintro ⟨hs0, hs1⟩
    have hy0_left : (8 / 39 : ℝ) ≤ dubY ξ 0 (k + 1) ∧ dubY ξ 0 (k + 1) ≤ (18 / 39 : ℝ) := by
      rcases hk0 with hleft | hright
      · exact hleft
      · have h := (hd0.2 hright).1; omega
    have hy1_left : (8 / 39 : ℝ) ≤ dubY ξ 0 (k + 2) ∧ dubY ξ 0 (k + 2) ≤ (18 / 39 : ℝ) := by
      rcases hk1 with hleft | hright
      · exact hleft
      · have h := (hd1.2 hright).1; omega
    have heq0 := (hd0.1 hy0_left).2
    have hidx : k + 1 + 1 = k + 2 := by omega
    rw [hidx] at heq0
    exact ⟨by linarith [hyk1_bounds.1, hy1_left.2, heq0],
      by linarith [hyk1_bounds.1, hy1_left.2, heq0]⟩
  · rintro ⟨hs0, hs1⟩
    have hy0_right : (21 / 39 : ℝ) ≤ dubY ξ 0 (k + 1) ∧ dubY ξ 0 (k + 1) ≤ (31 / 39 : ℝ) := by
      rcases hk0 with hleft | hright
      · have h := (hd0.1 hleft).1; omega
      · exact hright
    have hy1_right : (21 / 39 : ℝ) ≤ dubY ξ 0 (k + 2) ∧ dubY ξ 0 (k + 2) ≤ (31 / 39 : ℝ) := by
      rcases hk1 with hleft | hright
      · have h := (hd1.1 hleft).1; omega
      · exact hright
    have heq0 := (hd0.2 hy0_right).2
    have hidx : k + 1 + 1 = k + 2 := by omega
    rw [hidx] at heq0
    exact ⟨by linarith [hyk1_bounds.2, hy1_right.1, heq0],
      by linarith [hyk1_bounds.2, hy1_right.1, heq0]⟩

/-- **Explicit $W + 8$ Escape Bound on the Open Union $(8/39, 18/39) \cup (21/39, 31/39)$
(`dubickas2008_open_union_explicit_escape`)**:
On the open interior $(8/39, 18/39) \cup (21/39, 31/39)$, neither `00` nor `11` can occur
from step $1$ onward, so $s_n$ strictly alternates ($s_{k+2} = s_k$) from step $1$, and
**every** $\xi \in [1, 2^W)$ exits $(8/39, 18/39) \cup (21/39, 31/39)$ within $N = W + 8$ steps. -/
theorem dubickas2008_open_union_explicit_escape {ξ : ℝ} {W : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    ∃ n ≤ W + 8,
      ¬ (((8 / 39 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n) ∧
            Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (18 / 39 : ℝ)) ∨
          ((21 / 39 : ℝ) < Int.fract (ξ * (3 / 2 : ℝ) ^ n) ∧
            Int.fract (ξ * (3 / 2 : ℝ) ^ n) < (31 / 39 : ℝ))) := by
  by_contra hno
  push_neg at hno
  have hclosed : ∀ n ≤ W + 8, InDubickas2008ClosedUnion (dubY ξ 0 n) := by
    intro n hn
    unfold InDubickas2008ClosedUnion dubY
    rw [add_zero]
    rcases hno n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨le_of_lt h1, le_of_lt h2⟩
    · exact Or.inr ⟨le_of_lt h1, le_of_lt h2⟩
  have hbit : ∀ n < W + 8, dubCarry ξ 0 n = 0 ∨ dubCarry ξ 0 n = 1 := by
    intro n hn
    have hd := dubickas2008_step_dichotomy (hclosed n (by omega)) (hclosed (n + 1) (by omega))
    rcases hclosed n (by omega) with hleft | hright
    · exact Or.inl (hd.1 hleft).1
    · exact Or.inr (hd.2 hright).1
  have hne_succ : ∀ k ≤ W + 5, dubCarry ξ 0 (k + 2) ≠ dubCarry ξ 0 (k + 1) := by
    intro k hk heq
    have hlock :=
      dubickas2008_double_zero_or_one_locks_four_cycle
        (hclosed k (by omega)) (hclosed (k + 1) (by omega))
        (hclosed (k + 2) (by omega)) (hclosed (k + 3) (by omega))
    have hopen := hno (k + 2) (by omega)
    have hyk2_eq : Int.fract (ξ * (3 / 2 : ℝ) ^ (k + 2)) = dubY ξ 0 (k + 2) := by
      unfold dubY; rw [add_zero]
    rcases hbit (k + 1) (by omega) with h0 | h1
    · have h0' : dubCarry ξ 0 (k + 2) = 0 := by omega
      have hy := (hlock.2.1 ⟨h0, h0'⟩).2
      rcases hopen with ⟨_, h2⟩ | ⟨h1', _⟩ <;> linarith
    · have h1' : dubCarry ξ 0 (k + 2) = 1 := by omega
      have hy := (hlock.2.2 ⟨h1, h1'⟩).2
      rcases hopen with ⟨_, h2⟩ | ⟨h1'', _⟩ <;> linarith
  have hper2 : ∀ k ≤ W + 4, dubCarry ξ 0 (k + 3) = dubCarry ξ 0 (k + 1) := by
    intro k hk
    have hne1 := hne_succ k (by omega)
    have hne2 := hne_succ (k + 1) (by omega)
    have hidx1 : (k + 1) + 1 = k + 2 := by omega
    have hidx2 : (k + 1) + 2 = k + 3 := by omega
    rw [hidx1, hidx2] at hne2
    rcases hbit (k + 1) (by omega) with b0 | b0 <;>
      rcases hbit (k + 2) (by omega) with b1 | b1 <;>
      rcases hbit (k + 3) (by omega) with b2 | b2 <;> omega
  have hmatch : ∀ t < W + 3, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (4 + t) := by
    intro t ht
    have h := hper2 (1 + t) (by omega)
    have hidx1 : (1 + t) + 1 = 2 + t := by omega
    have hidx2 : (1 + t) + 3 = 4 + t := by omega
    rw [hidx1, hidx2] at h
    exact h.symm
  have hexp :=
    dubX_repeated_window_exp_bound (i := 2) (j := 4) (L := W + 3)
      hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
  have hpow : 3 ^ 4 * 2 ^ W < 2 ^ ((W + 3) + 4) := by
    calc
      3 ^ 4 * 2 ^ W = 81 * 2 ^ W := by ring
      _ < 128 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
      _ = 2 ^ ((W + 3) + 4) := by
        have h : (W + 3) + 4 = 7 + W := by omega
        rw [h, Nat.pow_add]
  omega

/-- Once $y_m \in \{4/13, 6/13, 9/13, 7/13\}$ on Dubickas's 2008 closed union,
every subsequent point stays in the 4-cycle and `dubCarry ξ 0 (r + 4) = dubCarry ξ 0 r`. -/
private theorem dubickas2008_four_cycle_persistence {ξ : ℝ} {N m : ℕ}
    (hclosed : ∀ n ≤ N, InDubickas2008ClosedUnion (dubY ξ 0 n))
    (hm :
      dubY ξ 0 m = (4 / 13 : ℝ) ∨ dubY ξ 0 m = (6 / 13 : ℝ) ∨
        dubY ξ 0 m = (9 / 13 : ℝ) ∨ dubY ξ 0 m = (7 / 13 : ℝ)) :
    ∀ k, m ≤ k → k + 5 ≤ N → dubCarry ξ 0 (k + 4) = dubCarry ξ 0 k := by
  have hstep :
      ∀ r < N,
        (dubY ξ 0 r = (4 / 13 : ℝ) → dubCarry ξ 0 r = 0 ∧ dubY ξ 0 (r + 1) = (6 / 13 : ℝ)) ∧
        (dubY ξ 0 r = (6 / 13 : ℝ) → dubCarry ξ 0 r = 0 ∧ dubY ξ 0 (r + 1) = (9 / 13 : ℝ)) ∧
        (dubY ξ 0 r = (9 / 13 : ℝ) → dubCarry ξ 0 r = 1 ∧ dubY ξ 0 (r + 1) = (7 / 13 : ℝ)) ∧
        (dubY ξ 0 r = (7 / 13 : ℝ) → dubCarry ξ 0 r = 1 ∧ dubY ξ 0 (r + 1) = (4 / 13 : ℝ)) := by
    intro r hr
    have hd := dubickas2008_step_dichotomy (hclosed r (by omega)) (hclosed (r + 1) (by omega))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have hsub := hd.1 ⟨by linarith, by linarith⟩
      exact ⟨hsub.1, by linarith [hsub.2]⟩
    · intro h
      have hsub := hd.1 ⟨by linarith, by linarith⟩
      exact ⟨hsub.1, by linarith [hsub.2]⟩
    · intro h
      have hsub := hd.2 ⟨by linarith, by linarith⟩
      exact ⟨hsub.1, by linarith [hsub.2]⟩
    · intro h
      have hsub := hd.2 ⟨by linarith, by linarith⟩
      exact ⟨hsub.1, by linarith [hsub.2]⟩
  have hmem_all :
      ∀ k, m ≤ k → k ≤ N →
        dubY ξ 0 k = (4 / 13 : ℝ) ∨ dubY ξ 0 k = (6 / 13 : ℝ) ∨
          dubY ξ 0 k = (9 / 13 : ℝ) ∨ dubY ξ 0 k = (7 / 13 : ℝ) := by
    intro k hmk hkN
    induction k with
    | zero =>
        have hm0 : m = 0 := by omega
        subst hm0
        exact hm
    | succ k ih =>
        rcases Nat.eq_or_lt_of_le hmk with heq | hlt
        · subst heq; exact hm
        · have ihk := ih (by omega) (by omega)
          have hs := hstep k (by omega)
          rcases ihk with h4 | h6 | h9 | h7
          · exact Or.inr (Or.inl (hs.1 h4).2)
          · exact Or.inr (Or.inr (Or.inl (hs.2.1 h6).2))
          · exact Or.inr (Or.inr (Or.inr (hs.2.2.1 h9).2))
          · exact Or.inl (hs.2.2.2 h7).2
  intro k hmk hk5
  have hk_mem := hmem_all k hmk (by omega)
  have hs0 := hstep k (by omega)
  have hs1 := hstep (k + 1) (by omega)
  have hs2 := hstep (k + 2) (by omega)
  have hs3 := hstep (k + 3) (by omega)
  have hs4 := hstep (k + 4) (by omega)
  rcases hk_mem with h4 | h6 | h9 | h7
  · rcases hs0.1 h4 with ⟨c0, y1⟩
    rcases hs1.2.1 y1 with ⟨_, y2⟩
    rcases hs2.2.2.1 y2 with ⟨_, y3⟩
    rcases hs3.2.2.2 y3 with ⟨_, y4⟩
    rcases hs4.1 y4 with ⟨c4, _⟩
    omega
  · rcases hs0.2.1 h6 with ⟨c0, y1⟩
    rcases hs1.2.2.1 y1 with ⟨_, y2⟩
    rcases hs2.2.2.2 y2 with ⟨_, y3⟩
    rcases hs3.1 y3 with ⟨_, y4⟩
    rcases hs4.2.1 y4 with ⟨c4, _⟩
    omega
  · rcases hs0.2.2.1 h9 with ⟨c0, y1⟩
    rcases hs1.2.2.2 y1 with ⟨_, y2⟩
    rcases hs2.1 y2 with ⟨_, y3⟩
    rcases hs3.2.1 y3 with ⟨_, y4⟩
    rcases hs4.2.2.1 y4 with ⟨c4, _⟩
    omega
  · rcases hs0.2.2.2 h7 with ⟨c0, y1⟩
    rcases hs1.1 y1 with ⟨_, y2⟩
    rcases hs2.2.1 y2 with ⟨_, y3⟩
    rcases hs3.2.2.1 y3 with ⟨_, y4⟩
    rcases hs4.2.2.2 y4 with ⟨c4, _⟩
    omega

/-- **Explicit $3 W + 19$ Finite-Horizon Escape Bound for Dubickas's 2008 Closed Union
$[8/39, 18/39] \cup [21/39, 31/39]$ (Total Length $20/39 > 1/2$)
(`dubickas2008_closed_union_explicit_escape`)**:
For **every** $\xi \in [1, 2^W)$, there exists an index $n \le 3 W + 19$ such that
$\{\xi (3/2)^n\} \notin [8/39, 18/39] \cup [21/39, 31/39]$. -/
theorem dubickas2008_closed_union_explicit_escape {ξ : ℝ} {W : ℕ}
    (hξ1 : (1 : ℝ) ≤ ξ) (hξW : ξ < (2 : ℝ) ^ W) :
    ∃ n ≤ 3 * W + 19,
      ¬ InDubickas2008ClosedUnion (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
  by_contra hno
  push_neg at hno
  set N := 3 * W + 19
  have hclosed : ∀ n ≤ N, InDubickas2008ClosedUnion (dubY ξ 0 n) := by
    intro n hn
    unfold dubY
    rw [add_zero]
    exact hno n hn
  have hbit : ∀ n < N, dubCarry ξ 0 n = 0 ∨ dubCarry ξ 0 n = 1 := by
    intro n hn
    have hd := dubickas2008_step_dichotomy (hclosed n (by omega)) (hclosed (n + 1) (by omega))
    rcases hclosed n (by omega) with hleft | hright
    · exact Or.inl (hd.1 hleft).1
    · exact Or.inr (hd.2 hright).1
  by_cases hex_eq : ∃ k ≤ W + 4, dubCarry ξ 0 (k + 2) = dubCarry ξ 0 (k + 1)
  · rcases hex_eq with ⟨k, hk_le, heq⟩
    have hlock :=
      dubickas2008_double_zero_or_one_locks_four_cycle
        (hclosed k (by omega)) (hclosed (k + 1) (by omega))
        (hclosed (k + 2) (by omega)) (hclosed (k + 3) (by omega))
    have hmem_k1 :
        dubY ξ 0 (k + 1) = (4 / 13 : ℝ) ∨ dubY ξ 0 (k + 1) = (6 / 13 : ℝ) ∨
          dubY ξ 0 (k + 1) = (9 / 13 : ℝ) ∨ dubY ξ 0 (k + 1) = (7 / 13 : ℝ) := by
      rcases hbit (k + 1) (by omega) with h0 | h1
      · have h0' : dubCarry ξ 0 (k + 2) = 0 := by omega
        exact Or.inl (hlock.2.1 ⟨h0, h0'⟩).1
      · have h1' : dubCarry ξ 0 (k + 2) = 1 := by omega
        exact Or.inr (Or.inr (Or.inl (hlock.2.2 ⟨h1, h1'⟩).1))
    have hper4 := dubickas2008_four_cycle_persistence hclosed hmem_k1
    set i0 := W + 5
    set j0 := W + 9
    set L0 := 2 * W + 9
    have hmatch : ∀ t < L0, dubCarry ξ 0 (i0 + t) = dubCarry ξ 0 (j0 + t) := by
      intro t ht
      have hidx : j0 + t = (i0 + t) + 4 := by omega
      rw [hidx, hper4 (i0 + t) (by omega) (by omega)]
    have hexp :=
      dubX_repeated_window_exp_bound (i := i0) (j := j0) (L := L0)
        hξ1 hξW (by norm_num) (by norm_num) (by omega) (by omega) hmatch
    have h3_le_4 : 3 ^ j0 ≤ 4 ^ j0 := Nat.pow_le_pow_left (by decide) j0
    have h4_eq : 4 ^ j0 * 2 ^ W = 2 ^ (L0 + j0) := by
      have h4 : 4 ^ j0 = (2 ^ 2) ^ j0 := rfl
      rw [h4, ← Nat.pow_mul, ← Nat.pow_add]
      have hexp_eq : 2 * j0 + W = L0 + j0 := by omega
      rw [hexp_eq]
    have hle : 3 ^ j0 * 2 ^ W ≤ 2 ^ (L0 + j0) := by
      rw [← h4_eq]
      exact Nat.mul_le_mul_right (2 ^ W) h3_le_4
    omega
  · push_neg at hex_eq
    have hper2 : ∀ k ≤ W + 3, dubCarry ξ 0 (k + 3) = dubCarry ξ 0 (k + 1) := by
      intro k hk
      have hne1 := hex_eq k (by omega)
      have hne2 := hex_eq (k + 1) (by omega)
      have hidx1 : (k + 1) + 1 = k + 2 := by omega
      have hidx2 : (k + 1) + 2 = k + 3 := by omega
      rw [hidx1, hidx2] at hne2
      rcases hbit (k + 1) (by omega) with b0 | b0 <;>
        rcases hbit (k + 2) (by omega) with b1 | b1 <;>
        rcases hbit (k + 3) (by omega) with b2 | b2 <;> omega
    have hmatch : ∀ t < W + 3, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (4 + t) := by
      intro t ht
      have h := hper2 (1 + t) (by omega)
      have hidx1 : (1 + t) + 1 = 2 + t := by omega
      have hidx2 : (1 + t) + 3 = 4 + t := by omega
      rw [hidx1, hidx2] at h
      exact h.symm
    have hexp :=
      dubX_repeated_window_exp_bound (i := 2) (j := 4) (L := W + 3)
        hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
    have hpow : 3 ^ 4 * 2 ^ W < 2 ^ ((W + 3) + 4) := by
      calc
        3 ^ 4 * 2 ^ W = 81 * 2 ^ W := by ring
        _ < 128 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
        _ = 2 ^ ((W + 3) + 4) := by
          have h : (W + 3) + 4 = 7 + W := by omega
          rw [h, Nat.pow_add]
    omega

/-- **Dubickas (2008, Cor. 1.2) Closed-Union Theorem (`dubickas2008_closed_union_infinite_escape`)**:
For **every** real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$
such that $\{\xi (3/2)^n\} \notin [8/39, 18/39] \cup [21/39, 31/39]$ (of total length $20/39 > 1/2$). -/
theorem dubickas2008_closed_union_infinite_escape {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ n ≥ N_0,
      ¬ InDubickas2008ClosedUnion (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  obtain ⟨m, _, hm_out⟩ := dubickas2008_closed_union_explicit_escape hge1 hltW
  refine ⟨k + m, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = ξ * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-- **Direct $2^m$-Divisibility Lock on the Rational 4-Cycle of Dubickas (2008)
(`dubickas2008_four_cycle_two_pow_dvd`)**:
Whenever $y_r \in \{4/13, 6/13, 9/13, 7/13\}$ and the orbit remains in
$[8/39, 18/39] \cup [21/39, 31/39]$ for $m$ further steps ($r + m \le N$),
there exist integer numerators $v_r, v_{r+m} \in \{4, 6, 9, 7\}$ such that:
1. $2^m (13 x_{r+m} + v_{r+m}) = 3^m (13 x_r + v_r)$, and
2. $(2 : \mathbb{Z})^m \mid (13 x_r + v_r)$. -/
theorem dubickas2008_four_cycle_two_pow_dvd {ξ : ℝ} {N r m : ℕ}
    (hclosed : ∀ n ≤ N, InDubickas2008ClosedUnion (dubY ξ 0 n))
    (hr_mem :
      dubY ξ 0 r = (4 / 13 : ℝ) ∨ dubY ξ 0 r = (6 / 13 : ℝ) ∨
        dubY ξ 0 r = (9 / 13 : ℝ) ∨ dubY ξ 0 r = (7 / 13 : ℝ))
    (hrm : r + m ≤ N) :
    ∃ v_r v_rm : ℤ,
      (v_r = 4 ∨ v_r = 6 ∨ v_r = 9 ∨ v_r = 7) ∧
      (v_rm = 4 ∨ v_rm = 6 ∨ v_rm = 9 ∨ v_rm = 7) ∧
      (v_r : ℝ) = 13 * dubY ξ 0 r ∧
      (v_rm : ℝ) = 13 * dubY ξ 0 (r + m) ∧
      (2 : ℤ) ^ m * (13 * dubX ξ 0 (r + m) + v_rm) =
        (3 : ℤ) ^ m * (13 * dubX ξ 0 r + v_r) ∧
      (2 : ℤ) ^ m ∣ (13 * dubX ξ 0 r + v_r) := by
  have hstep :
      ∀ k < N,
        (dubY ξ 0 k = (4 / 13 : ℝ) → dubY ξ 0 (k + 1) = (6 / 13 : ℝ)) ∧
        (dubY ξ 0 k = (6 / 13 : ℝ) → dubY ξ 0 (k + 1) = (9 / 13 : ℝ)) ∧
        (dubY ξ 0 k = (9 / 13 : ℝ) → dubY ξ 0 (k + 1) = (7 / 13 : ℝ)) ∧
        (dubY ξ 0 k = (7 / 13 : ℝ) → dubY ξ 0 (k + 1) = (4 / 13 : ℝ)) := by
    intro k hk
    have hd := dubickas2008_step_dichotomy (hclosed k (by omega)) (hclosed (k + 1) (by omega))
    refine ⟨fun h => by linarith [(hd.1 ⟨by linarith, by linarith⟩).2],
      fun h => by linarith [(hd.1 ⟨by linarith, by linarith⟩).2],
      fun h => by linarith [(hd.2 ⟨by linarith, by linarith⟩).2],
      fun h => by linarith [(hd.2 ⟨by linarith, by linarith⟩).2]⟩
  have hmem_rm :
      dubY ξ 0 (r + m) = (4 / 13 : ℝ) ∨ dubY ξ 0 (r + m) = (6 / 13 : ℝ) ∨
        dubY ξ 0 (r + m) = (9 / 13 : ℝ) ∨ dubY ξ 0 (r + m) = (7 / 13 : ℝ) := by
    induction m with
    | zero => simpa using hr_mem
    | succ k ih =>
        have ihk := ih (by omega)
        have hs := hstep (r + k) (by omega)
        have hidx : r + (k + 1) = (r + k) + 1 := by omega
        rw [hidx]
        rcases ihk with h4 | h6 | h9 | h7
        · exact Or.inr (Or.inl (hs.1 h4))
        · exact Or.inr (Or.inr (Or.inl (hs.2.1 h6)))
        · exact Or.inr (Or.inr (Or.inr (hs.2.2.1 h9)))
        · exact Or.inl (hs.2.2.2 h7)
  have hex_v : ∀ n : ℕ,
      (dubY ξ 0 n = (4 / 13 : ℝ) ∨ dubY ξ 0 n = (6 / 13 : ℝ) ∨
        dubY ξ 0 n = (9 / 13 : ℝ) ∨ dubY ξ 0 n = (7 / 13 : ℝ)) →
      ∃ v : ℤ, (v = 4 ∨ v = 6 ∨ v = 9 ∨ v = 7) ∧ (v : ℝ) = 13 * dubY ξ 0 n := by
    intro n hn
    rcases hn with h4 | h6 | h9 | h7
    · exact ⟨4, Or.inl rfl, by rw [h4]; norm_num⟩
    · exact ⟨6, Or.inr (Or.inl rfl), by rw [h6]; norm_num⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inl rfl)), by rw [h9]; norm_num⟩
    · exact ⟨7, Or.inr (Or.inr (Or.inr rfl)), by rw [h7]; norm_num⟩
  obtain ⟨v_r, hvr_set, hvr_eq⟩ := hex_v r hr_mem
  obtain ⟨v_rm, hvrm_set, hvrm_eq⟩ := hex_v (r + m) hmem_rm
  have hr_sum := dubX_add_dubY ξ 0 r
  have hrm_sum := dubX_add_dubY ξ 0 (r + m)
  rw [add_zero] at hr_sum hrm_sum
  have hpow_split : (3 / 2 : ℝ) ^ (r + m) = (3 / 2 : ℝ) ^ r * ((3 : ℝ) ^ m / (2 : ℝ) ^ m) := by
    rw [pow_add, div_pow (3 : ℝ) (2 : ℝ) m]
  have h2m_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hreal_id :
      ((2 : ℤ) ^ m * (13 * dubX ξ 0 (r + m) + v_rm) : ℝ) =
        ((3 : ℤ) ^ m * (13 * dubX ξ 0 r + v_r) : ℝ) := by
    push_cast
    rw [hvr_eq, hvrm_eq]
    have h1 : 13 * (dubX ξ 0 r : ℝ) + 13 * dubY ξ 0 r = 13 * (ξ * (3 / 2 : ℝ) ^ r) := by
      linarith [hr_sum]
    have h2 :
        13 * (dubX ξ 0 (r + m) : ℝ) + 13 * dubY ξ 0 (r + m) =
          13 * (ξ * (3 / 2 : ℝ) ^ (r + m)) := by
      linarith [hrm_sum]
    rw [h1, h2, hpow_split]
    field_simp [h2m_ne]
    ring
  have hint_id :
      (2 : ℤ) ^ m * (13 * dubX ξ 0 (r + m) + v_rm) =
        (3 : ℤ) ^ m * (13 * dubX ξ 0 r + v_r) := by
    exact_mod_cast hreal_id
  have hdvd_nat : 2 ^ m ∣ 3 ^ m * (13 * dubX ξ 0 r + v_r).natAbs := by
    have habs :
        ((2 : ℤ) ^ m * (13 * dubX ξ 0 (r + m) + v_rm)).natAbs =
          ((3 : ℤ) ^ m * (13 * dubX ξ 0 r + v_r)).natAbs := by
      rw [hint_id]
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at habs
    exact ⟨(13 * dubX ξ 0 (r + m) + v_rm).natAbs, habs.symm⟩
  have hcop : Nat.Coprime (2 ^ m) (3 ^ m) :=
    ((by decide : Nat.Coprime 2 3).pow_left m).pow_right m
  have hdvd_abs : 2 ^ m ∣ (13 * dubX ξ 0 r + v_r).natAbs :=
    hcop.dvd_of_dvd_mul_left hdvd_nat
  have hdvd_int : (2 : ℤ) ^ m ∣ (13 * dubX ξ 0 r + v_r) := by
    simpa [Nat.cast_pow] using Int.ofNat_dvd_left.mpr hdvd_abs
  exact ⟨v_r, v_rm, hvr_set, hvrm_set, hvr_eq, hvrm_eq, hint_id, hdvd_int⟩

/-! ## 5. General Coprime Rational Bases $p/q > 1$: Multi-Step Carry Cancellation & $q^L$-Divisibility -/

/-- Shifted integer part $x_n = \lfloor \xi (p/q)^n + \theta \rfloor$ for an arbitrary
rational base $p / q$. -/
noncomputable def dubBaseX (p q : ℕ) (ξ θ : ℝ) (n : ℕ) : ℤ :=
  ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ n + θ⌋

/-- Shifted fractional part $y_n = \{\xi (p/q)^n + \theta\}$ for an arbitrary rational base $p / q$. -/
noncomputable def dubBaseY (p q : ℕ) (ξ θ : ℝ) (n : ℕ) : ℝ :=
  Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n + θ)

/-- General-base shifted carry word $s_n = q x_{n+1} - p x_n \in \mathbb{Z}$ (Dubickas 2009). -/
noncomputable def dubBaseCarry (p q : ℕ) (ξ θ : ℝ) (n : ℕ) : ℤ :=
  (q : ℤ) * dubBaseX p q ξ θ (n + 1) - (p : ℤ) * dubBaseX p q ξ θ n

/-- General-base multi-step carry accumulator $\sum_{t=0}^{m-1} p^{m-1-t} q^t w(n + t)$. -/
def dubBaseCarryAcc (p q : ℕ) (w : ℕ → ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => (p : ℤ) * dubBaseCarryAcc p q w n m + (q : ℤ) ^ m * w (n + m)

theorem dubBaseCarryAcc_eq_of_window_eq {p q : ℕ} {w : ℕ → ℤ} {i j L : ℕ}
    (hmatch : ∀ t < L, w (i + t) = w (j + t)) :
    dubBaseCarryAcc p q w i L = dubBaseCarryAcc p q w j L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      simp only [dubBaseCarryAcc]
      rw [ih (fun t ht => hmatch t (by omega)), hmatch L (Nat.lt_succ_self L)]

/-- **General-Base Multi-Step Integer-Part Summation Identity (`dubBaseX_multi_step_carry_identity`)**:
For any natural numbers $p, q \in \mathbb{N}$, reals $\xi, \theta \in \mathbb{R}$, and $n, m \in \mathbb{N}$:
`q^m * dubBaseX p q ξ θ (n + m) = p^m * dubBaseX p q ξ θ n + dubBaseCarryAcc p q (dubBaseCarry p q ξ θ) n m`. -/
theorem dubBaseX_multi_step_carry_identity (p q : ℕ) (ξ θ : ℝ) (n m : ℕ) :
    (q : ℤ) ^ m * dubBaseX p q ξ θ (n + m) =
      (p : ℤ) ^ m * dubBaseX p q ξ θ n +
        dubBaseCarryAcc p q (dubBaseCarry p q ξ θ) n m := by
  induction m with
  | zero => simp [dubBaseCarryAcc]
  | succ m ih =>
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      have hstep :
          (q : ℤ) * dubBaseX p q ξ θ ((n + m) + 1) =
            (p : ℤ) * dubBaseX p q ξ θ (n + m) + dubBaseCarry p q ξ θ (n + m) := by
        unfold dubBaseCarry
        ring
      calc
        (q : ℤ) ^ (m + 1) * dubBaseX p q ξ θ (n + (m + 1)) =
            (q : ℤ) ^ m * ((q : ℤ) * dubBaseX p q ξ θ ((n + m) + 1)) := by
          rw [hidx, pow_succ]
          ring
        _ = (q : ℤ) ^ m * ((p : ℤ) * dubBaseX p q ξ θ (n + m) + dubBaseCarry p q ξ θ (n + m)) := by
          rw [hstep]
        _ = (p : ℤ) * ((q : ℤ) ^ m * dubBaseX p q ξ θ (n + m)) +
              (q : ℤ) ^ m * dubBaseCarry p q ξ θ (n + m) := by
          ring
        _ = (p : ℤ) * ((p : ℤ) ^ m * dubBaseX p q ξ θ n +
              dubBaseCarryAcc p q (dubBaseCarry p q ξ θ) n m) +
              (q : ℤ) ^ m * dubBaseCarry p q ξ θ (n + m) := by
          rw [ih]
        _ = (p : ℤ) ^ (m + 1) * dubBaseX p q ξ θ n +
              dubBaseCarryAcc p q (dubBaseCarry p q ξ θ) n (m + 1) := by
          simp only [dubBaseCarryAcc, pow_succ]
          ring

/-- **General-Base Repeated Carry-Factor Cancellation & $q^L$-Divisibility
(`dubBaseX_repeat_factor_cancellation`)**:
For any coprime integers $\gcd(p, q) = 1$, whenever a length-$L$ factor of
`dubBaseCarry p q ξ θ` repeats at origins $i$ and $j$:
1. `(q : ℤ)^L * (dubBaseX p q ξ θ (j + L) - dubBaseX p q ξ θ (i + L)) = (p : ℤ)^L * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i)`, and
2. `(q : ℤ)^L ∣ (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i)`. -/
theorem dubBaseX_repeat_factor_cancellation {p q : ℕ} {ξ θ : ℝ} {i j L : ℕ}
    (hcop_pq : Nat.Coprime p q)
    (hmatch : ∀ t < L, dubBaseCarry p q ξ θ (i + t) = dubBaseCarry p q ξ θ (j + t)) :
    (q : ℤ) ^ L * (dubBaseX p q ξ θ (j + L) - dubBaseX p q ξ θ (i + L)) =
      (p : ℤ) ^ L * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i) ∧
    (q : ℤ) ^ L ∣ (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i) := by
  have hi := dubBaseX_multi_step_carry_identity p q ξ θ i L
  have hj := dubBaseX_multi_step_carry_identity p q ξ θ j L
  have hacc := dubBaseCarryAcc_eq_of_window_eq (p := p) (q := q) hmatch
  have heq :
      (q : ℤ) ^ L * (dubBaseX p q ξ θ (j + L) - dubBaseX p q ξ θ (i + L)) =
        (p : ℤ) ^ L * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i) := by
    linarith
  refine ⟨heq, ?_⟩
  have hdvd_nat : q ^ L ∣ p ^ L * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i).natAbs := by
    have habs :
        ((q : ℤ) ^ L * (dubBaseX p q ξ θ (j + L) - dubBaseX p q ξ θ (i + L))).natAbs =
          ((p : ℤ) ^ L * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i)).natAbs := by
      rw [heq]
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at habs
    exact ⟨(dubBaseX p q ξ θ (j + L) - dubBaseX p q ξ θ (i + L)).natAbs, habs.symm⟩
  have hcop : Nat.Coprime (q ^ L) (p ^ L) :=
    (hcop_pq.symm.pow_left L).pow_right L
  have hdvd_abs : q ^ L ∣ (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i).natAbs :=
    hcop.dvd_of_dvd_mul_left hdvd_nat
  simpa [Nat.cast_pow] using Int.ofNat_dvd_left.mpr hdvd_abs

/-- **General-Base Exponential & $(a, b)$ Power Cutoff for Repeated Shifted Carry Windows
(`dubBaseX_repeated_window_exp_and_power_cutoff`)**:
Let $2 \le q < p$ with $\gcd(p, q) = 1$. Whenever a length-$L$ factor of `dubBaseCarry p q ξ θ`
repeats at $i < j$ where $1 \le \operatorname{dubBaseX} p\ q\ \xi\ \theta\ j - \operatorname{dubBaseX} p\ q\ \xi\ \theta\ i$
and $q^j (\operatorname{dubBaseX} p\ q\ \xi\ \theta\ j - \operatorname{dubBaseX} p\ q\ \xi\ \theta\ i) < p^j \cdot q^W$:
1. $q^{L + j} < p^j \cdot q^W$,
2. For any integers $a, b \in \mathbb{N}$ with $1 \le b$ and $p^b < q^{a + b}$ (meaning $\frac{\log(p/q)}{\log q} < \frac{a}{b}$):
   $$b L + 1 \le a j + b W,$$
3. In particular, in Dubickas's regime $p < q^2$ ($a = 1, b = 1$), $L + 1 \le j + W$. -/
theorem dubBaseX_repeated_window_exp_and_power_cutoff {p q W i j L : ℕ} {ξ θ : ℝ}
    (hq2 : 2 ≤ q) (hcop_pq : Nat.Coprime p q)
    (hpos : 1 ≤ dubBaseX p q ξ θ j - dubBaseX p q ξ θ i)
    (hupper :
      (q : ℤ) ^ j * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i) <
        (p : ℤ) ^ j * (q : ℤ) ^ W)
    (hmatch : ∀ t < L, dubBaseCarry p q ξ θ (i + t) = dubBaseCarry p q ξ θ (j + t)) :
    q ^ (L + j) < p ^ j * q ^ W ∧
      (∀ {a b : ℕ}, 1 ≤ b → p ^ b < q ^ (a + b) → b * L + 1 ≤ a * j + b * W) ∧
      (p < q ^ 2 → L + 1 ≤ j + W) := by
  have hdvd := (dubBaseX_repeat_factor_cancellation hcop_pq hmatch).2
  have hle_int : (q : ℤ) ^ L ≤ dubBaseX p q ξ θ j - dubBaseX p q ξ θ i :=
    Int.le_of_dvd (by omega) hdvd
  have hqj_nonneg : (0 : ℤ) ≤ (q : ℤ) ^ j := by positivity
  have hmul_le :
      (q : ℤ) ^ j * (q : ℤ) ^ L ≤
        (q : ℤ) ^ j * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i) :=
    mul_le_mul_of_nonneg_left hle_int hqj_nonneg
  have hlt_int : (q : ℤ) ^ (L + j) < (p : ℤ) ^ j * (q : ℤ) ^ W := by
    have hcomm : (q : ℤ) ^ (L + j) = (q : ℤ) ^ j * (q : ℤ) ^ L := by
      rw [pow_add, mul_comm]
    linarith
  have hexp : q ^ (L + j) < p ^ j * q ^ W := by exact_mod_cast hlt_int
  have hpow_cut :
      ∀ {a b : ℕ}, 1 ≤ b → p ^ b < q ^ (a + b) → b * L + 1 ≤ a * j + b * W := by
    intro a b hb hpb
    have hpow_b : (q ^ (L + j)) ^ b < (p ^ j * q ^ W) ^ b :=
      Nat.pow_lt_pow_left hexp (by omega)
    have hpb_j : (p ^ j) ^ b ≤ (q ^ (a + b)) ^ j := by
      have hcomm : (p ^ j) ^ b = (p ^ b) ^ j := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
      rw [hcomm]
      exact Nat.pow_le_pow_left (le_of_lt hpb) j
    have hrhs : (p ^ j * q ^ W) ^ b ≤ q ^ ((a + b) * j + W * b) := by
      calc
        (p ^ j * q ^ W) ^ b = (p ^ j) ^ b * (q ^ W) ^ b := Nat.mul_pow _ _ _
        _ ≤ (q ^ (a + b)) ^ j * (q ^ W) ^ b := Nat.mul_le_mul_right _ hpb_j
        _ = q ^ ((a + b) * j + W * b) := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
    have hlt_q : q ^ ((L + j) * b) < q ^ ((a + b) * j + W * b) := by
      rw [← Nat.pow_mul] at hpow_b
      exact lt_of_lt_of_le hpow_b hrhs
    have hexp_lt : (L + j) * b < (a + b) * j + W * b := by
      by_contra hge
      have hle : q ^ ((a + b) * j + W * b) ≤ q ^ ((L + j) * b) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hring1 : (L + j) * b = b * L + b * j := by ring
    have hring2 : (a + b) * j + W * b = a * j + b * j + b * W := by ring
    omega
  refine ⟨hexp, hpow_cut, ?_⟩
  intro hpq2
  have h1 := hpow_cut (a := 1) (b := 1) le_rfl (by simpa using hpq2)
  omega

theorem dubBaseX_add_dubBaseY (p q : ℕ) (ξ θ : ℝ) (n : ℕ) :
    (dubBaseX p q ξ θ n : ℝ) + dubBaseY p q ξ θ n =
      ξ * ((p : ℝ) / (q : ℝ)) ^ n + θ := by
  unfold dubBaseX dubBaseY
  have h := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n + θ)
  linarith

theorem dubBaseY_bounds (p q : ℕ) (ξ θ : ℝ) (n : ℕ) :
    0 ≤ dubBaseY p q ξ θ n ∧ dubBaseY p q ξ θ n < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **General-Base Fractional-Part Formula for Shifted Carry Words (`dubBaseCarry_eq_fract_linear`)**:
Whenever $1 \le q$, for all $\xi, \theta \in \mathbb{R}$ and $n \in \mathbb{N}$:
`(dubBaseCarry p q ξ θ n : ℝ) = p * dubBaseY p q ξ θ n - q * dubBaseY p q ξ θ (n + 1) - (p - q) * θ`. -/
theorem dubBaseCarry_eq_fract_linear {p q : ℕ} (hq1 : 1 ≤ q) (ξ θ : ℝ) (n : ℕ) :
    (dubBaseCarry p q ξ θ n : ℝ) =
      (p : ℝ) * dubBaseY p q ξ θ n -
        (q : ℝ) * dubBaseY p q ξ θ (n + 1) - ((p : ℝ) - (q : ℝ)) * θ := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  unfold dubBaseCarry
  push_cast
  have h0 := dubBaseX_add_dubBaseY p q ξ θ n
  have h1 := dubBaseX_add_dubBaseY p q ξ θ (n + 1)
  rw [pow_succ] at h1
  have h1_mul :
      (q : ℝ) * ((dubBaseX p q ξ θ (n + 1) : ℝ) + dubBaseY p q ξ θ (n + 1)) =
        (p : ℝ) * (ξ * ((p : ℝ) / (q : ℝ)) ^ n) + (q : ℝ) * θ := by
    calc
      (q : ℝ) * ((dubBaseX p q ξ θ (n + 1) : ℝ) + dubBaseY p q ξ θ (n + 1)) =
          (q : ℝ) * (ξ * (((p : ℝ) / (q : ℝ)) ^ n * ((p : ℝ) / (q : ℝ))) + θ) := by
        rw [h1]
      _ = (p : ℝ) * (ξ * ((p : ℝ) / (q : ℝ)) ^ n) + (q : ℝ) * θ := by
        field_simp [hq_ne]
        ring
  linear_combination h1_mul - (p : ℝ) * h0

/-- **General-Base Multi-Step Fractional-Part Summation Identity (`dubBaseY_multi_step_carry_identity`)**:
Whenever $1 \le q$, for all $n, m \in \mathbb{N}$:
`q^m * dubBaseY p q ξ θ (n + m) = p^m * dubBaseY p q ξ θ n - dubBaseCarryAcc p q (dubBaseCarry p q ξ θ) n m - (p^m - q^m) * θ`. -/
theorem dubBaseY_multi_step_carry_identity {p q : ℕ} (hq1 : 1 ≤ q)
    (ξ θ : ℝ) (n m : ℕ) :
    (q : ℝ) ^ m * dubBaseY p q ξ θ (n + m) =
      (p : ℝ) ^ m * dubBaseY p q ξ θ n -
        (dubBaseCarryAcc p q (dubBaseCarry p q ξ θ) n m : ℝ) -
          ((p : ℝ) ^ m - (q : ℝ) ^ m) * θ := by
  induction m with
  | zero => simp [dubBaseCarryAcc]
  | succ m ih =>
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      have hstep := dubBaseCarry_eq_fract_linear (p := p) hq1 ξ θ (n + m)
      rw [hidx]
      push_cast [dubBaseCarryAcc]
      rw [pow_succ (q : ℝ) m, pow_succ (p : ℝ) m]
      linear_combination (p : ℝ) * ih + (q : ℝ) ^ m * hstep

/-- **Universal Two-Letter Carry Alphabet on General-Base Shifted $1/p$-Windows
(`dubBaseCarry_mem_two_letters`)**:
For **every** $1 \le q < p$ and **every** real shift $s \in \mathbb{R}$, if
`dubBaseY p q ξ (-s) n ≤ 1 / p` and `dubBaseY p q ξ (-s) (n + 1) ≤ 1 / p`, then
`dubBaseCarry p q ξ (-s) n` lies in the explicit two-element set
$\{\lfloor (p - q)s \rfloor,\, \lfloor (p - q)s \rfloor + 1\}$. -/
theorem dubBaseCarry_mem_two_letters {p q : ℕ} {ξ s : ℝ} {n : ℕ}
    (hq1 : 1 ≤ q) (hqp : q < p)
    (hyn : dubBaseY p q ξ (-s) n ≤ 1 / (p : ℝ))
    (hyn1 : dubBaseY p q ξ (-s) (n + 1) ≤ 1 / (p : ℝ)) :
    let k0 : ℤ := ⌊((p : ℝ) - (q : ℝ)) * s⌋
    (k0 ≤ dubBaseCarry p q ξ (-s) n ∧ dubBaseCarry p q ξ (-s) n ≤ k0 + 1) ∧
      (dubBaseCarry p q ξ (-s) n = k0 ∨ dubBaseCarry p q ξ (-s) n = k0 + 1) := by
  intro k0
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hq_nonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hqp_real : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
  have hqp_div : (q : ℝ) / (p : ℝ) < 1 := (div_lt_one hp_pos).mpr hqp_real
  have hy0_lo := (dubBaseY_bounds p q ξ (-s) n).1
  have hy1_lo := (dubBaseY_bounds p q ξ (-s) (n + 1)).1
  have hpy_hi : (p : ℝ) * dubBaseY p q ξ (-s) n ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hyn (le_of_lt hp_pos)
    have h2 : (p : ℝ) * (1 / (p : ℝ)) = 1 := mul_one_div_cancel (ne_of_gt hp_pos)
    linarith
  have hqy_hi : (q : ℝ) * dubBaseY p q ξ (-s) (n + 1) ≤ (q : ℝ) / (p : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hyn1 hq_nonneg
    ring_nf at h1 ⊢
    exact h1
  have hpy_lo : 0 ≤ (p : ℝ) * dubBaseY p q ξ (-s) n := mul_nonneg (le_of_lt hp_pos) hy0_lo
  have hqy_lo : 0 ≤ (q : ℝ) * dubBaseY p q ξ (-s) (n + 1) := mul_nonneg hq_nonneg hy1_lo
  have hlin := dubBaseCarry_eq_fract_linear (p := p) hq1 ξ (-s) n
  have hk0_le : (k0 : ℝ) ≤ ((p : ℝ) - (q : ℝ)) * s := Int.floor_le _
  have hk0_gt : ((p : ℝ) - (q : ℝ)) * s < (k0 : ℝ) + 1 := Int.lt_floor_add_one _
  have hlo_real : (k0 : ℝ) - 1 < (dubBaseCarry p q ξ (-s) n : ℝ) := by linarith
  have hhi_real : (dubBaseCarry p q ξ (-s) n : ℝ) < (k0 : ℝ) + 2 := by linarith
  have hlo_int : k0 - 1 < dubBaseCarry p q ξ (-s) n := by exact_mod_cast hlo_real
  have hhi_int : dubBaseCarry p q ξ (-s) n < k0 + 2 := by exact_mod_cast hhi_real
  exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- **General-Base No-Bispecial-Pair Theorem on Shifted $1/p$-Windows
(`dubBaseCarry_no_bispecial_pair`)**:
For any $1 \le q < p$ and $s \in \mathbb{R}$, if `dubBaseY p q ξ (-s)` is $\le 1/p$ at
$i, i+m, j, j+m$ ($m \ge 2$), then `dubBaseCarry p q ξ (-s)` cannot have a bispecial
pair of length $m$ at $i$ and $j$. -/
theorem dubBaseCarry_no_bispecial_pair {p q : ℕ} {ξ s : ℝ} {i j m : ℕ}
    (hq1 : 1 ≤ q) (hqp : q < p) (hm : 2 ≤ m)
    (_hyi : dubBaseY p q ξ (-s) i ≤ 1 / (p : ℝ))
    (hyim : dubBaseY p q ξ (-s) (i + m) ≤ 1 / (p : ℝ))
    (hyj : dubBaseY p q ξ (-s) j ≤ 1 / (p : ℝ))
    (_hyjm : dubBaseY p q ξ (-s) (j + m) ≤ 1 / (p : ℝ))
    (hfirst : dubBaseCarry p q ξ (-s) j = dubBaseCarry p q ξ (-s) i + 1)
    (hmid : ∀ t : ℕ, 1 ≤ t → t + 1 < m →
      dubBaseCarry p q ξ (-s) (j + t) = dubBaseCarry p q ξ (-s) (i + t))
    (hlast : dubBaseCarry p q ξ (-s) (j + (m - 1)) =
      dubBaseCarry p q ξ (-s) (i + (m - 1)) + 1) :
    False := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqp_real : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
  have hqp_div : (q : ℝ) / (p : ℝ) < 1 := (div_lt_one hp_pos).mpr hqp_real
  have hi_id := dubBaseY_multi_step_carry_identity (p := p) hq1 ξ (-s) i m
  have hj_id := dubBaseY_multi_step_carry_identity (p := p) hq1 ξ (-s) j m
  have hyi0 := (dubBaseY_bounds p q ξ (-s) i).1
  have hyjm0 := (dubBaseY_bounds p q ξ (-s) (j + m)).1
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hmid_eq :
      ∀ r ≤ k + 1, 1 ≤ r →
        dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) j r -
          dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) i r =
          (p : ℤ) ^ (r - 1) := by
    intro r hr_hi hr_lo
    induction r with
    | zero => omega
    | succ r ih =>
        rcases Nat.eq_zero_or_pos r with rfl | hr_pos
        · simp only [dubBaseCarryAcc, pow_zero, mul_zero, zero_add, one_mul, Nat.add_zero, Nat.sub_self]
          omega
        · have ihr := ih (by omega) hr_pos
          have hmid_r := hmid r hr_pos (by omega)
          change ((p : ℤ) * dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) j r +
              (q : ℤ) ^ r * dubBaseCarry p q ξ (-s) (j + r)) -
            ((p : ℤ) * dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) i r +
              (q : ℤ) ^ r * dubBaseCarry p q ξ (-s) (i + r)) =
            (p : ℤ) ^ r
          rw [hmid_r]
          have hr_eq : r = (r - 1) + 1 := by omega
          have hpowp : (p : ℤ) * (p : ℤ) ^ (r - 1) = (p : ℤ) ^ r := by
            conv_rhs => rw [hr_eq, pow_succ']
          linear_combination (p : ℤ) * ihr + hpowp
  have hk1 := hmid_eq (k + 1) le_rfl (by omega)
  simp only [Nat.add_sub_cancel] at hk1
  have hlast_sub : k + 2 - 1 = k + 1 := by omega
  rw [hlast_sub] at hlast
  have hacc_diff :
      dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) j (k + 2) -
        dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) i (k + 2) =
        (p : ℤ) ^ (k + 1) + (q : ℤ) ^ (k + 1) := by
    change ((p : ℤ) * dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) j (k + 1) +
        (q : ℤ) ^ (k + 1) * dubBaseCarry p q ξ (-s) (j + (k + 1))) -
      ((p : ℤ) * dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) i (k + 1) +
        (q : ℤ) ^ (k + 1) * dubBaseCarry p q ξ (-s) (i + (k + 1))) =
      (p : ℤ) ^ (k + 1) + (q : ℤ) ^ (k + 1)
    rw [hlast]
    have hpowp : (p : ℤ) * (p : ℤ) ^ k = (p : ℤ) ^ (k + 1) := by rw [pow_succ']
    linear_combination (p : ℤ) * hk1 + hpowp
  have hacc_real :
      (dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) j (k + 2) : ℝ) -
        (dubBaseCarryAcc p q (dubBaseCarry p q ξ (-s)) i (k + 2) : ℝ) =
        (p : ℝ) ^ (k + 1) + (q : ℝ) ^ (k + 1) := by
    exact_mod_cast hacc_diff
  have hpj_hi : (p : ℝ) ^ (k + 2) * dubBaseY p q ξ (-s) j ≤ (p : ℝ) ^ (k + 1) := by
    have hp_split : (p : ℝ) ^ (k + 2) = (p : ℝ) ^ (k + 1) * (p : ℝ) := by rw [pow_succ]
    have h1 : (p : ℝ) * dubBaseY p q ξ (-s) j ≤ 1 := by
      have hm1 := mul_le_mul_of_nonneg_left hyj (le_of_lt hp_pos)
      have hm2 : (p : ℝ) * (1 / (p : ℝ)) = 1 := mul_one_div_cancel (ne_of_gt hp_pos)
      linarith
    have hpk1_pos : (0 : ℝ) ≤ (p : ℝ) ^ (k + 1) := by positivity
    calc
      (p : ℝ) ^ (k + 2) * dubBaseY p q ξ (-s) j =
          (p : ℝ) ^ (k + 1) * ((p : ℝ) * dubBaseY p q ξ (-s) j) := by
        rw [hp_split]; ring
      _ ≤ (p : ℝ) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left h1 hpk1_pos
      _ = (p : ℝ) ^ (k + 1) := mul_one _
  have hpi_lo : (0 : ℝ) ≤ (p : ℝ) ^ (k + 2) * dubBaseY p q ξ (-s) i := by positivity
  have hqjm_lo : (0 : ℝ) ≤ (q : ℝ) ^ (k + 2) * dubBaseY p q ξ (-s) (j + (k + 2)) := by positivity
  have hqim_lt :
      (q : ℝ) ^ (k + 2) * dubBaseY p q ξ (-s) (i + (k + 2)) < (q : ℝ) ^ (k + 1) := by
    have hq_split : (q : ℝ) ^ (k + 2) = (q : ℝ) ^ (k + 1) * (q : ℝ) := by rw [pow_succ]
    have h1 : (q : ℝ) * dubBaseY p q ξ (-s) (i + (k + 2)) < 1 := by
      have hm1 := mul_le_mul_of_nonneg_left hyim (le_of_lt hq_pos)
      have hm2 : (q : ℝ) * (1 / (p : ℝ)) = (q : ℝ) / (p : ℝ) := by ring
      linarith
    have hqk1_pos : (0 : ℝ) < (q : ℝ) ^ (k + 1) := by positivity
    calc
      (q : ℝ) ^ (k + 2) * dubBaseY p q ξ (-s) (i + (k + 2)) =
          (q : ℝ) ^ (k + 1) * ((q : ℝ) * dubBaseY p q ξ (-s) (i + (k + 2))) := by
        rw [hq_split]; ring
      _ < (q : ℝ) ^ (k + 1) * 1 := mul_lt_mul_of_pos_left h1 hqk1_pos
      _ = (q : ℝ) ^ (k + 1) := mul_one _
  linarith

/-- Natural-number shifted carry word for base $p / q$:
`dubBaseCarryNat p q ξ s n = Int.toNat (dubBaseCarry p q ξ (-s) n - ⌊(p - q)s⌋)`. -/
noncomputable def dubBaseCarryNat (p q : ℕ) (ξ s : ℝ) (n : ℕ) : ℕ :=
  Int.toNat (dubBaseCarry p q ξ (-s) n - ⌊((p : ℝ) - (q : ℝ)) * s⌋)

/-- **Derived Factor Complexity $\le L + 1$ for General-Base Shifted $1/p$-Windows
(`dubBaseCarryNat_prefixFactorCount_le`)**:
For **every** $1 \le q < p$ and **every** real shift $s \in \mathbb{R}$, whenever
`dubBaseY p q ξ (-s) n ≤ 1 / p` for all $n_0 \le n \le n_0 + C + L$, the shifted carry word
`shiftSeq (dubBaseCarryNat p q ξ s) n_0` has at most $L + 1$ distinct length-$L$ factors
on $0 \le r \le C$. -/
theorem dubBaseCarryNat_prefixFactorCount_le
    {p q : ℕ} {ξ s : ℝ} {n_0 L C : ℕ}
    (hq1 : 1 ≤ q) (hqp : q < p)
    (hy : ∀ n, n_0 ≤ n → n ≤ n_0 + C + L → dubBaseY p q ξ (-s) n ≤ 1 / (p : ℝ)) :
    prefixFactorCount (shiftSeq (dubBaseCarryNat p q ξ s) n_0) L C ≤ L + 1 := by
  set w := shiftSeq (dubBaseCarryNat p q ξ s) n_0
  set k0 : ℤ := ⌊((p : ℝ) - (q : ℝ)) * s⌋
  have hmem01 : ∀ n < C + L,
      (w n : ℤ) = dubBaseCarry p q ξ (-s) (n_0 + n) - k0 ∧
        (w n = 0 ∨ w n = 1) := by
    intro n hn
    have h2 := dubBaseCarry_mem_two_letters hq1 hqp
      (hy (n_0 + n) (by omega) (by omega))
      (hy (n_0 + n + 1) (by omega) (by omega))
    dsimp [k0] at h2
    unfold w shiftSeq dubBaseCarryNat
    have hnonneg : 0 ≤ dubBaseCarry p q ξ (-s) (n_0 + n) - k0 := by omega
    have hcast := Int.toNat_of_nonneg hnonneg
    refine ⟨hcast, ?_⟩
    rcases h2.2 with h0 | h1 <;> omega
  apply prefixFactorCount_le_add_one_of_no_bispecial (c0 := 0)
  · intro n hn
    exact (hmem01 n hn).2
  · intro i j m hm hi hj hfirst hmid hlast
    have hci := (hmem01 i (by omega)).1
    have hcj := (hmem01 j (by omega)).1
    have hcim := (hmem01 (i + (m - 1)) (by omega)).1
    have hcjm := (hmem01 (j + (m - 1)) (by omega)).1
    have hidx_im : n_0 + (i + (m - 1)) = (n_0 + i) + (m - 1) := by omega
    have hidx_jm : n_0 + (j + (m - 1)) = (n_0 + j) + (m - 1) := by omega
    rw [hidx_im] at hcim
    rw [hidx_jm] at hcjm
    apply dubBaseCarry_no_bispecial_pair hq1 hqp hm
      (hy (n_0 + i) (by omega) (by omega))
      (hy ((n_0 + i) + m) (by omega) (by omega))
      (hy (n_0 + j) (by omega) (by omega))
      (hy ((n_0 + j) + m) (by omega) (by omega))
    · omega
    · intro t ht1 ht2
      have hmid_t := hmid t ht1 ht2
      have hcit := (hmem01 (i + t) (by omega)).1
      have hcjt := (hmem01 (j + t) (by omega)).1
      have hi_t : n_0 + (i + t) = (n_0 + i) + t := by omega
      have hj_t : n_0 + (j + t) = (n_0 + j) + t := by omega
      rw [hi_t] at hcit
      rw [hj_t] at hcjt
      omega
    · omega

/-- General-base strict monotonicity and upper bound on `dubBaseX`:
Whenever $1 \le q < p$, $2 + \frac{2q}{p - q} \le \xi < q^W$, and $-1 \le \theta \le 0$,
for all $0 \le i < j$:
1. $1 \le \operatorname{dubBaseX} p\ q\ \xi\ \theta\ i$,
2. $1 \le \operatorname{dubBaseX} p\ q\ \xi\ \theta\ j - \operatorname{dubBaseX} p\ q\ \xi\ \theta\ i$, and
3. $q^j (\operatorname{dubBaseX} p\ q\ \xi\ \theta\ j - \operatorname{dubBaseX} p\ q\ \xi\ \theta\ i) < p^j \cdot q^W$. -/
theorem dubBaseX_strict_step_growth {p q W i j : ℕ} {ξ θ : ℝ}
    (hq1 : 1 ≤ q) (hqp : q < p)
    (hξ_lo : (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ)
    (hξW : ξ < (q : ℝ) ^ W)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0)
    (hij : i < j) :
    1 ≤ dubBaseX p q ξ θ i ∧
      1 ≤ dubBaseX p q ξ θ j - dubBaseX p q ξ θ i ∧
      (q : ℤ) ^ j * (dubBaseX p q ξ θ j - dubBaseX p q ξ θ i) <
        (p : ℤ) ^ j * (q : ℤ) ^ W := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hqp_real : (q : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : q + 1 ≤ p)
  have hpq_diff : (1 : ℝ) ≤ (p : ℝ) - (q : ℝ) := by linarith
  have hpq_pos : (0 : ℝ) < (p : ℝ) - (q : ℝ) := by linarith
  have hdiv_pos : (0 : ℝ) < (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) := by positivity
  have hξ_ge2 : (2 : ℝ) ≤ ξ := by linarith
  have hξ_ge_div : (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ := by linarith
  have hr_ge1 : (1 : ℝ) ≤ (p : ℝ) / (q : ℝ) := (one_le_div hq_pos).mpr (by linarith)
  have hpow_i_ge1 : (1 : ℝ) ≤ ((p : ℝ) / (q : ℝ)) ^ i := one_le_pow₀ hr_ge1
  have hxi_ge1 : 1 ≤ dubBaseX p q ξ θ i := by
    unfold dubBaseX
    exact Int.le_floor.mpr (by push_cast; nlinarith)
  have hpow_step :
      ((p : ℝ) / (q : ℝ)) ^ i * ((p : ℝ) / (q : ℝ)) ≤ ((p : ℝ) / (q : ℝ)) ^ j := by
    obtain ⟨d, hd⟩ : ∃ d, j = (i + 1) + d := ⟨j - (i + 1), by omega⟩
    rw [hd, pow_add, pow_succ]
    have hpos : (0 : ℝ) ≤ ((p : ℝ) / (q : ℝ)) ^ i * ((p : ℝ) / (q : ℝ)) := by positivity
    have hpow_d : (1 : ℝ) ≤ ((p : ℝ) / (q : ℝ)) ^ d := one_le_pow₀ hr_ge1
    nlinarith
  have hdiff_ge2 :
      (2 : ℝ) ≤ (ξ * ((p : ℝ) / (q : ℝ)) ^ j + θ) - (ξ * ((p : ℝ) / (q : ℝ)) ^ i + θ) := by
    have h1 : ξ * (((p : ℝ) / (q : ℝ)) - 1) ≥ 2 := by
      have hsub : (p : ℝ) / (q : ℝ) - 1 = ((p : ℝ) - (q : ℝ)) / (q : ℝ) := by
        field_simp [ne_of_gt hq_pos]
      rw [hsub]
      have hmul := mul_le_mul_of_nonneg_right hξ_ge_div (le_of_lt (div_pos hpq_pos hq_pos))
      have hcancel :
          ((2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ))) * (((p : ℝ) - (q : ℝ)) / (q : ℝ)) = 2 := by
        field_simp [ne_of_gt hpq_pos, ne_of_gt hq_pos]
      linarith
    have h2 :
        ξ * ((p : ℝ) / (q : ℝ)) ^ i * (((p : ℝ) / (q : ℝ)) - 1) ≤
          ξ * ((p : ℝ) / (q : ℝ)) ^ j - ξ * ((p : ℝ) / (q : ℝ)) ^ i := by
      have hm := mul_le_mul_of_nonneg_left hpow_step (by linarith : (0 : ℝ) ≤ ξ)
      linarith
    nlinarith
  have hfl_i_le : (dubBaseX p q ξ θ i : ℝ) ≤ ξ * ((p : ℝ) / (q : ℝ)) ^ i + θ :=
    Int.floor_le _
  have hfl_j_gt : ξ * ((p : ℝ) / (q : ℝ)) ^ j + θ - 1 < (dubBaseX p q ξ θ j : ℝ) := by
    have h := Int.lt_floor_add_one (ξ * ((p : ℝ) / (q : ℝ)) ^ j + θ)
    unfold dubBaseX
    linarith
  have hdiff_pos : 0 < dubBaseX p q ξ θ j - dubBaseX p q ξ θ i := by
    have hreal : ((0 : ℤ) : ℝ) < ((dubBaseX p q ξ θ j - dubBaseX p q ξ θ i : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hreal
  have hfl_j_le : (dubBaseX p q ξ θ j : ℝ) ≤ ξ * ((p : ℝ) / (q : ℝ)) ^ j + θ :=
    Int.floor_le _
  have hxi_real_ge1 : (1 : ℝ) ≤ (dubBaseX p q ξ θ i : ℝ) := by exact_mod_cast hxi_ge1
  have hqj_pos : (0 : ℝ) < (q : ℝ) ^ j := by positivity
  have hpj_pos : (0 : ℝ) < (p : ℝ) ^ j := by positivity
  have hupper_real :
      (q : ℝ) ^ j * ((dubBaseX p q ξ θ j - dubBaseX p q ξ θ i : ℤ) : ℝ) <
        (p : ℝ) ^ j * (q : ℝ) ^ W := by
    push_cast
    have h1 : (dubBaseX p q ξ θ j : ℝ) - (dubBaseX p q ξ θ i : ℝ) < ξ * ((p : ℝ) / (q : ℝ)) ^ j := by
      linarith
    have hdiv_pow_pos : (0 : ℝ) < ((p : ℝ) / (q : ℝ)) ^ j := by positivity
    have h2 : ξ * ((p : ℝ) / (q : ℝ)) ^ j < (q : ℝ) ^ W * ((p : ℝ) ^ j / (q : ℝ) ^ j) := by
      rw [← div_pow]
      exact mul_lt_mul_of_pos_right hξW hdiv_pow_pos
    have h3 :
        (q : ℝ) ^ j * ((q : ℝ) ^ W * ((p : ℝ) ^ j / (q : ℝ) ^ j)) =
          (p : ℝ) ^ j * (q : ℝ) ^ W := by
      field_simp [ne_of_gt hqj_pos]
      ring
    have h4 := mul_lt_mul_of_pos_left (lt_trans h1 h2) hqj_pos
    linarith
  exact ⟨hxi_ge1, by omega, by exact_mod_cast hupper_real⟩

private theorem pow_succ_add_mul_pow_le (p L : ℕ) :
    p ^ (L + 1) + L * p ^ L ≤ (p + 1) ^ (L + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Nat.pow_succ (p + 1) (L + 1)]
      have hmul :
          (p ^ (L + 1) + L * p ^ L) * (p + 1) ≤ (p + 1) ^ (L + 1) * (p + 1) :=
        Nat.mul_le_mul_right (p + 1) ih
      have hexp :
          (p ^ (L + 1) + L * p ^ L) * (p + 1) =
            p ^ (L + 1 + 1) + (L + 1) * p ^ (L + 1) + L * p ^ L := by
        rw [Nat.pow_succ p (L + 1), Nat.pow_succ p L]
        ring
      omega

/-- **Full General-Base Dubickas (2009) Theorem 1 with Explicit Escape Bound
(`dubickas2009_general_base_explicit_and_infinite_escape`)**:
Let $2 \le q < p < q^2$ with $\gcd(p, q) = 1$, and let $0 \le s \le 1 - 1/p$.
1. **Explicit Finite-Horizon Escape Bound:** Whenever $2 + \frac{2q}{p - q} \le \xi < q^W$,
   there exists an index $n \le p^2 \cdot q^{2 W} + 3$ such that $\{\xi (p/q)^n - s\} > 1/p$ and
   $\{\xi (p/q)^n\} \notin [s, s + 1/p]$.
2. **Unconditional Infinite-Horizon Escape (Dubickas 2009, Theorem 1):** For every real
   $\xi > 0$ and threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$ such that
   $\{\xi (p/q)^n\} \notin [s, s + 1/p]$ ($Z_{p/q}(s, s + 1/p) = \emptyset$). -/
theorem dubickas2009_general_base_explicit_and_infinite_escape
    {p q : ℕ} {s : ℝ}
    (hq2 : 2 ≤ q) (hqp : q < p) (hpq2 : p < q ^ 2) (hcop_pq : Nat.Coprime p q)
    (hs0 : 0 ≤ s) (hs_hi : s + 1 / (p : ℝ) ≤ 1) :
    (∀ {ξ : ℝ} {W : ℕ},
      (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ → ξ < (q : ℝ) ^ W →
      (∃ n ≤ p ^ 2 * q ^ (2 * W) + 3, 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s)) ∧
      (∃ n ≤ p ^ 2 * q ^ (2 * W) + 3,
        Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) < s ∨
          s + 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n))) ∧
    (∀ {ξ : ℝ}, 0 < ξ → ∀ N_0 : ℕ,
      ∃ n ≥ N_0,
        Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) < s ∨
          s + 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n)) := by
  have hq1 : 1 ≤ q := by omega
  have hexplicit :
      ∀ {ξ : ℝ} {W : ℕ},
        (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ → ξ < (q : ℝ) ^ W →
        (∃ n ≤ p ^ 2 * q ^ (2 * W) + 3, 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s)) ∧
        (∃ n ≤ p ^ 2 * q ^ (2 * W) + 3,
          Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) < s ∨
            s + 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n)) := by
    intro ξ W hξ_lo hξW
    have h1 : ∃ n ≤ p ^ 2 * q ^ (2 * W) + 3, 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s) := by
      by_contra hno
      push_neg at hno
      set L := p ^ 2 * q ^ (2 * W) / 2 + 1
      set C := L + 1
      have h2L_gt : p ^ 2 * q ^ (2 * W) < 2 * L := by omega
      have hCL_le : 0 + C + L ≤ p ^ 2 * q ^ (2 * W) + 3 := by omega
      have hy_le : ∀ n ≤ p ^ 2 * q ^ (2 * W) + 3, dubBaseY p q ξ (-s) n ≤ 1 / (p : ℝ) := by
        intro n hn
        unfold dubBaseY
        have hsub : ξ * ((p : ℝ) / (q : ℝ)) ^ n + -s = ξ * ((p : ℝ) / (q : ℝ)) ^ n - s := by ring
        rw [hsub]
        exact hno n hn
      have hcard :
          prefixFactorCount (shiftSeq (dubBaseCarryNat p q ξ s) 0) L C ≤ C := by
        apply dubBaseCarryNat_prefixFactorCount_le hq1 hqp
        intro n _ hn_hi
        exact hy_le n (le_trans hn_hi hCL_le)
      obtain ⟨r1, r2, hr12, hr2C, hmatch_nat⟩ :=
        exists_repeated_subword_of_prefixFactorCount_le
          (shiftSeq (dubBaseCarryNat p q ξ s) 0) L C hcard
      set k0 : ℤ := ⌊((p : ℝ) - (q : ℝ)) * s⌋
      have hmatch :
          ∀ t < L, dubBaseCarry p q ξ (-s) (r1 + t) = dubBaseCarry p q ξ (-s) (r2 + t) := by
        intro t ht
        have hnat_eq := hmatch_nat t ht
        simp only [shiftSeq, Nat.zero_add] at hnat_eq
        have hr1_hi : r1 + t + 1 ≤ p ^ 2 * q ^ (2 * W) + 3 := by omega
        have hr2_hi : r2 + t + 1 ≤ p ^ 2 * q ^ (2 * W) + 3 := by omega
        have hm1 := (dubBaseCarry_mem_two_letters hq1 hqp
          (hy_le (r1 + t) (by omega)) (hy_le (r1 + t + 1) hr1_hi)).1.1
        have hm2 := (dubBaseCarry_mem_two_letters hq1 hqp
          (hy_le (r2 + t) (by omega)) (hy_le (r2 + t + 1) hr2_hi)).1.1
        have hcast1 :
            (dubBaseCarryNat p q ξ s (r1 + t) : ℤ) =
              dubBaseCarry p q ξ (-s) (r1 + t) - k0 :=
          Int.toNat_of_nonneg (by omega)
        have hcast2 :
            (dubBaseCarryNat p q ξ s (r2 + t) : ℤ) =
              dubBaseCarry p q ξ (-s) (r2 + t) - k0 :=
          Int.toNat_of_nonneg (by omega)
        omega
      have hs_le1 : s ≤ 1 := by linarith [ (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ)) ]
      have hgrowth :=
        dubBaseX_strict_step_growth hq1 hqp hξ_lo hξW
          (θ := -s) (i := r1) (j := r2) (by linarith) (by linarith) hr12
      have hexp :=
        (dubBaseX_repeated_window_exp_and_power_cutoff hq2 hcop_pq
          hgrowth.2.1 hgrowth.2.2 hmatch).1
      set d := (L + 1) - r2
      have hd_add : d + r2 = L + 1 := Nat.sub_add_cancel hr2C
      have hqd_le_pd : q ^ d ≤ p ^ d := Nat.pow_le_pow_left (le_of_lt hqp) d
      have hqd_pos : 0 < q ^ d := Nat.pow_pos (by omega)
      have hstep1 : q ^ (2 * L + 1) < p ^ (L + 1) * q ^ W := by
        calc
          q ^ (2 * L + 1) = q ^ d * q ^ (L + r2) := by
            rw [← Nat.pow_add]
            have h : 2 * L + 1 = d + (L + r2) := by omega
            rw [h]
          _ < q ^ d * (p ^ r2 * q ^ W) := Nat.mul_lt_mul_of_pos_left hexp hqd_pos
          _ ≤ p ^ d * (p ^ r2 * q ^ W) := Nat.mul_le_mul_right _ hqd_le_pd
          _ = p ^ (L + 1) * q ^ W := by
            have h : p ^ d * (p ^ r2 * q ^ W) = (p ^ d * p ^ r2) * q ^ W := by ring
            rw [h, ← Nat.pow_add, hd_add]
      have hsq : q ^ (4 * L + 2) < p ^ (2 * L) * (p ^ 2 * q ^ (2 * W)) := by
        have hlt_sq : (q ^ (2 * L + 1)) ^ 2 < (p ^ (L + 1) * q ^ W) ^ 2 :=
          Nat.pow_lt_pow_left hstep1 (by decide)
        have hlhs : (q ^ (2 * L + 1)) ^ 2 = q ^ (4 * L + 2) := by
          rw [← Nat.pow_mul]
          have h : (2 * L + 1) * 2 = 4 * L + 2 := by ring
          rw [h]
        have hrhs : (p ^ (L + 1) * q ^ W) ^ 2 = p ^ (2 * L) * (p ^ 2 * q ^ (2 * W)) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
          have h1 : (L + 1) * 2 = 2 * L + 2 := by ring
          have h2 : W * 2 = 2 * W := by ring
          rw [h1, h2, Nat.pow_add p (2 * L) 2]
          ring
        rwa [hlhs, hrhs] at hlt_sq
      have hbern : 2 * L * p ^ (2 * L) ≤ q ^ (4 * L + 2) := by
        have h1 := pow_succ_add_mul_pow_le p (2 * L)
        have h2 : (p + 1) ^ (2 * L + 1) ≤ (q ^ 2) ^ (2 * L + 1) :=
          Nat.pow_le_pow_left (by omega : p + 1 ≤ q ^ 2) (2 * L + 1)
        have h3 : (q ^ 2) ^ (2 * L + 1) = q ^ (4 * L + 2) := by
          rw [← Nat.pow_mul]
          have h : 2 * (2 * L + 1) = 4 * L + 2 := by ring
          rw [h]
        omega
      have hp2L_pos : 0 < p ^ (2 * L) := Nat.pow_pos (by omega)
      have hcontra : p ^ (2 * L) * (p ^ 2 * q ^ (2 * W)) < 2 * L * p ^ (2 * L) := by
        rw [Nat.mul_comm (2 * L)]
        exact Nat.mul_lt_mul_of_pos_left h2L_gt hp2L_pos
      omega
    obtain ⟨n, hn_le, hn_gt⟩ := h1
    refine ⟨⟨n, hn_le, hn_gt⟩, n, hn_le, ?_⟩
    by_contra hmem
    push_neg at hmem
    set f := Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n)
    have hf_lt1 : f < 1 := Int.fract_lt_one _
    have hfl_eq :
        ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ n - s⌋ = ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ n⌋ := by
      rw [Int.floor_eq_iff]
      have h := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n)
      exact ⟨by linarith [h, hmem.1], by linarith [h, hf_lt1, hs0]⟩
    have hfract_eq : Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s) = f - s := by
      have h1 := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s)
      have h2 := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n)
      rw [hfl_eq] at h1
      linarith
    linarith [hmem.2, hfract_eq, hn_gt]
  refine ⟨hexplicit, ?_⟩
  intro ξ hξ N_0
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqp_real : (q : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : q + 1 ≤ p)
  have hpq_diff : (1 : ℝ) ≤ (p : ℝ) - (q : ℝ) := by linarith
  have hpq_pos : (0 : ℝ) < (p : ℝ) - (q : ℝ) := by linarith
  set B0 : ℝ := (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ))
  obtain ⟨k0, hk0⟩ := exists_nat_gt ((B0 * (q : ℝ)) / ξ)
  set k := max N_0 (k0 + 1)
  have hk_ge : N_0 ≤ k := le_max_left _ _
  have hbernoulli :
      (1 : ℝ) + (k : ℝ) * (((p : ℝ) - (q : ℝ)) / (q : ℝ)) ≤ ((p : ℝ) / (q : ℝ)) ^ k := by
    have hsub : (p : ℝ) / (q : ℝ) = 1 + ((p : ℝ) - (q : ℝ)) / (q : ℝ) := by
      field_simp [ne_of_gt hq_pos]
    rw [hsub]
    clear hk_ge
    induction k with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        have hpos : (0 : ℝ) ≤ (m : ℝ) * (((p : ℝ) - (q : ℝ)) / (q : ℝ)) ^ 2 := by positivity
        nlinarith [div_pos hpq_pos hq_pos]
  have hξk_lo : B0 ≤ ξ * ((p : ℝ) / (q : ℝ)) ^ k := by
    have h1 : B0 * (q : ℝ) < (k0 : ℝ) * ξ := (div_lt_iff₀ hξ).mp hk0
    have h2 : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k0 ≤ k)
    have h3 : B0 * (q : ℝ) ≤ (k : ℝ) * ξ * ((p : ℝ) - (q : ℝ)) := by
      have hm1 : (k0 : ℝ) * ξ ≤ (k : ℝ) * ξ := mul_le_mul_of_nonneg_right h2 (le_of_lt hξ)
      have hm2 : (k : ℝ) * ξ * 1 ≤ (k : ℝ) * ξ * ((p : ℝ) - (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hpq_diff (by positivity)
      linarith
    have h4 : B0 ≤ ξ * ((k : ℝ) * (((p : ℝ) - (q : ℝ)) / (q : ℝ))) := by
      have hdiv : B0 ≤ ((k : ℝ) * ξ * ((p : ℝ) - (q : ℝ))) / (q : ℝ) :=
        (le_div_iff₀ hq_pos).mpr h3
      have heq_div :
          ((k : ℝ) * ξ * ((p : ℝ) - (q : ℝ))) / (q : ℝ) =
            ξ * ((k : ℝ) * (((p : ℝ) - (q : ℝ)) / (q : ℝ))) := by ring
      linarith
    have h5 := mul_le_mul_of_nonneg_left hbernoulli (le_of_lt hξ)
    linarith
  obtain ⟨W, hW⟩ := exists_nat_gt (ξ * ((p : ℝ) / (q : ℝ)) ^ k)
  have hW_lt_qW : (W : ℝ) < (q : ℝ) ^ W := by
    have hnat : ∀ n : ℕ, n < q ^ n := by
      intro n
      induction n with
      | zero => exact Nat.pow_pos (by omega)
      | succ m ih =>
          have hpos : 1 ≤ q ^ m := Nat.pow_pos (by omega)
          rw [Nat.pow_succ]
          nlinarith
    exact_mod_cast hnat W
  have hξk_hi : ξ * ((p : ℝ) / (q : ℝ)) ^ k < (q : ℝ) ^ W := lt_trans hW hW_lt_qW
  obtain ⟨d, _, hd_out⟩ := (hexplicit hξk_lo hξk_hi).2
  refine ⟨k + d, by omega, ?_⟩
  have hmul :
      ξ * ((p : ℝ) / (q : ℝ)) ^ k * ((p : ℝ) / (q : ℝ)) ^ d =
        ξ * ((p : ℝ) / (q : ℝ)) ^ (k + d) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-- **Universal Infinite-Family Single-Cell Theorem Covering the Open Regime $p > q^2$ ($p \ge 2q$)
(`general_base_non_straddling_cell_escape`)**:
Let $2 \le q < p$ with $\gcd(p, q) = 1$, and let $1 \le k < p$ and $m \in \mathbb{N}$ satisfy
$$m p \le q k \quad \text{and} \quad q(k + 1) \le (m + 1)p$$
(in particular, $k = 1, m = 0$ holds for **every** coprime base with $p \ge 2q$, which
includes **every** coprime base in the open regime $p > q^2$!).
Then:
1. Confinement $\{\xi (p/q)^n\}, \{\xi (p/q)^{n+1}\} \in [k/p, (k+1)/p)$ forces the carry
   word to take the constant value `dubBaseCarry p q ξ 0 n = (k : ℤ) - (m : ℤ)`.
2. Whenever $2 + \frac{2q}{p - q} \le \xi < q^W$ and $p^2 < q^{W_0 + 2}$, there exists an explicit
   step $n \le W + W_0 + 3$ with $\{\xi (p/q)^n\} \notin [k/p, (k+1)/p)$. -/
theorem general_base_non_straddling_cell_escape
    {p q k m : ℕ}
    (hq2 : 2 ≤ q) (hqp : q < p) (hcop_pq : Nat.Coprime p q)
    (hk1 : 1 ≤ k) (hkp : k < p)
    (hlo_mp : m * p ≤ q * k) (hhi_mp : q * (k + 1) ≤ (m + 1) * p) :
    (∀ {ξ : ℝ} {n : ℕ},
      (k : ℝ) / (p : ℝ) ≤ dubBaseY p q ξ 0 n →
      dubBaseY p q ξ 0 n < ((k : ℝ) + 1) / (p : ℝ) →
      (k : ℝ) / (p : ℝ) ≤ dubBaseY p q ξ 0 (n + 1) →
      dubBaseY p q ξ 0 (n + 1) < ((k : ℝ) + 1) / (p : ℝ) →
      dubBaseCarry p q ξ 0 n = (k : ℤ) - (m : ℤ)) ∧
    (∀ {ξ : ℝ} {W W_0 : ℕ},
      p ^ 2 < q ^ (W_0 + 2) →
      (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ → ξ < (q : ℝ) ^ W →
      ∃ n ≤ W + W_0 + 3,
        Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) < (k : ℝ) / (p : ℝ) ∨
          ((k : ℝ) + 1) / (p : ℝ) ≤ Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n)) := by
  have hq1 : 1 ≤ q := by omega
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hconst_step :
      ∀ {ξ : ℝ} {n : ℕ},
        (k : ℝ) / (p : ℝ) ≤ dubBaseY p q ξ 0 n →
        dubBaseY p q ξ 0 n < ((k : ℝ) + 1) / (p : ℝ) →
        (k : ℝ) / (p : ℝ) ≤ dubBaseY p q ξ 0 (n + 1) →
        dubBaseY p q ξ 0 (n + 1) < ((k : ℝ) + 1) / (p : ℝ) →
        dubBaseCarry p q ξ 0 n = (k : ℤ) - (m : ℤ) := by
    intro ξ n hy0_lo hy0_hi hy1_lo hy1_hi
    have hlin := dubBaseCarry_eq_fract_linear (p := p) hq1 ξ 0 n
    have hpy_lo : (k : ℝ) ≤ (p : ℝ) * dubBaseY p q ξ 0 n := by
      have h1 := mul_le_mul_of_nonneg_left hy0_lo (le_of_lt hp_pos)
      have h2 : (p : ℝ) * ((k : ℝ) / (p : ℝ)) = (k : ℝ) := mul_div_cancel₀ _ (ne_of_gt hp_pos)
      linarith
    have hpy_hi : (p : ℝ) * dubBaseY p q ξ 0 n < (k : ℝ) + 1 := by
      have h1 := mul_lt_mul_of_pos_left hy0_hi hp_pos
      have h2 : (p : ℝ) * (((k : ℝ) + 1) / (p : ℝ)) = (k : ℝ) + 1 :=
        mul_div_cancel₀ _ (ne_of_gt hp_pos)
      linarith
    have hlo_real_mp : (m : ℝ) * (p : ℝ) ≤ (q : ℝ) * (k : ℝ) := by exact_mod_cast hlo_mp
    have hhi_real_mp : (q : ℝ) * ((k : ℝ) + 1) ≤ ((m : ℝ) + 1) * (p : ℝ) := by
      exact_mod_cast hhi_mp
    have hqy_lo : (m : ℝ) ≤ (q : ℝ) * dubBaseY p q ξ 0 (n + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hy1_lo (le_of_lt hq_pos)
      have h2 : (m : ℝ) ≤ (q : ℝ) * ((k : ℝ) / (p : ℝ)) := by
        rw [← mul_div_assoc]
        exact (le_div_iff₀ hp_pos).mpr hlo_real_mp
      linarith
    have hqy_hi : (q : ℝ) * dubBaseY p q ξ 0 (n + 1) < (m : ℝ) + 1 := by
      have h1 := mul_lt_mul_of_pos_left hy1_hi hq_pos
      have h2 : (q : ℝ) * (((k : ℝ) + 1) / (p : ℝ)) ≤ (m : ℝ) + 1 := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hp_pos).mpr hhi_real_mp
      linarith
    have hs_lo : ((k : ℤ) - (m : ℤ) - 1 : ℝ) < (dubBaseCarry p q ξ 0 n : ℝ) := by
      push_cast; linarith
    have hs_hi : (dubBaseCarry p q ξ 0 n : ℝ) < ((k : ℤ) - (m : ℤ) + 1 : ℝ) := by
      push_cast; linarith
    have hz_lo : (k : ℤ) - (m : ℤ) - 1 < dubBaseCarry p q ξ 0 n := by exact_mod_cast hs_lo
    have hz_hi : dubBaseCarry p q ξ 0 n < (k : ℤ) - (m : ℤ) + 1 := by exact_mod_cast hs_hi
    omega
  refine ⟨hconst_step, ?_⟩
  intro ξ W W_0 hp2 hξ_lo hξW
  by_contra hno
  have hmem :
      ∀ n ≤ W + W_0 + 3,
        (k : ℝ) / (p : ℝ) ≤ dubBaseY p q ξ 0 n ∧
          dubBaseY p q ξ 0 n < ((k : ℝ) + 1) / (p : ℝ) := by
    intro n hn
    unfold dubBaseY
    rw [add_zero]
    by_contra hout
    rcases lt_or_ge (Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n)) ((k : ℝ) / (p : ℝ)) with hlt | hge
    · exact hno ⟨n, hn, Or.inl hlt⟩
    · have hge2 : ((k : ℝ) + 1) / (p : ℝ) ≤ Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) := by
        by_contra hlt2
        exact hout ⟨hge, not_le.mp hlt2⟩
      exact hno ⟨n, hn, Or.inr hge2⟩
  set L := W + W_0
  have hmatch : ∀ t < L, dubBaseCarry p q ξ 0 (1 + t) = dubBaseCarry p q ξ 0 (2 + t) := by
    intro t ht
    have h1 := hconst_step (hmem (1 + t) (by omega)).1 (hmem (1 + t) (by omega)).2
      (hmem (1 + t + 1) (by omega)).1 (hmem (1 + t + 1) (by omega)).2
    have h2 := hconst_step (hmem (2 + t) (by omega)).1 (hmem (2 + t) (by omega)).2
      (hmem (2 + t + 1) (by omega)).1 (hmem (2 + t + 1) (by omega)).2
    omega
  have hgrowth :=
    dubBaseX_strict_step_growth hq1 hqp hξ_lo hξW (θ := 0) (i := 1) (j := 2)
      (by norm_num) (by norm_num) (by omega)
  have hexp : q ^ (L + 2) < p ^ 2 * q ^ W :=
    (dubBaseX_repeated_window_exp_and_power_cutoff hq2 hcop_pq
      hgrowth.2.1 hgrowth.2.2 hmatch).1
  have hrhs_lt : p ^ 2 * q ^ W < q ^ (L + 2) := by
    calc
      p ^ 2 * q ^ W < q ^ (W_0 + 2) * q ^ W :=
        Nat.mul_lt_mul_of_pos_right hp2 (Nat.pow_pos hq1)
      _ = q ^ (L + 2) := by
        rw [← Nat.pow_add]
        have h : (W_0 + 2) + W = L + 2 := by dsimp [L]; ring
        rw [h]
  exact Nat.lt_asymm hexp hrhs_lt

/-- **General-Base Floor-Residue Non-Stabilization $\lfloor \xi(p/q)^n \rfloor \bmod m$ for $m \ge p$
(`general_base_floor_mod_non_stabilization`)**:
For every coprime pair $2 \le q < p < q^2$, every modulus $m \ge p$, every real $\xi > 0$,
and every threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$ such that
$\lfloor \xi (p/q)^n \rfloor \bmod m \ne \lfloor \xi (p/q)^{N_0} \rfloor \bmod m$. -/
theorem general_base_floor_mod_non_stabilization
    {p q m : ℕ} (hq2 : 2 ≤ q) (hqp : q < p) (hpq2 : p < q ^ 2)
    (hcop_pq : Nat.Coprime p q) (hmp : p ≤ m)
    {ξ : ℝ} (hξ : 0 < ξ) (N_0 : ℕ) :
    ∃ n ≥ N_0,
      ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ n⌋ % (m : ℤ) ≠
        ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ N_0⌋ % (m : ℤ) := by
  have hm1 : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hmp_real : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmp
  have hinv_le : 1 / (m : ℝ) ≤ 1 / (p : ℝ) :=
    one_div_le_one_div_of_le hp_pos hmp_real
  have hm_int_pos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm1
  have hp1_le : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp_inv_le1 : 1 / (p : ℝ) ≤ 1 := (div_le_one hp_pos).mpr hp1_le
  set rem0 : ℤ := ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ N_0⌋ % (m : ℤ)
  set r : ℕ := Int.toNat rem0
  have hrem0_lo : 0 ≤ rem0 := Int.emod_nonneg _ (ne_of_gt hm_int_pos)
  have hrem0_hi : rem0 < (m : ℤ) := Int.emod_lt_of_pos _ hm_int_pos
  have hr_cast : (r : ℤ) = rem0 := Int.toNat_of_nonneg hrem0_lo
  have hr_lt : r < m := by
    have h : (r : ℤ) < (m : ℤ) := by omega
    exact_mod_cast h
  set s : ℝ := min ((r : ℝ) / (m : ℝ)) (1 - 1 / (p : ℝ))
  have hs0 : 0 ≤ s := le_min (div_nonneg (Nat.cast_nonneg r) (le_of_lt hm_pos)) (by linarith)
  have hs_hi : s + 1 / (p : ℝ) ≤ 1 := by
    have h : s ≤ 1 - 1 / (p : ℝ) := min_le_right _ _
    linarith
  have hs_le_rm : s ≤ (r : ℝ) / (m : ℝ) := min_le_left _ _
  have hrm1_le : ((r : ℝ) + 1) / (m : ℝ) ≤ s + 1 / (p : ℝ) := by
    by_cases hlt : (r : ℝ) / (m : ℝ) ≤ 1 - 1 / (p : ℝ)
    · have hs_eq : s = (r : ℝ) / (m : ℝ) := min_eq_left hlt
      rw [hs_eq, add_div]
      linarith
    · push_neg at hlt
      have hs_eq : s = 1 - 1 / (p : ℝ) := min_eq_right (le_of_lt hlt)
      have hr_le : (r : ℝ) + 1 ≤ (m : ℝ) := by
        have h : r + 1 ≤ m := by omega
        exact_mod_cast h
      have hdiv_le1 : ((r : ℝ) + 1) / (m : ℝ) ≤ 1 :=
        (div_le_one hm_pos).mpr hr_le
      rw [hs_eq]
      linarith
  have hξm_pos : 0 < ξ / (m : ℝ) := div_pos hξ hm_pos
  obtain ⟨n, hn_ge, hout⟩ :=
    (dubickas2009_general_base_explicit_and_infinite_escape hq2 hqp hpq2 hcop_pq hs0 hs_hi).2
      hξm_pos N_0
  refine ⟨n, hn_ge, ?_⟩
  intro hmod_eq
  rw [← hr_cast] at hmod_eq
  have hdiv_eq :
      (ξ * ((p : ℝ) / (q : ℝ)) ^ n) / (m : ℝ) = (ξ / (m : ℝ)) * ((p : ℝ) / (q : ℝ)) ^ n := by
    ring
  have hcell :=
    (floor_emod_eq_iff_fract_div_mem_cell (ξ * ((p : ℝ) / (q : ℝ)) ^ n) hm1 hr_lt).2.mp hmod_eq
  rw [hdiv_eq] at hcell
  rcases hout with hlt | hgt <;> linarith [hcell.1, hcell.2]

/-! ## 6. Verified Single-Block Funnel Engine & Explicit $W + 12$ Escape for the $7/12 > 20/39 > 1/2$ Four-Interval Union -/

/-- Check whether the intersection of $[q a + s D, q b + s D)$ and $[p c, p d)$ is empty,
or contained in $p \cdot [e, f)$ for some interval $(e, f) \in T_{\text{next}}$,
using only direct integer comparisons (avoiding `LinearOrder.max` / `min` overhead). -/
def funnelPieceOk (D : ℤ) (Tnext : List (ℤ × ℤ)) (c d s a b : ℤ) : Bool :=
  let lo1 := 2 * a + s * D
  let lo2 := 3 * c
  let hi1 := 2 * b + s * D
  let hi2 := 3 * d
  decide (hi1 ≤ lo1 ∨ hi1 ≤ lo2 ∨ hi2 ≤ lo1 ∨ hi2 ≤ lo2) ||
    Tnext.any (fun ef =>
      decide ((3 * ef.1 ≤ lo1 ∨ 3 * ef.1 ≤ lo2) ∧ (hi1 ≤ 3 * ef.2 ∨ hi2 ≤ 3 * ef.2)))

/-- Check one funnel transition $T_k \to T_{k+1}$ against base union $U$ over denominator $D$
at base $3 / 2$ (carries $s \in \{-1, 0, 1, 2\}$). -/
def funnelStepOk (D : ℤ) (U Tk Tk1 : List (ℤ × ℤ)) : Bool :=
  U.all (fun cd =>
    ([-1, 0, 1, 2] : List ℤ).all (fun s =>
      Tk.all (fun ab => funnelPieceOk D Tk1 cd.1 cd.2 s ab.1 ab.2)))

/-- Check a full funnel chain `levels` starting at `Tk` and ending at `H` over denominator `D`. -/
def funnelChainOk (D : ℤ) (U H : List (ℤ × ℤ)) :
    List (ℤ × ℤ) → List (List (ℤ × ℤ)) → Bool
  | Tk, [] => decide (Tk = H)
  | Tk, Tk1 :: rest => funnelStepOk D U Tk Tk1 && funnelChainOk D U H Tk1 rest

/-- Real membership in a union of half-open intervals $\bigcup_{(a, b) \in L} [a / D, b / D)$. -/
def InRatIntervalList (D : ℤ) (L : List (ℤ × ℤ)) (y : ℝ) : Prop :=
  ∃ ab ∈ L, (ab.1 : ℝ) ≤ (D : ℝ) * y ∧ (D : ℝ) * y < (ab.2 : ℝ)

/-- **Soundness of One Verified Funnel Step (`inRatIntervalList_next_of_funnelStepOk`)**:
If `funnelStepOk D U Tk Tk1 = true`, $y_n \in U$, and $y_{n+1} \in T_k$, then $y_n \in T_{k+1}$. -/
theorem inRatIntervalList_next_of_funnelStepOk {D : ℤ} {U Tk Tk1 : List (ℤ × ℤ)} {ξ : ℝ} {n : ℕ}
    (hD : 0 < D)
    (hstep : funnelStepOk D U Tk Tk1 = true)
    (hU : InRatIntervalList D U (dubY ξ 0 n))
    (hTk : InRatIntervalList D Tk (dubY ξ 0 (n + 1))) :
    InRatIntervalList D Tk1 (dubY ξ 0 n) := by
  rcases hU with ⟨⟨c, d⟩, hcd_mem, hc_lo, hd_hi⟩
  rcases hTk with ⟨⟨a, b⟩, hab_mem, ha_lo, hb_hi⟩
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hy0 := dubY_bounds ξ 0 n
  have hy1 := dubY_bounds ξ 0 (n + 1)
  have hlin := dubCarry_eq_fract_linear ξ 0 n
  set s := dubCarry ξ 0 n
  have hs_mem : s ∈ ([-1, 0, 1, 2] : List ℤ) := by
    have hlo : (-2 : ℝ) < (s : ℝ) := by linarith [hy0.1, hy1.2, hlin]
    have hhi : (s : ℝ) < (3 : ℝ) := by linarith [hy0.2, hy1.1, hlin]
    have hz1 : -2 < s := by exact_mod_cast hlo
    have hz2 : s < 3 := by exact_mod_cast hhi
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  unfold funnelStepOk at hstep
  rw [List.all_eq_true] at hstep
  have h1 := hstep (c, d) hcd_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 s hs_mem
  rw [List.all_eq_true] at h2
  have hpiece := h2 (a, b) hab_mem
  unfold funnelPieceOk at hpiece
  rw [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hpiece
  have h3y_eq : 3 * ((D : ℝ) * dubY ξ 0 n) = 2 * ((D : ℝ) * dubY ξ 0 (n + 1)) + (s : ℝ) * (D : ℝ) := by
    dsimp [s]
    linear_combination - (D : ℝ) * hlin
  have hlo1_real : ((2 * a + s * D : ℤ) : ℝ) ≤ 3 * ((D : ℝ) * dubY ξ 0 n) := by
    push_cast; linarith
  have hhi1_real : 3 * ((D : ℝ) * dubY ξ 0 n) < ((2 * b + s * D : ℤ) : ℝ) := by
    push_cast; linarith
  have hlo2_real : ((3 * c : ℤ) : ℝ) ≤ 3 * ((D : ℝ) * dubY ξ 0 n) := by
    push_cast; linarith
  have hhi2_real : 3 * ((D : ℝ) * dubY ξ 0 n) < ((3 * d : ℤ) : ℝ) := by
    push_cast; linarith
  rcases hpiece with hempty | ⟨⟨e, f⟩, hef_mem, hef_ok⟩
  · exfalso
    rcases hempty with hle1 | hle2 | hle3 | hle4
    · have h : ((2 * b + s * D : ℤ) : ℝ) ≤ ((2 * a + s * D : ℤ) : ℝ) := by exact_mod_cast hle1
      linarith
    · have h : ((2 * b + s * D : ℤ) : ℝ) ≤ ((3 * c : ℤ) : ℝ) := by exact_mod_cast hle2
      linarith
    · have h : ((3 * d : ℤ) : ℝ) ≤ ((2 * a + s * D : ℤ) : ℝ) := by exact_mod_cast hle3
      linarith
    · have h : ((3 * d : ℤ) : ℝ) ≤ ((3 * c : ℤ) : ℝ) := by exact_mod_cast hle4
      linarith
  · rw [decide_eq_true_eq] at hef_ok
    refine ⟨(e, f), hef_mem, ?_, ?_⟩
    · rcases hef_ok.1 with he1 | he2
      · have h : ((3 * e : ℤ) : ℝ) ≤ ((2 * a + s * D : ℤ) : ℝ) := by exact_mod_cast he1
        push_cast at h; linarith
      · have h : ((3 * e : ℤ) : ℝ) ≤ ((3 * c : ℤ) : ℝ) := by exact_mod_cast he2
        push_cast at h; linarith
    · rcases hef_ok.2 with hf1 | hf2
      · have h : ((2 * b + s * D : ℤ) : ℝ) ≤ ((3 * f : ℤ) : ℝ) := by exact_mod_cast hf1
        push_cast at h; linarith
      · have h : ((3 * d : ℤ) : ℝ) ≤ ((3 * f : ℤ) : ℝ) := by exact_mod_cast hf2
        push_cast at h; linarith

/-- Induction across a verified funnel chain `levels`: if `y_n ∈ U` for all `n ≤ N`,
then at depth `levels.length`, `y_n` lies in the terminal level `H`. -/
theorem inRatIntervalList_terminal_of_funnelChainOk
    {D : ℤ} {U H : List (ℤ × ℤ)} {ξ : ℝ} {N : ℕ}
    (hD : 0 < D)
    (hmemU : ∀ n ≤ N, InRatIntervalList D U (dubY ξ 0 n)) :
    ∀ (levels : List (List (ℤ × ℤ))) (Tk : List (ℤ × ℤ)) (K : ℕ),
      funnelChainOk D U H Tk levels = true →
      (∀ n, n + K ≤ N → InRatIntervalList D Tk (dubY ξ 0 n)) →
      ∀ n, n + K + levels.length ≤ N →
        InRatIntervalList D H (dubY ξ 0 n)
  | [], Tk, K, hchain, hTk, n, hn => by
      unfold funnelChainOk at hchain
      rw [decide_eq_true_eq] at hchain
      subst hchain
      exact hTk n (by omega)
  | Tk1 :: rest, Tk, K, hchain, hTk, n, hn => by
      unfold funnelChainOk at hchain
      rw [Bool.and_eq_true] at hchain
      have hTk1 : ∀ m, m + (K + 1) ≤ N → InRatIntervalList D Tk1 (dubY ξ 0 m) := by
        intro m hm
        exact inRatIntervalList_next_of_funnelStepOk hD hchain.1
          (hmemU m (by omega)) (hTk (m + 1) (by omega))
      exact inRatIntervalList_terminal_of_funnelChainOk hD hmemU rest Tk1 (K + 1) hchain.2 hTk1 n
        (by simp only [List.length_cons] at hn; omega)

/-- Base 4-interval union $U_{7/12} = [0, 1/6) \cup [1/4, 1/3) \cup [5/12, 2/3) \cup [3/4, 5/6)$
of total length $7 / 12 = 0.5833\ldots > 20 / 39 > 1 / 2$ scaled by $D = 8748$. -/
def unionSevenTwelfthsBase : List (ℤ × ℤ) :=
  [(0, 1458), (2187, 2916), (3645, 5832), (6561, 7290)]

/-- 7-step integer funnel for $U_{7/12}$ over $D = 8748$, collapsing to the single
interval $[(0, 440)]$. -/
def funnelSevenTwelfthsLevels : List (List (ℤ × ℤ)) :=
  [ [(0, 972), (2430, 2916), (3645, 3888), (4374, 4860), (5346, 5832), (6561, 6804)],
    [(0, 972), (2430, 2592), (3645, 3888), (4374, 4860), (5346, 5508), (6561, 6804)],
    [(0, 756), (2430, 2592), (3645, 3672), (4374, 4644), (5346, 5508), (6561, 6588)],
    [(0, 756), (2430, 2448), (3645, 3672), (4374, 4392), (4536, 4644), (5346, 5364), (6561, 6588)],
    [(0, 660), (2430, 2448), (4374, 4392), (4536, 4548), (5346, 5364)],
    [(0, 660), (4536, 4548)],
    [(0, 440)] ]

private theorem funnelSevenTwelfths_valid :
    funnelChainOk 8748 unionSevenTwelfthsBase [(0, 440)] unionSevenTwelfthsBase
      funnelSevenTwelfthsLevels = true := by
  decide

/-- Predicate for membership in the 4-interval union
$U_{7/12} = [0, 1/6) \cup [1/4, 1/3) \cup [5/12, 2/3) \cup [3/4, 5/6)$ of total length $7/12 > 1/2$. -/
def InUnionSevenTwelfths (y : ℝ) : Prop :=
  (0 ≤ y ∧ y < (1 / 6 : ℝ)) ∨
    ((1 / 4 : ℝ) ≤ y ∧ y < (1 / 3 : ℝ)) ∨
    ((5 / 12 : ℝ) ≤ y ∧ y < (2 / 3 : ℝ)) ∨
    ((3 / 4 : ℝ) ≤ y ∧ y < (5 / 6 : ℝ))

/-- **Explicit $W + 12$ Finite-Horizon Escape Bound & Infinite-Horizon Emptiness for the
$7/12 > 20/39 > 1/2$ Union $U_{7/12}$ (`union_seven_twelfths_explicit_and_infinite_escape`)**:
1. **Explicit $W + 12$ Escape Bound:** For **every** $\xi \in [1, 2^W)$, there exists an
   index $n \le W + 12$ such that $\{\xi (3/2)^n\} \notin U_{7/12}$.
2. **Infinite-Horizon Emptiness:** For **every** real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$,
   there exists $n \ge N_0$ such that $\{\xi (3/2)^n\} \notin U_{7/12}$. -/
theorem union_seven_twelfths_explicit_and_infinite_escape :
    (∀ {ξ : ℝ} {W : ℕ}, (1 : ℝ) ≤ ξ → ξ < (2 : ℝ) ^ W →
      ∃ n ≤ W + 12, ¬ InUnionSevenTwelfths (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) ∧
    (∀ {ξ : ℝ}, 0 < ξ → ∀ N_0 : ℕ,
      ∃ n ≥ N_0, ¬ InUnionSevenTwelfths (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) := by
  have hexplicit :
      ∀ {ξ : ℝ} {W : ℕ}, (1 : ℝ) ≤ ξ → ξ < (2 : ℝ) ^ W →
        ∃ n ≤ W + 12, ¬ InUnionSevenTwelfths (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
    intro ξ W hξ1 hξW
    by_contra hno
    push_neg at hno
    set N := W + 12
    have hmemU : ∀ n ≤ N, InRatIntervalList 8748 unionSevenTwelfthsBase (dubY ξ 0 n) := by
      intro n hn
      have hu := hno n hn
      unfold InUnionSevenTwelfths at hu
      unfold InRatIntervalList unionSevenTwelfthsBase dubY
      rw [add_zero]
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(0, 1458), by simp, by linarith, by linarith⟩
      · exact ⟨(2187, 2916), by simp, by linarith, by linarith⟩
      · exact ⟨(3645, 5832), by simp, by linarith, by linarith⟩
      · exact ⟨(6561, 7290), by simp, by linarith, by linarith⟩
    have hterm :=
      inRatIntervalList_terminal_of_funnelChainOk (by decide : (0 : ℤ) < 8748) hmemU
        funnelSevenTwelfthsLevels unionSevenTwelfthsBase 0 funnelSevenTwelfths_valid
        (fun n hn => hmemU n (by omega))
    have h440 : ∀ n ≤ W + 5, 0 ≤ dubY ξ 0 n ∧ dubY ξ 0 n < (440 / 8748 : ℝ) := by
      intro n hn
      have ht := hterm n (by simp [funnelSevenTwelfthsLevels, N]; omega)
      unfold InRatIntervalList at ht
      rcases ht with ⟨ab, hab_mem, hlo, hhi⟩
      simp only [List.mem_singleton] at hab_mem
      subst hab_mem
      dsimp at hlo hhi
      push_cast at hlo hhi
      exact ⟨by linarith, by linarith⟩
    have hzero : ∀ n ≤ W + 4, dubCarry ξ 0 n = 0 := by
      intro n hn
      have hy0 := h440 n (by omega)
      have hy1 := h440 (n + 1) (by omega)
      have hlin := dubCarry_eq_fract_linear ξ 0 n
      have hlo : (-1 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
      have hhi : (dubCarry ξ 0 n : ℝ) < (1 : ℝ) := by linarith
      have hz1 : -1 < dubCarry ξ 0 n := by exact_mod_cast hlo
      have hz2 : dubCarry ξ 0 n < 1 := by exact_mod_cast hhi
      omega
    have hmatch : ∀ t < W + 2, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (3 + t) := by
      intro t ht
      rw [hzero (2 + t) (by omega), hzero (3 + t) (by omega)]
    have hexp :=
      dubX_repeated_window_exp_bound (i := 2) (j := 3) (L := W + 2)
        hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
    have hpow : 3 ^ 3 * 2 ^ W < 2 ^ ((W + 2) + 3) := by
      calc
        3 ^ 3 * 2 ^ W = 27 * 2 ^ W := by ring
        _ < 32 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
        _ = 2 ^ ((W + 2) + 3) := by
          have h : (W + 2) + 3 = 5 + W := by omega
          rw [h, Nat.pow_add]
    omega
  refine ⟨hexplicit, ?_⟩
  intro ξ hξ N_0
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  obtain ⟨m, _, hm_out⟩ := hexplicit hge1 hltW
  refine ⟨k + m, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = ξ * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-! ## 7. General-Base Logarithmic Threshold $\kappa < \log q / \log(p/q)$ & Linear-in-$W$ Dubickas (2009) Escape -/

private theorem n_lt_q_pow {q : ℕ} (hq2 : 2 ≤ q) (n : ℕ) : n < q ^ n := by
  induction n with
  | zero => exact Nat.pow_pos (by omega)
  | succ m ih =>
      have hpos : 1 ≤ q ^ m := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]
      nlinarith

/-- **General-Base Real Logarithmic Threshold Rational Selection Bridge
(`exists_ab_of_lt_general_log_threshold`)**:
For **every** integer pair $2 \le q < p$ and **every** real complexity slope $\kappa$
satisfying $\kappa \cdot \log(p / q) < \log q$ (i.e. $\kappa < \log q / \log(p / q)$),
there exist natural numbers $a, b \in \mathbb{N}$ such that $1 \le b$, $p^b < q^{a + b}$,
and $(a : \mathbb{R}) \cdot \kappa < (b : \mathbb{R})$. -/
theorem exists_ab_of_lt_general_log_threshold {p q : ℕ} {kappa : ℝ}
    (hq2 : 2 ≤ q) (hqp : q < p)
    (hlog : kappa * Real.log ((p : ℝ) / (q : ℝ)) < Real.log (q : ℝ)) :
    ∃ a b : ℕ, 1 ≤ b ∧ p ^ b < q ^ (a + b) ∧ (a : ℝ) * kappa < (b : ℝ) := by
  by_cases hkap : kappa ≤ 0
  · refine ⟨p, 1, le_rfl, ?_, ?_⟩
    · have hlt := n_lt_q_pow hq2 p
      have hle : q ^ p ≤ q ^ (p + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using lt_of_lt_of_le hlt hle
    · have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hmul : (p : ℝ) * kappa ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp_nonneg hkap
      push_cast
      linarith
  · push_neg at hkap
    have hq_gt1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq2
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have hqp_real : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
    have hpq_gt1 : (1 : ℝ) < (p : ℝ) / (q : ℝ) := (one_lt_div hq_pos).mpr hqp_real
    have hlog_q : 0 < Real.log (q : ℝ) := Real.log_pos hq_gt1
    have hlog_pq : 0 < Real.log ((p : ℝ) / (q : ℝ)) := Real.log_pos hpq_gt1
    set γ : ℝ := Real.log ((p : ℝ) / (q : ℝ)) / Real.log (q : ℝ)
    have hγ_pos : 0 < γ := div_pos hlog_pq hlog_q
    have hγ_kap : γ * kappa < 1 := by
      unfold γ
      rw [div_mul_eq_mul_div, div_lt_one hlog_q]
      linarith
    set gap : ℝ := 1 - γ * kappa
    have hgap_pos : 0 < gap := by unfold gap; linarith
    obtain ⟨b, hb_gt⟩ := exists_nat_gt (kappa / gap + 1)
    have hdiv_pos : 0 < kappa / gap := div_pos hkap hgap_pos
    have hb_ge1 : 1 ≤ b := by
      have h1 : (1 : ℝ) < (b : ℝ) := by linarith
      exact_mod_cast (le_of_lt h1)
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_ge1
    have hkap_lt : kappa < (b : ℝ) * gap := by
      have h1 : kappa / gap < (b : ℝ) := by linarith
      exact (div_lt_iff₀ hgap_pos).mp h1
    set a : ℕ := Int.toNat (⌊γ * (b : ℝ)⌋ + 1)
    have hγb_pos : 0 < γ * (b : ℝ) := mul_pos hγ_pos hb_pos
    have hfl_nonneg : 0 ≤ ⌊γ * (b : ℝ)⌋ := Int.floor_nonneg.mpr (le_of_lt hγb_pos)
    have ha_cast : (a : ℝ) = ((⌊γ * (b : ℝ)⌋ : ℤ) : ℝ) + 1 := by
      have h : ((a : ℕ) : ℤ) = ⌊γ * (b : ℝ)⌋ + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h
    have ha_gt : γ * (b : ℝ) < (a : ℝ) := by
      rw [ha_cast]
      exact Int.lt_floor_add_one (γ * (b : ℝ))
    have ha_le : (a : ℝ) ≤ γ * (b : ℝ) + 1 := by
      rw [ha_cast]
      linarith [Int.floor_le (γ * (b : ℝ))]
    have ha_kap : (a : ℝ) * kappa < (b : ℝ) := by
      have h1 : (a : ℝ) * kappa ≤ (γ * (b : ℝ) + 1) * kappa :=
        mul_le_mul_of_nonneg_right ha_le (le_of_lt hkap)
      have h2 : (γ * (b : ℝ) + 1) * kappa < (b : ℝ) := by
        unfold gap at hkap_lt
        nlinarith
      exact lt_of_le_of_lt h1 h2
    have hlog_ineq : (b : ℝ) * Real.log ((p : ℝ) / (q : ℝ)) < (a : ℝ) * Real.log (q : ℝ) := by
      have h1 : γ * (b : ℝ) * Real.log (q : ℝ) < (a : ℝ) * Real.log (q : ℝ) :=
        mul_lt_mul_of_pos_right ha_gt hlog_q
      have h2 : γ * (b : ℝ) * Real.log (q : ℝ) = (b : ℝ) * Real.log ((p : ℝ) / (q : ℝ)) := by
        unfold γ
        field_simp [ne_of_gt hlog_q]
        ring
      linarith
    have hlog_p_eq : Real.log (p : ℝ) = Real.log ((p : ℝ) / (q : ℝ)) + Real.log (q : ℝ) := by
      have hmul : (p : ℝ) = ((p : ℝ) / (q : ℝ)) * (q : ℝ) := by
        field_simp [ne_of_gt hq_pos]
      conv_lhs => rw [hmul]
      exact Real.log_mul (ne_of_gt (div_pos (by linarith) hq_pos)) (ne_of_gt hq_pos)
    have hlog_pow : Real.log ((p : ℝ) ^ b) < Real.log ((q : ℝ) ^ (a + b)) := by
      rw [Real.log_pow, Real.log_pow, hlog_p_eq, Nat.cast_add]
      linarith
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hpow_real : (p : ℝ) ^ b < (q : ℝ) ^ (a + b) := by
      have hexp := Real.exp_lt_exp.mpr hlog_pow
      rwa [Real.exp_log (pow_pos hp_pos b), Real.exp_log (pow_pos hq_pos (a + b))] at hexp
    exact ⟨a, b, hb_ge1, by exact_mod_cast hpow_real, ha_kap⟩

/-- Non-negative natural-number encoding of the general-base carry word for $\theta \le 0$:
`dubBaseCarryGeneralNat p q ξ θ n = (dubBaseCarry p q ξ θ n + q).toNat`. -/
noncomputable def dubBaseCarryGeneralNat (p q : ℕ) (ξ θ : ℝ) (n : ℕ) : ℕ :=
  (dubBaseCarry p q ξ θ n + (q : ℤ)).toNat

theorem dubBaseCarryGeneralNat_eq_iff {p q : ℕ} {ξ θ : ℝ}
    (hq1 : 1 ≤ q) (hqp : q < p) (hθ_hi : θ ≤ 0) (i j : ℕ) :
    dubBaseCarryGeneralNat p q ξ θ i = dubBaseCarryGeneralNat p q ξ θ j ↔
      dubBaseCarry p q ξ θ i = dubBaseCarry p q ξ θ j := by
  have hpos : ∀ n, 0 ≤ dubBaseCarry p q ξ θ n + (q : ℤ) := by
    intro n
    have hp_pos : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hqp_real : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
    have hy0 := (dubBaseY_bounds p q ξ θ n).1
    have hy1 := (dubBaseY_bounds p q ξ θ (n + 1)).2
    have hpy : 0 ≤ (p : ℝ) * dubBaseY p q ξ θ n := mul_nonneg hp_pos hy0
    have hqy : (q : ℝ) * dubBaseY p q ξ θ (n + 1) < (q : ℝ) := by nlinarith
    have hθ_term : 0 ≤ -((p : ℝ) - (q : ℝ)) * θ := by nlinarith
    have hlin := dubBaseCarry_eq_fract_linear (p := p) hq1 ξ θ n
    have hgt : -(q : ℝ) < (dubBaseCarry p q ξ θ n : ℝ) := by linarith
    have hint : -(q : ℤ) < dubBaseCarry p q ξ θ n := by exact_mod_cast hgt
    omega
  constructor
  · intro h
    unfold dubBaseCarryGeneralNat at h
    have h1 := Int.toNat_of_nonneg (hpos i)
    have h2 := Int.toNat_of_nonneg (hpos j)
    omega
  · intro h
    unfold dubBaseCarryGeneralNat
    rw [h]

/-- **General-Base $\log q / \log(p/q)$ Sub-Critical Complexity Exclusion for Shifted Carry Words
(`no_subcritical_general_log_threshold_dubBaseCarry`)**:
For **every** coprime pair $2 \le q < p$ (including the open regime $p > q^2$), **every**
$\xi \ge 2 + \frac{2q}{p - q}$, **every** $\theta \in [-1, 0]$, $C_0 \ge 0$, and **every**
$\kappa$ with $\kappa \log(p/q) < \log q$, the general-base carry word
`dubBaseCarryGeneralNat p q ξ θ` cannot satisfy
`prefixFactorCount (dubBaseCarryGeneralNat p q ξ θ) L (C L) ≤ C L ≤ kappa * L + C_0`
at arbitrarily large lengths $L$. -/
theorem no_subcritical_general_log_threshold_dubBaseCarry
    {p q : ℕ} {ξ θ kappa C_0 : ℝ} {C : ℕ → ℕ}
    (hq2 : 2 ≤ q) (hqp : q < p) (hcop_pq : Nat.Coprime p q)
    (hξ_lo : (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ)
    (hθ_lo : (-1 : ℝ) ≤ θ) (hθ_hi : θ ≤ 0) (hC0 : 0 ≤ C_0)
    (hlog : kappa * Real.log ((p : ℝ) / (q : ℝ)) < Real.log (q : ℝ)) :
    ¬ (∀ L_min : ℕ, ∃ L ≥ L_min,
      prefixFactorCount (dubBaseCarryGeneralNat p q ξ θ) L (C L) ≤ C L ∧
        (C L : ℝ) ≤ kappa * (L : ℝ) + C_0) := by
  intro hliminf
  have hq1 : 1 ≤ q := by omega
  obtain ⟨a, b, hb1, hpab, ha_kap⟩ := exists_ab_of_lt_general_log_threshold hq2 hqp hlog
  obtain ⟨W, hW⟩ := exists_nat_gt ξ
  have hlt_pow : (W : ℝ) < (q : ℝ) ^ W := by
    have hnat : W < q ^ W := by
      clear hW
      induction W with
      | zero => exact Nat.pow_pos (by omega)
      | succ n ih =>
          have hpos : 1 ≤ q ^ n := Nat.pow_pos (by omega)
          have hq_mul : 2 * q ^ n ≤ q * q ^ n := Nat.mul_le_mul_right (q ^ n) hq2
          rw [Nat.pow_succ']
          omega
    exact_mod_cast hnat
  have hξW : ξ < (q : ℝ) ^ W := lt_trans hW hlt_pow
  set gap : ℝ := (b : ℝ) - (a : ℝ) * kappa
  have hgap_pos : 0 < gap := by unfold gap; linarith
  set RHS : ℝ := (a : ℝ) * C_0 + (b : ℝ) * (W : ℝ)
  have hRHS_nonneg : 0 ≤ RHS := by unfold RHS; positivity
  obtain ⟨L_min, hL_min⟩ := exists_nat_gt (RHS / gap + 1)
  obtain ⟨L, hL_ge, hcard, hC_bound⟩ := hliminf L_min
  obtain ⟨r1, r2, hr12, hr2C, hmatch_nat⟩ :=
    exists_repeated_subword_of_prefixFactorCount_le
      (dubBaseCarryGeneralNat p q ξ θ) L (C L) hcard
  have hmatch : ∀ t < L, dubBaseCarry p q ξ θ (r1 + t) = dubBaseCarry p q ξ θ (r2 + t) := by
    intro t ht
    exact (dubBaseCarryGeneralNat_eq_iff hq1 hqp hθ_hi (r1 + t) (r2 + t)).mp (hmatch_nat t ht)
  have hgrowth :=
    dubBaseX_strict_step_growth hq1 hqp hξ_lo hξW hθ_lo (by linarith) hr12
  have hcut :=
    (dubBaseX_repeated_window_exp_and_power_cutoff hq2 hcop_pq
      hgrowth.2.1 hgrowth.2.2 hmatch).2.1 hb1 hpab
  have har2 : a * r2 ≤ a * C L := Nat.mul_le_mul_left a hr2C
  have hcut_le : b * L + 1 ≤ a * C L + b * W := by omega
  have hcut_real :
      (b : ℝ) * (L : ℝ) + 1 ≤ (a : ℝ) * (C L : ℝ) + (b : ℝ) * (W : ℝ) := by
    exact_mod_cast hcut_le
  have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have ha_mul :
      (a : ℝ) * (C L : ℝ) ≤ (a : ℝ) * (kappa * (L : ℝ) + C_0) :=
    mul_le_mul_of_nonneg_left hC_bound ha_nonneg
  have hgap_le : gap * (L : ℝ) + 1 ≤ RHS := by
    unfold gap RHS
    linarith
  have hL_real : (L_min : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge
  have h1 : RHS / gap < (L : ℝ) := by linarith
  have h2 : RHS < (L : ℝ) * gap := (div_lt_iff₀ hgap_pos).mp h1
  linarith

/-- **Linear-in-$W$ General-Base Dubickas (2009) Escape Bound (`dubickas2009_general_base_linear_in_W_escape`)**:
For **every** coprime pair $2 \le q < p < q^2$, there exist integers $a < b$ ($1 \le b - a$)
with $p^b < q^{a + b}$ such that for **every** shift $s \in [0, 1 - 1/p]$ and **every**
$\xi \in [2 + \frac{2q}{p - q},\, q^W)$, there exists an index $n \le 2 b W + 2 a + 2$
where $\{\xi (p/q)^n\} \notin [s, s + 1/p]$. -/
theorem dubickas2009_general_base_linear_in_W_escape
    {p q : ℕ} (hq2 : 2 ≤ q) (hqp : q < p) (hpq2 : p < q ^ 2) (hcop_pq : Nat.Coprime p q) :
    ∃ a b : ℕ, a < b ∧ p ^ b < q ^ (a + b) ∧
      ∀ {s ξ : ℝ} {W : ℕ},
        0 ≤ s → s + 1 / (p : ℝ) ≤ 1 →
        (2 : ℝ) + (2 * (q : ℝ)) / ((p : ℝ) - (q : ℝ)) ≤ ξ → ξ < (q : ℝ) ^ W →
        ∃ n ≤ 2 * b * W + 2 * a + 2,
          Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) < s ∨
            s + 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n) := by
  have hq1 : 1 ≤ q := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpq2_real : (p : ℝ) < (q : ℝ) ^ 2 := by exact_mod_cast hpq2
  have hdiv_lt_q : (p : ℝ) / (q : ℝ) < (q : ℝ) := by
    rw [div_lt_iff₀ hq_pos]
    linarith [show (q : ℝ) * (q : ℝ) = (q : ℝ) ^ 2 by ring]
  have hlog1 : (1 : ℝ) * Real.log ((p : ℝ) / (q : ℝ)) < Real.log (q : ℝ) := by
    rw [one_mul]
    exact Real.log_lt_log (div_pos hp_pos hq_pos) hdiv_lt_q
  obtain ⟨a, b, hb1, hpab, hab_real⟩ := exists_ab_of_lt_general_log_threshold hq2 hqp hlog1
  rw [mul_one] at hab_real
  have hab : a < b := by exact_mod_cast hab_real
  refine ⟨a, b, hab, hpab, ?_⟩
  intro s ξ W hs0 hs_hi hξ_lo hξW
  have h1 : ∃ n ≤ 2 * b * W + 2 * a + 2, 1 / (p : ℝ) < Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s) := by
    by_contra hno
    push_neg at hno
    set L := b * W + a
    set C := L + 1
    have h2bW : 2 * b * W = 2 * (b * W) := by ring
    have hy_le : ∀ n ≤ 2 * b * W + 2 * a + 2, dubBaseY p q ξ (-s) n ≤ 1 / (p : ℝ) := by
      intro n hn
      unfold dubBaseY
      have hsub : ξ * ((p : ℝ) / (q : ℝ)) ^ n + -s = ξ * ((p : ℝ) / (q : ℝ)) ^ n - s := by ring
      rw [hsub]
      exact hno n hn
    have hcard :
        prefixFactorCount (shiftSeq (dubBaseCarryNat p q ξ s) 0) L C ≤ C := by
      apply dubBaseCarryNat_prefixFactorCount_le hq1 hqp
      intro n _ hn_hi
      exact hy_le n (by omega)
    obtain ⟨r1, r2, hr12, hr2C, hmatch_nat⟩ :=
      exists_repeated_subword_of_prefixFactorCount_le
        (shiftSeq (dubBaseCarryNat p q ξ s) 0) L C hcard
    set k0 : ℤ := ⌊((p : ℝ) - (q : ℝ)) * s⌋
    have hmatch :
        ∀ t < L, dubBaseCarry p q ξ (-s) (r1 + t) = dubBaseCarry p q ξ (-s) (r2 + t) := by
      intro t ht
      have hnat_eq := hmatch_nat t ht
      simp only [shiftSeq, Nat.zero_add] at hnat_eq
      have hm1 := (dubBaseCarry_mem_two_letters hq1 hqp
        (hy_le (r1 + t) (by omega)) (hy_le (r1 + t + 1) (by omega))).1.1
      have hm2 := (dubBaseCarry_mem_two_letters hq1 hqp
        (hy_le (r2 + t) (by omega)) (hy_le (r2 + t + 1) (by omega))).1.1
      have hcast1 :
          (dubBaseCarryNat p q ξ s (r1 + t) : ℤ) =
            dubBaseCarry p q ξ (-s) (r1 + t) - k0 :=
        Int.toNat_of_nonneg (by omega)
      have hcast2 :
          (dubBaseCarryNat p q ξ s (r2 + t) : ℤ) =
            dubBaseCarry p q ξ (-s) (r2 + t) - k0 :=
        Int.toNat_of_nonneg (by omega)
      omega
    have hs_le1 : s ≤ 1 := by linarith [ (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ)) ]
    have hgrowth :=
      dubBaseX_strict_step_growth hq1 hqp hξ_lo hξW
        (θ := -s) (i := r1) (j := r2) (by linarith) (by linarith) hr12
    have hcut :=
      (dubBaseX_repeated_window_exp_and_power_cutoff hq2 hcop_pq
        hgrowth.2.1 hgrowth.2.2 hmatch).2.1 hb1 hpab
    have har2 : a * r2 ≤ a * (L + 1) := Nat.mul_le_mul_left a hr2C
    have hba : a * L + L ≤ b * L := by
      have h : a + 1 ≤ b := by omega
      calc
        a * L + L = (a + 1) * L := by ring
        _ ≤ b * L := Nat.mul_le_mul_right L h
    have haL1 : a * (L + 1) = a * L + a := by ring
    omega
  rcases h1 with ⟨n, hn_le, hn_gt⟩
  refine ⟨n, hn_le, ?_⟩
  by_contra hmem
  push_neg at hmem
  set f := Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n)
  have hf_lt1 : f < 1 := Int.fract_lt_one _
  have hfl_eq :
      ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ n - s⌋ = ⌊ξ * ((p : ℝ) / (q : ℝ)) ^ n⌋ := by
    rw [Int.floor_eq_iff]
    have h := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n)
    exact ⟨by linarith [h, hmem.1], by linarith [h, hf_lt1, hs0]⟩
  have hfract_eq : Int.fract (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s) = f - s := by
    have h1 := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n - s)
    have h2 := Int.self_sub_floor (ξ * ((p : ℝ) / (q : ℝ)) ^ n)
    rw [hfl_eq] at h1
    linarith
  linarith [hmem.2, hfract_eq, hn_gt]

/-! ## 8. Human-Readable 4-Inequality Proof of $Z_{4/3}(1/3, 5/8) = \emptyset$ (Length $7/24 > 1/4$) with Explicit $W + 8$ Bound -/

/-- **4-Inequality Period-2 Carry Locking for Base $4/3$ on $[1/3, 5/8)$
(`base_four_three_carry_period_two`)**:
Whenever $\frac{1}{3} \le \operatorname{dubBaseY} 4\ 3\ \xi\ 0\ n < \frac{5}{8}$ for all $0 \le n \le N$:
1. $s_n \in \{0, 1\}$ for all $n < N$,
2. `11` is impossible for $k + 2 \le N$ ($9 y_{k+2} = 16 y_k - 7 < 3$),
3. `000` is impossible for $k + 3 \le N$ ($27 y_{k+3} = 64 y_k > 135/8$),
4. `00` is impossible for $k + 6 \le N$ (since `00100` has $243 y_{k+5} = 1024 y_k - 144 > 1215/8$
   and `001010` has $729 y_{k+6} = 4096 y_k - 675 > 3645/8$), and
5. Therefore $s_{k+2} = s_k$ (strict alternation) for all $k + 7 \le N$. -/
theorem base_four_three_carry_period_two {ξ : ℝ} {N : ℕ}
    (hmem : ∀ n ≤ N, (1 / 3 : ℝ) ≤ dubBaseY 4 3 ξ 0 n ∧ dubBaseY 4 3 ξ 0 n < (5 / 8 : ℝ)) :
    ∀ k, k + 7 ≤ N → dubBaseCarry 4 3 ξ 0 (k + 2) = dubBaseCarry 4 3 ξ 0 k := by
  have hlin_step : ∀ n : ℕ,
      (dubBaseCarry 4 3 ξ 0 n : ℝ) = 4 * dubBaseY 4 3 ξ 0 n - 3 * dubBaseY 4 3 ξ 0 (n + 1) := by
    intro n
    have h := dubBaseCarry_eq_fract_linear (p := 4) (q := 3) (by decide) ξ 0 n
    push_cast at h
    linarith
  have hbit : ∀ n < N, dubBaseCarry 4 3 ξ 0 n = 0 ∨ dubBaseCarry 4 3 ξ 0 n = 1 := by
    intro n hn
    have h0 := hmem n (by omega)
    have h1 := hmem (n + 1) (by omega)
    have hl := hlin_step n
    have hlo : (-1 : ℝ) < (dubBaseCarry 4 3 ξ 0 n : ℝ) := by linarith
    have hhi : (dubBaseCarry 4 3 ξ 0 n : ℝ) < (2 : ℝ) := by linarith
    have hz1 : -1 < dubBaseCarry 4 3 ξ 0 n := by exact_mod_cast hlo
    have hz2 : dubBaseCarry 4 3 ξ 0 n < 2 := by exact_mod_cast hhi
    omega
  have hno_11 : ∀ n, n + 2 ≤ N → ¬ (dubBaseCarry 4 3 ξ 0 n = 1 ∧ dubBaseCarry 4 3 ξ 0 (n + 1) = 1) := by
    intro n hn ⟨hs0, hs1⟩
    have hy0 := hmem n (by omega)
    have hy2 := hmem (n + 2) (by omega)
    have hl0 := hlin_step n
    have hl1 := hlin_step (n + 1)
    have hc0 : (dubBaseCarry 4 3 ξ 0 n : ℝ) = 1 := by exact_mod_cast hs0
    have hc1 : (dubBaseCarry 4 3 ξ 0 (n + 1) : ℝ) = 1 := by exact_mod_cast hs1
    linarith
  have hno_000 :
      ∀ n, n + 3 ≤ N →
        ¬ (dubBaseCarry 4 3 ξ 0 n = 0 ∧ dubBaseCarry 4 3 ξ 0 (n + 1) = 0 ∧
          dubBaseCarry 4 3 ξ 0 (n + 2) = 0) := by
    intro n hn ⟨hs0, hs1, hs2⟩
    have hy0 := hmem n (by omega)
    have hy3 := hmem (n + 3) (by omega)
    have hl0 := hlin_step n
    have hl1 := hlin_step (n + 1)
    have hl2 := hlin_step (n + 2)
    have hc0 : (dubBaseCarry 4 3 ξ 0 n : ℝ) = 0 := by exact_mod_cast hs0
    have hc1 : (dubBaseCarry 4 3 ξ 0 (n + 1) : ℝ) = 0 := by exact_mod_cast hs1
    have hc2 : (dubBaseCarry 4 3 ξ 0 (n + 2) : ℝ) = 0 := by exact_mod_cast hs2
    linarith
  have hno_00 :
      ∀ n, n + 6 ≤ N → ¬ (dubBaseCarry 4 3 ξ 0 n = 0 ∧ dubBaseCarry 4 3 ξ 0 (n + 1) = 0) := by
    intro n hn ⟨hs0, hs1⟩
    have hs2 : dubBaseCarry 4 3 ξ 0 (n + 2) = 1 := by
      rcases hbit (n + 2) (by omega) with h0 | h1
      · exfalso; exact hno_000 n (by omega) ⟨hs0, hs1, h0⟩
      · exact h1
    have hs3 : dubBaseCarry 4 3 ξ 0 (n + 3) = 0 := by
      rcases hbit (n + 3) (by omega) with h0 | h1
      · exact h0
      · exfalso; exact hno_11 (n + 2) (by omega) ⟨hs2, h1⟩
    have hl0 := hlin_step n
    have hl1 := hlin_step (n + 1)
    have hl2 := hlin_step (n + 2)
    have hl3 := hlin_step (n + 3)
    have hl4 := hlin_step (n + 4)
    have hl5 := hlin_step (n + 5)
    have hc0 : (dubBaseCarry 4 3 ξ 0 n : ℝ) = 0 := by exact_mod_cast hs0
    have hc1 : (dubBaseCarry 4 3 ξ 0 (n + 1) : ℝ) = 0 := by exact_mod_cast hs1
    have hc2 : (dubBaseCarry 4 3 ξ 0 (n + 2) : ℝ) = 1 := by exact_mod_cast hs2
    have hc3 : (dubBaseCarry 4 3 ξ 0 (n + 3) : ℝ) = 0 := by exact_mod_cast hs3
    have hy0 := hmem n (by omega)
    have hy5 := hmem (n + 5) (by omega)
    have hy6 := hmem (n + 6) (by omega)
    rcases hbit (n + 4) (by omega) with hs4_0 | hs4_1
    · have hc4 : (dubBaseCarry 4 3 ξ 0 (n + 4) : ℝ) = 0 := by exact_mod_cast hs4_0
      linarith
    · have hs5 : dubBaseCarry 4 3 ξ 0 (n + 5) = 0 := by
        rcases hbit (n + 5) (by omega) with h0 | h1
        · exact h0
        · exfalso; exact hno_11 (n + 4) (by omega) ⟨hs4_1, h1⟩
      have hc4 : (dubBaseCarry 4 3 ξ 0 (n + 4) : ℝ) = 1 := by exact_mod_cast hs4_1
      have hc5 : (dubBaseCarry 4 3 ξ 0 (n + 5) : ℝ) = 0 := by exact_mod_cast hs5
      linarith
  intro k hk
  rcases hbit k (by omega) with b0 | b0 <;>
    rcases hbit (k + 1) (by omega) with b1 | b1 <;>
    rcases hbit (k + 2) (by omega) with b2 | b2
  · exfalso; exact hno_00 k (by omega) ⟨b0, b1⟩
  · exfalso; exact hno_00 k (by omega) ⟨b0, b1⟩
  · omega
  · exfalso; exact hno_11 (k + 1) (by omega) ⟨b1, b2⟩
  · exfalso; exact hno_00 (k + 1) (by omega) ⟨b1, b2⟩
  · omega
  · exfalso; exact hno_11 k (by omega) ⟨b0, b1⟩
  · exfalso; exact hno_11 k (by omega) ⟨b0, b1⟩

/-- **Explicit $W + 8$ Escape Bound & Infinite-Horizon Emptiness for Base $4/3$ on $[1/3, 5/8)$
(Length $7/24 > 1/4 = 1/p$, `base_four_three_beyond_quarter_explicit_and_infinite_escape`)**:
1. **Explicit $W + 8$ Escape Bound:** For **every** $\xi \in [8, 3^W)$, there exists an
   index $n \le W + 8$ such that $\{\xi (4/3)^n\} \notin [1/3, 5/8)$.
2. **Infinite-Horizon Emptiness ($Z_{4/3}(1/3, 5/8) = \emptyset$):** For **every** real $\xi > 0$
   and threshold $N_0 \in \mathbb{N}$, there exists $n \ge N_0$ with $\{\xi (4/3)^n\} \notin [1/3, 5/8)$. -/
theorem base_four_three_beyond_quarter_explicit_and_infinite_escape :
    (∀ {ξ : ℝ} {W : ℕ}, (8 : ℝ) ≤ ξ → ξ < (3 : ℝ) ^ W →
      ∃ n ≤ W + 8,
        Int.fract (ξ * (4 / 3 : ℝ) ^ n) < (1 / 3 : ℝ) ∨
          (5 / 8 : ℝ) ≤ Int.fract (ξ * (4 / 3 : ℝ) ^ n)) ∧
    (∀ {ξ : ℝ}, 0 < ξ → ∀ N_0 : ℕ,
      ∃ n ≥ N_0,
        Int.fract (ξ * (4 / 3 : ℝ) ^ n) < (1 / 3 : ℝ) ∨
          (5 / 8 : ℝ) ≤ Int.fract (ξ * (4 / 3 : ℝ) ^ n)) := by
  have hexplicit :
      ∀ {ξ : ℝ} {W : ℕ}, (8 : ℝ) ≤ ξ → ξ < (3 : ℝ) ^ W →
        ∃ n ≤ W + 8,
          Int.fract (ξ * (4 / 3 : ℝ) ^ n) < (1 / 3 : ℝ) ∨
            (5 / 8 : ℝ) ≤ Int.fract (ξ * (4 / 3 : ℝ) ^ n) := by
    intro ξ W hξ8 hξW
    by_contra hno
    have hmem : ∀ n ≤ W + 8, (1 / 3 : ℝ) ≤ dubBaseY 4 3 ξ 0 n ∧ dubBaseY 4 3 ξ 0 n < (5 / 8 : ℝ) := by
      intro n hn
      unfold dubBaseY
      push_cast
      rw [add_zero]
      by_contra hout
      rcases lt_or_ge (Int.fract (ξ * (4 / 3 : ℝ) ^ n)) (1 / 3 : ℝ) with hlt | hge
      · exact hno ⟨n, hn, Or.inl hlt⟩
      · have hge2 : (5 / 8 : ℝ) ≤ Int.fract (ξ * (4 / 3 : ℝ) ^ n) := by
          by_contra hlt2
          exact hout ⟨hge, not_le.mp hlt2⟩
        exact hno ⟨n, hn, Or.inr hge2⟩
    have hper2 := base_four_three_carry_period_two hmem
    set L := W + 1
    have hmatch : ∀ t < L, dubBaseCarry 4 3 ξ 0 (0 + t) = dubBaseCarry 4 3 ξ 0 (2 + t) := by
      intro t ht
      have h := hper2 t (by omega)
      have hidx : 2 + t = t + 2 := by omega
      rw [Nat.zero_add, hidx, h]
    have hgrowth :=
      dubBaseX_strict_step_growth (p := 4) (q := 3) (by decide) (by decide)
        (by push_cast; linarith) hξW (θ := 0) (i := 0) (j := 2)
        (by norm_num) (by norm_num) (by decide)
    have hexp : 3 ^ (L + 2) < 4 ^ 2 * 3 ^ W :=
      (dubBaseX_repeated_window_exp_and_power_cutoff (by decide) (by decide)
        hgrowth.2.1 hgrowth.2.2 hmatch).1
    have hrhs_lt : 4 ^ 2 * 3 ^ W < 3 ^ (L + 2) := by
      calc
        4 ^ 2 * 3 ^ W < 3 ^ 3 * 3 ^ W :=
          Nat.mul_lt_mul_of_pos_right (by decide : 4 ^ 2 < 3 ^ 3) (Nat.pow_pos (by decide))
        _ = 3 ^ (L + 2) := by
          rw [← Nat.pow_add]
          have h : 3 + W = L + 2 := by dsimp [L]; ring
          rw [h]
    exact Nat.lt_asymm hexp hrhs_lt
  refine ⟨hexplicit, ?_⟩
  intro ξ hξ N_0
  obtain ⟨k0, hk0⟩ := exists_nat_gt (24 / ξ)
  set k := max N_0 (k0 + 1)
  have hk_ge : N_0 ≤ k := le_max_left _ _
  have hbernoulli : (1 : ℝ) + (k : ℝ) / 3 ≤ (4 / 3 : ℝ) ^ k := by
    clear hk_ge
    induction k with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        have hpos : (0 : ℝ) ≤ (m : ℝ) / 9 := by positivity
        nlinarith
  have hξk_ge8 : (8 : ℝ) ≤ ξ * (4 / 3 : ℝ) ^ k := by
    have h1 : 24 < (k0 : ℝ) * ξ := (div_lt_iff₀ hξ).mp hk0
    have h2 : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k0 ≤ k)
    have h3 : 24 ≤ (k : ℝ) * ξ := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hbernoulli (le_of_lt hξ)
    linarith
  obtain ⟨W, hW⟩ := exists_nat_gt (ξ * (4 / 3 : ℝ) ^ k)
  have hW_lt : (W : ℝ) < (3 : ℝ) ^ W := by exact_mod_cast (n_lt_q_pow (by decide : 2 ≤ 3) W)
  have hξk_ltW : ξ * (4 / 3 : ℝ) ^ k < (3 : ℝ) ^ W := lt_trans hW hW_lt
  obtain ⟨d, _, hd_out⟩ := hexplicit hξk_ge8 hξk_ltW
  refine ⟨k + d, by omega, ?_⟩
  have hmul : ξ * (4 / 3 : ℝ) ^ k * (4 / 3 : ℝ) ^ d = ξ * (4 / 3 : ℝ) ^ (k + d) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-! ## 9. Forward Funnel Pruning & Explicit $O(W)$ Escape for the $2/3$ and $25/36 \approx 0.6944$ Multi-Interval Unions -/

/-- Check whether the forward image $[3 a - s D, 3 b - s D) \cap [2 c, 2 d)$ is empty or
contained in $2 \cdot [e, f)$ for some $(e, f) \in T_{\text{next}}$. -/
def forwardPieceOk (D : ℤ) (Tnext : List (ℤ × ℤ)) (a b s c d : ℤ) : Bool :=
  let lo1 := 3 * a - s * D
  let lo2 := 2 * c
  let hi1 := 3 * b - s * D
  let hi2 := 2 * d
  decide (hi1 ≤ lo1 ∨ hi1 ≤ lo2 ∨ hi2 ≤ lo1 ∨ hi2 ≤ lo2) ||
    Tnext.any (fun ef =>
      decide ((2 * ef.1 ≤ lo1 ∨ 2 * ef.1 ≤ lo2) ∧ (hi1 ≤ 2 * ef.2 ∨ hi2 ≤ 2 * ef.2)))

/-- Check one forward pruning transition: if $y_n \in T_{\text{cur}}$ and $y_{n+1} \in T_{\text{amb}}$,
then $y_{n+1} \in T_{\text{next}}$. -/
def forwardStepOk (D : ℤ) (Tcur Tamb Tnext : List (ℤ × ℤ)) : Bool :=
  Tcur.all (fun ab =>
    ([-1, 0, 1, 2] : List ℤ).all (fun s =>
      Tamb.all (fun cd => forwardPieceOk D Tnext ab.1 ab.2 s cd.1 cd.2)))

/-- **Soundness of Forward Funnel Pruning (`inRatIntervalList_next_of_forwardStepOk`)**:
If `forwardStepOk D Tcur Tamb Tnext = true`, $y_n \in T_{\text{cur}}$, and $y_{n+1} \in T_{\text{amb}}$,
then $y_{n+1} \in T_{\text{next}}$. -/
theorem inRatIntervalList_next_of_forwardStepOk
    {D : ℤ} {Tcur Tamb Tnext : List (ℤ × ℤ)} {ξ : ℝ} {n : ℕ}
    (_hD : 0 < D)
    (hfwd : forwardStepOk D Tcur Tamb Tnext = true)
    (hcur : InRatIntervalList D Tcur (dubY ξ 0 n))
    (hamb : InRatIntervalList D Tamb (dubY ξ 0 (n + 1))) :
    InRatIntervalList D Tnext (dubY ξ 0 (n + 1)) := by
  rcases hcur with ⟨⟨a, b⟩, hab_mem, ha_lo, hb_hi⟩
  rcases hamb with ⟨⟨c, d⟩, hcd_mem, hc_lo, hd_hi⟩
  have hy0 := dubY_bounds ξ 0 n
  have hy1 := dubY_bounds ξ 0 (n + 1)
  have hlin := dubCarry_eq_fract_linear ξ 0 n
  set s := dubCarry ξ 0 n
  have hs_mem : s ∈ ([-1, 0, 1, 2] : List ℤ) := by
    have hlo : (-2 : ℝ) < (s : ℝ) := by linarith [hy0.1, hy1.2, hlin]
    have hhi : (s : ℝ) < (3 : ℝ) := by linarith [hy0.2, hy1.1, hlin]
    have hz1 : -2 < s := by exact_mod_cast hlo
    have hz2 : s < 3 := by exact_mod_cast hhi
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  unfold forwardStepOk at hfwd
  rw [List.all_eq_true] at hfwd
  have h1 := hfwd (a, b) hab_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 s hs_mem
  rw [List.all_eq_true] at h2
  have hpiece := h2 (c, d) hcd_mem
  unfold forwardPieceOk at hpiece
  rw [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hpiece
  have h2y_eq : 2 * ((D : ℝ) * dubY ξ 0 (n + 1)) = 3 * ((D : ℝ) * dubY ξ 0 n) - (s : ℝ) * (D : ℝ) := by
    dsimp [s]
    linear_combination (D : ℝ) * hlin
  have hlo1_real : ((3 * a - s * D : ℤ) : ℝ) ≤ 2 * ((D : ℝ) * dubY ξ 0 (n + 1)) := by
    push_cast; linarith
  have hhi1_real : 2 * ((D : ℝ) * dubY ξ 0 (n + 1)) < ((3 * b - s * D : ℤ) : ℝ) := by
    push_cast; linarith
  have hlo2_real : ((2 * c : ℤ) : ℝ) ≤ 2 * ((D : ℝ) * dubY ξ 0 (n + 1)) := by
    push_cast; linarith
  have hhi2_real : 2 * ((D : ℝ) * dubY ξ 0 (n + 1)) < ((2 * d : ℤ) : ℝ) := by
    push_cast; linarith
  rcases hpiece with hempty | ⟨⟨e, f⟩, hef_mem, hef_ok⟩
  · exfalso
    rcases hempty with hle1 | hle2 | hle3 | hle4
    · have h : ((3 * b - s * D : ℤ) : ℝ) ≤ ((3 * a - s * D : ℤ) : ℝ) := by exact_mod_cast hle1
      linarith
    · have h : ((3 * b - s * D : ℤ) : ℝ) ≤ ((2 * c : ℤ) : ℝ) := by exact_mod_cast hle2
      linarith
    · have h : ((2 * d : ℤ) : ℝ) ≤ ((3 * a - s * D : ℤ) : ℝ) := by exact_mod_cast hle3
      linarith
    · have h : ((2 * d : ℤ) : ℝ) ≤ ((2 * c : ℤ) : ℝ) := by exact_mod_cast hle4
      linarith
  · rw [decide_eq_true_eq] at hef_ok
    refine ⟨(e, f), hef_mem, ?_, ?_⟩
    · rcases hef_ok.1 with he1 | he2
      · have h : ((2 * e : ℤ) : ℝ) ≤ ((3 * a - s * D : ℤ) : ℝ) := by exact_mod_cast he1
        push_cast at h; linarith
      · have h : ((2 * e : ℤ) : ℝ) ≤ ((2 * c : ℤ) : ℝ) := by exact_mod_cast he2
        push_cast at h; linarith
    · rcases hef_ok.2 with hf1 | hf2
      · have h : ((3 * b - s * D : ℤ) : ℝ) ≤ ((2 * f : ℤ) : ℝ) := by exact_mod_cast hf1
        push_cast at h; linarith
      · have h : ((2 * d : ℤ) : ℝ) ≤ ((2 * f : ℤ) : ℝ) := by exact_mod_cast hf2
        push_cast at h; linarith

/-- Base 5-interval union $U_{2/3} = [0, 1/9) \cup [1/6, 4/9) \cup [1/2, 5/9) \cup [11/18, 7/9) \cup [5/6, 8/9)$
of total length $2 / 3 \approx 0.6667 > 7 / 12 > 1 / 2$ scaled by $D = 118098$. -/
def unionTwoThirdsBase : List (ℤ × ℤ) :=
  [(0, 13122), (19683, 52488), (59049, 65610), (72171, 91854), (98415, 104976)]

/-- 9-step backward funnel for $U_{2/3}$ over $D = 118098$. -/
def funnelTwoThirdsLevels : List (List (ℤ × ℤ)) :=
  [ [(0, 13122), (19683, 34992), (39366, 52488), (59049, 65610), (72171, 74358), (78732, 91854), (98415, 104976)],
    [(0, 10206), (19683, 23328), (26244, 34992), (39366, 49572), (59049, 62694), (72171, 74358), (78732, 88938), (98415, 102060)],
    [(0, 10206), (19683, 23328), (26244, 33048), (39366, 49572), (59049, 62694), (72171, 72414), (78732, 88938), (98415, 102060)],
    [(0, 8910), (19683, 22032), (26244, 33048), (39366, 48276), (59049, 61398), (72171, 72414), (78732, 87642), (98415, 100764)],
    [(0, 5940), (8748, 8910), (19683, 22032), (26244, 32184), (39366, 45306), (48114, 48276), (59049, 61398), (78732, 84672), (87480, 87642), (98415, 100764)],
    [(0, 5940), (19683, 21456), (26244, 32184), (39366, 45306), (59049, 60822), (78732, 84672), (98415, 100188)],
    [(0, 3960), (19683, 21456), (26244, 30204), (39366, 43326), (59049, 60822), (78732, 82692), (98415, 100188)],
    [(0, 2640), (19683, 20136), (26244, 28884), (39366, 42006), (59049, 59502), (78732, 81372), (98415, 98868)],
    [(0, 1760), (26244, 28004), (39366, 41126), (78732, 80492)] ]

def funnelTwoThirdsT9 : List (ℤ × ℤ) :=
  [(0, 1760), (26244, 28004), (39366, 41126), (78732, 80492)]

def funnelTwoThirdsF1 : List (ℤ × ℤ) :=
  [(0, 1760), (39366, 41126)]

private theorem funnelTwoThirds_valid :
    funnelChainOk 118098 unionTwoThirdsBase funnelTwoThirdsT9 unionTwoThirdsBase
      funnelTwoThirdsLevels = true ∧
    forwardStepOk 118098 funnelTwoThirdsT9 funnelTwoThirdsT9 funnelTwoThirdsF1 = true ∧
    forwardStepOk 118098 funnelTwoThirdsF1 funnelTwoThirdsT9 [(0, 1760)] = true := by
  decide

/-- Predicate for membership in the 5-interval union
$U_{2/3} = [0, 1/9) \cup [1/6, 4/9) \cup [1/2, 5/9) \cup [11/18, 7/9) \cup [5/6, 8/9)$ of total length $2/3 > 1/2$. -/
def InUnionTwoThirds (y : ℝ) : Prop :=
  (0 ≤ y ∧ y < (1 / 9 : ℝ)) ∨
    ((1 / 6 : ℝ) ≤ y ∧ y < (4 / 9 : ℝ)) ∨
    ((1 / 2 : ℝ) ≤ y ∧ y < (5 / 9 : ℝ)) ∨
    ((11 / 18 : ℝ) ≤ y ∧ y < (7 / 9 : ℝ)) ∨
    ((5 / 6 : ℝ) ≤ y ∧ y < (8 / 9 : ℝ))

/-- **Explicit $W + 14$ Escape Bound & Infinite-Horizon Emptiness for the $2/3 > 7/12 > 1/2$
Union $U_{2/3}$ (`union_two_thirds_explicit_and_infinite_escape`)**:
1. **Explicit $W + 14$ Escape Bound:** For **every** $\xi \in [1, 2^W)$, there exists an
   index $n \le W + 14$ such that $\{\xi (3/2)^n\} \notin U_{2/3}$.
2. **Infinite-Horizon Emptiness:** For **every** real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$,
   there exists $n \ge N_0$ such that $\{\xi (3/2)^n\} \notin U_{2/3}$. -/
theorem union_two_thirds_explicit_and_infinite_escape :
    (∀ {ξ : ℝ} {W : ℕ}, (1 : ℝ) ≤ ξ → ξ < (2 : ℝ) ^ W →
      ∃ n ≤ W + 14, ¬ InUnionTwoThirds (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) ∧
    (∀ {ξ : ℝ}, 0 < ξ → ∀ N_0 : ℕ,
      ∃ n ≥ N_0, ¬ InUnionTwoThirds (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) := by
  have hexplicit :
      ∀ {ξ : ℝ} {W : ℕ}, (1 : ℝ) ≤ ξ → ξ < (2 : ℝ) ^ W →
        ∃ n ≤ W + 14, ¬ InUnionTwoThirds (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
    intro ξ W hξ1 hξW
    by_contra hno
    push_neg at hno
    set N := W + 14
    have hmemU : ∀ n ≤ N, InRatIntervalList 118098 unionTwoThirdsBase (dubY ξ 0 n) := by
      intro n hn
      have hu := hno n hn
      unfold InUnionTwoThirds at hu
      unfold InRatIntervalList unionTwoThirdsBase dubY
      rw [add_zero]
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(0, 13122), by simp, by linarith, by linarith⟩
      · exact ⟨(19683, 52488), by simp, by linarith, by linarith⟩
      · exact ⟨(59049, 65610), by simp, by linarith, by linarith⟩
      · exact ⟨(72171, 91854), by simp, by linarith, by linarith⟩
      · exact ⟨(98415, 104976), by simp, by linarith, by linarith⟩
    have hT9 :=
      inRatIntervalList_terminal_of_funnelChainOk (by decide : (0 : ℤ) < 118098) hmemU
        funnelTwoThirdsLevels unionTwoThirdsBase 0 funnelTwoThirds_valid.1
        (fun n hn => hmemU n (by omega))
    have hF1 : ∀ n, 1 ≤ n → n ≤ W + 5 → InRatIntervalList 118098 funnelTwoThirdsF1 (dubY ξ 0 n) := by
      intro n hn1 hn5
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact inRatIntervalList_next_of_forwardStepOk (by decide) funnelTwoThirds_valid.2.1
        (hT9 m (by simp [funnelTwoThirdsLevels, N]; omega))
        (hT9 (m + 1) (by simp [funnelTwoThirdsLevels, N]; omega))
    have hF2 : ∀ n, 2 ≤ n → n ≤ W + 5 → InRatIntervalList 118098 [(0, 1760)] (dubY ξ 0 n) := by
      intro n hn2 hn5
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact inRatIntervalList_next_of_forwardStepOk (by decide) funnelTwoThirds_valid.2.2
        (hF1 m (by omega) (by omega))
        (hT9 (m + 1) (by simp [funnelTwoThirdsLevels, N]; omega))
    have hzero : ∀ n, 2 ≤ n → n ≤ W + 4 → dubCarry ξ 0 n = 0 := by
      intro n hn2 hn4
      have hy0_mem := hF2 n hn2 (by omega)
      have hy1_mem := hF2 (n + 1) (by omega) (by omega)
      unfold InRatIntervalList at hy0_mem hy1_mem
      rcases hy0_mem with ⟨ab0, hab0, hlo0, hhi0⟩
      rcases hy1_mem with ⟨ab1, hab1, hlo1, hhi1⟩
      simp only [List.mem_singleton] at hab0 hab1
      subst hab0; subst hab1
      dsimp at hlo0 hhi0 hlo1 hhi1
      push_cast at hlo0 hhi0 hlo1 hhi1
      have hlin := dubCarry_eq_fract_linear ξ 0 n
      have hlo : (-1 : ℝ) < (dubCarry ξ 0 n : ℝ) := by linarith
      have hhi : (dubCarry ξ 0 n : ℝ) < (1 : ℝ) := by linarith
      have hz1 : -1 < dubCarry ξ 0 n := by exact_mod_cast hlo
      have hz2 : dubCarry ξ 0 n < 1 := by exact_mod_cast hhi
      omega
    have hmatch : ∀ t < W + 2, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (3 + t) := by
      intro t ht
      rw [hzero (2 + t) (by omega) (by omega), hzero (3 + t) (by omega) (by omega)]
    have hexp :=
      dubX_repeated_window_exp_bound (i := 2) (j := 3) (L := W + 2)
        hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
    have hpow : 3 ^ 3 * 2 ^ W < 2 ^ ((W + 2) + 3) := by
      calc
        3 ^ 3 * 2 ^ W = 27 * 2 ^ W := by ring
        _ < 32 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
        _ = 2 ^ ((W + 2) + 3) := by
          have h : (W + 2) + 3 = 5 + W := by omega
          rw [h, Nat.pow_add]
    omega
  refine ⟨hexplicit, ?_⟩
  intro ξ hξ N_0
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  obtain ⟨m, _, hm_out⟩ := hexplicit hge1 hltW
  refine ⟨k + m, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = ξ * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-- Base 6-interval union $U_{25/36} = [0, 1/12) \cup [1/9, 11/36) \cup [4/9, 2/3) \cup [25/36, 3/4) \cup [5/6, 8/9) \cup [11/12, 1)$
of total length $25 / 36 \approx 0.6944 > 2 / 3 > 1 / 2$ scaled by $D = 708588$. -/
def unionTwentyFiveThirtySixthsBase : List (ℤ × ℤ) :=
  [(0, 59049), (78732, 216513), (314928, 472392), (492075, 531441), (590490, 629856), (649539, 708588)]

/-- 11-step backward funnel for $U_{25/36}$ over $D = 708588$. -/
def funnelTwentyFiveThirtySixthsLevels : List (List (ℤ × ℤ)) :=
  [ [(0, 59049), (78732, 144342), (157464, 183708), (196830, 216513), (314928, 380538), (393660, 419904), (433026, 472392), (492075, 531441), (590490, 616734), (649539, 656100), (669222, 708588)],
    [(0, 59049), (78732, 144342), (157464, 174960), (196830, 216513), (314928, 380538), (393660, 411156), (433026, 472392), (492075, 531441), (590490, 616734), (669222, 708588)],
    [(0, 39366), (52488, 59049), (78732, 118098), (131220, 144342), (157464, 174960), (209952, 216513), (314928, 354294), (367416, 380538), (393660, 411156), (446148, 472392), (492075, 511758), (524880, 531441), (603612, 616734), (682344, 708588)],
    [(0, 39366), (52488, 59049), (87480, 118098), (139968, 144342), (166212, 174960), (209952, 216513), (323676, 354294), (376164, 380538), (402408, 411156), (446148, 472392), (492075, 511758), (524880, 531441), (612360, 616734), (682344, 708588)],
    [(0, 39366), (58320, 59049), (91854, 118098), (139968, 144342), (172044, 174960), (215784, 216513), (328050, 354294), (376164, 380538), (408240, 411156), (451980, 472392), (492075, 511758), (530712, 531441), (612360, 616734), (688176, 708588)],
    [(0, 39366), (91854, 118098), (143856, 144342), (172044, 174960), (328050, 354294), (380052, 380538), (408240, 411156), (454896, 472392), (492075, 511758), (616248, 616734), (691092, 708588)],
    [(0, 37908), (91854, 116640), (174636, 174960), (328050, 352836), (410832, 411156), (454896, 472392), (492075, 510300), (691092, 708588)],
    [(0, 25272), (37692, 37908), (91854, 104004), (116424, 116640), (328050, 340200), (352620, 352836), (454896, 472392), (492075, 497664), (510084, 510300), (691092, 708588)],
    [(0, 25272), (91854, 104004), (328050, 340200), (454896, 472392), (497520, 497664), (691092, 708588)],
    [(0, 16848), (95484, 95580), (331680, 331776), (454896, 472392), (691092, 708588)],
    [(0, 11232), (457316, 472392), (693512, 708588)] ]

def funnelTwentyFiveThirtySixthsT11 : List (ℤ × ℤ) :=
  [(0, 11232), (457316, 472392), (693512, 708588)]

def funnelTwentyFiveThirtySixthsF1 : List (ℤ × ℤ) :=
  [(0, 11232), (693512, 708588)]

set_option maxHeartbeats 800000 in
private theorem funnelTwentyFiveThirtySixths_valid :
    funnelChainOk 708588 unionTwentyFiveThirtySixthsBase funnelTwentyFiveThirtySixthsT11
      unionTwentyFiveThirtySixthsBase funnelTwentyFiveThirtySixthsLevels = true ∧
    forwardStepOk 708588 funnelTwentyFiveThirtySixthsT11 funnelTwentyFiveThirtySixthsT11
      funnelTwentyFiveThirtySixthsF1 = true := by
  decide

/-- Predicate for membership in the 6-interval union
$U_{25/36} = [0, 1/12) \cup [1/9, 11/36) \cup [4/9, 2/3) \cup [25/36, 3/4) \cup [5/6, 8/9) \cup [11/12, 1)$
of total length $25/36 \approx 0.6944 > 2/3 > 1/2$. -/
def InUnionTwentyFiveThirtySixths (y : ℝ) : Prop :=
  (0 ≤ y ∧ y < (1 / 12 : ℝ)) ∨
    ((1 / 9 : ℝ) ≤ y ∧ y < (11 / 36 : ℝ)) ∨
    ((4 / 9 : ℝ) ≤ y ∧ y < (2 / 3 : ℝ)) ∨
    ((25 / 36 : ℝ) ≤ y ∧ y < (3 / 4 : ℝ)) ∨
    ((5 / 6 : ℝ) ≤ y ∧ y < (8 / 9 : ℝ)) ∨
    ((11 / 12 : ℝ) ≤ y ∧ y < (1 : ℝ))

/-- **Explicit $W + 16$ Escape Bound & Infinite-Horizon Emptiness for the $25/36 \approx 0.6944 > 2/3$
Union $U_{25/36}$ (`union_twenty_five_thirty_sixths_explicit_and_infinite_escape`)**:
1. **Explicit $W + 16$ Escape Bound:** For **every** $\xi \in [1, 2^W)$, there exists an
   index $n \le W + 16$ such that $\{\xi (3/2)^n\} \notin U_{25/36}$.
2. **Infinite-Horizon Emptiness:** For **every** real $\xi > 0$ and threshold $N_0 \in \mathbb{N}$,
   there exists $n \ge N_0$ such that $\{\xi (3/2)^n\} \notin U_{25/36}$. -/
theorem union_twenty_five_thirty_sixths_explicit_and_infinite_escape :
    (∀ {ξ : ℝ} {W : ℕ}, (1 : ℝ) ≤ ξ → ξ < (2 : ℝ) ^ W →
      ∃ n ≤ W + 16, ¬ InUnionTwentyFiveThirtySixths (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) ∧
    (∀ {ξ : ℝ}, 0 < ξ → ∀ N_0 : ℕ,
      ∃ n ≥ N_0, ¬ InUnionTwentyFiveThirtySixths (Int.fract (ξ * (3 / 2 : ℝ) ^ n))) := by
  have hexplicit :
      ∀ {ξ : ℝ} {W : ℕ}, (1 : ℝ) ≤ ξ → ξ < (2 : ℝ) ^ W →
        ∃ n ≤ W + 16, ¬ InUnionTwentyFiveThirtySixths (Int.fract (ξ * (3 / 2 : ℝ) ^ n)) := by
    intro ξ W hξ1 hξW
    by_contra hno
    push_neg at hno
    set N := W + 16
    have hmemU : ∀ n ≤ N, InRatIntervalList 708588 unionTwentyFiveThirtySixthsBase (dubY ξ 0 n) := by
      intro n hn
      have hu := hno n hn
      unfold InUnionTwentyFiveThirtySixths at hu
      unfold InRatIntervalList unionTwentyFiveThirtySixthsBase dubY
      rw [add_zero]
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(0, 59049), by simp, by linarith, by linarith⟩
      · exact ⟨(78732, 216513), by simp, by linarith, by linarith⟩
      · exact ⟨(314928, 472392), by simp, by linarith, by linarith⟩
      · exact ⟨(492075, 531441), by simp, by linarith, by linarith⟩
      · exact ⟨(590490, 629856), by simp, by linarith, by linarith⟩
      · exact ⟨(649539, 708588), by simp, by linarith, by linarith⟩
    have hT11 :=
      inRatIntervalList_terminal_of_funnelChainOk (by decide : (0 : ℤ) < 708588) hmemU
        funnelTwentyFiveThirtySixthsLevels unionTwentyFiveThirtySixthsBase 0
        funnelTwentyFiveThirtySixths_valid.1 (fun n hn => hmemU n (by omega))
    have hF1 :
        ∀ n, 1 ≤ n → n ≤ W + 5 →
          dubY ξ 0 n < (1 / 5 : ℝ) ∨ (4 / 5 : ℝ) ≤ dubY ξ 0 n := by
      intro n hn1 hn5
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hmem_f1 :=
        inRatIntervalList_next_of_forwardStepOk (by decide) funnelTwentyFiveThirtySixths_valid.2
          (hT11 m (by simp [funnelTwentyFiveThirtySixthsLevels, N]; omega))
          (hT11 (m + 1) (by simp [funnelTwentyFiveThirtySixthsLevels, N]; omega))
      unfold InRatIntervalList funnelTwentyFiveThirtySixthsF1 at hmem_f1
      rcases hmem_f1 with ⟨ab, hab_mem, hlo, hhi⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hab_mem
      rcases hab_mem with rfl | rfl
      · dsimp at hlo hhi; push_cast at hlo hhi; exact Or.inl (by linarith)
      · dsimp at hlo hhi; push_cast at hlo hhi; exact Or.inr (by linarith)
    have hstep_eq : ∀ k, 1 ≤ k → k ≤ W + 3 → dubCarry ξ 0 (k + 1) = dubCarry ξ 0 k := by
      intro k hk1 hk3
      have hk0 := hF1 k hk1 (by omega)
      have hk1_mem := hF1 (k + 1) (by omega) (by omega)
      have hk2_mem := hF1 (k + 2) (by omega) (by omega)
      have hs0 := nearest_int_fifth_carry_step hk0 hk1_mem
      have hs1 := nearest_int_fifth_carry_step hk1_mem hk2_mem
      rcases hk0 with hlt | hge
      · rcases hs0.1 hlt with ⟨hc0, hlt1⟩
        rcases hs1.1 hlt1 with ⟨hc1, _⟩
        omega
      · rcases hs0.2 hge with ⟨hc0, hge1⟩
        rcases hs1.2 hge1 with ⟨hc1, _⟩
        omega
    have hmatch : ∀ t < W + 2, dubCarry ξ 0 (2 + t) = dubCarry ξ 0 (3 + t) := by
      intro t ht
      have hidx : 3 + t = (2 + t) + 1 := by omega
      rw [hidx, hstep_eq (2 + t) (by omega) (by omega)]
    have hexp :=
      dubX_repeated_window_exp_bound (i := 2) (j := 3) (L := W + 2)
        hξ1 hξW (by norm_num) (by norm_num) le_rfl (by omega) hmatch
    have hpow : 3 ^ 3 * 2 ^ W < 2 ^ ((W + 2) + 3) := by
      calc
        3 ^ 3 * 2 ^ W = 27 * 2 ^ W := by ring
        _ < 32 * 2 ^ W := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
        _ = 2 ^ ((W + 2) + 3) := by
          have h : (W + 2) + 3 = 5 + W := by omega
          rw [h, Nat.pow_add]
    omega
  refine ⟨hexplicit, ?_⟩
  intro ξ hξ N_0
  obtain ⟨k, W, hk_ge, _, hge1, hltW⟩ := exists_pow_shift_ge_one_and_lt_two_pow hξ N_0
  obtain ⟨m, _, hm_out⟩ := hexplicit hge1 hltW
  refine ⟨k + m, by omega, ?_⟩
  have hmul : ξ * (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ m = ξ * (3 / 2 : ℝ) ^ (k + m) := by
    rw [pow_add, mul_assoc]
  rwa [← hmul]

/-! ## 10. The Thue–Morse Period-Doubling Cantor Cascade on $[c, 1-c]$, Exact Fermat-Denominator Reduction, and the $[2/7, 5/7]$ Cutoff Between $k = 4$ and $k = 5$ -/

/-- Carry accumulator $A(T_k) = \sum_{t=0}^{2^k - 1} 3^{2^k - 1 - t} 2^t \operatorname{tmBit}(t)$
of the length-$2^k$ Thue–Morse prefix $T_k = T_{k-1} \overline{T_{k-1}}$. -/
def tmCascadeCarryAcc : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      (3 : ℤ) ^ (2 ^ k) * tmCascadeCarryAcc k +
        (2 : ℤ) ^ (2 ^ k) * (((3 : ℤ) ^ (2 ^ k) - (2 : ℤ) ^ (2 ^ k)) - tmCascadeCarryAcc k)

/-- Homogeneous Thue–Morse Mahler product
$\operatorname{tmMahlerProd}(k) = \prod_{n=0}^{k-1} (3^{2^n} - 2^{2^n})$. -/
def tmMahlerProd : ℕ → ℤ
  | 0 => 1
  | k + 1 => tmMahlerProd k * ((3 : ℤ) ^ (2 ^ k) - (2 : ℤ) ^ (2 ^ k))

/-- **Exact Factorization of the Thue–Morse Carry Accumulator (`tmCascadeCarryAcc_succ_factored`)**:
Because $T_{k+1} = T_k \overline{T_k}$, the carry accumulator $A(T_{k+1})$ factors by
$(3^{2^k} - 2^{2^k})$, reducing the period-$2^{k+1}$ denominator from $3^{2^{k+1}} - 2^{2^{k+1}}$
to the Fermat-like factor $3^{2^k} + 2^{2^k}$:
`tmCascadeCarryAcc (k + 1) = (3^(2^k) - 2^(2^k)) * (tmCascadeCarryAcc k + 2^(2^k))`. -/
theorem tmCascadeCarryAcc_succ_factored (k : ℕ) :
    tmCascadeCarryAcc (k + 1) =
      ((3 : ℤ) ^ (2 ^ k) - (2 : ℤ) ^ (2 ^ k)) * (tmCascadeCarryAcc k + (2 : ℤ) ^ (2 ^ k)) := by
  conv_lhs => rw [tmCascadeCarryAcc]
  ring

/-- **Exact Thue–Morse Mahler Product Identity (`tmCascadeCarryAcc_mahlerProd_identity`)**:
For every $k \in \mathbb{N}$:
$$(3^{2^k} - 2^{2^k}) - 2 A(T_k) = \prod_{n=0}^{k-1} \left(3^{2^n} - 2^{2^n}\right).$$ -/
theorem tmCascadeCarryAcc_mahlerProd_identity (k : ℕ) :
    ((3 : ℤ) ^ (2 ^ k) - (2 : ℤ) ^ (2 ^ k)) - 2 * tmCascadeCarryAcc k = tmMahlerProd k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hpow3 : (3 : ℤ) ^ (2 ^ (k + 1)) = ((3 : ℤ) ^ (2 ^ k)) ^ 2 := by
        rw [Nat.pow_succ, pow_mul]
      have hpow2 : (2 : ℤ) ^ (2 ^ (k + 1)) = ((2 : ℤ) ^ (2 ^ k)) ^ 2 := by
        rw [Nat.pow_succ, pow_mul]
      rw [tmCascadeCarryAcc_succ_factored, tmMahlerProd, hpow3, hpow2, ← ih]
      ring

/-- Fermat-like denominator $F_m = 3^{2^m} + 2^{2^m}$ of the period-$2^{m+1}$ Thue–Morse cycle. -/
def tmFermatDenom (m : ℕ) : ℤ :=
  (3 : ℤ) ^ (2 ^ m) + (2 : ℤ) ^ (2 ^ m)

theorem tmFermatDenom_pos (m : ℕ) : 0 < tmFermatDenom m := by
  unfold tmFermatDenom
  positivity

/-- Half-period orbit numerator $3^{2^m} - A(T_m)$ at index $r = 2^m$ of the period-$2^{m+1}$
Thue–Morse cycle, and minimum orbit numerator $N_{\min}(m) = \frac{3(3^{2^m} - A(T_m)) - (3^{2^m} + 2^{2^m})}{2}$
at index $r = 2^m + 1$. -/
noncomputable def tmCascadeEntry (k : ℕ) : ℝ :=
  let m := k - 1
  (3 * ((3 : ℝ) ^ (2 ^ m) - (tmCascadeCarryAcc m : ℝ)) - (tmFermatDenom m : ℝ)) /
    (2 * (tmFermatDenom m : ℝ))

/-- **Exact Closed-Form Thue–Morse Cantor Cascade Entry Formula (`tmCascadeEntry_closed_form`)**:
For every cascade level $k \ge 1$ ($m = k - 1$, period $2^k$):
1. $(3^{2^{k-1}} + 2^{2^{k-1}})(4 c_k - 1) = 3 \prod_{n=0}^{k-2} (3^{2^n} - 2^{2^n})$, and
2. $4 c_k - 1 = \frac{3 \cdot \operatorname{tmMahlerProd}(k - 1)}{3^{2^{k-1}} + 2^{2^{k-1}}}$. -/
theorem tmCascadeEntry_closed_form {k : ℕ} (_hk : 1 ≤ k) :
    (tmFermatDenom (k - 1) : ℝ) * (4 * tmCascadeEntry k - 1) =
      3 * (tmMahlerProd (k - 1) : ℝ) ∧
    4 * tmCascadeEntry k - 1 =
      (3 * (tmMahlerProd (k - 1) : ℝ)) / (tmFermatDenom (k - 1) : ℝ) := by
  set m := k - 1
  have hF_pos : (0 : ℝ) < (tmFermatDenom m : ℝ) := by exact_mod_cast tmFermatDenom_pos m
  have hF_ne : (tmFermatDenom m : ℝ) ≠ 0 := ne_of_gt hF_pos
  have hid_int := tmCascadeCarryAcc_mahlerProd_identity m
  have hid_real :
      ((3 : ℝ) ^ (2 ^ m) - (2 : ℝ) ^ (2 ^ m)) - 2 * (tmCascadeCarryAcc m : ℝ) =
        (tmMahlerProd m : ℝ) := by
    exact_mod_cast hid_int
  have hF_def : (tmFermatDenom m : ℝ) = (3 : ℝ) ^ (2 ^ m) + (2 : ℝ) ^ (2 ^ m) := by
    unfold tmFermatDenom
    push_cast
    rfl
  have hmul :
      (tmFermatDenom m : ℝ) * (4 * tmCascadeEntry k - 1) = 3 * (tmMahlerProd m : ℝ) := by
    unfold tmCascadeEntry
    dsimp [m]
    have h1 :
        (tmFermatDenom m : ℝ) *
          (4 * ((3 * ((3 : ℝ) ^ (2 ^ m) - (tmCascadeCarryAcc m : ℝ)) - (tmFermatDenom m : ℝ)) /
            (2 * (tmFermatDenom m : ℝ))) - 1) =
          6 * ((3 : ℝ) ^ (2 ^ m) - (tmCascadeCarryAcc m : ℝ)) - 3 * (tmFermatDenom m : ℝ) := by
      field_simp [hF_ne]
      ring
    rw [h1, hF_def, ← hid_real]
    ring
  refine ⟨hmul, ?_⟩
  rw [eq_div_iff hF_ne]
  linarith

/-- **Exact Difference-of-Squares Ratio & Strict Descent of the Thue–Morse Cascade
(`tmCascadeEntry_step_ratio_and_strictAnti`)**:
For every cascade level $k \ge 1$:
1. $(3^{2^k} + 2^{2^k})(4 c_{k+1} - 1) = (3^{2^k} - 2^{2^k})(4 c_k - 1)$,
2. $\frac{1}{4} < c_{k+1} < c_k$. -/
theorem tmCascadeEntry_step_ratio_and_strictAnti {k : ℕ} (hk : 1 ≤ k) :
    ((3 : ℝ) ^ (2 ^ k) + (2 : ℝ) ^ (2 ^ k)) * (4 * tmCascadeEntry (k + 1) - 1) =
      ((3 : ℝ) ^ (2 ^ k) - (2 : ℝ) ^ (2 ^ k)) * (4 * tmCascadeEntry k - 1) ∧
    (1 / 4 : ℝ) < tmCascadeEntry (k + 1) ∧
    tmCascadeEntry (k + 1) < tmCascadeEntry k := by
  have hk1 : (k + 1) - 1 = k := by omega
  have hcf_k := (tmCascadeEntry_closed_form hk).1
  have hcf_k1 := (tmCascadeEntry_closed_form (by omega : 1 ≤ k + 1)).1
  rw [hk1] at hcf_k1
  set m := k - 1
  have hm_succ : k = m + 1 := by omega
  have hdiff_sq :
      (tmFermatDenom m : ℝ) * ((3 : ℝ) ^ (2 ^ m) - (2 : ℝ) ^ (2 ^ m)) =
        (3 : ℝ) ^ (2 ^ k) - (2 : ℝ) ^ (2 ^ k) := by
    unfold tmFermatDenom
    push_cast
    rw [hm_succ, Nat.pow_succ, pow_mul, pow_mul]
    ring
  have hprod_succ :
      (tmMahlerProd k : ℝ) =
        (tmMahlerProd m : ℝ) * ((3 : ℝ) ^ (2 ^ m) - (2 : ℝ) ^ (2 ^ m)) := by
    conv_lhs => rw [hm_succ, tmMahlerProd]
    push_cast
    rfl
  have hFk_def : (tmFermatDenom k : ℝ) = (3 : ℝ) ^ (2 ^ k) + (2 : ℝ) ^ (2 ^ k) := by
    unfold tmFermatDenom
    push_cast
    rfl
  have hratio :
      ((3 : ℝ) ^ (2 ^ k) + (2 : ℝ) ^ (2 ^ k)) * (4 * tmCascadeEntry (k + 1) - 1) =
        ((3 : ℝ) ^ (2 ^ k) - (2 : ℝ) ^ (2 ^ k)) * (4 * tmCascadeEntry k - 1) := by
    rw [← hFk_def, hcf_k1, hprod_succ, ← hdiff_sq]
    linear_combination ((3 : ℝ) ^ (2 ^ m) - (2 : ℝ) ^ (2 ^ m)) * hcf_k.symm
  have hprod_pos : ∀ n : ℕ, 0 < tmMahlerProd n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        unfold tmMahlerProd
        have hlt : (2 : ℤ) ^ (2 ^ n) < (3 : ℤ) ^ (2 ^ n) := by
          exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide)))
        exact mul_pos ih (by linarith)
  have h4ck1_pos : 0 < 4 * tmCascadeEntry (k + 1) - 1 := by
    rw [(tmCascadeEntry_closed_form (by omega : 1 ≤ k + 1)).2, hk1]
    have h1 : (0 : ℝ) < (tmMahlerProd k : ℝ) := by exact_mod_cast hprod_pos k
    have h2 : (0 : ℝ) < (tmFermatDenom k : ℝ) := by exact_mod_cast tmFermatDenom_pos k
    positivity
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ k) := by positivity
  have h3pow_gt : (2 : ℝ) ^ (2 ^ k) < (3 : ℝ) ^ (2 ^ k) := by
    exact_mod_cast Nat.pow_lt_pow_left (by decide : 2 < 3) (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide)))
  have hlt_4 : 4 * tmCascadeEntry (k + 1) - 1 < 4 * tmCascadeEntry k - 1 := by
    have hdiff :
        ((3 : ℝ) ^ (2 ^ k) - (2 : ℝ) ^ (2 ^ k)) * (4 * tmCascadeEntry k - 1) -
          ((3 : ℝ) ^ (2 ^ k) - (2 : ℝ) ^ (2 ^ k)) * (4 * tmCascadeEntry (k + 1) - 1) =
          2 * (2 : ℝ) ^ (2 ^ k) * (4 * tmCascadeEntry (k + 1) - 1) := by
      linarith [hratio]
    have hpos_rhs : 0 < 2 * (2 : ℝ) ^ (2 ^ k) * (4 * tmCascadeEntry (k + 1) - 1) := by positivity
    nlinarith
  exact ⟨hratio, by linarith, by linarith⟩

/-- **Exact Rational Values of $c_1, \dots, c_5$ and the $[2/7, 5/7]$ Cutoff Between $k = 4$ and $k = 5$
(`tmCascadeEntry_explicit_values_and_two_sevenths_cutoff`)**:
1. $c_1 = 2/5$, $c_2 = 4/13$, $c_3 = 28/97$, $c_4 = 1948/6817$, $c_5 = 12314908/43112257$,
2. $c_5 < 2/7 < c_4 < c_3 < c_2 < c_1$, with exact margins
   $c_4 - 2/7 = \frac{2}{47719} > 0$ and $2/7 - c_5 = \frac{20198}{301785799} > 0$.
This explains why the centred window $[2/7, 5/7]$ admits the first 4 levels of the
Thue–Morse period-doubling cascade (periods $2, 4, 8, 16$, matching the binary partition
growth $2, 4, 6, 10, \dots, 166$ up to depth $2^4 - 1 = 15$) and cuts off the 5th bifurcation
at depth $2^4 = 16$ (period $32$). -/
theorem tmCascadeEntry_explicit_values_and_two_sevenths_cutoff :
    tmCascadeEntry 1 = (2 / 5 : ℝ) ∧
    tmCascadeEntry 2 = (4 / 13 : ℝ) ∧
    tmCascadeEntry 3 = (28 / 97 : ℝ) ∧
    tmCascadeEntry 4 = (1948 / 6817 : ℝ) ∧
    tmCascadeEntry 5 = (12314908 / 43112257 : ℝ) ∧
    tmCascadeEntry 4 - (2 / 7 : ℝ) = (2 / 47719 : ℝ) ∧
    (2 / 7 : ℝ) - tmCascadeEntry 5 = (20158 / 301785799 : ℝ) ∧
    tmCascadeEntry 5 < (2 / 7 : ℝ) ∧
    (2 / 7 : ℝ) < tmCascadeEntry 4 := by
  have hacc :
      tmCascadeCarryAcc 0 = 0 ∧ tmCascadeCarryAcc 1 = 2 ∧
      tmCascadeCarryAcc 2 = 30 ∧ tmCascadeCarryAcc 3 = 2990 ∧
      tmCascadeCarryAcc 4 = 20466030 := by
    decide
  have hF :
      tmFermatDenom 0 = 5 ∧ tmFermatDenom 1 = 13 ∧
      tmFermatDenom 2 = 97 ∧ tmFermatDenom 3 = 6817 ∧
      tmFermatDenom 4 = 43112257 := by
    decide
  have h1 : tmCascadeEntry 1 = (2 / 5 : ℝ) := by
    unfold tmCascadeEntry; dsimp; rw [hacc.1, hF.1]; norm_num
  have h2 : tmCascadeEntry 2 = (4 / 13 : ℝ) := by
    unfold tmCascadeEntry; dsimp; rw [hacc.2.1, hF.2.1]; norm_num
  have h3 : tmCascadeEntry 3 = (28 / 97 : ℝ) := by
    unfold tmCascadeEntry; dsimp; rw [hacc.2.2.1, hF.2.2.1]; norm_num
  have h4 : tmCascadeEntry 4 = (1948 / 6817 : ℝ) := by
    unfold tmCascadeEntry; dsimp; rw [hacc.2.2.2.1, hF.2.2.2.1]; norm_num
  have h5 : tmCascadeEntry 5 = (12314908 / 43112257 : ℝ) := by
    unfold tmCascadeEntry; dsimp; rw [hacc.2.2.2.2, hF.2.2.2.2]; norm_num
  refine ⟨h1, h2, h3, h4, h5,
    by rw [h4]; norm_num,
    by rw [h5]; norm_num,
    by rw [h5]; norm_num,
    by rw [h4]; norm_num⟩

/-- **General Fermat-Denominator $2^{2^k m}$-Divisibility Trap on Level-$k$ Thue–Morse Cycles
(`tmCascade_periodic_orbit_two_pow_dvd`)**:
Generalizes `dubickas2008_four_cycle_two_pow_dvd` ($k = 2, F_1 = 13$) to **every** level
$k \ge 1$ of the Thue–Morse cascade ($F_{k-1} = 3^{2^{k-1}} + 2^{2^{k-1}} \in \{5, 13, 97, 6817, \dots\}$):
whenever $y_r = \frac{v}{F_{k-1}}$ and $y_{r + 2^k m} = \frac{v}{F_{k-1}}$, the integer part
$x_r = \lfloor \xi (3/2)^r \rfloor$ satisfies:
$$2^{2^k m} \;\Big|\; \Big(\big(3^{2^{k-1}} + 2^{2^{k-1}}\big) x_r + v\Big).$$ -/
theorem tmCascade_periodic_orbit_two_pow_dvd {ξ : ℝ} {k r m : ℕ} {v : ℤ}
    (hy_r : dubY ξ 0 r = (v : ℝ) / (tmFermatDenom (k - 1) : ℝ))
    (hy_rm : dubY ξ 0 (r + 2 ^ k * m) = (v : ℝ) / (tmFermatDenom (k - 1) : ℝ)) :
    ((2 : ℤ) ^ (2 ^ k * m)) ∣ (tmFermatDenom (k - 1) * dubX ξ 0 r + v) := by
  set L := 2 ^ k * m
  set F := tmFermatDenom (k - 1)
  have hF_pos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast tmFermatDenom_pos (k - 1)
  have hF_ne : (F : ℝ) ≠ 0 := ne_of_gt hF_pos
  have hX := dubX_multi_step_carry_identity ξ 0 r L
  have hY := dubY_multi_step_carry_identity ξ 0 r L
  rw [hy_r, hy_rm] at hY
  have hY_cleared :
      (2 : ℝ) ^ L * (v : ℝ) =
        (3 : ℝ) ^ L * (v : ℝ) - (F : ℝ) * (dubCarryAcc (dubCarry ξ 0) r L : ℝ) := by
    have h := congrArg ((F : ℝ) * ·) hY
    field_simp [hF_ne] at h
    linarith
  have hY_int :
      (2 : ℤ) ^ L * v = (3 : ℤ) ^ L * v - F * dubCarryAcc (dubCarry ξ 0) r L := by
    exact_mod_cast hY_cleared
  have hcomb :
      (2 : ℤ) ^ L * (F * dubX ξ 0 (r + L) + v) =
        (3 : ℤ) ^ L * (F * dubX ξ 0 r + v) := by
    linear_combination F * hX + hY_int
  have hdvd_nat : 2 ^ L ∣ 3 ^ L * (F * dubX ξ 0 r + v).natAbs := by
    have habs :
        ((2 : ℤ) ^ L * (F * dubX ξ 0 (r + L) + v)).natAbs =
          ((3 : ℤ) ^ L * (F * dubX ξ 0 r + v)).natAbs := by
      rw [hcomb]
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at habs
    exact ⟨(F * dubX ξ 0 (r + L) + v).natAbs, habs.symm⟩
  have hcop : Nat.Coprime (2 ^ L) (3 ^ L) :=
    ((by decide : Nat.Coprime 2 3).pow_left L).pow_right L
  have hdvd_abs : 2 ^ L ∣ (F * dubX ξ 0 r + v).natAbs :=
    hcop.dvd_of_dvd_mul_left hdvd_nat
  simpa [Nat.cast_pow] using Int.ofNat_dvd_left.mpr hdvd_abs

/-- Exact integer-scaled step of the Cantor cylinder tree on $(2/7, 5/7)$ from depth $d$
(denominator $7 \cdot 2^d$) to depth $d + 1$ (denominator $7 \cdot 2^{d+1}$). -/
def cantorTwoSeventhsStep (d : ℕ) (ivs : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  let loBound : ℤ := 2 * (2 : ℤ) ^ (d + 1)
  let hiBound : ℤ := 5 * (2 : ℤ) ^ (d + 1)
  let shift1 : ℤ := 7 * (2 : ℤ) ^ d
  ivs.flatMap fun (x, y) =>
    let lo0 := if loBound ≤ 3 * x then 3 * x else loBound
    let hi0 := if 3 * y ≤ hiBound then 3 * y else hiBound
    let lo1 := if loBound ≤ 3 * x - shift1 then 3 * x - shift1 else loBound
    let hi1 := if 3 * y - shift1 ≤ hiBound then 3 * y - shift1 else hiBound
    (if lo0 < hi0 then [(lo0, hi0)] else []) ++
      (if lo1 < hi1 then [(lo1, hi1)] else [])

/-- Single-pass accumulator returning the list of surviving Cantor interval counts
`[|C_0|, |C_1|, ..., |C_n|]` on $(2/7, 5/7)$ without recomputing earlier depths. -/
def cantorTwoSeventhsLengthsAux : ℕ → ℕ → List (ℤ × ℤ) → List ℕ
  | 0, _, ivs => [ivs.length]
  | k + 1, d, ivs => ivs.length :: cantorTwoSeventhsLengthsAux k (d + 1) (cantorTwoSeventhsStep d ivs)

def cantorTwoSeventhsLengths (n : ℕ) : List ℕ :=
  cantorTwoSeventhsLengthsAux n 0 [(2, 5)]

/-- Structural step appending the next Mahler binary partition term
$B(n) = B(n - 1) + B(\lfloor n / 2 \rfloor)$ ($B(0) = 1, B(1) = 2$) to the prefix table `acc`. -/
def mahlerBinaryPartitionStep (acc : List ℕ) : List ℕ :=
  let n := acc.length
  let nextVal :=
    if n = 0 then 1
    else if n = 1 then 2
    else acc.getD (n - 1) 0 + acc.getD (n / 2) 0
  acc ++ [nextVal]

/-- Prefix table `[B(0), B(1), ..., B(n)]` of Mahler's binary partition sequence. -/
def mahlerBinaryPartitionList : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => mahlerBinaryPartitionStep (mahlerBinaryPartitionList k)

set_option maxRecDepth 400000 in
/-- **Exact Match Between the $(2/7, 5/7)$ Cantor Tree and Mahler's Binary Partition Sequence
through Depth $15$, and Truncation of the $k = 5$ Bifurcation at Depth $16$
(`cantorTwoSevenths_matches_mahlerBinaryPartition_up_to_15_and_splits_at_16`)**:
1. For every depth $d \in \{0, \dots, 15\}$, the number of surviving Cantor cylinder intervals
   of $(2/7, 5/7)$ equals Mahler's binary partition number $B(d)$:
   `[1, 2, 4, 6, 10, 14, 20, 26, 36, 46, 60, 74, 94, 114, 140, 166]`.
2. At depth $d = 2^4 = 16$ (where the period-32 Thue–Morse orbit $c_5 = \frac{12314908}{43112257} < \frac{2}{7}$
   falls outside $(2/7, 5/7)$), `mahlerBinaryPartitionList 16` reaches `202` whereas the $(2/7, 5/7)$
   Cantor tree has `200` intervals (exact deficit $2$ from the two mirror period-doubling
   branches clipped at $2/7$ and $5/7$). -/
theorem cantorTwoSevenths_matches_mahlerBinaryPartition_up_to_15_and_splits_at_16 :
    cantorTwoSeventhsLengths 15 = mahlerBinaryPartitionList 15 ∧
    cantorTwoSeventhsLengths 15 =
      [1, 2, 4, 6, 10, 14, 20, 26, 36, 46, 60, 74, 94, 114, 140, 166] ∧
    cantorTwoSeventhsLengths 16 =
      [1, 2, 4, 6, 10, 14, 20, 26, 36, 46, 60, 74, 94, 114, 140, 166, 200] ∧
    mahlerBinaryPartitionList 16 =
      [1, 2, 4, 6, 10, 14, 20, 26, 36, 46, 60, 74, 94, 114, 140, 166, 202] := by
  decide

/-! ## 11. The General Gap-$g$ Window-to-Residue Ladder ($g \ge 3$), $\alpha_g < \beta_g < 1/2$, and General $g$-Rung First-Defect Valuation Lock -/

/-- Lower endpoint $\alpha_g = \frac{3^{g-1}}{3^g - 2^g}$ of the gap-$g$ window ladder ($g \ge 3$),
equal to the real value of the periodic code $(1 0^{g-1})^\infty$. -/
noncomputable def rungAlpha (g : ℕ) : ℝ :=
  (3 : ℝ) ^ (g - 1) / ((3 : ℝ) ^ g - (2 : ℝ) ^ g)

/-- Upper endpoint $\beta_g = \frac{1 + (2/3)^{g-1}}{3} = \frac{3^{g-1} + 2^{g-1}}{3^g}$ of the
gap-$g$ window ladder ($g \ge 3$). -/
noncomputable def rungBeta (g : ℕ) : ℝ :=
  ((3 : ℝ) ^ (g - 1) + (2 : ℝ) ^ (g - 1)) / (3 : ℝ) ^ g

private theorem two_pow_lt_three_pow_pred {g : ℕ} (hg : 3 ≤ g) :
    2 ^ g < 3 ^ (g - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, g = d + 3 := ⟨g - 3, by omega⟩
  have hsub : d + 3 - 1 = d + 2 := by omega
  rw [hsub]
  induction d with
  | zero => decide
  | succ d ih =>
      have h2 : 2 ^ (d + 1 + 3) = 2 * 2 ^ (d + 3) := by rw [Nat.pow_succ']
      have h3 : 3 ^ (d + 1 + 2) = 3 * 3 ^ (d + 2) := by rw [Nat.pow_succ']
      omega

/-- **Strict Ordering of the Gap-$g$ Window Ladder (`rungAlpha_lt_rungBeta_lt_half`)**:
For every rung $g \ge 3$:
$$\frac{1}{3} < \alpha_g < \beta_g < \frac{1}{2}, \qquad \beta_g - \alpha_g = \frac{2^{g-1}(3^{g-1} - 2^g)}{3^g(3^g - 2^g)} > 0.$$ -/
theorem rungAlpha_lt_rungBeta_lt_half {g : ℕ} (hg : 3 ≤ g) :
    (1 / 3 : ℝ) < rungAlpha g ∧
    rungAlpha g < rungBeta g ∧
    rungBeta g < (1 / 2 : ℝ) ∧
    rungBeta g - rungAlpha g =
      (2 : ℝ) ^ (g - 1) * ((3 : ℝ) ^ (g - 1) - (2 : ℝ) ^ g) /
        ((3 : ℝ) ^ g * ((3 : ℝ) ^ g - (2 : ℝ) ^ g)) := by
  have hlt_nat := two_pow_lt_three_pow_pred hg
  have hlt_real : (2 : ℝ) ^ g < (3 : ℝ) ^ (g - 1) := by exact_mod_cast hlt_nat
  obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlt_real ⊢
  have h3g_eq : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := pow_succ' (3 : ℝ) m
  have h2g_eq : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := pow_succ' (2 : ℝ) m
  have h3g1_pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have h2g1_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h3g_pos : (0 : ℝ) < (3 : ℝ) ^ (m + 1) := by positivity
  have hdiff_pos : (0 : ℝ) < (3 : ℝ) ^ (m + 1) - (2 : ℝ) ^ (m + 1) := by linarith
  have hgap_eq :
      rungBeta (m + 1) - rungAlpha (m + 1) =
        (2 : ℝ) ^ m * ((3 : ℝ) ^ m - (2 : ℝ) ^ (m + 1)) /
          ((3 : ℝ) ^ (m + 1) * ((3 : ℝ) ^ (m + 1) - (2 : ℝ) ^ (m + 1))) := by
    unfold rungBeta rungAlpha
    simp only [Nat.add_sub_cancel]
    have h1 : (3 : ℝ) ^ (m + 1) ≠ 0 := ne_of_gt h3g_pos
    have h2 : (3 : ℝ) ^ (m + 1) - (2 : ℝ) ^ (m + 1) ≠ 0 := ne_of_gt hdiff_pos
    field_simp [h1, h2]
    rw [h3g_eq, h2g_eq]
    ring
  have hgap_pos : 0 < rungBeta (m + 1) - rungAlpha (m + 1) := by
    rw [hgap_eq]
    have hsub : 0 < (3 : ℝ) ^ m - (2 : ℝ) ^ (m + 1) := by linarith
    positivity
  have halpha_gt : (1 / 3 : ℝ) < rungAlpha (m + 1) := by
    unfold rungAlpha
    simp only [Nat.add_sub_cancel]
    rw [div_lt_div_iff₀ (by norm_num) hdiff_pos]
    linarith [h3g_eq, h2g1_pos, h2g_eq]
  have hbeta_lt : rungBeta (m + 1) < (1 / 2 : ℝ) := by
    unfold rungBeta
    simp only [Nat.add_sub_cancel]
    rw [div_lt_div_iff₀ h3g_pos (by norm_num)]
    linarith [h3g_eq, h2g_eq, hlt_real]
  exact ⟨halpha_gt, by linarith, hbeta_lt, hgap_eq⟩

/-- **Short-Gap Fractional Cost & Invariance of $[0, \alpha_g]$ (`gap_ladder_short_gap_cost_and_cap`)**:
For any rung $g \ge 3$:
1. **Short-gap cost ($\ge \beta_g$):** If $1 \le d \le g - 1$ and $r_{n+d} \ge 1/3$, then
   $\frac{1}{3} + (2/3)^d r_{n+d} \ge \beta_g$. Thus any odd step with another odd step at
   distance $d \le g - 1$ has fractional part $\ge \beta_g$.
2. **Long-gap cap ($\le \alpha_g$):** If $c \ge g$ and $0 \le r_{n+c} \le \alpha_g$, then
   $\frac{1}{3} + (2/3)^c r_{n+c} \le \alpha_g$ (with equality if and only if $c = g$ and $r_{n+c} = \alpha_g$). -/
theorem gap_ladder_short_gap_cost_and_cap {g : ℕ} (hg : 3 ≤ g) :
    (∀ {d : ℕ} {r_next : ℝ}, 1 ≤ d → d ≤ g - 1 → (1 / 3 : ℝ) ≤ r_next →
      rungBeta g ≤ (1 / 3 : ℝ) + (2 / 3 : ℝ) ^ d * r_next) ∧
    (∀ {c : ℕ} {r_next : ℝ}, g ≤ c → 0 ≤ r_next → r_next ≤ rungAlpha g →
      (1 / 3 : ℝ) + (2 / 3 : ℝ) ^ c * r_next ≤ rungAlpha g) := by
  have h23_le : ∀ {a b : ℕ}, a ≤ b → (2 / 3 : ℝ) ^ b ≤ (2 / 3 : ℝ) ^ a := by
    intro a b hab
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
  have hlt_real : (2 : ℝ) ^ g < (3 : ℝ) ^ (g - 1) := by
    exact_mod_cast two_pow_lt_three_pow_pred hg
  obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlt_real ⊢
  have h3g_eq : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := pow_succ' (3 : ℝ) m
  have hbeta_eq : rungBeta (m + 1) = (1 / 3 : ℝ) + (2 / 3 : ℝ) ^ m * (1 / 3 : ℝ) := by
    unfold rungBeta
    simp only [Nat.add_sub_cancel]
    have h3m_ne : (3 : ℝ) ^ m ≠ 0 := by positivity
    rw [h3g_eq, div_pow]
    apply mul_right_cancel₀ h3m_ne
    calc
      ((3 : ℝ) ^ m + (2 : ℝ) ^ m) / (3 * (3 : ℝ) ^ m) * (3 : ℝ) ^ m =
          (((3 : ℝ) ^ m + (2 : ℝ) ^ m) / 3) * ((3 : ℝ) ^ m / (3 : ℝ) ^ m) := by ring
      _ = ((3 : ℝ) ^ m + (2 : ℝ) ^ m) / 3 := by rw [div_self h3m_ne, mul_one]
      _ = (1 / 3 : ℝ) * (3 : ℝ) ^ m + ((2 : ℝ) ^ m / (3 : ℝ) ^ m * (3 : ℝ) ^ m) * (1 / 3 : ℝ) := by
        rw [div_mul_cancel₀ _ h3m_ne]
        ring
      _ = ((1 / 3 : ℝ) + (2 : ℝ) ^ m / (3 : ℝ) ^ m * (1 / 3 : ℝ)) * (3 : ℝ) ^ m := by ring
  have halpha_fixed : (1 / 3 : ℝ) + (2 / 3 : ℝ) ^ (m + 1) * rungAlpha (m + 1) = rungAlpha (m + 1) := by
    unfold rungAlpha
    simp only [Nat.add_sub_cancel]
    have h3g1_pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    have h3g_pos : (0 : ℝ) < (3 : ℝ) ^ (m + 1) := by positivity
    have hdiff_ne : (3 : ℝ) ^ (m + 1) - (2 : ℝ) ^ (m + 1) ≠ 0 := ne_of_gt (by linarith)
    have h3g_ne : (3 : ℝ) ^ (m + 1) ≠ 0 := ne_of_gt h3g_pos
    rw [div_pow]
    field_simp [hdiff_ne, h3g_ne]
    rw [h3g_eq]
    ring
  refine ⟨?_, ?_⟩
  · intro d r_next _ hd_hi hr_next
    have hpow := h23_le hd_hi
    have hmul1 : (2 / 3 : ℝ) ^ m * (1 / 3 : ℝ) ≤ (2 / 3 : ℝ) ^ d * (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    have hmul2 : (2 / 3 : ℝ) ^ d * (1 / 3 : ℝ) ≤ (2 / 3 : ℝ) ^ d * r_next :=
      mul_le_mul_of_nonneg_left hr_next (by positivity)
    linarith [hbeta_eq]
  · intro c r_next hgc hr0 hr_hi
    have hpow := h23_le hgc
    have halpha_pos : 0 ≤ rungAlpha (m + 1) :=
      le_of_lt (lt_trans (by norm_num) (rungAlpha_lt_rungBeta_lt_half hg).1)
    have hmul1 : (2 / 3 : ℝ) ^ c * r_next ≤ (2 / 3 : ℝ) ^ c * rungAlpha (m + 1) :=
      mul_le_mul_of_nonneg_left hr_hi (by positivity)
    have hmul2 : (2 / 3 : ℝ) ^ c * rungAlpha (m + 1) ≤ (2 / 3 : ℝ) ^ (m + 1) * rungAlpha (m + 1) :=
      mul_le_mul_of_nonneg_right hpow halpha_pos
    linarith [halpha_fixed]

/-- The general rung-$g$ affine invariant $I_g(b) = (3^g - 2^g) b + 3^{g-1}$ ($g \ge 1$).
At $g = 3$, $I_3(b) = 19 b + 9$; at $g = 4$, $I_4(b) = 65 b + 27$; at $g = 5$, $I_5(b) = 211 b + 81$. -/
def rungAffInv (g b : ℕ) : ℕ :=
  (3 ^ g - 2 ^ g) * b + 3 ^ (g - 1)

private theorem two_pow_le_three_pow (g : ℕ) : 2 ^ g ≤ 3 ^ g :=
  Nat.pow_le_pow_left (by decide) g

/-- **Universal Single-Block Identity for `rungAffInv g b` (`rungAffInv_single_block_identity`)**:
For any rung $g \ge 1$ and any block boundary $b$ with $3 b + 1 = 2^c u$:
$$3 \cdot \operatorname{rungAffInv}(g, b) = (3^g - 2^g) \cdot 2^c \cdot u + 2^g.$$ -/
theorem rungAffInv_single_block_identity {g b c u : ℕ} (hg : 1 ≤ g)
    (hdecomp : 3 * b + 1 = 2 ^ c * u) :
    3 * rungAffInv g b = (3 ^ g - 2 ^ g) * 2 ^ c * u + 2 ^ g := by
  have h3g_eq : 3 * 3 ^ (g - 1) = 3 ^ g := by
    have hg_eq : g = (g - 1) + 1 := by omega
    conv_rhs => rw [hg_eq, Nat.pow_succ']
  have hle := two_pow_le_three_pow g
  unfold rungAffInv
  zify [hle] at h3g_eq hdecomp ⊢
  linear_combination ((3 : ℤ) ^ g - (2 : ℤ) ^ g) * hdecomp + h3g_eq

/-- **Single-Defect Valuation $v_2(I_g(b)) = g$ for Any $c \ge g + 1$ (`rungAffInv_single_defect_valuation`)**:
Whenever $c \ge g + 1$ ($g \ge 1$) and $3 b + 1 = 2^c u$:
$$2^g \;\big|\; \operatorname{rungAffInv}(g, b) \quad \text{and} \quad 2^{g + 1} \;\nmid\; \operatorname{rungAffInv}(g, b).$$ -/
theorem rungAffInv_single_defect_valuation {g b c u : ℕ}
    (hg : 1 ≤ g) (hc : g + 1 ≤ c) (hdecomp : 3 * b + 1 = 2 ^ c * u) :
    2 ^ g ∣ rungAffInv g b ∧ ¬ (2 ^ (g + 1) ∣ rungAffInv g b) := by
  have hid := rungAffInv_single_block_identity hg hdecomp
  have hpow : 2 ^ c = 2 ^ g * (2 * 2 ^ (c - (g + 1))) := by
    have hc_eq : c = g + (1 + (c - (g + 1))) := by omega
    calc
      2 ^ c = 2 ^ (g + (1 + (c - (g + 1)))) := by rw [← hc_eq]
      _ = 2 ^ g * 2 ^ (1 + (c - (g + 1))) := Nat.pow_add 2 g _
      _ = 2 ^ g * (2 * 2 ^ (c - (g + 1))) := by rw [Nat.pow_add 2 1, pow_one]
  set k := (3 ^ g - 2 ^ g) * 2 ^ (c - (g + 1)) * u
  have hid_k : 3 * rungAffInv g b = 2 ^ g * (2 * k + 1) := by
    calc
      3 * rungAffInv g b = (3 ^ g - 2 ^ g) * 2 ^ c * u + 2 ^ g := hid
      _ = (3 ^ g - 2 ^ g) * (2 ^ g * (2 * 2 ^ (c - (g + 1)))) * u + 2 ^ g := by rw [hpow]
      _ = 2 ^ g * (2 * k + 1) := by unfold k; ring
  have hdvd_3 : 2 ^ g ∣ 3 * rungAffInv g b := ⟨2 * k + 1, hid_k⟩
  have hcop : Nat.Coprime (2 ^ g) 3 := (by decide : Nat.Coprime 2 3).pow_left g
  have hdvd : 2 ^ g ∣ rungAffInv g b := hcop.dvd_of_dvd_mul_left hdvd_3
  refine ⟨hdvd, ?_⟩
  rintro ⟨q, hq⟩
  have hpow_g1 : 2 ^ (g + 1) = 2 ^ g * 2 := by rw [Nat.pow_succ]
  rw [hq, hpow_g1] at hid_k
  have hmul_eq : 2 ^ g * (3 * (2 * q)) = 2 ^ g * (2 * k + 1) := by linarith
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul_eq
  omega

/-- **Multi-Step Pure Rung-$g$ Transition Identity (`rungAffInv_pure_prefix_identity`)**:
Along any `ValidBlockChain a_0 s u K` whose first $m \le K$ blocks all have length $s(k) = g$ ($g \ge 1$):
$$2^{g m} \cdot \operatorname{rungAffInv}\big(g,\, \operatorname{orbit}(a_0, \operatorname{blockSteps}(s, m))\big) = 3^{g m} \cdot \operatorname{rungAffInv}(g, a_0).$$ -/
theorem rungAffInv_pure_prefix_identity {g a_0 K m : ℕ} {s u : ℕ → ℕ}
    (hg : 1 ≤ g) (hmK : m ≤ K) (hchain : ValidBlockChain a_0 s u K)
    (hpure : ∀ k < m, s k = g) :
    (2 ^ g) ^ m * rungAffInv g (orbit a_0 (blockSteps s m)) =
      (3 ^ g) ^ m * rungAffInv g a_0 := by
  induction m with
  | zero => simp [blockSteps, orbit]
  | succ m ih =>
      have ihm := ih (by omega) (fun k hk => hpure k (by omega))
      have hsm : s m = g := hpure m (Nat.lt_succ_self m)
      rcases hchain m (by omega) with ⟨hsk_pos, _, hdecomp⟩
      have horb_next : orbit a_0 (blockSteps s (m + 1)) = 3 ^ (g - 1) * u m := by
        have hsteps : blockSteps s (m + 1) = blockSteps s m + s m := rfl
        rw [hsteps, orbit_add, ← hsm]
        exact orbit_odd_block_return hsk_pos hdecomp
      rw [hsm] at hdecomp
      have hid_m := rungAffInv_single_block_identity hg hdecomp
      have hstep : 2 ^ g * rungAffInv g (orbit a_0 (blockSteps s (m + 1))) =
          3 ^ g * rungAffInv g (orbit a_0 (blockSteps s m)) := by
        have h3g_eq : 3 ^ g = 3 * 3 ^ (g - 1) := by
          have hg_eq : g = (g - 1) + 1 := by omega
          conv_lhs => rw [hg_eq, Nat.pow_succ']
        calc
          2 ^ g * rungAffInv g (orbit a_0 (blockSteps s (m + 1))) =
              2 ^ g * ((3 ^ g - 2 ^ g) * (3 ^ (g - 1) * u m) + 3 ^ (g - 1)) := by
            rw [horb_next]; rfl
          _ = 3 ^ (g - 1) * ((3 ^ g - 2 ^ g) * 2 ^ g * u m + 2 ^ g) := by ring
          _ = 3 ^ (g - 1) * (3 * rungAffInv g (orbit a_0 (blockSteps s m))) := by rw [← hid_m]
          _ = (3 * 3 ^ (g - 1)) * rungAffInv g (orbit a_0 (blockSteps s m)) := by ring
          _ = 3 ^ g * rungAffInv g (orbit a_0 (blockSteps s m)) := by rw [← h3g_eq]
      calc
        (2 ^ g) ^ (m + 1) * rungAffInv g (orbit a_0 (blockSteps s (m + 1))) =
            (2 ^ g) ^ m * (2 ^ g * rungAffInv g (orbit a_0 (blockSteps s (m + 1)))) := by
          rw [Nat.pow_succ]
          ring
        _ = (2 ^ g) ^ m * (3 ^ g * rungAffInv g (orbit a_0 (blockSteps s m))) := by
          rw [hstep]
        _ = 3 ^ g * ((2 ^ g) ^ m * rungAffInv g (orbit a_0 (blockSteps s m))) := by
          ring
        _ = 3 ^ g * ((3 ^ g) ^ m * rungAffInv g a_0) := by
          rw [ihm]
        _ = (3 ^ g) ^ (m + 1) * rungAffInv g a_0 := by
          rw [Nat.pow_succ]
          ring

/-- **General $g$-Rung First-Defect Valuation Lock (`general_rung_first_defect_valuation_lock`)**:
Generalizes `local_prefix_first_defect_valuation_lock` ($g = 3, I_3(a_0) = 19 a_0 + 9$) to **every**
rung $g \ge 1$ ($I_g(a_0) = (3^g - 2^g) a_0 + 3^{g-1}$):
Whenever `ValidBlockChain a_0 s u (j_0 + 1)` has $s(0) = \dots = s(j_0 - 1) = g$ and a first
defect $s(j_0) \ge g + 1$ at block $j_0$:
1. $2^{g(j_0 + 1)} \;\big|\; \big((3^g - 2^g) a_0 + 3^{g-1}\big)$,
2. $2^{g(j_0 + 1) + 1} \;\nmid\; \big((3^g - 2^g) a_0 + 3^{g-1}\big)$, and
3. $2^{g(j_0 + 1)} \le (3^g - 2^g) a_0 + 3^{g-1}$. -/
theorem general_rung_first_defect_valuation_lock
    {g a_0 j_0 : ℕ} {s u : ℕ → ℕ}
    (hg : 1 ≤ g)
    (hchain : ValidBlockChain a_0 s u (j_0 + 1))
    (hpure : ∀ k < j_0, s k = g)
    (hdefect : g + 1 ≤ s j_0) :
    2 ^ (g * (j_0 + 1)) ∣ rungAffInv g a_0 ∧
    ¬ (2 ^ (g * (j_0 + 1) + 1) ∣ rungAffInv g a_0) ∧
    2 ^ (g * (j_0 + 1)) ≤ rungAffInv g a_0 := by
  have hpre := rungAffInv_pure_prefix_identity hg (Nat.le_succ j_0) hchain hpure
  rcases hchain j_0 (Nat.lt_succ_self j_0) with ⟨_, _, hdecomp_j0⟩
  have hval_j0 := rungAffInv_single_defect_valuation hg hdefect hdecomp_j0
  rcases hval_j0.1 with ⟨q0, hq0⟩
  have hpow_mul : (2 ^ g) ^ j_0 * 2 ^ g = 2 ^ (g * (j_0 + 1)) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_add, Nat.mul_one]
  have hpre_q0 : 2 ^ (g * (j_0 + 1)) * q0 = (3 ^ g) ^ j_0 * rungAffInv g a_0 := by
    calc
      2 ^ (g * (j_0 + 1)) * q0 = (2 ^ g) ^ j_0 * (2 ^ g * q0) := by
        rw [← hpow_mul]
        ring
      _ = (2 ^ g) ^ j_0 * rungAffInv g (orbit a_0 (blockSteps s j_0)) := by rw [← hq0]
      _ = (3 ^ g) ^ j_0 * rungAffInv g a_0 := hpre
  have hdvd_mul : 2 ^ (g * (j_0 + 1)) ∣ (3 ^ g) ^ j_0 * rungAffInv g a_0 :=
    ⟨q0, hpre_q0.symm⟩
  have hcop : Nat.Coprime (2 ^ (g * (j_0 + 1))) ((3 ^ g) ^ j_0) :=
    (((by decide : Nat.Coprime 2 3).pow_left (g * (j_0 + 1))).pow_right g).pow_right j_0
  have hdvd : 2 ^ (g * (j_0 + 1)) ∣ rungAffInv g a_0 :=
    hcop.dvd_of_dvd_mul_left hdvd_mul
  have hnot_dvd : ¬ (2 ^ (g * (j_0 + 1) + 1) ∣ rungAffInv g a_0) := by
    rintro ⟨q1, hq1⟩
    have hpow_succ : 2 ^ (g * (j_0 + 1) + 1) = (2 ^ g) ^ j_0 * 2 ^ (g + 1) := by
      rw [← Nat.pow_mul, ← Nat.pow_add]
      have h : g * (j_0 + 1) + 1 = g * j_0 + (g + 1) := by ring
      rw [h]
    rw [hq1, hpow_succ] at hpre
    have hmul_eq :
        (2 ^ g) ^ j_0 * rungAffInv g (orbit a_0 (blockSteps s j_0)) =
          (2 ^ g) ^ j_0 * (2 ^ (g + 1) * ((3 ^ g) ^ j_0 * q1)) := by
      linarith
    have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pow_pos (by decide))) hmul_eq
    exact hval_j0.2 ⟨(3 ^ g) ^ j_0 * q1, hcancel⟩
  have hpos_inv : 0 < rungAffInv g a_0 := by
    unfold rungAffInv
    have h : 0 < 3 ^ (g - 1) := Nat.pow_pos (by decide)
    omega
  exact ⟨hdvd, hnot_dvd, Nat.le_of_dvd hpos_inv hdvd⟩

end Mahler.DubickasExtension
