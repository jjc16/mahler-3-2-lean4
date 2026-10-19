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

end Mahler.DubickasExtension
