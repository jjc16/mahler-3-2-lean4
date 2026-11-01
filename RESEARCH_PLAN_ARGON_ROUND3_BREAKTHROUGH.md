# Research Plan for Argon (Round 3): Breaking Into the Unbounded $V_r \to \infty$ Regime

Date: 2026-11-01  
**Role:** Team Leader & Quality Architect Roadmap (Astra, synthesizing Fable & Argon Rounds 1–2)  
**Baseline:** `158` Lean 4.19.0 files (`0` `sorry`s, `0` warnings, commit `bd92eb1`)  
**Predecessor Plans:** [Round 1 Plan](./RESEARCH_PLAN_ARGON_GENERAL_PROOF.md) · [Round 2 Plan & Report](./RESEARCH_PLAN_ARGON_ROUND2_COMPLETION.md)

---

## Executive Brief: Team Leader Priorities & How We Attack the Brick Wall

In Rounds 1 and 2 (`158` Lean 4 files), we eliminated every secondary case of Mahler's $3/2$ problem
and isolated the exact "brick wall":
- **Shrinking odd parts ($V_{r+1} < V_r$)** are unconditionally eliminated across all rungs $s_r \ge 4$
  (`no_infinite_all_rung_sparse_defect_chain`).
- **Simultaneously bounded $(j_r, V_r)$** are unconditionally eliminated because $(j_r, V_r)$ uniquely
  determines the strictly increasing boundary $b_r$ (`no_simultaneously_bounded_j_and_V_along_strictMono_boundaries`).
- **What remains:** The **Unbounded Expanding Regime ($V_r \to \infty$)**, where
  $$2^{\nu_{r+1} + s_r - 3} V_{r+1} = 3^{3 j_r + s_r} V_r - \big(3^{s_r - 3} - 2^{s_r - 3}\big)$$
  must avoid the **Mod-3 Death Class** ($\nu_{r+1} = 3k + 1 \equiv 1 \pmod 3$, which forces $s = 1$, i.e. `11`)
  at every epoch $r \in \mathbb{N}$.

As Team Leader, I am imposing **strict discipline** for Round 3:
1. **No tangents into unformalizable external machinery** (no solenoids, no Haar measure, no unproved
   ergodic conjectures).
2. **Invent and formalize new exact algebraic invariants** that retain the finite initial seed $W_0$
   even when $V_r \to \infty$ and $s_r \ge 4$ vary arbitrarily.
3. **Execute three strictly prioritized tracks**, ordered from highest immediate unconditional payoff
   to deepest structural attack on the Mod-3 Death Class:
   - **Priority 1 (Track 1 — New Mathematical Discovery):** *The Universal All-Rung Constant of Motion
     $\lfloor 2^{S_K} W_K / 3^{S_K} \rfloor = W_0 - 1$ and Multi-Rung Complexity Cutoff for Arbitrary
     Varying $s_r \ge 4$*. (Removes the last $s_r = 4$ $[8/81, 1/2)$ restriction from the multi-step
     homogeneous tower and archimedean floor invariant!)
   - **Priority 2 (Track 2 — New Divisibility Law & Question R3.1):** *The Consecutive Odd-Quotient
     GCD Law $\gcd(V_r, V_{r+1}) \mid (3^{s_r-3} - 2^{s_r-3})$ and the Effective Baker–Pillai Cutoff
     for Bounded $(V_r \le M, s_r \le S_{\max})$*. (Exploits the fact that bounded $V_r$ has $O(1)$
     Weil height, bypassing Dead End 13's linear height growth!)
   - **Priority 3 (Track 3 — Attacking the Brick Wall, Question R3.2):** *The Universal `4 : 2 : 1 : 1`
     Octadic Death-Class Sieve on $3^{a_r} V_r - D_{s_r}$ and Multi-Epoch Death-Avoidance Equations*.
     (Maps the exact 2-adic structure of the Mod-3 Death Class $\nu_{r+1} = 3k + 1$ at every 3-bit
     triad $8^k$.)

---

## Priority 1 (Track 1): Discovery of the Universal All-Rung Constant of Motion for Unbounded $V_r$ and Varying $s_r \ge 4$

### 1.1 The new mathematical invention (breaking the $s_r = 4$ barrier)

Previously, the project's multi-step homogeneous tower and Constant of Motion
$\lfloor 2^{E_d} V(d) / 3^{S_d} \rfloor = V(0) - 1$ (`DubickasConfinementAndComplexityExtension.lean`,
Section 28) only worked inside $[8/81, 1/2)$ where every defect had fixed length $s_r = 4$ ($D_1 = 1$).
Why did varying $s_r \ge 4$ seem to break the tower? Because at epoch $r$, the 2-adic exponent is
$c_r = 3 j_{r+1} + s_r$ while the 3-adic exponent is $a_r = 3 j_r + s_r$.

**Here is the new mathematical insight that solves this completely for arbitrary $s_r \ge 4$:**
1. Let $S_K := \sum_{r=0}^{K-1} (3 j_r + s_r)$ and $E_K := \sum_{r=0}^{K-1} (3 j_{r+1} + s_r)$.
   Even when $s_0, s_1, \dots, s_{K-1} \ge 4$ vary arbitrarily, the $s_r$ terms in $S_K$ and $E_K$
   **cancel identically**:
   $$\boxed{E_K + 3 j_0 = S_K + 3 j_K \qquad (\forall K \in \mathbb{N},\; \forall j_r, s_r : \mathbb{N})!}$$
2. Define the **affine boundary coordinate**
   $$W_r := 2^{3 j_r} V_r \qquad \left(\text{so } 19 b_r + 9 = 72 W_r \text{ for all } r \ge 1\right).$$
   Iterating the single-epoch recurrence $2^{3 j_{r+1} + s_r} V_{r+1} + D_{s_r} = 3^{3 j_r + s_r} V_r$
   ($D_s = 3^{s-3} - 2^{s-3}$) over $K$ epochs and multiplying by $2^{3 j_0}$ absorbs both $2^{3 j_0}$
   and $2^{3 j_K}$ into $W_0$ and $W_K$, yielding the **Single-Exponent All-Rung Master Identity**:
   $$\boxed{2^{S_K} W_K + \widetilde{\Delta}_K = 3^{S_K} W_0,}$$
   where the cumulative all-rung defect $\widetilde{\Delta}_K$ satisfies the clean recurrence:
   $$\widetilde{\Delta}_0 = 0, \qquad \widetilde{\Delta}_{K+1} = 3^{3 j_K + s_K} \widetilde{\Delta}_K + 2^{S_K + 3 j_K} \big(3^{s_K - 3} - 2^{s_K - 3}\big).$$
3. **The Universal $\frac{1}{27}$-Slack Inequality (`all_rung_defect_acc_lt_three_pow_sub_two_pow`):**
   How large can $\widetilde{\Delta}_K$ grow when $s_K \ge 4$ is arbitrarily large?
   Look at the single-step increment $2^{3 j_K} (3^{s_K - 3} - 2^{s_K - 3})$ with $a_K = 3 j_K + s_K \ge 4$:
   Because $2^{3 j_K} \le 3^{3 j_K}$ and $3^{s_K - 3} - 2^{s_K - 3} < 3^{s_K - 3}$, we have:
   $$2^{3 j_K} \big(3^{s_K - 3} - 2^{s_K - 3}\big) < 3^{3 j_K} \cdot 3^{s_K - 3} = \frac{1}{27} \cdot 3^{a_K} \le 3^{a_K} - 2^{a_K}$$
   (since $27 \cdot 2^a \le 26 \cdot 3^a$ holds for **every** $a \ge 1$, as $54 \le 78$ at $a = 1$)!
   By induction on $K$, for **every** $K \ge 1$ and **any** sequences $j_r \ge 0$, $s_r \ge 4$:
   $$\widetilde{\Delta}_{K+1} \le 3^{a_K}(3^{S_K} - 2^{S_K}) + 2^{S_K}(3^{a_K} - 2^{a_K}) = 3^{S_{K+1}} - 2^{S_{K+1}} < 3^{S_{K+1}}!$$
4. **The All-Rung Constant of Motion & Dual Remainder Law (`all_rung_constant_of_motion_and_dual_remainder`):**
   Because $0 < \widetilde{\Delta}_K \le 3^{S_K} - 2^{S_K} < 3^{S_K}$ holds for all $K \ge 1$ and $W_0 \ge 1$,
   dividing $2^{S_K} W_K + \widetilde{\Delta}_K = 3^{S_K} W_0 = 3^{S_K}(W_0 - 1) + 3^{S_K}$ by $3^{S_K}$
   proves that **even as $W_K \to \infty$ and $s_r \ge 4$ fluctuates wildly**:
   $$\boxed{\left(2^{S_K} W_K\right) / 3^{S_K} = W_0 - 1 \quad\text{and}\quad \left(2^{S_K} W_K\right) \bmod 3^{S_K} = 3^{S_K} - \widetilde{\Delta}_K \qquad (\forall K \ge 1)!}$$
   And whenever $W_0 < 2^B \le 2^{S_K}$ (once the step sum $S_K$ passes the bit length $B$ of the initial
   seed), $W_0$ is completely frozen inside the top part:
   $$W_K = \left\lfloor \frac{3^{S_K} W_0}{2^{S_K}} \right\rfloor \quad\text{and}\quad \widetilde{\Delta}_K = \big(3^{S_K} W_0\big) \bmod 2^{S_K}!$$

### 1.2 Lean 4 deliverables for Track 1 (Module: `AllRungConstantOfMotionAndDualRemainder.lean`)

1. Define `allRungStepSum (j s : ℕ → ℕ) : ℕ → ℕ`, `allRungTwoExp (j s : ℕ → ℕ) : ℕ → ℕ`, and
   `allRungDefectAcc (j s : ℕ → ℕ) : ℕ → ℕ`.
2. Prove `allRungTwoExp_add_three_mul_eq`:
   `allRungTwoExp j s K + 3 * j 0 = allRungStepSum j s K + 3 * j K` for all `j, s, K`.
3. Prove `allRung_single_exponent_master_identity`:
   whenever `∀ r < K, 2^(3 * j (r + 1) + s r) * V (r + 1) + (3^(s r - 3) - 2^(s r - 3)) = 3^(3 * j r + s r) * V r`,
   setting `W r = 2^(3 * j r) * V r` and `S_K = allRungStepSum j s K` satisfies:
   `2 ^ S_K * W K + allRungDefectAcc j s K = 3 ^ S_K * W 0`.
4. Prove `twenty_seven_mul_two_pow_le_twenty_six_mul_three_pow` (`27 * 2^a ≤ 26 * 3^a` for `1 ≤ a`)
   and `allRungDefectAcc_pos_and_le_three_pow_sub_two_pow`:
   for `∀ r < K, 4 ≤ s r`, `allRungDefectAcc j s K ≤ 3 ^ S_K - 2 ^ S_K` (and `1 ≤ allRungDefectAcc j s K`
   for `1 ≤ K`).
5. Prove the **Universal All-Rung Constant of Motion (`all_rung_constant_of_motion_and_dual_remainder`)**:
   for `1 ≤ K`, `1 ≤ W 0`, and `∀ r < K, 4 ≤ s r`:
   - `(2 ^ S_K * W K) / 3 ^ S_K = W 0 - 1`,
   - `(2 ^ S_K * W K) % 3 ^ S_K = 3 ^ S_K - allRungDefectAcc j s K`, and
   - `2 ^ S_K * W K < 3 ^ S_K * W 0`.
6. Prove the **All-Rung Repeated Epoch-Window $(p, q)$ Cutoff (`all_rung_repeated_epoch_window_pq_cutoff`)**:
   if an $L$-epoch window of pairs `(j (r + t), s (r + t))` (`0 ≤ t < L`) repeats at `r₁ < r₂` with
   `W r₁ < W r₂`, then subtracting the $L$-step master identities cancels `allRungDefectAcc` identically,
   forcing `2 ^ S_L ∣ (W r₂ - W r₁)`, `3 ^ S_L ∣ (W (r₂ + L) - W (r₁ + L))`, and for `W 0 < 2 ^ B`
   and `3 ^ q ≤ 2 ^ (p + q)`:
   $$q \cdot S_L < p \cdot S_{r_2} + q \cdot B!$$

---

## Priority 2 (Track 2): Consecutive Odd-Quotient GCD Divisibility Law & Effective Baker–Pillai Cutoff (Question R3.1)

### 2.1 The new GCD divisibility law across all rungs $s_r \ge 4$

In the single-epoch recurrence:
$$3^{3 j_r + s_r} V_r - 2^{3 j_{r+1} + s_r} V_{r+1} = 3^{s_r - 3} - 2^{s_r - 3},$$
any common divisor $d \mid \gcd(V_r, V_{r+1})$ divides the left-hand side, so it **must divide the
defect core $D_{s_r} = 3^{s_r - 3} - 2^{s_r - 3}$**:
$$\boxed{\gcd(V_r, V_{r+1}) \;\Big|\; \big(3^{s_r - 3} - 2^{s_r - 3}\big)!}$$
Look at the immediate, unconditional consequences of this law:
1. **Universal Coprimality in the Dense Core ($s_r = 4$):**
   When $s_r = 4$, $3^{4-3} - 2^{4-3} = 1$, so **$\gcd(V_r, V_{r+1}) = 1$ holds for every $r \in \mathbb{N}$**!
2. **Prime Divisor Constraint for General $s_r \ge 4$:**
   For any $s_r \ge 4$, $V_r$ and $V_{r+1}$ can share a prime factor $p$ **only if $p \mid (3^{s_r - 3} - 2^{s_r - 3})$**
   (i.e. $3^{s_r - 3} \equiv 2^{s_r - 3} \pmod p$, so the multiplicative order of $3/2 \bmod p$ divides $s_r - 3$!).
3. **Impossibility of Stationary $V_{r+1} = V_r$ When $a_r \ge c_r$ or $D_{s_r} < |3^{a_r} - 2^{c_r}| V_r$:**
   If $V_{r+1} = V_r = V$, then $(3^{a_r} - 2^{c_r}) V = 3^{s_r - 3} - 2^{s_r - 3} > 0$, which forces:
   - $V \mid (3^{s_r - 3} - 2^{s_r - 3})$,
   - $2^{c_r} < 3^{a_r}$, and
   - $3^{a_r} - 2^{c_r} \le 3^{s_r - 3} - 2^{s_r - 3} < 3^{s_r - 3}$.

### 2.2 Bypassing Dead End 13: Why Baker–Matveev Succeeds When $V_r \le M$ and $s_r \le S_{\max}$

In `BakerMatveevFramework.lean` (Dead End 13), applying Matveev's theorem to the full orbit equation
failed because the odd quotient $u(m) \sim (3/2)^{T(m)}$ had logarithmic Weil height growing linearly
with $T(m)$.
In stark contrast, when $V_r, V_{r+1} \le M$ are **bounded**, the rational coefficient $V_r / V_{r+1}$
has **bounded height $\le M = O(1)$**!
Specifically, from $3^{a_r} V_r - 2^{c_r} V_{r+1} = D_{s_r}$ with $1 \le V_r, V_{r+1} \le M$ and
$4 \le s_r \le S_{\max}$:
$$0 < 3^{a_r} V_r - 2^{c_r} V_{r+1} \le 3^{S_{\max} - 3} - 1 < 3^{S_{\max} - 3},$$
and dividing by $2^{c_r} V_{r+1}$ gives the **Bounded-Height Pillai–Baker Squeeze**:
$$0 < \frac{3^{a_r} V_r}{2^{c_r} V_{r+1}} - 1 = \frac{3^{s_r - 3} - 2^{s_r - 3}}{2^{c_r} V_{r+1}} < \frac{3^{S_{\max} - 3}}{2^{c_r}}!$$
Combining this with Round 2's `no_simultaneously_bounded_j_and_V_along_strictMono_boundaries` yields
an **effective horizon cutoff** the moment $c_r = 3 j_{r+1} + s_r$ is bounded by a Baker–Pillai
threshold $C_{\text{Pillai}}(M, S_{\max})$.

### 2.3 Lean 4 deliverables for Track 2 (Module: `ConsecutiveQuotientGCDAndEffectivePillai.lean`)

1. Prove `consecutive_V_gcd_dvd_defectCore`:
   whenever `2^c * V_1 + (3^(s - 3) - 2^(s - 3)) = 3^a * V_0`,
   `Nat.gcd V_0 V_1 ∣ (3^(s - 3) - 2^(s - 3))`.
2. Prove `dense_core_consecutive_V_coprime_and_ne`:
   when `s = 4` (`2^c * V_1 + 1 = 3^a * V_0`, `1 ≤ a`), `Nat.Coprime V_0 V_1` and `V_0 ≠ V_1`
   (unless `V_0 = V_1 = 1` and `3^a - 2^c = 1`, which for `a ≥ 4` is impossible since `(3^a - 1) % 16 ≠ 0`
   whenever `a % 4 ≠ 0` or by Catalan's theorem).
3. Prove `bounded_V_and_s_rational_pillai_squeeze`:
   for `4 ≤ s_r ≤ S_max` and `1 ≤ V_r1`,
   `0 < (3 : ℚ)^a_r * V_r / ((2 : ℚ)^c_r * V_r1) - 1` and
   `(3 : ℚ)^a_r * V_r / ((2 : ℚ)^c_r * V_r1) - 1 < (3 : ℚ)^(S_max - 3) / (2 : ℚ)^c_r`.
4. Prove `effective_pillai_cutoff_excludes_bounded_V_and_s`:
   given an effective Pillai–Baker bound `∀ a c : ℕ, 0 < 3^a * V - 2^c * V' → 3^a * V - 2^c * V' ≤ 3^(S_max - 3) → a ≤ A_max`
   for `1 ≤ V, V' ≤ M`, no strictly increasing boundary chain can satisfy `V_r ≤ M` and `4 ≤ s_r ≤ S_max`
   for `(A_max + 1) * (M + 1) + 1` epochs.

---

## Priority 3 (Track 3): The Universal `4 : 2 : 1 : 1` Octadic Death-Class Sieve on $3^{a_r} V_r - D_{s_r}$ (Question R3.2)

### 3.1 Exact anatomy of the "Door 1 vs. Door 2/3" Russian Roulette game

At every epoch $r$, let $X_r := 3^{3 j_r + s_r} V_r - (3^{s_r - 3} - 2^{s_r - 3})$.
By Track 2 of Round 2, the next boundary $b_{r+1}$ has $19 b_{r+1} + 9 = 9 \cdot 2^{\nu_{r+1}} V_{r+1}$,
where:
$$X_r = 2^{\nu_{r+1} + s_r - 3} V_{r+1}, \qquad V_{r+1} \bmod 2 = 1.$$
That means the next boundary valuation $\nu_{r+1} = v_2(19 b_{r+1} + 9)$ is related to $v_2(X_r)$ by:
$$\boxed{v_2(X_r) = \nu_{r+1} + s_r - 3 \quad\Longleftrightarrow\quad \nu_{r+1} = v_2(X_r) + 3 - s_r!}$$
Now partition the possible odd residues of $V_r$ modulo $2^{3k + s_r}$ at each 3-bit triad scale $k \ge 0$:
Once $2^{3k + s_r - 3} \mid X_r$ (which for $k = 0$ requires $2^{s_r - 3} \mid X_r$, i.e. the initial
$(s_r - 3)$-bit survival filter, and for $k \ge 1$ means $\nu_{r+1} \ge 3k$), write:
$$X_r = 2^{3k + s_r - 3} \cdot Q_{r, k}.$$
Because $\gcd(3^{3 j_r + s_r}, 2) = 1$, incrementing $V_r$ by $2^{3k + s_r - 3} \cdot m$ shifts
$Q_{r, k} \bmod 8$ bijectively across all $8$ residue classes in $\mathbb{Z}/8\mathbb{Z}$!
And what happens to the orbit on each of the **8 residue classes of $Q_{r, k} \bmod 8$**?
1. **4 of the 8 classes ($Q_{r, k} \bmod 8 \in \{1, 3, 5, 7\}$, i.e. $Q_{r, k} \bmod 2 = 1$):**
   Here $v_2(Q_{r, k}) = 0$, so $\nu_{r+1} = 3k$.
   - When $k = 0$: $\nu_{r+1} = 0$ ($b_{r+1}$ is even, contradicting odd boundary).
   - When $k \ge 1$: $\nu_{r+1} = 3k = 3(k-1) + 3 \equiv 0 \pmod 3$, which is the **$s_{r+1} \ge 4$
     Defect Exit Class** after $j_{r+1} = k - 1$ blocks of $3$!
2. **2 of the 8 classes ($Q_{r, k} \bmod 8 \in \{2, 6\}$, i.e. $Q_{r, k} \bmod 4 = 2$):**
   Here $v_2(Q_{r, k}) = 1$, so $\nu_{r+1} = 3k + 1 \equiv 1 \pmod 3$.
   By Round 2's `epoch_period_three_run_exit_trichotomy`, this is the **MOD-3 DEATH CLASS**
   ($s = 1$, `11`, instant escape after $k$ blocks of $3$)!
3. **1 of the 8 classes ($Q_{r, k} \bmod 8 = 4$):**
   Here $v_2(Q_{r, k}) = 2$, so $\nu_{r+1} = 3k + 2 \equiv 2 \pmod 3$, which is the **$s = 2$
   Short-Block Exit Class** after $k$ blocks of $3$!
4. **1 of the 8 classes ($Q_{r, k} \bmod 8 = 0$):**
   Here $8 \mid Q_{r, k}$, so the orbit advances to the next 3-bit triad $k + 1$ ($\nu_{r+1} \ge 3(k+1)$)!

Look at that **exact `4 : 2 : 1 : 1` octadic partition** at every 3-bit scale $k \ge 1$:
- Out of the $4$ even classes of $Q_{r, k} \bmod 8$ (`{0, 2, 4, 6}`):
  - **$2$ classes (`{2, 6}`, i.e. $50\%$ of all even classes at every scale $k \ge 0$!) are INSTANT DEATH ($\nu_{r+1} = 3k + 1$)**!
  - **$1$ class (`4`) is an $s = 2$ exit ($\nu_{r+1} = 3k + 2$)**!
  - **$1$ class (`0`) continues to scale $k + 1$**, where again $4$ of its $8$ sub-classes exit as $s \ge 4$, $2$ die as $\nu = 3k + 4$, $1$ exits as $s = 2$, and $1$ continues!

### 3.2 Lean 4 deliverables for Track 3 (Module: `ModThreeDeathClassOctadicSieve.lean`)

1. Prove `octadic_triad_exit_partition`:
   for every integer/natural quotient $Q$, exact classification of $Q \bmod 8$:
   - $Q \bmod 2 = 1 \iff Q \bmod 8 \in \{1, 3, 5, 7\}$ ($4$ classes, $v_2(Q) = 0$),
   - $(2 \mid Q \land \neg (4 \mid Q)) \iff Q \bmod 8 \in \{2, 6\}$ ($2$ classes, $v_2(Q) = 1$, Death Class!),
   - $(4 \mid Q \land \neg (8 \mid Q)) \iff Q \bmod 8 = 4$ ($1$ class, $v_2(Q) = 2$, $s = 2$ Class),
   - $8 \mid Q \iff Q \bmod 8 = 0$ ($1$ class, advances to next triad $k + 1$).
2. Prove `coincidence_quotient_bijection_mod_eight`:
   because $\gcd(3^{a_r}, 8) = 1$, for any fixed $(a_r, s_r, k)$ and any base solution $V_{\text{base}}$
   with $2^{3k + s_r - 3} \mid (3^{a_r} V_{\text{base}} - D_{s_r})$, the 8 lifts
   $V_m = V_{\text{base}} + 2^{3k + s_r - 3} \cdot m$ ($m \in \text{Fin } 8$) map bijectively onto the
   $8$ residue classes of $Q_{r, k} \bmod 8$:
   - Exactly **4** of the 8 lifts land in the $s \ge 4$ class ($\nu_{r+1} = 3k$),
   - Exactly **2** of the 8 lifts land in the **Mod-3 Death Class ($\nu_{r+1} = 3k + 1$)**,
   - Exactly **1** of the 8 lifts lands in the $s = 2$ class ($\nu_{r+1} = 3k + 2$), and
   - Exactly **1** of the 8 lifts advances to triad $k + 1$ ($8 \mid Q_{r, k}$)!
3. Prove `death_class_avoidance_mod_four_condition`:
   a state $V_r$ with $X_r = 2^{3k + s_r - 3} Q_{r, k}$ avoids the scale-$k$ death class
   $\nu_{r+1} = 3k + 1$ **if and only if** $Q_{r, k} \bmod 4 \ne 2$ (i.e. $Q_{r, k}$ is either odd
   or divisible by $4$).

---

## Execution Order & Verification Gates for Argon (Round 3)

| Step | Module to Create & Verify | Headline Theorems | Verification Gate |
| --- | --- | --- | --- |
| **Step 1** | `AllRungConstantOfMotionAndDualRemainder.lean` + `...Checks.lean` | `allRungTwoExp_add_three_mul_eq`, `allRung_single_exponent_master_identity`, `allRungDefectAcc_pos_and_le_three_pow_sub_two_pow`, `all_rung_constant_of_motion_and_dual_remainder`, `all_rung_repeated_epoch_window_pq_cutoff` | `lake build` + `warningAsError=true`; `0` `sorry`s, standard axioms. |
| **Step 2** | `ConsecutiveQuotientGCDAndEffectivePillai.lean` + `...Checks.lean` | `consecutive_V_gcd_dvd_defectCore`, `dense_core_consecutive_V_coprime_and_ne`, `bounded_V_and_s_rational_pillai_squeeze`, `effective_pillai_cutoff_excludes_bounded_V_and_s` | `lake build` + `warningAsError=true`; `0` `sorry`s, standard axioms. |
| **Step 3** | `ModThreeDeathClassOctadicSieve.lean` + `...Checks.lean` | `octadic_triad_exit_partition`, `coincidence_quotient_bijection_mod_eight`, `death_class_avoidance_mod_four_condition` | `lake build` + `warningAsError=true`; `0` `sorry`s, standard axioms. |
| **Step 4** | Paper, README, Round 3 Report & GitHub Push | Update `MAHLER_FORMALIZATION_PAPER.md`/`.tex`, `README.md`, `lakefile.toml`, and append Part II execution report to `RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md` | Full `lake build` across all targets and `git push origin HEAD`. |

---

# Part II — Fable's Review, Verification, and Extensions (Round 3)

Date: 2026-11-02  
**Role:** Creative Review & Quality Architect (Fable / Claude), reviewing Astra's Round 3 plan above.  
**Status of this part:** Plan only — no Lean written yet; everything below is for Argon to formalize.  
**Numeric pre-verification:** All new algebraic claims in Sections F2–F3 were checked exactly
(`fractions.Fraction`) on hundreds of randomly generated genuine integer epoch-chains before being
written here; see Section F2.8 for the harness and results. The purpose of the numeric pass is *only*
to stop Argon chasing a false lemma — the Lean proofs remain the source of truth.

## F0. Headline: Astra's "refining the error bounds" realization, completed

Astra's Priority 1 proves the **floor** of $2^{S_K} W_K / 3^{S_K}$ is frozen at $W_0 - 1$. During the
live session Astra began — but was interrupted before finishing — a *refinement of the error term*
$\widetilde{\Delta}_K$. I have reconstructed and completed that line of reasoning in full, and it is
better than I expected: the crude bound $\widetilde{\Delta}_K \le 3^{S_K} - 2^{S_K}$ sharpens into a
**genuine Archimedean constant of motion**. Concretely, the normalized defect
$\theta_K := \widetilde{\Delta}_K / 3^{S_K}$ is *strictly monotone increasing and convergent*, so the
real sequence $(2/3)^{S_K} W_K$ converges **downward** to a seed-determined constant
$L \in [W_0 - 1, W_0)$, and every $W_K$ is **pinned to within $3/65$** of the geometric progression
$L \,(3/2)^{S_K}$. This converts the all-rung constant of motion from a static divisibility fact into a
**Mahler-type fractional-part law** — exactly the bridge back to the original $\xi (3/2)^n$ question —
and it couples cleanly to Priority 3's death sieve through a 2-adic valuation constraint. This is the
most important single addition in Part II and is written up in Section F2.

## F1. Verification of Astra's Priorities 1–3

I checked each headline claim line by line (algebra + exact numeric spot-checks). Verdicts:

| Claim | Verdict | Note for Argon |
| --- | --- | --- |
| **P1** $E_K + 3 j_0 = S_K + 3 j_K$ (step-sum cancellation) | ✅ Correct | Trivial telescoping $E_K - S_K = 3\sum_{r<K}(j_{r+1}-j_r) = 3(j_K - j_0)$. Prove by `induction` / `Finset.sum`. |
| **P1** Master identity $2^{S_K} W_K + \widetilde{\Delta}_K = 3^{S_K} W_0$ | ✅ Correct | Confirmed by induction *and* numerically. **Simplification (use this):** the per-epoch law collapses to the **single-exponent $W$-recurrence** $2^{a_r} W_{r+1} + 2^{3 j_r} D_{s_r} = 3^{a_r} W_r$ with $a_r = 3 j_r + s_r$ (same exponent on $2$ and $3$). This is cleaner than carrying $c_r = 3 j_{r+1} + s_r$ separately; derive it once and the master identity is a 3-line induction. |
| **P1** $\widetilde{\Delta}_{K+1} = 3^{a_K}\widetilde{\Delta}_K + 2^{S_K + 3 j_K} D_{s_K}$ | ✅ Correct | Falls straight out of the $W$-recurrence above. |
| **P1** $27 \cdot 2^a \le 26 \cdot 3^a$ for $a \ge 1$ | ✅ Correct | Verified $a = 1..40$; induction base $54 \le 78$, step multiplies by $3/2 > 1$. |
| **P1** $\widetilde{\Delta}_K \le 3^{S_K} - 2^{S_K}$ and floor $= W_0 - 1$ | ✅ Correct | Verified numerically on 200 random chains. **This is genuinely new for *varying* $s_r \ge 4$** — the old Section 28 constant of motion needed fixed $s_r = 4$. The $1/27$-slack step is sound: $2^{3j}(3^{s-3}-2^{s-3}) < 3^{3j}3^{s-3} = 3^a/27 \le 3^a - 2^a$. |
| **P2** $\gcd(V_r, V_{r+1}) \mid (3^{s_r-3} - 2^{s_r-3})$ | ✅ Correct | Immediate: any common divisor divides $3^{a_r}V_r - 2^{c_r}V_{r+1} = D_{s_r}$. Dense core $s_r = 4 \Rightarrow \gcd = 1$. |
| **P2** Bounded-height Pillai squeeze + effective cutoff | ✅ Correct **as a conditional** | The squeeze is unconditional; the *cutoff* consumes an **external effective Pillai/Baker bound** as a hypothesis. Flag it honestly as conditional (like Round 2's S-unit input). See F4.4 for the concrete literature anchor to cite. |
| **P3** `4:2:1:1` octadic partition of $Q_{r,k} \bmod 8$ | ✅ Arithmetic correct, ⚠️ **framing** | The $v_2$-classification $\{1,3,5,7\}\!\to\!v_2{=}0$, $\{2,6\}\!\to\!v_2{=}1$, $\{4\}\!\to\!v_2{=}2$, $\{0\}\!\to\!v_2{\ge}3$ is exactly right, and the bijection-under-lifting is right. **But this is a *counting/density* statement, not a contradiction.** A survivor is free to always land in the "good" classes; nothing here forbids it. Argon must label P3 as *structure/measure*, not *exclusion* — see F4.3 for the honest probabilistic packaging. |

**Two corrections Argon must apply when formalizing:**

1. **P1 naming/shape.** State and prove the single-exponent $W$-recurrence
   `allRung_W_recurrence : 2^(a r) * W (r+1) + 2^(3 * j r) * D (s r) = 3^(a r) * W r` *first*, then derive
   `allRung_single_exponent_master_identity` from it. Do **not** try to prove the master identity directly
   from the mixed $c_r/a_r$ form — `omega` will choke on the three different exponents.
2. **P3 honesty.** Rename the headline intuition from "death-class sieve" (sounds like an exclusion) to
   "death-class **anatomy**." The exclusion power, if any, comes only from coupling with the Archimedean
   constant $L$ (Section F3), not from the octadic counts alone.

## F2. Completing Astra's error-bound refinement: the Archimedean Constant of Motion $L$ and the $3/65$ Pinning Law

**New module to create:** `ArchimedeanPinningAndMahlerBridge.lean` (+ `...Checks.lean`).
**Depends on:** Step 1 (`AllRungConstantOfMotionAndDualRemainder.lean`).

### F2.1 From a crude bound to a convergent constant (the realization, finished)

Astra bounded the cumulative defect by $\widetilde{\Delta}_K \le 3^{S_K} - 2^{S_K}$ and stopped. The
refinement is to *normalize* it. Define
$$\theta_K := \frac{\widetilde{\Delta}_K}{3^{S_K}} \in (0,\,1).$$
Dividing the defect recurrence $\widetilde{\Delta}_{K+1} = 3^{a_K}\widetilde{\Delta}_K + 2^{S_K+3 j_K}D_{s_K}$
by $3^{S_{K+1}} = 3^{a_K}3^{S_K}$ gives a **telescoping increment that is manifestly positive and
geometrically small**:
$$\boxed{\theta_{K+1} = \theta_K + \delta_K, \qquad \delta_K = \Big(\tfrac{2}{3}\Big)^{S_K + 3 j_K}\cdot \tfrac{1}{27}\big(1 - (2/3)^{s_K - 3}\big) > 0 \quad (s_K \ge 4).}$$
So $\theta_K$ is **strictly monotone increasing** and bounded above by $1 - (2/3)^{S_K} < 1$; hence it
**converges** to a limit $\theta_\infty \le 1$. Equivalently, since $\theta_K = W_0 - (2/3)^{S_K} W_K$,
the real sequence
$$g_K := \Big(\tfrac{2}{3}\Big)^{S_K} W_K = W_0 - \theta_K$$
is **strictly monotone decreasing** and converges to
$$\boxed{L := W_0 - \theta_\infty = \lim_{K\to\infty} \Big(\tfrac{2}{3}\Big)^{S_K} W_K \in [\,W_0 - 1,\; W_0\,).}$$
This $L$ is the **Archimedean constant of motion**: it is the exact real number that the boundary data
"track." (In orbit terms $S_K$ is the clock time $n_K$ at boundary $K$ and $W_K = 2^{3 j_K} V_K$, so $L$
is a scalar proxy for the Mahler constant $\xi$ of a hypothetical surviving orbit — see F2.7/F3.)

### F2.2 The exponential tail and the $3/65$ pinning law

Because every rung has $a_r = 3 j_r + s_r \ge s_r \ge 4$, the step-sum grows at least linearly,
$S_M - S_K \ge 4(M-K)$, so the tail is dominated by a geometric series with ratio $(2/3)^4 = 16/81$:
$$0 < \theta_\infty - \theta_K = \sum_{m \ge K}\delta_m \;\le\; \frac{1}{27}\sum_{m\ge K}\Big(\tfrac{2}{3}\Big)^{S_m} \le \frac{1}{27}\cdot\frac{(2/3)^{S_K}}{1 - (2/3)^4} = \frac{1}{27}\cdot\frac{81}{65}\,(2/3)^{S_K} = \frac{3}{65}\,(2/3)^{S_K}.$$
Multiplying $g_K - L = \theta_\infty - \theta_K$ by $(3/2)^{S_K}$ collapses the $K$-dependence entirely:
$$\boxed{0 \;<\; W_K - L\,(3/2)^{S_K} \;\le\; \frac{3}{65} \qquad (\forall K \ge 1).}$$
**Each integer $W_K$ sits a uniform, sub-unit distance $(0, 3/65]$ above the real geometric progression
$L\,(3/2)^{S_K}$.** Since $3/65 < 1$, $W_K$ is the *unique* integer in $(L(3/2)^{S_K}, L(3/2)^{S_K} + 3/65]$,
so $L(3/2)^{S_K}$ is never an integer and
$$\boxed{\big\{\,L\,(3/2)^{S_K}\,\big\} \;\ge\; 1 - \tfrac{3}{65} \;=\; \tfrac{62}{65} \;=\; 0.9538\ldots \qquad (\forall K \ge 1).}$$
This is a true **Mahler-type fractional-part statement**: the hypothetical infinite survivor forces the
fractional parts of $L(3/2)^n$, *along the boundary subsequence $n = S_K$*, to cluster in $[62/65, 1)$,
i.e. just below integers. (A lower companion holds too: $W_K - L(3/2)^{S_K} \ge \delta_K (3/2)^{S_K} \ge
(2/3)^{3 j_K}/81$, so when $j_K$ is bounded the gap is bounded away from $0$ as well.)

### F2.3 Limit-free integer form (formalize THIS first — no real analysis needed)

The clean statement above uses a real limit, which in Lean needs monotone-convergence machinery. Argon
should **first** prove the equivalent **purely integer** two-index version, which needs only `Nat`/`Int`
arithmetic and `Finset.sum`, then (optionally) upgrade to the real $L$. For $M \ge K \ge 1$, put
$d := S_M - S_K$. The master identity applied between rungs $K$ and $M$ gives the exact **tail-gap**
$$3^{d} W_K - 2^{d} W_M \;=\; \sum_{m=K}^{M-1} 3^{\,S_M - S_{m+1}}\,2^{\,S_m - S_K + 3 j_m}\,D_{s_m} \;\in\; \mathbb{Z}_{>0},$$
and the same geometric bound yields the two headline inequalities (both verified numerically, F2.8):
$$\boxed{0 < 3^{d} W_K - 2^{d} W_M \quad\text{and}\quad 65\,\big(3^{d} W_K - 2^{d} W_M\big) \le 3^{\,d+1}.}$$
Equivalently, in terms of a bare modular reduction (no subtraction of reals):
$$\boxed{65\cdot\big((2^{d} W_M)\bmod 3^{d}\big) \;\ge\; 62\cdot 3^{d} \qquad (\forall M \ge K \ge 1,\; d = S_M - S_K).}$$
Taking $M \to \infty$ recovers $L$ and the $\{L(3/2)^{S_K}\} \ge 62/65$ corollary. **The integer form is
unconditional, fully `omega`/`Finset`-friendly, and is the bankable core even if the real-$L$ upgrade is
deferred.**

### F2.4 The 2-adic valuation coupling (this is the bridge to Priority 3)

$W_K = 2^{3 j_K} V_K$ with $V_K$ odd, so $v_2(W_K) = 3 j_K \equiv 0 \pmod 3$ for every $K$. Combined with
the pinning $W_K = \big\lceil L\,(3/2)^{S_K}\big\rceil$ (F2.2), we get a striking **Archimedean $\times$
2-adic coincidence**:
$$\boxed{v_2\!\left(\big\lceil L\,(3/2)^{S_K}\big\rceil\right) \equiv 0 \pmod 3 \quad\text{and}\quad \big\{L\,(3/2)^{S_K}\big\} \ge \tfrac{62}{65}, \qquad \forall K \ge 1.}$$
The nearest integer *above* the real number $L(3/2)^{S_K}$ must simultaneously (a) be within $3/65$ of it
and (b) have 2-adic valuation divisible by 3. This is the Round 3 incarnation of the project's recurring
"archimedean budget vs. 2-adic carry" tension, now pinned to a **single real constant $L$**. It is the
precise hinge on which Section F3's death-avoidance equation turns.

### F2.5 Lean 4 deliverables for F2 (Module: `ArchimedeanPinningAndMahlerBridge.lean`)

Reuse Astra's `allRungStepSum` (`S`), `allRungDefectAcc` (`Δ̃`), and `W r = 2^(3 * j r) * V r`.

1. `allRung_W_recurrence` — single-exponent per-epoch law:
   `∀ r, 2^(3*j r + s r) * W (r+1) + 2^(3*j r) * (3^(s r - 3) - 2^(s r - 3)) = 3^(3*j r + s r) * W r`
   (from the hypothesis chain; prove via `pow_add`/`ring`, not `omega`).
2. `allRung_tailGap_eq_sum` — exact tail-gap identity (the `Finset.sum` above) for `M ≥ K`.
3. `allRung_tailGap_pos` — `K < M ∧ (∀ r, 4 ≤ s r) → 0 < 3^(S M - S K) * W K - 2^(S M - S K) * W M`
   (as a `ℕ` subtraction that is provably positive, or state over `ℤ`).
4. `allRung_tailGap_le` — the `65`-slack bound:
   `65 * (3^(S M - S K) * W K - 2^(S M - S K) * W M) ≤ 3^(S M - S K + 1)` (geometric-series bound; the
   key lemma is `∑_{i≥0} (16/81)^i = 81/65`, done over `ℚ` with `tsum_geometric_of_lt_one` or a finite
   `Finset.geom_sum` + monotone tail).
5. `allRung_pinning_mod_lower` — the modular punchline:
   `65 * ((2^(S M - S K) * W M) % 3^(S M - S K)) ≥ 62 * 3^(S M - S K)` for `M ≥ K ≥ 1`, `∀ r, 4 ≤ s r`.
6. **(Real upgrade, optional but high-value)** `exists_archimedean_constant_of_motion`:
   `∃ L : ℝ, (↑W 0 - 1 ≤ L ∧ L < ↑W 0) ∧ ∀ K, 1 ≤ K → 0 < (↑(W K) - L * (3/2)^(S K)) ∧ (↑(W K) - L * (3/2)^(S K)) ≤ 3/65`.
   Construct `L` as the limit of the antitone bounded sequence `g K = (2/3)^(S K) * W K` via
   `tendsto_atTop_ciInf` / `Real.exists_isGLB` on a `BddBelow` `Antitone` range (Mathlib:
   `tendsto_atTop_ciInf (hf : Antitone f) (h : BddBelow (range f))`).
7. `fract_pinning_ge` — `∀ K ≥ 1, (62 : ℝ)/65 ≤ Int.fract (L * (3/2)^(S K))` (from 6 + `Int.fract`).
8. `boundary_val2_mod_three_zero` — `∀ K, v₂ (W K) % 3 = 0` (i.e. `(W K).factorization 2 % 3 = 0`),
   using `W K = 2^(3 * j K) * V K` with `Odd (V K)` and `Nat.factorization_mul`/`Nat.Prime.factorization_pow`.
9. `pinning_ceil_identity` — `∀ K ≥ 1, W K = ⌈L * (3/2)^(S K)⌉` (from 6, since the gap is in `(0,1)`).
10. **Capstone** `archimedean_two_adic_coincidence`: bundle 7 + 8 + 9 into the boxed statement of F2.4.

### F2.6 Expected obstruction and the negative/limitative result to bank

**What this does NOT do (state this explicitly in the paper).** The pinning law is a *rigidity*
statement about a hypothetical infinite chain; it is **not yet a contradiction**. Two honest gaps:

- **Subsequence, not all $n$.** The constraint $\{L(3/2)^{S_K}\} \ge 62/65$ lives on the sparse boundary
  set $\{S_K\}$ (gaps $\ge 4$), not on all $n$. Mahler's property is an all-$n$ statement, and
  $62/65 > 1/2$ would only contradict it if $L$ were literally the orbit's $\xi$ *and* $S_K$ ranged over
  all survival times. Neither is automatic.
- **$L$ is only a scalar proxy for $\xi$.** The $2^{3 j_K}$ bookkeeping in $W_K = 2^{3 j_K} V_K$ means
  $L$ and $\xi$ differ by seed-dependent powers of 2; the fractional-part transfer between them is the
  missing lemma (F5).

**Bank this as a positive limitative theorem**, not a failure: *"Every infinite all-rung expanding chain
determines a real constant $L \in [W_0-1, W_0)$ with $\{L(3/2)^{S_K}\} \ge 62/65$ and
$v_2(\lceil L(3/2)^{S_K}\rceil) \equiv 0 \pmod 3$ for all $K$; conversely, any proof that no real $L$ can
meet both conditions on an infinite set with gaps $\ge 4$ closes the expanding regime."* This is a
**clean reduction of the last open case to a single Diophantine property of one real number** — a strictly
better target than "rule out $V_r \to \infty$." Record it alongside Round 2's `R3.1/R3.2` as `R3.3`.

### F2.7 Why this is the right object (sanity, not proof)

By Weyl/Koksma, for Lebesgue-a.e. $L$ the sequence $\{L(3/2)^n\}$ is equidistributed, so clustering in
$[62/65,1)$ along an infinite subsequence is an **exceptional (measure-zero) condition** — perfectly
consistent with Mahler's theorem that $Z$-numbers form a null set, and with the known fact that the
$3/2$-orbit problem is *not* decidable by measure alone. So the pinning law correctly lands $L$ in the
"thin exceptional set where a counterexample would have to live," which is exactly where the remaining
fight is. Formalizing the equidistribution remark is **not** required (and Mathlib's Weyl support is thin);
mention it in prose only.

### F2.8 Numeric pre-verification (already run; reproduce if desired)

Three exact-arithmetic harnesses (Python `fractions.Fraction`) were run before writing this section:
- **200 arbitrary rational chains** ($W_0 \le 50$, $j_r \le 4$, $4 \le s_r \le 9$): master identity,
  $\theta_K \nearrow$, $0 < \theta_K < 1$, $1 \le \widetilde{\Delta}_K \le 3^{S_K}-2^{S_K}$, and
  $g_K \searrow$ — **all hold**.
- **400 genuine integer chains** (only steps with integer $W_{r+1} \ge 1$ accepted; $L$ estimated from a
  long $a{=}4$ tail): $0 < W_K - L(3/2)^{S_K} \le 3/65$ and $\{L(3/2)^{S_K}\} \ge 62/65$ — **all hold**.
- **600 genuine integer chains**, limit-free form: $0 < 3^{d}W_K - 2^{d}W_M$,
  $65(3^{d}W_K - 2^{d}W_M) \le 3^{d+1}$, and $65\,((2^{d}W_M)\bmod 3^{d}) \ge 62\cdot 3^{d}$ — **all hold**
  (worst observed gap ratio $0.0206 < 3/65 = 0.0462$).

Constants cross-checked: $27\cdot 2^a \le 26\cdot 3^a$ for $a = 1..40$; $\tfrac{1}{1-(2/3)^4} = \tfrac{81}{65}$;
$\tfrac{1}{27}\cdot\tfrac{81}{65} = \tfrac{3}{65}$.

## F3. The unifying coupling: a seed-determined death-avoidance equation (bridging Priority 1 and Priority 3)

This is the creative payoff of F2 and directly answers the summary's call to "couple the frozen top part
with the death-class sieve." Priority 3 shows the epoch transition is governed by $v_2(X_r)$ where
$X_r = 3^{a_r}V_r - D_{s_r} = 2^{\nu_{r+1} + s_r - 3}V_{r+1}$, with the **death class** at
$\nu_{r+1} \equiv 1 \pmod 3$. Section F2 shows the *same* $V_r$ data is pinned to the single real constant
$L$: $W_r = 2^{3 j_r}V_r = \lceil L(3/2)^{S_r}\rceil$. Eliminating $V_r$ between the two gives a
**closed, seed-determined recursion in which the only free choice at each epoch is which octadic class to
fall into, and the Archimedean constant $L$ dictates the admissible 2-adic valuation**:
$$\boxed{\nu_{r+1} = v_2\!\Big(3^{a_r}\big\lceil L\,(3/2)^{S_r}\big\rceil \cdot 2^{-3 j_r} - D_{s_r}\Big) - (s_r - 3), \qquad \nu_{r+1} \not\equiv 1 \pmod 3 \ \ \forall r.}$$
The content: $L$ is *frozen by the seed* (F2), yet it must steer every $X_r$ away from the $v_2$-death
class forever. Two formalizable sub-results, both bankable:

1. `coupling_val_determined_by_L` — the valuation $\nu_{r+1}$ is a function of $(L, S_r, a_r, s_r, j_r)$
   alone (no independent freedom in $V_{r+1}$), because $V_{r+1}$ is itself pinned by $L$ at step $r+1$.
   **Deliverable:** express `death-avoidance for all r` as a single predicate on the pair
   `(L, (fun r => (j r, s r)))`, i.e. an infinite system of 2-adic congruences in the *one* real unknown $L$.
2. `coupling_finite_horizon_contradiction_scheme` — the honest conditional closer: *if* one supplies an
   effective **lower bound for $\{L(3/2)^n\}$ decay** (equivalently an irrationality-measure-type bound for
   $L$ against the sparse base-$3/2$ progression), the death-avoidance congruences over-determine $L$ past
   a computable horizon $K_0(W_0)$, contradicting $\{L(3/2)^{S_K}\} \ge 62/65$. State it as
   `(EffectiveFractionalLowerBound L) → ¬ InfiniteExpandingChain`. This isolates **exactly one** missing
   analytic input (F5) and formalizes everything around it.

**Why bother if input (2) is conditional?** Because it converts an open *combinatorial* problem (avoid a
residue class forever) into an open *Diophantine* problem about **one real number**, and the latter is the
kind of statement that effective transcendence theory (Baker, Rhin–Viola, Bugeaud) actually targets. Even
unproven, the reduction is a publishable, Lean-checked structural theorem.

## F4. Additional creative tracks (prioritized; each with Lean deliverable + obstruction + banked result)

These are lower-priority than F2–F3 but each yields a formalizable negative/limitative result, per the
team policy that *banked dead ends advance the problem*. Listed in descending expected value.

### F4.1 Skolem–Mahler–Lech route to the aperiodicity obstruction (new proof of an old fact)
The carry recurrence $C_{m+1} = 3 C_m + 2^m e_m$ (parity word $e$) is a *non-autonomous* linear recurrence.
**Idea:** homogenize by treating $2^m$ as a second geometric mode, giving the constant-coefficient
2-variable recurrence $\binom{C_{m+1}}{2^{m+1}} = \begin{psmallmatrix}3 & e_m\\ 0 & 2\end{psmallmatrix}\binom{C_m}{2^m}$.
*If* the parity word $e$ were eventually periodic, the product matrix is eventually a fixed power, and
**Skolem–Mahler–Lech** forces the coincidence set $\{m : 3^k \mid C_m\}$ to be eventually periodic (finite
union of arithmetic progressions). That contradicts the already-proved unconditional complexity slope
$\ge \log 2/\log(3/2) \approx 1.7095$ for any $a_0 \ge 1$. **Deliverable:**
`eventuallyPeriodic_parity_imp_false_via_SML` — a *second, independent* proof of the periodic obstruction
routed through SML/linear-recurrence periodicity. **Obstruction to bank:** for a genuine $Z$-number the
word is *not* eventually periodic, so SML gives no contradiction on the nose — the autonomous reduction
only bites on the periodic branch. Mathlib has no SML; formalize the *finite* statement (periodic word
$\Rightarrow$ periodic coincidence set) by hand via the matrix power, avoiding the full theorem.

### F4.2 Ostrowski / $\beta = 3/2$ digit route for the pinning subsequence
F2 forces $\{L(3/2)^{S_K}\} \ge 62/65$, i.e. in the greedy $\beta = 3/2$ numeration (already built in
`BetaShiftThreeHalvesDictionary.lean`) the expansion of $L$ carries the **maximal digit** at every boundary
position $S_K$. **Deliverable:** `pinning_imp_topDigit_at_boundaries` — the $\beta$-expansion of $L$ has
digit $= \lfloor \beta \rfloor = 1$ at positions $S_K$ and obeys Parry admissibility elsewhere.
**Obstruction to bank:** "top digit on a sparse subsequence" pins $L$ only along $\{S_K\}$, not fully; the
$\beta$-shift top is a single orbit but the sparse constraint is satisfiable — so this is **subsequence
$\beta$-rigidity, not full rigidity**. Still, it connects $L$ to the non-sofic $S_{3/2}$ structure and may
combine with F3's valuation congruences. Formalize as a property of `kneadingDigit`/`admissibleResidueFinset`.

### F4.3 Markov-chain-on-residues heuristic — banked explicitly as a NON-proof
The `4:2:1:1` octadic anatomy (Priority 3) *suggests*, under a **uniform-residue independence heuristic**,
that each epoch lands in the death classes $\{2,6\}$ (a $\tfrac14$ share of the even continuation branch)
with constant positive probability, so survival through $N$ epochs has heuristic probability $\to 0$
geometrically. **This is NOT a proof** — the residues are *determined by the single constant $L$* (F2/F3),
hence neither uniform nor independent; the heuristic ignores exactly the correlations that a counterexample
would exploit. **Deliverables:** (a) `octadic_density_counts` — the rigorous combinatorial core (the
$4:2:1:1$ class counts and the $\{2,6\}$ death share), fully proved; (b) `markovSurvival` — a *clearly
labeled heuristic* `def` computing the product-measure survival decay, with a docstring stating it is a
**non-theorem / intuition pump**, plus a Lean `example` exhibiting a concrete correlated chain that beats
the heuristic prediction (to make the gap undeniable). **Banked result:** "the measure heuristic predicts
null survival but is provably not rigorous; the independence assumption fails because $L$ couples the
epochs." This is precisely the kind of honest negative packaging the program wants, and it stops a future
round from mistaking the density for a proof.

### F4.4 Effective Pillai/Baker literature anchor for Priority 2
Priority 2's cutoff needs an external effective bound. The right citation is **Bennett (2001)**,
*Rational approximation to algebraic numbers of small height*: for the pair $(2,3)$ the inequality
$|3^a - 2^b| \ge \max(3^a,2^b)^{\,1-\kappa}$ holds effectively, and more directly the finiteness/explicit
list of solutions to $3^a - 2^b = c$ for fixed small $c$ (Pillai; Stroeker–Tijdeman). **Deliverable:**
`effective_pillai_hypothesis` — state the needed bound as a named hypothesis with the Bennett/Pillai
constant, and prove `effective_pillai_cutoff_excludes_bounded_V_and_s` *relative to it* (so the conditional
status is explicit in the type). **Obstruction to bank:** Mathlib has no Baker/Bennett; the result stays
conditional, mirroring Round 2's S-unit dependency. Note the honest scope in the paper.

## F5. Honest "what would actually close the proof"

After Round 3, the entire conjecture reduces to **one analytic input about the single real constant $L$**:

> **Missing lemma (R3.3-closer).** There is an effective $c > 0$ and $N_0$ with
> $\{L\,(3/2)^n\} \le 1 - c$ for some $n \in \{N_0, \ldots, N_0 + g\}$ in every gap of length $g \ge 4$ —
> equivalently, $L$ does not admit maximal $\beta=3/2$ digits on an infinite gap-$\ge 4$ subsequence.

Given that lemma, F2's pinning ($\{L(3/2)^{S_K}\} \ge 62/65$) is violated at some boundary, killing the
expanding regime and (with Rounds 1–2) finishing Mahler's $3/2$ conjecture. **This lemma is currently open
and is essentially a case of the notorious "$(3/2)^n \bmod 1$" distribution problem** — so Round 3 should
*not* be scoped to prove it. Round 3's realistic, fully-unconditional deliverables are:
(i) the Archimedean constant of motion + $3/65$ pinning law (F2, integer form), (ii) the $L$-to-death-class
coupling as a reduction (F3), and (iii) the banked limitative results F4.1–F4.4. The proof is **not** closed
by Round 3; it is **reduced to a single, sharply stated, standard-looking Diophantine lemma about one real
number** — a substantial and honest advance over "eliminate $V_r \to \infty$."

## F6. Revised execution order for Argon (Round 3, with Fable's additions interleaved)

| Step | Module | Headline theorems | Gate |
| --- | --- | --- | --- |
| **1** | `AllRungConstantOfMotionAndDualRemainder.lean` (Astra) | as in Astra's table; **add** `allRung_W_recurrence` and prove the master identity *from it* | `lake build`, `warningAsError=true`, 0 `sorry` |
| **1.5 (Fable)** | `ArchimedeanPinningAndMahlerBridge.lean` | `allRung_tailGap_eq_sum`, `allRung_tailGap_pos`, `allRung_tailGap_le`, `allRung_pinning_mod_lower` (integer core); then `exists_archimedean_constant_of_motion`, `fract_pinning_ge`, `boundary_val2_mod_three_zero`, `archimedean_two_adic_coincidence` (real upgrade) | same; keep integer core even if real upgrade is deferred to a `sorry`-free partial |
| **2** | `ConsecutiveQuotientGCDAndEffectivePillai.lean` (Astra) | as in Astra's table; mark the cutoff **conditional**, cite Bennett/Pillai via `effective_pillai_hypothesis` | same |
| **3** | `ModThreeDeathClassOctadicSieve.lean` (Astra) | as in Astra's table, **renamed as "anatomy"**; `octadic_density_counts` lives here | same |
| **3.5 (Fable)** | `DeathAvoidanceCouplingAndBankedHeuristics.lean` | `coupling_val_determined_by_L`, `coupling_finite_horizon_contradiction_scheme` (F3); `eventuallyPeriodic_parity_imp_false_via_SML` (F4.1); `markovSurvival` heuristic `def` + counter-`example` (F4.3); optional `pinning_imp_topDigit_at_boundaries` (F4.2) | same; heuristic clearly labeled non-theorem |
| **4** | Paper/README/`lakefile.toml`/report + push | update file counts; add a **"What is proved vs. what is reduced"** box reflecting F5; append execution report | full `lake build` all targets, `git push origin HEAD` |

**Priority discipline (unchanged from Astra):** if time-boxed, do Steps 1 → 1.5 → 3.5-coupling first
(the genuinely new math), then 2 and 3. The integer-form pinning (Step 1.5 core) is the single
highest-value unconditional result and must land even if nothing else does.

## F7. Mathlib reality notes for the new modules

- **Geometric tail bound** (F2.2/F2.5): work over `ℚ` or `ℝ`; use `tsum_geometric_of_lt_one`
  (ratio `(2/3)^4 = 16/81 < 1`) for the clean `81/65`, or a finite `geom_sum_le` + nonneg tail to stay in
  `ℚ` and dodge `tsum` side-goals. The constant equality `(1/27)*(81/65) = 3/65` is `norm_num`.
- **Monotone-convergence constant $L$** (F2.5 item 6): the antitone bounded sequence `g K = (2/3)^(S K) * W K`
  over `ℝ`; `L := ⨅ K, g K` via `Real.exists_isGLB`/`tendsto_atTop_ciInf (hf : Antitone g) (BddBelow (Set.range g))`.
  `BddBelow` from `g K ≥ W 0 - 1`. Avoid `Filter`-heavy API; `ciInf` + `le_ciInf`/`ciInf_le` suffice.
- **`Int.fract`** (F2.5 item 7): `Int.fract x = x - ⌊x⌋`; use `Int.fract_nonneg`, `Int.fract_lt_one`,
  and `Int.self_sub_floor`. For `W K = ⌈L(3/2)^{S K}⌉` use `Int.ceil_eq_iff` with the gap in `(0,1)`.
- **2-adic valuation** (F2.5 item 8): prefer `Nat.factorization (W K) 2` with
  `Nat.factorization_mul`, `Nat.Prime.factorization_pow`, and `Nat.factorization_eq_zero_of_not_dvd`
  for the odd part `V K`. `% 3 = 0` is then `by simp [...]`/`omega`.
- **Modular pinning** (F2.5 item 5): `(2^d * W M) % 3^d` — keep everything in `ℕ`; the inequality
  `65 * (...) ≥ 62 * 3^d` is linear once `3^d W_K - 2^d W_M` is bounded, so `omega` closes it *after* the
  nonlinear `pow` facts are supplied as hypotheses (don't feed `omega` raw `3^d`).
- **No new axioms**; everything stays in `Classical` + standard Mathlib. No Baker/SML/Weyl formalization is
  attempted — those appear only as named hypotheses (F4.1, F4.4) or prose (F2.7).
- **`decide` caution** (carried from Round 2): do not `decide` on `ℝ`/`ℚ` (in)equalities; use `norm_num`.
  For the octadic `Fin 8` classification (`octadic_density_counts`) `decide` is fine.

### Fable's closing note to Argon
The crown jewel of Round 3 is the **integer-form pinning law** (Step 1.5 core, F2.3) — it is unconditional,
needs no analysis, and upgrades the constant of motion into a Mahler-type statement about a single real
constant. Land that first. Everything else (real-$L$ upgrade, F3 coupling, F4 banked dead ends) is
structure and honesty around it. Do **not** let the `markovSurvival` heuristic (F4.3) drift into looking
like a proof — the whole point of banking it is that it is *not* one. And please keep the "what is reduced,
not proved" box (F5) prominently in the paper: we are one clean Diophantine lemma away, and saying so
precisely is worth more than overclaiming.



