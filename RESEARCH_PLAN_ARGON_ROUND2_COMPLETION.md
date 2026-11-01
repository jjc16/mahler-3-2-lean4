# Research Plan for Argon (Round 2): Toward Closing Mahler's $Z$-Number Problem

Date: 2026-11-01  
**Baseline:** `150` Lean 4.19.0 files (`0` `sorry`s, `0` warnings, commit `4da5f53`)  
**Predecessor Plan & Report:** [RESEARCH_PLAN_ARGON_GENERAL_PROOF.md](./RESEARCH_PLAN_ARGON_GENERAL_PROOF.md)  
**Structure:** Part I (Tracks 1–5, drafted by Argon) · **Part II (Sections 6–16, Fable's review: verification of Tracks 1–5, three corrections, the β-shift identification, and Tracks 6–15).** Argon should execute in the order of **Section 16**, which supersedes the Part I execution table.

---

## Executive Summary: What Round 1 Proved and How It Reshapes Round 2

Round 1 executed all 23 sections of Astra and Fable's research plan across eight new Lean 4 modules
([ParitySurplusPotentialsAndSafetyGame.lean](./ParitySurplusPotentialsAndSafetyGame.lean),
[BaseSixMultiplicationAutomaton.lean](./BaseSixMultiplicationAutomaton.lean),
[TransferOperatorJSRAndCarryFourier.lean](./TransferOperatorJSRAndCarryFourier.lean),
[SolenoidRigidityDiscrepancyAndRenormalization.lean](./SolenoidRigidityDiscrepancyAndRenormalization.lean),
and their `*Checks.lean` suites). Those machine-checked proofs established **four structural laws**
that rule out entire classes of dead-end proof attempts and isolate the exact mechanisms capable of
reaching a general proof:

1. **Law 1 — Fixed-Depth Congruence Graphs Are Blocked by 2-Adic Ghost Self-Loops
   (`mod_two_pow_ghost_self_loop_at_all_depths`, `no_subcritical_weight_of_self_loop`):**
   At *every* finite 2-adic depth $2^k$, the 2-adic rational fixed points
   $-9/19,\, 1/2059,\, 1/58025 \in \mathbb{Z}_2$ reduce to integer residues $< 2^k$ that form
   **self-loops** in the mod-$2^k$ transition graph, forcing spectral radius $\rho_k \ge 1$ and
   $\mathrm{JSR} \ge 1$.
   - *Consequence for Round 2:* Any proof that forgets the **stabilized top binary bits**
     ($\eta_N = 0$ for $N \ge W$, i.e. $0 < a_0 < 2^W$ in $\mathbb{N}$ rather than $\mathbb{Z}_2$)
     cannot succeed. Every Round 2 attack must explicitly use $\eta_N = 0$ ($N \ge W$) or the
     archimedean positivity/size of $q_N = \text{orbit } a_0\ N$.

2. **Law 2 — Exact 3-Adic Carry Memory Erasure & Bit-for-Bit Carry Injectivity
   (`wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod`, `wordCarry_mod_three_pow_eq_iff_parity_eq`):**
   In the 3-adic carry group $\mathbb{Z}/3^m\mathbb{Z}$, the $m$-step carry erases all history prior
   to step $n$, and the normalized carry map $(e_0, \dots, e_{m-1}) \mapsto C_m \bmod 3^m$ is
   **100% injective** on binary words of length $m$.
   - *Negative consequence:* Non-identical anagrams never collide in their normalized $3^m$ carry;
     raw carry pigeonhole requires waiting for an exact length-$m$ word repeat.
   - *New positive consequence for Round 2 (Track 1 below):* Because the carry map modulo $3^m$ is
     bijective on length-$m$ binary words and $2^m b_{n+m} = 3^m b_n + C_m(\text{shift}_n \varepsilon)$,
     the **ending orbit residue $b_{n+m} \bmod 3^m$ uniquely determines the entire $m$-step backward
     parity word**, while the **starting residue $b_n \bmod 2^m$ uniquely determines the entire
     $m$-step forward parity word**—on **all of $[0, 1/2)$**, with no Dense-Core restriction!

3. **Law 3 — Look-Ahead-Free Nonnegativity of the Odd-Count Deficit Potential
   (`signedMargin_add_le_two_pow_mul_shift`, `three_mul_oddParityCount_le_add_three_of_signedMargin_pos`):**
   Because `signedMargin` is shift-submultiplicative ($D_{k+m}(\varepsilon) \le 2^k D_m(\text{shift}_k\varepsilon)$),
   every suffix of a feasible parity stream is feasible from depth $0$, and
   $$\Phi_{\text{def}}(\varepsilon, N) := (N + 3) - 3\,\text{oddParityCount}(\varepsilon, N) \ge 0$$
   holds unconditionally at every feasible horizon $N$. Moreover, $\Phi_{\text{def}}$ and $D_N / 2^N$
   are strictly stationary ($\Delta = 0$) across `100` ($s = 3$) blocks, whereas the stabilized
   seed quotient $q_N$ loses 3 factors of $2$ per `100` block via
   $8(19 q_{N+3} + 9) = 27(19 q_N + 9)$ (`stabilized_seed_100_two_adic_valuation_drop`).

4. **Law 4 — Safety-Game & Escape-Rank Completeness (`safety_game_kernel_and_rank_completeness`):**
   Mahler's conjecture holds if and only if the safety-game survivor kernel $\mathcal{K} = \bigcap_N \text{Surv}_N$
   is empty, if and only if $B(N) = \text{leastPositiveSurvivor } N \to \infty$, if and only if
   every positive seed $a_0 \ge 1$ hits a finite horizon where $D_N \le 0$ (which is implied by a
   single horizon with $\Phi_{\text{def}}(a_0, N) < 0$, i.e. $3 O_{a_0}(N) > N + 3$, or a single visit
   to $T^n(a_0) \equiv 3 \pmod 4$).

---

## Round 2 Primary Objective & Architecture

Round 2 replaces broad exploration with **five focused, high-leverage mathematical tracks** aimed at
closing the remaining coverage gaps identified in the [Phase A Audit Matrix](./RESEARCH_PLAN_ARGON_GENERAL_PROOF.md)
and exploiting the new structural laws above:

- **Track 1 (Universal Forward $2$-Adic / Backward $3$-Adic Orbit Bijection & Global Right-Special Spectral Gap on $[0, 1/2)$):**
  Lift the $(2^m, 3^m)$ prefix-collision biconditional and right-special valuation lock from the
  Dense Core $[8/81, 1/2)$ to **arbitrary integer orbits on all of $[0, 1/2)$** using
  `wordCarry_mod_three_pow_eq_iff_parity_eq`.
- **Track 2 (The Universal $-72(3^{s-3} - 2^{s-3})$ Defect Factorization & Removing the $[8/81, 1/2)$ Floor):**
  Exploit the exact identity
  $$E(s) = 9\cdot 2^s - 8\cdot 3^{s-1} = -72\big(3^{s-3} - 2^{s-3}\big) \qquad (\forall s \ge 3)$$
  where $\gcd(3^{s-3} - 2^{s-3}, 6) = 1$ for **every** $s \ge 4$. This proves that **both**
  $v_2(E(s)) = 3$ and $v_3(E(s)) = 2$ are universal across all $s \ge 4$ (`0001`, `00001`, ... all
  the way to $0$), extending the normalized coprime recurrence $U_r = 9 V_r$ ($\gcd(V_r, 6) = 1$)
  from $s = 4$ to arbitrary $s_r \ge 4$!
- **Track 3 (Coupled $(\Phi_{\text{def}},\, v_2(19 q_N + 9))$ Potential & the $s = 2$ vs. $s \ge 4$ Tradeoff — Target R2.1):**
  Combine the look-ahead-free deficit potential $\Phi_{\text{def}}(\varepsilon, N) \ge 0$ with the
  2-adic valuation of $19 q_N + 9$ on stabilized seeds ($\eta_N = 0$ for $N \ge W$) to bound how
  long an orbit can alternate between $\Phi_{\text{def}}$-increasing blocks ($s \ge 4$),
  $\Phi_{\text{def}}$-stationary blocks ($s = 3$, which drain $v_2(19 q_N + 9)$ by $-3$), and
  $\Phi_{\text{def}}$-decreasing blocks ($s = 2$, which drop $\Phi_{\text{def}}$ by $-1$ and force
  $s_{\text{next}} \ge 6$).
- **Track 4 (Superlinear & Bispecial Return-Time Complexity Exclusions — Target R2.3):**
  Combine Track 1's global step-by-step right-special valuation lock $v_2(b_{n_2} - b_{n_1}) = m$
  with multi-occurrence ultrametric pigeonhole to push complexity exclusions beyond fixed linear
  slopes $p(L) \le \kappa L + C_0$.
- **Track 5 (Base-6 Left-Boundary Causal-Cone Compression & Certified $B(N)$ Horizon Lifting):**
  Couple the left-zero boundary $d(i) = 0$ ($i \ge m$) of [BaseSixMultiplicationAutomaton.lean](./BaseSixMultiplicationAutomaton.lean)
  to the shift-submultiplicative `signedMargin` engine to certify stronger lower bounds on
  `leastPositiveSurvivor N` ($B(N)$) and test candidate inductive rank certificates.

---

## Track 1: Universal Forward $2$-Adic / Backward $3$-Adic Orbit Bijection on All of $[0, 1/2)$

### 1.1 Mathematical discovery from Round 1

Along any integer orbit $b_n = \text{orbit } a_0\ n$ with parity stream $\varepsilon(n) = b_n \bmod 2$,
applying `two_pow_mul_seedQuotient_eq` to the shifted seed $b_n$ over $m$ steps gives the exact
step-by-step transition identity:
$$2^m \cdot b_{n+m} = 3^m \cdot b_n + \text{wordCarry }(\text{shiftStream }\varepsilon\ n)\ m.$$
Reducing this single equation modulo $2^m$ and modulo $3^m$ and applying Round 1's
`wordCarry_mod_three_pow_eq_iff_parity_eq` yields a **3-way universal biconditional** valid for
**every** integer seed $a_0 \in \mathbb{N}$, **every** pair of indices $n_1, n_2 \in \mathbb{N}$,
and **every** window length $m \in \mathbb{N}$ (with **no** interval or block-length assumption):
$$\boxed{
  b_{n_1} \equiv b_{n_2} \pmod{2^m}
  \;\Longleftrightarrow\;
  \big(\forall j < m,\; b_{n_1+j} \bmod 2 = b_{n_2+j} \bmod 2\big)
  \;\Longleftrightarrow\;
  b_{n_1+m} \equiv b_{n_2+m} \pmod{3^m}!
}$$

### 1.2 Exact right-special 2-adic & 3-adic valuation lock on raw orbits

Suppose a length-$m$ parity factor repeats at $n_1 < n_2$ ($\forall j < m,\, b_{n_1+j} \bmod 2 = b_{n_2+j} \bmod 2$)
and diverges at step $m$ ($b_{n_1+m} \bmod 2 \ne b_{n_2+m} \bmod 2$, i.e. the factor is **right-special**).
Then:
1. Subtracting the $m$-step equations cancels `wordCarry` identically:
   $$2^m (b_{n_2+m} - b_{n_1+m}) = 3^m (b_{n_2} - b_{n_1}).$$
2. Because the parities agree for $j < m$ and disagree at $j = m$, the universal bijection in 1.1 forces:
   - $2^m \mid (b_{n_2} - b_{n_1})$ and $2^{m+1} \nmid (b_{n_2} - b_{n_1})$, so the 2-adic quotient
     $q_2 := (b_{n_2} - b_{n_1}) / 2^m$ is **strictly odd** ($q_2 \bmod 2 = 1$)!
   - $3^m \mid (b_{n_2+m} - b_{n_1+m})$, and the 3-adic quotient
     $q_3 := (b_{n_2+m} - b_{n_1+m}) / 3^m = q_2$ is the **exact same odd integer**!
3. Since $b_n$ is strictly increasing for every $a_0 \ge 1$ (`orbit_strictMono_of_pos`:
   $b_{n+1} = \lfloor (3 b_n + 1)/2 \rfloor > b_n$ for all $b_n \ge 1$), $n_1 < n_2$ guarantees
   $b_{n_1} < b_{n_2}$ and $b_{n_1+m} < b_{n_2+m}$, so $q_2 = q_3 \ge 1$ is a positive odd integer,
   yielding the **assumption-free raw-orbit bounds**:
   $$2^m \le b_{n_2} - b_{n_1} < b_{n_2} \quad\text{and}\quad 3^m \le b_{n_2+m} - b_{n_1+m} < b_{n_2+m}!$$

### 1.3 Lean 4 deliverables for Track 1 (Module: `UniversalOrbitBijectionAndRightSpecialLock.lean`)

1. Prove `orbit_strictMono_of_pos`: for $a_0 \ge 1$, $n_1 < n_2 \implies \text{orbit } a_0\ n_1 < \text{orbit } a_0\ n_2$.
2. Prove `two_pow_mul_orbit_add_eq`:
   $2^m \cdot \text{orbit } a_0\ (n + m) = 3^m \cdot \text{orbit } a_0\ n + \text{wordCarry }(\text{shiftStream }(\text{orbit } a_0)\ n)\ m$.
3. Prove the **Universal Forward–Backward $(2^m, 3^m)$ Orbit Bijection
   (`orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow`)**:
   $$\text{orbit } a\ n_1 \bmod 2^m = \text{orbit } a\ n_2 \bmod 2^m
     \;\Longleftrightarrow\;
     (\forall j < m,\, \text{orbit } a\ (n_1+j) \bmod 2 = \text{orbit } a\ (n_2+j) \bmod 2)
     \;\Longleftrightarrow\;
     \text{orbit } a\ (n_1+m) \bmod 3^m = \text{orbit } a\ (n_2+m) \bmod 3^m.$$
4. Prove the **Global Right-Special Exact Valuation & Odd-Quotient Lock
   (`right_special_orbit_exact_two_and_three_adic_lock`)**:
   Whenever $a_0 \ge 1$, $n_1 < n_2$, $\forall j < m,\, \text{orbit } a_0\ (n_1+j) \bmod 2 = \text{orbit } a_0\ (n_2+j) \bmod 2$,
   and $\text{orbit } a_0\ (n_1+m) \bmod 2 \ne \text{orbit } a_0\ (n_2+m) \bmod 2$, there exists a
   positive **odd** integer $q_{\text{odd}} \ge 1$ (`q_odd % 2 = 1`) such that:
   $$\text{orbit } a_0\ n_2 - \text{orbit } a_0\ n_1 = 2^m \cdot q_{\text{odd}}
     \quad\text{and}\quad
     \text{orbit } a_0\ (n_2 + m) - \text{orbit } a_0\ (n_1 + m) = 3^m \cdot q_{\text{odd}}!$$
5. Prove the **Two-Occurrence Ultrametric Pairing Upgrade (`three_occurrence_raw_orbit_two_pow_add_one_dvd`)**:
   If a length-$m$ parity factor occurs at **three** positions $n_1 < n_2 < n_3$, then at least two
   of the three extensions at index $m$ must agree in parity $\bmod 2$, forcing $2^{m+1} \mid (b_{n_b} - b_{n_a})$
   and $3^{m+1} \mid (b_{n_b + m + 1} - b_{n_a + m + 1})$ for some pair $(a, b) \in \{(1,2),(2,3),(1,3)\}$!

---

## Track 2: The Universal $-72(3^{s-3} - 2^{s-3})$ Defect Factorization & Removing the $[8/81, 1/2)$ Floor

### 2.1 Exact algebraic identity across all $s \ge 3$

In [SparseDefectCocycleAndValuationLock.lean](./SparseDefectCocycleAndValuationLock.lean), a single
odd-to-odd block of length $s$ satisfies:
$$2^s (19 b' + 9) = 3^s (19 b + 9) + E(s), \qquad E(s) = 9\cdot 2^s - 8\cdot 3^{s-1}.$$
For **every** $s \ge 3$, $E(s)$ factors identically as:
$$E(s) = 9\cdot 8\cdot 2^{s-3} - 8\cdot 9\cdot 3^{s-3} = -72 \cdot \big(3^{s-3} - 2^{s-3}\big).$$
Observe the two key properties of $D_{s-3} := 3^{s-3} - 2^{s-3}$ for **every** $s \ge 4$:
1. $D_{s-3} \ge 1$ is **odd** ($3^{s-3} \equiv 1 \pmod 2$, $2^{s-3} \equiv 0 \pmod 2$) and
   **not divisible by $3$** ($3^{s-3} \equiv 0 \pmod 3$, $2^{s-3} \not\equiv 0 \pmod 3$), so
   $$\gcd\big(3^{s-3} - 2^{s-3},\, 6\big) = 1 \qquad (\forall s \ge 4)!$$
2. Consequently, **both the 2-adic valuation and the 3-adic valuation of $E(s)$ are constant across all $s \ge 4$**:
   $$v_2(E(s)) = v_2(72) = 3 \quad\text{and}\quad v_3(E(s)) = v_3(72) = 2 \qquad (\forall s \ge 4)!$$

### 2.2 Universal normalized defect recurrence for arbitrary $s_r \ge 4$

Suppose an orbit undergoes $j_0$ blocks of length $3$, a defect of **arbitrary** length $s_0 \ge 4$,
$j_1$ blocks of length $3$, and a second defect of **arbitrary** length $s_1 \ge 4$ (with **no**
requirement that $s_0 = 4$ or $s_1 = 4$, and **no** restriction to $[8/81, 1/2)$!).
Then:
1. The first defect plus $j_1$ blocks of $3$ and the start of the second defect $s_1 \ge 4$ locks:
   $$19 b_0 + 9 = 9 \cdot 2^{3 j_0 + 3} V_0, \qquad 19 b_{j_0 + 1} + 9 = 9 \cdot 2^{3 j_1 + 3} V_1, \qquad \gcd(V_0, 6) = \gcd(V_1, 6) = 1!$$
2. Dividing the transition equation by $72 = 8 \times 9$ yields the **Generalized Normalized Defect
   Recurrence valid for all $s_0 \ge 4$**:
   $$\boxed{2^{3 j_1 + s_0} V_1 + \big(3^{s_0 - 3} - 2^{s_0 - 3}\big) = 3^{3 j_0 + s_0} V_0, \qquad \gcd(V_r, 6) = 1!}$$
   When $s_0 = 4$, $3^1 - 2^1 = 1$, recovering the Dense-Core recurrence $2^{3j_1+4} V_1 + 1 = 3^{3j_0+4} V_0$!
   When $s_0 \ge 4$ is arbitrary, since $2^{3 j_1 + s_0} \ge 2^4 = 16$, reducing modulo $16$ still locks:
   $$3^{3 j_0 + s_0} V_0 \equiv 3^{s_0 - 3} - 2^{s_0 - 3} \pmod{16}!$$
3. **Well-Founded Quotient Descent for Arbitrary $s_r \ge 4$:**
   Whenever $3^{3 j_r + s_r} \le 2^{3 j_{r+1} + s_r}$ (in particular whenever $j_r \le j_{r+1}$ and
   $3^{3 j_r + s_r} \le 2^{3 j_{r+1} + s_r}$), since $3^{s_r - 3} - 2^{s_r - 3} \ge 1$ and $V_r, V_{r+1}$
   are odd, we have $V_{r+1} < V_r$, hence $V_{r+1} + 2 \le V_r$!

### 2.3 Lean 4 deliverables for Track 2 (Module: `GeneralizedDefectFactorizationAndAllRungDescent.lean`)

1. Prove `defectError_eq_neg_seventy_two_mul`:
   for all $s \ge 3$, $9 \cdot 2^s - 8 \cdot 3^{s-1} = -72 \cdot ((3^s / 27) - (2^s / 8))$
   (in $\mathbb{Z}$: $9 \cdot (2 : \mathbb{Z})^s - 8 \cdot (3 : \mathbb{Z})^{s-1} = -72 \cdot ((3 : \mathbb{Z})^{s-3} - (2 : \mathbb{Z})^{s-3})$).
2. Prove `three_pow_sub_two_pow_coprime_six`:
   for all $k \ge 1$, $(3^k - 2^k) \bmod 2 = 1$ and $(3^k - 2^k) \bmod 3 \ne 0$ ($\gcd(3^k - 2^k, 6) = 1$).
3. Prove the **Generalized Normalized Defect Recurrence (`general_s_ge_four_normalized_defect_recurrence`)**:
   $2^{3 j_1 + s_0} V_1 + (3^{s_0 - 3} - 2^{s_0 - 3}) = 3^{3 j_0 + s_0} V_0$ for arbitrary $s_0 \ge 4$.
4. Prove the **All-Rung Sparse-Defect Descent (`general_s_ge_four_sparse_defect_strict_descent`)**:
   whenever $s_r \ge 4$, $V_r \ge 1$ is odd, and $3^{3 j_r + s_r} \le 2^{3 j_{r+1} + s_r}$,
   $V_{r+1} + 2 \le V_r$, eliminating all infinite chains of $s_r \ge 4$ defects satisfying
   $3^{3 j_r + s_r} \le 2^{3 j_{r+1} + s_r}$ across **all rungs $s_r \ge 4$ simultaneously**!
5. Analyze the **Mixed $(s = 2,\, s \ge 6)$ Recovery Pair**:
   For $s_0 = 2$ followed by $s_1 \ge 6$ (`GlobalStepRateBounds.six_le_after_two_of_minSlack_pos`),
   compute the composite 2-block defect $E_{2, s_1} = 3^{s_1} E(2) + 4 E(s_1) = 12 \cdot 3^{s_1} - 288 (3^{s_1-3} - 2^{s_1-3}) = 36 \cdot 3^{s_1-3} + 288 \cdot 2^{s_1-3} = 36 \cdot (3^{s_1-3} + 8 \cdot 2^{s_1-3})$,
   whose 2-adic valuation is **locked at exact $v_2(36) = 2$** and whose 3-adic valuation is **locked at exact $v_3(36) = 2$** for every $s_1 \ge 6$!
   *(Note this remarkable cancellation: $12 \cdot 27 - 288 = 324 - 288 = +36 > 0$, so every $(2, s_1)$ recovery pair with $s_1 \ge 6$ has a strictly positive composite defect $+36(3^{s_1-3} + 2^{s_1})$ with constant valuation $(v_2, v_3) = (2, 2)$!)*

---

## Track 3: Coupled $(\Phi_{\text{def}},\, v_2(19 q_N + 9))$ Potential & Parity-Surplus Tradeoff (Target R2.1)

### 3.1 The exact sign and valuation table across all surviving block types

Combine Round 1's look-ahead-free deficit potential
$\Phi_{\text{def}}(\varepsilon, N) = (N + 3) - 3\,\text{oddParityCount}(\varepsilon, N) \ge 0$
with Track 2's defect factorization on a stabilized seed ($N \ge W$, $\eta_N = 0$):

| Block / Macro-Block Type | Step Length $\Delta N$ | Odd Steps $\Delta O$ | Deficit Change $\Delta \Phi_{\text{def}} = \Delta N - 3\Delta O$ | Invariant Transition on $I(q) = 19 q + 9$ | Valuation Lock / Effect |
| --- | --- | --- | --- | --- | --- |
| Pure period-3 block `100` ($s = 3$) | $3$ | $1$ | **$0$ (Stationary)** | $8 I(q') = 27 I(q)$ | **Strictly drains $v_2(I)$ by $-3$** (at most $\lfloor v_2(I)/3 \rfloor$ consecutive blocks) |
| Long block `10^(s-1)` ($s \ge 4$) | $s$ | $1$ | **$+(s - 3) \ge +1$ (Increases)** | $2^s I(q') = 3^s I(q) - 72(3^{s-3} - 2^{s-3})$ | **Locks $v_2(I(q)) = 3$** whenever $2^{s} \mid \text{LHS}$ and $s \ge 4$ |
| Short recovery pair $(2, s_1)$ ($s_0 = 2, s_1 \ge 6$) | $2 + s_1 \ge 8$ | $2$ | **$+(s_1 - 4) \ge +2$ (Increases!)** | $2^{s_1+2} I(q'') = 3^{s_1+2} I(q) + 36(3^{s_1-3} + 2^{s_1})$ | **Locks $v_2(I(q)) = 2$** and $v_3 = 2$ for all $s_1 \ge 6$! |

### 3.2 Two fundamental consequences of the table above

Look closely at the third row of the table above:
1. **Even an $s_0 = 2$ block cannot decrease $\Phi_{\text{def}}$ across a completed $(2, s_1)$ recovery pair!**
   - While the $s_0 = 2$ step (`10`) temporarily drops $\Phi_{\text{def}}$ by $2 - 3(1) = -1$, feasibility
     past the next block forces $s_1 \ge 6$ (`10100000...`), which increases $\Phi_{\text{def}}$ by
     $s_1 - 3 \ge +3$!
   - Thus across the mandatory 2-block recovery pair $(2, s_1)$, the net change in $\Phi_{\text{def}}$ is
     $$\Delta \Phi_{\text{def}}(2, s_1) = (2 + s_1) - 3(2) = s_1 - 4 \ge 6 - 4 = +2 > 0!$$
   - Consequently, **across all feasible macro-blocks ($s = 3$, $s \ge 4$, and $(2, s_1)$ with $s_1 \ge 6$),
     the macro-block deficit potential $\Phi_{\text{def}}$ is NEVER net-decreasing ($\Delta \Phi_{\text{def}} \ge 0$)**,
     and is stationary ($\Delta \Phi_{\text{def}} = 0$) **if and only if $s = 3$ (`100`)**!
2. **Simultaneous $v_2(I(q)) = 3$ vs. $v_2(I(q)) = 2$ Mod-8 Incompatibility Between $s \ge 4$ and $(2, s_1)$ Defects:**
   - Any $s \ge 4$ defect after $j$ blocks of $3$ requires $v_2(I(q_{\text{start}})) = 3j + 3 \equiv 0 \pmod 3$!
   - Any $(2, s_1)$ recovery pair ($s_1 \ge 6$) after $j$ blocks of $3$ has composite error
     $E_{2, s_1} = 36(3^{s_1-3} + 2^{s_1})$ with $v_2(E_{2, s_1}) = 2$, which requires
     $v_2(I(q_{\text{start}})) = 3j + 2 \equiv 2 \pmod 3$!
   - Because $3j + 3 \equiv 0 \not\equiv 2 \equiv 3j + 2 \pmod 3$, **no state $q_{\text{start}}$ can ever
     reach an $s \ge 4$ defect and a $(2, s_1)$ defect from the same mod-3 valuation class of $v_2(19 q + 9)$**!

### 3.3 Lean 4 deliverables for Track 3 (within `GeneralizedDefectFactorizationAndAllRungDescent.lean`)

1. Prove `recovery_pair_two_s1_deficitPotential_increase`:
   across any $(2, s_1)$ parity pattern with $s_1 \ge 6$, $\Phi_{\text{def}}(\varepsilon, N + 2 + s_1) = \Phi_{\text{def}}(\varepsilon, N) + (s_1 - 4) \ge \Phi_{\text{def}}(\varepsilon, N) + 2$.
2. Prove `composite_defect_two_s1_identity_and_valuation_two`:
   for any $s_1 \ge 4$, $3^{s_1} E(2) + 4 E(s_1) = 36 \cdot (3^{s_1 - 3} + 2^{s_1})$, whose odd part
   $3^{s_1 - 3} + 2^{s_1}$ is coprime to $6$, locking $v_2 = 2$ and $v_3 = 2$.
3. Prove `mod_three_valuation_incompatibility_s_ge_four_vs_two_pair`:
   for every $j_1, j_2 \in \mathbb{N}$, $3 j_1 + 3 \ne 3 j_2 + 2$, so the 2-adic valuation lock
   $v_2(19 q + 9) = 3 j_1 + 3$ (required before an $s \ge 4$ defect) and the lock
   $v_2(19 q + 9) = 3 j_2 + 2$ (required before a $(2, s_1)$ defect) are **mutually exclusive**.

---

## Track 4: Superlinear & Bispecial Return-Time Complexity Exclusions (Target R2.3)

### 4.1 Pushing beyond linear factor complexity $p(L) \le \kappa L + C_0$

In Round 1, we noted that `no_subcritical_log_threshold_dense_core` excludes linear complexity bounds
$p(L) \le \kappa L + C_0$. Why did the proof assume a linear bound? Only because it applied basic
Pigeonhole to `C(L)` windows of length $L$!
However, Track 1's **Global Right-Special Valuation Lock** on raw orbits gives us:
$$\text{orbit } a_0\ n_2 - \text{orbit } a_0\ n_1 = 2^m \cdot q_{\text{odd}} \ge 2^m$$
whenever two occurrences $n_1 < n_2$ of a length-$m$ factor diverge at step $m$!
Even more:
- What if a factor of length $m$ occurs at $2^k + 1$ positions $n_0 < n_1 < \dots < n_{2^k}$?
  By binary ultrametric pigeonhole on the $k$-bit top-part residue $(b_{n_i} / 2^m) \bmod 2^k$, at
  least two occurrences $n_i < n_j$ must collide modulo $2^{m + k}$, forcing:
  $$2^{m + k} \mid (b_{n_j} - b_{n_i}) \quad\Longrightarrow\quad 2^{m + k} \le b_{n_j} < 3^{n_j} (a_0 + 1) / 2^{n_j}!$$
- More directly, on any orbit of $0 < a_0 < 2^W$, at every horizon $H$, the orbit values
  $b_0 < b_1 < \dots < b_H$ satisfy $(p, q)$ growth $b_n < 2^{W + \lceil n \log_2(3/2) \rceil}$.
  Therefore, **all $(H + 1)$ prefixes at positions $0 \le n \le H$ must have pairwise distinct
  residues modulo $2^{m_{\max}}$ as soon as $2^{m_{\max}} > b_H$**!

### 4.2 Lean 4 deliverables for Track 4 (within `UniversalOrbitBijectionAndRightSpecialLock.lean`)

1. Prove `raw_orbit_repeated_parity_window_pq_cutoff`:
   For **any** integer seed $1 \le a_0 < 2^W$ (with **no** $[8/81, 1/2)$ or `ValidBlockChain` hypothesis!),
   if a length-$m$ parity factor repeats at $n_1 < n_2$ ($\forall j < m,\, \text{orbit } a_0\ (n_1+j) \bmod 2 = \text{orbit } a_0\ (n_2+j) \bmod 2$),
   then for every $(p, q)$ with $q \ge 1$ and $3^q \le 2^{p+q}$:
   $$q m < p n_2 + q W + p \qquad (\text{and } 17 m < 10 n_2 + 17 W + 10 \text{ at } (10, 17))!$$
   *(Wait: pause and appreciate what this theorem does! Previously, repetition cutoffs were proved either
   for `ValidBlockChain` block lengths $s(k)$ or inside the Dense Core $[8/81, 1/2)$. Using Track 1's
   `two_pow_mul_orbit_add_eq` and `orbit_strictMono_of_pos`, we get the **universal raw parity-stream
   repetition cutoff $q m < p n_2 + q W + p$ for EVERY positive integer $a_0 \ge 1$ under $T(x) = \lceil 3x/2 \rceil$,
   even without assuming `ValidCompanionForever`**!)*
2. Prove `raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds`:
   For **every** positive integer $a_0 \ge 1$ (whether or not $a_0$ has a Mahler companion!), the parity
   sequence $n \mapsto \text{orbit } a_0\ n \bmod 2$ of $T(x) = \lceil 3x/2 \rceil$ **cannot** have
   sub-critical liminf prefix-factor complexity $\kappa < \log 2 / \log(3/2) \approx 1.709511$!
   - **Why this is a major standalone theorem for rational-base number systems (Akiyama–Frougny–Sakarovitch 2008, Andrieu–Eliahou–Vivion 2025):**
     It proves unconditionally in Lean 4 that **every** positive integer's base-$3/2$ parity sequence
     has factor complexity $P(m) \ge (\frac{\log 2}{\log(3/2)} - o(1)) m$—establishing a universal
     deterministic complexity lower bound toward the Andrieu–Eliahou–Vivion rational-base normality
     conjecture for all $a_0 \ge 1$!
3. Prove the **Multi-Collision Ultrametric Boost (`raw_orbit_multi_collision_ultrametric_pq_cutoff`)**:
   If $2^k + 1$ positions $n_0 < n_1 < \dots < n_{2^k} \le H$ share the same length-$m$ parity factor,
   Pigeonhole on $(\text{orbit } a_0\ n_i / 2^m) \bmod 2^k$ forces a pair $n_i < n_j \le H$ agreeing
   modulo $2^{m + k}$ (hence sharing their length-$(m + k)$ parity prefix!), upgrading the cutoff to
   $q(m + k) < p H + q W + p$.

---

## Track 5: Base-6 Left-Boundary Causal-Cone Compression & Certified $B(N)$ Lifting

### 5.1 Connecting the base-6 left-zero boundary to `leastPositiveSurvivor`

In Round 1 ([BaseSixMultiplicationAutomaton.lean](./BaseSixMultiplicationAutomaton.lean)), we proved
that the base-6 configuration $d : \mathbb{Z} \to \mathbb{N}$ of a real number $\alpha \in [1, 6^m)$
satisfies $d(i) = 0$ for all $i \ge m$, and that after $n$ steps of $\Pi_{3/2, 6}$, the zero boundary
propagates to $i \ge m + n$ (`left_zero_boundary_mulThreeHalvesCA_iterate`).
Meanwhile, at position $i = -1$, the trace digit $(F^n d)_{-1}$ determines whether $\{(3/2)^n \alpha\} < 1/2$.

### 5.2 Lean 4 deliverables for Track 5 (within `BaseSixMultiplicationAutomaton.lean` or a dedicated extension)

1. **Exact Base-6 Integer-Part Carry Coupling:**
   Prove that for any natural number $a_0 < 6^m$, its base-6 configuration `natToBaseSixConfig a_0`
   satisfies `baseSixScaledNat (natToBaseSixConfig a_0) 0 m = a_0` and `natToBaseSixConfig a_0 i = 0`
   for all $i \ge m$ and $i < 0$.
2. **Certified Dyadic & Base-6 Horizon Lower Bounds on $B(N)$:**
   Extend `leastPositiveSurvivor_certified_bounds` ($B(4) \ge 4$, $B(12) \ge 53$, $B(29) \ge 4096$)
   by combining the shift-submultiplicative `signedMargin` pruning with `fastSeedSurvives` to certify
   how $B(N)$ jumps at $N = 29$ and characterize the surviving residue classes at $N = 29, 30$.

---

## Execution Order, Quality Gates & Stop Rules for Argon (Round 2)

| Step | Module to Create & Verify | Primary Theorems | Verification Gate |
| --- | --- | --- | --- |
| **Step 1** | `UniversalOrbitBijectionAndRightSpecialLock.lean` + `...Checks.lean` | `orbit_strictMono_of_pos`, `two_pow_mul_orbit_add_eq`, `orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow`, `right_special_orbit_exact_two_and_three_adic_lock`, `raw_orbit_repeated_parity_window_pq_cutoff`, `raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds` | `lake build` + `lake env lean -DwarningAsError=true`; `0` `sorry`s, standard axioms only. |
| **Step 2** | `GeneralizedDefectFactorizationAndAllRungDescent.lean` + `...Checks.lean` | `defectError_eq_neg_seventy_two_mul`, `three_pow_sub_two_pow_coprime_six`, `general_s_ge_four_normalized_defect_recurrence`, `general_s_ge_four_sparse_defect_strict_descent`, `recovery_pair_two_s1_deficitPotential_increase`, `composite_defect_two_s1_identity_and_valuation_two`, `mod_three_valuation_incompatibility_s_ge_four_vs_two_pair` | `lake build` + `lake env lean -DwarningAsError=true`; `0` `sorry`s, standard axioms only. |
| **Step 3** | Documentation, Paper & GitHub Push | Update `MAHLER_FORMALIZATION_PAPER.md`/`.tex`, `README.md`, `lakefile.toml`, and `RESEARCH_PLAN_ARGON_ROUND2_COMPLETION.md` with execution results | Full `lake build` across all targets and `git push origin HEAD`. |

### Explicit Stop & Honesty Rules
- **Do not claim Mahler's conjecture is solved unless `survivorKernel = ∅` or `∀ B, ∃ N, B ≤ leastPositiveSurvivor N` is proved with zero unproved hypotheses.**
- Keep every newly proved unconditional theorem (such as the universal $(2^m, 3^m)$ orbit bijection, the unconditional $1.709511$ parity-complexity lower bound for all $T_{3/2}$ orbits, and the universal $-72(3^{s-3}-2^{s-3})$ all-rung defect factorization) clearly distinguished from the remaining open step (ruling out bounded-run super-critical trajectories with $\Delta \Phi_{\text{def}} \ge 0$ where $s \ge 4$ blocks replenish $v_2(19 q_N + 9) = 3$).

---

# Part II — Fable's review of the Round 2 plan: verification, corrections, and Tracks 6–16

Date: 2026-11-01. Reviewer: Fable. Executor: Argon (Lean 4.19.0 / Mathlib v4.19.0).

This part does three things. **Section 6** audits every mathematical claim in
Tracks 1–5 above (all of them check out, with three corrections that matter for
formalization). **Sections 7–15** add new tracks, several from branches of
mathematics the project has not yet used (symbolic dynamics of β-shifts, 2-adic
dynamics in the style of Lagarias's Collatz conjugacy, S-unit equations,
lifting-the-exponent dynamics, combinatorics on words, logical complexity).
**Section 16** gives the revised execution order, quality gates, and an honest
statement of what would actually close the proof.

As in Part II of the original plan: every track lists **idea → exact object →
Lean deliverables → why it might work → expected obstruction → negative result
to bank → Mathlib notes**. Negative and limitative results remain first-class
deliverables; a machine-checked "this method cannot reach" is progress.

## 6. Verification of Tracks 1–5 (what is correct, what must be fixed)

All five tracks were checked by hand against the exact recurrences in
[ExactSeedResidueTreeAndStabilization.lean](./ExactSeedResidueTreeAndStabilization.lean),
[SparseDefectCocycleAndValuationLock.lean](./SparseDefectCocycleAndValuationLock.lean), and
[TransferOperatorJSRAndCarryFourier.lean](./TransferOperatorJSRAndCarryFourier.lean).

| Track | Verdict | Notes for Argon |
| --- | --- | --- |
| **1** (universal $(2^m,3^m)$ bijection, right-special odd-quotient lock) | **Correct.** | The forward direction (equal parities for $j<m$ ⟹ equal carries exactly ⟹ $2^m \mid$ and $3^m \mid$ with a common quotient) is elementary and does **not** need the injectivity theorem; only the converse "$3^m$-agreement ⟹ parity agreement" uses `wordCarry_mod_three_pow_eq_iff_parity_eq`. Oddness of the common quotient is exactly "disagreement at step $m$ ⟺ not congruent mod $2^{m+1}$". |
| **2** (factorization $E(s) = -72(3^{s-3}-2^{s-3})$, all-rung descent) | **Correct, with one indexing correction.** | $\gcd(3^k-2^k,6)=1$ for all $k\ge1$ is right, so $v_2(E(s))=3$ and $v_3(E(s))=2$ for every $s\ge4$. **But** the 3-adic lock $U_r = 9V_r$ is derived from the recurrence *into* $U_r$ (reduce $2^{c}U_{r} = 3^{a}U_{r-1} - 9D$ modulo $27$), so it holds only for boundaries that **follow at least one defect** ($r\ge1$). For the first epoch only oddness of $U_0$ is known; use the $U$-form $2^{3j_1+s_0}U_1 = 3^{3j_0+s_0}U_0 - 9D_{s_0}$ there. The same remark applies to the $(2,s_1)$ composite: reducing $2^{s_1+2}I(b'') = 3^{s_1+2}I(b) + 36(3^{s_1-3}+2^{s_1})$ modulo 9 gives $9 \mid I(b'')$, so **every boundary that follows a defect of either type has $9 \mid I$**. |
| **3** (coupled potential table, $(2,s_1)$ pair) | **Correct table; wrong emphasis.** | $\Delta\Phi_{\text{def}} \ge 0$ on every feasible macro-block is **consistent with survival** (it is the statement "$s\ge3$ on average", already known) and is **not** a contradiction mechanism. The genuinely new content is the exact trichotomy law of Section 7 below, which turns the table into a *symbolic coding of the whole block sequence by 2-adic valuations*. Keep the $(2,s_1)$ composite identity $3^{s_1}E(2)+4E(s_1) = 36(3^{s_1-3}+2^{s_1})$ (verified; the odd part is coprime to 6 for $s_1\ge4$). |
| **4** (unconditional $P(10k+W)\ge 17k+1$) | **Correct and clean.** | $b_0<\dots<b_H<2^m$ are distinct integers, hence distinct residues mod $2^m$, hence distinct length-$m$ parity prefixes (bijection). With $3^{17}<2^{27}$: $b_{17k}+1 \le (3/2)^{17k}2^W < 2^{10k+W}$. No Mahler hypothesis is used: this holds for the orbit of **every** $a_0\ge1$. |
| **5** (base-6 lifting) | Fine as stated. | Lower priority; see Section 15 for the logical structure that makes certified $B(N)$ floors meaningful. |

Three further corrections to carry into documentation:

1. **Entropy of the admissible language.** The admissible parity language on
   $[0,1/2)$ has **positive** topological entropy — in fact exactly $\log(3/2)$
   (Section 8). Already the sub-language "all blocks $s\ge3$" (ceiling-saturated,
   always feasible) has growth rate $\lambda=1.4656$ (root of $x^3=x^2+1$). The
   README's remark that surviving cylinder counts follow Mahler's binary partition
   recursion $B(d)=B(d-1)+B(\lfloor d/2\rfloor)$ concerns the **$(2/7,5/7)$
   window**; it must not be applied to the number $|G_N|$ of admissible words of
   length $N$ for $[0,1/2)$, which is $\asymp (3/2)^N$.
2. **Round 1's post-`101` lock is under-stated.** `signedMargin_post_101_five_zeros_lock`
   proves zeros at positions $3,4,5$ only. The margin recurrence gives **five**:
   after `101`, $D_3=1$ and $D_n\le3^{n-3}$, while an odd step at $n$ needs
   $3D_n>2^{n+1}$; this fails for $n=3,4,5,6,7$ ($3\cdot81=243<256$) and first
   succeeds at $n=8$ ($729>512$). Strengthen the theorem to positions $3$–$7$. This
   matches the kneading sequence $K = 1\,0\,1\,0\,0\,0\,0\,0\,1\dots$ of Section 8.
3. **Terminology.** "Dense Core" results assume fractional parts in $[8/81,1/2)$;
   Section 8's β-shift frame covers all of $[0,1/2)$ (including $s=2$ blocks and
   arbitrarily long zero runs) and should be the default frame for Round 2.

## 7. The mod-3 valuation trichotomy: exact symbolic coding of a survivor's block sequence

**Idea.** One identity decides, at every odd block boundary, both the length of
the coming run of `100` blocks and the *type* of the block that ends it.

**Exact object.** For an odd integer $b$ put $I(b)=19b+9$ and $s=v_2(3b+1)$
(the block length starting at $b$). Then
$$3\,I(b) \;=\; 19\,(3b+1) + 8 .$$
Since $v_2(8)=3$ and $v_2(19(3b+1))=s$:
$$v_2(I(b)) = \begin{cases} s & s\in\{1,2\},\\ \ge 4 & s = 3,\\ 3 & s\ge 4.\end{cases}$$

**Consequences (all unconditional, all elementary).**

1. **Death class.** $s=1$ is the forbidden word `11`. Hence along a surviving
   orbit, at every odd boundary, $v_2(I(b)) \not\equiv 1 \pmod 3$: if
   $v_2(I(b)) = 3j+1$ with $j\ge1$, then after $j$ blocks of length 3 (each divides
   $I$ by $2^3$ exactly: $8I(b')=27I(b)$) the valuation is $1$, forcing $s=1$ and death.
2. **Run length and exit type are read off from one valuation.**
   $v_2(I(b)) = 3j+2$ ⟹ exactly $j$ blocks of length 3, then a block of length $2$;
   $v_2(I(b)) = 3j+3$ ⟹ exactly $j$ blocks of length 3, then a block of length $\ge4$.
3. **The whole block-length sequence of a survivor is the sequence of valuations
   $\nu_r = v_2(I(b_r))$ at the boundaries that follow each defect**, together with
   the defect lengths $s_r$ themselves (Section 9 shows the $s_r$ are also valuations).

This subsumes the project's first-defect lock $v_2(19a_0+9)=3j_0+3$ and the mod-8
lock, and it is the right replacement for Track 3's table.

**Lean deliverables (module `ValuationTrichotomyAndEpochCoding.lean`).**
- `three_mul_affInv_eq_nineteen_mul_add_eight : 3 * (19*b+9) = 19*(3*b+1) + 8`.
- `two_adic_valuation_affInv_trichotomy`: the three-case statement above, phrased
  with `padicValNat 2` or with explicit `2^k ∣ · ∧ ¬ 2^(k+1) ∣ ·`.
- `survivor_affInv_valuation_not_one_mod_three`: for a `ValidBlockChain` (or for
  `ValidCompanionForever`), at every odd boundary $v_2(19b+9) \bmod 3 \ne 1$.
- `run_length_and_exit_type_of_valuation`: the two implications in (2), proved by
  induction on $j$ using `8 * (19*b'+9) = 27 * (19*b+9)` for $s=3$ blocks.

**Mathlib notes.** `padicValNat`, `Nat.Prime.two`, and the existing
`stabilized_seed_100_two_adic_valuation_drop` suffice; everything is finite
arithmetic.

## 8. The admissible parity language is the β-shift for β = 3/2 (organizing frame for Round 2)

**Idea.** Put $x_n := 2\theta_n$ where $\theta_n=\{(3/2)^n\alpha\}\in[0,1/2)$ is the
fractional part of a hypothetical $Z$-number. Then $x_n\in[0,1)$ and, because
$g_n$ is odd exactly when $\theta_n\ge1/3$ (project: `odd_step_floor_exceeds_half_and_forces_ceil`),
$$x_{n+1} \;=\; \tfrac32 x_n - \lfloor \tfrac32 x_n\rfloor \;=\; T_\beta(x_n),\qquad
e_n \;=\; g_n \bmod 2 \;=\; \lfloor \tfrac32 x_n \rfloor, \qquad \beta=\tfrac32 .$$
So **the fractional-part dynamics of a $Z$-number is the β-transformation with
β = 3/2, and the parity word of the $Z$-number is exactly the greedy β-expansion of
$x_0 = 2\theta_0$.** Consequently the set $\mathcal W$ of archimedean-admissible
parity words is the β-shift $S_{3/2}$. (Dead End 6 already observed that a sofic
Parry presentation is impossible because $3/2$ is not an algebraic integer; this
section completes the dictionary and extracts the quantitative consequences.)

**Exact dictionary.**

| β-shift notion ($\beta=3/2$, digits $\{0,1\}$) | Mahler/project notion |
| --- | --- |
| greedy expansion $x_0=\sum_{k\ge0} e_k\beta^{-(k+1)}$ | Mahler's companion series $\theta_0=\sum e_k (2/3)^{k+1}/2$ (`InfiniteSeries.lean`) |
| $T_\beta$-orbit $x_n$ | $2\times$ fractional tail (`fractionalTail`) |
| kneading sequence $d_\beta(1) = 1\,0\,1\,0\,0\,0\,0\,0\,1\,0\,0\,1\,0\,0\,1\,0\,1\,0^9\,1\,0^6\,1\dots$ | block lengths $(2,6,3,3,2,10,7,\dots)$ = the project's recovery cascade in `GlobalStepRateBounds`/`MinSlackDynamicalSystem` |
| Parry criterion: $w\in S_\beta$ iff $\sigma^k w \le_{\text{lex}} d_\beta(1)\ \forall k$ | the FLP forbidden-word hierarchy `11`, `10101`, `101001`, `1010001`, `10100001`, … (each = a prefix of $K$ with a $0$ flipped to $1$) |
| $d_\beta(1)$ not eventually periodic ⟺ β not a Parry number | $3/2$ is not an algebraic integer ⟹ $S_{3/2}$ is **not sofic** (recovers Kopra's Theorem 3.18 and Dead End 6) |
| $h_{\text{top}}(S_\beta)=\log\beta$ | $|G_N| \asymp (3/2)^N$ admissible words of length $N$ (= surviving residues mod $2^N$) |
| periodic points $x = 2^P m/(3^P-2^P)$ | periodic parity words; 2-adic seed $-\big(1+2^{s(0)}R_0/(3^P-2^P)\big)/3<0$ (`periodic_macro_block_seed_divisibility`) |
| Parry (ACIM) measure, digit-1 frequency $\approx 0.21$ | "typical" admissible words have odd-step density ≈ 0.21; hard bound for every survivor is $\le 1/3$ (`GlobalStepRateBounds`) |

**Lean deliverables (module `BetaShiftThreeHalvesDictionary.lean`).**
1. `betaMap : ℝ → ℝ := fun x => 3/2*x - ⌊3/2*x⌋` on $[0,1)$ and
   `fract_dynamics_conj_betaMap`: for a valid companion, $2\,\mathrm{fract}((3/2)^{n+1}\alpha) = \text{betaMap}(2\,\mathrm{fract}((3/2)^n\alpha))$ and $\text{orbit } a_0\ n \bmod 2 = \lfloor \tfrac32 \cdot 2\,\mathrm{fract}((3/2)^n\alpha)\rfloor$.
2. `kneading_prefix_27`: the first 27 digits of $d_{3/2}(1)$ computed exactly over
   $\mathbb Q$ (`norm_num`), and `kneading_blocks_2_6_3_3_2_10_7` identifying them
   with the project's cascade.
3. `parry_forbidden_prefixes`: `11`, `10101`, `101001`, `1010001`, `10100001` are
   not factors of any admissible word (derive each from `signedMargin` as in
   Section 6, item 2); conversely `101000001` is admissible (margin stays positive).
4. **Counting.** `admissible_word_count_ge_three_halves_pow`:
   $|G_N| \ge (3/2)^N$. Proof: every $\theta_0\in[0,1/2)$ lies in the companion
   interval (`validCompanionUpTo_add_offset_iff_mem_ratInterval`) of the residue
   determined by its own itinerary, those intervals have length $\le \frac12(2/3)^N$,
   and they cover $[0,1/2)$. Optional upper bound $|G_N|\le 3(3/2)^N$ via Parry.
5. **Exact survivor count below the bit length.** For $N\le W$,
   `survivor_count_eq_admissible_times_two_pow`: $\#\{a<2^W : \text{survivesSteps } a\ N\} = |G_N|\cdot 2^{W-N}$
   (survival to depth $N$ depends only on $a \bmod 2^N$ — `residue_class_feasibility_iff_seedResidue`).
   This makes the heuristic "$2^W(3/4)^N$ survivors" an exact statement up to the
   factor $|G_N|/(3/2)^N\in[1,3]$ for $N\le W$, and isolates the conjecture as the
   statement $G_N\cap[1,2^W)=\emptyset$ for $N\ge N(W)$.
6. **Complexity threshold (conditional reduction).**
   `not_z_number_of_factor_complexity_exceeds_admissible_count`: if some length-$m$
   factor of the parity word of $a_0$ is not admissible — equivalently if
   $P_{a_0}(m) > |G_m|$ — then $a_0$ is not a $Z$-floor. With $|G_m|\le 3(3/2)^m$
   this reads: $P_{a_0}(m) > 3(3/2)^m$ excludes $a_0$. Compare Track 4's
   unconditional $P(m)\ge1.709m$: the gap between linear and exponential complexity
   **is** the conjecture.

**Why it matters.** Every archimedean fact about survivors (`11`-exclusion, the
cascade, the $3K\le T(K)+1$ step-rate theorem, the $8/57$ catapult, …) is a
statement about $S_{3/2}$ and can be proved uniformly from the Parry criterion.
Round 2 should state archimedean lemmas in β-shift language and reserve the
2-adic machinery for the integer-seed constraint.

**Expected obstruction / negative result to bank.** $S_{3/2}$ is not sofic (so
no finite automaton recognizes admissibility) and has positive entropy (so no
counting/measure argument on words alone excludes integer seeds). Bank both as
theorems: `betaShift_three_halves_not_sofic` (via non-periodicity of $d_\beta(1)$,
which follows from $3/2\notin\overline{\mathbb Z}$) and `admissible_word_count_ge_three_halves_pow`.

**Mathlib notes.** Only real arithmetic and `Int.floor`/`Int.fract`; no β-shift
library exists, so define the two needed objects directly. Keep endpoint
conventions (strict upper endpoint $1/2$, the dyadic-endpoint alternative in
`EndpointCompactnessAndBalancedExclusion.lean`) explicit.

## 9. The two shifts and the real-to-2-adic conjugacy $h$ (Lagarias-style reformulation)

**Idea.** The project's parity bijection `orbit_parity_eq_upto_iff_mod_two_pow`
says the map $\Phi:\mathbb Z_2\to\{0,1\}^{\mathbb N}$, $a\mapsto (T^n(a)\bmod2)_n$, is a
homeomorphism (here $T(x)=(3x+(x\bmod2))/2$ extends continuously to $\mathbb Z_2$).
Composing with the itinerary map of Section 8 gives
$$h := \Phi^{-1}\circ\mathrm{itin}_F:\ [0,1/2)\longrightarrow \mathcal A := \Phi^{-1}(S_{3/2})\subset\mathbb Z_2 ,$$
and **Mahler's conjecture ⟺ $h([0,1/2))\cap\mathbb N_{\ge1}=\emptyset$.** This is
the exact analogue of the Bernstein–Lagarias conjugacy for $3x+1$: the real
dynamics ($T_\beta$) and the 2-adic dynamics ($T$ on $\mathbb Z_2$, conjugate to the
**full** shift) are both coded by $\{0,1\}^{\mathbb N}$, and the conjecture says the
full-shift coding of every positive integer leaves the β-shift.

**Exact facts to formalize (finite-level versions; no $\mathbb Z_2$ needed).**
- `seed_of_itinerary_mod_two_pow`: for $\theta_0\in[0,1/2)$ and $N$, the least residue
  $h_N(\theta_0) := \text{seedResidue}(\mathrm{itin}(\theta_0))\ N$; cylinder-wise
  2-adic Hölder bound: if $\theta,\theta'$ share their first $N$ itinerary digits then
  $h_N(\theta)=h_N(\theta')$, and depth-$N$ cylinders have length $\le\frac12(2/3)^N$
  (exponent $\log2/\log(3/2)=1.709$).
- `periodic_itinerary_seed_negative`: eventually periodic admissible word ⟹ the
  2-adic seed is the rational $-\big(1+2^{s(0)}R_0/(3^D-2^D)\big)/3<0$ (restates
  `periodic_macro_block_seed_divisibility` as a **sign obstruction**: $h$ sends
  $T_\beta$-periodic points to negative rationals, so no positive integer has a
  periodic parity word).
- `haar_measure_of_survivor_set_zero` (optional): $\mu(\mathcal A)\le 3(3/4)^N\to0$;
  2-adic dimension $\log_2(3/2)=0.585$. Bank as the limitative statement
  "$\mathcal A$ is a null set of dimension $0.585$ while $\mathbb N$ is dense in
  $\mathbb Z_2$: no measure/dimension argument in $\mathbb Z_2$ can finish."

**Why it might work.** It separates cleanly the two ingredients and shows the
*only* coupling is the requirement that the 2-adic seed have finitely many 1-bits
($\eta_n=0$ for $n\ge W$). Every route to a proof must use that finiteness.

**Mathlib notes.** Finite-level statements avoid `PadicInt`. If a $\mathbb Z_2$
version is wanted, `PadicInt` and `ZMod`-limits exist, but keep it optional.

## 10. The lifting-the-exponent "coincidence law": every block and run length is a 2-adic coincidence

**Idea.** Combine Track 2's factorization with 2-adic LTE
($v_2(3^n-1)=v_2(n)+2$ for even $n$, $=1$ for odd $n$; `TwoAdicLiftingExponent.lean`)
to write the *entire* epoch dynamics as 2-adic valuations of integer–target
differences.

**Exact object.** Epoch $r$: a run of $j_r$ blocks `100`, then a defect
$s_r\ge4$; length $a_r=3j_r+s_r$; odd part $V_r$ with $I(b_r)=72\cdot2^{3j_r}V_r$
(valid for $r\ge1$, Section 6). Let $D_s := 3^{s-3}-2^{s-3}$. Then, exactly:
$$\nu_{r+1} := v_2(I(b_{r+1})) \;=\; 3 + v_2\big(3^{a_r}V_r - D_{s_r}\big) - s_r, \qquad
V_{r+1} \;=\; \frac{3^{a_r}V_r - D_{s_r}}{2^{\,\nu_{r+1}+s_r-3}},$$
$$s_{r+1} \;=\; 3 + v_2\big(3^{\,3(j_{r+1}+1)}\,V_{r+1} - 1\big)$$
(the last from $3b''+1 = (216\cdot3^{3j_{r+1}}V_{r+1}-8)/19$). By LTE, whenever the
mod-8 class permits, $v_2(3^aV-D) = 2+v_2(a-a^*)$ and
$v_2(3^mV'-1)=2+v_2(m-m^*)$ for 2-adic integers $a^*,m^*$ ("2-adic logarithms"
of $D/V$ and $1/V'$ base 3); otherwise the valuation is $\le2$. The mod-8
condition is exactly the project's lock $U\bmod8\in\{1,3\}$.

**Consequences.**
- Run lengths and defect lengths are **coincidences** $v_2(\text{integer}-\text{2-adic target})$
  where the integer is a *time quantity* ($a_r$, or $3(j_{r+1}+1)$) and the target
  depends on the *odd part* $V$. Long runs/defects require the current epoch length
  to agree with a 2-adic logarithm to many bits.
- Pure periodicity ⟺ all targets hit exactly ⟺ $V$ equals a 2-adic rational
  fixed point ($1/65$ for `0001`$^\infty$, $-9/19$ for `100`$^\infty$) — the
  Round 1 ghost self-loops in this language.

**Lean deliverables (module `TwoAdicCoincidenceLaw.lean`).**
`next_valuation_eq_three_add_v2_sub_s`, `next_defect_eq_three_add_v2`, both by
direct algebra from `rungAffInv_general_defect_step_identity`; `v2_three_pow_mul_sub_eq_two_add_v2_of_mod_eight`
(LTE form, stated with a natural-number witness $a'$ with $3^{a'}V\equiv D \pmod{2^K}$
instead of a 2-adic logarithm); `mod_eight_lock_of_next_valuation_ge_three`.

**Negative result to bank (method-cannot-reach).** Yu's $p$-adic Baker theorem
bounds $v_2(3^aV-D)\le C\,\log V\cdot\log a$. Since $\log_2V_r\approx W+0.585\,n_r-3j_r$
can be linear in time, this is **weaker** than the trivial archimedean budget
$3j+3\le\log_2 I(b)\le W+0.585n+5$ as soon as $\log V\gtrsim n/\log n$. Formalize
the comparison inequality (both sides are explicit) so nobody re-attempts
"Baker bounds the run lengths" without a new idea.

## 11. Bounded odd parts are impossible (new infinite-family exclusion, conditional on S-unit finiteness)

**Idea.** The epoch transition is a four-term $\{2,3\}$-unit equation with bounded
coefficients when the odd parts are bounded. S-unit finiteness then forces a
finite state space, hence eventual periodicity, hence contradiction.

**Exact object.** With $c_r := \nu_{r+1}+s_r-3 = 3j_{r+1}+s_r$ (Section 10),
$$V_r\,3^{a_r} - V_{r+1}\,2^{c_r} \;=\; 3^{s_r-3} - 2^{s_r-3}. \tag{$\ast$}$$
For a $(2,s_1)$ epoch the same shape holds with right-hand side
$36(3^{s_1-3}+2^{s_1})/\,(\text{power of }2\text{ absorbed into }c)$.

**Theorem (conditional).** *Assume* the S-unit theorem (Evertse; van der Poorten–Schlickewei):
for fixed nonzero rationals $c_1,\dots,c_4$ the equation $\sum c_ix_i=0$ has finitely
many solutions in $\{2,3\}$-units $x_i$ with no vanishing subsum. *Then* no positive
integer orbit has $V_r\le M$ for all $r\ge1$ (any fixed $M$).
*Proof sketch.* For each of the finitely many pairs $(V,V')\in[1,M]^2$, $(\ast)$ is
$V\cdot3^a - V'\cdot2^c - 3^{s-3} + 2^{s-3} = 0$. Vanishing subsums are impossible:
$V3^a=V'2^c$ (coprime to 6), $V3^a=3^{s-3}$ (needs $V=1$, $a=s-3$, but $a\ge s$),
$V'2^c=2^{s-3}$ (needs $c=s-3$, but $c\ge s$), $3^{s-3}=2^{s-3}$ (only $s=3$, excluded).
Hence $(a_r,c_r,s_r)$ take finitely many values, so the state $(j_r,s_r,V_r)$ is
eventually periodic, so the parity word is eventually periodic, contradicting the
periodic exclusion (`periodic_macro_block_seed_divisibility` / Section 9 sign obstruction).

**Unconditional skeleton to formalize now.**
- `bounded_odd_part_iff_runs_saturate_budget`: $V_r\le M$ for all $r$ ⟺
  $3j_r \ge \log_2(19b_r+9) - \log_2(72M)$, i.e. the runs sit within $O(\log M)$ of
  the archimedean maximum $0.585\,n_r+W$. (Bounded odd parts are exactly the
  "maximally 2-adically coincident" trajectories — the indifference surface of Section 18.)
- `bounded_epoch_data_implies_eventually_periodic`: bounded $(j_r,s_r,V_r)$ ⟹
  eventually periodic block sequence (pigeonhole on a finite state set).
- `no_bounded_odd_part_orbit_of_sunit_finiteness`: the conditional theorem with the
  S-unit statement as an explicit hypothesis (Section 21 type 5 deliverable).

**Why it might work beyond the conditional statement.** For fixed bounded $(V,V')$,
$(\ast)$ is a *three-term* Pillai-type equation $V3^a-V'2^c=D$ whenever $s$ is also
bounded, where Baker's method is effective. A fully effective version
("no orbit with $V_r\le M$ and $s_r\le S$") is a realistic Round 2 target using the
project's existing `BakerMatveevFramework.lean` interfaces.

**Expected obstruction.** $V_r$ unbounded is the generic case; this track excludes
an infinite family on the critical line but not the general orbit.

**Mathlib notes.** No S-unit theory in Mathlib; keep it as a named hypothesis.
The non-degeneracy case analysis is pure `omega`/`decide` arithmetic.

## 12. Backward 3-adic sieve: two-sided digit confinement and why it adds nothing beyond words

**Idea.** Track 1 shows $b_K\bmod3^m$ determines the **past** $m$ parities and
$b_K\bmod2^m$ the **future** $m$ parities. Forbidden words therefore become
forbidden residue classes.

**Exact facts.**
- $b_K\not\equiv1\pmod3$ for $K\ge1$ (no predecessor; `DeadEnds` item 7).
- From $4b_K \equiv 3e_{K-2}+2e_{K-1}\pmod 9$ and `11` forbidden: **$b_K\not\equiv 8\pmod 9$ for $K\ge2$**.
- In general $b_K \bmod 3^\ell$ lies in $|G_\ell|$ classes, $b_K\bmod2^\ell$ in
  $|G_\ell|$ classes, and $b_K\bmod6^\ell$ in $|G_{2\ell}|$ classes (the last
  $\ell$ base-6 digits of $b_K$ — Kopra's trace picture).

**Lean deliverables.** `orbit_mod_three_ne_one`, `orbit_mod_nine_ne_eight_of_survives`,
`orbit_mod_six_pow_confinement_iff_window_admissible`.

**Negative result to bank.** The mod-$6^\ell$ confinement is **equivalent** to
admissibility of the surrounding length-$2\ell$ parity window (prove the
biconditional). Hence residue sieving modulo powers of 2, 3, or 6 carries no
information beyond the word constraints: formal justification for not pursuing
"sieve" approaches further.

## 13. Integer and rational $\alpha$; the subsum-interval obstruction; the minimal floor

**Exact statements.**
- `not_z_number_of_integer`: an integer $\alpha=a_0$ is never a $Z$-number ($\xi=0$
  would force $g_n=a_0(3/2)^n\in\mathbb N$ for all $n$). (The 2024 arXiv claim for the
  integer case was withdrawn; this trivial statement is all that is true there.)
- `z_number_iff_floor_two_mul_even`: $\alpha$ is a $Z$-number ⟺
  $\lfloor 2(3/2)^n\alpha\rfloor$ is even for all $n\ge0$ ⟺ the binary digit of
  $3^n\alpha$ in position $n-1$ is $0$ for all $n\ge1$ (the "diagonal" of the base-2
  space-time diagram of $\times3$; Lagarias–Erdős family of two-base digit problems).
- `minimal_z_floor_not_dvd_three`: if $Z$-numbers exist and $a^*$ is the least
  integer part, then $3\nmid a^*$ (else $m=2a^*/3$ and $\beta=2\alpha/3$ with
  $\{\beta\}=2\xi/3<1/3$ is a $Z$-number with smaller floor).
- **Rational $\alpha$ (open).** $\alpha=p/q$ is a $Z$-number ⟺
  $\lfloor 3^np/(2^{n-1}q)\rfloor$ is even for all $n\ge1$. If the parity word is
  eventually periodic the seed is negative (Section 9) — excluded. Rationality of
  $\theta_0=\sum e_k(2/3)^{k+1}/2$ does **not** force periodicity: Schmidt's theorem
  (β-expansions of all rationals eventually periodic only for Pisot/Salem β; $3/2$ is
  neither) and, elementarily, the subsum set $\{\sum e_k r^k\}$ with $r=2/3$ is a full
  interval even under the no-`11` constraint ($K=rK\cup(1+r^2K)$ is an interval iff
  $r\ge(\sqrt5-1)/2\approx0.618$).

**Lean deliverables.** The four items above; for the interval statement, prove
`no_eleven_subsum_set_is_interval` over $\mathbb R$ by the standard
"ratio ≥ golden" argument (bank as the limitative result "value-rationality
cannot exclude aperiodic admissible words").

## 14. Rauzy graphs, right-special abundance, and multi-occurrence ultrametrics (combinatorics on words)

**Exact facts.** $P(M)-1=\sum_{m<M}RS(m)$ (number of right-special factors), so
Track 4 gives on average $\ge1.709$ right-special factors per length, each
occurrence pair of which yields the exact lock $2^m\,\|\,(b_{n_2}-b_{n_1})$,
$3^m\,\|\,(b_{n_2+m}-b_{n_1+m})$ with a common odd quotient (Track 1). Three
occurrences of one factor force a pair agreeing mod $2^{m+1}$ (Track 1.3(5));
$2^k+1$ occurrences force a pair agreeing mod $2^{m+k}$ (Track 4.2(3)).

**Lean deliverables.** `prefix_factor_count_sub_one_eq_sum_right_special`,
`average_right_special_ge`, and the multi-occurrence pigeonhole already listed in
Track 4.

**Negative result to bank.** Carry out the self-consistency count: with $P(m)\approx
1.709m$ the required positions $n_2\ge1.709(m-W)$ are exactly available. Record
"Rauzy counting alone yields no contradiction" as a theorem-level remark.

## 15. Logical structure and certificates: what a proof must look like

- "No $Z$-number with integer part $<X$" is a **$\Sigma_1$** statement with a finite
  certificate: a depth $N$ with $B(N)>X$ (compactness of the depth-$N$ cylinders;
  `leastPositiveSurvivor`). `positive_survivor_step29_ge_4096` is such a certificate
  for $X=4096$.
- The full conjecture "$\forall X\,\exists N: B(N)>X$" is **$\Pi_2$**. A proof must
  therefore supply an explicit unbounded computable $f$ with $B(N)\ge f(N)$, or an
  equivalent well-founded rank (Section 19 completeness).
- Consequently **no finite computation can prove the conjecture**, but every
  certified $B(N)$ floor is genuine progress and tests candidate ranks. Track 5's
  base-6 lifting should be run through a verified checker (the shift-submultiplicative
  `signedMargin` pruning is sound) to extend $B(29)\ge4096$ and to record the
  surviving residue classes at $N=29,30$ as data for Sections 10–11.

## 16. Revised execution order, gates, and the honest closing statement

| Step | Module | Headline theorems | Gate |
| --- | --- | --- | --- |
| 0 | fix `ParitySurplusPotentialsAndSafetyGame.lean` | extend the post-`101` lock to positions 3–7 (Section 6) | `lake build` + `warningAsError` |
| 1 | `ValuationTrichotomyAndEpochCoding.lean` | trichotomy, death class, run/exit coding (Section 7) | all `#print axioms` standard |
| 2 | `BetaShiftThreeHalvesDictionary.lean` | β-map conjugacy, kneading prefix = cascade, Parry forbidden prefixes, $\lvert G_N\rvert\ge(3/2)^N$, exact survivor count for $N\le W$, complexity-threshold reduction (Section 8) | numeric checks by `norm_num`/`decide` |
| 3 | `UniversalOrbitBijectionAndRightSpecialLock.lean` | Tracks 1 and 4 as specified above | — |
| 4 | `TwoAdicCoincidenceLaw.lean` | Section 10 laws, mod-8 lock, Baker comparison remark | — |
| 5 | `GeneralizedDefectFactorizationAndAllRungDescent.lean` | Track 2 with the $r\ge1$ indexing fix; $(2,s_1)$ composite; all-rung descent | — |
| 6 | `BoundedOddPartExclusion.lean` | Section 11 skeleton + conditional theorem; attempt the effective bounded-$(V,s)$ version | S-unit hypothesis explicit |
| 7 | `ThreeAdicSieveAndRationalCases.lean` | Sections 12–14 | — |
| 8 | docs/paper/README, push | reconcile Markdown/TeX; record negatives | full `lake build` |

**Stop rules.** One main attempt (Step 6's effective version) and one small lemma at
a time; after two materially different failures, bank the negative result and move
on. Do not spend Round 2 on more special-sequence exclusions.

**What would close the proof.** In the language of Sections 8–10: show that for
every positive integer the sequence of 2-adic coincidences $v_2(a_r-a_r^*)$,
$v_2(3(j_{r+1}+1)-m_{r+1}^*)$ cannot continue forever while the odd parts $V_r$
remain positive integers — equivalently, that the full-shift coding of $a_0$ exits
the β-shift $S_{3/2}$. Section 11 settles this on the critical line (bounded $V_r$)
conditionally; the unbounded-$V_r$ regime is the open problem, and nothing in
Rounds 1–2 claims otherwise.

---

# Part III — Round 2 execution report & formalized Lean 4 deliverables

Date executed: 2026-11-01 (`158` `.lean` files total, `0` `sorry`s, `0` warnings)

## 17. Summary of Round 2 Lean 4 formalization (`Steps 0–8`)

Every track in Part I (Tracks 1–5) and Part II (Sections 6–16) has been formalized in Lean 4.19.0
and verified with `warningAsError=true` and standard axioms `[propext, Classical.choice, Quot.sound]`:

1. **Step 0 — Strengthening the Post-`101` Five-Zero Lock (`ParitySurplusPotentialsAndSafetyGame.lean`):**
   - Strengthened `signedMargin_post_101_five_zeros_lock` to prove that after `(1, 0, 1)`, feasibility
     (`0 < signedMargin ε N`) forces all **five** subsequent parities `ε 3, ε 4, ε 5, ε 6, ε 7` to vanish
     (ruling out `1011`, `10101`, `101001`, `1010001`, and `10100001`), while `101000001` (`ε 8 = 1`)
     achieves `signedMargin ε 8 = 243` and `signedMargin ε 9 = 217 > 0`.

2. **Steps 1 & 3 — Universal $(2^m, 3^m)$ Orbit Bijection, Global Right-Special Lock, Unconditional
   $1.709511$ Parity Complexity for All $a_0 \ge 1$ & Mod-3 Valuation Trichotomy
   ([UniversalOrbitBijectionAndRightSpecialLock.lean](./UniversalOrbitBijectionAndRightSpecialLock.lean) &
   [UniversalOrbitBijectionAndRightSpecialLockChecks.lean](./UniversalOrbitBijectionAndRightSpecialLockChecks.lean)):**
   - **Strict Monotonicity & Upper Growth (`orbit_strictMono_of_pos`, `two_pow_mul_orbit_add_eq`):**
     Proved `n₁ < n₂ → orbit a_0 n₁ < orbit a_0 n₂`, `2^n * (orbit a_0 n + 1) ≤ 3^n * (a_0 + 1)`, and
     `2^m * orbit a_0 (n + m) = 3^m * orbit a_0 n + wordCarry (shiftStream (orbit a_0) n) m`.
   - **Universal Forward $2^m$ / Backward $3^m$ Orbit Bijection
     (`orbit_mod_two_pow_iff_parity_eq_iff_orbit_add_mod_three_pow`, Track 1):**
     Proved for **every** seed `a_0 : ℕ`, indices `n₁, n₂ : ℕ`, and window length `m : ℕ`:
     `orbit a_0 n₁ % 2^m = orbit a_0 n₂ % 2^m ↔ (∀ j < m, orbit a_0 (n₁ + j) % 2 = orbit a_0 (n₂ + j) % 2) ↔ orbit a_0 (n₁ + m) % 3^m = orbit a_0 (n₂ + m) % 3^m`.
   - **Global Right-Special Odd-Quotient Lock & Three-Occurrence Pairing
     (`right_special_orbit_exact_two_and_three_adic_lock`, `three_occurrence_raw_orbit_two_pow_add_one_dvd`):**
     Proved that any right-special length-`m` parity repeat at `n₁ < n₂` satisfies
     `orbit a_0 n₂ - orbit a_0 n₁ = 2^m * q_odd` and `orbit a_0 (n₂ + m) - orbit a_0 (n₁ + m) = 3^m * q_odd`
     for a single positive odd integer `q_odd ≥ 1` (`q_odd % 2 = 1`).
   - **Unconditional $\log 2 / \log(3/2) \approx 1.709511$ Parity-Complexity Lower Bound for ALL Positive
     Integers (`raw_orbit_repeated_parity_window_pq_cutoff`,
     `raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds`, Track 4):**
     Proved that for **every** positive integer `1 ≤ a_0 < 2^W` (with **no** Mahler companion assumption!),
     any repeated length-`m` parity window at `n₁ < n₂` satisfies `q * m < p * n₂ + q * W` (`17 * m < 10 * n₂ + 17 * W`),
     so `17 * k + 1 ≤ prefixFactorCount (orbitParityStream a_0) (10 * k + W) (17 * k)` and no positive
     integer's $T_{3/2}$ parity stream can have liminf factor complexity slope `< log 2 / log(3/2)`.
   - **Mod-3 Valuation Trichotomy & Epoch Coding (`three_mul_affInv_eq_nineteen_mul_add_eight`,
     `two_adic_valuation_affInv_trichotomy`, `epoch_period_three_run_exit_trichotomy`, Section 7):**
     Proved `3 * (19 * b + 9) = 19 * (3 * b + 1) + 8`, the 4-way valuation trichotomy (`v_2 = 1 ↔ s = 1`,
     `v_2 = 2 ↔ s = 2`, `v_2 = 3 ↔ 4 ≤ s`, `v_2 ≥ 4 ↔ s = 3`), and the exact run/exit coding theorem
     showing that `19 * b 0 + 9 = 2^(3 * j + r) * q` (`q % 2 = 1`) forces `s_j = 1` (`r = 1`),
     `s_j = 2` (`r = 2`), or `4 ≤ s_j` (`r = 3`).

3. **Step 2 — The $\beta = 3/2$ Shift Dictionary, Kneading Cascade, $|G_N| \ge (3/2)^N$ Counting &
   Lagarias-Style Conjugacy
   ([BetaShiftThreeHalvesDictionary.lean](./BetaShiftThreeHalvesDictionary.lean) &
   [BetaShiftThreeHalvesDictionaryChecks.lean](./BetaShiftThreeHalvesDictionaryChecks.lean), Sections 8 & 9):**
   - Proved the exact conjugacy `fract_dynamics_conj_betaMap` between `2 * fracPart a_0 α n` and
     `betaMap x = (3/2) * x - ⌊(3/2) * x⌋`.
   - Certified the first 34 digits of the kneading sequence $d_{3/2}(1)$ (`kneading_prefix_27_and_blocks_2_6_3_3_2_10_7`)
     and proved that its block lengths are `[2, 6, 3, 3, 2, 10, 7]`.
   - Proved the shift-invariant Parry forbidden-subword theorem (`parry_forbidden_prefixes_and_admissible_101000001`)
     and the non-Parry / non-sofic algebraic obstruction (`three_halves_not_monic_integer_root`).
   - Proved the exact survivor count formula below bit length $W$:
     `#{a < 2^W | survivesSteps a N = true} = 2^(W - N) * |G_N|` (`survivor_count_eq_admissible_card_mul_two_pow`).
   - Constructed the Lagarias-style itinerary map `itinerarySeedModTwoPow θ N` (`orbit_add_itinerary_mul_three_halves_pow`)
     and proved by rational grid covering that $3^N \le 2^N \cdot |G_N|$ (`|G_N| ≥ (3/2)^N`,
     `two_pow_mul_admissible_card_ge_three_pow`), together with `orbit_mod_two_pow_mem_admissibleResidueFinset_of_validCompanionForever`
     and the periodic sign obstruction `periodic_itinerary_two_adic_seed_neg`.

4. **Steps 4 & 5 — Universal $-72(3^{s-3} - 2^{s-3})$ Factorization, All-Rung Descent, $(2, s_1)$ Composite
   Lock & the 2-Adic Coincidence Law
   ([GeneralizedDefectFactorizationAndAllRungDescent.lean](./GeneralizedDefectFactorizationAndAllRungDescent.lean) &
   [GeneralizedDefectFactorizationAndAllRungDescentChecks.lean](./GeneralizedDefectFactorizationAndAllRungDescentChecks.lean),
   Tracks 2 & 3, Sections 6 & 10):**
   - Proved `defectError_eq_neg_seventy_two_mul` and `three_pow_sub_two_pow_coprime_six` ($\gcd(3^k - 2^k, 6) = 1$
     for all $k \ge 1$).
   - Proved the Section 6 post-defect 3-adic lock `9 ∣ U₁ ∧ ¬ (27 ∣ U₁)` and generalized normalized recurrence
     (`post_defect_quotient_divisible_by_nine_and_normalized_recurrence`), together with all-rung sparse-defect
     descent (`general_s_ge_four_sparse_defect_strict_descent`, `no_infinite_all_rung_sparse_defect_chain`).
   - Proved the $(2, s_1)$ composite defect identity $+36(3^{s_1 - 3} + 2^{s_1})$ and coprimality to $6$
     (`composite_defect_two_s1_identity_and_coprime_six`), the net increase `Δ Φ_def = s₁ - 4 ≥ +2` across
     feasible $(2, s_1)$ pairs (`recovery_pair_two_s1_deficitPotential_increase`), and mod-3 valuation
     incompatibility (`mod_three_valuation_incompatibility_s_ge_four_vs_two_pair`).
   - Proved the 2-adic coincidence law and mod-8 target lock (`two_adic_coincidence_law_and_mod_eight_lock`)
     and the $p$-adic Baker/Yu vs. archimedean budget comparison (`p_adic_baker_yu_vs_archimedean_budget_comparison`).

5. **Steps 6 & 7 — Bounded-Odd-Part $S$-Unit Exclusion, Backward 3-Adic Sieve, Integer/Rational Cases,
   Multi-Collision Ultrametric Boost & $\Sigma_1 / \Pi_2$ Certificates
   ([BoundedOddPartAndThreeAdicSieve.lean](./BoundedOddPartAndThreeAdicSieve.lean) &
   [BoundedOddPartAndThreeAdicSieveChecks.lean](./BoundedOddPartAndThreeAdicSieveChecks.lean),
   Tracks 4 & 5, Sections 11–15):**
   - **Section 11:** Proved non-vanishing of all proper 2-term subsums in the 4-term $\{2, 3\}$-unit epoch
     equation (`four_term_sunit_epoch_equation_no_vanishing_subsum`), budget saturation
     (`bounded_odd_part_iff_runs_saturate_budget`), strict-monotonicity injectivity of $(j_r, V_r)$
     (`strictMono_boundaries_injective_on_j_and_V`), the **unconditional** impossibility of simultaneously
     bounded $(j_r, V_r)$ along strictly increasing boundaries (`no_simultaneously_bounded_j_and_V_along_strictMono_boundaries`),
     and the conditional $S$-unit exclusion of bounded odd parts (`no_bounded_odd_part_orbit_of_sunit_finiteness`).
   - **Section 12:** Proved `orbit_mod_three_ne_one`, `orbit_add_two_mod_nine_eq_eight_iff_consecutive_odd`,
     and the mod-$6^\ell$ limitative biconditional `orbit_mod_six_pow_eq_iff_surrounding_window_parity_eq`.
   - **Section 13:** Proved `not_validCompanionUpTo_of_zero_offset` (no integer $\alpha = a_0$ survives past
     step $W$), `fract_lt_half_iff_floor_two_mul_even`, `minimal_z_floor_not_dvd_three` ($3 \nmid a^*$),
     and `no_eleven_subsum_interval_overlap_at_two_thirds`.
   - **Sections 14, 15 & Tracks 4–5:** Proved `monotone_complexity_telescope_sum`,
     `sigma1_bounded_box_escape_of_survivesSteps_false`, `pi2_unbounded_lower_bound_iff_mahler`,
     `raw_orbit_multi_collision_ultrametric_pq_cutoff`, and `baseSixScaledNat_natToBaseSixConfig_eq`.

## 18. Synthesis of Where the Problem Now Stands & Next-Round Questions

Across Rounds 1 and 2 (`158` Lean 4 files), the formalization has cleanly separated what is
unconditionally proved from the exact remaining open regime:

1. **Unconditionally Resolved in Round 2:**
   - Every positive integer $a_0 \ge 1$ under $T(x) = \lceil 3x/2 \rceil$ has parity factor complexity
     $P(m) \ge (\frac{\log 2}{\log(3/2)} - o(1)) m \approx 1.7095 m$ (`raw_orbit_no_subcritical_parity_complexity_for_all_pos_seeds`),
     while every hypothetical $Z$-number has its parity word confined to the $\beta = 3/2$ shift $S_{3/2}$
     of size $|G_m| \ge (3/2)^m$ (`two_pow_mul_admissible_card_ge_three_pow`).
   - Every epoch transition across **all rungs $s_r \ge 4$** obeys the universal coprime recurrence
     $2^{3 j_{r+1} + s_r} V_{r+1} + (3^{s_r - 3} - 2^{s_r - 3}) = 3^{3 j_r + s_r} V_r$ with
     $\gcd(3^{s_r - 3} - 2^{s_r - 3}, 6) = 1$, and **no two epochs $r_1 < r_2$ can ever repeat the same
     pair $(j_r, V_r)$** (`strictMono_boundaries_injective_on_j_and_V`), ruling out simultaneously
     bounded $(j_r, V_r)$ unconditionally and ruling out bounded odd parts $V_r \le M$ conditional on
     4-term $\{2, 3\}$ $S$-unit finiteness.

2. **Open Questions for Round 3 (If Pursued):**
   - **Question R3.1 (Effective Baker/Pillai Cutoff for Bounded $(V_r \le M,\, s_r \le S_{\max})$):**
     When both $V_r \le M$ and $s_r \le S_{\max}$ are bounded, the 4-term equation reduces to finitely
     many 3-term Pillai equations $V \cdot 3^a - V' \cdot 2^c = D_s$. Connecting this directly to
     `BakerMatveevFramework.lean` gives an explicit logarithmic bound on $a = 3 j_r + s_r$, turning
     `no_bounded_odd_part_orbit_of_sunit_finiteness` into an effective theorem for bounded $(V, s)$.
   - **Question R3.2 (Unbounded Odd Parts $V_r \to \infty$ vs. the Mod-3 Death Class $v_2(I(b)) \equiv 1 \pmod 3$):**
     When $V_r$ grows without bound, $3^{a_r} V_r - D_{s_r} = 2^{3 j_{r+1} + s_r} V_{r+1}$ must avoid
     the death valuation class $v_2(3^{a_r} V_r - D_{s_r}) \equiv s_r - 2 \pmod 3$ (which corresponds to
     $\nu_{r+1} \equiv 1 \pmod 3$, forcing $s = 1$, i.e. `11`) at **every** epoch $r \in \mathbb{N}$.
     Determining whether an unbounded integer trajectory can avoid $\nu_{r+1} \equiv 1 \pmod 3$ forever is
     the exact arithmetic heart of Mahler's $3/2$ problem.

See **[RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md](./RESEARCH_PLAN_ARGON_ROUND3_BREAKTHROUGH.md)** for the
complete, prioritized Round 3 research plan and new mathematical invariants addressing these questions.

