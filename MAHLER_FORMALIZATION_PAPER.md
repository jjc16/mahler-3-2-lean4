# Formalizing the Reduced Mahler $3/2$ Dynamical System in Lean 4: Exact 1D Slack Reduction, Constructive Coasting Survivors, Conditional Finiteness Theorems, and Certified Transcendence Barriers

**Authors:** Joshua Coon (with Astra and Argon AI assistance via GitHub Copilot)  
**Toolchain:** Lean 4.19.0 + Mathlib v4.19.0 (`140` `.lean` files, `0` `sorry`s, `0` warnings, standard Lean axioms `[propext, Classical.choice, Quot.sound]`)

---

## Abstract

Mahler's $3/2$ problem (1968) asks whether there exists any real "$Z$-number" $\alpha > 0$ such that the fractional part $\{(3/2)^n \alpha\}$ lies in $[0, 1/2)$ for every integer $n \ge 0$. Writing $\alpha = a_0 + \xi$ with $a_0 = \lfloor \alpha \rfloor \in \mathbb{N}$ and $\xi \in [0, 1)$, survival up to step $N$ is equivalent to the discrete ceiling recurrence $g_{n+1} = \lceil 3 g_n / 2 \rceil = \lfloor (3 g_n + 1)/2 \rfloor$ ($g_0 = a_0$) admitting a non-empty intersection of $N$ nested archimedean companion intervals $[\text{lowerBound}(a_0, n),\, \text{upperBound}(a_0, n))$ (`InfiniteZNumberBridgeAndRationalBase.lean`).

In this work, we present a 140-file, `sorry`-free formalization in Lean 4 that investigates both **constructive survival** and **obstructions to infinite orbits**:
1. **Exact 1D Slack Reduction & Infinite-Horizon $Z$-Number Bridge:** By grouping each odd step $g \mapsto (3g+1)/2$ with its $s(k)-1$ subsequent even steps $g \mapsto 3g/2$ via $3 b_k + 1 = 2^{s(k)} u(k)$ ($\gcd(u(k), 6) = 1$), we collapse all $\binom{K}{2}$ pairwise companion-interval inequalities along a finite block chain into a **single 1D recurrence** (`minSlack`), and prove its exact two-way equivalence with the existence of a real companion surviving through step $T(K)$ (both in interval form and in direct `Int.fract` form). Normalizing by $2^{T(m)}$ yields the time-homogeneous 1D slack map $\mu_2(s, m+1) = \min\big(1,\, (3/2)^{s(m)} \mu_2(s, m) - 2\big)$ driven by the arithmetic-controlled block length $s(m) = v_2(3 b_m + 1)$ (`CoupledFractionalPartDynamics.lean`, `FiniteSeedCarryAndBackwardDescent.lean`).
2. **Constructive Survivors & 113-Step Record-Holder:** We prove that any block sequence with $s(k) \ge 3$ saturates the ceiling $\text{minSlack } s\ m = 2^{T(m)}$ and automatically admits a valid real companion at every finite horizon. Using this sufficiency theorem, we construct closed-form seed families surviving arbitrarily many blocks prior to ceiling exit, and machine-certify a 55-bit integer (`recordHolderA0 = 29871555608238677 < 2^55`) that survives **113 steps** (58 steps past its 55-bit binary length) before dying at step 114 (`MahlerGrandSynthesis.lean`, `InfiniteZNumberBridgeAndRationalBase.lean`).
3. **Unconditional Exclusion of Restricted, Aperiodic, Non-Stationary & Rapid-Growth Classes:** We prove explicit, logarithm-free step cutoffs in Lean 4 ruling out: (i) sub-ceiling bounded-block runs ($s(k) \le c$), (ii) periodic and uniform-macro-block sequences (`2^(D m) ∣ ((3^D - 2^D)(3a_0+1) + 2^(s 0) R_0)`), (iii) **arbitrary two-letter $\{a, b\}$ ($3 \le a \le b$) mechanical/Sturmian block chains** (`no_infinite_mechanical_two_letter_block_chain`, with factor complexity $\le L + 1$ derived directly from phase thresholds), (iv) **sub-critical liminf-complexity sequences** ($\kappa < \log 2 / \log(3/2) \approx 1.709511$) under a positive Cesàro mean, uniform window balance, or scale-local epoch balance (`no_infinite_tendsto_mean_log_threshold_block_chain`, `no_infinite_uniformWindowMean_global_complexity_block_chain`, `no_infinite_scale_local_balanced_block_chain`, including the non-stationary oscillating-epoch family `nonStationaryEpochSeq a b`), (v) **3-step encoded Thue–Morse and Period-Doubling parity streams** (`no_nonneg_seed_realizes_tmEncodedParity`, `pdEncodedParity_cutoff_and_exclusion`, with quantitative seed-residue lower bounds $\ge 2^{2^k}$) and **Thue–Morse block-length chains** (`no_infinite_tmBlockSeq_block_chain`), and (vi) **sustained rapid-growth chains** ($3 \le s(m+1)$ and $3^{s(m)} < 2^{s(m+1)}$, via well-founded odd-quotient descent $u(m+1) + 2 \le u(m)$ in `no_infinite_rapid_growth_block_chain`). We also formalize the exact arithmetic setup for Baker–Matveev, Ridout, and Schlickewei Subspace analyses, clearly separating the machine-checked algebraic/analytic bounds from external transcendence theorems not yet in Mathlib.
4. **Exact Coupled Seed-Residue State, 5-Way General Conjecture Equivalence, Certified $B(29) \ge 4096$ Bound & Structural Barriers:** We formalize the denominator-cleared integer feasibility margin $D_{N+1} = \min(2^{N+1},\, 3D_N - 2^{N+1}(\varepsilon_N \bmod 2))$, the coupled quotient–residue–margin transition $2q_{N+1} = 3q_N + 3^{N+1}\eta_N + e_N$, the **5-way general Mahler conjecture equivalence** (`general_mahler_conjecture_iff_positive_stabilized_branch_escape`, `mahler_conjecture_iff_leastPositiveSurvivor_unbounded`), the **Lean-certified global step-29 lower bound $m \ge 4096$ ($B(29) \ge 4096$) and extremal seed `149`** (`positive_survivor_step29_ge_4096`, `seed_149_survives_28_and_fails_29`), and the exact ceiling-recovery theorem (`signedMargin_100_ceiling_recovery`) explaining why $s(m) \ge 3$ (`100`) blocks escape pure scalar-margin contraction and why the general conjecture remains open.

---

## 1. Introduction: From Informal Proof Brainstorming to Machine-Checked Rigor

When attempting to prove Mahler's $3/2$ conjecture or related Collatz-type problems, informal proof sketches typically fall into two traps:
1. **The Probabilistic / Density Fallacy:** Treating 2-adic parity constraints and archimedean interval constraints as statistically independent, or assuming that once the step count $T$ exceeds the bit-length $W = \lfloor \log_2 a_0 \rfloor + 1$ (the "coasting regime"), a trajectory can only survive a handful of steps.
2. **The Hidden Rank-Collapse Trap:** Constructing auxiliary linear combinations, Wronskians, or multi-origin determinants that appear to overdetermine the orbit, without noticing that the underlying 1D affine recurrence forces those combinations to be algebraically dependent.

By formalizing every proposed attack vector in Lean 4—and requiring that every failed approach be diagnosed via a machine-checked counterexample or algebraic identity—we separated genuine number-theoretic structure from mirages.

---

## 1.5 Literature Survey, Attribution of Prior Work & Novel Contributions

To place this formalization in its proper mathematical context, we carefully distinguish **prior theorems from the literature that we rediscovered or formalized** from **novel formulations, theorems, and certified barrier analyses originating in this work**.

### A. Attribution to Prior Mathematical Literature

1. **Mahler (1968) — Discrete Companion Reduction, Series Formula & Two-Seed Ridout Bound [1]:**
   - Kurt Mahler introduced $Z$-numbers and proved the foundational reduction: for each integer $g_0 = a_0 \ge 1$, there is *at most one* real companion $\alpha = a_0 + \xi$ ($\xi \in [0, 1)$) such that $\alpha$ is a $Z$-number, governed by the discrete ceiling recurrence $g_{n+1} = \lceil 3 g_n / 2 \rceil = \lfloor (3 g_n + 1)/2 \rfloor$ and nested archimedean intervals (`MahlerDemandA.lean`, `PureIntegerPinch.lean`, `InfiniteZNumberBridgeAndRationalBase.lean`). As we formally verify in `odd_step_floor_exceeds_half_and_forces_ceil`, when $g_n$ is odd and $0 \le r_n < 1/2$, the remainder relative to $\lfloor 3 g_n / 2 \rfloor$ is $1/2 + 3 r_n / 2 \ge 1/2$, so keeping $\{(3/2)^{n+1}\alpha\} < 1/2$ forces $r_n \ge 1/3$ and $\lfloor (3/2)^{n+1}\alpha \rfloor = \lceil 3 g_n / 2 \rceil$.
   - Mahler also derived the infinite series representation of the unique candidate companion $\xi_\infty$ (`InfiniteSeries.lean`, `TelescopingSeriesDuality.lean`) and applied **Ridout's Theorem (1957) [2]** to the difference of two hypothetical $Z$-numbers in the same binary interval $[2^k, 2^{k+1})$ to show that at most finitely many $Z$-numbers exist per interval (`mahler_two_seed_same_step_ridout_bound` and `two_seed_shared_prefix_divisibility` in `RidoutSubspaceFramework.lean`), yielding $|\{Z\text{-numbers} \le X\}| = O(X^{0.7})$.
2. **Vijayaraghavan (1940), Pollington (1979) & Choquet (1980) — Distribution of Powers of $3/2$ and the $1/3$ Range Gap [3, 4, 5]:**
   - Vijayaraghavan [3] proved that fractional parts of rational powers $(p/q)^n \alpha$ for $\alpha \in \mathbb{Q}^\times$ have infinitely many limit points and cannot stay confined to $[0, 1/2)$.
   - Pollington [4] and Choquet [5] established lower bounds on the oscillation of $\{(3/2)^n \alpha\}$, leading to the critical gap constant $1/3$.
3. **Flatto, Lagarias & Pollington (1995) — The $1/3$ Range Theorem, Symbolic Dynamics & Forbidden Subwords [6]:**
   - In their landmark paper [6], Flatto, Lagarias, and Pollington proved that for every real $\alpha > 0$,
     $$\limsup_{n\to\infty} \{(3/2)^n \alpha\} - \liminf_{n\to\infty} \{(3/2)^n \alpha\} \ge \frac{3 - 2}{3} = \frac{1}{3}.$$
     This $1/3$ range gap is the continuous foundation of our **$\frac{1}{3}$ Archimedean Drain Budget** ($\sum_{k=1}^m (2/3)^{T(k)+1} < 1/3$ in `TelescopingSeriesDuality.lean`) and explains why $s(k) = 1$ (which consumes $(2/3)^2 = 4/9 > 1/3$ in one block) is forbidden (`EscapeBranchTwoCap.lean`).
   - Flatto, Lagarias, and Pollington also developed the **symbolic dynamics of the parity sequence $g_n \bmod 2$**, characterizing admissible finite binary words via an infinite hierarchy of forbidden subwords and deriving average step-rate / topological entropy bounds. Our theorems in `GlobalStepRateBounds.lean` and `MinSlackDynamicalSystem.lean`—including $s(k) \ge 2$, the post-$2$ recovery requirements $s(k+1) \ge 6, s(k+2) \ge 3, s(k+3) \ge 3$, the $(2, 6, 3, 3, 2, 10, 7)$ cascade, and the $3m - 1$ step-rate bound—rediscover and machine-check these symbolic-dynamical constraints in odd-block length coordinates $s(k)$.
4. **Classical Diophantine & Transcendence Machinery (Ridout [2], Schlickewei [7], Stewart [8], Baker–Wüstholz / Matveev [9, 10], Corvaja–Zannier [11, 12], Adamczewski–Bugeaud [13], Dubickas [14]) & Rational-Base Numeration Systems (Akiyama–Frougny–Sakarovitch [16], Andrieu–Eliahou–Vivion [17]):**
   - Our analyses in Modules 89–102 formalize the exact algebraic and logarithmic inequalities feeding into the classical frameworks of linear forms in logarithms (Baker–Wüstholz [9], Matveev [10]), $p$-adic Diophantine approximation (Ridout [2], Schlickewei's $p$-adic Subspace Theorem [7]), simultaneous representation in bases $2$ and $3$ (Stewart [8]), $S$-unit GCD bounds (Corvaja–Zannier [11, 12]), and subword-complexity transcendence criteria (Adamczewski–Bugeaud [13]). Because the deep transcendence theorems of Matveev, Ridout, and Schlickewei are not themselves formalized in Mathlib, our Lean modules establish the unconditional algebraic/archimedean upper bounds, GCD divisibility laws, and hyperplane syzygies directly, while clearly noting where external transcendence theorems are invoked in conditional interpretations.
   - Akiyama, Frougny, and Sakarovitch (2008) [16] introduced rational-base number systems $\text{rep}_{p/q}(n)$, and Andrieu, Eliahou, and Vivion (2025) [17] proved that Borel normality of minimal/maximal rational-base words (or residue equidistribution of $T_{3/2}^n(a_0) = \lceil 3x/2 \rceil \bmod 2^k$) implies the non-existence of $Z$-numbers. In `InfiniteZNumberBridgeAndRationalBase.lean`, we connect `Mahler.step` directly to $T_{3/2}$ and prove that single deterministic occurrences of forbidden patterns suffice without assuming full normality.

---

### B. Novel Contributions Originating in This Work (and Comparison with Prior Lean Formalizations)

1. **Relationship to Prior Lean Repositories on Mahler's Work:**
   - A direct search of all public Lean repositories on GitHub shows that **Google DeepMind's `formal-conjectures` project [15]** (`FormalConjectures/Wikipedia/Mahler32.lean`, `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_9.lean`, and `FormalConjecturesForMathlib/NumberTheory/DiophantineApproximation/ZNumber.lean`, 2025–2026) previously formalized the *definition* `IsZNumber`, a 5-line sanity check `¬ IsZNumber 1`, and the *statements* (with `sorry` placeholders) of Mahler's conjecture, the consequence of $\Omega(3/2) > 1/2$, the Flatto–Lagarias–Pollington bound $\Omega(p/q) \ge 1/p$, Lebesgue measure zero, and Hausdorff dimension $< 1$.
   - Other Lean 4 repositories bearing Mahler's name address distinct theorems of Kurt Mahler: `giuliocaflisch/mahler` (Mahler's theorem on $p$-adic continuous functions), `DiegoMarquesMath/MahlerLean` (Mahler's classification of Liouville numbers), and `baobingzhang/jsp-000025-lehmer-schinzel-lean` (polynomial Mahler measure).
   - Thus, while `google-deepmind/formal-conjectures` [15] formalized the top-level conjecture statements for $Z$-numbers, our 122-module `sorry`-free library is a substantial proved Lean 4 development of the discrete Mahler $3/2$ dynamical system, the finite and infinite companion-interval reductions, the Flatto–Lagarias–Pollington symbolic forbidden-subword constraints in odd-block coordinates, the Sturmian/balanced aperiodic complexity exclusions, the finite-seed vs. 2-adic isolation theorems, and the Diophantine setup identities.
2. **The Reduced Coprime Quotient System & Exact 1D `minSlack` Dynamical Collapse (`CoprimeRemainderSlack.lean`, `MinSlackDynamicalSystem.lean`, `ConverseCompanionReconstruction.lean`, `CoupledFractionalPartDynamics.lean`):**
   - Formulating the dynamics in terms of the coprime odd quotients $2^{s(k+1)} u(k+1) = 3^{s(k)} u(k) + 1$ ($\gcd(u(k), 6) = 1$), the 3-adic block-boundary factorization $b_{k+1} = 3^{s(k)-1} u(k)$, and the polynomial $R(s, m)$.
   - Collapsing all $\binom{K}{2}$ shifted archimedean companion inequalities into the **single 1D recurrence** `minSlack s (m+1) = min (2^(T(m+1))) (3^(s m) * minSlack s m - 2^(T(m+1)+1))` and its normalized 1D update $\mu_2(s, m+1) = \min\big(1,\, (3/2)^{s(m)} \mu_2(s, m) - 2\big)$ driven by the block length $s(m)$ (with uncapped values in $(0, 1]$ partitioned by $(0, 1] = \bigsqcup_{c=2}^\infty (2(2/3)^c, 3(2/3)^c] \cap (0, 1]$), together with the two-way **Converse Companion Reconstruction Theorem** (`(∃ ξ, ValidCompanionUpTo a_0 ξ (blockSteps s K)) ↔ 0 < minSlack s (K - 1)`).
3. **Additive Separation of Shifted Slacks & the Three-Origin Subspace Syzygy (`MultiOriginSubspaceSyzygy.lean`):**
   - Proving that the two-parameter triangle of shifted slacks separates additively as $\frac{2^{T(r)} \Delta^{(r)}_{m-r}}{3^{T(m)}} = \frac{\Delta^{(0)}_m}{3^{T(m)}} - \frac{\Delta^{(0)}_r - 2^{T(r)}}{3^{T(r)}}$, eliminating `shiftSeq` completely from `0 < minSlack s m`, and proving the exact **Three-Origin Schlickewei Subspace Hyperplane Syzygy** (Dead End 15) showing that any $\ge 3$ shifted origins lie in the 2D plane $\text{span}\{\Delta^{(0)}_m, 3^{T(m)}\}$.
4. **Carryless Base-3 Frozen-Prefix Equivalence & Dual Remainder Complementarity (`SimultaneousBaseDigitRigidity.lean`):**
   - Proving $0 < \Delta_m \iff \lfloor 2^{T(m+1)+1} u(m) / 3^{T(m)} \rfloor = 6a_0 + 2$ (and its multi-origin companion equivalence) together with the exact dual remainder law $(P_m \bmod 3^{T(m)}) + (Q_m \bmod 2^{T(m)}) = 3^{T(m)}$.
5. **Exact Three-Way Multi-Step GCD Identities & Two-Sided CRT Quotient Floors (`MultiStepQuotientGCD.lean`, `ThreeAdicAndSeedGCDLocks.lean`, `Mod2304CombinedSieve.lean`, `TwoSidedCRTAndBackwardObstructions.lean`, `Mod216TwoSidedQuotientFloor.lean`):**
   - Proving the exact GCD equalities $\gcd(u(r), u(r+d)) = \gcd(u(r), R^{(r)}_d) = \gcd(u(r+d), R^{(r)}_d)$, $\gcd(\Delta_r, \Delta_{r+d}) = \gcd(\Delta_r, R^{(r)}_d)$ (with $\gcd(\Delta_r, \Delta_{r+1}) = 1$), and $\gcd(u(m), \Delta_m) = \gcd(u(m), 2a_0+1) = \gcd(\Delta_m, 2a_0+1)$.
   - Proving the closed-form 3-adic residue lock $u(k+1) \bmod 3^{s(k)} = ((3^{s(k)}+1)/2)^{s(k+1)} \bmod 3^{s(k)}$ and combining backward 3-adic congruences ($\bmod\, 3, 9, 27$) with forward 2-adic congruences ($\bmod\, 4, 8, 64, 256$) to prove $u(k) \ne 1$ ($k \ge 1$), $1735 \le u(k)$ at $s(k) = 2$, $65 \le u(k)$ across $2 \le s(k) \le 6$, and $103 \le u(k)$ on ceiling-saturated runs.
6. **Exact $2^{T(m)}$-Cancellation in the Single-Origin Ridout Product & Explicit Repeated-Subword Cutoffs (`RidoutSubspaceFramework.lean`, `RepeatedSubwordComplexity.lean`):**
   - Proving the single-origin cancellation $2^{s(m)+D+1} u(m) \Delta_m < 3^{T(m)+1}(2a_0 + 1)$ and the exponent identity $(1 - \frac{\log 2}{\log 3}) + \frac{\log 2}{\log 3} + 1 = 2$ (Dead End 14).
   - Proving the parity-enhanced common multiplier $u(r_2) - u(r_1) = 2^{S_{\text{tail}}+1} K_0$, $u(r_2+d) - u(r_1+d) = 2 \cdot 3^S K_0$ across any repeated subword and its logarithm-free linear cutoff $\text{blockSteps}^{(r_1)} L \le T(r_2) + W$.
7. **Discovery & Machine Certification of the 55-Bit, 113-Step Coasting Record-Holder (`MahlerGrandSynthesis.lean`):**
   - Using our ceiling-saturation sufficiency theorem (`exists_validCompanionUpTo_of_three_le`) to construct a targeted congruence search that uncovered `recordHolderA0 = 29871555608238677 < 2^55`, surviving 113 steps (58 steps past its 55-bit binary length) and dying at step 114.

---

## 2. The Odd-Block Reduction & Dual 2-Adic / 3-Adic Recurrence

Let `step x = (3 * x + 1) / 2` if `x` is odd and `3 * x / 2` if `x` is even, and let `orbit a_0 t` be the $t$-th iterate starting from $a_0 \in \mathbb{N}$.

A sequence of block lengths $s : \mathbb{N} \to \mathbb{N}$ and odd quotients $u : \mathbb{N} \to \mathbb{N}$ forms a **`ValidBlockChain a_0 s u K`** (`OddBlockReduction.lean`) if for every $k < K$:
$$1 \le s(k), \qquad u(k) \bmod 2 = 1, \qquad 3 \cdot b_k + 1 = 2^{s(k)} u(k),$$
where $b_k := \text{orbit } a_0\ (T(k))$ and $T(k) := \text{blockSteps } s\ k = \sum_{i=0}^{k-1} s(i)$.

### Fundamental Identities Along Any Valid Block Chain
- **One-Step Coprime Quotient Recurrence (`CoprimeRemainderSlack.lean`):**
  $$2^{s(k+1)} u(k+1) = 3^{s(k)} u(k) + 1 \qquad (k + 1 < K).$$
- **Exact 3-Adic Factorization of Block-Boundary Orbit Values (`ThreeAdicAndSeedGCDLocks.lean`):**
  $$b_{k+1} = \text{orbit } a_0\ (T(k+1)) = 3^{s(k) - 1} \cdot u(k), \qquad \gcd(u(k), 6) = 1.$$
  Thus at every block boundary $b_{k+1}$, its **3-adic valuation** is $s(k) - 1$ (encoding the *preceding* block length) with 3-free part $u(k)$, while the **2-adic valuation of $3 b_{k+1} + 1$** is $s(k+1)$ (encoding the *upcoming* block length) with 2-free part $u(k+1)$!
- **Multi-Step Coprime Remainder & Intrinsic Slack (`CoprimeRemainderSlack.lean`, `AperiodicSlackCocycle.lean`):**
  Defining $R(s, 0) = 0$ and $R(s, m+1) = 3^{s(m)} R(s, m) + 2^{\text{tailSteps } s\ m}$ (where $\text{tailSteps } s\ m = \sum_{i=1}^m s(i)$), the $m$-step quotient satisfies:
  $$2^{\text{tailSteps } s\ m} u(m) = 3^{T(m)} u(0) + R(s, m).$$
  Eliminating $u(0)$ via $2^{s(0)} u(0) = 3 a_0 + 1$ yields the **Orbit Slack Identity**:
  $$\Delta_m := \text{integerSlack } s\ m := 3^{T(m)} - 2^{s(0)+1} R(s, m) = 3^{T(m)+1}(2a_0 + 1) - 2^{T(m+1)+1} u(m).$$
  Notice that the middle expression $3^{T(m)} - 2^{s(0)+1} R(s, m)$ depends **solely on the block sequence $s$** and is completely independent of $a_0$ and $u$!

---

## 3. Exact 1D Dynamical Reduction & Converse Companion Reconstruction

At first glance, ensuring that all $K$ archimedean companion intervals $[\text{lowerBound}(a_0, T(j)),\, \text{upperBound}(a_0, T(m+1)))$ overlap requires checking $\binom{K}{2}$ pairwise inequalities:
$$\forall\, 0 \le j \le m < K, \qquad 0 < \Delta^{(j)}_{m - j} := \text{integerSlack } (\text{shiftSeq } s\ j)\ (m - j).$$

We proved four equivalent ways to collapse this $\binom{K}{2}$ triangular system into a **1D dynamical condition**:

1. **The 1D `minSlack` Dynamical System (`MinSlackDynamicalSystem.lean`, `ConverseCompanionReconstruction.lean`):**
   Define:
   $$\text{minSlack } s\ 0 = 1, \qquad \text{minSlack } s\ (m+1) = \min\!\Big(2^{T(m+1)},\ 3^{s(m)} \cdot \text{minSlack } s\ m - 2^{T(m+1)+1}\Big).$$
   Then for any `ValidBlockChain a_0 s u K` ($K \ge 1$), a real companion $\xi \in \mathbb{R}$ surviving through step $T(K)$ exists **if and only if** `0 < minSlack s (K - 1)`:
   $$\big(\exists \xi : \mathbb{R},\ \text{ValidCompanionUpTo } a_0\ \xi\ (T(K))\big) \iff 0 < \text{minSlack } s\ (K - 1).$$

2. **Shift-Free Unshifted Ceiling Comparison (`MultiOriginSubspaceSyzygy.lean`):**
   Using the **Shifted Slack Affine Collapse Identity**
   $$2^{T(r)} \Delta^{(r)}_d = \Delta^{(0)}_{r+d} + 3^{S_{r, d}} \big(2^{T(r)} - \Delta^{(0)}_r\big),$$
   every `shiftSeq` can be eliminated:
   $$0 < \text{minSlack } s\ m \iff \forall j \le m,\quad 3^{T(m)} \big(\Delta^{(0)}_j - 2^{T(j)}\big) < 3^{T(j)} \Delta^{(0)}_m.$$

3. **Carryless Base-3 Shift-and-Add Automaton (`SimultaneousBaseDigitRigidity.lean`):**
   The scaled quotients $P_m := 2^{T(m+1)+1} u(m)$ satisfy the base-3 shift-and-add recurrence $P_{m+1} = 3^{s(m)} P_m + 2^{T(m+1)+1}$, and unconditionally $P_m = 3^{T(m)}(6a_0 + 2) + 2^{s(0)+1} R(s, m)$. Thus:
   $$0 < \Delta^{(0)}_m \iff \left\lfloor \frac{2^{T(m+1)+1} u(m)}{3^{T(m)}} \right\rfloor = 6a_0 + 2 \quad (\text{no base-3 carry across } 3^{T(m)}\text{!}).$$

4. **Time-Homogeneous 1D Slack Map & Lüroth–Markov Partition (`CoupledFractionalPartDynamics.lean`, `FiniteSeedCarryAndBackwardDescent.lean`):**
   Normalizing by $2^{T(m)}$ via $\mu_2(s, m) := \text{minSlack } s\ m / 2^{T(m)}$ removes the explicit time dependence $T(m)$ from the recurrence:
   $$\mu_2(s, 0) = 1, \qquad \mu_2(s, m + 1) = \min\!\left(1,\ \left(\frac{3}{2}\right)^{s(m)} \mu_2(s, m) - 2\right).$$
   *(Scope note: $\mu_2$ still takes the block length $s(m)$ as input—at $\mu_2 = 1$, every $s(m) \ge 3$ preserves $\mu_2 = 1$. Along an integer orbit, $s(m) = v_2(3 b_m + 1)$ and $u(m) = (3 b_m + 1)/2^{s(m)}$ are uniquely forced by the arithmetic boundary $b_m$, as proved in `arith_block_parameters_unique`.)*
   Whenever the uncapped ratio $\theta_2(s, m) = \Delta_m / 2^{T(m)}$ transitions into $(0, 1]$, $\theta_2(s, m)$ must lie in the partition cell $I_{s(m)} = (2(2/3)^{s(m)},\, 3(2/3)^{s(m)}]$. Because $3(2/3)^{c+1} = 2(2/3)^c$, the cells $I_c \cap (0, 1]$ ($c = 2, 3, 4, \dots$) form a **pairwise-disjoint partition of $(0, 1]$**.

5. **Infinite-Horizon $Z$-Number Bridge & Direct `Int.fract` Equivalence (`InfiniteZNumberBridgeAndRationalBase.lean`):**
   For any $a_0 \in \mathbb{N}$ and $\alpha \in \mathbb{R}$, `ValidCompanionUpTo a_0 α N` holds **if and only if** $\lfloor \alpha \rfloor = a_0$ and $\forall n \le N,\ \text{Int.fract}(\alpha (3/2)^n) < 1/2$ (`validCompanionUpTo_iff_floor_and_fract_lt_half`), and `ValidCompanionForever a_0 α` holds **if and only if** $\lfloor \alpha \rfloor = a_0$ and $\forall n \in \mathbb{N},\ \text{Int.fract}(\alpha (3/2)^n) < 1/2$ (`validCompanionForever_iff_floor_and_forall_fract_lt_half`). Along an infinite block chain, any $\alpha_\infty$ satisfying the strict block-boundary separation $\forall m,\ \text{lowerBound } a_0\ (T(m)) \le \alpha_\infty < \text{upperBound } a_0\ (T(m))$ is a valid companion across all steps (`validCompanionForever_of_block_boundary_separation`).

---

## 4. Ceiling Saturation & the 113-Step 55-Bit Record-Holder

Whenever $s(k) \ge 3$ for all $k < m$, `minSlack` remains pinned at its ceiling (`CeilingSaturationSynthesis.lean`):
$$\big(\forall k < m,\ 3 \le s(k)\big) \implies \text{minSlack } s\ m = 2^{T(m)} > 0.$$
Consequently, **every** block chain with $s(k) \ge 3$ automatically satisfies all archimedean companion constraints (`exists_validCompanionUpTo_of_three_le`).

- **Arbitrarily Long Closed-Form Survivors (`ExplicitHorizonCutoffs.lean`):**
  The closed-form integer family
  $$a_0(r) = \frac{92 \cdot 2^{12 r} - 27}{65}$$
  executes $r$ consecutive $(3, 3, 3, 3)$ cycles ($12r$ steps) with $s(k) = 3$, surviving arbitrarily many steps before its first $s = 2$ block.
- **The 113-Step Coasting Record-Holder (`MahlerGrandSynthesis.lean`):**
  Searching the ceiling-saturated congruence tree uncovered the 55-bit seed:
  $$\text{recordHolderA0} = 29{,}871{,}555{,}608{,}238{,}677 < 2^{55}.$$
  In `recordHolderA0_exact_113_survival_and_114_death`, Lean machine-checks that `recordHolderA0` executes 31 blocks with $s(k) \ge 3$ through $T(31) = 109$, hits its first $s(31) = 2$ at step 109, takes $s(32) = 1$ at step 111, **survives 113 steps** (58 steps past its 55-bit binary length!), and dies at step 114.

---

## 5. Unconditional Finiteness Theorems & Two-Sided CRT Sieves

While ceiling-saturated chains can be constructed up to $T(m) \approx W$ for $a_0 < 2^W$, once $T(m) > W$ (the **coasting regime**), we proved unconditional finiteness across the following regimes:

1. **Global Step-Rate & Even-Step Domination (`GlobalStepRateBounds.lean`, `ThreeAdicValuationConservation.lean`):**
   Every surviving orbit satisfies $s(k) \ge 2$, $s(k) = 2 \implies s(k+1) \ge 6, s(k+2) \ge 3, s(k+3) \ge 3$, and the global step-rate bound:
   $$3 m \le T(m) + 1 \iff 2 m \le \text{evenStepSum } s\ m + 1.$$
   Moreover, the product of the first $m$ block-boundary orbit values has exact 3-adic valuation $T(m) - m$:
   $$\prod_{k=0}^{m-1} b_{k+1} = 3^{T(m) - m} \prod_{k=0}^{m-1} u(k), \qquad \gcd\!\left(\prod_{k=0}^{m-1} u(k),\, 6\right) = 1.$$

2. **Time-Independent Bounded-Block Escape Ceilings (`AperiodicBoundedBlockSqueeze.lean`, `TimeIndependentDeficiencySqueeze.lean`):**
   During any run of blocks bounded by $s(k+i) \le c$ after $s(k-1) = 2$, the $2^{T(k)}$ factor cancels identically from `minSlackDeficiency`, bounding the run to at most **6 steps** for $c = 3$ and **4 blocks** for $c = 5$ regardless of how large $T(k)$ is!

3. **Repeated-Subword & Aperiodic Sturmian / Balanced Complexity Cutoffs (`RepeatedSubwordComplexity.lean`, `SturmianAndBalancedComplexityExclusion.lean`):**
   Whenever an $L$-block subword repeats at two origins $r_1 < r_2$ ($\forall i < L,\, s(r_1+i) = s(r_2+i)$), subtracting the multi-step quotient equations cancels the unknown remainder $R_{\text{win}}$ identically and yields a common positive integer $K_0 \ge 1$ such that:
   $$u(r_2) - u(r_1) = 2^{\text{tailSteps}^{(r_1)}(L-1) + 1} K_0, \qquad u(r_2 + L - 1) - u(r_1 + L - 1) = 2 \cdot 3^{\text{blockSteps}^{(r_1)}(L-1)} K_0.$$
   Raising the resulting exponential bound $2^{T(r_2) + S + 2} < 3^{T(r_2)+1}(2a_0+1)$ to the 5th ($3^5 = 243 < 2^8 = 256$) and 17th ($3^{17} < 2^{27}$) powers yields the **weighted logarithm-free cutoffs**:
   $$5 S \le 3 T(r_2) + 5 W + 2, \qquad 17 S \le 10 T(r_2) + 17 W + 9, \qquad 51 L \le 10 T(r_2) + 17 W + 26.$$
   Combining these weighted inequalities with the **Finite Pigeonhole Principle on subword complexity** (`exists_repeated_subword_of_pattern_classifier`) unconditionally excludes substantial **aperiodic** classes—including ceiling-saturated classes ($s(k) \ge 3$) that never trigger any archimedean or deficiency pinch:
   - **Aperiodic Ceiling-Saturated $\{3, 4\}$ & $[3, 5]$ Sturmian Classes (`aperiodic_sturmian_three_four_exclusion`, `aperiodic_sturmian_three_five_exclusion`):** Any chain in $\{3, 4\}$ (resp. $[3, 5]$) of complexity $p(L) \le L + C_0$ satisfies $3 L \le 12 C_0 + 5 W + 2$ (resp. $L \le 50 C_0 + 17 W + 9$).
   - **General Sub-Critical Balanced Complexity (`balanced_subcritical_complexity_exclusion`):** For *any* average block length $\lambda$, any surviving chain with $10 T(r_2) \le (17 - \delta) S + D_0$ ($\delta \ge 1$, corresponding to complexity factor $\kappa \le (17-\delta)/10 < 1.7$) satisfies $3 \delta L \le D_0 + 17 W + 9 + \delta$.

4. **Two-Sided Chinese Remainder Sieves & Quotient Floors (`Mod256CompleteSieve.lean`, `Mod2304CombinedSieve.lean`, `TwoSidedCRTAndBackwardObstructions.lean`, `Mod216TwoSidedQuotientFloor.lean`):**
   - **Mod-2304 ($256 \times 9$) Two-Block Sieve:** Eliminates $2283$ of $2304$ residue classes of $(3^{s(k)} u(k) + 1) \bmod 2304$ ($99.09\%$), locking the post-$2$ recovery branch to the single class $Y = 28 \pmod{2304}$.
   - **Unconditional Impossibility of $u(k) = 1$ ($k \ge 1$):** Looking one step backward ($k-1 \to k$) mod $3$ forces $u(k) = 1 \implies s(k)$ even, and looking one step forward ($k \to k+1$) mod $4$ forces $3^{s(k)} + 1 \equiv 2 \pmod 4 \implies s(k+1) = 1$ (immediate death).
   - **Mod-54, Mod-216 & Mod-1728 Quotient Floors:** Combining backward Mod-27 locks ($3 \le s(k-1)$) with forward 2-adic locks forces **$1735 \le u(k)$** at $s(k) = 2$, **$65 \le u(k)$** across $2 \le s(k) \le 6$, and **$103 \le u(k)$** on ceiling-saturated runs ($3 \le s(k) \le 6$ with $3 \le s(k+1)$).

---

## 6. Certified Transcendence & Diophantine Barriers (Why the General Case Remains Open)

A central contribution of this formalization is proving **exact algebraic conservation laws (Dead Ends 1–18)** that explain why every standard transcendence and Diophantine method falls just short on a general aperiodic sequence $s$:

### Barrier 1: Why Infinite Solutions Exist in $\mathbb{Z}_2 \times \mathbb{R}$ vs. Finite Positive Seeds (`TwoAdicCauchyConvergence.lean`, `MahlerSeriesHankelFramework.lean`, `FiniteSeedCarryAndBackwardDescent.lean`, `SubstitutionMahlerMethodAndGrandSynthesis.lean`)
The single power series $\Sigma_m(s) = \sum_{k=1}^m (2/3)^{T(k)+1} = \frac{2^{s(0)+1} R(s, m)}{3^{T(m)+1}}$ converges in **both** $\mathbb{R}$ (since $|2/3|_\infty = 2/3 < 1$) and $\mathbb{Q}_2$ (since $|2/3|_2 = 1/2 < 1$). Along any valid block chain (`dual_place_rational_limit_sign_split`):
$$0 < \Sigma_m(s) < \frac{1}{3}, \qquad -\frac{6a_0 + 2}{3} \le -\frac{2}{3} < 0, \qquad \Sigma_m(s) - \left(-\frac{6a_0 + 2}{3}\right) = \frac{2^{T(m+1)+1} u(m)}{3^{T(m)+1}}.$$
In $\mathbb{Z}_2 \times \mathbb{R}$, **infinite solutions genuinely exist** for every sequence $s$ with $\text{minSlack } s\ m > 0$: there is a unique 2-adic integer $\alpha_2 \in \mathbb{Z}_2$ and real companion $\alpha_\infty$ satisfying all congruences and archimedean bounds. For a **positive integer seed $a_0 \in \mathbb{N}$**, the rational partial sums $\Sigma_m(s) \in (0, 1/3)$ converge in $\mathbb{Q}_2$ to the negative rational $-\frac{6a_0+2}{3} < 0$. *(Scope note: because $\mathbb{R}$ and $\mathbb{Q}_2$ are distinct completions of $\mathbb{Q}$, opposite real signs of the archimedean and 2-adic limits are not by themselves a contradiction for an arbitrary aperiodic series; they yield an immediate algebraic contradiction only when the series is forced to represent a common rational or algebraic relation in both places, as in the periodic macro-block case below.)*
- **Periodic / Uniform Macro-Block Sign Obstruction (`periodic_macro_block_seed_divisibility`):** Whenever $s$ has uniform macro-block step sum $D$ and remainder $R_0$, the geometric series sums to the *same* positive rational $\frac{2^{s(0)+1} R_0}{3(3^D - 2^D)} > 0$ in both $\mathbb{R}$ and $\mathbb{Q}_2$, forcing $2^{D m} \mid \big((3^D - 2^D)(3a_0 + 1) + 2^{s(0)} R_0\big)$.
- **Concrete Resolution of the $G_{3,6}$ Product-Graph False Positive (`g3_6_false_positive_cycle_and_real_orbit`, `constant_three_block_chain_eight_pow_dvd`):** In `G_{3,6}`, the 3-cycle $(5,5) \to (4,2) \to (6,3) \to (5,5)$ ($s(k) = 3$) has valid fractional cycle $9/19 \to 4/19 \to 6/19 \to 9/19$ and 2-adic seed $a_0 = -9/19 \in \mathbb{Z}_2$, but any natural seed $a_0 \in \mathbb{N}$ must satisfy $8^m (19 b_m + 9) = 27^m (19 a_0 + 9)$, hence $8^m \mid (19 a_0 + 9)$ and $3 m \le W + 4$ for $a_0 < 2^W$.
- **Backward-Lifting Descent Dichotomy (`predecessor_lt_boundary`, `fracPart_backward_lift_identity`, `backward_archimedean_survival_dichotomy`):** Every predecessor block boundary $a = (2^c u - 1)/3$ satisfies $a < b = 3^{c-1} u$ and $r_a = 1/3 + (2/3)^c r_b$, with $1/3 \le r_a < 13/27 < 1/2$ holding **unconditionally** for every $c \ge 3$.

### Barrier 2: Rank-1 Determinant & Padé–Hankel Valuation Collapse (Dead Ends 12 & 18, `DeterminantFactorization.lean`, `MahlerSeriesHankelFramework.lean`)
When one forms the $2 \times 2$ determinant between steps $r$ and $r + d$ to eliminate $2a_0 + 1$ (either from the archimedean slacks $\Delta_k$ or from the 2-adic numerators $P_k = 2^{T(k+1)+1} u(k)$), the determinant factors identically as:
$$3^{T(r+d)} \Delta_r - 3^{T(r)} \Delta_{r+d} = 3^{T(r)} \cdot 2^{T(r+1)+1} \cdot R(\text{shiftSeq } s\ r,\, d),$$
$$3^{T(r)+1} P_{r+d} - 3^{T(r+d)+1} P_r = 3^{T(r)+1} \cdot 2^{T(r+1)+1} \cdot R(\text{shiftSeq } s\ r,\, d).$$
Because $\gcd(R^{(r)}_d, 6) = 1$, the 2-adic valuation of the determinant drops from $T(r+d+1) + 1$ all the way back to $T(r+1) + 1$, preventing Padé approximation from gaining a 2-adic advantage over a single step.

### Barrier 3: Baker–Matveev Linear Forms in Logarithms & Multi-Step GCDs (Dead Ends 13 & 17, `BakerMatveevFramework.lean`, `MultiStepQuotientGCD.lean`)
In `BakerMatveevFramework.lean`, we proved the exponentially small 3-logarithm linear form bounds:
$$0 < s(m+1)\log 2 - s(m)\log 3 + \log\!\left(\frac{u(m+1)}{u(m)}\right) < \frac{1}{3a_0 + 1}\left(\frac{2}{3}\right)^{T(m+1)},$$
$$0 < (T(m)+1)\log 3 - (T(m+1)+1)\log 2 + \log\!\left(\frac{2a_0+1}{u(m)}\right) \le \frac{1}{6a_0 + 2}\left(\frac{2}{3}\right)^{T(m)}.$$
When $u(m)$ is supported on a fixed finite set of primes ($S$-units), all algebraic bases are fixed, so invoking Matveev's external lower bound $\log|\Lambda| \ge -C(S, a_0)\log T(m)$ beats $-T(m)\log(3/2)$ and implies finiteness conditional on Matveev's theorem.
However, in the general case:
- Consecutive quotients are always coprime ($\gcd(u(m), u(m+1)) = 1$, `consecutive_u_coprime`).
- Across $d$ steps (`multi_step_u_gcd_eq_gcd_coprimeRemainder`), $\gcd(u(r), u(r+d)) = \gcd(u(r), R^{(r)}_d) < 3^{S_{r, d}} / 2^{s(r)+1}$.
- Even after canceling $\gcd(u(r), u(r+d))$, the reduced denominator satisfies $2^{T(r)} 3^{S_{r, d}} \big(u(r)/\gcd(u(r), u(r+d))\big) > 3^{T(r)}(3a_0 + 1)$ (`multi_step_reduced_denominator_exponential_lower_bound`).
Thus the logarithmic Weil height of the variable rational term grows linearly as $h \sim T(m)\log(3/2)$, causing Matveev's lower bound $-C_3 \cdot T(m)\log T(m)$ to lose to $-T(m)\log(3/2)$ by a factor of $\log T(m)$.

### Barrier 4: Ridout's Theorem & the Critical $Q_m^{-2}$ Exponent Identity (Dead End 14, `RidoutSubspaceFramework.lean`)
In the orbit equation $Q_m - P_m = \Delta_m$ with $Q_m = 3^{T(m)+1}(2a_0 + 1)$ and $P_m = 2^{T(m+1)+1} u(m)$, the $\{2, 3\}$-free part of $P_m$ is $u(m) \sim (3/2)^{T(m)}$ (with $2^{T(m)}$ in the denominator), while in any sub-ceiling phase $\Delta_m \le 2^{T(m)}$ (with $2^{T(m)}$ in the numerator). Multiplying $u(m)$ and $\Delta_m$ **cancels $2^{T(m)}$ identically** (`ridout_non_s_part_cancellation`):
$$2^{s(m) + D + 1} \cdot u(m) \cdot \Delta_m < 3^{T(m)+1}(2a_0 + 1) = Q_m.$$
Consequently, the 3-place $\{\infty, 2, 3\}$ Ridout product satisfies (`ridout_three_place_quadratic_bound`):
$$\left(1 - \frac{P_m}{Q_m}\right) \cdot \frac{u(m)}{P_m} \cdot \frac{2a_0 + 1}{Q_m} < \frac{(6a_0 + 3)(2a_0 + 1)}{2^{s(m)+1}(6a_0 + 2)} \cdot \frac{1}{Q_m^2}.$$
Because the three place exponents sum to **exact $2$**:
$$\underbrace{\left(1 - \frac{\log 2}{\log 3}\right)}_{|\cdot|_\infty} + \underbrace{\left(\frac{\log 2}{\log 3}\right)}_{|\cdot|_2} + \underbrace{1}_{|\cdot|_3} = 2,$$
the general bounded-block orbit sits **right on Ridout's critical $Q_m^{-2}$ boundary**, crossing below $Q_m^{-2 - \varepsilon}$ only when $s(m) \ge \delta T(m)$ or $\Delta_m \le 2^{(1-\delta)T(m)}$.

### Barrier 5: Multi-Origin Schlickewei Subspace Hyperplane Syzygy (Dead End 15, `MultiOriginSubspaceSyzygy.lean`)
Attempting to break the single-origin $Q_m^{-2}$ tangency by combining $k \ge 3$ shifted origins $(0, r_1, r_2, \dots)$ in Schlickewei's higher-dimensional $p$-adic Subspace Theorem fails because every scaled shifted slack $2^{T(r)} \Delta^{(r)}_{m-r}$ lies in the **same 2-dimensional plane** $\text{span}\{\Delta^{(0)}_m, 3^{T(m)}\}$ as $m \to \infty$. Any three origins $(0, r_1, r_2)$ satisfy the exact $m$-independent hyperplane syzygy (`three_origin_subspace_syzygy`):
$$D_0(r_2) \cdot 3^{T(r_1)} \big(2^{T(r_1)} \Delta^{(r_1)}_{m - r_1} - \Delta^{(0)}_m\big) = D_0(r_1) \cdot 3^{T(r_2)} \big(2^{T(r_2)} \Delta^{(r_2)}_{m - r_2} - \Delta^{(0)}_m\big),$$
landing identically inside the degenerate exceptional subspace of Schlickewei's theorem.

---

## 7. Architecture of the 140 Lean 4 Files & Verification

Every theorem in this repository is machine-checked in Lean 4.19.0 (`mahler_demand_a/`) without a single `sorry`. Each core module `Foo.lean` is paired with a verification module `FooChecks.lean` that runs `#check` and `#print axioms` on every exported theorem.

### Key Module Groups
- **Foundations & Odd-Block Reduction (Modules 1–36):** `MahlerDemandA.lean` through `TwoSidedSqueeze.lean` — basic Mahler step/orbit properties, companion intervals, odd-to-odd block reduction, `coprimeRemainder`, `integerSlack`, and initial two-sided squeezes.
- **1D Dynamical Collapse & Converse Reconstruction (Modules 37–52):** `SharpenedSqueezes.lean`, `AperiodicSlackCocycle.lean`, `MinSlackDynamicalSystem.lean`, `GlobalStepRateBounds.lean`, `BaseTwoDivModLock.lean`, `CeilingSaturationSynthesis.lean`, `TelescopingSeriesDuality.lean`, `ConverseCompanionReconstruction.lean`.
- **2-Adic LTE, Cauchy Convergence & Time-Independent Bounds (Modules 53–80):** `ExplicitHorizonCutoffs.lean`, `CeilingDeficitAmplification.lean`, `UniversalTwoVisitSeparation.lean`, `MonotonicStepSumSeparation.lean`, `CeilingSaturatedModTraps.lean`, `TwoAdicLiftingExponent.lean`, `FullStepSumValuation.lean`, `CoprimeRemainderAdditionLaw.lean`, `TwoAdicCauchyConvergence.lean`, `AllHistoryQuotientRecovery.lean`, `ParametricRemainderCorridor.lean`, `AperiodicBoundedBlockSqueeze.lean`, `TimeIndependentDeficiencySqueeze.lean`, `SlackDeadEndsAndWitnesses.lean`.
- **Record-Holder, Sieves, Aperiodic Exclusions & Finite-Seed Isolation (Modules 81–122):**
  - `MahlerGrandSynthesis.lean`: Equivalence `validBlockChain_iff_coprime_recurrence` and 113-step survival / 114-step death of `recordHolderA0 = 29871555608238677`.
  - `Mod256CompleteSieve.lean`, `CoprimeUnitRigidity.lean`, `DeterminantFactorization.lean`: Mod-256 two-block sieve, unit-sum rigidity, and rank-1 determinant collapse (Dead End 12).
  - `BakerMatveevFramework.lean`: Consecutive coprimality, 3-logarithm `Real.log` squeezes, and Weil height growth (Dead End 13).
  - `RidoutSubspaceFramework.lean`: Intrinsic $\gcd(\Delta_m, 6) = 1$, $2^{T(m)}$-cancellation law $2^{s(m)+1} u(m) \Delta_m < Q_m$, and $Q_m^{-2}$ Ridout bound (Dead End 14).
  - `MultiOriginSubspaceSyzygy.lean`: Additive separation of variables, shift-free `minSlack` equivalence, and 3-origin Subspace syzygy (Dead End 15).
  - `RepeatedSubwordComplexity.lean`: Strict quotient aperiodicity $u(r_1) < u(r_2)$, parity-enhanced common multiplier, and linear subword-complexity cutoffs.
  - `SimultaneousBaseDigitRigidity.lean`: Carryless Base-3 prefix equivalence and dual Base-2 / Base-3 remainder complementarity (Dead End 16).
  - `MultiStepQuotientGCD.lean`: Exact three-way multi-step GCD equality $\gcd(u(r), u(r+d)) = \gcd(u(r), R^{(r)}_d)$ and reduced-denominator exponential growth (Dead End 17).
  - `MahlerSeriesHankelFramework.lean`: Power-series functional equation and two-point Padé–Hankel determinant factorization (Dead End 18).
  - `ThreeAdicAndSeedGCDLocks.lean`, `CoupledFractionalPartDynamics.lean`, `Mod2304CombinedSieve.lean`, `TwoSidedCRTAndBackwardObstructions.lean`, `ThreeAdicValuationConservation.lean`, `Mod216TwoSidedQuotientFloor.lean`: Seed/slack GCD locks, 3-adic orbit factorization $b_{k+1} = 3^{s(k)-1} u(k)$, $\mu_2$ interval map, disjoint Lüroth–Markov partition, Mod-2304 / Mod-1728 / Mod-216 sieves, $u(k) \ne 1$ ($k \ge 1$), and 3-adic valuation conservation.
  - `InfiniteZNumberBridgeAndRationalBase.lean`: Ceiling-vs-floor odd-step proof, direct `Int.fract` finite/infinite companion equivalences, upstream `Int.fract` 113-step theorem, and rational-base $T_{3/2}$ deterministic subword exclusions.
  - `SturmianAndBalancedComplexityExclusion.lean`: $5:3$ and $17:10$ weighted repetition cutoffs, Finite Pigeonhole Principle on pattern classifiers, and exclusion of aperiodic ceiling-saturated $\{3,4\}$ / $[3,5]$ and weighted-balanced ($\delta \ge 1$, slope $\le (17-\delta)/10 \le 1.6$) block chains.
  - `FiniteSeedCarryAndBackwardDescent.lean`: $G_{3,6}$ false-positive cycle $(5,5)\to(4,2)\to(6,3)\to(5,5)$ vs. $8^m \mid (19 a_0 + 9)$ positive-seed cutoff, arithmetic block-parameter uniqueness, and backward-lifting descent dichotomy (`a < b`, `r_a = 1/3 + (2/3)^c r_b < 13/27` for $c \ge 3$).
  - `SubstitutionMahlerMethodAndGrandSynthesis.lean`: Dual-place partial-sum bounds (`0 < \Sigma_m < 1/3` vs. `-(6a_0+2)/3 \le -2/3 < 0`), closed-form uniform macro-block summation (`2^{Dm} \mid ((3^D-2^D)(3a_0+1) + 2^{s(0)} R_0)`), 3-point macro-block remainder syzygy, and `mahler_grand_122_module_synthesis`.
  - `EndpointCompactnessAndBalancedExclusion.lean`: Stage 0 perpetual finite survival supremum `supCompanion a_0 = ⨆ n, lowerBound a_0 n`, strict-vs-dyadic-endpoint shift alternative (`perpetual_finite_survival_endpoint_alternative`), and positive-real forward shift (`exists_positive_seed_ge_one_of_pos_companion`); standard prefix factor complexity equivalence `prefixFactorCount s L C ≤ C ↔ ∃ r1 < r2 ≤ C, ...` (`prefixFactorCount_le_iff_exists_repeated_subword`) and global factor complexity `globalFactorComplexity s L`; parameterized $(p, q)$ rational power bounds $3^q < 2^{p+q}$ ($q S + 1 \le p T + q W + p$); the **real logarithmic threshold selection bridge** (`exists_pq_of_lt_log_threshold` for every $\kappa \log(3/2) < \log 2$); the **asymptotic-mean ($T(n)/n \to \lambda > 0$), normalized maximum-discrepancy convergence ($E_H/H \to 0$), uniform-window-mean, and liminf-complexity exclusions** (`maxPrefixDiscrepancy_div_tendsto_zero`, `no_infinite_asymptotic_mean_liminf_subcritical_block_chain`, `no_infinite_tendsto_mean_log_threshold_block_chain`, `no_infinite_global_complexity_log_threshold_block_chain`, `tendsto_mean_of_uniformWindowMean`, `no_infinite_uniformWindowMean_global_complexity_block_chain`); the **scale-local balance exclusion without a global limiting mean (`no_infinite_scale_local_balanced_block_chain`) and unconditional exclusion of the concrete non-stationary oscillating-epoch family `nonStationaryEpochSeq a b` (`nonStationaryEpochSeq_no_limiting_mean`, `no_infinite_nonStationaryEpochSeq_block_chain`)**; and the **derived phase-threshold factor complexity bound $\le L + 1$** (`mechTwoLetterSeq_finset_factor_card_le`, `mechTwoLetterSeq_prefixFactorCount_le`) yielding the **assumption-free exclusion of arbitrary two-letter $\{a, b\}$ ($3 \le a \le b$) mechanical/Sturmian block chains** (`unconditional_mechanical_two_letter_finite_cutoff`, `no_infinite_mechanical_two_letter_block_chain`).
  - `ExactSeedResidueTreeAndStabilization.lean`: Stage 2 bidirectional parity-prefix bijection `(∀ n < N, orbit a n % 2 = orbit b n % 2) ↔ a % 2^N = b % 2^N`, constructive `seedResidue ε N < 2^N` and bit extension $r_{N+1} = r_N + \eta_N 2^N$, exact characterization of ordinary nonnegative/positive integer seeds by residue stabilization, canonical `FeasibleSeedNode` (`FeasibleSeedNode.eq_canonical`), full companion-set membership (`validCompanionUpTo_add_offset_iff_mem_ratInterval`), **denominator-cleared signed integer margin $D_{N+1} = \min(2^{N+1}, 3 D_N - 2^{N+1}(\varepsilon_N \bmod 2))$ (`signedMargin_cast_rat`, `validCompanionUpTo_iff_signedMargin_pos`), coupled quotient-residue-margin transition (`coupled_seedQuotient_and_margin_transition`), the 5-way general Mahler conjecture equivalence (`general_mahler_conjecture_iff_positive_stabilized_branch_escape`, `mahler_conjecture_iff_leastPositiveSurvivor_unbounded`), rank-certificate escape interface (`no_perpetual_feasible_stabilized_branch_of_rank_certificate`), scalar-margin `11`/`10101` contraction vs. `100` ceiling recovery (`signedMargin_10101_neg`, `signedMargin_100_ceiling_recovery`), Lean-certified step-28 survival / step-29 failure of seed `149` and global step-29 lower bound $m \ge 4096$ ($B(29) \ge 4096$) (`seed_149_survives_28_and_fails_29`, `positive_survivor_step29_ge_4096`, `leastPositiveSurvivor_certified_bounds`)**, single-block spike cutoff (`no_infinite_superLacunary_block_chain`), and the **well-founded odd-quotient descent ranking $u(m+1) + 2 \le u(m)$ and $u(m) = 1$ mod-8 trap** (`no_infinite_rapid_growth_block_chain`) excluding all rapid-growth chains with $3 \le s(m+1)$ and $3^{s(m)} < 2^{s(m+1)}$.
  - `ThueMorseMahlerFunctionalEquation.lean`: Stage 3 formalization of the Thue–Morse sequence (`tmBit (2k) + tmBit (2k+1) = 1`), its 3-step encoded Mahler stream (`0 ≤ fractionalTail ≤ 9/19 < 1/2`, 1 odd step per 6-step aligned window), closed finite and infinite Mahler functional equations $F(z) = (1-z)F(z^2) + \frac{z}{1-z^2}$ (`tmSeries_mahler_functional_equation`), 2-adic seed Mahler bridge `64^M ∣ (729^M (665 a_0 + 72) + 113715 * tmIntCarry 64 729 M)`, **unconditional non-eventual-periodicity** (`tmBit_not_eventually_periodic`, `tmEncodedParity_not_eventually_periodic`, `pdBit_not_eventually_periodic`, `pdEncodedParity_not_eventually_periodic`), **reusable dyadic-inflation repetition cutoff (`dyadic_inflated_repetition_cutoff`), finite seed cutoffs ($< 30 \cdot 2^k$ and $< 60 W$ for `tmEncodedParity`; $< 21 \cdot 2^k$ and $< 42 W$ for Period-Doubling `pdEncodedParity_cutoff_and_exclusion`), quantitative seed-residue lower bounds $\text{seedResidue}(\varepsilon, 30\cdot 2^k) \ge 2^{2^k}$ and bounded waiting window $[N_0, 60 N_0)$ for a forced nonzero extension bit (`seedResidue_tmEncodedParity_ge_two_pow`, `tmEncodedParity_forced_seedBit_in_sixty_mul_window`, `seedResidue_pdEncodedParity_ge_two_pow`), and unconditional exclusion of two-letter Thue–Morse block-length chains $s(n) = a + (b-a)t_n$ ($3 \le a \le b$) (`tmBlockSeq_finite_seed_cutoff`, `no_infinite_tmBlockSeq_block_chain`)**.
  - `SparseDefectCocycleAndValuationLock.lean`: Stage 4 signed single-block defect identity $2^{s(k)} I(b_{k+1}) = 3^{s(k)} I(b_k) + (9\cdot 2^{s(k)} - 8\cdot 3^{s(k)-1})$, constant 2-adic valuation $v_2(E(c)) = 3$ for all $c \ge 4$, iterated multi-block defect cocycle and its **proved explicit `Finset.sum` expansion (`defectCocycleSum_eq_finset_sum`)**, the **short local prefix derivation (`local_prefix_first_defect_valuation_lock`)** showing that the finite prefix up to the first defect $s(j_0) \ge 4$ after $j_0$ blocks of $3$ already forces $2^{3j_0+3} \mid (19a_0+9)$ and $2^{3j_0+4} \nmid (19a_0+9)$, multi-block valuation non-cancellation (`first_defect_valuation_lock_and_non_cancellation`), and the growing boundary invariant identity (`defectCocycle_residual_eq_growing_boundary_affInv`).

### Reproducing the Verification Build
```bash
cd mahler_demand_a
lake build
lake env lean -DwarningAsError=true EndpointCompactnessAndBalancedExclusionChecks.lean
lake env lean -DwarningAsError=true ExactSeedResidueTreeAndStabilizationChecks.lean
lake env lean -DwarningAsError=true ThueMorseMahlerFunctionalEquationChecks.lean
lake env lean -DwarningAsError=true SparseDefectCocycleAndValuationLockChecks.lean
```

---

## Acknowledgments

This research and its 140-file Lean 4 formalization were developed by Joshua Coon with the assistance of the **Astra** and **Argon** AI models in GitHub Copilot.

---

## References

1. **K. Mahler (1968),** *"An unsolved problem on the powers of $3/2$,"* Journal of the Australian Mathematical Society **8**, 313–321.
2. **D. Ridout (1957),** *"Rational approximations to algebraic numbers,"* Mathematika **4**, 125–131.
3. **T. Vijayaraghavan (1940),** *"On the fractional parts of the powers of a number (I),"* Journal of the London Mathematical Society **15**, 159–160.
4. **A. D. Pollington (1979),** *"On the density of sequence $\{\theta^k\}$,"* Illinois Journal of Mathematics **23**, 511–515.
5. **G. Choquet (1980),** *"$\theta$-fermés et dimension de Hausdorff. Conjectures de travail. Arithmétique des $\theta$-cycles (où $\theta = 3/2$),"* Comptes Rendus de l'Académie des Sciences Paris Sér. A–B **290**, A863–A868.
6. **L. Flatto, J. C. Lagarias, and A. D. Pollington (1995),** *"On the range of fractional parts $\{\xi (p/q)^n\}$,"* Acta Arithmetica **70**, 197–227.
7. **H. P. Schlickewei (1977),** *"The $\mathfrak{p}$-adic Thue–Siegel–Roth–Schmidt theorem,"* Archiv der Mathematik **29**, 267–270.
8. **C. L. Stewart (1980),** *"On the representation of an integer in two different bases,"* Journal für die reine und angewandte Mathematik **319**, 63–72.
9. **A. Baker and G. Wüstholz (1993),** *"Logarithmic forms and group varieties,"* Journal für die reine und angewandte Mathematik **442**, 19–62.
10. **E. M. Matveev (2000),** *"An explicit lower bound for a homogeneous rational linear form in the logarithms of algebraic numbers. II,"* Izvestiya: Mathematics **64**, 1217–1269.
11. **P. Corvaja and U. Zannier (2002),** *"Some new applications of the Subspace Theorem,"* Compositio Mathematica **131**, 319–340.
12. **P. Corvaja and U. Zannier (2003),** *"On the greatest prime factor of $(a b + 1)(a c + 1)$,"* Proceedings of the American Mathematical Society **131**, 1705–1709.
13. **B. Adamczewski and Y. Bugeaud (2007),** *"On the complexity of algebraic numbers I. Expansions in integer bases,"* Annals of Mathematics **165**, 547–565.
14. **A. Dubickas (2006),** *"On the distance from a rational power to the nearest integer,"* Journal of Number Theory **117**, 222–239.
15. **The Formal Conjectures Authors (Google DeepMind, 2025–2026),** *"Formal Conjectures in Lean 4: `Mahler32.lean`, `Problem10_9.lean`, and `ZNumber.lean`,"* `https://github.com/google-deepmind/formal-conjectures`.
16. **S. Akiyama, C. Frougny, and J. Sakarovitch (2008),** *"Powers of rationals modulo 1 and rational base number systems,"* Israel Journal of Mathematics **168**, 53–91.
17. **M. Andrieu, S. Eliahou, and L. Vivion (2025),** *"A Normality Conjecture on Rational Base Number Systems,"* `arXiv:2510.11723`.
