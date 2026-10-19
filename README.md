# Mahler $3/2$ Problem — 142-File Lean 4 Formalization (`mahler_demand_a`)

This repository contains a **142-file (`sorry`-free) Lean 4.19.0 + Mathlib v4.19.0 formalization** of the reduced Mahler $3/2$ dynamical system ($Z$-numbers) and its interval- and union-confinement relaxations ([`MAHLER_FORMALIZATION_PAPER.pdf`](./MAHLER_FORMALIZATION_PAPER.pdf)).

---

## Plain-English Overview: The Big Picture & How Fractals Play In

Before diving into the technical theorems and Lean module index below, here is a plain-English guide to what Mahler’s problem actually is, why Cantor fractals appear inside it, and where this project stands today.

### 1. The Game We Are Playing (Mahler’s $3/2$ Problem)

Imagine a simple game on a calculator:
1. Pick any starting number (say, $x_0 = 8$).
2. At every turn, **multiply by $1.5$** (which is $\frac{3}{2}$).
3. Look at the **decimal part** (the fractional part after the decimal point, between $0$ and $1$).

Mahler’s original question (from 1968) is:
> **Is there any starting number whose decimal part stays below $0.5$ forever?**

Every turn you multiply by $1.5$, the decimal part gets stretched by $1.5\times$ (and wraps around if it passes $1$). Because $1.5$ is an awkward multiplier relative to $1$, the decimal part usually bounces around chaotically and eventually lands above $0.5$.
- **A "$Z$-number"** is a mythical starting number that somehow dodges the upper half $[0.5, 1)$ at **every single step forever**.
- **Nobody knows** if a $Z$-number exists for $[0, 0.5)$. That full question remains open worldwide.

### 2. Why Does a Fractal (Cantor Set) Appear?

Instead of asking *"Can a number stay in $[0, 0.5)$ forever?"*, researchers (such as Dubickas, Stephan, and Gareth) also study a closely related question:
> **What if we change the "safe zone" from $[0, 0.5)$ to a shifted interval—say, the middle window $(2/7, 5/7) \approx (0.286, 0.714)$—or a collection of separate islands?**

Watch what happens when you try to keep a number inside a safe zone turn after turn:

* **Turn 0:** Your decimal part has to start inside the safe zone (1 solid bar).
* **Turn 1:** When you multiply by $1.5$, the middle of that bar gets stretched **outside** the safe zone and dies. Only **2 smaller sub-bars** (one on the left, one on the right) survive Turn 1.
* **Turn 2:** Each of those 2 sub-bars gets stretched by $1.5$ again. Their middles die, leaving **4 even tinier bars**.
* **Turn 3:** Those split and get clipped again, leaving **6 tiny bars**, then **10**, then **14**, then **20**...

If you draw the surviving safe spots at Step 1, Step 2, Step 3, Step 4..., **you are literally carving out a Cantor fractal**:

```text
Step 0 (start):   [========================]   (1 bar)
Step 1:           [========]      [========]   (2 bars)
Step 2:           [===]  [===]  [===]  [===]   (4 bars)
Step 3:           [=] [=]  [=]  [=]  [=] [=]   (6 bars)
...
Step ∞:            .   .    .    .    .   .    (fractal dust!)
```

Here is the crucial difference between a **real number** (a continuous decimal) and a **whole-number Mahler orbit**:
1. **In pure geometry (real numbers):** If you keep carving out middles forever, you can still have an infinite "fractal dust" of points left over at Step $\infty$.
2. **In Mahler’s problem (whole-number powers):** Every time you multiply by $\frac{3}{2}$, the denominator grows by a power of $2$ ($\frac{1}{2}, \frac{1}{4}, \frac{1}{8}, \frac{1}{16}\dots$). That means at Step $d$, your number **must sit on a rigid grid of spacing $\frac{1}{2^d}$**.

So a number can only survive if **the surviving fractal bars are wide enough and lined up well enough to catch grid points at every single step**.

### 3. What We Discovered About That Fractal

When we analyzed the centered safe zone $[c, 1-c]$ (such as $(2/7, 5/7)$) in [`DubickasConfinementAndComplexityExtension.lean`](./DubickasConfinementAndComplexityExtension.lean), we found out *why* the $(2/7, 5/7)$ problem was so tricky:

1. **The Period-Doubling Cascade (Chaos Theory in Disguise):**
   As you widen the centered window $[c, 1-c]$ by shrinking $c$ down toward $0.25$:
   - At $c_1 = 2/5 = 0.4000$: a 2-step loop appears.
   - At $c_2 = 4/13 \approx 0.3077$: it splits into a 4-step loop.
   - At $c_3 = 28/97 \approx 0.2887$: it splits into an 8-step loop.
   - At $c_4 = 1948/6817 \approx 0.285756$: it splits into a 16-step loop.
   - At $c_5 = 12314908/43112257 \approx 0.2856475$: it splits into a 32-step loop.
   - At $c_\infty \approx 0.2856473$: it hits the **Thue–Morse fractal limit**, where infinitely many loops exist!

2. **Why $(2/7, 5/7)$ Was Such a Close Call:**
   Notice where $2/7 \approx 0.285714$ sits: **right between Step 4 ($c_4 \approx 0.285756$) and Step 5 ($c_5 \approx 0.2856475$)**.
   - For the first **15 steps** ($d = 0$ to $15$), the fractal for $(2/7, 5/7)$ acts **exactly** as if it were the full infinite fractal—the number of surviving bars (`1, 2, 4, 6, 10, 14, 20, 26, 36, 46, 60, 74, 94, 114, 140, 166`) follows Mahler’s classic binary partition sequence $B(d) = B(d-1) + B(\lfloor d/2 \rfloor)$.
   - Then, at **Step 16**, the boundary $2/7$ finally clips off the 5th period-doubling branch ($200$ bars survive instead of $202$).
   - Once that 5th branch is clipped, the fractal stops growing fast and slows down to polynomial growth ($\Theta(d^3)$), which is **too thin** to hide a Mahler orbit forever.

3. **Why Our Proof Method Beats Brute-Force Fractal Carving:**
   If you try to prove a safe zone is empty just by tracking the fractal bars (the "interval certificate" method), you get stuck at $c_\infty \approx 0.2856473$ because the fractal dust never disappears.
   Our approach adds a **second weapon (2-adic divisibility)**: even when a point stays inside the fractal dust on a repeating loop, the $\frac{3}{2}$ multiplier forces the whole number to be divisible by higher and higher powers of $2$ until the number would have to be infinitely large—which is impossible! That is how we push all the way past $c_\infty$ down to $0.25$.

### 4. Where the Project Stands Right Now (Scorecard)

Every result below is 100% computer-verified in Lean 4 (zero `sorry`s, standard axioms only) and documented in [`MAHLER_FORMALIZATION_PAPER.pdf`](./MAHLER_FORMALIZATION_PAPER.pdf):

| Part of the Project | What It Means in Plain English | Status |
| :--- | :--- | :--- |
| **1. The Original $[0, 0.5)$ Problem** | Can a number stay in the bottom half $[0, 0.5)$ forever? | **Still Open Worldwide.** We proved that *if* a culprit exists, it must follow an extraordinarily rigid "staircase" of near-misses (Sections 2–5 of the paper & Section 11's general $g$-rung ladder), and we ruled out all repeating and low-complexity patterns—but a completely chaotic culprit is not ruled out yet. |
| **2. Single Safe Zones (Width up to $0.5$)** | What if we shift the safe zone away from $0$, like $[0.25, 0.75)$ or $[1/3, 5/6)$? | **Completely Solved & Formalized.** Not only did we prove no number stays inside forever, we proved an exact **speed limit**: any number with $W$ binary digits must get kicked out in at most **$W + \text{constant}$ steps** (e.g., $W + 5$ steps for $(2/7, 5/7)$). |
| **3. Multi-Island Safe Zones (Width $> 0.5$, up to $69.4\%$)** | What if the safe zone is 5 or 6 separate islands covering **nearly $70\%$ of the entire number line** ($25/36 \approx 69.4\%$)? | **Completely Solved & Formalized.** Even when the safe zone covers $69.4\%$ of $[0,1)$, any $W$-bit number gets funneled and kicked out in at most **$W + 16$ steps**. |
| **4. Other Multiplier Games (like $4/3$, $5/3$, general $p/q$)** | Does our method work if you multiply by $\frac{4}{3}$ or $\frac{p}{q}$ instead of $\frac{3}{2}$? | **Completely Solved & Formalized.** We proved the general logarithmic complexity threshold for all bases $p/q$ and broke the $1/4$ barrier for base $4/3$ with a 4-line human-readable proof on $[1/3, 5/8)$. |
| **5. The Fractal Cascade on $[c, 1-c]$** | Why do interval searches explode near $2/7$, and how do the fractals behave? | **Completely Solved & Formalized.** We proved the exact formula for every period-doubling threshold $c_k$, why $(2/7, 5/7)$ splits at Step 16, and how the fractal structure works. |

**Bottom Line:** Think of Mahler's original $[0, 0.5)$ problem as the **summit of Mount Everest**. Nobody has reached the summit of $[0, 0.5)$ yet because the boundary at $0$ acts like a "trapdoor" where powers of $3/2$ can linger without repeating. However, we mapped the exact geometry of that trapdoor (the $g$-rung staircase ladder), **and** we conquered the surrounding peaks—showing with machine-checked certainty that shifted windows up to width $0.5$, multi-island unions covering nearly $70\%$ of the line, and the entire Thue–Morse fractal cascade cannot hide a $Z$-number.

---

## Technical Summary of Formalized Contributions

This repository formalizes:

- **Exact 1D Dynamical Reduction, Infinite-Horizon Bridge & Perpetual Endpoint Alternative:** Equivalence between the existence of a real Mahler companion (in both nested-interval and direct `Int.fract` form) and the 1D `minSlack` recurrence (`ConverseCompanionReconstruction.lean`, `InfiniteZNumberBridgeAndRationalBase.lean`), together with the supremum construction `supCompanion a_0 = ⨆ n, lowerBound a_0 n` proving that perpetual finite survival implies either strict infinite survival of $a_0$ or a unique dyadic upper-endpoint hit at step $j$ followed by strict infinite survival of the shifted positive seed $\text{orbit } a_0\ (j+1)$, plus the global forward-shift reduction `exists_positive_seed_ge_one_of_pos_companion` from any $\alpha > 0$ to $\beta \ge 1$ and $b_0 \ge 1$ (`EndpointCompactnessAndBalancedExclusion.lean`). Also includes the shift-free ceiling comparison (`MultiOriginSubspaceSyzygy.lean`), the carryless Base-3 frozen-prefix condition (`SimultaneousBaseDigitRigidity.lean`), and the normalized 1D slack update $\mu_2(s, m+1) = \min\big(1,\, (3/2)^{s(m)} \mu_2(s, m) - 2\big)$ on $(0, 1]$ driven by the arithmetic-controlled block length $s(m) = v_2(3 b_m + 1)$ (`CoupledFractionalPartDynamics.lean`, `FiniteSeedCarryAndBackwardDescent.lean`).
- **Constructive Survivors & 113-Step Record-Holder:** Closed-form arbitrary-length pre-exit survivors (`ExplicitHorizonCutoffs.lean`) and machine-checked **113-step survival / 114-step death** of the 55-bit integer `recordHolderA0 = 29871555608238677 < 2^55` in both interval and `Int.fract` formats (`MahlerGrandSynthesis.lean`, `InfiniteZNumberBridgeAndRationalBase.lean`).
- **Unconditional Exclusion of Mechanical, Balanced, Asymptotic-Mean, Scale-Local Non-Stationary & Uniform-Window-Mean Classes:** Time-independent bounded-block escape ceilings (`TimeIndependentDeficiencySqueeze.lean`), parameterized $(p, q)$ rational power cutoffs $3^q < 2^{p+q}$ ($q S + 1 \le p T + q W + p$), the **real logarithmic threshold selection bridge** (`exists_pq_of_lt_log_threshold` for every $\kappa \log(3/2) < \log 2$, i.e. $\kappa < 1/\log_2(3/2) \approx 1.709511$), the **asymptotic-mean ($T(n)/n \to \lambda > 0$), normalized discrepancy convergence ($E_H / H \to 0$), global factor complexity $P(L)$, and liminf-complexity exclusions** (`maxPrefixDiscrepancy_div_tendsto_zero`, `no_infinite_global_complexity_log_threshold_block_chain`, `tendsto_mean_of_uniformWindowMean`, `no_infinite_uniformWindowMean_global_complexity_block_chain`), the **scale-local balance exclusion without a global limiting mean** (`no_infinite_scale_local_balanced_block_chain`) together with the concrete oscillating-epoch family `nonStationaryEpochSeq a b` proved to have no limiting Cesàro mean (`nonStationaryEpochSeq_no_limiting_mean`) and no infinite block chain (`no_infinite_nonStationaryEpochSeq_block_chain`), and the **derived phase-threshold factor complexity bound $\le L + 1$** (`mechTwoLetterSeq_finset_factor_card_le`, `mechTwoLetterSeq_prefixFactorCount_le`) yielding the complete **assumption-free exclusion of arbitrary two-letter $\{a, b\}$ ($3 \le a \le b$) mechanical/Sturmian block chains** (`no_infinite_mechanical_two_letter_block_chain` in `EndpointCompactnessAndBalancedExclusion.lean`). Also includes Two-Sided Chinese Remainder Sieves (`Mod256CompleteSieve.lean`, `Mod2304CombinedSieve.lean`, `Mod216TwoSidedQuotientFloor.lean`) and 3-adic valuation conservation (`ThreeAdicValuationConservation.lean`).
- **Exact Coupled Seed-Residue State, Certified $B(29) \ge 4096$ Bound, Quantitative Thue–Morse & Period-Doubling Exclusions & Local Prefix Defect Locks:**
  - **Exact Coupled Seed-Residue State, Signed Integer Margin $D_N$ & Certified $4096$ Bound (`ExactSeedResidueTreeAndStabilization.lean`):** Bidirectional parity-prefix bijection `(∀ n < N, orbit a n % 2 = orbit b n % 2) ↔ a % 2^N = b % 2^N`, constructive `seedResidue ε N < 2^N`, canonical `FeasibleSeedNode` with enforced equality invariants (`FeasibleSeedNode.eq_canonical`), full companion-set membership (`validCompanionUpTo_add_offset_iff_mem_ratInterval`), denominator-cleared signed integer margin $D_{N+1} = \min(2^{N+1},\, 3 D_N - 2^{N+1}(\varepsilon_N \bmod 2))$ (`signedMargin_cast_rat`, `validCompanionUpTo_iff_signedMargin_pos`), coupled quotient-residue-margin transition (`coupled_seedQuotient_and_margin_transition`), the **5-way general Mahler conjecture equivalence** (`general_mahler_conjecture_iff_positive_stabilized_branch_escape`, `mahler_conjecture_iff_leastPositiveSurvivor_unbounded`), rank-certificate escape interface (`no_perpetual_feasible_stabilized_branch_of_rank_certificate`), scalar-margin `11`/`10101` contraction vs. `100` ceiling recovery (`signedMargin_10101_neg`, `signedMargin_100_ceiling_recovery`), **Lean-certified step-28 survival / step-29 failure of seed `149` and global step-29 lower bound $m \ge 4096$ ($B(29) \ge 4096$)** (`seed_149_survives_28_and_fails_29`, `positive_survivor_step29_ge_4096`, `leastPositiveSurvivor_certified_bounds`), single-block spike cutoffs (`no_infinite_superLacunary_block_chain`), and the **well-founded odd-quotient descent ranking $u(m+1) + 2 \le u(m)$ and $u(m) = 1$ mod-8 trap** (`no_infinite_rapid_growth_block_chain`).
  - **Quantitative Thue–Morse Seed-Bit Forcing, Block-Length Coding & Period-Doubling Exclusion (`ThueMorseMahlerFunctionalEquation.lean`):** Closed finite and infinite Mahler functional equations $F(z) = (1-z)F(z^2) + \frac{z}{1-z^2}$, unconditional non-eventual-periodicity (`tmBit_not_eventually_periodic`, `tmEncodedParity_not_eventually_periodic`, `pdBit_not_eventually_periodic`, `pdEncodedParity_not_eventually_periodic`), reusable dyadic-inflation repetition cutoff (`dyadic_inflated_repetition_cutoff`), explicit finite seed cutoffs (`< 30 * 2^k` and `< 60 * W` for `tmEncodedParity`; `< 21 * 2^k` and `< 42 * W` for the Period-Doubling encoding `pdEncodedParity_cutoff_and_exclusion`), **quantitative seed-residue lower bounds $\text{seedResidue}(\varepsilon, 30\cdot 2^k) \ge 2^{2^k}$ and bounded waiting window $[N_0, 60 N_0)$ for a forced nonzero extension bit $\eta_N = 1$** (`seedResidue_tmEncodedParity_ge_two_pow`, `tmEncodedParity_forced_seedBit_in_sixty_mul_window`, `seedResidue_pdEncodedParity_ge_two_pow`), and **unconditional exclusion of two-letter Thue–Morse block-length chains $s(n) = a + (b-a)t_n$ ($3 \le a \le b$)** (`tmBlockSeq_finite_seed_cutoff`, `no_infinite_tmBlockSeq_block_chain`).
  - **Signed Defect Cocycle & Local Prefix Valuation Lock (`SparseDefectCocycleAndValuationLock.lean`):** Signed single-block and explicit `Finset.sum` multi-block defect cocycle (`defectCocycleSum_eq_finset_sum`), constant 2-adic valuation $v_2(E(c)) = 3$ for $c \ge 4$, and both the multi-block non-cancellation proof and the **short local prefix derivation** (`local_prefix_first_defect_valuation_lock`) showing that the finite prefix up to the first defect $s(j_0) \ge 4$ after $j_0$ blocks of $3$ already forces $2^{3j_0+3} \mid (19a_0+9)$ and $2^{3j_0+4} \nmid (19a_0+9)$.
  - **Quantitative Extensions of Dubickas (2008 / 2009) on Shifted Carry Words & Explicit $O(\log \xi)$ Confinement Escape Bounds (`DubickasConfinementAndComplexityExtension.lean`):** Formalizes the shifted carry word $s_n = 2\lfloor \xi(3/2)^{n+1} + \theta \rfloor - 3\lfloor \xi(3/2)^n + \theta \rfloor$ and the general coprime rational base version $s_n = q x_{n+1} - p x_n$ (`dubBaseCarry_eq_fract_linear`, `dubBaseY_multi_step_carry_identity`, `dubBaseX_repeated_window_exp_and_power_cutoff`), proves the universal two-letter alphabet $s_n \in \{\lfloor(p-q)s\rfloor, \lfloor(p-q)s\rfloor+1\}$ (`dubBaseCarry_mem_two_letters`), the general-base no-bispecial-pair property (`dubBaseCarry_no_bispecial_pair`), and the finite bispecial-free binary complexity bound $\operatorname{prefixFactorCount}(w, L, C) \le L + 1$ (`prefixFactorCount_le_add_one_of_no_bispecial`, `dubBaseCarryNat_prefixFactorCount_le`) to establish **the full general-base Dubickas (2009) Theorem 1 for all coprime $1 < q < p < q^2$ across all $s \in [0, 1 - 1/p]$ (`dubickas2009_general_base_explicit_and_infinite_escape`), its strictly linear-in-$W$ bound $N \le 2bW + 2a + 2$ (`dubickas2009_general_base_linear_in_W_escape`), and the sharp $5W + 14$ escape bound at base $3/2$ (`shifted_third_unconditional_explicit_escape`)**; proves **general-base floor-residue non-stabilization $\lfloor \xi(p/q)^n \rfloor \bmod m$ for all coprime $1 < q < p < q^2$ and $m \ge p$ (`general_base_floor_mod_non_stabilization`, `floor_mod_non_stabilization_of_three_le`)**; proves a **universal infinite-family single-cell theorem covering the open regime $p > q^2$ ($p \ge 2q$, `general_base_non_straddling_cell_escape`)**; upgrades Dubickas's Sturmian carry-word endgame ($\kappa = 1$) to the **general-base critical threshold $\kappa < \log q / \log(p/q)$ for all coprime $2 \le q < p$ (`exists_ab_of_lt_general_log_threshold`, `no_subcritical_general_log_threshold_dubBaseCarry`, and $\kappa < \log 2 / \log(3/2) \approx 1.709511$ at base $3/2$ in `no_subcritical_log_threshold_dubCarry`)**; and establishes **explicit $O(W) = O(\log \xi)$ finite-horizon escape bounds and infinite-horizon eventual escape** for: (i) the nearest-integer arc $\|\xi(3/2)^n\| < 1/5$ ($n \le W + 5$), (ii) the beyond-$1/3$ single window $[1/6, 13/24)$ of length $3/8 > 1/3$ at base $3/2$ ($n \le W + 15$) and the **beyond-$1/4$ single window $[1/3, 5/8)$ of length $7/24 > 1/4 = 1/p$ at base $4/3$ ($n \le W + 8$, `base_four_three_beyond_quarter_explicit_and_infinite_escape`)**, (iii) **Dubickas's 2008 closed union $[8/39, 18/39] \cup [21/39, 31/39]$ of total length $20/39 > 1/2$** ($n \le W + 8$ on the open union, $n \le 3W + 19$ on the closed union, and direct $2^m \mid (13 x_r + v_r)$ divisibility on the rational 4-cycle), and (iv) **increasingly large unions above $1/2$ via our verified backward-forward integer funnel engine (`inRatIntervalList_terminal_of_funnelChainOk`, `inRatIntervalList_next_of_forwardStepOk`)**: the 4-interval union $U_{7/12}$ of total length $7/12 \approx 0.5833$ ($n \le W + 12$), the **5-interval union $U_{2/3}$ of total length $2/3 \approx 0.6667$ ($n \le W + 14$, `union_two_thirds_explicit_and_infinite_escape`)**, and the **6-interval union $U_{25/36}$ of total length $25/36 \approx 0.6944 > 2/3 > 1/2$ ($n \le W + 16$, `union_twenty_five_thirty_sixths_explicit_and_infinite_escape`)**; and formalizes the **Thue–Morse period-doubling Cantor cascade on $[c, 1-c]$** (proving the Fermat-denominator reduction $3^{2^{k-1}} + 2^{2^{k-1}}$, the closed-form entry thresholds $c_k$, the difference-of-squares step ratio, the $[2/7, 5/7]$ cutoff $c_5 < 2/7 < c_4$, and the exact match between the $(2/7, 5/7)$ Cantor cylinder tree and Mahler's binary partition sequence $B(d)$ through depth $15$ before the $k=5$ truncation at depth $16$ in `cantorTwoSevenths_matches_mahlerBinaryPartition_up_to_15_and_splits_at_16`) together with the **general gap-$g$ window ladder ($1/3 < \alpha_g < \beta_g < 1/2$ for all $g \ge 3$) and general $g$-rung first-defect valuation lock $v_2((3^g-2^g)a_0 + 3^{g-1}) = g(j_0+1)$** (`rungAlpha_lt_rungBeta_lt_half`, `gap_ladder_short_gap_cost_and_cap`, `general_rung_first_defect_valuation_lock`).

For a complete, human-readable mathematical exposition of our results and barrier analyses, see **[MAHLER_FORMALIZATION_PAPER.pdf](./MAHLER_FORMALIZATION_PAPER.pdf)** (and the synchronized Markdown/LaTeX sources **[MAHLER_FORMALIZATION_PAPER.md](./MAHLER_FORMALIZATION_PAPER.md)** / **[MAHLER_FORMALIZATION_PAPER.tex](./MAHLER_FORMALIZATION_PAPER.tex)**).

## Acknowledgments

Developed by Joshua Coon with the assistance of the **Astra** and **Argon** AI models in GitHub Copilot.

## Building & Verifying

Requires **Lean 4.19.0** (`leanprover/lean4:v4.19.0`):

```bash
lake build
```
