# Research plan for Argon: toward a resolution of Mahler's Z-number problem

Date: 2026-11-01

**Status:** proposed research, not a proof or a prediction that a proof is close.
This plan follows the [integer-seed research outline](./RESEARCH_OUTLINE_SEED_ESCAPE_AND_RECURRENCE.md)
and the subsequent review of the [paper's final conclusions](./MAHLER_FORMALIZATION_PAPER.md).
The Lean declarations, rather than older planning documents or theorem names,
are the authority for what has already been established.

## Executive brief

Argon: aim to resolve the general problem, not to accumulate more identities,
larger fixed divisors, or exclusions of selected symbolic sequences.

1. Audit the claimed reductions before assuming there is only one remaining
   trajectory family.
2. Reuse the exact seed-residue and signed-margin framework already implemented.
3. Investigate the exact base-6 multiplication automaton as a way to retain
   the finite integer-side boundary that unrestricted symbolic methods lose.
4. As a lower-cost alternative, investigate a finite parity-surplus target;
   do not set out to prove full normality unless weaker targets require it.
5. Require an all-scale induction, a well-founded certificate, or another
   genuinely pointwise arithmetic obstruction before claiming general progress.

These are plausible research programs, not known missing lemmas that can
necessarily be proved. Refuting a proposed lemma is a useful outcome. If the
program stalls, report the precise obstruction rather than announcing either
that Mahler is solved or that every possible method must fail.

## 1. Fix the exact finish line

The desired nonexistence theorem is

\[
  \forall \alpha\in\mathbb R,\quad
  \alpha>0 \Longrightarrow
  \exists n\in\mathbb N:\ \{\alpha(3/2)^n\}\geq 1/2.
\]

The initial real number need not be an integer or rational. The ordinary
integer **seed** is its integer part, after shifting forward if necessary.
Do not solve the easier problem of integer starting real numbers instead.

The [exact seed-residue module](./ExactSeedResidueTreeAndStabilization.lean)
already supplies two suitable completion interfaces:

- `general_mahler_conjecture_iff_positive_stabilized_branch_escape`:
  every perpetually feasible branch must either have zero seed or fail to
  stabilize at any positive ordinary integer.
- `mahler_conjecture_iff_leastPositiveSurvivor_unbounded`:
  if \(B(N)\) is the least positive integer seed admitting a companion through
  horizon \(N\), the conjecture is equivalent to
  \[
    \forall M\in\mathbb N,\ \exists N\in\mathbb N:\ M\leq B(N).
  \]

**Any proved unbounded growth is enough.** Neither an exponential lower bound
on \(B(N)\) nor an \(O(\log a)\) escape time is necessary. Bounds along a
sufficiently sparse sequence of horizons are enough.

If research instead produces a candidate Z-number, retain that possibility.
A counterexample requires a positive real construction and a proof of the
strict inequality at every time; arbitrarily long finite survival is not one.

## 2. Phase A: audit the mathematical coverage

### A1. Build a claim-to-theorem matrix

For each advertised reduction, record: its exact statement, hypotheses,
upstream source of each hypothesis, and the family still not covered.
Do this before extending the large confinement module.

| Claim needing attention | Required check |
| --- | --- |
| Only bounded-run dense-core trajectories remain | Derive the dense-core and bounded-run hypotheses from a general hypothetical survivor, or leave other families explicitly open. Confinement to \([8/81,1/2)\) is not automatic from confinement to \([0,1/2)\). |
| All subexponential or \(p(N)<(3/2)^N\) complexity is excluded | The cited `no_subcritical_log_threshold_dense_core` concerns specified **linear** complexity bounds. Do not replace \(p(N)\leq\kappa N+C\) by an exponential threshold. |
| All unbounded or sparse runs are excluded | Distinguish unboundedness from the sustained growth/contraction inequalities assumed by the descent theorems. Intermittent expansion may undo descent. |
| The final capstone is an exhaustive reduction | Inspect its conjunctions and antecedents. Matching conditions and a large endpoint-state hypothesis must be proved, not inferred from the theorem's name. |
| Vanishing measure or a large computed seed floor closes the problem | Neither excludes a single exceptional positive integer seed. |

Principal source:
[DubickasConfinementAndComplexityExtension.lean](./DubickasConfinementAndComplexityExtension.lean).
An omitted bridge is a gap in coverage, not evidence that Lean proved a false
implication.

### A2. Do not redo completed milestones

The current [seed-residue module](./ExactSeedResidueTreeAndStabilization.lean)
already contains enforced canonical node invariants, the coupled transition,
the general equivalences, and certified bounds including \(B(29)\geq4096\).
Some older outlines list these as future work. Check current declarations
before implementing anything.

Start with the pinned [toolchain](./lean-toolchain) and
[Lake targets](./lakefile.toml). A focused baseline, from the project directory:

```powershell
lake build ExactSeedResidueTreeAndStabilizationChecks GlobalStepRateBoundsChecks InfiniteZNumberBridgeAndRationalBaseChecks
```

Build additional confinement targets only when the selected route depends on
them. Record failures without silently upgrading Lean or Mathlib.

**Exit gate A:** an honest coverage matrix and a working baseline. If the
dense-core reduction is incomplete, the main route below must start from the
general seed interface, not assume the missing classification.

## 3. Common arithmetic state: keep the finite seed visible

For a binary parity stream \(e_n\), use the existing quantities

\[
\begin{aligned}
 C_0&=0,& C_{n+1}&=3C_n+2^n e_n,\\
 D_0&=1,& D_{n+1}&=\min(2^{n+1},\,3D_n-2^{n+1}e_n).
\end{aligned}
\]

Here \(D_n\) is a **signed integer**. Its positivity is exactly finite
companion feasibility. Never replace negative values by truncated natural
subtraction.

Let \(r_n\) be the canonical least seed residue and \(q_n\) its orbit quotient.
The [proved coupled transition](./ExactSeedResidueTreeAndStabilization.lean)
is

\[
\begin{aligned}
 e_n&=(q_n+\eta_n)\bmod2,\\
 r_{n+1}&=r_n+\eta_n2^n,\qquad \eta_n\in\{0,1\},\\
 2q_{n+1}&=3q_n+3^{n+1}\eta_n+e_n,\\
 2^nq_n&=3^nr_n+C_n.
\end{aligned}
\]

For a fixed \(0<a<2^W\), its actual orbit has \(r_n=a\) and \(\eta_n=0\)
for \(n\geq W\). Thereafter the exact continuation is

\[
 e_n=q_n\bmod2,\qquad q_{n+1}=(3q_n+e_n)/2,
\]

coupled to the signed-margin recurrence.

The seed-extension digits \(\eta_n\) are **not** the orbit parities \(e_n\).
Seed stabilization does not imply eventual parity periodicity or eventual
zero parity.

### The certificate the main program should seek

For every exactly reachable state with positive stabilized seed and \(D_n>0\),
prove that within an explicitly finite macro-transition:

1. the margin becomes nonpositive; or
2. survival requires a nonzero seed-extension digit; or
3. an explicit rank in a well-founded order strictly decreases.

The cases must cover every continuation allowed by the exact arithmetic.
For an ordinary seed beyond bit \(W\), case 2 is unavailable, and case 3
cannot repeat indefinitely. This would close the general escape interface.

The rank may use the seed, quotient, margin, and a proved boundary invariant.
It must not be defined using the unknown future escape time. Quotients grow
and margins can recover, so neither quantity alone is an established rank.
Any return-time lemma must also be proved without assuming eventual escape.

## 4. Phase B: the main new route, exact multiplication automata

### B1. Establish the representation bridge, not a Rule 30 analogy

Read [Kopra's multiplication-automaton paper](https://arxiv.org/abs/2005.05112),
especially the introduction and Theorems 3.18 and 3.21. It provides an exact
connection between Mahler's problem and base-6 multiplication traces.

Use an explicit coordinate convention. For example, let \(d_i\in\{0,\ldots,5\}\)
be the digit at weight \(6^i\), with \(i\in\mathbb Z\), and

\[
 \operatorname{value}(d)=\sum_{i\in\mathbb Z}d_i6^i.
\]

A finite nonnegative real number has \(d_i=0\) for all sufficiently large
**positive** \(i\). The negative-index fractional tail can be infinite.

One concrete local-rule construction to verify against Kopra's convention is

\[
 (M_3d)_i=3(d_i\bmod2)+\lfloor d_{i-1}/2\rfloor,\qquad
 (Fd)_i=(M_3(M_3d))_{i+1}.
\]

The first rule represents multiplication by 3; the index shift in the second
divides the value by 6, so \(F\) represents multiplication by \(9/6=3/2\).
The resulting rule depends only on \(d_{i-1},d_i,d_{i+1}\).

This formula is a proposed implementation starting point, not a theorem
already added to the project. Prove digit-range preservation, convergence
and reindexing of the value series, the multiplication identity, and iteration.

Choose canonical base-6 expansions and prove their preservation. In
particular, exclude the alternative tail
\(0.25555\ldots_6=0.3_6=1/2\). Otherwise the digit test below gets the strict
endpoint wrong.

Then prove

\[
  \{\operatorname{value}(F^n d)\}<1/2
  \quad\Longleftrightarrow\quad
  (F^n d)_{-1}\in\{0,1,2\}.
\]

Also connect the finite trace constraints to the **same companion sets**
used by the existing seed/margin checker. Do not validate only the special
case where the starting real number is an integer.

**Exit gate B1:** a proved representation bridge, with zero, positivity,
coordinate direction, arbitrary fractional tails, and endpoints handled.
Do not build a large new automata library merely to rename the recurrence.

### B2. Test boundary forcing on exact finite space-time regions

Investigate diagrams with:

- an initial integer-side bound \(d_i=0\) for \(i\geq m\);
- at least one nonzero integer-side digit, corresponding to
  \(1\leq\alpha<6^m\);
- the observed column confined to \(\{0,1,2\}\) through horizon \(H\);
- all relevant fractional digits left free, not replaced by zeros.

Use the full causal cone of the observed column and the integer-boundary
constraints. Unknown boundary digits must be quantified over or soundly
overapproximated. A truncated simulation of one chosen tail does not rule
out other companions.

The all-scale target is

\[
 \forall m\geq1,\ \exists H(m),\
 \forall \alpha\in[1,6^m),\
 \exists n\leq H(m):\{\alpha(3/2)^n\}\geq1/2.
\]

Together with forward shifting for \(0<\alpha<1\), this suffices for the
general theorem. It is still a reformulation until an induction on \(m\)
or an equivalent arithmetic certificate is supplied.

**Important:** do not demand a uniform escape horizon for all
\(0<\alpha<6^m\). Arbitrarily tiny positive values give arbitrarily long
initial survival. The lower bound \(1\) is essential to this finite task.

Initially reproduce already certified exclusions, rather than chasing new
record sizes. Compare every finite result with the exact companion checker.
If a constraint solver is used, extract a small certificate that Lean can
check; a solver's unverified `UNSAT` output is not the final proof.

### B3. Seek a boundary-sensitive scale induction

The hoped-for mechanism is that a permanently safe column forces nonzero
digits arbitrarily far toward the **initial integer side**, contradicting
the finite boundary. Ordinary growth of later rows is not a contradiction.

For each candidate local mechanism:

1. Define a finite boundary signature and the arithmetic invariant it retains.
2. Prove that every relevant reachable diagram has such a signature.
3. Prove a one-scale transition that either creates a forbidden digit or
   forces a new initial nonzero digit beyond the previous certified boundary.
4. Prove preservation and strict progress under iteration.
5. Translate this to the seed-extension/rank certificate in Section 3, or
   directly prove the bounded-interval theorem in B2.

The useful new result is the **one-scale implication**, not the assertion
that permanent survival would somehow force infinitely many digits.

Kopra proves the restricted trace language is not sofic: a fixed finite
labeled graph cannot describe that entire language exactly. This does not
forbid finite certificates for bounded problems, parameterized abstractions,
or arithmetic ranks. It does rule out assuming that increasing a fixed
automaton's state count must eventually yield an exact general solution.

**Stop gate B:** after a representation bridge and a bounded experiment,
continue only if there is a specific scale lemma with new boundary content.
If the construction merely reproduces the signed-margin recurrence or admits
the same unrestricted 2-adic branches, record the equivalence and pause this
route. More diagrams alone are not progress toward the universal statement.

## 5. Phase C: a smaller target than rational-base normality

This route can be attempted after Phase A without waiting for all of Phase B.
Prefer it if the representation work reveals no new boundary mechanism.

Put \(T(a)=\lceil3a/2\rceil\) and define the finite odd count

\[
 O_a(N)=\#\{0\leq n<N:T^n(a)\text{ is odd}\}.
\]

### C1. Finish the finite counting bridge

The [global block-rate theorem](./GlobalStepRateBounds.lean) gives
\(3k\leq T_{\mathrm{blocks}}(k)+1\) for a surviving block chain.
Translate it to the following proposed finite statement:

\[
 \operatorname{ValidCompanionForever}(a,\alpha),\ a>0
 \quad\Longrightarrow\quad
 \forall N,\ 3O_a(N)\leq N+3.
\]

Proof route: enumerate odd times \(\tau_0<\tau_1<\cdots\). If \(m=O_a(N)>0\),
the first \(m-1\) gaps satisfy
\(3(m-1)\leq\tau_{m-1}-\tau_0+1\leq N\).
Handle \(m=0\), \(N=0\), and the initial even run explicitly.
Show that a positive orbit cannot become permanently even, since that
would force a fixed positive integer to be divisible by every power of 2.
Check the block-chain construction and its look-ahead hypotheses in Lean.

This is a small derivation to formalize, not a claim that the finite-count
theorem already exists.

### C2. Target a single finite surplus, not a limiting distribution

The following stronger-than-Mahler assertion would then suffice:

\[
 \boxed{\forall a\in\mathbb N,\ a>0\Longrightarrow
        \exists N:\ 3O_a(N)>N+3.}
\]

It is enough to prove one finite violation for each seed. A still stronger
condition is
\(\limsup_{N\to\infty}O_a(N)/N>1/3\); full normality is stronger again.
Do not impose existence of a limiting mean.

A separate sufficient target is

\[
 \forall a>0,\ \exists n:\ T^n(a)\equiv3\pmod4.
\]

That gives consecutive odd terms, already excluded by
`no_validCompanionForever_of_consecutive_odd_steps` in the
[infinite-companion bridge](./InfiniteZNumberBridgeAndRationalBase.lean).
For \(a=4k+3\), \(T(a)=6k+5\), so the residue-to-parity implication is immediate.

Neither universal arithmetic assertion is established here, and neither
is necessary for Mahler's conjecture to be true. Failure of one would
refute that route, not automatically produce a Z-number.

### C3. Use experiments to reject lemmas, not to infer normality

Reuse exact integer orbits to record parity surplus, first forbidden pattern,
and margin failure separately. Search adversarially for long delays.

Try a pointwise induction or macro-transition inequality that forces a
finite surplus, preferably only under the additional hypothesis of
perpetual companion feasibility if the unconditional statement is too strong.
At every proposed induction step, control intervening negative surplus.
An average over starting seeds, a random-bit heuristic, or an
almost-everywhere theorem cannot discharge this requirement.

**Exit gate C:** either a new infinite-family pointwise theorem, a candidate
universal induction with explicit remaining cases, or a counterexample to
the proposed induction. Merely proving C1 supplies an interface, not the
missing arithmetic theorem.

## 6. Reopen the carry/anagram route only with a new quantitative ingredient

The [sliding-window development](./DubickasConfinementAndComplexityExtension.lean)
contains necessary inequalities of the form

\[
 10S_d+100L_2(d+1)+330
 <
 7S_0+70L_2(0)+10w,
 \qquad W(0)<2^w.
\]

Here \(S_0\) is the intervening-horizon exponent from the existing theorem,
not a zero-time exponent. Preserve its definitions and all matching,
divisibility, ordering, and endpoint hypotheses.

A useful new collision theorem must force the reverse weak inequality
at some scale, not merely produce a collision:

\[
 10S_d+100L_2(d+1)+330
 \geq
 7S_0+70L_2(0)+10w.
\]

For bounded runs and a fixed origin, a sufficient asymptotic margin would be
\(7S_0\leq(10-\delta)S_d+K\), with \(\delta>0\), fixed \(K\), and unbounded
\(S_d\), **together with every carry-matching hypothesis**.
If origins move, also control growth of their starting states and bit lengths.
Bounds on the distance between matches alone may not be enough.

Admission criteria for renewed work:

- a proved restriction on **reachable** carries stronger than an ambient
  residue count;
- or a new exact cancellation that survives arbitrarily large scales;
- or a collision bound with constants that beat the displayed inequality.

An exponentially large possible palette does not itself prove that actual
orbits visit exponentially many states or wait exponentially long.
Conversely, an \(O(d)\) collision bound with an unfavorable constant need
not suffice. Do not turn either heuristic into a method-impossibility claim.

**Stop gate:** a larger fixed divisor, a smaller fixed defect cutoff, or
another bundled syzygy does not justify continuing this route as the main
general-proof program.

## 7. Experimental and logical controls

Keep a single reproducible case table with exact inputs, the lemma being
tested, coverage bounds, and witnesses. Use existing checkers where possible.

| Control | What it guards against |
| --- | --- |
| Seed zero survives forever | Accidentally proving an impossible statement without the positivity exception. |
| \(a=2^N\) survives through horizon \(N\) | Claiming a seed-independent finite escape horizon or treating a zero residue as the absence of positive seeds. |
| Certified \(B(4)\geq4\), \(B(12)\geq53\), \(B(29)\geq4096\) | New engine disagrees with existing exact finite feasibility. |
| Seed 149 survives through 28 and fails at 29 | Off-by-one errors and incorrect strict endpoints. |
| The periodic `100100...` symbolic stream | Scalar feasibility can persist without a positive ordinary integer realization; its corresponding 2-adic seed is \(-9/19\). |
| Arbitrarily small positive real inputs and base-6 half-endpoints | Losing the real-number quantifier or changing the half-open safe interval. |

When checking all seeds \(0<a<M\), use a horizon with \(M\leq2^N\) before
identifying them with their canonical residues. Prune only with proved
monotonicity or infeasibility. A bounded search that has not terminated is
not evidence that its termination follows by induction.

Use exact integers/rationals, not floating-point thresholds. Finite automaton
or solver witnesses are discovery evidence until translated to the original
arithmetic semantics and checked. A finite surviving patch, or even an
unrestricted infinite symbolic branch, is not an ordinary positive seed.

## 8. Execution order and decision points

Run at most one main proof attempt and one small independent lemma at a time.
Do not launch an open-ended literature survey or several alternative
formalizations of the same recurrence.

| Cycle | Work | Required output before continuing |
| --- | --- | --- |
| 1 | Phase A; state-interface review; C1 | Coverage matrix, targeted baseline results, and the finite odd-count implication or a precise indexing obstruction. |
| 2 | B1 and one bounded B2 cross-check | Exact multiplication/trace bridge, or an explicit reason it adds no useful arithmetic information. |
| 3 | Choose B3 or C2 as the main route | One fully stated scale/rank/parity lemma, its proof attempt, and adversarial finite checks. |
| 4 | Generalize only a successful mechanism | A parameterized theorem covering an infinite family, with a written account of all uncovered states. |
| 5 | Close Section 1, if possible | A universal escape proof, an all-scale \(B(N)\) lower-bound argument, or a rigorous positive counterexample construction. |

After two materially different failed attempts at a proposed lemma, pause
and reassess it. Record the smallest counterexample or missing hypothesis.
Do not respond by repeatedly enlarging numerical bounds without changing
the mechanism.

### Standard result labels

Every handoff should distinguish:

- **Established:** existing theorem, with exact hypotheses and source.
- **Newly proved:** new theorem, with validation and dependency information.
- **Observed:** finite experiment, with explicit bounds and reproduction.
- **Proposed:** unproved lemma and why it would help.
- **Refuted or blocked:** exact counterexample or remaining obstruction.

Measure progress by weaker assumptions, new infinite-family coverage, or
an all-scale implication. File counts, large constants, and a new capstone
name are not proof-completion metrics.

## 9. Final proof and formalization gates

A completed nonexistence proof must:

1. Quantify over every positive real starting value, or close an existing
   equivalent general interface.
2. Derive, rather than assume, any recurrence, complexity, density,
   bounded-run, or dense-core condition used.
3. Preserve the ordinary-integer seed constraint, the zero exception, and
   the strict upper endpoint.
4. Prove all return-time, scale-progress, and termination assertions.
5. Compose the finite/infinite and initial-shift bridges explicitly; do
   not interchange quantifiers over companions and horizons informally.
6. Expose any external analytic theorem as a dependency until formalized.
   An implication assuming an unproved normality conjecture is conditional.
7. Build affected modules and check files, inspect principal theorem axioms,
   and finally run the full configured build before claiming formal completion.

Use the existing check-file pattern. For a new check file, run it with
warnings as errors, for example `lake env lean -DwarningAsError=true .\NewChecks.lean`,
after building its dependencies. No `sorry`, `admit`, or new assumption
encoding the desired conclusion may occur in the final theorem's dependency
closure. A kernel-checked implication can still have an unproved antecedent.

Require a separate mathematical review of the final statement and reduction
coverage; a clean Lean build does not certify that the prose describes the
same theorem.

If no route closes, the legitimate deliverable is a verified partial result
and a precise open lemma. Do not call the conjecture resolved.

## 10. Literature and directions to keep in proportion

1. **Johan Kopra, 2020:** [On the Trace Subshifts of Fractional Multiplication Automata](https://arxiv.org/abs/2005.05112).
   Exact multiplication/trace connection; non-sofic restricted trace language.
   It does not prove emptiness of the positive-real-realizable confined traces.
2. **Jarkko Kari, 2012:** [Cellular automata, the Collatz conjecture and powers of 3/2](https://doi.org/10.1007/978-3-642-31653-1_5).
   Source of the exact automaton connection, not a transfer of a solution from
   Collatz or Rule 30.
3. **Andrieu, Eliahou, Vivion, 2025; revised April 2026:**
   [A Normality Conjecture on Rational Base Number Systems](https://arxiv.org/abs/2510.11723).
   Normality would imply the relevant nonexistence result; normality itself
   remains conjectural. This connection is already recognized in the project.
4. **Daniel Rudolph, 1990:** [Multiplication-by-2 and multiplication-by-3 invariant measures and entropy](https://doi.org/10.1017/S0143385700005629).
   Positive-entropy rigidity needs joint invariance under two independent
   maps. The [coupled ratio identities](./CoupledFractionalPartDynamics.lean)
   do not supply it. Keep this route parked unless a new construction proves
   those invariance and entropy hypotheses while retaining confinement.

Do not infer emptiness from zero measure or zero dimension. Do not use
generalized-Collatz heuristics, generic equidistribution, or a resemblance
between two recurrences as a substitute for a proved pointwise bridge.

---

# Part II: additional and cross-disciplinary research tracks

Everything above (Sections 1-10) is the primary program. Part II adds creative
tracks, several from other branches of mathematics. They are included because
Mahler's problem has resisted every single-discipline attack in this project,
so a decisive idea may come from importing a tool the project has not used.

Read this entire part as **proposed** research. None of these tracks is known
to close the problem, and some will certainly fail. That is acceptable and
useful: **a cleanly formalized negative or limitative result is a first-class
deliverable here** (Section 21 explains how to package one). When a track
fails, the goal is to convert the failure into a precise, machine-checked
statement of *why* the obstruction is real, so the next attempt does not repeat
it. Favor tracks that reduce to **finite, exactly verifiable certificates**
(explicit rational matrices, finite congruence tables, `decide`/`norm_num`
goals), because those are cheap to formalize and hard to get wrong, over tracks
that need large new Mathlib foundations (flagged per section).

Each track below uses the same template: **idea**, **exact object**, **lemmas
to formalize**, **why it might work**, **expected obstruction**, **negative
result to bank if it fails**, and **Mathlib/formalization notes**.

## 11. Transfer operators and thermodynamic formalism (the coupled survival operator)

**Idea.** Treat "which cylinders survive to depth \(d\)" as the action of a
nonnegative **transfer (Ruelle) operator** and bound its growth by exhibiting a
positive sub-invariant weight. The project already computed the *archimedean*
cylinder-growth spectrum: the Perron-Fibonacci characteristic polynomials
\(\lambda^{3k+4}-\lambda^{3k+1}-1\) with Perron roots \(\lambda_k\to1^+\)
(`cantorDust_perron_fibonacci_counts`,
`perronCharPoly_sign_change_and_root_squeeze`). This track turns that spectral
picture into a decisive tool by **coupling it to the 2-adic constraint**.

**Exact object.** Fix a congruence depth \(k\). Define a finite state set
\(\mathcal S_k\) = (symbolic block state) \(\times\) (seed residue mod \(2^k\),
or equivalently the mod-\(2^k\)/mod-\(16\)/mod-\(128\) sieve class already proved
in `DubickasConfinementAndComplexityExtension.lean`). Build the entrywise
nonnegative **coupled survival matrix** \(M_k\) over \(\mathbb Q\): \(M_k[s,s']=1\)
when a one-block transition \(s\to s'\) is simultaneously (a) archimedean-admissible
(stays in \([0,1/2)\)) and (b) 2-adically consistent (compatible with the proved
residue bijections \(j\bmod4\leftrightarrow V\bmod16\), etc.). Weight each
transition by the exact width-and-grid factor it carries.

**Lemmas to formalize.**

1. *Sub-invariant weight bound (foundational, ~15 lines, no Mathlib gap).*
   For `M : Matrix (Fin r) (Fin r) ℚ` with `0 ≤ M i j`, a strictly positive
   `w : Fin r → ℚ`, and `ρ : ℚ` with `∀ i, (∑ j, M i j * w j) ≤ ρ * w i`, prove
   `∀ n i, (∑ j, (M ^ n) i j * w j) ≤ ρ ^ n * w i` by induction on `n`. This is
   an elementary, Perron-Frobenius-free certificate for "spectral radius \(\le\rho\)".
2. *Coupled criticality search.* For each \(k\) up to a budget, search for a
   positive rational weight \(w\) and \(\rho_k\) with \(M_k w\le\rho_k w\) and
   \(\rho_k<1\) **after** folding in the width/grid normalization. A single
   success at any finite \(k\) gives: only finitely many integer seeds survive,
   hence (with the certified finite bounds) none.
3. *Honest marginal identity (do this first).* Prove the **archimedean-only**
   operator cannot be contracted: its normalized growth constant is
   \(\lambda\cdot\tfrac43>1\). This is exactly the "density fallacy" the paper
   warns about and explains why pruning by 2-adic state is mandatory.

**Why it might work.** The independent archimedean and 2-adic constraints each
have codimension that *cancels* to an \(O(1)\) marginal (the source of the
difficulty). The coupled operator keeps the **correlation** between the two
places instead of multiplying marginals. If the correlation is even slightly
favorable at some finite congruence depth, \(\rho_k\) drops below the critical
value and the whole problem collapses to a finite matrix inequality.

**Expected obstruction.** The coupling may be exactly critical at every \(k\):
\(\rho_k\to1^-\) but never \(<1\), mirroring \(\lambda_k\to1^+\). If so, no finite
congruence depth suffices and an unbounded/renormalization argument is needed.

**Negative result to bank.** Formalize \(\rho_k\) as an explicit decreasing
rational sequence with proven limit \(1\) (a 2-adically-enriched analogue of the
existing Perron root squeeze). That is a precise, citable statement of the
barrier: "no fixed-depth coupled transfer certificate exists," which rules out a
large class of attempts once and for all.

**Mathlib notes.** Needs only `Matrix`, `Finset.sum`, `ℚ`; avoid Perron-Frobenius
entirely via lemma (1). Matrices are small and explicit, so entries and the
weight inequality are `decide`/`norm_num` goals. No analysis dependency.

## 12. Joint spectral radius and the matrix-product (cocycle) view

**Idea.** An infinite surviving orbit is an infinite product of transition
matrices drawn from a finite set \(\{A_0,\dots,A_{t}\}\) (one per admissible block
length). Boundedness/positivity of **every** such product is a **joint spectral
radius (JSR)** question: if \(\mathrm{JSR}(\{A_i\})<1\) in the correct normalization,
no orbit survives.

**Exact object.** The finite matrix set generated by the coupled survival
transitions of Section 11, normalized by width/grid factors so that "survival
forever" is "some infinite product stays bounded away from collapse."

**Lemmas to formalize.**

1. *Common sub-invariant polytope / weight.* A single positive weight \(w\) with
   \(A_i w\le\rho w\) for **all** \(i\) gives \(\mathrm{JSR}\le\rho\) by the same
   elementary induction as 11(1), now quantified over the generator index. This
   is a finite, verifiable certificate.
2. *Extremal-norm refinement.* If a common linear weight fails, try a common
   polytope norm (finitely many linear inequalities) or a max of a few weights;
   still a finite rational feasibility check.

**Why it might work.** JSR \(<1\) is exactly "no infinite product survives,"
which is the general statement. Upper bounds via one norm are cheap and
formalization-friendly even though computing JSR exactly is hard in general.

**Expected obstruction.** JSR may be exactly \(1\) (critical), consistent with the
finiteness/criticality seen elsewhere. The JSR **finiteness conjecture** (optimal
products are eventually periodic) is itself open, so do not rely on it.

**Negative result to bank.** A proof that \(\mathrm{JSR}=1\) via an explicit
near-critical periodic product (e.g. the `100100...`/period-3 witness already in
the project) formalizes the exact tightness of the matrix method.

**Mathlib notes.** Pure linear algebra over \(\mathbb Q\); finite generator set;
no JSR library needed because only an upper-bound certificate is formalized.

## 13. Harmonic analysis on the carry group (attack the Section 6 gap directly)

**Idea.** Section 6's barrier is that the carry \(\mathrm{Acc}_d\in\mathbb Z/3^{S_d}\)
seems to need an *exponential* horizon before it collides. Use **3-adic Fourier
analysis** to test whether reachable carries **concentrate** (a large low-frequency
coefficient) rather than equidistribute. Concentration forces an **early
approximate return**, which combined with the exact divisibility could yield the
reverse inequality Section 6 demands.

**Exact object.** For a surviving orbit, the carry sequence
\(n\mapsto\mathrm{Acc}_n\bmod3^{m}\) and its additive-character sums
\(\widehat{\mathrm{Acc}}(\chi)=\sum_{n<N}\chi(\mathrm{Acc}_n)\) for characters
\(\chi\) of \(\mathbb Z/3^{m}\) (equivalently 3-adic exponentials).

**Lemmas to formalize.**

1. *Autocorrelation \(\Rightarrow\) early near-return.* If some bounded-lag
   autocorrelation of the carry sequence exceeds an explicit threshold, then two
   carries agree modulo \(3^{m}\) within a **linear** window; make the constant
   explicit and feed it to the Section 6 inequality.
2. *Carry recurrence in character coordinates.* The exact carry recurrence
   \(C_{n+1}=3C_n+2^n e_n\) becomes a clean multiplicative/shift relation on
   characters; formalize it so concentration is a checkable property at each
   finite modulus \(3^m\).

**Why it might work.** The carries are **not** random: they are generated by a
deterministic low-complexity recurrence driven by the parity stream, which for a
survivor is itself heavily constrained (Sections 11, 6). Deterministic structure
typically shows up as Fourier concentration, exactly the favorable case.

**Expected obstruction.** The carries may provably equidistribute, giving only a
birthday-type \(\sim3^{S_d/2}\) (still exponential) collision time, which does not
reach Section 6's linear horizon.

**Negative result to bank.** A proven upper bound on all nontrivial carry Fourier
coefficients (equidistribution) is a clean, important limitative theorem: it shows
**no** pigeonhole/collision argument on the raw carry group can close Section 6,
formally justifying the stop gate there and redirecting effort.

**Mathlib notes.** `ZMod (3^m)`, `AddChar`, and `Padic`/`PadicInt` exist; a full
discrete-Fourier-inversion toolkit may need building, but the specific character
sums and the single autocorrelation inequality can be stated and checked at fixed
small \(m\) by finite computation first.

## 14. Measure rigidity and the honest adelic \(\times2,\times3\) / solenoid reframing

**Idea.** Build the correct ambient space where \(\times(3/2)\) lives together
with genuine \(\times2\) and \(\times3\) actions, then try to invoke rigidity
(Rudolph/Host/Johnson, Lindenstrauss) **honestly** — supplying the second
independent action and the entropy hypothesis the theorems require, which the
project's coupled identity does **not** yet provide.

**Exact object.** The \(\{2,3\}\)-solenoid
\(\mathbb S=(\mathbb R\times\mathbb Q_2\times\mathbb Q_3)/\mathbb Z[1/6]\),
on which \(\times2\) and \(\times3\) act as commuting automorphisms and the orbit
of a Z-number sits on a \(\times(3/2)\)-invariant subset. The confinement
\(\{(3/2)^n\alpha\}<1/2\) is a constraint in the real coordinate only; the
2-adic/3-adic coordinates carry the exactness.

**Lemmas to formalize (or refute).**

1. *Orbit-closure invariance.* Decide whether the closure of a hypothetical
   survivor's orbit (or a measure on it) is invariant under a genuine **second**
   multiplicatively independent map, not merely expressible with 2 and 3.
2. *Entropy side condition.* If such invariance exists, check the
   positive-entropy / ergodicity hypothesis the rigidity theorem needs.
3. *Rigidity \(\Rightarrow\) emptiness.* Only then conclude the invariant set is
   Lebesgue or a finite rational orbit, excluding a confined survivor.

**Geometric-measure sub-track (Bernoulli convolutions / self-affine sets).** The
candidate companion is a value of the series \(\sum\pm(2/3)^{T(k)}\); the set of
admissible values is an intersection of a **self-affine attractor** (contraction
ratio \(2/3\), a Bernoulli-convolution-type object) with the integer grid. Import
dimension results (Hochman inverse theorem; Shmerkin, Varjú) to bound the
dimension of the survivor set, then ask whether the grid can meet it.

**Why it might work.** The \(\times2,\times3\) theme is not accidental: the exact
arithmetic genuinely mixes both primes, and the solenoid is the natural home
where both become automorphisms.

**Expected obstruction (stated plainly).** Mahler's problem has **one** generator
\(\times(3/2)\); a single endomorphism of a solenoid admits a huge zoo of invariant
sets. Rigidity collapses that zoo only with a **second independent** action, which
is not visibly present. Dimension/measure results give measure- or dimension-zero,
**not emptiness**, and cannot delete one exceptional arithmetic orbit.

**Negative result to bank.** Formalize the precise failure: construct the solenoid
and prove that the survivor set, while \(\times(3/2)\)-invariant, is **not**
invariant under any second independent map (or carries no non-Lebesgue jointly
invariant measure). A machine-checked "rigidity does not apply, and here is
exactly why" is valuable and is currently only folklore.

**Mathlib notes.** Heavy: solenoids, Haar measure on \(\mathbb Q_p\), entropy, and
rigidity are not in Mathlib. Treat this as a long foundational track or confine it
to a precisely stated **negative** lemma. Do not over-invest before Sections
11-13 are exhausted.

## 15. Exponential sums, discrepancy, and Erdős-Turán (conditional reductions)

**Idea.** Count \(\#\{n<N:\{(3/2)^n\alpha\}\ge1/2\}\) via the discrepancy of the
sequence \((3/2)^n\alpha\), bounded by exponential sums through the Erdős-Turán
inequality. A good bound on \(\sum_{n<N}e(k(3/2)^n\alpha)\) gives a lower bound on
escapes.

**Exact object.** The Weyl sums \(S_k(N)=\sum_{n<N}e\!\big(k(3/2)^n\alpha\big)\),
the star-discrepancy \(D_N^*\), and the Erdős-Turán bridge
\(N\cdot(\text{proportion in }[0,1/2))\le N/2+O(N D_N^*)\).

**Lemmas to formalize.**

1. *Erdős-Turán inequality* (finite, elementary but currently absent from
   Mathlib): \(D_N^*\le\frac{C}{K}+\frac{C}{N}\sum_{k=1}^K\frac{|S_k(N)|}{k}\).
2. *Reduction.* Any nontrivial bound \(|S_k(N)|=o(N)\) uniform enough implies
   \(\{(3/2)^n\alpha\}\) exceeds \(1/2\) infinitely often — Mahler for that \(\alpha\).

**Why it might work.** It converts the problem to the well-studied language of
equidistribution and gives a clean *conditional* theorem that is cheap to
formalize and immediately useful.

**Expected obstruction.** Whether \((3/2)^n\) is equidistributed mod 1 is a
notorious open problem; unconditional bounds on \(S_k(N)\) for the specific base
\(3/2\) are not known. So this yields a conditional result, not a proof.

**Negative result / conditional deliverable.** Formalize Erdős-Turán and the exact
reduction "equidistribution of \((3/2)^n\alpha\) \(\Rightarrow\) Mahler for
\(\alpha\)," exposing the equidistribution input as a named, unproved hypothesis.
This cleanly delimits what analysis alone can and cannot do here.

**Mathlib notes.** `Mathlib.Analysis.SpecialFunctions`, `Complex.exp`, and finite
sums are available; Erdős-Turán and discrepancy need building but are self-contained.

## 16. Simultaneous digit restriction in two bases; S-unit equation counting; cross-seed emptiness

**Idea.** A Z-number's floor sequence is an integer that is simultaneously
constrained in base 2 (parity/carry) and base 3 (the \(3/2\) multiplier). Use the
theory of integers with restricted digits in two multiplicatively independent
bases (Stewart 1980, already cited) and uniform **counting** bounds for S-unit
equations (Evertse-Schlickewei-Schmidt) to sharpen per-block finiteness toward
emptiness.

**Exact object.** The orbit identity \(Q_m-P_m=\Delta_m\) with
\(Q_m=3^{T(m)+1}(2a_0+1)\), \(P_m=2^{T(m+1)+1}u(m)\) is an **S-unit equation** over
\(S=\{2,3\}\) (plus the \(u(m)\) support). The project already has the two-seed
shared-prefix divisibility (`two_seed_shared_prefix_divisibility`) and per-dyadic-block
Ridout finiteness (`mahler_two_seed_same_step_ridout_bound`).

**Lemmas to formalize.**

1. *Uniform solution-count bound.* Formalize (or axiomatize as a dependency) the
   bound on the **number** of solutions of the relevant S-unit equation, uniform
   in the block.
2. *Cross-seed pigeonhole.* Combine with the certified finite bounds (\(B(29)\ge4096\),
   seed 149) to try to push the per-block survivor count below 1.

**Why it might work.** Counting bounds (as opposed to size bounds) are uniform and
sometimes small; combined with cross-seed interactions they might collapse a block.

**Expected obstruction.** "Finitely many per block" is classical; "zero per block"
is the entire difficulty, and solution-counting will not generically reach zero.

**Negative result to bank.** A formalized exact solution-count for the \(\{2,3\}\)
S-unit equation, with an explicit example achieving the count, documents precisely
how far finiteness methods go and why they stop short of emptiness.

**Mathlib notes.** Subspace theorem and S-unit counting are **not** in Mathlib; the
project already isolates these as external. Keep them as named dependencies and
formalize only the reduction and the elementary parts.

## 17. Mahler's method: transcendence of the companion **value** for structured streams

**Idea.** The project's structured-stream work (Thue-Morse functional equation
\(F(z)=(1-z)F(z^2)+\tfrac{z}{1-z^2}\)) is **function-level**. Modern Mahler's
method (Adamczewski-Faverjon) upgrades a transcendental Mahler *function* to a
transcendental *value* at algebraic points. That turns the structured-stream
exclusions into genuine "cannot be an integer-seed parity word" theorems.

**Exact object.** The \(z\mapsto z^2\) Mahler function \(F\) and its value
\(F(\alpha)\) at the specific algebraic \(\alpha\) (e.g. \(8/27\)) where the
2-adic seed identity \(a_0=-F(8/27)/3\) lives.

**Lemmas to formalize.**

1. *Conditional value-transcendence.* Formalize the implication: \(F\) a
   transcendental Mahler function + standard non-degeneracy \(\Rightarrow F(\alpha)\)
   irrational/transcendental, with the Adamczewski-Faverjon theorem as a named
   dependency.
2. *Stream exclusion.* Irrationality of the value \(\Rightarrow\) the structured
   stream is **not** the parity stream of any ordinary integer seed, upgrading the
   existing finite-cutoff results to an unconditional exclusion for that family.

**Why it might work.** For the specific structured families already built in Lean,
this is the exact missing ingredient the project flagged ("function transcendence
\(\ne\) value transcendence"), and the modern theorems supply it.

**Expected obstruction.** It is family-specific (Thue-Morse, period-doubling, other
\(z\mapsto z^2\) streams), not a route to the general case. The general survivor
need not be automatic/morphic at all.

**Negative result / scope statement.** Even if fully formalized, record explicitly
that it excludes a measure-zero set of structured streams and says nothing about a
generic aperiodic survivor. This prevents over-claiming.

**Mathlib notes.** Mahler's method is not in Mathlib; formalize the **implication**
with the deep theorem as a hypothesis, which is cheap and immediately sharpens the
existing results the moment any special case lands in Mathlib.

## 18. Deterministic Lyapunov / potential (supermartingale-style) functions

**Idea.** Find an explicit potential \(\Phi\) on exact states that **strictly
decreases** over each bounded macro-transition for a positive-seed survivor,
giving a well-founded descent (this is the concrete realization of Section 3's
rank). The probabilistic intuition (carries look random, so the orbit drifts to
escape) must be replaced by a **deterministic** decreasing quantity.

**Exact object & candidate potentials to try in order.**

1. \(\Phi=\) the signed margin \(D_n\) itself — **known to fail** (the
   `signedMargin_100_ceiling_recovery` "100-block" recovery). Re-deriving its
   failure precisely is the baseline.
2. \(\Phi(N)=(N+3)-3\,O_a(N)\), the **odd-count deficit** of Section 5/C. The
   global step-rate theorem gives \(\Phi\ge0\) (non-strict); the task is a
   **strict** per-macro-block decrease. Framing C as a potential clarifies exactly
   what extra inequality is missing.
3. \(\Phi=\,\)an \(\{\infty,2\}\)-coupled potential: a positive combination of
   \(\log q_n\), the 2-adic valuation \(v_2(\cdot)\) of the margin numerator, and
   the archimedean slack, tuned so the ceiling-recovery gain in one place is
   overpaid by a loss in the other.

**Lemmas to formalize.** For a chosen \(\Phi\): (i) \(\Phi\ge0\) for feasible
states; (ii) a strict drop \(\Phi(\text{after macro-block})\le\Phi-\delta\) for an
explicit \(\delta>0\); (iii) control of intervening increases within the block.
Then well-foundedness yields escape.

**Why it might work.** The project already has *all three* ingredient inequalities
(step-rate, valuation locks, archimedean corridor) as separate theorems; the open
question is whether a single **weighted combination** is strictly monotone. That is
a finite search over rational weights with a finite case analysis per block type —
very formalizable.

**Expected obstruction.** The ceiling-recovery mechanism may exactly balance every
candidate potential (no strict \(\delta\)); i.e. the system sits on a true
indifference surface.

**Negative result to bank.** For each candidate weight vector, a formal proof that
\(\Phi\) is **not** strictly decreasing — with the exact balancing transition — maps
out the indifference surface and tells the next attempt which direction is still
free. A table of refuted potentials is genuine progress.

**Mathlib notes.** `WellFounded`, `Nat`/`ℚ` orders; everything is finite case
analysis and rational arithmetic. No external theory.

## 19. Infinite-game / determinacy framing (build on `Adversarial.lean`)

**Idea.** Phrase survival as a **safety game**: an "orbit" player tries to stay in
\([0,1/2)\) forever; an "environment" resolves the bounded choices. Safety games are
determined without full Borel determinacy, and the orbit player wins from a state
iff that state lies in a largest invariant "survivor kernel." Mahler's conjecture
is exactly "the survivor kernel contains no positive-integer seed."

**Exact object.** The monotone decreasing sets \(\mathrm{Surv}_N=\{a:B\text{-feasible
through }N\}\) and their intersection; the "kernel" is \(\bigcap_N\mathrm{Surv}_N\).
This reuses `leastPositiveSurvivor` and the existing adversarial witnesses.

**Lemmas to formalize.** (i) The safety game's value equals kernel membership
(elementary, finite branching per depth). (ii) "Escaper wins from every positive
seed" \(\iff\) a well-founded rank on the kernel complement \(\iff\)
\(B(N)\to\infty\). This gives a clean **completeness** statement: a rank certificate
is not just sufficient but necessary, so Section 3/18 is the "right" target.

**Why it might work.** It certifies that the rank/potential search cannot miss a
solution for structural reasons, and it connects to the existing adversarial
machinery rather than starting fresh.

**Expected obstruction.** It reformulates rather than solves; the rank still has to
be exhibited. But it rules out "there is no finite certificate" as an excuse.

**Negative result to bank.** If a proposed strategy for the orbit player is shown to
lose in bounded time (a finite game tree), that is exactly a certified finite escape
bound for a family of seeds.

**Mathlib notes.** Mathlib's game/determinacy support is thin; here the game is a
**safety/reachability game with finite branching per level**, so encode the kernel
directly as a greatest fixed point and avoid general determinacy machinery.

## 20. Renormalization by inducing (first-return maps)

**Idea.** Induce the dynamics on a well-chosen sub-interval so the first-return map
is a **full-branch** (and ideally self-similar) expanding map, where confinement may
become a clean self-referential condition amenable to induction.

**Exact object.** A first-return map \(R\) to a sub-interval \(I\subset[0,1/2)\),
its finitely many branches, and the induced block-length/carry recurrence (the
project's homoclinic catapult structure already hints at such self-similarity).

**Lemmas to formalize.** (i) \(R\) is well-defined and full-branch on \(I\);
(ii) a renormalization identity relating survival under \(R\) at scale \(I\) to
survival at a rescaled copy; (iii) a contraction/monotonicity across the
renormalization step.

**Why it might work.** Self-similarity is the natural match to the Cantor cascade
already mapped; a renormalization fixed point could linearize the obstruction.

**Expected obstruction.** The 2-adic coordinate does not renormalize as cleanly as
the archimedean one; the induced carry may not be self-similar.

**Negative result to bank.** A formal statement that the induced map fails to be
self-similar (explicit mismatch), documenting why renormalization stalls.

**Mathlib notes.** Interval dynamics over \(\mathbb Q\); finite branch bookkeeping.
Lower priority than Sections 11-13.

## 21. How to formalize negative and limitative results (first-class deliverables)

Because many Part II tracks will not close the problem, treat their failures as
**the** output, not as waste. A good negative result is reusable: it stops future
effort from re-entering a dead end and often sharpens the real obstruction.

Package each negative result as one of these precise shapes:

1. **Tightness/criticality:** an explicit sequence of certificates whose quality
   provably converges to the critical value but never crosses it (e.g. coupled
   transfer radii \(\rho_k\to1^-\), Section 11; \(\mathrm{JSR}=1\), Section 12).
2. **Method-cannot-reach:** a theorem that a named mechanism is quantitatively
   insufficient (e.g. carry equidistribution \(\Rightarrow\) only birthday-time
   collisions, Section 13; "no fixed-depth congruence certificate," Section 11).
3. **Hypothesis-does-not-apply:** a construction showing the preconditions of an
   imported theorem fail (e.g. no second independent action for rigidity,
   Section 14).
4. **Refuted certificate:** an exact counterexample to a proposed invariant,
   potential, or induction step (e.g. a potential that fails to decrease on a named
   transition, Section 18).
5. **Conditional reduction:** a fully proved implication whose antecedent is a
   named open input (e.g. Erdős-Turán reduction, Section 15; Mahler-value
   transcendence, Section 17). These are positive contributions in negative
   disguise: they relocate the difficulty to a precise external statement.

For every negative result, the Lean artifact must (a) state the limitation with
exact quantifiers, (b) carry a witness or an explicit convergent bound, and (c)
avoid `sorry` in its own proof even if it references an external hypothesis. A
refuted lemma with a machine-checked counterexample is worth more than an
unverified heuristic that "seems" to work.

## 22. Cross-cutting formalization infrastructure and a Mathlib reality check

To keep Part II cheap and robust:

- **Prefer finite rational certificates.** Sections 11, 12, 18, 19 reduce to
  explicit \(\mathbb Q\)-matrices/weights/tables verifiable by `decide`/`norm_num`.
  Do these first; they need no new Mathlib theory and are hard to get wrong.
- **Isolate deep external theorems as named hypotheses.** Sections 14, 15, 16, 17
  depend on results not in Mathlib (rigidity, Erdős-Turán, Subspace/S-unit counting,
  Mahler's method). Formalize the **reduction** now with the theorem as an explicit
  assumption; the result upgrades automatically if Mathlib later gains the input.
- **Reuse existing engines.** The seed/margin checker, the sieve bijections, the
  Perron-Fibonacci counts, `Adversarial.lean`, and `leastPositiveSurvivor` are the
  substrate for Sections 11, 12, 18, 19. Do not rebuild them.
- **One shared state type.** Define the coupled (symbolic \(\times\) 2-adic residue)
  state once and let Sections 11, 12, 18, 19 all consume it, so a certificate found
  in one view transfers to the others.
- **Keep each new module behind its own `...Checks.lean`** built with warnings as
  errors, following the existing convention, and record `#print axioms` for every
  headline theorem (including negative ones).

## 23. Priority and sequencing for Part II

Run Part II **after** Cycle 1-2 of Section 8 (coverage audit + representation
bridge), interleaving one Part II track at a time with the primary program.
Suggested order, highest expected value first:

1. **Section 11 (coupled transfer operator)** and **Section 18 (potentials)** —
   the most formalization-friendly, reuse the most existing machinery, and attack
   the true crux (the 2-adic/archimedean correlation). Expect a decisive finite
   certificate or a sharp criticality negative result.
2. **Section 13 (carry Fourier)** — directly resolves whether Section 6 can ever
   work; either outcome is valuable.
3. **Section 12 (JSR)** and **Section 19 (game completeness)** — cheap theoretical
   scaffolding that certifies the rank/potential target is the right one.
4. **Section 17 (Mahler-value)** — concrete upgrade of existing structured-stream
   results; do when a structured-stream question is already open on the desk.
5. **Sections 15, 16, 20** — conditional/auxiliary; formalize reductions only.
6. **Section 14 (rigidity/solenoid)** — highest ceiling but highest cost; attempt
   only its precise negative lemma unless Sections 11-13 reveal a genuine second
   action.

Hard rule unchanged from Part I: **one main attempt and one small lemma at a time**,
and after two materially different failures on a track, convert it into the best
available negative result (Section 21) and move on. Do not let Part II become an
open-ended survey.

## First handoff to Argon

Start with Cycle 1. Return the coverage matrix, focused build results, and
the exact finite odd-count lemma. Then undertake one small representation
bridge for the base-6 automaton. Before expanding either route, write down
the first genuinely new arithmetic lemma that would make all-scale progress.
If no such lemma survives scrutiny, stop and report that fact.

The opportunity is to make finite ordinary-seed information persist through
the argument. The plan succeeds as a general proof only when that information
forces escape for every positive seed, not merely for the examples tested.

Once the Cycle 1-2 baseline is in place, open the highest-value Part II track
(Section 23 orders them): the **coupled transfer operator** of Section 11 and a
**deterministic potential** of Section 18 are the first picks, because both reuse
existing engines, reduce to finite rational certificates, and strike at the real
crux — the correlation between the archimedean and 2-adic constraints. Treat a
sharp negative result (Section 21) as a successful outcome of any track, not a
failure: a machine-checked criticality bound, a refuted potential, or a clean
conditional reduction each advances the problem and is explicitly in scope here.

---

# Part III: Round 1 execution report, claim-to-theorem audit & formalized deliverables

Date executed: 2026-11-01 (`150` `.lean` files total, `0` `sorry`s, `0` warnings)

## 24. Phase A claim-to-theorem coverage audit matrix

Every advertised reduction was audited against its exact Lean 4 theorem signature:

| Claim audited | Exact Lean theorem(s) | Verified antecedents & scope | Remaining open coverage gap |
| --- | --- | --- | --- |
| Dense-Core confinement to \([8/81,1/2)\) and \(\{3,4\}\) block lengths | `punctured_eight_eighty_firsts_forbids_four_zeros_and_short_gaps`, `cantor_dust_three_adic_valuation_and_normalized_recurrence` | Assumes fractional parts stay in \([8/81,1/2)\) (`80.25%` of \([0,1/2)\)). | Orbits that repeatedly dip into the lower strip \([0,8/81)\) via leak-window preimages without stabilizing on a single rung \(g\). |
| Sub-critical factor complexity exclusion in the Dense Core | `no_subcritical_log_threshold_dense_core`, `no_density_weighted_subcritical_log_threshold_dense_core` | Excludes **linear** prefix-factor complexity bounds \(p(L)\le\kappa L+C_0\) at arbitrarily large \(L\) for \(\kappa<\frac{7\log 2}{\mu\log(3/2)}\in[1.1967,1.7095]\). | Superlinear subexponential growth (e.g. \(p(L)=\Theta(L^2)\) or \(L^{\alpha}\) with \(\alpha>1\)) and exponential complexity \(p(L)\ge c^L\). |
| Unbounded / sparse run and defect exclusions | `no_infinite_rapid_growth_block_chain`, `no_infinite_sparse_defect_cantor_dust_chain`, `no_infinite_cumulative_sparse_epoch_cantor_dust_chain` | Assumes sustained growth \(3^{s(m)}<2^{s(m+1)}\), sustained sparse spacing \(2j_r+2\le j_{r+1}\), or cumulative epoch dominance. | Intermittent unbounded spikes separated by long expanding (`j=1,2`) epochs that replenish the odd quotient \(u(m)\) or \(V_r\) between drops. |
| Sliding-window & abelian block-match capstone | `mahler_dense_core_complete_reduction_and_sliding_syzygy_capstone` | Proves linear-in-\(d\) abelian step-sum Pigeonhole and conditional \(W(0)\)-referenced cutoffs under block-carry equality (`S_d ≤ 28`) or 4-window pure \(3\)-adic growth (`8121643200 * 3^(S_d + 10*L_2 0) < W(N+1+d+1)`). | For \(W_0\to\infty\) and \(S_d>28\), two windows with equal abelian step sum \(S_d\) need not share the same \(3\)-adic interior carry \(\mathrm{Acc}_d\). |
| Vanishing Lebesgue measure & certified finite floors | `rungDeathGap_maps_onto_catapult_zone`, `positive_survivor_step29_ge_4096`, `binary_cantor_dust_certified_depth_11_and_12` | Measure shrinks at \((1/19)^K\to0\); \(B(29)\ge4096\); Dense-Core \(V(0)>2^{92}\). | Measure zero and finite lower bounds do not by themselves rule out a single exceptional positive integer orbit. |

## 25. New Lean 4 modules formalized in this round

All tracks in Part I (Phases A, B, C) and Part II (Sections 11–21) have been formalized across
four new core modules and four verification modules (`warningAsError=true`, standard axioms only):

1. **[ParitySurplusPotentialsAndSafetyGame.lean](./ParitySurplusPotentialsAndSafetyGame.lean) &
   [ParitySurplusPotentialsAndSafetyGameChecks.lean](./ParitySurplusPotentialsAndSafetyGameChecks.lean)
   (Phase C, Section 18 & Section 19):**
   - **Universal Shift-Submultiplicativity of `signedMargin` (`signedMargin_add_le_two_pow_mul_shift`,
     `signedMargin_shift_pos_of_add_pos`):** Proves `signedMargin ε (k + m) ≤ 2^k * signedMargin (shiftStream ε k) m`
     for all `ε, k, m`, so every suffix of a feasible parity stream is automatically feasible from depth `0`.
   - **Look-Ahead-Free Finite Odd-Count Theorem (`three_mul_oddParityCount_le_add_three_of_signedMargin_pos`,
     `three_mul_oddCount_le_add_three_of_validCompanionUpTo`,
     `three_mul_oddCount_le_add_three_of_validCompanionForever`):** Proves Phase C1 in its strongest
     finite-horizon form: `0 < signedMargin ε N → 3 * oddParityCount ε N ≤ N + 3` for **all** `ε` and `N`,
     without needing `ValidBlockChain` look-ahead hypotheses.
   - **Pointwise Sufficient Conditions (Phase C2):** Formalizes `mahler_conjecture_of_forall_pos_seed_parity_surplus`
     (`∀ a_0 ≥ 1, ∃ N, N + 3 < 3 * oddCount a_0 N` implies Mahler's conjecture) and
     `mahler_conjecture_of_forall_pos_seed_hits_three_mod_four` (`∀ a_0 ≥ 1, ∃ n, orbit a_0 n % 4 = 3`
     implies Mahler's conjecture), plus `exists_odd_orbit_step_of_pos`.
   - **Deterministic Potentials & Indifference Surface Refutation (Section 18):** Formalizes
     `deficitPotential ε N = N + 3 - 3 * oddParityCount ε N`, proves `0 ≤ deficitPotential ε N`
     under feasibility, proves that every linear combination of normalized margin `D_N / 2^N` and
     `deficitPotential` is strictly stationary across ceiling-saturated `100` blocks
     (`linear_coupled_margin_deficit_stationary_on_100_cycle`), and proves that incorporating the
     stabilized seed quotient breaks this stationarity via `8 * (19 * q_{N+3} + 9) = 27 * (19 * q_N + 9)`
     (`stabilized_seed_100_two_adic_valuation_drop`).
   - **Infinite Safety-Game & Survivor-Kernel Completeness (Section 19):** Formalizes
     `survivesHorizonSet N`, `survivorKernel`, and the 4-way equivalence
     `safety_game_kernel_and_rank_completeness` between Mahler's conjecture, `survivorKernel = ∅`,
     existence of a finite escape rank `R : ℕ → ℕ` on positive seeds, and `B(N) → ∞`.

2. **[BaseSixMultiplicationAutomaton.lean](./BaseSixMultiplicationAutomaton.lean) &
   [BaseSixMultiplicationAutomatonChecks.lean](./BaseSixMultiplicationAutomatonChecks.lean)
   (Phase B: Sections B1–B3 & Section 10.1–10.2):**
   - Formalizes Kari and Kopra's exact base-6 multiplication cellular automata `mulThreeCA` and
     `mulThreeHalvesCA` ($\Pi_{3/2, 6}$), proving digit-range preservation
     (`isBaseSixConfig_iterate_mulThreeHalvesCA`), the explicit 3-cell radius-1 local rule
     (`mulThreeHalvesCA_eq_local_rule`), and `n`-step causal-cone locality
     (`mulThreeHalvesCA_iterate_causal_cone_congr`).
   - Proves the unconditional finite-window carry-flux identity (`baseSixScaledNat_mulThreeCA_flux`)
     and the exact rational value homomorphism `baseSixWindowVal (mulThreeHalvesCA d) (a - 1) (L + 2) = (3/2) * baseSixWindowVal d a L`
     (`baseSixWindowVal_mulThreeHalvesCA`).
   - Proves the canonical fractional-part / digit-`(-1)` trace equivalence
     `Int.fract (I + (d_neg1 / 6 + r)) < 1 / 2 ↔ d_neg1 < 3` for `0 ≤ r < 1/6`
     (`fract_lt_half_iff_digit_neg_one_lt_three`) and the non-canonical all-`5` tail counterexample
     `0.2555..._6 = 1/2` (`noncanonical_tail_endpoint_counterexample`).
   - Proves integer-side zero-boundary propagation (`left_zero_boundary_mulThreeHalvesCA_iterate`),
     concrete space-time trace escapes for `x = 1` and `x = 8` (`seed_one_and_eight_base_six_trace_escape`),
     and the **Phase B3 Negative Theorem** (`zero_and_two_adic_ghost_trace_obstruction`) showing why
     the unconstrained `{0, 1, 2}` trace subshift contains both the zero fixed point and 2-adic ghost
     trajectories (`periodicThreeParity`) whose seed residues never stabilize.

3. **[TransferOperatorJSRAndCarryFourier.lean](./TransferOperatorJSRAndCarryFourier.lean) &
   [TransferOperatorJSRAndCarryFourierChecks.lean](./TransferOperatorJSRAndCarryFourierChecks.lean)
   (Part II Sections 11, 12, and 13):**
   - **Perron–Frobenius-Free Sub-Invariant Weight & JSR Bounds (Sections 11.1 & 12.1):**
     Proves `subinvariant_weight_matrix_pow_bound` (`∑ j, (M^n) i j * w j ≤ ρ^n * w i`) and
     `common_subinvariant_weight_jsr_bound` across arbitrary words `ω : ℕ → Fin m`.
   - **Coupled Mod-`2^k` Transfer Criticality (`ρ_k ≥ 1`, Sections 11.2, 11.3 & 12 Negative Result):**
     Proves `no_subcritical_weight_of_self_loop`, `no_subcritical_weight_of_three_cycle`,
     `archimedean_only_density_fallacy_supercritical` (`ρ ≥ 4/3 > 1`), and
     `mod_two_pow_ghost_self_loop_at_all_depths` — showing that at **every** finite 2-adic depth `k`,
     the 2-adic ghost fixed points (`19 r_k + 9 ≡ 0`, `2059 v_1 ≡ 1`, `58025 v_2 ≡ 1 (mod 2^k)`)
     create self-loops in the mod-`2^k` state graph, forcing `ρ_k ≥ 1` and `JSR ≥ 1` for every
     fixed congruence depth `k`.
   - **3-Adic Carry Memory Erasure & Exact Word-to-Carry Injectivity (Section 13 & Section 6 Resolution):**
     Proves `wordCarry ε (n + m) = 3^m * wordCarry ε n + 2^n * wordCarry (shiftStream ε n) m`
     (`wordCarry_add_eq_three_pow_mul_add_two_pow_mul_shift`), `m`-step memory erasure modulo `3^m`
     (`wordCarry_mod_three_pow_eq_two_pow_mul_shift_mod`), and the **Exact 3-Adic Carry Injectivity
     Theorem (`wordCarry_mod_three_pow_eq_iff_parity_eq`, `aligned_carry_collision_iff_exact_factor_match`)**:
     two length-`m` parity windows have equal normalized carry modulo `3^m` **if and only if they are
     identical bit-for-bit** (`∀ j < m, ε₁ j % 2 = ε₂ j % 2`). This proves that non-identical anagrams
     never collide in their normalized `3^m` carry and that the carry palette size equals the full
     factor complexity `P(m)`.

4. **[SolenoidRigidityDiscrepancyAndRenormalization.lean](./SolenoidRigidityDiscrepancyAndRenormalization.lean) &
   [SolenoidRigidityDiscrepancyAndRenormalizationChecks.lean](./SolenoidRigidityDiscrepancyAndRenormalizationChecks.lean)
   (Part II Sections 14, 15, 16, 17, 20 & 21):**
   - **Measure-Rigidity Obstruction (Section 14):** Proves `single_generator_orbit_not_two_or_three_invariant`
     (`2 * x_0, 3 * x_0 ∉ O_{3/2}(x_0)`) and `finite_horizon_confinement_not_two_or_three_invariant`
     (explicit counterexamples `α = 2/9` and integer seed `a = 9` at `N = 3`).
   - **Discrepancy & Erdős–Turán Reduction (Section 15):** Proves `lowerHalfCount_add_upperHalfCount_eq`,
     `discrepancy_lt_half_forces_mahler_escape`, and `erdos_turan_conditional_mahler_reduction`.
   - **Dyadic-Block Uniqueness vs. Emptiness (Section 16):** Proves `distinct_dyadic_seeds_cannot_share_prefix_past_W`
     and `single_dyadic_survivor_witness_149`.
   - **Mahler's Method Value-Irrationality Bridge (Section 17):** Proves
     `mahler_method_irrational_value_excludes_integer_seed`.
   - **First-Return 2-Adic Non-Self-Similarity (Section 20):** Proves
     `first_return_two_adic_defect_and_multiplier_mismatch` (`E(3) = 0` vs. `E(4) = -72 ≠ 0` and
     `27/8 ≠ 81/16`).

## 26. Key findings and next-round questions

1. **Why fixed-depth mod-`2^k` transfer operators and raw `3^m` carry collisions stall (and what breaks the symmetry):**
   - `mod_two_pow_ghost_self_loop_at_all_depths` proves that any finite-state method tracking only
     residues modulo a fixed `2^k` is blocked by the 2-adic ghost fixed points (`-9/19`, `1/2059`, `1/58025`),
     which are genuine periodic orbits in $\mathbb{Z}_2 \times \mathbb{R}$.
   - `wordCarry_mod_three_pow_eq_iff_parity_eq` proves that in the 3-adic carry group $\mathbb{Z}/3^m\mathbb{Z}$,
     the carry map on length-`m` binary words is **bijective onto its image** (zero collisions between
     distinct words).
   - **Implication for Round 2:** A successful obstruction must use the **positivity and archimedean
     size bound of the ordinary integer seed** (`0 < a_0 < 2^W`, equivalently `η_N = 0` for `N ≥ W`),
     not merely local congruence transitions.
2. **Most promising concrete targets for Round 2:**
   - **Target R2.1 (Pointwise Parity Surplus under Feasibility):** Use the new look-ahead-free potential
     `deficitPotential ε N = N + 3 - 3 * oddParityCount ε N ≥ 0` together with `η_N = 0` (`N ≥ W`):
     since `deficitPotential` only increases on `s ≥ 4` blocks (`+1` on `1000`) and is stationary on
     `s = 3` (`100`) where `v_2(19 q_N + 9)` drops by `3`, bound how many `s = 3` blocks can occur
     between `s ≥ 4` blocks before `v_2(19 q_N + 9)` is exhausted.
   - **Target R2.2 (Closing the Lower Strip `[0, 8/81)` Without Stationarity):** Formalize the
     transition graph between the Rung-`g` leak windows $L_g = [2^{g-1}/3^g, z_g^*)$ for varying $g \ge 4$
     to determine whether an orbit that visits infinitely many distinct rungs $g_k$ forces unbounded
     seed-extension bits $\eta_N = 1$.
   - **Target R2.3 (Superlinear Sub-Exponential Factor Complexity):** Extend the $(p, q)$ repetition
     cutoff from linear complexity $p(L) \le \kappa L + C_0$ to general sub-exponential complexity
     using multi-scale Ostrowski / bispecial return times.

