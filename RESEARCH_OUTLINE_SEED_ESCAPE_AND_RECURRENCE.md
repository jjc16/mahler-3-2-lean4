# Research outline: integer-seed escape and recurrence

## Aim and present assessment

The next stage should prioritize the general Mahler conjecture, not merely add
more examples of excluded symbolic sequences. There are credible research
directions, but we do not currently have a complete general-case argument.
Everything labeled a target below is proposed work, not a new Lean theorem.

This follows the substantially implemented
[structured-aperiodic and finite-seed plan](./RESEARCH_PLAN_STRUCTURED_APERIODIC_AND_FINITE_SEEDS.md).
It separates:

1. A general-case program: prove escape for every positive ordinary integer seed.
2. Achievable stronger results: quantitative seed-bit forcing and broader
   structured-family exclusions.
3. Supporting engineering: exact state semantics, certified computations, and
   accurate mathematical interfaces.

**Main recommendation:** use structured examples to develop and test a reusable
integer-escape certificate, then seek an induction that works without assumptions
on complexity, recurrence, average block length, or bounded block lengths.

## 1. What is established, and what is not

The current source includes:

- An exact correspondence between parity prefixes and residues modulo `2^N`,
  with ordinary nonnegative integer realization equivalent to eventual
  stabilization of the least residues.
- Exact rational finite-feasibility inequalities and an endpoint/shift bridge
  from perpetual finite feasibility to strict infinite survival.
- An elementary exclusion of the three-step zero-encoded Thue-Morse parity
  stream, including a mismatch before `60W` for positive seeds below `2^W`.
- Mechanical two-letter block-chain exclusions with the complexity hypothesis
  derived for the actual coding.
- A subcritical complexity exclusion under a positive limiting mean and good
  complexity bounds at arbitrarily large lengths.
- Local defect valuation locks, explicit defect sums, and an exclusion of
  sustained rapid block-length growth.

Relevant developments:
[seed residues](./ExactSeedResidueTreeAndStabilization.lean),
[endpoint and complexity results](./EndpointCompactnessAndBalancedExclusion.lean),
[Thue-Morse](./ThueMorseMahlerFunctionalEquation.lean), and
[defect identities](./SparseDefectCocycleAndValuationLock.lean).

These results do not cover every possible parity or block-length sequence.
In particular, an exceptional survivor need not have a limiting mean, bounded
block lengths, uniform recurrence, or low complexity. Occasional long runs,
repetitions, or contracting quotient steps are not all prohibited: the existing
exclusions have quantitative hypotheses.

The finite experiment on seeds `1,...,4095` reported failure by horizon 29,
with seed 149 attaining that horizon. This is an exact-arithmetic observation,
not yet a saved, Lean-certified bounded-seed theorem, and not evidence of a
proved universal logarithmic escape bound.

## 2. Central general-case target: positive stabilized branches must fail

Let `r_N` be the least nonnegative seed residue realizing a parity prefix.
The established extension rule is

    r_(N+1) = r_N + eta_N * 2^N,       eta_N in {0,1}.

A fixed ordinary integer seed has only finitely many nonzero binary digits.
Consequently, its compatible residue branch eventually has `eta_N = 0`.
This fact concerns the extension digits `eta_N`, not the orbit's parity digits.
The orbit parity need not become eventually zero.

The decisive target is:

> Every exactly reachable feasible branch with a positive stabilized seed
> eventually becomes infeasible.

Equivalently, infinite feasibility must force either the zero seed or infinitely
many nonzero extension digits. This is a general-case reformulation, not itself
an obstruction or a proof.

The zero-seed exception is essential: zero really does survive forever.
The final conjecture interface must explicitly compose the fractional-part,
positive-seed, finite-feasibility, and strict-endpoint shift bridges.

### 2.1 An exact coupled state to investigate

Write

    e_N = epsilon_N mod 2
    C_0 = 0
    C_(N+1) = 3*C_N + 2^N*e_N
    ell_N = C_N / 3^N
    U_N = min_{0 <= j <= N} (C_j/3^j + (1/2)*(2/3)^j).

For a seed compatible with the prefix, the full finite companion set should be
expressed by the exact membership theorem

    ValidCompanionUpTo(a, a+x, N)  iff  ell_N <= x < U_N.

Nonemptiness is already proved; the membership API and transitions should be
completed. The real argument here is `a+x`, not just the offset `x`.

Define the signed, denominator-cleared margin

    D_N = 2*3^N*(U_N - ell_N).

Direct algebra suggests the integer recurrence

    D_0 = 1
    D_(N+1) = min(2^(N+1), 3*D_N - 2^(N+1)*e_N).

Finite feasibility is exactly `D_N > 0`. Use integers, not truncated natural
subtraction: a negative margin records a genuine failure.

To retain integer compatibility, also track

    q_N = (3^N*r_N + C_N) / 2^N = orbit(r_N, N).

Choosing an extension digit `eta_N` should give the coupled transition

    e_N       = (q_N + eta_N) mod 2
    r_(N+1)   = r_N + eta_N*2^N
    q_(N+1)   = (3*q_N + 3^(N+1)*eta_N + e_N) / 2
    D_(N+1)   = min(2^(N+1), 3*D_N - 2^(N+1)*e_N).

The displayed division is exact for compatible states. These formulas are
derived proof targets; they have not been added to Lean in this planning stage.
When `eta_N = 0`, the quotient transition is the original integer orbit step.

**Why this might help:** it puts the finite binary seed and the real interval
constraint into one exact transition system. Studying only the scalar margin
throws away the very arithmetic constraint we need.

**Why it is not already a proof:** the quotient grows, and there is no known
well-founded rank for all reachable positive states with a zero extension tail.
Renaming the original recurrence does not resolve this.

### 2.2 Search for an inductive escape certificate

The useful next object is a certificate covering a parameterized family of
reachable states, not another collection of isolated orbit computations.
Such a certificate would prove that every allowed continuation either:

1. Makes the margin nonpositive;
2. Requires another nonzero extension digit; or
3. Enters a state with a strictly smaller, nonnegative integer rank.

Prove that the cases exhaust all continuations and that every transition
preserves the exact reachability invariants. A finite abstract graph is useful
only when its arithmetic soundness and the treatment of any surviving cycles
are proved.

Start with a restricted infinite family to test the mechanism. A certificate
for one family is progress, but it is not a general proof until its coverage is
unconditional.

**Success criterion:** an actual infinite-family escape theorem depending on
the original finite seed, with no hidden eventual-periodicity or finite-state
realizability assumption.

**Stop criterion:** if an abstraction retains feasible cycles because it forgot
integer compatibility, refine that missing information or abandon the
abstraction. Do not count another symbolic cycle search as an exclusion.

## 3. A second general-case formulation: certified growing seed lower bounds

Define mathematically

    B(N) = least positive integer seed surviving through horizon N.

This minimum exists: the seed `2^N` survives through horizon `N` with an integer
companion. Thus `1 <= B(N) <= 2^N`. Since survival sets shrink with the horizon,
`B(N)` is nondecreasing.

The global escape target becomes

    B(N) tends to infinity.

The repository already has finite-residue checking and an unbounded-exclusion
bridge in [OddBlockCoupling.lean](./OddBlockCoupling.lean) and
[BridgeOneArchimedean.lean](./BridgeOneArchimedean.lean).
Reuse these; do not introduce an unrelated second checker.

### Proposed work

1. Certify the reported bounded experiment through the existing checker, or a
   proved-equivalent efficient margin recurrence.
2. Save explicit failure horizons so results can be reproduced and checked.
3. Test proposed state ranks and parameterized residue exclusions against the
   exact checker before formalizing them.
4. Seek an inductive certificate for whole dyadic seed ranges, or a proved rule
   that advances an already certified lower bound.

An indefinitely extendable induction is qualitatively different from checking
one larger seed range. No fixed finite lower bound proves divergence, and an
observed `O(log a)` failure horizon must not become an assumed lemma.

This route and Section 2 are complementary views of the same central problem,
not two independent solutions.

## 4. First achievable milestone: quantitative seed-bit forcing

The existing encoded Thue-Morse cutoff should yield

    seedResidue(epsilon, 30R) >= 2^R,       R = 2^k.

Proof plan:

1. The least residue realizes the length-`30R` parity prefix.
2. It is nonzero, since this prefix contains a one.
3. A positive realizing residue below `2^R` contradicts the existing finite
   cutoff, with `W = R`.

Combining this bound with residue monotonicity and a dyadic sandwich should give

    for every N0 >= 1, some N with N0 <= N < 60*N0
    satisfies r_N < r_(N+1).

This would force another nonzero seed bit within a controlled multiplicative
window. It is stronger than qualitative non-stabilization and is a useful
prototype for Section 2.

It does not establish positive density of nonzero digits or irrationality of
the associated 2-adic value. It remains a theorem about a particular structured
parity family, not all feasible branches.

**Deliverable:** exact Lean statements for residue growth and bounded waiting
for a strict extension, using the existing finite cutoff.

## 5. Broaden exclusions without assuming an independently supplied mean

### 5.1 Uniform recurrence and low complexity: a literature-supported bridge

For a word over a finite alphabet, uniform recurrence means every occurring
finite factor reappears with bounded gaps. Its shift system is minimal.

Boshernitzan's complexity bound implies that a minimal subshift with

    liminf P(L)/L < 2

is uniquely ergodic. Unique ergodicity gives letter frequencies for every point,
and hence a limiting mean for a finite alphabet of positive block lengths.
Periodic cases can be handled separately.

Since

    log(2)/log(3/2) = approximately 1.709511 < 2,

this suggests the following target:

> A uniformly recurrent block-length word over a finite alphabet of positive
> integers, with global liminf factor complexity below `log(2)/log(3/2)`,
> cannot support an infinite integer block chain with perpetual positive slack.

This removes the separately assumed limiting mean for that class.
The current arithmetic exclusion supplies the final contradiction; the new
work is the recurrence/frequency bridge and the literal global-complexity
interface.

**Source verification:** the introduction of Cyr and Kra,
[*Counting generic measures for a subshift of linear growth*,
arXiv:1505.02748](https://arxiv.org/abs/1505.02748), states the minimal-subshift
bound: `liminf P(L)/L < k` allows at most `k-1` ergodic measures.
Taking `k = 2` gives the needed implication. The same introduction distinguishes
the separate unique-ergodicity criterion `limsup P(L)/L < 3`.
Do not substitute `liminf < 3` for that latter statement.

**Formalization gate:** an external citation is not a Lean proof. First inspect
available dynamical-systems infrastructure. Either formalize the needed
implication, prove a narrower combinatorial frequency theorem, or explicitly
leave the result conditional. Do not insert an axiom and call the bridge done.

This is a broader class exclusion, not a general-case solution: uniform
recurrence and a finite block alphabet remain genuine assumptions.

### 5.2 Scale-local balance when a global mean does not exist

The finite repetition estimate needs approximate linearity only on the prefix
used to find a repeated window. Investigate replacing one global slope by
scale-dependent slopes `lambda_L > 0`.

At arbitrarily large good lengths, require

    C(L) <= kappa*L + C0
    E_L = max_{n <= C(L)+L} |T(n) - lambda_L*n|
    E_L / (lambda_L*L) tends to zero,

with `lambda_L` bounded below by a fixed positive constant and
`kappa*log(3/2) < log(2)`. The existing finite inequality

    lambda_L*(q-p*kappa)*L + 1
      <= (2*q+p)*E_L + p*lambda_L*C0 + q*W + p

should then contradict survival.

**Success criterion:** derive these hypotheses for an actual family without a
global limiting mean. A restatement of the finite inequality alone is not a
meaningful new exclusion.

Also finish the global factor-count/liminf wrapper and the named normalized
maximum-discrepancy convergence lemma. These are interface improvements, not
separate general-case breakthroughs.

## 6. Reusable substitution certificates, not an endless list of examples

Extract a small mechanism: a finite repeated window, a proved inflation law,
and an exact integer power inequality imply a finite seed cutoff.
Use [MahlerDemandA.lean](./MahlerDemandA.lean) and the existing weighted block
repetition bounds.

Two concrete test cases:

### 6.1 Thue-Morse as block lengths

For `s(n) = a + (b-a)*t(n)` with `3 <= a <= b`, put `R = 2^k`.
The known repetition at origins `0` and `6R`, of length `4R`, and pair balance
should give

    S = T(4R) = 2R*(a+b)
    T(6R) = 3R*(a+b).

The existing `p = 3, q = 5` repetition inequality yields

    (a+b)*R <= 5W+2

under its finite-chain and slack hypotheses, for `a_0 < 2^W`.
Choosing a larger dyadic scale would exclude the infinite family.
This is a different coding from the already excluded zero-encoded parity word.

### 6.2 Period-doubling as an encoded parity word

For the substitution `0 -> 01`, `1 -> 00`, the candidate base repetition is

    d[0,3) = 010 = d[4,7).

After dyadic inflation and three-step zero encoding, expect matching parity
windows of length `9R` separated by `12R`. Since `3^12 < 2^20`, the proposed
cutoff is a mismatch before `21R` for positive seeds below `2^W` when `W <= R`,
and hence before `42W` after choosing the dyadic scale.

Verify the recurrence, indexing, inflation, and nonperiodicity before claiming
the result. These are proposed bounds, not currently formalized theorems.
Neither example justifies a claim about every automatic or substitutive word.

## 7. Secondary routes and explicit stopping rules

- **Sparse defects:** require a bound tied to the original seed that survives
  later signed cancellation. The current normalized residual grows with the
  boundary; it is not a descending rank.
- **Intermittent quotient contraction:** a return argument must control
  intervening expansion. Sustained contraction is already excluded; occasional
  contraction is not enough.
- **Backward minimal-seed descent:** both predecessor integrality and companion
  survival must be established. Existing arithmetic predecessors or local
  fractional lifts alone do not give universal descent. See
  [FiniteSeedCarryAndBackwardDescent.lean](./FiniteSeedCarryAndBackwardDescent.lean).
- **Distributional estimates:** density decay or generic behavior cannot remove
  a single exceptional stabilized branch. Use estimates only when they yield a
  deterministic bound for every positive integer seed.
- **More symbolic restrictions:** all block lengths at least three already
  leave many fractionally admissible words. A general argument must retain
  integer compatibility, not merely exclude another popular sequence.

## 8. Recommended execution order and quality gates

1. **Repair exact state semantics.** The current
   [FeasibleSeedNode declaration](./ExactSeedResidueTreeAndStabilization.lean)
   uses default field values, which callers can override. Replace this with
   canonical derived data or explicit invariants; prove full companion-set
   membership and the coupled transitions.
2. **Prove quantitative Thue-Morse residue growth.** This provides a manageable,
   explicit seed-bit escape certificate.
3. **Certify the bounded experiment and test candidate ranks.** Reuse the
   established checker and record reproducible failure witnesses.
4. **Attempt one parameterized arithmetic escape induction.** This is the main
   general-case research effort. Report precisely which states it covers and
   why remaining states escape its argument.
5. **Pursue the recurrence/frequency bridge.** Assess proof-engineering cost
   before committing to a large ergodic-theory development.
6. **Extract substitution certificates and test scale-local balance.** Keep
   these supporting projects bounded; require a stronger theorem or a genuinely
   new class, not additional identities alone.

For implemented results: build affected modules, run their check files with
warnings as errors, inspect principal theorem axioms, and verify assumptions
against the advertised statement. Preserve the zero exception and strict
endpoint conventions in tests.

Before a new publication update, reconcile the
[Markdown paper](./MAHLER_FORMALIZATION_PAPER.md),
[TeX source](./MAHLER_FORMALIZATION_PAPER.tex),
[PDF](./MAHLER_FORMALIZATION_PAPER.pdf), and [README](./README.md).
Recent Markdown/source changes do not establish that the PDF or public
repository has been updated.

## Bottom line

There is a defensible route toward the general case: develop an arithmetic
certificate forcing infinitely many seed extensions, or equivalently prove
unbounded growth of certified positive-seed lower bounds. The missing piece is
an unconditional induction or well-founded obstruction; neither is presently
known here.

The immediate milestones are realistic and useful. They should be measured by
new excluded families, quantitative escape statements, and reduced assumptions.
They do not yet warrant a claim that a complete proof is close.
