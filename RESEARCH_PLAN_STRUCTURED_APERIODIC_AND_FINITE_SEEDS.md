# Next research stage: structured aperiodic exclusions and finite-seed escape

Date: 2026-10-18

## Objective

Produce a complete named aperiodic-class exclusion, then seek an obstruction
that applies beyond low-complexity words to positive ordinary integer seeds.
Mahler's conjecture remains open. The proposed results below are proof targets,
not claims of new Lean theorems or mathematical priority.

This plan follows [the previous research outline](./RESEARCH_OUTLINE_NEXT_STAGE.md).
It deliberately prioritizes finishing useful implications over adding more
identities or bundled synthesis theorems.

## 0. Establish the exact starting point

The latest development has proved important building blocks:

- The perpetual-finite-feasibility supremum and strict-endpoint shift
  alternative in
  [EndpointCompactnessAndBalancedExclusion.lean](./EndpointCompactnessAndBalancedExclusion.lean).
- A parameterized balanced repetition bound, using natural numbers `p,q`
  with `q >= 1` and `3^q < 2^(p+q)`. It gives an infinite contradiction when
  `p*kappa < q`, under the stated discrepancy and prefix-complexity hypotheses.
- A constructive parity-prefix/seed-residue correspondence, including the
  exact characterization of ordinary nonnegative seeds by eventual residue
  stabilization, in
  [ExactSeedResidueTreeAndStabilization.lean](./ExactSeedResidueTreeAndStabilization.lean).
- Real Thue-Morse generating-function equations and finite integer carry
  identities in
  [ThueMorseMahlerFunctionalEquation.lean](./ThueMorseMahlerFunctionalEquation.lean).
- Signed defect identities and a first-defect valuation lock in
  [SparseDefectCocycleAndValuationLock.lean](./SparseDefectCocycleAndValuationLock.lean).

### Claims to finish or narrow

1. **Mechanical words:** bounded discrepancy has been proved, but the displayed
   exclusion theorem still assumes its factor-complexity bound. Prove that
   bound for the actual mechanical coding before calling this an unconditional
   exclusion of every such coding.
2. **Sharp threshold:** the proved family is indexed by explicit `p,q`.
   Supply the rational-approximation/logarithm bridge before advertising a
   single Lean theorem for every slope below
   `1/log_2(3/2)`, approximately `1.709511`.
3. **Thue-Morse:** the existing infinite series is real-valued. Its finite
   integer divisibility bridge does not establish irrationality of a 2-adic
   value or exclude integer realization.
4. **First-defect lock:** it is a necessary condition already forced by a
   finite prefix. Later defects cannot change that low-order valuation, but
   this is not an exclusion of all sparse-defect continuations.
5. **Documentation:** correct stale constants (`+q` versus the proved `+1`,
   and `+5` versus `+1` in the specialized bound), distinguish recursive
   cocycles from unproved explicit-sum presentations, and reconcile the paper,
   README, and PDF before a further publication update. Do not infer progress
   from unverified module/file counts.

**Completion criterion:** each advertised result points to a theorem whose
quantifiers and assumptions match the prose. Keep unproved bridges visible.

## 1. First priority: exclude encoded Thue-Morse by elementary repetition

**New opportunity:** a p-adic transcendence theorem may be unnecessary for the
specific encoded Thue-Morse stream already defined in Lean.

### A concrete scalable repetition

Let `t` be the Thue-Morse sequence and let

    epsilon(3n) = t(n),
    epsilon(3n+1) = epsilon(3n+2) = 0.

The base windows satisfy

    t[0,4) = 0110 = t[6,10).

The identities `t(2n)=t(n)` and `t(2n+1)=1-t(n)` should imply, for every
`R=2^k`,

    t[i] = t[6R+i]                  for 0 <= i < 4R,
    epsilon[i] = epsilon[18R+i]    for 0 <= i < 12R.

Prove this inflation lemma by induction; no global complexity estimate is
needed. The base windows, scaled equalities for `k=0,...,8`, and the integer
power comparison below passed finite sanity checks during preparation of this
plan. These checks are not a proof of the all-scale claim.

### Why this should exclude every positive integer seed

The existing
[early-window theorem](./MahlerDemandA.lean) rules out matching parity windows
of length `L` at origins `i < j <= H` when

    (a+1) * 3^H < 2^(L+H),    a > 0.

Use

    L = 12R,    i = 0,    j = H = 18R,
    3^18 = 387420489 < 536870912 = 2^29.

If `a < 2^W` and `R >= W`, then

    (a+1) * 3^(18R)
      <= 2^W * 3^(18R)
       < 2^(W+29R)
      <= 2^(30R).

Thus a positive seed cannot match this encoded stream for all `n < 30R`.
This argument uses integer growth and parity separation alone, not a
fractional-survival hypothesis.

### Lean deliverables

1. Prove the all-scale Thue-Morse window-inflation lemma.
2. Transfer it through the existing three-step encoding.
3. Prove the explicit finite theorem:

       0 < a, a < 2^W, W <= 2^k
       ==> not (forall n < 30*2^k,
                  orbit a n % 2 = tmEncodedParity n).

4. Deduce no positive integer realizes the entire stream; handle `a=0`
   separately using its all-zero orbit.
5. Apply the existing stabilization equivalence to conclude that this stream's
   seed residues do not eventually stabilize at any nonnegative integer.
6. Combine that exclusion with the already proved real fractional-tail
   admissibility. This gives an explicit structured aperiodic example that is
   fractionally admissible but cannot come from an ordinary integer seed.

For `W >= 1`, choosing the smallest power of two `R >= W` gives `R < 2W`.
The proposed finite obstruction therefore uses fewer than `60W` parity symbols.
Verify this bound, not just the infinite corollary.

**Next extension:** prove a general scalable-early-repetition criterion, then
test fixed shifts and complemented codings. For a fixed shift by `h`, trim the
matching windows to length `12R-h`; `R >= W+h` supplies the same growth margin.
Handle a fixed finite preperiod by shifting the integer orbit as well.

**Success:** a complete unconditional named-stream/family exclusion, not another
conditional generating-function theorem.

**Limit:** arbitrary automatic or morphic sequences need not have this favorable
early repetition. Do not extrapolate from Thue-Morse to all such sequences.

## 2. Finish the mechanical-word bridge and broaden the discrepancy hypothesis

**Priority:** high-confidence expansion of the aperiodic-class theorem.

### 2A. Derive mechanical factor complexity instead of assuming it

For the existing coding

    s(n) = a + (b-a) *
      (floor(alpha*(n+1)+rho) - floor(alpha*n+rho)),

with `a <= b` and `0 <= alpha <= 1`, prove that every length-`L` factor is
determined by the phase `x = fract(alpha*r+rho)` of its origin.

The cumulative differences `floor(x+i*alpha)`, for `1 <= i <= L`, change only
at at most `L` thresholds in `[0,1)`. Partition that interval consistently at
the thresholds to obtain at most `L+1` factors.

Required edge cases:

- Coincident thresholds and rational slopes;
- Phase exactly on a threshold;
- `alpha=0`, `alpha=1`, and `a=b`;
- `L=0` in the definitions, even if exclusions use only `L>=1`.

Combine this factor bound with the proved telescoping/discrepancy theorem and
automatic slack positivity for `3 <= a`. The final theorem must quantify over
the actual mechanical sequence and conclude that no infinite valid integer
block chain has those lengths, with no classifier or complexity assumption
left over. Irrational slopes with distinct letters give the intended
Sturmian subclass.

### 2B. Replace bounded discrepancy by an asymptotic mean

The existing theorem assumes

    |T(n)-lambda*n| <= D    for one fixed D.

A stronger target only assumes

    T(n)/n --> lambda,     0 < lambda < infinity.

For a finite-alphabet word with global factor count `P(L)`, target:

    liminf P(L)/L < 1/log_2(3/2)
    ==> no infinite surviving integer block chain.

The argument needs good complexity bounds at arbitrarily large lengths, not
at every length.

**Proof route:** choose a fixed strict margin `kappa < q/p` and an unbounded
sequence of lengths with `P(L) <= kappa*L`. Pigeonhole supplies repeats with
later origin `r2 <= P(L)`. Set

    E_L = max_{0 <= n <= P(L)+L} |T(n)-lambda*n|.

Prove `E_L/L --> 0` along these lengths. The existing finite inequality, with
`D=E_L` and complexity intercept zero, becomes

    lambda*(q-p*kappa)*L + 1
      <= (2q+p)*E_L + q*W+p.

Divide by `L` to obtain a contradiction.

**Supporting bridges:** define global factor sets with their finiteness
hypotheses, relate their cardinalities to the existing prefix counts, and
prove the rational `p,q` selection from the strict logarithmic margin.

**Success:** exclusion under an asymptotic mean and subcritical *liminf*
complexity, strictly weaker assumptions than bounded discrepancy at all lengths.

**Limit:** an arbitrary surviving word is not known to have an asymptotic mean,
low complexity, or suitable early repetitions.

## 3. Main long-term attack: couple exact feasibility to seed stabilization

**Priority:** closest to the general conjecture, but exploratory.

The existing seed tree encodes every parity word. It must now be coupled to
the exact survival condition rather than treated as an exclusion by itself.

### Exact finite state semantics

For a parity prefix of length `N`, let `C_j` be its existing `wordCarry` at
depth `j`. The orbit identity gives

    lowerBound(a,j) = a + C_j/3^j.

Consequently, the feasible fractional-offset interval is

    [ C_N/3^N,
      min_{0 <= j <= N} (C_j/3^j + (1/2)*(2/3)^j) ).

Prove this formula and its nonemptiness criterion using exact rational
arithmetic. Include both the least seed residue `r_N` and this interval in a
node. Establish that all nonnegative seeds congruent to `r_N` modulo `2^N`
have exactly this offset feasibility through horizon `N`.

The distinction is then precise:

- A compatible symbolic branch may add infinitely many nonzero seed bits.
- An ordinary integer branch eventually has only zero seed-extension bits.
- The zero seed is genuinely feasible and must never be excluded accidentally.

### Bounded experiment and certificate target

First reproduce the periodic-three and encoded Thue-Morse exclusions in this
representation. Then examine positive seeds below `2^12`, stopping each path
at its exact first empty interval or horizon `256`. Report unresolved cases
explicitly. Use the experiment to falsify proposed carry/slack rankings, not
to infer a universal theorem from a finite search.

Seek one of:

1. A well-founded ranking that strictly decreases during a feasible,
   eventually-zero seed suffix;
2. A return certificate forcing another nonzero seed bit;
3. A seed-dependent, proved finite escape bound for a precisely defined
   nonperiodic family not covered by Sections 1 or 2.

A finite abstraction must prove transition soundness and account for omitted
high carries. If two exact states with the same abstraction require different
conclusions, refine or abandon that abstraction; do not silently assume a
finite-memory model.

**Success:** a certificate applied to an infinite family with a formal soundness
proof. A theorem excluding every positive stabilized feasible branch would
address the central obstacle, but is not promised by this plan.

**Stop condition:** residue-density decay, larger graphs, or longer tested
horizons without a new invariant are not sufficient progress.

## 4. Audit the defect lock before investing in a sparse-defect attack

**Priority:** supporting investigation, not the next centerpiece.

There is a useful simplification to check. For a block boundary `b` with
`3b+1=2^c*u`, the existing invariant `I(b)=19b+9` satisfies

    3*I(b) = 19*2^c*u + 8.

For `c>=4`, this already forces `v_2(I(b))=3`. Each preceding length-three
block adds exactly `3` to that valuation through

    8*I(b_next) = 27*I(b).

Thus the current first-defect valuation lock can be obtained from the prefix
ending at the first defect; later survival is not required. Formalize this
short local derivation and distinguish it from a new global obstruction.

Only continue the sparse-defect route if the signed cocycle yields a height or
valuation estimate not already implied by this prefix constraint, the
single-block spike cutoff, or the existing repeated-window bounds.

In particular, the normalized residual

    (3^T(m)*I(a) + defectCocycleSum(s,m)) / 2^T(m) = I(b_m)

is the growing boundary invariant, not a descending rank. A successful
multi-defect argument must control cancellation while retaining a bound in
terms of the original seed, rather than repeatedly replacing it by a larger
orbit boundary.

**Success:** one precisely stated sparse-defect family excluded beyond the
existing bounds. **Otherwise:** retain the identities as supporting tools and
defer this route.

## Recommended order and quality gates

1. Correct claim scope in Section 0.
2. Prove the concrete Thue-Morse finite cutoff and seed non-stabilization.
3. Finish mechanical complexity and the direct mechanical-chain exclusion.
4. Prove the asymptotic-mean/liminf-complexity extension and logarithmic bridge.
5. Run the bounded exact-state investigation for a genuinely new certificate.
6. Pursue sparse defects only if the independence test in Section 4 succeeds.

Reuse existing definitions and lemmas. Add only the development/check modules
needed for these results; avoid another module-count-based grand synthesis.
Compile each targeted module and its checks, inspect principal theorem axiom
dependencies, then run the integrated build after registration. No `sorry`,
custom mathematical axiom, or unproved transcendence input may be presented
as an unconditional result.

Before publication, record which targets actually succeeded, synchronize the
human-readable sources and PDF, and verify the actual published revision.

## What completion would mean

The near-term outcome would be complete exclusions of concrete structured
aperiodic families, a broader mean/complexity theorem, and an exact framework
for investigating ordinary-seed escape.

It would still not prove Mahler's conjecture unless the exceptional positive
stabilized branches are excluded without assumptions about complexity, average
block length, repetitions, or defect spacing. Words lacking a limiting mean,
as well as high-complexity words with one, remain possible obstacles.
