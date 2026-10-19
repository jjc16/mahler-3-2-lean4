# Next-stage research outline: aperiodic exclusions and finite-seed realization

Date: 2026-10-18

## Objective and current status

Mahler's conjecture remains open. The next valuable result should either:

1. Exclude a precisely defined, substantial aperiodic class; or
2. Give a new obstruction to realizing an indefinitely compatible symbolic or
   2-adic path by a fixed positive integer seed.

This outline proposes research, not established theorems. It is based on the
current Lean statements, not on the stronger descriptions in earlier responses.
No new mathematical priority claim is made.

### Scope corrections before proceeding

- The `{3,4}` and `[3,5]` low-complexity finite-window bounds are proved in
  [SturmianAndBalancedComplexityExclusion.lean](./SturmianAndBalancedComplexityExclusion.lean).
  To obtain named infinite-class exclusions, explicitly supply classifiers from
  standard factor-complexity definitions and quantify over arbitrarily large
  windows.
- The general balanced theorem assumes a weighted discrepancy inequality. It
  does not yet derive that hypothesis from the usual definition of balanced
  cumulative steps.
- Its parameter `delta` is a natural number with `1 <= delta <= 17`. Consequently,
  the displayed interpretation `(17-delta)/10` reaches at most `1.6`, not every
  complexity slope below `1.7`. The exact repetition inequality suggests a
  limiting threshold near `1.7095`; that full theorem is not yet formalized.
- The infinite-horizon bridge assumes one real number satisfies all strict
  upper-endpoint conditions. It does not itself prove that separate companions
  at every finite horizon have a common strict infinite companion.
- [SubstitutionMahlerMethodAndGrandSynthesis.lean](./SubstitutionMahlerMethodAndGrandSynthesis.lean)
  proves uniform macro-block identities. It does not yet establish a closed
  nonperiodic substitution functional system or a p-adic transcendence theorem.
- Opposite real signs of two candidate limits are not a contradiction: real and
  2-adic limits can differ. The periodic obstruction works because a geometric
  sum has the same rational value at both places.

## 0. Foundation: finish the endpoint and class-definition bridges

**Priority:** necessary proof hygiene, not the main conjectural breakthrough.

For a fixed positive integer seed `a`, write

    L_n = (2/3)^n * orbit a n,
    U_n = (2/3)^n * (orbit a n + 1/2).

Assuming a companion exists separately at every finite horizon:

1. Prove `L_n` has a finite supremum `alpha`.
2. Prove `L_n <= alpha <= U_n` for every `n`.
3. Distinguish strict survival from an upper-endpoint hit.

If `alpha = U_j`, then

    alpha * (3/2)^j = orbit a j + 1/2.

For every `k >= 1`, the later value is

    (2 * orbit a j + 1) * 3^k / 2^(k+1).

Its numerator is odd, so its fractional part cannot equal `1/2`. Thus the closed
survival inequalities would imply strict survival after shifting beyond `j`.
Formalize this as a separate endpoint alternative; do not claim the original
seed necessarily has a strict companion.

**Deliverable:** an exact global bridge between perpetual finite feasibility and
existence of a positive Z-number, allowing a forward shift in the endpoint case.
Also supply standard finite-factor definitions for the aperiodic results.

## 1. Complete the balanced low-complexity exclusion at the sharp threshold

**Priority:** highest-confidence substantial aperiodic-class theorem.

Let `T(n)` be cumulative block steps and set

    gamma = log_2(3/2),
    H(a) = log_2(3 * (2*a + 1)) - 2.

The existing exact repeated-window inequality implies

    S < gamma * T(r2) + H(a),

where `S = T(r1+L)-T(r1)` and the length-`L` windows at `r1 < r2` agree.

### Proposed theorem

No infinite surviving integer block chain can satisfy both

    |T(n) - lambda*n| <= D               for every n,
    p(L) <= kappa*L + C                  for every positive L,

with fixed constants `lambda > 0`, `D,C >= 0`, and

    gamma * kappa < 1.

Here `p(L)` is the number of distinct length-`L` block factors.

### Proof mechanism

Pigeonhole gives matching windows with `r2 <= p(L)`. Balance gives

    S >= lambda*L - 2*D,
    T(r2) <= lambda*(kappa*L + C) + D.

Combining these estimates yields

    lambda*(1-gamma*kappa)*L
      < (2+gamma)*D + gamma*lambda*C + H(a).

The left side grows without bound, while the right side is fixed.

### First concrete family

Mechanical/Sturmian block codings using any two fixed allowed block lengths,
not just lengths in `[3,5]`. Prove bounded cumulative discrepancy and
`p(L) <= L+1` from the coding definition.

For two lengths at least `3`, slack positivity is automatic; the new exclusion
would therefore be purely an integer-realization obstruction. For codings using
length `2`, retain the survival hypothesis rather than assume admissibility.

**Lean strategy:** either use real logarithms carefully, or parameterize the
power comparison by integers `p,q` satisfying `3^q < 2^(p+q)` and choose
`gamma < p/q < 1/kappa`. Avoid a fixed integer margin that loses the threshold.

**Continue if:** the standard hypotheses, explicit finite bound, and infinite
contradiction all compile without additional orbit assumptions.

**Limitation:** high-complexity or unbalanced words remain untouched. Do not
claim all remaining candidates have slope at least `1.7095` until this bridge
has actually been proved.

## 2. Main long-term attack: the exact seed-residue tree

**Priority:** most directly addresses exceptional integer survivors.

For a parity word `epsilon_0,...,epsilon_(N-1)`, define its carry

    C_N = sum_{j<N} epsilon_j * 2^j * 3^(N-1-j).

The step recurrence gives

    2^N * a_N = 3^N * a_0 + C_N.

Because `3^N` is invertible modulo `2^N`, the word determines a unique seed
residue `r_N` in `[0,2^N)`. Establish both directions of this parity encoding.

Compatible residues satisfy

    r_(N+1) = r_N + eta_N * 2^N,   eta_N in {0,1}.

An infinite compatible path comes from an ordinary nonnegative integer exactly
when its least residues eventually stabilize. The all-zero seed is a genuine
exception and must be separated from positive seeds.

### Research target

Prove that a strictly admissible infinite path cannot have least residues
eventually constant at a positive value.

This target is close to the original conjecture, not an automatic consequence
of the encoding. The point is to expose a precise place for a new certificate.

### First falsifiable experiment

Couple exact seed residues to exact rational feasibility intervals, and record
the positions at which a new seed bit is forced to `1`. Search for:

- A well-founded carry/slack ranking under an eventually-zero seed suffix;
- A certificate that each surviving return must eventually force another
  nonzero seed bit;
- An adaptive-depth obstruction to a positive frozen residue.

Use only seed bits for the eventually-zero condition. The evolving orbit's
high bits need not become zero.

**Required baseline:** recover the existing constant-length-3 obstruction
`8^m | (19*a_0+9)` before trying aperiodic paths.

**Success criterion:** certify a nonperiodic family not already excluded by
repetition bounds. Graph pruning alone, residue-density decay, or an unproved
finite-memory assumption does not count.

**Obstacle:** an exact useful state may need unbounded carry information.
Arbitrarily long finite survivors also rule out a seed-independent exit time.

## 3. A concrete nonperiodic generating-function test

**Priority:** bounded experiment with a genuinely closed functional equation.

Let `t_n` be the Thue-Morse sequence and insert two zeros between its digits:

    epsilon_(3n) = t_n,   epsilon_(3n+1) = epsilon_(3n+2) = 0.

The existing encoded-stream construction already gives fractional tails below
`1/2` for such words; see [InfiniteSeries.lean](./InfiniteSeries.lean).

Define

    F(z) = sum_{n>=0} t_n*z^n.

The Thue-Morse recursions give the closed equation

    F(z) = (1-z)*F(z^2) + z/(1-z^2).

The seed identity, if this parity stream comes from an integer orbit, is

    a_0 = -F(8/27)/3                         in Q_2.

### Work sequence

1. Check whether the existing balanced/repetition exclusions already settle this
   coding. If so, choose a different structured class rather than duplicate it.
2. Formalize the nonperiodic coding and the coefficient functional equation.
3. Prove the exact 2-adic evaluation/seed bridge.
4. Verify an applicable p-adic Mahler-value theorem, including specialization
   and singularity hypotheses, before claiming irrationality of `F(8/27)`.

If that value is irrational over `Q`, the coding cannot be the parity stream of
any ordinary integer seed.

**Deliverable:** either an actual exclusion of a specified structured family or
a precise conditional theorem with the missing transcendence input displayed.

**Obstacle:** transcendence of the function alone does not establish
transcendence or irrationality of its value. A theorem not formalized in Lean
must not be hidden behind the phrase "machine-checked exclusion."

## 4. Sparse defects: extend the periodic invariant without assuming periodicity

**Priority:** exploratory route into some unbalanced aperiodic classes.

For an odd block boundary `b`, let `c` be its next block length, `b'` its next
boundary, and `I(b)=19*b+9`. Direct algebra gives the exact signed identity

    2^c * I(b') = 3^c * I(b) + E(c),
    E(c) = 9*2^c - 8*3^(c-1).

For `c >= 1`, examples are

    E(2)=12,   E(3)=0,   E(4)=-72.

Thus departures from the constant-3 path can be tracked rather than discarded.
Iterating gives

    2^T(m) * I(b_m)
      = 3^T(m) * I(b_0)
        + sum_{j<m} 3^(T(m)-T(j+1)) * 2^T(j) * E(c_j).

### First targets

- Formalize this signed defect cocycle.
- Use exact valuations to measure cancellation between defect terms.
- Seek a quantitative exclusion for a precisely stated sparse-defect class,
  including cases with unbounded defect lengths not covered by Path 1.

**Continue if:** a defect-spacing/size hypothesis yields a new finite-seed
height bound or forces new nonzero seed bits.

**Stop or redesign if:** the argument merely rederives the existing repeated
window cutoff, or replaces exact cancellation by unjustified independence.
Sparsity alone is not a claimed exclusion.

## Recommended execution order and completion criteria

1. Complete Path 0 and correct descriptions that exceed theorem statements.
2. Finish Path 1 with standard complexity/balance definitions and named infinite
   aperiodic-class corollaries.
3. Build Path 2's exact encoding and run one bounded certificate experiment.
4. In light of that outcome, pursue Path 3 or Path 4, not both indiscriminately.

For each stage, record the exact proved statement, the hypotheses still assumed,
the smallest Lean checks, and a clear stop condition. Do not use module counts
or bundled synthesis statements as a measure of progress.

The conjecture is solved only after all positive seeds are excluded, with no
unproved complexity, balance, distribution, or realization assumption. None of
the proposed routes currently supplies that final argument.
