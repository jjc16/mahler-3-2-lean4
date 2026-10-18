# Mahler $3/2$ Problem — 114-Module Lean 4 Formalization (`mahler_demand_a`)

This repository contains a **114-module, `sorry`-free Lean 4.19.0 + Mathlib v4.19.0 formalization** of the reduced Mahler $3/2$ dynamical system ($Z$-numbers), including:

- **Exact 1D Dynamical Reduction:** Equivalence between the existence of a real Mahler companion $\xi \in \mathbb{R}$ and the 1D `minSlack` recurrence (`ConverseCompanionReconstruction.lean`), the shift-free unshifted ceiling comparison (`MultiOriginSubspaceSyzygy.lean`), the carryless Base-3 frozen-prefix condition (`SimultaneousBaseDigitRigidity.lean`), and the autonomous 1D piecewise-expanding map $\mu_2(s, m+1) = \min\big(1,\, (3/2)^{s(m)} \mu_2(s, m) - 2\big)$ on $(0, 1]$ (`CoupledFractionalPartDynamics.lean`).
- **Constructive Survivors & 113-Step Record-Holder:** Closed-form arbitrary-length pre-exit survivors (`ExplicitHorizonCutoffs.lean`) and machine-checked **113-step survival / 114-step death** of the 55-bit integer `recordHolderA0 = 29871555608238677 < 2^55` (`MahlerGrandSynthesis.lean`).
- **Unconditional Finiteness in Restricted Regimes:** Time-independent bounded-block escape ceilings (`TimeIndependentDeficiencySqueeze.lean`), linear subword-complexity cutoffs on repeated subwords (`RepeatedSubwordComplexity.lean`), Two-Sided Chinese Remainder Sieves (`Mod256CompleteSieve.lean`, `Mod2304CombinedSieve.lean`, `Mod216TwoSidedQuotientFloor.lean`), and 3-adic valuation conservation (`ThreeAdicValuationConservation.lean`).
- **Certified Transcendence & Diophantine Barriers (Dead Ends 1–18):** Machine-checked proofs of the exact algebraic conservation laws explaining why determinant interpolation (`DeterminantFactorization.lean`), Baker–Matveev linear forms in logarithms (`BakerMatveevFramework.lean`, `MultiStepQuotientGCD.lean`), Ridout's theorem (`RidoutSubspaceFramework.lean`), Schlickewei's $p$-adic Subspace Theorem (`MultiOriginSubspaceSyzygy.lean`), and Padé–Hankel approximants (`MahlerSeriesHankelFramework.lean`) stall on the general aperiodic case.

For a complete, human-readable mathematical exposition of our results and barrier analyses, see **[MAHLER_FORMALIZATION_PAPER.pdf](./MAHLER_FORMALIZATION_PAPER.pdf)** (and the Markdown/LaTeX sources **[MAHLER_FORMALIZATION_PAPER.md](./MAHLER_FORMALIZATION_PAPER.md)** / **[MAHLER_FORMALIZATION_PAPER.tex](./MAHLER_FORMALIZATION_PAPER.tex)**).

## Acknowledgments

Developed by Joshua Coon with the assistance of the **Astra** and **Argon** AI models in GitHub Copilot.

## Building & Verifying

Requires **Lean 4.19.0** (`leanprover/lean4:v4.19.0`):

```bash
lake build
```
