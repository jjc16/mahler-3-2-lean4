# Irrationality Probes (`e-plus-pi-no-go` Branch)

Standalone Lean 4.19.0 + Python formalization of split-approximation and recurrence obstructions for $e + \pi \notin \mathbb{Q}$:

- [`EPlusPiSplitNoGo.lean`](./EPlusPiSplitNoGo.lean): `sorry`-free, warning-free verification of `EP.1–EP.4`:
  1. **`EP.1` (`quadratic_sum_prod_irrational_disjunction`)**: Any $\alpha \in \mathbb{R}$ satisfying no nontrivial integer quadratic equation forces $\operatorname{Irrational}(\alpha + \beta) \lor \operatorname{Irrational}(\alpha \cdot \beta)$ for all $\beta \in \mathbb{R}$.
  2. **`EP.2` (`split_integer_offset_nearest_int_floor_no_go`)**: Any additive split $L = (C\alpha + B_1) + (C\beta + B_2)$ with separate integer offsets $B_1, B_2 \in \mathbb{Z}$ and $|C\beta + B_2| \le \varepsilon$ is bounded below by $\operatorname{distToInt}(C\alpha) - \varepsilon$ across all $B_1 \in \mathbb{Z}$, blocking decoupled Hermite + Beukers combinations.
  3. **`EP.3` (`second_order_recurrence_two_generator_span_collapse`)**: Any second-order integer recurrence $A_{n+2} = c_n A_{n+1} + d_n A_n$ (including Hermite's $A_{s+2} = -(4s+6)A_{s+1} + A_s$) collapses arbitrary $L$-term combinations $\sum_{j<L} u_j A_{s+j}$ into $\mathbb{Z} A_s + \mathbb{Z} A_{s+1}$.
  4. **`EP.4` (`denominator_divisible_multiplier_forces_exact_vanishing`)**: Under $\xi = p/q$, if $q \mid C$ and $|C\xi + M| < 1$, then $C\xi + M = 0$ identically.
- [`e_plus_pi_split_no_go_probe.py`](./e_plus_pi_split_no_go_probe.py): 140-digit numerical verification of `EP.2–EP.3`.

## Verification

```powershell
lake build
lake env lean -DwarningAsError=true irrationality_probes\EPlusPiSplitNoGo.lean
python irrationality_probes\e_plus_pi_split_no_go_probe.py
```
