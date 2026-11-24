# Maximal inequalities and weighted BMO processes in Lean

This project formalizes estimates from Khoa Lê's
[*Maximal inequalities and weighted BMO processes*](https://arxiv.org/abs/2211.15550v3).

| Paper | Lean declaration |
|---|---|
| Equation (1.1), coefficient `p * c_p` | `WeightedBMO.goodLambdaConstant` |
| Lemma 2.1 | `WeightedBMO.goodLambda_eLpNorm_le` |
| Finite-grid (1.8) and (1.9), unit oscillation bound | `WeightedBMO.grid_johnNirenberg` |
| Partitioned exponential bound on a finite grid | `WeightedBMO.grid_partition_exponential` |
| Single-interval exponential bound on a finite grid | `WeightedBMO.grid_exponential` |

Lemma 2.1 works on finite measure spaces, including probability spaces. It
uses measurable nonnegative real-valued functions and mathlib's extended
`eLpNorm`, so the statement covers all real exponents `p > 0` and needs no
moment finiteness assumption. The proof applies the layer-cake identity to
powers of scaled truncations, absorbs the finite truncated moment, and then
uses monotone convergence.

## Build and check

From this directory, with [Elan](https://github.com/leanprover/elan) installed,
run the following commands. The toolchain and mathlib revision are pinned.

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Exponential Mathlib.Probability.Process.Stopping Mathlib.MeasureTheory.Integral.Layercake Mathlib.MeasureTheory.Function.LpSeminorm.Defs Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake build
lake env lean Verify.lean
```

The last command checks that the published estimates use only Lean’s standard
axioms (`propext`, `Classical.choice`, and `Quot.sound`).

## Finite-grid estimates

For a centered adapted path and positive adapted weight on times 0 through N,
the two estimates control its maximum and its maximum divided by the running
weight. Both use the exact coefficient from Lemma 2.1 and hold on every event
measurable at the initial time. The hypothesis `UnitGridOscillation` expresses
the unit oscillation bound by integration over events in the stopped σ-algebra.
The single-interval exponential estimate holds on every initial event E for
rates up to and including exp(−3). Its bound is M times the mass of E, with
convergence of the series (1.1) proved in `hasSum_exponentialBound`. For a deterministic partition with K blocks, the bound is M^K times the
mass of E when the rate times each block’s oscillation bound is at most
exp(−3). The block hypothesis uses the centered process divided by its
positive local bound. The continuous-time version of (1.10), including
partition selection from the small-scale modulus, remains open.
