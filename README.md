# Maximal inequalities and weighted BMO processes in Lean

This project formalizes estimates from Khoa Lê's
[*Maximal inequalities and weighted BMO processes*](https://arxiv.org/abs/2211.15550v3).

| Paper | Lean declaration |
|---|---|
| Equation (1.1), coefficient `p * c_p` | `WeightedBMO.goodLambdaConstant` |
| Lemma 2.1 | `WeightedBMO.goodLambda_eLpNorm_le` |
| Finite-grid (1.8) and (1.9), unit oscillation bound | `WeightedBMO.grid_johnNirenberg` |

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
lake exe cache get Mathlib.Probability.Process.Stopping Mathlib.MeasureTheory.Integral.Layercake Mathlib.MeasureTheory.Function.LpSeminorm.Defs Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake build
lake env lean Verify.lean
```

The last command checks that both published theorems use only Lean’s standard
axioms (`propext`, `Classical.choice`, and `Quot.sound`).

## Finite-grid estimates

For a centered adapted path and positive adapted weight on times 0 through N,
the two estimates control its maximum and its maximum divided by the running
weight. Both use the exact coefficient from Lemma 2.1 and hold on every event
measurable at the initial time. The hypothesis `UnitGridOscillation` expresses
the unit oscillation bound by integration over events in the stopped σ-algebra.
The continuous-time theorem and the exponential estimate remain open.
