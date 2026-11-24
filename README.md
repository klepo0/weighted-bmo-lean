# Maximal inequalities and weighted BMO processes in Lean

This project formalizes estimates from Khoa Lê's
[*Maximal inequalities and weighted BMO processes*](https://arxiv.org/abs/2211.15550v3).

| Paper | Lean declaration |
|---|---|
| Equation (1.1), coefficient `p * c_p` | `WeightedBMO.goodLambdaConstant` |
| Lemma 2.1 | `WeightedBMO.goodLambda_eLpNorm_le` |
| Finite-grid (1.8) and (1.9), unit oscillation bound | `WeightedBMO.grid_johnNirenberg` |
| Partitioned exponential bound on a finite grid | `WeightedBMO.grid_partition_exponential` |
| Real-time (1.9) ⇒ conditional (1.10) | `WeightedBMO.conditional_exponential_of_interval_moments` |
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
positive local bound.

## Real-time exponential estimate

For a fixed interval [a,T], `conditional_exponential_of_interval_moments`
proves that the supremum over all starting times r of the conditional
essential supremum of exp(λ Z(r,T)) is finite. Its hypotheses specify a
measurable nonnegative interval maximum Z with the splitting inequality,
the event-tested integer moments of (1.9), and a locally bounded modulus ρ.
The small-scale modulus is the infimum of uniform upper bounds valid at
some positive mesh size. The rate condition includes λκ = exp(−3).
The proof uses convergence at exp(−5/2) to select a single mesh for every r.

The declaration `path_exponential_of_interval_moments` specializes this bound
to the actual normalized path maximum. For bounded right-continuous adapted
paths and positive weights, Lean proves the splitting law and measurability.
The measurability proof detects strict crossings at rational times or at the
right endpoint, so it also covers a jump at that endpoint.

To recover the full theorem from weighted BMO, the remaining stochastic
estimate is the continuous-time (1.9) from the stopped oscillation bound.
The finite-grid theorem proves this estimate on a finite index set.
