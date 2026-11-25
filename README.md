# Maximal inequalities and weighted BMO processes in Lean

This project formalizes estimates from Khoa Lê's
[*Maximal inequalities and weighted BMO processes*](https://arxiv.org/abs/2211.15550v3).

| Paper | Lean declaration |
|---|---|
| Equation (1.1), coefficient `p * c_p` | `WeightedBMO.goodLambdaConstant` |
| Lemma 2.1 | `WeightedBMO.goodLambda_eLpNorm_le` |
| Finite-grid (1.8) and (1.9), unit oscillation bound | `WeightedBMO.grid_johnNirenberg` |
| Partitioned exponential bound on a finite grid | `WeightedBMO.grid_partition_exponential` |
| Definition 1.2, equivalence with conditional expectations | `WeightedBMO.weightedBMOOn_iff_condExp` |
| Continuous-time (1.8) on every initial event | `WeightedBMO.weightedBMO_maximal_moments` |
| Continuous-time (1.8) in conditional expectation form | `WeightedBMO.weightedBMO_conditional_maximal_moments` |
| Continuous-time (1.10) from weighted BMO | `WeightedBMO.weightedBMO_exponential` |
| Continuous-time (1.9) from the stopped oscillation modulus | `WeightedBMO.real_interval_moments` |
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
lake exe cache get
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

## Continuous-time weighted BMO theorem

`WeightedBMO.weightedBMO_exponential` proves (1.10) from the weighted BMO
stopping-time inequality. It fixes an interval [a,T] and takes the supremum
over r in that interval. The filtration is right-continuous and the paths of
the process and its positive weight are càdlàg. The conclusion holds for
λκ ≤ exp(−3), including equality.

`WeightedBMOOn` uses an event-integral formulation of Definition 1.2:
for every pair of bounded stopping times S ≤ U and every event G known at S,
the integral of |V(U) − V(S−)| / φ(S) over G is at most B times its mass.
`oscillationModulus` uses the least such bound with the running weight on
[S,U] in the denominator. `tendsto_meshOscillation` identifies the
small-scale infimum with the paper's right-hand limit.

`real_interval_moments` proves (1.9) using first strict crossings in real
time, including terminal jumps. Their stopped increment controls the tail
by Lemma 2.1. The exponential estimate then follows by the partition and
conditional expectation arguments above.

For (1.8), the first crossings are of the unnormalized increment
|V(u) − V(r)|. The good-λ inequality uses the running weight over [r,T]
and the exact oscillation modulus, including the case where it is zero.
The event formulation allows infinite moments. The conditional
expectation formulation uses mathlib's real-valued conditional
expectation and assumes that the weight has a finite p-th moment.

`weightedBMOOn_iff_condExp` allows the conditional-expectation
hypothesis in Definition 1.2 to be used with these theorems. It states
explicitly that the stopped weight is measurable at the first stopping
time and that the absolute stopped increment is measurable and integrable.
