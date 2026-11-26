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
| Doob's weak-type (1,1) maximal inequality | `WeightedBMO.submartingale_weak_type` |
| Doob's `L^p` maximal inequality, sharp constant `p/(p-1)` | `WeightedBMO.submartingale_eLpNorm_maximal_le` |
| Theorem 1.1 (b), path of increments in weighted BMO | `WeightedBMO.weightedBMOOfSharpMaximal` |
| Theorem 1.1, `est.upperbound` with the sharp maximal function as a hypothesis | `WeightedBMO.sharpMaximal_eLpNorm_le` |
| Theorem 1.1 (c), Doob's step for a martingale with terminal value `Ψ` | `WeightedBMO.martingale_eLpNorm_maximal_le_of_terminal` |
| Continuous-time Doob step over `[0,T]`, sharp constant `p/(p-1)` | `WeightedBMO.eLpNorm_supOn_le` |
| `est.Smaximal`, right-hand side, end to end | `WeightedBMO.estSmaximal_upper` |

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

If `elan` is not installed, Lake falls back to the `lean` on `PATH`. Extracting
the pinned `lean-4.19.0-linux.tar.zst` release and putting its `bin` directory
first on `PATH` reproduces the build without `elan`.

## Doob's `L^p` maximal inequality

The paper deduces Theorem 1.1 from the John--Nirenberg inequality (1.8) and
Doob's `L^p` maximal inequality with constant `m/(m-1)`. Mathlib has the
weak-type `(1,1)` inequality `MeasureTheory.maximal_ineq` but not its `L^p`
consequence, so `WeightedBMO/DoobMaximal.lean` supplies it for discrete-time
nonnegative submartingales on a finite measure space: for `p > 1`,

```
‖max_{k ≤ n} f k‖_p ≤ p/(p-1) ‖f n‖_p
```

(`submartingale_eLpNorm_maximal_le`, with the moment form
`submartingale_moment_maximal_le` that states
`∫ (max_{k ≤ n} f k)^p ≤ (p/(p-1))^p ∫ (f n)^p`) and the martingale
specialization `martingale_eLpNorm_maximal_le`. The proof computes the moment
by layer cake, integrates the weak-type bound over the level parameter
(Tonelli), evaluates the resulting one-dimensional power integral, and
concludes with Hölder's inequality. The weak-type inequality is restated as
`submartingale_weak_type` in the normalization used by the rest of the
argument.

## Theorem 1.1 with the sharp maximal function as a hypothesis

Theorem 1.1 of the paper bounds the maximal function of `t ↦ d(X_0, X_t)` by
the sharp maximal function `X^♯`. Its proof has two steps beyond (1.8).

First, the path `V_t = d(X_a, X_t)` lies in weighted BMO with weight `2X^♯`.
The paper obtains this from the two estimates
`E_S d(X_U, X_T) ≤ E_S X^♯_{S,T}` and `E_S d(X_{S-}, X_T) ≤ E_S X^♯_{S,T}`
for stopping times `S ≤ U ≤ T`, the reverse triangle inequality, and the
monotonicity of the conditional mean. Instead of proving measurability of the
supremum over times (which needs an RCLL version of `t ↦ E_t X^♯_{t,T}`,
Dellacherie--Meyer II (2.9), not available in this environment),
`weightedBMOOfSharpMaximal` takes such a process `ψ` with those two domination
properties as a hypothesis and concludes `WeightedBMOOn … (2ψ) a T 1`.

Second, (1.8) applied to this weighted BMO process gives the maximal estimate
with the paper's constant. `sharpMaximal_eLpNorm_le` states it on every
initial event: the maximal function of `t ↦ d(X_a, X_t)` is bounded by
`goodLambdaConstant p = p c_p` times the `Lᵖ` seminorm of the supremum of the
weight `2ψ`.

Third, Doob's `L^p` maximal inequality (`WeightedBMO/DoobMaximal.lean`)
converts `‖sup_t E_t X^♯_{t,T}‖_p` into `p/(p-1) ‖X^♯_T‖_p`.
`martingale_eLpNorm_maximal_le_of_terminal` records that step for a
nonnegative martingale whose terminal value is a given `Ψ`; in the paper
`M_t = E_t X^♯_τ` and `Ψ = X^♯_τ`, which is `ℱ_τ`-measurable.
The continuous-time form of this step is `eLpNorm_supOn_le` in
`WeightedBMO/ContinuousDoob.lean`: for a nonnegative martingale `M` indexed by
`ℝ` and `p > 1`,

```
‖sup_{t∈[0,T]} M_t‖_p ≤ p/(p-1) ‖M_T‖_p
```

(`supOn` is the supremum over the dyadic grids of `[0,T]`; for right-continuous
paths `ofReal_le_supOn` shows it dominates every value on `[0,T]`).
Mathlib has optional sampling only in discrete time, so the argument runs the
first-passage inequality on each dyadic grid — where the sampled process is a
finite-time nonnegative martingale — and passes to the limit by monotone
convergence, which reproduces the continuous-time statement with the same
constant. The terminal-value form is `eLpNorm_supOn_le_of_terminal`.

The bridge between the two formulations is `ofReal_intervalSup_le_supOn`: the
interval supremum used by (1.8) is at most the dyadic supremum `supOn` used by
the Doob step, provided the dominating process is right-continuous.

Putting the three pieces together, `estSmaximal_upper` states the second
inequality of `est.Smaximal` end to end. The sharp maximal function `ψ` stays a
hypothesis, and the paper's weight `2ψ` must be dominated by a nonnegative
right-continuous martingale `M`:

```
‖sup_{t∈[0,T]} d(X_0, X_t)‖_p ≤ c_p p · p/(p-1) · ‖M_T‖_p ,  p > 1,
```

proved from the weighted BMO bound, (1.8) with the weight `2ψ`, and Doob's
step. In the paper `ψ = X^♯_{·,T}` and `M = 2 E_· X^♯_T`, so `M_T = 2 X^♯_T`
and the constant is `2 c_p p²/(p-1)`, as printed in `est.Smaximal`.

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
