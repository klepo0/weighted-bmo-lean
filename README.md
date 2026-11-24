# Maximal inequalities and weighted BMO processes in Lean

This project formalizes Lemma 2.1 of Khoa Lê's
[*Maximal inequalities and weighted BMO processes*](https://arxiv.org/abs/2211.15550v3).

| Paper | Lean declaration |
|---|---|
| Equation (1.1), coefficient `p * c_p` | `WeightedBMO.goodLambdaConstant` |
| Lemma 2.1 | `WeightedBMO.goodLambda_eLpNorm_le` |

The theorem works on finite measure spaces, including probability spaces. It
uses measurable nonnegative real-valued functions and mathlib's extended
`eLpNorm`, so the statement covers all real exponents `p > 0` and needs no
moment finiteness assumption. The proof applies the layer-cake identity to
powers of scaled truncations, absorbs the finite truncated moment, and then
uses monotone convergence.

## Build and check

From this directory, with [Elan](https://github.com/leanprover/elan) installed,
run the following commands. The toolchain and mathlib revision are pinned.

```sh
lake exe cache get Mathlib.MeasureTheory.Integral.Layercake Mathlib.MeasureTheory.Function.LpSeminorm.Defs Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake build
lake env lean Verify.lean
```

The last command checks that the main theorem uses only Lean’s standard
axioms (`propext`, `Classical.choice`, and `Quot.sound`). The next
milestone is the finite-grid weighted John–Nirenberg estimates corresponding
to (1.8) and (1.9).
