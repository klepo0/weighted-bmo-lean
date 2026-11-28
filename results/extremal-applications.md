# What the extremal results are for

Question: what would be applications of the results on the extremal problem
(§3.2–§3.5, starting at `sec:monotone`: the class `C` of `eqn.class`, the extremal tail
`P*` of `eqn.Pstar`, the sharp exponent of `thm.refined`/`cor.second`, the matching
construction of `prop.lower`).

Everything below was computed or read in this session; nothing here is a
novelty claim.  The one literature check made is recorded at the end and is
not a sweep.

## 1. What is actually available

| object | statement | where |
|---|---|---|
| the class and the extremal tail | `C`, `Z_n = max S_k/(K+J_k)`, `P*(u) = sup_C P(Z_n>u)` | paper, `eqn.class`, `eqn.Pstar` |
| sharp upper exponent | `P <= exp(-u t_H - 1/(t_H-1) + O(1/u))`, `u >= e^20` | paper, `thm.refined` |
| two-sided form | `-log P* = u t_H + 1/(t_H-1) + O(log u)` | paper, `cor.second` |
| matching construction | two-point models reach the same three terms | paper, `prop.lower` |
| finite-level form | `P <= e^{-u x_u} = (1+u x_u)^{-u}`, `e^{x_u} = 1 + u x_u`, **every `u>1`** | paper, `cor.finite` (`eqn.finite`), commit `6dd7898`; was `tail-asymptotics`, `results/t3-finite-bounds.md`, proof `proofs/s3-m6-finite-u-bound.md` |
| sharp prefactor | `P* = (1+o(1))(2 pi u)^{-1/2}(1-1/t_H)^{1/2}e^{-I(u)}`, whole class | `tail-asymptotics`, `results/t1-sharp-prefactor.md`; **not in the paper**, `rmk.prefactor` still calls it open |
| finite-`u` truth | `P*(2) in [0.02407, 0.07805]`, factor 3.24; brackets at `u=5,10` of factor 5–7 | `tail-asymptotics`, `results/t3-finite-bounds.md` |
| continuous time | same exponent for jump-measure costs, `int x nu <= K` | paper, `prop.cont`, `cor.fartail` |
| budget revealed late | normaliser `B_T` dies; bracket on the record scale costs a polynomial factor | paper, `rmk.randomscale` |

The finite-level form is not a new theorem: it is the same infimum the proof of
`thm.refined` evaluates, before the expansion `r = t_H + 1/(u(1-1/t_H)) + O(u^{-2})`
is applied.  The `u >= e^20` of `thm.refined` is there for the `O(1/u)`, not for
the inequality.  Substituting `x_u = r* - 1/u`, `r*` the root `>1` of
`r - log(u r) = 1/u`, turns one into the other.

## 2. The applied number in the paper was obsolete (fixed in `6dd7898`)

`ex.pareto` then ended: "Taking `u = 4.317` in `eqn.obja` gives the simultaneous envelope
`S_k <= 4.317 (K+J_k)`, `k<=n`, with probability at least 0.95."  It now reads: "Taking
`u = 2.163` in `cor.finite` gives the simultaneous envelope `S_k <= 2.163 (K+J_k)`, `k<=n`,
with probability at least 0.95; the estimate `eqn.obja` needs `u = 4.317` for the same
level."  The 4.317 is `e^{u-1}u^{-u} = 0.05`;
the 2.163 is `e^{-u x_u} = 0.05`.  Both are proved, both are uniform over `n` and
over the whole class, and the second is the better of the two by a factor 2.

Levels for the three bounds (smallest `u` with bound `<= target`):

| target | `e^{-u x_u}` (finite form) | `e^{u-1}u^{-u}` | `e/(1+u)` |
|---|---|---|---|
| 0.05 | 2.163 | 4.316 | 53.4 |
| 0.01 | 2.672 | 5.340 | 271 |
| 1e-3 | 3.341 | 6.628 | 2717 |
| 1e-6 | 5.125 | 9.909 | 2.7e6 |

And the finite form is not merely an upper bound far from the truth: at `u=2`
the certified bracket is `[0.0241, 0.0780]`, i.e. the frontier is pinned within
a factor 3.2 at a level anyone would use.  The asymptotic `thm.refined` is
different in kind: at its own threshold `u = e^20` it reads
`-log P* = 1.12e10`, that is `eps = e^{-1.1e10}`.

## 3. Three shapes of application

**(A) Model-free envelopes at levels people use.** The envelope is a statement
about the ratio, uniform in the horizon, in the number of costs, in dependence,
in the cost law, and with no moment beyond the budget.  It costs nothing to
state and it is the only part of §3.2–§3.5 that a reader outside probability can
consume.

**(B) The extremal model as a stress scenario and a sharpness witness.** The
saddle pins the worst case: budget exhausted, one cost size `K(t_H-1) =
K log(u log u) + O(K)`, `u t_H/(t_H-1)` costs, mass banded at the record.  Two
uses follow and neither needs a new hypothesis: it is a concrete model to run a
procedure against, and it is a lower-bound machine for anything of the form
`P(max S >= f(B_n, J_n)) <= g(u)` — no such bound can be smaller than
`exp(-u t_H - 1/(t_H-1))` up to sublinear factors.

**(C) Inside the theory.** `cor.fartail`/`rmk.fartailjn` is the one application
already written: a pathwise compensator bound gives all exponential moments and
`||sup X||_p = O(pK/log p)`, where John–Nirenberg gives only `lambda < ||V||^{-1}`.
Note the two-sidedness matters here too: `prop.lower` is what forbids reading
the `log log` term as a defect of the proof.

## 4. Fields, with the gate each has to pass

* **Contractual mean budget, monitored sequentially** (protocol-specified event
  budgets, treaty or limit-bounded loss aggregates, design-spec damage
  accumulation).  Strongest fit: `K` is fixed at time 0 by construction, which
  is exactly the `F_0`-measurability `rmk.randomphi` needs, and "anytime"
  costs nothing because the bound is uniform in `n`.
* **Heavy-tailed claim aggregates.** `ex.pareto` is the template: tail index
  `alpha in (1,2)` has no mgf, so no Chernoff bound and no variance-based
  maximal inequality applies, and the `J` in the denominator is the credit for
  the largest claim.  The quantity bounded is a loss ratio net of the largest
  claim, not an absolute reserve.
* **Suprema of counting-process integrals with an unknown but bounded
  mean intensity.** Nearest neighbours in the literature: `Zbl 1101.60033`
  (Reynaud-Bouret 2006) computes compensators and applies van de Geer's
  martingale inequality (`Zbl 0852.60019`) to get exponential inequalities for
  such suprema; that tradition normalises predictably.  The differentiator here
  is the optional normaliser and the sharpness, not the field.
* **Queues / Lindley workload.** Weak.  The reduction to `sup|Z_u|` plus the
  one-sided estimate is bounded by 2210.15736's John–Nirenberg in the regime
  that matters.
* **Bandits / stochastic approximation with heavy tails.** Weak.  Wherever a
  variance proxy is available, Bernstein/Freedman is `u log(1+u)` in the same
  normalisation and wins; the budget-only hypothesis buys heavy tails and
  nothing else.

## 5. The gates, stated plainly

1. **`K` must be known before the process starts.**  `rmk.randomscale` gives a
   model with `B_T <= 1`, `E X_T <= 1` and `P(sup X_t/(B_T+J_t)>u) -> 1` for a
   path-revealed compensator, so Hawkes and Cox intensities are outside, and so
   is anything where the budget is estimated from the data.  The bracket repair
   `eqn.bracket`/`eqn.bracketrange` keeps the constants but costs a polynomial
   factor and needs the record scale bracketed in advance.
2. **`Z` is a ratio, not a total.**  A single cost `a` gives `a/(K+a) < 1`, so
   nothing in `u>1` is a one-jump event; to bound an absolute total one needs
   `J_T <= cK` and pays for it (`cor.fartail`).  Any application must be happy
   to normalise by the observed largest cost.
3. **It is a worst case over the whole class.**  The class contains every
   adapted dependence and every cost law, so for a parametric model the bound is
   very conservative, and the honest reading is the price of model uncertainty,
   not a competitor to model-specific bounds.
4. **Asymptotics vs levels.**  `thm.refined`/`cor.second`/the prefactor speak at
   `u >= e^20`; only the finite form speaks at `u ~ 2`.  Any "capital is
   `K log(1/eps)`" reading is an asymptotic at `eps = e^{-1.1e10}` and must not
   be quoted at 5%.
5. **Nothing here is machine-checked, and the prefactor is not in the paper.**

## 6. What I would write, in order

1. ~~Add the finite-level form to §4.2 as the usable member ... and change
   `4.317` to `2.163` in `ex.pareto`.~~ **Done, commit `6dd7898`**: `cor.finite`
   (`eqn.finite`) follows the proof of `thm.refined`, the proof evaluates the
   infimum exactly, it is noted there that `(eqn.finite)` contains `(eqn.obja)`
   via `x_u >= log u - 1 + 1/u`, `ex.pareto` quotes `2.163`, and
   `rmk.verification` lists the new corollary.  Sanitised build clean
   (0 errors, 0 overfull, 36 pages).
2. One paragraph naming the extremal model as the stress scenario, with the
   three pinned quantities, and saying explicitly that `prop.lower` is what
   makes the rate a benchmark rather than an estimate.
3. Leave a field-level application out until a model is found where the mean
   budget is contractual and the ratio is the field's own object; on the
   evidence above, naming a field first and checking the gate afterwards has
   failed in this project before.

## 7. What was checked, and how

* Numerics: `u x_u` vs `e^{u-1}u^{-u}` vs `e/(1+u)` quantiles, and `e^{-u x_u}`
  at `u=2,3,4,5,10`, recomputed in this session with `scipy.optimize`; the
  `u=2` value `0.0810` agrees with `s3-m6`'s `e^{-2x_2}` to the digits shown,
  and sits above the certified lower bound `0.0241` as it must.
* One zbMATH query, 2026-11-27: `ab:compensator ab:"exponential inequalities"`
  returned 2 records, of which `Zbl 1101.60033` is the relevant one;
  `ab:"maximal jump" ab:inequalit*` and `ab:"self-normalized" ab:"maximal
  inequalities"` returned nothing usable.  The `ab:` field reaches reviews and
  summaries, many of which are withheld, so these empty answers are not
  evidence of absence and no novelty claim is made on them.
* `x_u >= log u - 1 + 1/u`, used in `cor.finite` to deduce `e^{u-1}u^{-u}`,
  checked on a grid of `u` in `(1,101]` (minimum of the difference `~1e-15`,
  i.e. the inequality is tight only at `u=1`), and `e^{-u x_u}` against
  `s3-m6`'s `e^{-2x_2}` at `u=2` to 17 digits.
* Sanitised `pdflatex` build after the edit: 0 errors, 0 overfull, 0 undefined
  references or citations, 2 underfull `\vbox` at page breaks (the last page
  carries only the author's address), 37 pages.
* Literature check for the §3.2–§3.5 positioning, 27 Nov 2026: `ti:"self-normalized"
  cc:60F10` 61 records, `ab:"one big jump"` 13, `ab:saddlepoint cc:60F10` 22,
  `ab:"worst case" ab:"large deviations"` 17, `ab:"best possible" ab:"tail
  probabilities"` 6.  Four references were verified individually with
  `zbmath.py show` before being added to §3.5 and to the `.bbl`: Bahadur–Ranga
  Rao Zbl 0101.12603, Jensen Zbl 1274.62008, Asmussen–Klüppelberg Zbl
  0879.60020, de la Peña–Klass–Lai Zbl 1189.60057 (Freedman re-checked as Zbl
  0313.60037 against the existing `Fre75` entry).  No sweep of the
  Lenglart/Pratelli, Garsia–Neveu or Bass strands was completed, so the
  positioning is hedged in a footnote rather than claimed as a novelty audit.
