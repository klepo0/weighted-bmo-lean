# Can the new §4 results be applied to §3?

Short answer: yes in two places, no in two others. Both transfers run through the
*increasing* processes that §3 already contains --- the quadratic variation `[f]` and the
dual-Doob sum `V_k = sum_{i<=k} E_i z_i` --- because those, and not the martingales
themselves, satisfy §4's monotonicity requirement. Both come with a sharpness statement,
because the extremal models of §4.2 are realisable inside §3's classes.

Notation as in §3: `f` a square-integrable discrete martingale, `f_{-1}=0`,
`df_k = f_k - f_{k-1}`, `[f]_k = sum_{j<=k} |df_j|^2`, `<f>_k = sum_{j<=k} E_{j-1}|df_j|^2`,
`f^*_{k,n} = sup_{k<=j<=n} |f_j - f_k|`.

---

## What §4.2 proves (the tool being transferred)

`prop.obja`: nonnegative adapted `xi_k`, `b_k = E_{k-1} xi_k`, `S_k = sum_{j<=k} xi_j`,
`J_k = max_{j<=k} xi_j`, and the *pathwise* budget `B_n = sum_{k<=n} b_k <= K`. Then for
`Z_n = max_{k<=n} S_k/(K+J_k)`

    P(Z_n > u) <= exp(e^lambda - 1 - lambda u),   hence  <= e^{u-1} u^{-u}  (u > 1),

with `E Z_n^m <= e^{e^lambda-1} Gamma(m+1)/lambda^m` and `E e^{q Z_n} <= 1 + q/(lambda-q) e^{e^lambda-1}`
for `q < lambda`. `thm.refined`: for `u >= e^{20}`, `P(Z_n > u) <= exp(-u log u - u log log u + 11u)`.
`prop.lower`: over that class the rate cannot be improved, and `sup E exp(lambda Z_n^alpha) = +inf`
for every `alpha > 1`.

The proof uses exactly three properties: additivity `S_k = sum_{j<=k} xi_j`; the identity
`b_k = E_{k-1} xi_k`; and the increment bound `(R_k - R_{k-1})_+ <= min{1, xi_k/(K+J_{k-1})}`
with `R_k = S_k/(K+J_k)`. None of the three is special to costs.

---

## Transfer 1: the quadratic variation (a one-big-jump theorem for `[f]`)

**Proposition.** Let `K` be `F_0`-measurable, `0 < K < inf`, and assume `<f>_n <= K` a.s.
Put `J_n = max_{j<=n} |df_j|^2`. Then the conclusions of `prop.obja`, `thm.refined` and
`cor.second` hold verbatim with `S_k = [f]_k`, `J = J_n`:

    P([f]_n > u (K + J_n)) <= exp(e^lambda - 1 - lambda u),
    P([f]_n > u (K + J_n)) <= exp(-u log u - u log log u + 11u)   (u >= e^{20}),

and `Z = max_{k<=n} [f]_k/(K+J_k)` has all moments and all exponential moments.

*Proof.* Apply `prop.obja`/`thm.refined` to `xi_k := |df_k|^2`. Adaptivity and
nonnegativity are clear. `S_k = [f]_k` is additivity of `[f]`. And
`b_k = E_{k-1}|df_k|^2 = <f>_k - <f>_{k-1}`, so `B_n = <f>_n <= K`. Finally
`K + J_{k-1}` is `F_{k-1}`-measurable because `K` is `F_0`-measurable, which is the only
place the measurability of the budget is used (it makes the bound hold conditionally on
`F_0`, hence a.s.). `[f]` is finite because `f` is square integrable. QED

What this adds to §3, stated precisely. §3 has two statements about `[f]`:
`(bdg.fbk0)`, the `L^m` bound

    |[f]_n|_m <= 2 c_m m | sup_{k<=n} E_k |f^*_{k,n}|^2 |_m ,

and, in the final display of `thm.dismart`, the pair `([f]_k, sup_{i<=k} E_i |f^*_{i,n}|^2)`
with `sup_eps E exp(lambda sup_k [f]_k/(eps + sup_i E_i|f^*_{i,n}|^2)) <= M`. So a ratio
form is *not* absent from §3. What the transfer changes is the normaliser and the exponent:

  - the normaliser `K + J_n` is observed --- an `F_0`-measurable budget plus the realised
    largest squared increment --- whereas `sup_i E_i |f^*_{i,n}|^2` is a conditional mean of
    the future size of the path;
  - the exponent is unrestricted (`lambda > 0`, `M` absent) instead of `(est.jnexpwei)`'s
    restriction and constant;
  - the tail rate is the sharp `u log u + u log log u + O(u)`, not merely exponential;
  - no bounded-jump hypothesis is needed, where Freedman/Bass-type bounds for `[f] - <f>`
    require one.

The transfer is neither implied by nor implies `(bdg.fbk0)`: different normalisers, and the
transfer needs `<f>_n <= K`. What is genuinely new relative to §3 is the pair (unrestricted
exponent, sharp rate) *together with* the no-go below, which says neither can be pushed
further in the class.

**Sharpness, inside the class of square functions.** The extremal models of `prop.lower`
*are* square functions of genuine martingales: let `df_k = +-a^{1/2}` with probability
`p/2` each and `0` with probability `1-p`, signs i.i.d. and symmetric. Then `f` is a
martingale, `|df_k|^2` takes the values `a` and `0` with probabilities `p` and `1-p`, and
`<f>_n = n p a = K` exactly. So the class of Transfer 1 contains the class of `prop.lower`,
and therefore

  (i) the rate `u log u + u log log u + O(u)` cannot be improved for `[f]`/(budget + largest squared increment);
  (ii) `sup E exp(lambda Z^alpha) = +inf` for every `alpha > 1`, the supremum over discrete
       martingales with conditionally bounded quadratic variation.

So §3 gains a sharp rate and a no-go in the same statement. Note (ii) is confined to this
class: with a bounded-jump hypothesis `|df_k| <= j` a martingale is sub-Gaussian and no
such obstruction exists. This is the same caveat as `rmk.constant`.

## Transfer 2: the dual of Doob's inequality

In §3 the dual Doob estimate is `(doob0)` for positive `z_i`:

    | sum_{i<=n} E_i z_i |_m <= 2 c_m m | sup_{k<=n} E_k sum_{i=k}^n z_i |_m .

Its left-hand side is `V_n` with `V_k = sum_{i<=k} E_i z_i`, which is nondecreasing because
`E_k z_k >= 0`. Conversely, for *any* nonnegative adapted nondecreasing `xi`, taking
`z_k = xi_k` gives `E_k z_k = xi_k`, hence `V_k = S_k`. So the models of `prop.obja` sit
inside the class `(doob0)` controls, and `prop.obja`, `thm.refined`, `prop.lower` apply to
`V` as soon as `sum_k E_{k-1} z_k <= K` pathwise:

    P( sup_{k<=n} V_k/(K + max_{j<=k} E_j z_j) > u ) <= e^{u-1} u^{-u},  etc.,

with the same sharpness and the same no-go. To be fair about what is already available: the
proof of §3's proposition identifies `V` as BMO with weight `phi_k = E_k sum_{i=k}^n z_i`,
so `(est.jnweight2)` and `(est.jnexpwei)` already give a ratio statement for `V` with
normaliser `sup{phi}` and the exponent restriction. The gain here is again the normaliser
(an `F_0`-measurable budget `K` plus the realised `max_j E_j z_j` instead of a conditional
mean of the future costs) together with the unrestricted exponent, the sharp rate, and the
no-go. The cost is once more the pathwise budget; `(doob0)` remains the general statement
and is not implied.

---

## What does not transfer, and why

1. **`thm.contmart` (currently stated without proof).** §4.3 is about increasing processes
   with a compensator. For a continuous martingale the relevant increasing process `<X>` is
   continuous, so `J_t = sup_{s<=t} Delta<X>_s = 0` and the normaliser `K + J_t` collapses to
   the budget: this is the degenerate case §4.3 itself flags (`rmk.contlimits` (ii) for
   infinite activity, and the subsection's literature paragraph for bounded jumps, "nothing
   beyond that body of results is obtained"). The missing proof is a continuous-time
   John--Nirenberg step, which is §2/§3 machinery. §4.3 is the wrong tool, and nothing in §4
   shortens that gap.

2. **The martingale suprema themselves.** §4.2's supermartingale needs the numerator
   nondecreasing with `(R_k - R_{k-1})_+ <= xi_k/(K + J_{k-1})`. `|f_k|` is not monotone and
   its positive increments are not bounded by the running maximum of anything, so the
   exponential integrability in `thm.dismart` (constant `M`, exponent restricted by
   `(est.jnexpwei)`) cannot be upgraded to the §4.3 form --- every `lambda > 0`, no `M` ---
   by these means. That upgrade is available only through monotone auxiliaries, i.e.
   through Transfers 1 and 2.

3. **`cor.mono` has a weaker hypothesis and a weaker conclusion.** It needs only
   `E_t(X_T - X_t) <= K`, and so applies to `[f]` whenever `E_k([f]_n - [f]_k) <= K` for all
   `k` (a terminal-scale condition on `<f>`), giving the ratio bound with the degraded
   exponent `lambda <= (2e^3)^{-1}` and the constant `2 c_m m`. Under the stronger pathwise
   budget `prop.obja` dominates it, as `rmk.budget` records. Worth at most a remark.

4. **§4.1 (stable Volterra) has nothing to say to §3**: no martingale in §3 is a
   Riemann--Liouville functional of stable noise.

---

## Net effect on §3

Two new propositions (square function; dual Doob), each replacing §3's conditional-mean
normaliser by an observed budget-plus-largest-jump one, at an unrestricted exponent and the
sharp rate, with a matching no-go; and two clarifications (why §4.3 does not prove
`thm.contmart`, why the `thm.dismart` constants stay). No hypothesis of an existing §3 result
is weakened, and no existing §3 statement is dominated. The honest description of the value
is: §4.2 gives a normaliser for the two §3 inequalities that is observable and
jump-based rather than a conditional mean of the future path, in the subclass where the
budget is pathwise and conditionally deterministic, and `prop.lower` says that form is as
sharp as it can be there.

If this is to enter the paper, the cheapest coherent shape is one corollary after §4.2
stating Transfer 1, plus a paragraph in §3 pointing at it from `thm.dismart`; Transfer 2 is
a remark at most, since it duplicates the shape of §4.2 and its only new content is the
statement that the dual-Doob class contains the §4.2 class.

---

## Status: in the tex

Landed in `paper/src/weightedBMO.tex` (uncommitted):

  - `cor.square` (Corollary 4.21) with proof, at the end of §4.2, after `rmk.constant`;
  - `rmk.dualdoob` (Remark 4.22), immediately after it;
  - a pointer paragraph at the end of §3, after the `thm.dismart`/`thm.contmart` discussion;
  - `\label[proposition]{prop.lower}` (was a bare `\label`), because this document's cleveref
    setup infers the counter, not the environment, so `\cref{prop.lower}` printed "Theorem".

Local sanitised build (`.scratch/rebuild_paper.sh`, fonts stripped): 0 errors, 0 undefined
references or citations, 0 overfull boxes, 27 pages. Not a verification of the committed
source and not the committed page count.
