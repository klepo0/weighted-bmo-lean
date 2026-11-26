# Applications of Theorem 1.1 of arXiv:2211.15550 — what a search found

Question posed: find an application of Theorem 1.1 of Khoa Lê, *Maximal inequalities and
weighted BMO processes* (arXiv:2211.15550v3), that is not in the literature and is worth
publishing.

Method: an eight-member search (ultramath swarm `smwwvwoh2`, `.ultramath/smwwvwoh2/`) ran 20
directions over roughly five hours. Each direction had to deliver a fully derived application
theorem, an explicit computation of the sharp function from the model, and a novelty argument.
Every submission was checked by hand against the primary sources; 8 were submitted, 2 accepted,
6 rejected, and 12 directions were abandoned by the members themselves as they collapsed into
known results.

## 1. The structural finding

Theorem 1.1 is a synthesis, and the paper says so. In §"Relation to previous works":
*"cor.maximaldagger and martingale inequalities are consequences of thm.bmophi but not earlier
results."* The proof bears it out:

- (1.1) is `ineq.JNweighted`, i.e. Theorem 1.3 applied with weight `phi = 2 E_. X^sharp_{.,tau}`;
- (1.2) is `est.jnweight2`, the self-normalized John–Nirenberg inequality;
- (1.6) upper is (1.1) plus Doob; (1.6) lower is Doob plus the triangle inequality;
- (1.7) is a Doob-type bound for the supermartingale `sup_t E_t X^sharp_{t,tau}`.

Consequently an "application of Theorem 1.1" is, in one of four ways, a corollary of something
already known, and every rejected submission was one of these:

| shape of the application | what dominates it |
|---|---|
| sharp function bounded by a deterministic modulus `C(t-s)^a` | arXiv:2210.15736 (John–Nirenberg), constant `11 p` vs `2 c_m m` |
| model is Gaussian or scale-Gaussian after conditioning | Borell/Fernique quenched, growth `sqrt(m)` vs `2 c_m m` |
| adapted defect telescopes into observed levels | a union bound over the grid |
| normalizer bounded below by a terminal scale | a terminal-scale maximal inequality |

So a genuinely new application needs a sharp function that is (i) *not* Gaussian after any
change of filtration, (ii) genuinely random and computed from the model rather than postulated,
(iii) not dominated below by a terminal scale, and (iv) belonging to a field where the resulting
statement is what a specialist wants. Nothing weaker survived scrutiny here.

## 2. The two things that cleared the bar

### A. Self-normalized maximal bounds for Riemann–Liouville stable processes

`.ultramath/smwwvwoh2/m2/application.md`. For symmetric `alpha`-stable `L`, `1<alpha<2`,
`1/alpha<H<1`, `a = H - 1/alpha`, and `X_t = int_0^t (t-s)^a dL_s`:

    A_{r,tau} = sup_{u in [r,tau]} | int_0^r ((tau-s)^a - (u-s)^a) dL_s |,
    N_t       = D_{H,alpha} tau^H + sup_{r<=t} A_{r,tau},

then `|| sup_t |X_t| / (eps + N_t) ||_m <= 2 c_m m` for every `m>0`, and the exponential moment
is bounded by `M` for `lambda <= (2e^3)^{-1}`, with `D` explicit (37.3198 at `alpha=3/2`,
`H=4/5`). The sharp function splits into an `F_u`-measurable historical term and an independent
future stable term, exactly computable; the historical term is a nondegenerate stable variable,
so the essential supremum of the sharp function is infinite and the unweighted John–Nirenberg
theorem of arXiv:2210.15736 cannot be used at all. That is what makes this one an application
rather than a corollary.

Correction required in the note: (11) states an identity
`a int_0^t (t-s)^{a-1} s^{1/alpha} ds = m t^H / H` which is only an inequality (the integral is
`t^H B(a, 1+1/alpha) a`, so one needs `a B(a,1+1/alpha) <= 1/(a+1/alpha)`; at `alpha=2`,
`a=1/2` the two sides are 0.7854 and 1).

### B. A one-big-jump maximal principle for monotone processes

`.ultramath/smwwvwoh2/m6/application.md`. For `xi_k>=0` adapted, `b_k = E_{k-1} xi_k`, with the
pathwise mean budget `sum_{k<=n} b_k <= K`, put `S_k = sum_{j<=k} xi_j`, `J_k = max_{j<=k} xi_j`.
Then

    P( max_{k<=n} S_k/(K+J_k) > u ) <= exp(e^lambda - 1 - lambda u)   for all lambda>0,
    hence                              <= e^{u-1} u^{-u}.

So the statistic is sub-Poisson: `E Z <= 4.78`, 95% envelope `S_k <= 4.316 (K+J_k)` simultaneously
for all prefixes, all moments and all exponential moments finite, with no independence, variance,
mixing or mark mgf; the Pareto tail index 1.2 case has `E exp(theta S_n) = infinity` and is
covered. The mechanism is `(R_k - R_{k-1})_+ <= min{1, xi_k/(K+J_{k-1})}` — a new record cost
raises the quotient by at most one — followed by a chord inequality and a positive supermartingale.

Novelty anchor: Geiss–Scheutzow (arXiv:2101.10884), Theorem 2.2 is sharp for *predictable*
dominators and their Remark 2.7 records that a non-predictable dominator admits no finite
constant. `K + J` is exactly such an optional dominator, and the quotient argument gets order-one
tails anyway. This is a new inequality, not a corollary: Theorem 1.1 supplies the normalizer, the
quotient supermartingale supplies the result and beats the imported constants by two orders of
magnitude.

Honest limits: the pathwise budget `B_n <= K` is stronger than a conditional-mean cost-to-go, and
no sharpness is claimed for `e^{u-1}u^{-u}` (the open question is which model attains it).

## 3. The terrain, direction by direction

Abandoned by the members as collapsible (12): Wasserstein propagation of chaos (sharp function
carries no `N`-dependent information); stochastic approximation (Doob decomposition makes the
noise a martingale); metric-space diffusions (heat-kernel/exit-time theory); Markov bridges
(normalizer comparable to the path range); optimal stopping (Snell-envelope bounds are sharper);
reflected queues (Lindley makes it a one-line corollary); adaptive MCMC (Dobrushin bounds are
sub-Gaussian; Poisson-equation route available); metric groups / noncommuting isometries (Lévy–
Ottaviani plus matrix Doob–BDG); filtering (direct recursion is sharper); occupation times
(standard conditional-occupation estimates); U-statistics (compensator/Hoeffding decomposition);
BSVIE (the known part of the terminal increment recreates the original problem).

Rejected by the judge after submission (6): the adapted Kolmogorov–Chentsov criterion (corollary
of arXiv:2210.15736); the predictive CUSUM/queue bound (one line from Lindley + (1.2), constants
2–3× worse than arXiv:2210.15736); quenched subordinated fBm (normalizer dominated below by the
terminal clock scale, so Borell wins by `sqrt(m)` vs `m`); delayed Riemann quadrature (the adapted
defect telescopes to `-hZ_{t_{n-1}} - (h/2)Z_{t_n}`, so a three-line union bound beats the
certificate by a factor 35); hidden-scale posterior normalization (correct, but a normal scale
mixture is the most classical non-Gaussian family and the phenomenon is Studentization); and
second-chaos Rosenblatt–Volterra readouts, which ended with a clean negative result worth
recording: for a second Wiener chaos the sharp function's floor is the terminal `L^2`/canonical-
metric scale, and Kolmogorov–Chentsov at that scale already gives `O(p)` moments on every quenched
fiber, so no choice of readout creates a gap.

## 4. What is worth doing next

1. Write up (B) as the short paper it is: "An optional dominator that escapes the Geiss–Scheutzow
   sharpness obstruction", with (i) a model attaining the Poisson-type tail or a proof that none
   does, (ii) the continuous-time form with a deterministic compensator budget, (iii) the
   comparison with Freedman/Fuk–Nagaev at a fixed truncation level.
2. Write up (A) with the two referee-level additions it still needs: a lower bound showing the
   historical normalizer is nondegenerate, and the explicit statement that the normalizer is a
   functional of the driver, not of the observed `X`.
3. Treat this as a boundary: the paper's own deferred sentence, "applications of (1.1) will be
   discussed elsewhere", cannot be discharged by finding an application of (1.1), only by finding
   results in other fields that the sharp-function method reaches. (B) is the sharpest instance:
   the method identifies the right normalizer and then the domain-specific argument improves on it.
