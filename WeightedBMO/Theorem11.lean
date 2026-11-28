import WeightedBMO.EstSmax01
import WeightedBMO.EstSmaximal
import WeightedBMO.EstX2X3

/-!
# Theorem 1.1 end to end

Khoa Lê, *Maximal inequalities, weighted BMO processes and the largest-jump normaliser*
(arXiv:2211.15550), Theorem 1.1 (`cor.maximaldagger`), as a single statement:
`cor_maximaldagger` concludes the five displayed estimates as the conjuncts of
one conclusion, from one hypothesis bundle.

## The three objects

The paper's theorem involves three distinct objects, and the statement keeps
them separate:

* the **weight** `ψ`, which in the paper is `t ↦ E_t X^♯_{t,τ}` — the
  nonnegative supermartingale of `est.upperbound` (`estSmax01`'s `hψ`), with the
  two stopping-time domination properties `hdom`, `hdomL` that make
  `d(X_s, X_·)` lie in weighted BMO with weight `2ψ`;
* the **horizon sharp maximal function** `Ψ`, which in the paper is
  `X^♯_τ = X^♯_{0,τ} = sup_{s∈[0,τ]} E_s d(X_{s-},X_τ)` — the object of
  `est.Smaximal`;
* the two **martingales** `M` and `N`, in the paper `M = 2 E_· X^♯_τ` (so
  `M_τ = 2X^♯_τ`) and `N = E_· d(X_0,X_τ)` (so `N_τ = d(X_0,X_τ)`).

`ψ` and `Ψ` cannot be merged: in the paper `ψ_τ = E_τ X^♯_{τ,τ} =
E_τ d(X_{τ-},X_τ)`, which is strictly smaller than `X^♯_τ` in general, so the
terminal value of the weight is *not* the horizon sharp maximal function.  The
one place where they meet is time `0`: `ψ_0 = E_0 X^♯_{0,τ} = E_0 X^♯_τ =
E_0 Ψ`, which is the right-hand side of `est.Smax01`.

## The five displays

* `est.upperbound`, `‖sup_{t∈[0,τ]} d(X_0,X_t)‖_m ≤ 2 c_m m ‖sup_{t∈[0,τ]} ψ_t‖_m`
  for every `m > 0` — `estUpperbound`; `2 * goodLambdaConstant p = 2 c_p p`
  since `goodLambdaConstant p = p c_p`;
* `est.X2`, the normalized form `sup_{ε>0} ‖·‖_m ≤ 2 c_m m` — `estX2`,
  reduced to the paper's bare constant here by `eLpNorm_one` (the estimate
  itself is stated for a finite measure, where the constant carries `‖1‖_p`);
* `est.X3`, `sup_{ε>0} E exp(λ sup_t ·) ≤ M` for `λ ≤ (2e³)⁻¹` — `estX3`,
  likewise reduced from `M · μ(univ)`; `exponentialBound` is the paper's `M`,
  its term of index zero being one;
* `est.Smaximal`, both inequalities,
  `(m-1)/(2m-1)‖Ψ‖_m ≤ ‖sup_t d(X_0,X_t)‖_m ≤ (2c_m m²)/(m-1)‖Ψ‖_m` for
  `m > 1` — `estSmaximal_lower` and `estSmaximal_upper` composed with
  `M_τ = 2Ψ`;
* `est.Smax01`, `‖sup_t d(X_0,X_t)‖_m ≤ 2c_m m (1-m)^{-1/m} ‖ψ_0‖_m` for
  `0 < m < 1` — `estSmax01`, with no Kuhn hypothesis.

## Differences from the paper, none of them in the constants

* `‖·‖_m = (E|·|^m)^{1/m}` is `eLpNorm · (ofReal m) μ`; the paper's
  `‖·‖_∞` case is not covered.
* The paper has `τ > 0`; here `0 ≤ T`, so `T = 0` is also allowed.
* `est.X3` is stated with `∫⁻ ofReal` rather than `E`; the integrand is
  nonnegative, so the two agree.
* `X` is described in the paper as an RCLL adapted integrable process; here
  right-continuity, left limits, adaptedness and the integrability needed at
  stopping times are the explicit hypotheses `cX`, `lX`, `mv`, `hdata`.
* `X^♯` itself is not defined: `ψ` and `Ψ` stand in for it, because an RCLL
  version of `t ↦ E_t X^♯_{t,τ}` is not available here (Dellacherie--Meyer II
  (2.9)).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ m}

omit [IsProbabilityMeasure μ] in
/-- `eLpNorm` of a pointwise doubled real function. -/
private theorem eLpNorm_two_mul {f : Ω → ℝ} {p : ℝ} :
    eLpNorm (fun ω => 2 * f ω) (ENNReal.ofReal p) μ =
      ENNReal.ofReal 2 * eLpNorm f (ENNReal.ofReal p) μ := by
  rw [show (fun ω => 2 * f ω) = (2 : ℝ) • f from rfl, eLpNorm_const_smul,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- `ofReal A * (ofReal 2 * x) = ofReal (2 * A) * x`. -/
private theorem ofReal_mul_ofReal_two_mul {A : ℝ} (hA : 0 ≤ A) (x : ℝ≥0∞) :
    ENNReal.ofReal A * (ENNReal.ofReal 2 * x) = ENNReal.ofReal (2 * A) * x := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA, mul_comm A 2]

/-- On a probability measure the `L^p` norm of the constant `1` is `1`; this is
what turns the finite-measure forms of `est.X2` and `est.X3` into the paper's
bare constants. -/
private theorem eLpNorm_one {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal q) μ = 1 := by
  rw [eLpNorm_const' (1:ℝ) (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top,
    measure_univ]
  simp

set_option maxHeartbeats 1200000 in
/-- **Theorem 1.1** (`cor.maximaldagger`) end to end: the five displayed
estimates, from one set of hypotheses. -/
theorem cor_maximaldagger {E : Type*} [PseudoMetricSpace E]
    (X Xl : Ω → ℝ → E) (ψ : Ω → ℝ → ℝ) (Ψ : Ω → ℝ) (M N : ℝ → Ω → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hℱ : RightContinuousFiltration ℱ)
    (hψpos : ∀ ω t, t ∈ Icc 0 T → 0 < ψ ω t)
    (hψmeas : ∀ t ∈ Icc 0 T, Measurable[ℱ t] (fun ω => ψ ω t))
    (hdom : ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
      (∀ ω, 0 ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫ ω in G, dist (X ω (U ω)) (X ω T) ∂μ) ≤ ∫ ω in G, ψ ω (S ω) ∂μ)
    (hdomL : ∀ (S : Ω → ℝ) (hS : IsStoppingTime ℱ S),
      (∀ ω, 0 ≤ S ω) → (∀ ω, S ω ≤ T) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫ ω in G, dist (Xl ω (S ω)) (X ω T) ∂μ) ≤ ∫ ω in G, ψ ω (S ω) ∂μ)
    (hdata : ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
      (∀ ω, 0 ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
      Measurable[hS.measurableSpace] (fun ω => ψ ω (S ω)) ∧
      Measurable[m] (fun ω => |dist (X ω 0) (X ω (U ω)) - dist (X ω 0) (Xl ω (S ω))|) ∧
      Integrable (fun ω => |dist (X ω 0) (X ω (U ω)) - dist (X ω 0) (Xl ω (S ω))|) μ ∧
      Integrable (fun ω => dist (X ω (U ω)) (X ω T)) μ ∧
      Integrable (fun ω => dist (Xl ω (S ω)) (X ω T)) μ ∧
      Integrable (fun ω => ψ ω (S ω)) μ)
    (mv : ∀ u ∈ Icc 0 T, Measurable[ℱ u] (fun ω => dist (X ω 0) (X ω u)))
    (cX : ∀ ω u, u ∈ Ico 0 T → ContinuousWithinAt (X ω) (Ici u) u)
    (lX : ∀ ω u, u ∈ Ioc 0 T → Tendsto (X ω) (𝓝[<] u) (𝓝 (Xl ω u)))
    (cw : ∀ ω u, u ∈ Ico 0 T → ContinuousWithinAt (ψ ω) (Ici u) u)
    (lw : ∀ ω u, u ∈ Ioc 0 T → ∃ l, Tendsto (ψ ω) (𝓝[<] u) (𝓝 l))
    (hψbdd : ∀ ω, BddAbove ((fun t => 2 * ψ ω t) '' Icc 0 T))
    (hψ : Supermartingale (fun t ω => ψ ω t) ℱ μ)
    (hM : Martingale M ℱ μ) (hMmeas : ∀ t, Measurable (M t)) (hM0 : ∀ t ω, 0 ≤ M t ω)
    (hMc : ∀ ω, ∀ t ∈ Ico 0 T, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (hwt : ∀ ω t, t ∈ Icc 0 T → 2 * ψ ω t ≤ M t ω)
    (hMΨ : M T =ᵐ[μ] fun ω => 2 * Ψ ω)
    (hAb : ∀ ω, BddAbove ((fun u => dist (X ω 0) (X ω u)) '' Icc 0 T))
    (hN : Martingale N ℱ μ) (hNmeas : ∀ t, Measurable (N t)) (hN0 : ∀ t ω, 0 ≤ N t ω)
    (hNc : ∀ ω, ∀ t ∈ Ico 0 T, ContinuousWithinAt (fun s => N s ω) (Ici t) t)
    (hNb : ∀ ω, BddAbove ((fun u => N u ω) '' Icc 0 T))
    (hNT : N T =ᵐ[μ] fun ω => dist (X ω 0) (X ω T))
    (hΨ0 : ∀ ω, 0 ≤ Ψ ω)
    (hΨ : ∀ ω, Ψ ω ≤ intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T +
      intervalSup (fun u => N u ω) 0 T) :
    -- `est.upperbound`
    (∀ p : ℝ, 0 < p →
        eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p) *
            eLpNorm (fun ω => intervalSup (fun t => ψ ω t) 0 T) (ENNReal.ofReal p) μ) ∧
    -- `est.X2`
    (∀ (ε : ℝ), 0 < ε → ∀ p : ℝ, 0 < p →
        eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
          (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p)) ∧
    -- `est.X3`
    (∀ (ε rate : ℝ), 0 < ε → rate ≤ (2 * Real.exp 3)⁻¹ →
        (∫⁻ ω, ENNReal.ofReal (Real.exp (rate * intervalSup (fun t =>
          dist (X ω 0) (X ω t) / (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T)) ∂μ) ≤
          ENNReal.ofReal exponentialBound) ∧
    -- `est.Smaximal`, lower bound
    (∀ p : ℝ, 1 < p → ENNReal.ofReal ((p - 1) / (2 * p - 1)) *
        eLpNorm Ψ (ENNReal.ofReal p) μ ≤
          eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
            (ENNReal.ofReal p) μ) ∧
    -- `est.Smaximal`, upper bound
    (∀ p : ℝ, 1 < p →
        eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p * (p / (p - 1))) *
            eLpNorm Ψ (ENNReal.ofReal p) μ) ∧
    -- `est.Smax01`
    (∀ p : ℝ, 0 < p → p < 1 →
        eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p * (1 - p) ^ (-(1 / p))) *
            eLpNorm (fun ω => ψ ω 0) (ENNReal.ofReal p) μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact estUpperbound X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hψbdd hp
  · intro ε hε p hp
    refine (estX2 X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hε hp).trans
      (le_of_eq ?_)
    rw [eLpNorm_one hp, mul_one]
  · intro ε rate hε hrate
    refine (estX3 X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hε hrate).trans
      (le_of_eq ?_)
    rw [measure_univ, mul_one]
  · intro p hp
    exact estSmaximal_lower X Ψ N hT (fun u hu => (mv u hu).mono (ℱ.le u) le_rfl)
      (fun ω u hu => continuousWithinAt_const.dist (cX ω u hu)) hAb hN hNmeas hN0 hNc hNb hNT
      hΨ0 hΨ hp
  · intro p hp
    have hupper := estSmaximal_upper X Xl ψ M hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw
      hM hMmeas hM0 hMc hwt hp
    have hMT' : eLpNorm (M T) (ENNReal.ofReal p) μ =
        ENNReal.ofReal 2 * eLpNorm Ψ (ENNReal.ofReal p) μ := by
      rw [eLpNorm_congr_ae hMΨ, eLpNorm_two_mul]
    rw [hMT'] at hupper
    have hA : (0:ℝ) ≤ goodLambdaConstant p * (p / (p - 1)) := by
      have h0 : (0:ℝ) ≤ goodLambdaConstant p := by
        unfold goodLambdaConstant
        positivity
      exact mul_nonneg h0 (div_nonneg (by linarith) (by linarith))
    refine hupper.trans (le_of_eq ?_)
    rw [ofReal_mul_ofReal_two_mul hA,
      show 2 * (goodLambdaConstant p * (p / (p - 1))) =
        2 * goodLambdaConstant p * (p / (p - 1)) from by ring]
  · intro p hp hp1
    exact estSmax01 X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hψbdd hψ hp hp1

end WeightedBMO
