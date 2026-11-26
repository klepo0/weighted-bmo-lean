import WeightedBMO.EstSmax01
import WeightedBMO.EstSmaximal
import WeightedBMO.EstX2X3

/-!
# Theorem 1.1 end to end

Khoa Lê, *Maximal inequalities and weighted BMO processes*
(arXiv:2211.15550v3), Theorem 1.1 (`cor.maximaldagger`), as a single statement.
For a `PseudoMetricSpace`-valued path `X` with right limits `Xl`, a weight `ψ`
(a hypothesis: in the paper `ψ_t = E_t X^♯_{t,T}`), a nonnegative
right-continuous martingale `M` dominating `2ψ`, and a nonnegative
right-continuous martingale `N` with terminal value `d(X_0, X_T)`,
`cor_maximaldagger` concludes all five displayed estimates at once:

* (1.6) `est.upperbound`, `‖sup_t d(X_0,X_t)‖_p ≤ 2c_p p ‖sup_t ψ_t‖_p`,
  `estUpperbound`;
* (1.7) `est.X2`, the normalized form, `estX2`;
* (1.8) `est.X3`, the exponential form at rate `(2e³)⁻¹`, `estX3`;
* (1.9) `est.Smaximal`, both inequalities, `estSmaximal_lower` and
  `estSmaximal_upper` composed with `M_T = 2ψ_T`;
* (1.10) `est.Smax01`, `‖sup_t d(X_0,X_t)‖_p ≤ 2c_p p (1-p)^{-1/p} ‖ψ_0‖_p`,
  `estSmax01`, which no longer assumes Kuhn's lemma.

The constants are the paper's: `goodLambdaConstant p = p c_p`, so
`2 * goodLambdaConstant p = 2c_p p`, and `2 * goodLambdaConstant p *
(p / (p - 1)) = 2c_p p²/(p-1)`.
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

set_option maxHeartbeats 1200000 in
/-- **Theorem 1.1** (`cor.maximaldagger`) end to end: the five displayed
estimates, from one set of hypotheses. -/
theorem cor_maximaldagger {E : Type*} [PseudoMetricSpace E]
    (X Xl : Ω → ℝ → E) (ψ : Ω → ℝ → ℝ) (M N : ℝ → Ω → ℝ) {T : ℝ} (hT : 0 ≤ T)
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
    (hMT : M T =ᵐ[μ] fun ω => 2 * ψ ω T)
    (hAb : ∀ ω, BddAbove ((fun u => dist (X ω 0) (X ω u)) '' Icc 0 T))
    (hN : Martingale N ℱ μ) (hNmeas : ∀ t, Measurable (N t)) (hN0 : ∀ t ω, 0 ≤ N t ω)
    (hNc : ∀ ω, ∀ t ∈ Ico 0 T, ContinuousWithinAt (fun s => N s ω) (Ici t) t)
    (hNb : ∀ ω, BddAbove ((fun u => N u ω) '' Icc 0 T))
    (hNT : N T =ᵐ[μ] fun ω => dist (X ω 0) (X ω T))
    (hψT0 : ∀ ω, 0 ≤ ψ ω T)
    (hψT : ∀ ω, ψ ω T ≤ intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T +
      intervalSup (fun u => N u ω) 0 T) :
    -- (1.6) `est.upperbound`
    (∀ p : ℝ, 0 < p →
        eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p) *
            eLpNorm (fun ω => intervalSup (fun t => ψ ω t) 0 T) (ENNReal.ofReal p) μ) ∧
    -- (1.7) `est.X2`
    (∀ (ε : ℝ), 0 < ε → ∀ p : ℝ, 0 < p →
        eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
          (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p) *
            eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal p) μ) ∧
    -- (1.8) `est.X3`
    (∀ (ε rate : ℝ), 0 < ε → rate ≤ (2 * Real.exp 3)⁻¹ →
        (∫⁻ ω, ENNReal.ofReal (Real.exp (rate * intervalSup (fun t =>
          dist (X ω 0) (X ω t) / (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T)) ∂μ) ≤
          ENNReal.ofReal exponentialBound * μ univ) ∧
    -- (1.9) `est.Smaximal`, lower bound
    (∀ p : ℝ, 1 < p → ENNReal.ofReal ((p - 1) / (2 * p - 1)) *
        eLpNorm (fun ω => ψ ω T) (ENNReal.ofReal p) μ ≤
          eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
            (ENNReal.ofReal p) μ) ∧
    -- (1.9) `est.Smaximal`, upper bound
    (∀ p : ℝ, 1 < p →
        eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p * (p / (p - 1))) *
            eLpNorm (fun ω => ψ ω T) (ENNReal.ofReal p) μ) ∧
    -- (1.10) `est.Smax01`
    (∀ p : ℝ, 0 < p → p < 1 →
        eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T)
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (2 * goodLambdaConstant p * (1 - p) ^ (-(1 / p))) *
            eLpNorm (fun ω => ψ ω 0) (ENNReal.ofReal p) μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact estUpperbound X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hψbdd hp
  · intro ε hε p hp
    exact estX2 X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hε hp
  · intro ε rate hε hrate
    exact estX3 X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hε hrate
  · intro p hp
    exact estSmaximal_lower X ψ N hT (fun u hu => (mv u hu).mono (ℱ.le u) le_rfl)
      (fun ω u hu => continuousWithinAt_const.dist (cX ω u hu)) hAb hN hNmeas hN0 hNc hNb hNT
      hψT0 hψT hp
  · intro p hp
    have hupper := estSmaximal_upper X Xl ψ M hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw
      hM hMmeas hM0 hMc hwt hp
    have hMT' : eLpNorm (M T) (ENNReal.ofReal p) μ =
        ENNReal.ofReal 2 * eLpNorm (fun ω => ψ ω T) (ENNReal.ofReal p) μ := by
      rw [eLpNorm_congr_ae hMT, eLpNorm_two_mul]
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
