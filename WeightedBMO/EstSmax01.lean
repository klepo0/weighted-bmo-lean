import WeightedBMO.EstX2X3
import WeightedBMO.Kuhn

/-!
# `est.Smax01`: Theorem 1.1 for exponents below one

Khoa Lê, *Maximal inequalities and weighted BMO processes*
(arXiv:2211.15550v3), Theorem 1.1, the last estimate:

  `‖sup_{t∈[0,T]} d(X_0,X_t)‖_p ≤ 2c_p p (1-p)^{-1/p} ‖E_0 X^♯_T‖_p` for `0 < p < 1`.

The paper's derivation has two inputs: the maximal estimate `est.upperbound`,
which holds for every exponent `p > 0` and bounds the path by the supremum of
the weight `2ψ`, and the `L^p` bound for `0 < p < 1`
`‖sup_t ψ_t‖_p ≤ (1-p)^{-1/p} ‖ψ_0‖_p` for the nonnegative supermartingale
`ψ_t = E_t X^♯_{t,T}` (Kuhn's lemma).  `estSmax01` performs that composition:
it bounds `sup(2ψ)` by `2 sup ψ` and applies the `p`-th power estimate.

Kuhn's lemma is *proved*, not assumed: `Kuhn.supermartingale_eLpNorm_intervalSup_le`
gives it for any nonnegative supermartingale with right-continuous paths, so the
only hypothesis about `ψ` here is `Supermartingale (fun t ω => ψ ω t) ℱ μ`.

Its proof needs the *event-tested* weak-type inequality

  `α μ({sup ψ > α} ∩ G) ≤ ∫_G ψ_0`  for every `G ∈ ℱ_0`,

not the global form `α μ{sup ψ > α} ≤ ∫ ψ_0`, which only gives an `L¹` bound.
The tested form is `SupermartingaleWeakType.supermartingale_max_le_of_measurableSet_zero`,
lifted to `[0,T]` by
`SupermartingaleLift.supermartingale_max_le_supOn_of_measurableSet_zero`; the
truncation that produces the sharp constant is
`Kuhn.lintegral_rpow_le_of_weak`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ m}

omit [IsProbabilityMeasure μ] in
/-- The interval supremum of a pointwise doubled process. -/
theorem eLpNorm_intervalSup_two_mul {f : Ω → ℝ → ℝ} {T p : ℝ} (hT : 0 ≤ T)
    (hf0 : ∀ ω t, t ∈ Icc 0 T → 0 ≤ f ω t)
    (hb : ∀ ω, BddAbove ((fun t => 2 * f ω t) '' Icc 0 T))
    (hb' : ∀ ω, BddAbove (f ω '' Icc 0 T)) (_hp : 0 < p) :
    eLpNorm (fun ω => 2 * intervalSup (f ω) 0 T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal 2 * eLpNorm (fun ω => intervalSup (fun t => 2 * f ω t) 0 T)
        (ENNReal.ofReal p) μ := by
  have hscale : eLpNorm (fun ω => 2 * intervalSup (f ω) 0 T) (ENNReal.ofReal p) μ =
      ENNReal.ofReal 2 * eLpNorm (fun ω => intervalSup (f ω) 0 T) (ENNReal.ofReal p) μ := by
    rw [show (fun ω => 2 * intervalSup (f ω) 0 T) =
        (2 : ℝ) • (fun ω => intervalSup (f ω) 0 T) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hscale]
  refine mul_le_mul_left' ?_ _
  apply eLpNorm_mono
  intro ω
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ((hf0 ω 0 ⟨le_rfl, hT⟩).trans
      (le_intervalSup (s := 0) (t := T) (u := 0) (hb' ω) ⟨le_rfl, hT⟩)),
    abs_of_nonneg ((mul_nonneg (by norm_num) (hf0 ω 0 ⟨le_rfl, hT⟩)).trans
      (le_intervalSup (s := 0) (t := T) (u := 0) (hb ω) ⟨le_rfl, hT⟩))]
  refine intervalSup_le hT ?_
  intro t ht
  exact (le_mul_of_one_le_left (hf0 ω t ht) (by norm_num : (1:ℝ) ≤ 2)).trans
    (le_intervalSup (s := 0) (t := T) (u := t) (hb ω) ht)

/-- **`est.Smax01`**: for `0 < p < 1` the maximal function of the path is
bounded by `2 c_p p (1-p)^{-1/p}` times the `L^p` norm of `ψ_0`, the value of
the weight at the initial time.  The supermartingale `L^p` bound for `p < 1`
(Kuhn's lemma) is `Kuhn.supermartingale_eLpNorm_intervalSup_le`, applied here to
the supermartingale hypothesis `hψ`. -/
theorem estSmax01 {E : Type*} [PseudoMetricSpace E]
    (X Xl : Ω → ℝ → E) (ψ : Ω → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
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
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * goodLambdaConstant p * (1 - p) ^ (-(1 / p))) *
        eLpNorm (fun ω => ψ ω 0) (ENNReal.ofReal p) μ := by
  have h1 := sharpMaximal_eLpNorm_le (ℱ := ℱ) (a := 0) (p := p) X Xl ψ hT hℱ hψpos hψmeas
    hdom hdomL hdata mv cX lX cw lw hp (E₀ := univ) MeasurableSet.univ
  rw [Measure.restrict_univ] at h1
  -- `sup(2ψ) ≤ 2 sup ψ`
  have hψbdd' : ∀ ω, BddAbove ((fun t => ψ ω t) '' Icc 0 T) := by
    intro ω
    obtain ⟨d, hd⟩ := hψbdd ω
    refine ⟨d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact ((le_mul_of_one_le_left (hψpos ω u hu).le (by norm_num : (1:ℝ) ≤ 2))).trans
      (hd (mem_image_of_mem _ hu))
  have h2 : eLpNorm (fun ω => intervalSup (fun t => 2 * ψ ω t) 0 T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal 2 * eLpNorm (fun ω => intervalSup (fun t => ψ ω t) 0 T)
        (ENNReal.ofReal p) μ := by
    have hscale : eLpNorm (fun ω => 2 * intervalSup (fun t => ψ ω t) 0 T) (ENNReal.ofReal p) μ =
        ENNReal.ofReal 2 * eLpNorm (fun ω => intervalSup (fun t => ψ ω t) 0 T)
          (ENNReal.ofReal p) μ := by
      rw [show (fun ω => 2 * intervalSup (fun t => ψ ω t) 0 T) =
          (2 : ℝ) • (fun ω => intervalSup (fun t => ψ ω t) 0 T) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hn1 : ∀ ω, 0 ≤ intervalSup (fun t => ψ ω t) 0 T := fun ω =>
      (hψpos ω 0 ⟨le_rfl, hT⟩).le.trans
        (le_intervalSup (s := 0) (t := T) (u := 0) (hψbdd' ω) ⟨le_rfl, hT⟩)
    have hn2 : ∀ ω, 0 ≤ intervalSup (fun t => 2 * ψ ω t) 0 T := fun ω =>
      (mul_nonneg (by norm_num) (hψpos ω 0 ⟨le_rfl, hT⟩).le).trans
        (le_intervalSup (s := 0) (t := T) (u := 0) (hψbdd ω) ⟨le_rfl, hT⟩)
    have hpt : ∀ ω, intervalSup (fun t => 2 * ψ ω t) 0 T ≤ 2 * intervalSup (fun t => ψ ω t) 0 T := by
      intro ω
      refine intervalSup_le hT ?_
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (le_intervalSup (s := 0) (t := T) (u := t) (hψbdd' ω) ht) (by norm_num)
    rw [← hscale]
    apply eLpNorm_mono
    intro ω
    calc ‖intervalSup (fun t => 2 * ψ ω t) 0 T‖ = intervalSup (fun t => 2 * ψ ω t) 0 T := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hn2 ω)]
      _ ≤ 2 * intervalSup (fun t => ψ ω t) 0 T := hpt ω
      _ = ‖2 * intervalSup (fun t => ψ ω t) 0 T‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (hn1 ω))]
  have h3 := supermartingale_eLpNorm_intervalSup_le (ℱ := ℱ) (T := T) (q := p) hT hp hp1 hψ
    (fun ω t ht => (hψpos ω t ht).le) hψbdd' cw
  calc eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (goodLambdaConstant p) *
          eLpNorm (fun ω => intervalSup (fun t => 2 * ψ ω t) 0 T) (ENNReal.ofReal p) μ := h1
    _ ≤ ENNReal.ofReal (goodLambdaConstant p) * (ENNReal.ofReal 2 *
          eLpNorm (fun ω => intervalSup (fun t => ψ ω t) 0 T) (ENNReal.ofReal p) μ) :=
        mul_le_mul_left' h2 _
    _ ≤ ENNReal.ofReal (goodLambdaConstant p) * (ENNReal.ofReal 2 *
          (ENNReal.ofReal ((1 - p) ^ (-(1 / p))) *
            eLpNorm (fun ω => ψ ω 0) (ENNReal.ofReal p) μ)) :=
        mul_le_mul_left' (mul_le_mul_left' h3 _) _
    _ = ENNReal.ofReal (2 * goodLambdaConstant p * (1 - p) ^ (-(1 / p))) *
          eLpNorm (fun ω => ψ ω 0) (ENNReal.ofReal p) μ := by
        have hC : 0 ≤ goodLambdaConstant p := by
          unfold goodLambdaConstant
          positivity
        have hsplit : 2 * goodLambdaConstant p * (1 - p) ^ (-(1 / p)) =
            2 * (goodLambdaConstant p * (1 - p) ^ (-(1 / p))) := by ring
        rw [hsplit, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_mul hC]
        ring

end WeightedBMO
