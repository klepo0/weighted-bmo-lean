import WeightedBMO.EstX2X3

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

Kuhn's lemma itself is *not* proved here; it enters as the hypothesis `hKuhn`.
The obstruction is the same one recorded for `est.Smaximal`: the sharp `L^p`
bound for `p < 1` needs the event-tested form of the supermartingale maximal
inequality,
`α μ{sup ψ > α} ≤ ∫_{sup ψ > α} ψ_0`,
which is optional sampling at the first passage time `S = inf{t : ψ_t ≥ α}`
tested on `{S ≤ T} ∈ ℱ_S`.  Mathlib has optional sampling only in discrete
time and only unconditionally, and the global weak-type inequality (which does
follow from it) cannot give the sharp constant, because the layer-cake
integral `∫_0^∞ p α^{p-2} dα` diverges at the origin for `p < 1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ m}

omit [IsFiniteMeasure μ] in
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
(Kuhn's lemma) enters as a hypothesis on `ψ`. -/
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
    (hKuhn : ∀ {q : ℝ}, 0 < q → q < 1 →
      eLpNorm (fun ω => intervalSup (fun t => ψ ω t) 0 T) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((1 - q) ^ (-(1 / q))) *
          eLpNorm (fun ω => ψ ω 0) (ENNReal.ofReal q) μ)
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
  have h3 := hKuhn hp hp1
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
