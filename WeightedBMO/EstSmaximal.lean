import WeightedBMO.SharpMaximal
import WeightedBMO.ContinuousDoob

/-!
# `est.Smaximal` end to end

Khoa Lê, *Maximal inequalities and weighted BMO processes*
(arXiv:2211.15550v3), Theorem 1.1, second inequality of `est.Smaximal`:
for a nonnegative martingale `M`, the maximal function of `t ↦ d(X_0, X_t)` on
`[0,T]` is bounded by the John--Nirenberg constant times `p/(p-1)` times the
`Lᵖ` norm of the terminal value.

The bookkeeping between the two formulations of the supremum is
`ofReal_intervalSup_le_supOn`: on each time `t` of `[0,T]` the interval
supremum used by the John--Nirenberg estimate is at most the dyadic supremum
`supOn` used by the continuous-time Doob step, provided the dominating process
is right-continuous.

`estSmaximal_upper` assembles the three pieces: the weighted BMO bound
`weightedBMOOfSharpMaximal`, the John--Nirenberg inequality
`sharpMaximal_eLpNorm_le` with the weight `2ψ`, and Doob's step
`eLpNorm_supOn_le`.  The sharp maximal function `ψ` is a hypothesis; in the
paper `ψ = X^♯_{·,T}` and `M = 2 E_· X^♯_T`, so `M_T = 2 X^♯_T` and the
constant `c_p p²/(p-1)` becomes `2 c_p p²/(p-1)`, as in `est.Smaximal`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ m}

omit m in
/-- An interval supremum dominated by a right-continuous process is bounded by
the dyadic supremum of that process. -/
theorem ofReal_intervalSup_le_supOn {M : ℝ → Ω → ℝ} {f : Ω → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcont : ∀ ω, ∀ t ∈ Ico 0 T, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (hf0 : ∀ ω t, t ∈ Icc 0 T → 0 ≤ f ω t)
    (hle : ∀ ω t, t ∈ Icc 0 T → f ω t ≤ M t ω) (ω : Ω) :
    ENNReal.ofReal (intervalSup (f ω) 0 T) ≤ supOn M T ω := by
  rcases eq_or_ne (supOn M T ω) ⊤ with htop | htop
  · simp [htop]
  · have hbound : ∀ x ∈ f ω '' Icc 0 T, x ≤ (supOn M T ω).toReal := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : ENNReal.ofReal (M u ω) ≤ supOn M T ω :=
        ofReal_le_supOn hT hcont hu ω
      have h2 : ENNReal.ofReal (f ω u) ≤ supOn M T ω :=
        (ENNReal.ofReal_le_ofReal (hle ω u hu)).trans h1
      have h3 : (ENNReal.ofReal (f ω u)).toReal ≤ (supOn M T ω).toReal :=
        ENNReal.toReal_mono htop h2
      rwa [ENNReal.toReal_ofReal (hf0 ω u hu)] at h3
    have hs : intervalSup (f ω) 0 T = sSup (f ω '' Icc 0 T) := rfl
    rw [hs, ← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal (Real.sSup_le hbound (by positivity))

/-- **`est.Smaximal`, right-hand side, end to end.**  With the sharp maximal
function `ψ` supplied as a hypothesis and the paper's weight `2ψ` dominated by a
nonnegative right-continuous martingale `M`, the maximal function of the path
`t ↦ d(X_0, X_t)` is bounded by `c_p p · p/(p-1)` times `‖M_T‖_p`.  In the
paper `ψ = X^♯_{·,T}` and `M = 2 E_· X^♯_T`, so `M_T = 2 X^♯_T` and the constant
becomes `2 c_p p²/(p-1)`. -/
theorem estSmaximal_upper {E : Type*} [PseudoMetricSpace E]
    (X Xl : Ω → ℝ → E) (ψ : Ω → ℝ → ℝ) (M : ℝ → Ω → ℝ) {T : ℝ} (hT : 0 ≤ T)
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
    (hM : Martingale M ℱ μ) (hMmeas : ∀ t, Measurable (M t)) (hM0 : ∀ t ω, 0 ≤ M t ω)
    (hMc : ∀ ω, ∀ t ∈ Ico 0 T, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (hwt : ∀ ω t, t ∈ Icc 0 T → 2 * ψ ω t ≤ M t ω)
    {p : ℝ} (hp : 1 < p) :
    eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (goodLambdaConstant p * (p / (p - 1))) *
        eLpNorm (M T) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  -- (1) the Johnson--Nirenberg bound with the weight `2ψ`
  have hJN := sharpMaximal_eLpNorm_le (ℱ := ℱ) (a := 0) (p := p) X Xl ψ hT hℱ hψpos hψmeas
    hdom hdomL hdata mv cX lX cw lw hp0 (E₀ := univ) MeasurableSet.univ
  -- (2) the sup of the weight is dominated by the dyadic sup of `M`
  have hbdd : ∀ ω, BddAbove ((fun u => 2 * ψ ω u) '' Icc 0 T) := by
    intro ω
    obtain ⟨d, hd⟩ := cadlag_bounded (cw ω) (lw ω)
    refine ⟨2 * d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact mul_le_mul_of_nonneg_left
      ((le_abs_self (ψ ω u)).trans (hd (mem_image_of_mem _ hu))) (by norm_num)
  have hf0 : ∀ ω t, t ∈ Icc 0 T → 0 ≤ 2 * ψ ω t := fun ω t ht =>
    (mul_pos (by norm_num) (hψpos ω t ht)).le
  have hpt : ∀ ω, ENNReal.ofReal (intervalSup (fun u => 2 * ψ ω u) 0 T) ≤ supOn M T ω :=
    fun ω => ofReal_intervalSup_le_supOn hT hMc hf0 hwt ω
  have hInt0 : ∀ ω, 0 ≤ intervalSup (fun u => 2 * ψ ω u) 0 T := fun ω =>
    (hf0 ω 0 ⟨le_rfl, hT⟩).trans (le_intervalSup (hbdd ω) ⟨le_rfl, hT⟩)
  have hbridge : eLpNorm (fun ω => intervalSup (fun u => 2 * ψ ω u) 0 T) (ENNReal.ofReal p) μ ≤
      eLpNorm (supOn M T) (ENNReal.ofReal p) μ := by
    have hA : eLpNorm (fun ω => intervalSup (fun u => 2 * ψ ω u) 0 T) (ENNReal.ofReal p) μ =
        (∫⁻ ω, ENNReal.ofReal ((intervalSup (fun u => 2 * ψ ω u) 0 T) ^ p) ∂μ) ^ (1 / p) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp0)
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
      congr 1
      apply lintegral_congr
      intro ω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hInt0 ω),
        ENNReal.ofReal_rpow_of_nonneg (hInt0 ω) hp0.le]
    have hB : eLpNorm (supOn M T) (ENNReal.ofReal p) μ =
        (∫⁻ ω, (supOn M T ω) ^ p ∂μ) ^ (1 / p) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp0)
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
      simp
    have hstep : ∫⁻ ω, ENNReal.ofReal ((intervalSup (fun u => 2 * ψ ω u) 0 T) ^ p) ∂μ
        ≤ ∫⁻ ω, (supOn M T ω) ^ p ∂μ := by
      calc ∫⁻ ω, ENNReal.ofReal ((intervalSup (fun u => 2 * ψ ω u) 0 T) ^ p) ∂μ
          = ∫⁻ ω, (ENNReal.ofReal (intervalSup (fun u => 2 * ψ ω u) 0 T)) ^ p ∂μ := by
            apply lintegral_congr
            intro ω
            exact (ENNReal.ofReal_rpow_of_nonneg (hInt0 ω) hp0.le).symm
        _ ≤ ∫⁻ ω, (supOn M T ω) ^ p ∂μ :=
            lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpt ω) hp0.le
    rw [hA, hB]
    exact ENNReal.rpow_le_rpow (z := 1 / p) hstep (by positivity)
  -- (3) Doob's step
  have hDoob := eLpNorm_supOn_le hMmeas hM hM0 hT hp
  -- (4) assemble
  rw [Measure.restrict_univ] at hJN
  calc eLpNorm (fun ω => intervalSup (fun u => dist (X ω 0) (X ω u)) 0 T) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (goodLambdaConstant p) *
          eLpNorm (fun ω => intervalSup (fun u => 2 * ψ ω u) 0 T) (ENNReal.ofReal p) μ := hJN
    _ ≤ ENNReal.ofReal (goodLambdaConstant p) * eLpNorm (supOn M T) (ENNReal.ofReal p) μ :=
        mul_le_mul_left' hbridge _
    _ ≤ ENNReal.ofReal (goodLambdaConstant p) *
          (ENNReal.ofReal (p / (p - 1)) * eLpNorm (M T) (ENNReal.ofReal p) μ) :=
        mul_le_mul_left' hDoob _
    _ = ENNReal.ofReal (goodLambdaConstant p * (p / (p - 1))) *
          eLpNorm (M T) (ENNReal.ofReal p) μ := by
        have hC : 0 ≤ goodLambdaConstant p := by
          unfold goodLambdaConstant
          positivity
        rw [ENNReal.ofReal_mul hC]
        ring

end WeightedBMO
