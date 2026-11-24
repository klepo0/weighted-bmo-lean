import WeightedBMO.RealTimePartition
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

/-- Recover a conditional essential supremum bound from tests on all initial events. -/
theorem condExp_bound_of_event_tests {Ω : Type*} [m : MeasurableSpace Ω]
    {s : MeasurableSpace Ω} (hs : s ≤ m) (μ : @Measure Ω m) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable[m] f) (hn : ∀ ω, 0 ≤ f ω)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (h : ∀ E : Set Ω, MeasurableSet[s] E →
      (∫⁻ ω in E, ENNReal.ofReal (f ω) ∂μ) ≤ C * μ E) :
    eLpNorm (μ[f|s]) ⊤ μ ≤ C := by
  have hi : Integrable f μ := by
    refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all μ hn)).2 ?_⟩
    have hu := h univ MeasurableSet.univ
    rw [Measure.restrict_univ] at hu
    exact hu.trans_lt (ENNReal.mul_lt_top hC (measure_lt_top _ _))
  let g : Ω → ℝ := μ[f|s]
  have hb : g ≤ᵐ[μ.trim hs] fun _ => C.toReal := by
    apply ae_le_of_forall_setIntegral_le (integrable_condExp.trim hs stronglyMeasurable_condExp)
      (integrable_const _)
    intro E hE _
    rw [← setIntegral_trim hs stronglyMeasurable_condExp hE, setIntegral_condExp hs hi hE,
      ← setIntegral_trim hs stronglyMeasurable_const hE, setIntegral_const, smul_eq_mul]
    have hh := ENNReal.toReal_mono (ENNReal.mul_lt_top hC (measure_lt_top _ _)).ne (h E hE)
    rw [← ofReal_integral_eq_lintegral_ofReal hi.restrict (ae_of_all _ hn),
      ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_mul, mul_comm] at hh
    exact hh
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [ae_le_of_ae_le_trim hb, condExp_nonneg (m := s) (ae_of_all μ hn)] with ω hu hl
  rw [Real.enorm_of_nonneg hl, ← ENNReal.ofReal_toReal hC.ne]
  exact ENNReal.ofReal_le_ofReal hu

/-- Equation (1.10) from the interval moments in (1.9), uniformly over start times. -/
theorem conditional_exponential_of_interval_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℝ m)
    (Z : ℝ → ℝ → Ω → ℝ) (ρ : ℝ → ℝ → ℝ) {a T rate : ℝ}
    (hm : ∀ s t, a ≤ s → s ≤ t → t ≤ T → Measurable[ℱ t] (Z s t))
    (hz : ∀ s t ω, a ≤ s → s ≤ t → t ≤ T → 0 ≤ Z s t ω)
    (hzero : ∀ r ∈ Icc a T, ∀ ω, Z r r ω = 0)
    (hsplit : ∀ r s t ω, a ≤ r → r ≤ s → s ≤ t → t ≤ T →
      Z r t ω ≤ Z r s ω + Z s t ω)
    (hmom : ∀ s t, a ≤ s → s ≤ t → t ≤ T → ∀ c : ℝ, 0 < c → ρ s t ≤ c →
      ∀ E : Set Ω, MeasurableSet[ℱ s] E → ∀ n : ℕ, 0 < n →
      eLpNorm (fun ω => Z s t ω / c) (ENNReal.ofReal n) (μ.restrict E) ≤
        ENNReal.ofReal (goodLambdaConstant n) *
          eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal n) (μ.restrict E))
    (hb : (smallScaleBounds ρ a T).Nonempty)
    (hend : rate * sInf (smallScaleBounds ρ a T) ≤ Real.exp (-3)) :
    (⨆ r : Icc a T, eLpNorm (μ[fun ω => Real.exp (rate * Z r T ω)|ℱ r]) ⊤ μ) < ⊤ := by
  obtain ⟨C, hC, he⟩ := uniform_exponential_of_interval_moments μ ℱ Z ρ
    hm hz hzero hsplit hmom hb hend
  refine lt_of_le_of_lt (iSup_le fun r => ?_) hC
  apply condExp_bound_of_event_tests (ℱ.le r) μ _ (fun _ => (Real.exp_pos _).le) hC (he r r.property)
  exact Real.continuous_exp.measurable.comp
    (measurable_const.mul ((hm r T r.property.1 r.property.2 le_rfl).mono (ℱ.le T) le_rfl))

end WeightedBMO
