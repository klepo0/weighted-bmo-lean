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

/-- `est.jnexpwei` from the interval moments in `est.jnweight2`, uniformly over start times. -/
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


/-- Express a weighted conditional expectation bound by tests on initial events. -/
theorem weighted_condExp_iff_event_tests {Ω : Type*} [m : MeasurableSpace Ω]
    {s : MeasurableSpace Ω} (hs : s ≤ m) (μ : @Measure Ω m) [IsFiniteMeasure μ]
    {f w : Ω → ℝ} (hf : Measurable[m] f) (hi : Integrable f μ) (hn : ∀ ω, 0 ≤ f ω)
    (hw : Measurable[s] w) (hp : ∀ ω, 0 < w ω) {B : ℝ} :
    (eLpNorm (fun ω => (μ[f|s]) ω / w ω) ⊤ μ ≤ ENNReal.ofReal B) ↔
      ∀ E : Set Ω, MeasurableSet[s] E →
        (∫⁻ ω in E, ENNReal.ofReal (f ω / w ω) ∂μ) ≤ ENNReal.ofReal B * μ E := by
  let g : Ω → ℝ := μ[f|s]
  let F ω := ENNReal.ofReal (f ω)
  let G ω := ENNReal.ofReal (g ω)
  have gm : Measurable[m] g := stronglyMeasurable_condExp.measurable.mono hs le_rfl
  have gn : 0 ≤ᵐ[μ] g := condExp_nonneg (ae_of_all μ hn)
  constructor
  · intro h E hE
    let ν := μ.restrict E
    let k ω := ENNReal.ofReal ((w ω)⁻¹)
    have km : Measurable[s] k := hw.inv.ennreal_ofReal
    have dEq : (ν.withDensity F).trim hs = (ν.withDensity G).trim hs := by
      apply Measure.ext
      intro A hA
      rw [trim_measurableSet_eq hs hA, trim_measurableSet_eq hs hA,
        withDensity_apply F (hs _ hA), withDensity_apply G (hs _ hA)]
      change (∫⁻ ω in A, F ω ∂μ.restrict E) = ∫⁻ ω in A, G ω ∂μ.restrict E
      rw [Measure.restrict_restrict (hs _ hA),
        ← ofReal_integral_eq_lintegral_ofReal hi.restrict (ae_of_all _ hn),
        ← ofReal_integral_eq_lintegral_ofReal integrable_condExp.restrict
          (ae_mono Measure.restrict_le_self gn),
        setIntegral_condExp hs hi (hA.inter hE)]
    have pull : (∫⁻ ω, (F * k) ω ∂ν) = ∫⁻ ω, (G * k) ω ∂ν := by
      rw [← lintegral_withDensity_eq_lintegral_mul ν hf.ennreal_ofReal (km.mono hs le_rfl),
        ← lintegral_withDensity_eq_lintegral_mul ν gm.ennreal_ofReal (km.mono hs le_rfl),
        ← lintegral_trim hs km, ← lintegral_trim hs km, dEq]
    have hpoint : ∀ᵐ ω ∂μ, ENNReal.ofReal (g ω / w ω) ≤ ENNReal.ofReal B := by
      apply (ae_le_eLpNormEssSup (f := fun ω => g ω / w ω) (μ := μ)).mono
      intro ω hω
      exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
        (by simpa [Real.enorm_eq_ofReal_abs] using hω.trans h)
    calc
      _ = ∫⁻ ω, (F * k) ω ∂ν := by
        congr 1
        funext ω
        exact ENNReal.ofReal_mul' (inv_nonneg.mpr (hp ω).le)
      _ = ∫⁻ ω, (G * k) ω ∂ν := pull
      _ ≤ ∫⁻ _ , ENNReal.ofReal B ∂ν := by
        apply lintegral_mono_ae (ae_mono Measure.restrict_le_self ?_)
        filter_upwards [hpoint] with ω hω
        exact (ENNReal.ofReal_mul' (inv_nonneg.mpr (hp ω).le)).ge.trans hω
      _ = _ := by simp [ν]
  · intro h
    let z ω := f ω / w ω
    have zm : Measurable[m] z := hf.div (hw.mono hs le_rfl)
    have zn ω : 0 ≤ z ω := div_nonneg (hn ω) (hp ω).le
    have zi : Integrable z μ := by
      refine ⟨zm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all μ zn)).2 ?_⟩
      have hu := h univ MeasurableSet.univ
      rw [Measure.restrict_univ] at hu
      exact hu.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
    have wz : w * z = f := funext fun ω =>
      mul_div_cancel₀ _ (hp ω).ne'
    have eq := condExp_mul_of_stronglyMeasurable_left (μ := μ) hw.stronglyMeasurable
      (show Integrable (w * z) μ by rw [wz]; exact hi) zi
    rw [wz] at eq
    have point : (fun ω => g ω / w ω) =ᵐ[μ] μ[z|s] := by
      filter_upwards [eq] with ω hω
      change g ω = w ω * (μ[z|s]) ω at hω
      rw [hω, mul_div_cancel_left₀ _ (hp ω).ne']
    exact (eLpNorm_congr_ae point).le.trans
      (@condExp_bound_of_event_tests Ω m s hs μ _ z zm zn _ ENNReal.ofReal_lt_top h)


/-- Turn localized Lᵖ estimates into a conditional comparison of p-th moments. -/
theorem condExp_rpow_le_of_event_norms {Ω : Type*} [m : MeasurableSpace Ω]
    {s : MeasurableSpace Ω} (hs : s ≤ m) (μ : @Measure Ω m) [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (fm : Measurable[m] f) (fn : ∀ ω, 0 ≤ f ω) (gn : ∀ ω, 0 ≤ g ω)
    {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (gi : Integrable (fun ω => g ω ^ p) μ)
    (h : ∀ E : Set Ω, MeasurableSet[s] E →
      eLpNorm f (ENNReal.ofReal p) (μ.restrict E) ≤
        ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) (μ.restrict E)) :
    μ[fun ω => f ω ^ p | s] ≤ᵐ[μ] μ[fun ω => C ^ p * g ω ^ p | s] := by
  let F ω := f ω ^ p
  let G ω := g ω ^ p
  have Gn ω : 0 ≤ G ω := Real.rpow_nonneg (gn ω) _
  have Fn ω : 0 ≤ F ω := Real.rpow_nonneg (fn ω) _
  have gi' : Integrable (fun ω => C ^ p * G ω) μ := gi.const_mul _
  have tests E (hE : MeasurableSet[s] E) :
      (∫⁻ ω in E, ENNReal.ofReal (F ω) ∂μ) ≤
        ∫⁻ ω in E, ENNReal.ofReal (C ^ p * G ω) ∂μ := by
    have eq (v : Ω → ℝ) (vn : ∀ ω, 0 ≤ v ω) :
        eLpNorm v (ENNReal.ofReal p) (μ.restrict E) ^ p =
          ∫⁻ ω in E, ENNReal.ofReal (v ω ^ p) ∂μ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
      congr 1
      funext ω
      rw [Real.enorm_of_nonneg (vn ω), ENNReal.ofReal_rpow_of_nonneg (vn ω) hp.le]
    have raised := ENNReal.rpow_le_rpow (h E hE) hp.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, eq f fn, eq g gn, ENNReal.ofReal_rpow_of_nonneg hC hp.le,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at raised
    simpa only [F, G, ENNReal.ofReal_mul (Real.rpow_nonneg hC p)] using raised
  have fi : Integrable F μ := by
    refine ⟨(fm.pow_const p).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all μ Fn)).2 ?_⟩
    have hu := tests univ MeasurableSet.univ
    simp only [Measure.restrict_univ] at hu
    exact hu.trans_lt ((hasFiniteIntegral_iff_ofReal
      (ae_of_all μ fun ω => mul_nonneg (Real.rpow_nonneg hC p) (Gn ω))).1 gi'.2)
  let u : Ω → ℝ := μ[F|s]
  let v : Ω → ℝ := μ[fun ω => C ^ p * G ω|s]
  have huv : u ≤ᵐ[μ.trim hs] v := by
    apply ae_le_of_forall_setIntegral_le
      (integrable_condExp.trim hs stronglyMeasurable_condExp)
      (integrable_condExp.trim hs stronglyMeasurable_condExp)
    intro E hE _
    rw [← setIntegral_trim hs stronglyMeasurable_condExp hE,
      ← setIntegral_trim hs stronglyMeasurable_condExp hE,
      setIntegral_condExp hs fi hE, setIntegral_condExp hs gi' hE]
    have ht := tests E hE
    rw [← ofReal_integral_eq_lintegral_ofReal fi.restrict (ae_of_all _ Fn),
      ← ofReal_integral_eq_lintegral_ofReal gi'.restrict (ae_of_all _ fun ω =>
        mul_nonneg (Real.rpow_nonneg hC p) (Gn ω))] at ht
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω =>
      mul_nonneg (Real.rpow_nonneg hC p) (Gn ω))).1 ht
  exact ae_le_of_ae_le_trim huv

end WeightedBMO
