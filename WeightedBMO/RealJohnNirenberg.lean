import WeightedBMO.RealFirstCrossing

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

/-- Stopped increments tested on events at the first stopping time.
The denominator is the running maximum of the weight between both stops. -/
def StoppedOscillationBound {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℝ m) (v vLeft φ : Ω → ℝ → ℝ) (r T c : ℝ) :=
  ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
    (∀ ω, r ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
    ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
      (∫⁻ ω in G, ENNReal.ofReal (|v ω (U ω) - vLeft ω (S ω)| /
        intervalSup (φ ω) (S ω) (U ω)) ∂μ) ≤ ENNReal.ofReal c * μ G

private theorem crossing_jump {v vLeft φ : ℝ → ℝ} {r T a b : ℝ} (hr : r ≤ T)
    (ha : 0 < a) (hb : 0 < b) (hp : ∀ u ∈ Icc r T, 0 < φ u)
    (hw : BddAbove (φ '' Icc r T))
    (hl : ∀ u ∈ Ioc r T, Tendsto v (𝓝[<] u) (𝓝 (vLeft u)))
    (f : ℝ → ℝ) (hf : ∀ u, f u = |v u - v r| / intervalSup φ r u)
    (hc : ∀ u ∈ Ico r T, ContinuousWithinAt f (Ici u) u)
    (hit : ∃ u ∈ Icc r T, a+b < f u) :
    let S := crossingTime f r T a
    let U := crossingTime f r T (a+b)
    b ≤ |v U - vLeft S| / intervalSup φ S U := by
  let S := crossingTime f r T a
  let U := crossingTime f r T (a+b)
  have hS : S ∈ Icc r T := crossingTime_mem hr
  have hU : U ∈ Icc r T := crossingTime_mem hr
  have hSU : S ≤ U := crossingTime_mono hr (by linarith)
  have wpos (u : ℝ) (hu : u ∈ Icc r T) : 0 < intervalSup φ r u :=
    (hp r (left_mem_Icc.mpr hr)).trans_le (le_intervalSup (hw.mono (image_mono (Icc_subset_Icc le_rfl hu.2)))
      (left_mem_Icc.mpr hu.1))
  have haS : a ≤ f S := threshold_le_at_crossing hr hc (by
    obtain ⟨u,hu,h⟩ := hit; exact ⟨u,hu,by linarith⟩)
  have hrS : r < S := lt_of_le_of_ne hS.1 (by
    intro heq; rw [← heq,hf] at haS; simp at haS; linarith)
  have before : |vLeft S - v r| ≤ a * intervalSup φ r U := by
    apply le_of_tendsto ((hl S ⟨hrS,hS.2⟩).sub_const (v r)).abs
    filter_upwards [Ioo_mem_nhdsLT hrS] with x hx
    have hxT : x ∈ Icc r T := ⟨hx.1.le,hx.2.le.trans hS.2⟩
    have hx' := le_threshold_before_crossing (b := a) hr hxT hx.2
    rw [hf, div_le_iff₀ (wpos x hxT)] at hx'
    exact hx'.trans (mul_le_mul_of_nonneg_left (weight_mono le_rfl hxT.1 (hx.2.le.trans hSU)
      (hw.mono (image_mono (Icc_subset_Icc le_rfl hU.2)))) ha.le)
  have after := threshold_le_at_crossing hr hc hit
  change a+b ≤ f U at after
  rw [hf,le_div_iff₀ (wpos U hU)] at after
  have hD := hw.mono (image_mono (Icc_subset_Icc hS.1 hU.2))
  have hDpos := (hp S hS).trans_le (le_intervalSup hD (left_mem_Icc.mpr hSU))
  apply (le_div_iff₀ hDpos).2
  have wd := weight_mono hS.1 hSU le_rfl (hw.mono (image_mono (Icc_subset_Icc le_rfl hU.2)))
  have triangle := abs_sub_le (v U) (vLeft S) (v r)
  nlinarith [mul_le_mul_of_nonneg_left wd hb.le]


/-- Continuous-time `est.jnweight2`, tested on any event at the start of the interval. -/
theorem real_interval_moments {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℝ m) (hℱ : RightContinuousFiltration ℱ)
    (v vLeft φ : Ω → ℝ → ℝ) {r T c p : ℝ} (hr : r ≤ T) (hcap : 0 < c) (hp : 0 < p)
    (hv : ∀ ω, BddAbove ((fun u => |v ω u|) '' Icc r T))
    (hw : ∀ ω, BddAbove (φ ω '' Icc r T)) (hφ : ∀ ω u, u ∈ Icc r T → 0 < φ ω u)
    (mv : ∀ u ∈ Icc r T, Measurable[ℱ u] (fun ω => v ω u))
    (mw : ∀ u ∈ Icc r T, Measurable[ℱ u] (fun ω => φ ω u))
    (cv : ∀ ω u, u ∈ Ico r T → ContinuousWithinAt (v ω) (Ici u) u)
    (cw : ∀ ω u, u ∈ Ico r T → ContinuousWithinAt (φ ω) (Ici u) u)
    (hl : ∀ ω u, u ∈ Ioc r T → Tendsto (v ω) (𝓝[<] u) (𝓝 (vLeft ω u)))
    (hmean : StoppedOscillationBound μ ℱ v vLeft φ r T c)
    {E : Set Ω} (hE : MeasurableSet[ℱ r] E) :
    eLpNorm (fun ω => normalizedMaximum (v ω) (φ ω) r T / c) (ENNReal.ofReal p) (μ.restrict E) ≤
      ENNReal.ofReal (goodLambdaConstant p) *
        eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal p) (μ.restrict E) := by
  let f (ω : Ω) (u : ℝ) := |v ω u - v ω r| / intervalSup (φ ω) r u
  have bound ω : BddAbove (f ω '' Icc r T) := ratio_bounded (hφ ω r (left_mem_Icc.mpr hr)) (hv ω) (hw ω)
  have fm u (hu : u ∈ Icc r T) : Measurable[ℱ u] (fun ω => f ω u) := by
    apply (continuous_abs.measurable.comp ((mv u hu).sub
      ((mv r (left_mem_Icc.mpr hr)).mono (ℱ.mono hu.1) le_rfl))).div
    exact @measurable_intervalSup Ω (ℱ u) φ r u hu.1
      (fun ω => (hw ω).mono (image_mono (Icc_subset_Icc le_rfl hu.2)))
      (fun x hx => (mw x ⟨hx.1,hx.2.trans hu.2⟩).mono (ℱ.mono hx.2) le_rfl)
      (fun ω x hx => cw ω x ⟨hx.1,hx.2.trans_le hu.2⟩)
  have fc ω u (hu : u ∈ Ico r T) : ContinuousWithinAt (f ω) (Ici u) u := by
    apply ((cv ω u hu).sub continuousWithinAt_const).abs.div
      (continuousWithinAt_runningSup hu.1 hu.2 (hw ω) (cw ω u hu))
    exact ((hφ ω r (left_mem_Icc.mpr hr)).trans_le (le_intervalSup
      ((hw ω).mono (image_mono (Icc_subset_Icc le_rfl hu.2.le))) (left_mem_Icc.mpr hu.1))).ne'
  let Z ω := intervalSup (f ω) r T
  have zm : Measurable Z := measurable_intervalSup hr bound (fun u hu => (fm u hu).mono (ℱ.le u) le_rfl) fc
  apply goodLambda_eLpNorm_le (μ.restrict E) measurable_const (zm.div_const c) (fun _ => zero_le_one)
    (fun ω => div_nonneg (normalizedMaximum_nonneg hr (hφ ω r (left_mem_Icc.mpr hr)) (hv ω) (hw ω)) hcap.le) hp
  intro a b θ ha hb hθ _
  by_cases ht : θ*b < 1
  · simpa [ht] using (show (μ.restrict E) {ω | a+b < Z ω / c} ≤
        ENNReal.ofReal θ * (μ.restrict E) {ω | a < Z ω / c} + (μ.restrict E) univ from
      (measure_mono (subset_univ _)).trans (le_add_self))
  let S ω := crossingTime (f ω) r T (a*c)
  let U ω := crossingTime (f ω) r T (a*c+b*c)
  have hS : IsStoppingTime ℱ S := isStoppingTime_crossingTime ℱ hℱ hr _ fm fc
  have hU : IsStoppingTime ℱ U := isStoppingTime_crossingTime ℱ hℱ hr _ fm fc
  let H := {ω | a*c < Z ω}
  let B := {ω | (a+b)*c < Z ω}
  have hH : MeasurableSet[hS.measurableSpace] H := measurableSet_crossing_hit ℱ hr bound fm fc hS
  have hB : MeasurableSet B := measurableSet_lt measurable_const zm
  have hsub : B ∩ E ⊆ H ∩ E := fun ω h => ⟨(by
    have hh : (a+b)*c < Z ω := h.1
    change a*c < Z ω
    nlinarith [mul_pos hb hcap]),h.2⟩
  have hSr ω : r ≤ S ω := (crossingTime_mem hr).1
  have hSU ω : S ω ≤ U ω := crossingTime_mono hr (by nlinarith [mul_pos hb hcap])
  let J ω := |v ω (U ω) - vLeft ω (S ω)| / intervalSup (φ ω) (S ω) (U ω)
  have hj ω (h : ω ∈ B) : b*c ≤ J ω := by
    have hh : a*c+b*c < Z ω := by simpa [B,add_mul] using h
    obtain ⟨_,⟨u,hu,rfl⟩,hfu⟩ := (lt_csSup_iff (bound ω) ((nonempty_Icc.mpr hr).image _)).1 hh
    exact crossing_jump hr (mul_pos ha hcap) (mul_pos hb hcap) (hφ ω) (hw ω) (hl ω)
      (f ω) (fun _ => rfl) (fc ω) ⟨u,hu,hfu⟩
  have hInt := hmean S U hS hU hSr hSU (fun ω => (crossingTime_mem hr).2) (H ∩ E)
    (hH.inter ((hS.le_measurableSpace_of_const_le hSr) _ hE))
  have htest : ENNReal.ofReal (b*c) * μ (B ∩ E) ≤ ENNReal.ofReal c * μ (H ∩ E) := calc
    _ = ∫⁻ _ in B ∩ E, ENNReal.ofReal (b*c) ∂μ := by simp
    _ ≤ ∫⁻ ω in B ∩ E, ENNReal.ofReal (J ω) ∂μ :=
      lintegral_mono_ae ((ae_restrict_iff' (hB.inter (ℱ.le _ _ hE))).2
        (ae_of_all μ fun ω h => ENNReal.ofReal_le_ofReal (hj ω h.1)))
    _ ≤ _ := (lintegral_mono_set hsub).trans hInt
  have hscaled := mul_le_mul_left' htest (ENNReal.ofReal (1/(b*c)))
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel (mul_ne_zero hb.ne' hcap.ne'),
    ENNReal.ofReal_one,one_mul] at hscaled
  have hfactor : 1/(b*c)*c ≤ θ := by
    rw [show 1/(b*c)*c = 1/b by field_simp; ring]
    exact (div_le_iff₀ hb).2 (le_of_not_gt ht)
  have hfinal := hscaled.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hfactor) _)
  have eqB : {ω | a+b < Z ω / c} = B := Set.ext fun _ => lt_div_iff₀ hcap
  have eqH : {ω | a < Z ω / c} = H := Set.ext fun _ => lt_div_iff₀ hcap
  change (μ.restrict E) {ω | a+b < Z ω / c} ≤ ENNReal.ofReal θ * (μ.restrict E) {ω | a < Z ω / c} + _
  rw [eqB,eqH,Measure.restrict_apply hB,Measure.restrict_apply (hS.measurableSpace_le _ hH)]
  exact hfinal.trans le_self_add


/-- Continuous-time `ineq.JNweighted` as a moment comparison on each initial event. -/
theorem real_weighted_maximal_moments {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℝ m) (hℱ : RightContinuousFiltration ℱ)
    (v vLeft φ : Ω → ℝ → ℝ) {r T c p : ℝ} (hr : r ≤ T) (hc : 0 ≤ c) (hp : 0 < p)
    (hv : ∀ ω, BddAbove ((fun u => |v ω u|) '' Icc r T))
    (hw : ∀ ω, BddAbove (φ ω '' Icc r T)) (hφ : ∀ ω u, u ∈ Icc r T → 0 < φ ω u)
    (mv : ∀ u ∈ Icc r T, Measurable[ℱ u] (fun ω => v ω u))
    (mw : ∀ u ∈ Icc r T, Measurable[ℱ u] (fun ω => φ ω u))
    (cv : ∀ ω u, u ∈ Ico r T → ContinuousWithinAt (v ω) (Ici u) u)
    (cw : ∀ ω u, u ∈ Ico r T → ContinuousWithinAt (φ ω) (Ici u) u)
    (hl : ∀ ω u, u ∈ Ioc r T → Tendsto (v ω) (𝓝[<] u) (𝓝 (vLeft ω u)))
    (hmean : StoppedOscillationBound μ ℱ v vLeft φ r T c)
    {E : Set Ω} (hE : MeasurableSet[ℱ r] E) :
    eLpNorm (fun ω => intervalSup (fun u => |v ω u - v ω r|) r T) (ENNReal.ofReal p)
        (μ.restrict E) ≤
      ENNReal.ofReal (goodLambdaConstant p * c) *
        eLpNorm (fun ω => intervalSup (φ ω) r T) (ENNReal.ofReal p) (μ.restrict E) := by
  let f (ω : Ω) (u : ℝ) := |v ω u - v ω r|
  let Y ω := intervalSup (f ω) r T
  let W ω := intervalSup (φ ω) r T
  have fBound ω : BddAbove (f ω '' Icc r T) := by
    obtain ⟨d,hd⟩ := hv ω
    refine ⟨d + |v ω r|,?_⟩
    rintro _ ⟨u,hu,rfl⟩
    exact (abs_sub _ _).trans (add_le_add_right (hd (mem_image_of_mem _ hu)) _)
  have fMeas u (hu : u ∈ Icc r T) : Measurable[ℱ u] (fun ω => f ω u) :=
    continuous_abs.measurable.comp ((mv u hu).sub
      ((mv r (left_mem_Icc.mpr hr)).mono (ℱ.mono hu.1) le_rfl))
  have fRight ω u (hu : u ∈ Ico r T) : ContinuousWithinAt (f ω) (Ici u) u :=
    ((cv ω u hu).sub continuousWithinAt_const).abs
  have ym : Measurable Y :=
    measurable_intervalSup hr fBound (fun u hu => (fMeas u hu).mono (ℱ.le u) le_rfl) fRight
  have wm : Measurable W :=
    measurable_intervalSup hr hw (fun u hu => (mw u hu).mono (ℱ.le u) le_rfl) cw
  have wp ω : 0 < W ω := (hφ ω r (left_mem_Icc.mpr hr)).trans_le
    (le_intervalSup (hw ω) (left_mem_Icc.mpr hr))
  have yn ω : 0 ≤ Y ω := (abs_nonneg _).trans (le_intervalSup (fBound ω) (left_mem_Icc.mpr hr))
  have hnorm := goodLambda_eLpNorm_le (μ.restrict E) (measurable_const.mul wm) ym
    (fun ω => mul_nonneg hc (wp ω).le) yn hp
  have htail : ∀ a b θ : ℝ, 0 < a → 0 < b → 0 < θ → θ < 1 →
      (μ.restrict E) {ω | a+b < Y ω} ≤ ENNReal.ofReal θ * (μ.restrict E) {ω | a < Y ω} +
        (μ.restrict E) {ω | θ*b < c * W ω} := by
    intro a b θ ha hb hθ _
    let S ω := crossingTime (f ω) r T a
    let U ω := crossingTime (f ω) r T (a+b)
    have hS : IsStoppingTime ℱ S := isStoppingTime_crossingTime ℱ hℱ hr _ fMeas fRight
    have hU : IsStoppingTime ℱ U := isStoppingTime_crossingTime ℱ hℱ hr _ fMeas fRight
    let H := {ω | a < Y ω}
    let B := {ω | a+b < Y ω ∧ c * W ω ≤ θ*b}
    have hH : MeasurableSet[hS.measurableSpace] H :=
      measurableSet_crossing_hit ℱ hr fBound fMeas fRight hS
    have hB : MeasurableSet B := (measurableSet_lt measurable_const ym).inter
      (measurableSet_le (measurable_const.mul wm) measurable_const)
    have sub : B ∩ E ⊆ H ∩ E := fun ω h => ⟨(lt_add_of_pos_right a hb).trans h.1.1,h.2⟩
    have hSr ω : r ≤ S ω := (crossingTime_mem hr).1
    have hSU ω : S ω ≤ U ω := crossingTime_mono hr (le_add_of_nonneg_right hb.le)
    have hUT ω : U ω ≤ T := (crossingTime_mem hr).2
    let J ω := |v ω (U ω) - vLeft ω (S ω)| / intervalSup (φ ω) (S ω) (U ω)
    have lower ω (h : ω ∈ B) : b / W ω ≤ J ω := by
      obtain ⟨_,⟨u,hu,rfl⟩,hfu⟩ := (lt_csSup_iff (fBound ω) ((nonempty_Icc.mpr hr).image _)).1 h.1
      have start : a ≤ f ω (S ω) := threshold_le_at_crossing hr (fRight ω)
        ⟨u,hu,(lt_add_of_pos_right a hb).trans hfu⟩
      have hrs : r < S ω := lt_of_le_of_ne (hSr ω) (by
        intro eq
        rw [← eq] at start
        simp [f, not_le_of_gt ha] at start)
      have before : |vLeft ω (S ω) - v ω r| ≤ a := by
        apply le_of_tendsto ((hl ω (S ω) ⟨hrs,(hSU ω).trans (hUT ω)⟩).sub_const (v ω r)).abs
        filter_upwards [Ioo_mem_nhdsLT hrs] with x hx
        exact le_threshold_before_crossing (f := f ω) hr ⟨hx.1.le,hx.2.le.trans ((hSU ω).trans (hUT ω))⟩ hx.2
      have after : a+b ≤ f ω (U ω) :=
        threshold_le_at_crossing hr (fRight ω) ⟨u,hu,hfu⟩
      have jump : b ≤ |v ω (U ω) - vLeft ω (S ω)| := by
        have triangle := abs_sub_le (v ω (U ω)) (vLeft ω (S ω)) (v ω r)
        dsimp [f] at after
        linarith
      have dp := (hφ ω _ ⟨hSr ω,(hSU ω).trans (hUT ω)⟩).trans_le
        (le_intervalSup ((hw ω).mono (image_mono (Icc_subset_Icc (hSr ω) (hUT ω))))
          (left_mem_Icc.mpr (hSU ω)))
      exact (div_le_div_of_nonneg_left hb.le dp
        (weight_mono (hSr ω) (hSU ω) (hUT ω) (hw ω))).trans (div_le_div_of_nonneg_right jump dp.le)
    have hInt := hmean S U hS hU hSr hSU hUT (H ∩ E)
      (hH.inter ((hS.le_measurableSpace_of_const_le hSr) _ hE))
    rw [← Measure.restrict_apply (hS.measurableSpace_le _ hH)] at hInt
    have hBE := hB.inter (ℱ.le _ _ hE)
    have test {g : Ω → ℝ≥0∞} (hg : ∀ ω ∈ B, g ω ≤ ENNReal.ofReal (J ω)) :
        (∫⁻ ω in B ∩ E, g ω ∂μ) ≤ ENNReal.ofReal c * (μ.restrict E) H :=
      (lintegral_mono_ae ((ae_restrict_iff' hBE).2 (ae_of_all μ fun ω h => hg ω h.1))).trans
        ((lintegral_mono_set sub).trans hInt)
    have small : (μ.restrict E) B ≤ ENNReal.ofReal θ * (μ.restrict E) H := by
      rcases hc.eq_or_lt with hc0 | hcp
      · have htest := test (fun ω h => ENNReal.ofReal_le_ofReal (lower ω h))
        simp only [← hc0, ENNReal.ofReal_zero, zero_mul] at htest
        have eq := le_antisymm htest (zero_le _)
        have ae := (lintegral_eq_zero_iff (wm.const_div b).ennreal_ofReal).1 eq
        have null := (ae_restrict_iff' hBE).1 ae
        have outside : ∀ᵐ ω ∂μ, ω ∉ B ∩ E := by
          filter_upwards [null] with ω h hn
          exact (ENNReal.ofReal_pos.mpr (div_pos hb (wp ω))).ne' (h hn)
        have hnull : μ (B ∩ E) = 0 := by simpa [ae_iff] using outside
        simp [Measure.restrict_apply hB, hnull]
      · have htest := test (g := fun _ => ENNReal.ofReal (c/θ)) fun ω h =>
          ENNReal.ofReal_le_ofReal (((div_le_div_iff₀ hθ (wp ω)).2 (by simpa [mul_comm θ b] using h.2)).trans (lower ω h))
        simp only [lintegral_const, Measure.restrict_apply_univ, ← Measure.restrict_apply hB] at htest
        have scaled := mul_le_mul_left' htest (ENNReal.ofReal (θ/c))
        rwa [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), show θ/c*(c/θ) = 1 by field_simp,
          div_mul_cancel₀ _ hcp.ne', ENNReal.ofReal_one, one_mul] at scaled
    have cover : {ω | a+b < Y ω} ⊆ B ∪ {ω | θ*b < c * W ω} := by
      intro ω h
      by_cases hw' : c * W ω ≤ θ*b
      · exact Or.inl ⟨h,hw'⟩
      · exact Or.inr (lt_of_not_ge hw')
    exact (measure_mono cover).trans ((measure_union_le _ _).trans (add_le_add_right small _))
  have result := hnorm htail
  rwa [show (fun ω => c * W ω) = c • W from rfl, eLpNorm_const_smul,
    Real.enorm_of_nonneg hc, ← mul_assoc, ← ENNReal.ofReal_mul (by unfold goodLambdaConstant; positivity)] at result

end WeightedBMO
