import WeightedBMO.SupermartingaleLift
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import WeightedBMO.EstSmaximal

set_option maxHeartbeats 2000000

/-!
# Towards Kuhn's `L^p` maximal inequality for `p < 1`

For a nonnegative supermartingale `N` on `[0,T]` and `0 < p < 1`, Kuhn's lemma
(used as `est.Smax01` in arXiv:2211.15550v3, cited there as
[kuhn2022maximal, Lemma 2.22]) states

  `‖sup_{t≤T} N_t‖_p ≤ (1-p)^{-1/p} ‖N_0‖_p`.

The *global* weak-type inequality `α μ{sup N > α} ≤ ∫ N_0` is not enough for
this sharp constant: the resulting layer-cake integral diverges at the origin.
What is needed is the event-tested form, tested on events known at time `0`,
which `SupermartingaleLift.supermartingale_max_le_supOn_of_measurableSet_zero`
supplies.  In conditional form it reads `α μ{sup N > α | ℱ 0} ≤ N_0` a.e., and
then the sharp constant comes from the elementary pointwise computation

  `∫_0^∞ t^{p-1} min (1, c/t) dt = c^p / (p (1-p))`.

This file contains the two ingredients that are proved:

* `lintegral_min_mul_rpow`: the one-variable integral above, evaluated in
  `ℝ≥0∞` (the two pieces are `∫_0^c t^{p-1}` and `∫_c^∞ c t^{p-2}`);
* `ae_le_of_setIntegral_le`: the passage from "`g` dominates `f` in integral
  over `{g < f}`" to "`g` dominates `f` almost everywhere", which converts the
  event-tested weak-type inequality into its conditional form.

The remaining step — assembling them through the layer-cake formula
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` and Tonelli — is not yet
formalized, so `estSmax01` still takes Kuhn's lemma as a hypothesis.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open intervalIntegral

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}

/-- The one-variable computation behind Kuhn's lemma: for `0 < p < 1` and `c ≥ 0`,
`∫_0^∞ t^{p-1} min(1, c/t) dt = c^p / (p (1-p))`. -/
theorem lintegral_min_mul_rpow {p c : ℝ} (hp : 0 < p) (hp1 : p < 1) (hc : 0 ≤ c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (c ^ p / (p * (1 - p))) := by
  have hp1' : -1 < p - 1 := by linarith
  have hp2 : p - 2 < -1 := by linarith
  have hpne : p ≠ 0 := hp.ne'
  have h1mp : (0:ℝ) < 1 - p := by linarith
  rcases eq_or_lt_of_le hc with h0 | hpos
  · rw [← h0]
    have hz : (fun t : ℝ => ENNReal.ofReal (min 1 ((0:ℝ) / t)) * ENNReal.ofReal (t ^ (p - 1)))
        = fun _ => (0 : ℝ≥0∞) := by
      funext t
      rw [zero_div, min_eq_right zero_le_one, ENNReal.ofReal_zero, zero_mul]
    rw [hz]
    simp [Real.zero_rpow hpne]
  have hsplit : (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1)))
      = (∫⁻ t in Ioc (0:ℝ) c, ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1)))
        + (∫⁻ t in Ioi c, ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1))) := by
    have hdisj : Disjoint (Ioc (0:ℝ) c) (Ioi c) := by
      rw [Set.disjoint_left]
      intro x hx hy
      exact absurd hx.2 (not_le.mpr hy)
    have hun : Ioc (0:ℝ) c ∪ Ioi c = Ioi (0:ℝ) := by
      ext x
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (⟨_, h⟩ | h) <;> linarith
      · intro h
        rcases le_or_lt x c with hx | hx
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr hx
    rw [← lintegral_union (μ := volume) (f := fun t : ℝ =>
      ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1))) measurableSet_Ioi
      hdisj, hun]
  -- first piece: `min 1 (c/t) = 1`
  have hcong1 : ∫⁻ t in Ioc (0:ℝ) c, ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1))
      = ∫⁻ t in Ioc (0:ℝ) c, ENNReal.ofReal (t ^ (p - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioc (Eventually.of_forall ?_)
    intro t ht
    have h1 : min 1 (c / t) = 1 := by
      refine min_eq_left ?_
      rw [le_div_iff₀ ht.1]
      simpa using ht.2
    rw [h1, ENNReal.ofReal_one, one_mul]
  have hint1 : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Ioc 0 c) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).mp (intervalIntegrable_rpow' hp1')
  have hnn1 : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] (fun t : ℝ => t ^ (p - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hval1 : ∫⁻ t in Ioc (0:ℝ) c, ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (c ^ p / p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint1 hnn1]
    congr 1
    rw [← intervalIntegral.integral_of_le hc, integral_rpow (Or.inl hp1')]
    have he : p - 1 + 1 = p := by ring
    rw [he, Real.zero_rpow hpne, sub_zero]
  -- second piece: `min 1 (c/t) = c/t`
  have hcong2 : ∫⁻ t in Ioi (c:ℝ), ENNReal.ofReal (min 1 (c / t)) * ENNReal.ofReal (t ^ (p - 1))
      = ∫⁻ t in Ioi c, ENNReal.ofReal (c * t ^ (p - 2)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (Eventually.of_forall ?_)
    intro t ht
    have ht0 : 0 < t := hpos.trans ht
    have h2 : min 1 (c / t) = c / t := by
      refine min_eq_right ?_
      rw [div_le_iff₀ ht0]
      simpa using ht.le
    have hts : t ^ (p - 1) / t = t ^ (p - 2) := by
      have h := Real.rpow_sub ht0 (p - 1) (1:ℝ)
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    rw [h2, ← ENNReal.ofReal_mul (div_nonneg hc ht0.le)]
    congr 1
    calc c / t * t ^ (p - 1) = c * (t ^ (p - 1) / t) := by ring
      _ = c * t ^ (p - 2) := by rw [hts]
  have hint2 : IntegrableOn (fun t : ℝ => c * t ^ (p - 2)) (Ioi c) volume :=
    (integrableOn_Ioi_rpow_of_lt hp2 hpos).const_mul c
  have hnn2 : 0 ≤ᵐ[volume.restrict (Ioi c)] (fun t : ℝ => c * t ^ (p - 2)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg hc (Real.rpow_nonneg (hpos.trans ht).le _)
  have hval2 : ∫⁻ t in Ioi (c:ℝ), ENNReal.ofReal (c * t ^ (p - 2)) =
      ENNReal.ofReal (c ^ p / (1 - p)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint2 hnn2]
    congr 1
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hp2 hpos]
    have he : p - 2 + 1 = p - 1 := by ring
    rw [he]
    have hcp : c * c ^ (p - 1) = c ^ p := by
      have := Real.rpow_add hpos (1:ℝ) (p - 1)
      rw [Real.rpow_one] at this
      rw [← this]; ring_nf
    have step : c * (-c ^ (p - 1) / (p - 1)) = -(c * c ^ (p - 1)) / (p - 1) := by ring
    rw [step, hcp, div_eq_div_iff (by linarith : (p - 1) ≠ 0) h1mp.ne']
    ring
  rw [hsplit, hcong1, hcong2, hval1, hval2,
    ← ENNReal.ofReal_add (div_nonneg (Real.rpow_nonneg hc p) hp.le)
      (div_nonneg (Real.rpow_nonneg hc p) h1mp.le)]
  congr 1
  field_simp
  ring


/-- If `g` dominates `f` in integral over the set `{g < f}`, it dominates `f` a.e. -/
theorem ae_le_of_setIntegral_le {f g : Ω → ℝ}
    (hS : MeasurableSet[m] {ω | g ω < f ω})
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (h : ∫ ω in {ω | g ω < f ω}, f ω ∂μ ≤ ∫ ω in {ω | g ω < f ω}, g ω ∂μ) :
    f ≤ᵐ[μ] g := by
  have hle : ∫ ω in {ω | g ω < f ω}, (f ω - g ω) ∂μ ≤ 0 := by
    rw [integral_sub hfi.integrableOn hgi.integrableOn]
    linarith
  have hge : 0 ≤ ∫ ω in {ω | g ω < f ω}, (f ω - g ω) ∂μ :=
    setIntegral_nonneg hS (fun ω hω => by simp only [mem_setOf_eq] at hω; linarith)
  have hzero : ∫ ω in {ω | g ω < f ω}, (f ω - g ω) ∂μ = 0 := le_antisymm hle hge
  have hnn : 0 ≤ᵐ[μ.restrict {ω | g ω < f ω}] (fun ω => f ω - g ω) := by
    filter_upwards [ae_restrict_mem hS] with ω hω
    show (0:ℝ) ≤ f ω - g ω
    linarith
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hnn
    (hfi.integrableOn.sub hgi.integrableOn)).1 hzero
  have hpos : ∀ᵐ ω ∂μ.restrict {ω | g ω < f ω}, (0:ℝ) < f ω - g ω := by
    filter_upwards [ae_restrict_mem hS] with ω hω
    linarith
  have hfalse : ∀ᵐ ω ∂μ.restrict {ω | g ω < f ω}, False := by
    filter_upwards [hz, hpos] with ω h1 h2
    simp only [Pi.zero_apply] at h1
    linarith
  have hmeas0 : μ {ω | g ω < f ω} = 0 := by
    have h := (ae_iff).1 hfalse
    simp only [not_false_eq_true, setOf_true] at h
    rwa [Measure.restrict_apply_univ] at h
  have hmem : ∀ᵐ ω ∂μ, ω ∉ {ω | g ω < f ω} := measure_zero_iff_ae_nmem.mp hmeas0
  filter_upwards [hmem] with ω hω
  simp only [mem_setOf_eq, not_lt] at hω
  exact hω

/-- **Kuhn's truncation.**  If the event-tested weak-type inequality
`α μ({α < Y} ∩ G) ≤ ∫_G Z` holds for every `α > 0` and every `𝒢`-measurable `G`,
then for `0 < q < 1` the `q`-th moments satisfy `∫ Y^q ≤ (1-q)^{-1} ∫ Z^q`.

The proof conditions on `𝒢`: the weak-type inequality is equivalent to
`α μ{α < Y | 𝒢} ≤ Z`, so the tail `μ{t < Y}` is at most
`∫ min (1) (Z/t)`, and the one-variable computation `lintegral_min_mul_rpow`
then gives the sharp constant. -/
theorem lintegral_rpow_le_of_weak [IsProbabilityMeasure μ]
    {Y Z : Ω → ℝ} {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hYm : @Measurable Ω ℝ m _ Y)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZm : @Measurable Ω ℝ m _ Z) (hZint : Integrable Z μ)
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ m) (hZ𝒢 : @Measurable Ω ℝ 𝒢 _ Z)
    (hweak : ∀ (α : ℝ), 0 < α → ∀ G : Set Ω, @MeasurableSet Ω 𝒢 G →
      ENNReal.ofReal α * μ ({ω | α < Y ω} ∩ G) ≤ ENNReal.ofReal (∫ ω in G, Z ω ∂μ)) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤
      ENNReal.ofReal (1 / (1 - q)) * ∫⁻ ω, ENNReal.ofReal (Z ω ^ q) ∂μ := by
  letI : MeasurableSpace Ω := m
  have h1q : (0:ℝ) < 1 - q := by linarith
  have hbound : ∀ t : ℝ, 0 < t →
      μ {ω | t < Y ω} ≤ ∫⁻ ω, ENNReal.ofReal (min 1 (Z ω / t)) ∂μ := by
    intro t ht
    classical
    have hA : MeasurableSet {ω | t < Y ω} := hYm measurableSet_Ioi
    set f : Ω → ℝ := μ[({ω | t < Y ω}).indicator (fun _ => (1:ℝ)) | 𝒢] with hf
    have hind_int : Integrable (({ω | t < Y ω}).indicator (fun _ => (1:ℝ))) μ :=
      Integrable.indicator (integrable_const (1:ℝ)) hA
    have hfmeas : @Measurable Ω ℝ 𝒢 _ f := stronglyMeasurable_condExp.measurable
    have hfint : Integrable f μ := by rw [hf]; exact integrable_condExp
    have hind_le : ∀ ω, ({ω | t < Y ω}).indicator (fun _ => (1:ℝ)) ω ≤ 1 := by
      intro ω
      by_cases hω : ω ∈ {ω | t < Y ω} <;> simp [Set.indicator_apply, hω]
    have hf1 : f ≤ᵐ[μ] fun _ => (1:ℝ) := by
      have hone : μ[(fun _ => (1:ℝ)) | 𝒢] = fun _ => (1:ℝ) :=
        condExp_of_stronglyMeasurable (μ := μ) h𝒢 stronglyMeasurable_const
          (integrable_const (1:ℝ))
      have h := condExp_mono (m := 𝒢) hind_int (integrable_const (1:ℝ))
        (Eventually.of_forall hind_le)
      filter_upwards [h] with ω h1
      simp only [hf]
      rw [hone] at h1
      exact h1
    have hS𝒢 : @MeasurableSet Ω 𝒢 {ω | Z ω < t * f ω} :=
      measurableSet_lt hZ𝒢 (hfmeas.const_mul t)
    have hS : MeasurableSet {ω | Z ω < t * f ω} := h𝒢 _ hS𝒢
    have hped : (fun ω => t * f ω) ≤ᵐ[μ] Z := by
      refine ae_le_of_setIntegral_le hS (hfint.const_mul t) hZint ?_
      have h1 : ∫ ω in {ω | Z ω < t * f ω}, f ω ∂μ
          = μ.real ({ω | Z ω < t * f ω} ∩ {ω | t < Y ω}) := by
        have hstep : ∫ ω in {ω | Z ω < t * f ω}, f ω ∂μ
            = ∫ ω in {ω | Z ω < t * f ω},
                ({ω | t < Y ω}).indicator (fun _ => (1:ℝ)) ω ∂μ := by
          simp only [hf]
          exact setIntegral_condExp h𝒢 hind_int hS𝒢
        rw [hstep, setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
          measureReal_def]
      have hset : ∫ ω in {ω | Z ω < t * f ω}, t * f ω ∂μ
          = t * μ.real ({ω | Z ω < t * f ω} ∩ {ω | t < Y ω}) := by
        rw [MeasureTheory.integral_const_mul, h1]
      have hreal : t * μ.real ({ω | Z ω < t * f ω} ∩ {ω | t < Y ω})
          ≤ ∫ ω in {ω | Z ω < t * f ω}, Z ω ∂μ := by
        have hfin : μ ({ω | t < Y ω} ∩ {ω | Z ω < t * f ω}) ≠ ⊤ := measure_ne_top _ _
        have hW := hweak t ht _ hS𝒢
        rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def, ← ENNReal.ofReal_mul ht.le] at hW
        rw [Set.inter_comm]
        exact (ENNReal.ofReal_le_ofReal_iff
          (setIntegral_nonneg hS (fun ω _ => hZ0 ω))).1 hW
      rw [hset]
      exact hreal
    have hf2 : f ≤ᵐ[μ] fun ω => Z ω / t := by
      filter_upwards [hped] with ω hω
      rw [le_div_iff₀ ht]
      linarith
    have hmin : f ≤ᵐ[μ] fun ω => min 1 (Z ω / t) := by
      filter_upwards [hf1, hf2] with ω h1 h2
      exact le_min h1 h2
    have hminint : Integrable (fun ω => min 1 (Z ω / t)) μ := by
      refine Integrable.mono' (integrable_const (1:ℝ))
        (measurable_const.min (hZm.div_const t)).aestronglyMeasurable ?_
      filter_upwards with ω
      have h0 : 0 ≤ min 1 (Z ω / t) := le_min zero_le_one (div_nonneg (hZ0 ω) ht.le)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_left _ _
    have hnn : 0 ≤ᵐ[μ] (fun ω => min 1 (Z ω / t)) :=
      Eventually.of_forall fun ω => le_min zero_le_one (div_nonneg (hZ0 ω) ht.le)
    have hle_int : ∫ ω, f ω ∂μ ≤ ∫ ω, min 1 (Z ω / t) ∂μ :=
      integral_mono_ae hfint hminint hmin
    have hfval : ∫ ω, f ω ∂μ = μ.real {ω | t < Y ω} := by
      simp only [hf]
      rw [integral_condExp h𝒢, MeasureTheory.integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_def]
    have hmu : μ {ω | t < Y ω} = ENNReal.ofReal (∫ ω, f ω ∂μ) := by
      rw [hfval]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    calc μ {ω | t < Y ω} = ENNReal.ofReal (∫ ω, f ω ∂μ) := hmu
      _ ≤ ENNReal.ofReal (∫ ω, min 1 (Z ω / t) ∂μ) := ENNReal.ofReal_le_ofReal hle_int
      _ = ∫⁻ ω, ENNReal.ofReal (min 1 (Z ω / t)) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hminint hnn
  have huncurry : AEMeasurable
      (Function.uncurry (fun t ω => ENNReal.ofReal (min 1 (Z ω / t)) *
        ENNReal.ofReal (t ^ (q - 1)))) (Measure.prod (volume.restrict (Ioi (0:ℝ))) μ) := by
    have hbase : Measurable (fun t : ℝ => t ^ (q - 1)) := by measurability
    have h1 : Measurable (fun p : ℝ × Ω => ENNReal.ofReal (min 1 (Z p.2 / p.1))) :=
      ENNReal.measurable_ofReal.comp
        (measurable_const.min ((hZm.comp measurable_snd).div measurable_fst))
    have h2 : Measurable (fun p : ℝ × Ω => ENNReal.ofReal (p.1 ^ (q - 1))) :=
      ENNReal.measurable_ofReal.comp (hbase.comp measurable_fst)
    exact (h1.mul h2).aemeasurable
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hY0) hYm.aemeasurable hq]
  have hstep : (∫⁻ t in Ioi (0:ℝ), μ {a | t < Y a} * ENNReal.ofReal (t ^ (q - 1)))
      ≤ ∫⁻ t in Ioi (0:ℝ),
          (∫⁻ ω, ENNReal.ofReal (min 1 (Z ω / t)) * ENNReal.ofReal (t ^ (q - 1)) ∂μ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [lintegral_mul_const (ENNReal.ofReal (t ^ (q - 1))) (by measurability)]
    exact mul_le_mul_right' (hbound t ht) _
  calc ENNReal.ofReal q * ∫⁻ t in Ioi (0:ℝ), μ {a | t < Y a} * ENNReal.ofReal (t ^ (q - 1))
      ≤ ENNReal.ofReal q * ∫⁻ t in Ioi (0:ℝ),
          (∫⁻ ω, ENNReal.ofReal (min 1 (Z ω / t)) * ENNReal.ofReal (t ^ (q - 1)) ∂μ) :=
        mul_le_mul_left' hstep _
    _ = ENNReal.ofReal q * (∫⁻ ω, (∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal (min 1 (Z ω / t)) * ENNReal.ofReal (t ^ (q - 1))) ∂μ) := by
        congr 1
        exact lintegral_lintegral_swap (μ := volume.restrict (Ioi (0:ℝ))) (ν := μ) huncurry
    _ = ENNReal.ofReal q * ∫⁻ ω, ENNReal.ofReal ((Z ω) ^ q / (q * (1 - q))) ∂μ := by
        congr 1
        exact lintegral_congr fun ω => lintegral_min_mul_rpow hq hq1 (hZ0 ω)
    _ = ENNReal.ofReal (1 / (1 - q)) * ∫⁻ ω, ENNReal.ofReal (Z ω ^ q) ∂μ := by
        have hqne : q ≠ 0 := hq.ne'
        have hfac : (0:ℝ) ≤ 1 / (q * (1 - q)) :=
          div_nonneg zero_le_one (mul_nonneg hq.le h1q.le)
        have hpt : ∀ ω, ENNReal.ofReal ((Z ω) ^ q / (q * (1 - q)))
            = ENNReal.ofReal ((Z ω) ^ q) * ENNReal.ofReal (1 / (q * (1 - q))) := by
          intro ω
          rw [div_eq_mul_one_div, ENNReal.ofReal_mul (Real.rpow_nonneg (hZ0 ω) q)]
        simp_rw [hpt]
        rw [lintegral_mul_const (ENNReal.ofReal (1 / (q * (1 - q)))) (by measurability)]
        rw [mul_comm (∫⁻ ω, ENNReal.ofReal (Z ω ^ q) ∂μ) (ENNReal.ofReal (1 / (q * (1 - q)))),
          ← mul_assoc, ← ENNReal.ofReal_mul hq.le]
        congr 1
        field_simp


end WeightedBMO
