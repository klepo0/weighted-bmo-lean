import WeightedBMO.SupermartingaleLift
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

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


end WeightedBMO
