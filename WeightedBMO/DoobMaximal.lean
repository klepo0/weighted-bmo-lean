import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Doob's `L^p` maximal inequality

Mathlib has Doob's weak-type `(1,1)` maximal inequality
(`MeasureTheory.maximal_ineq`) but not its `L^p` consequence. The weighted
BMO estimates of Khoa Lê, *Maximal inequalities, weighted BMO processes and the largest-jump normaliser*,
arXiv:2211.15550, use the `L^p` form with the sharp constant `m/(m-1)` to
deduce Theorem 1.1 from the John--Nirenberg inequality `ineq.JNweighted`.

For a nonnegative submartingale `f` on a finite measure space we prove

* `submartingale_weak_type`: the weak-type bound,
* `submartingale_moment_maximal_le`: `∫ (max_{k ≤ n} f k)^p ≤ (p/(p-1))^p ∫ f n^p`,
* `submartingale_eLpNorm_maximal_le` and `martingale_eLpNorm_maximal_le`:
  the seminorm form `‖max_{k ≤ n} f k‖_p ≤ p/(p-1) ‖f n‖_p` for `p > 1`.

The proof computes the moment by layer cake, integrates the weak-type
inequality over the level parameter (Tonelli), evaluates the resulting
one-dimensional power integral, and closes with Hölder's inequality.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace WeightedBMO

/-- `NNReal` acting on `ℝ≥0∞` is multiplication by the coerced scalar. -/
private theorem nnreal_smul_ennreal (c : NNReal) (y : ℝ≥0∞) :
    (c • y : ℝ≥0∞) = (c : ℝ≥0∞) * y := by
  rw [Algebra.smul_def]; rfl

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The finite maximal function `max_{k ≤ n} f k`. -/
noncomputable def subMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_succ fun k => f k ω

theorem measurable_subMax {f : ℕ → Ω → ℝ} (h : ∀ k, Measurable (f k)) (n : ℕ) :
    Measurable (subMax f n) :=
  Finset.measurable_range_sup'' (fun k _ => h k)

omit m0 in
theorem subMax_nonneg {f : ℕ → Ω → ℝ} (hnonneg : 0 ≤ f) (n : ℕ) (ω : Ω) :
    0 ≤ subMax f n ω :=
  (hnonneg 0 ω).trans (Finset.le_sup' (f := fun k => f k ω)
    (Finset.mem_range.mpr (Nat.succ_pos n)))

/-- Doob's weak-type `(1,1)` maximal inequality, in the form used below. -/
theorem submartingale_weak_type (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ENNReal.ofReal t * μ {ω | t ≤ subMax f n ω} ≤
      ∫⁻ ω in {ω | t ≤ subMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := by
  have hm := MeasureTheory.maximal_ineq (μ := μ) hsub hnonneg (n := n) (ε := ⟨t, ht.le⟩)
  rw [nnreal_smul_ennreal, ← ENNReal.ofReal_eq_coe_nnreal ht.le] at hm
  simp only [NNReal.coe_mk] at hm
  have hconv : ENNReal.ofReal (∫ ω in {ω | t ≤ subMax f n ω}, f n ω ∂μ) =
      ∫⁻ ω in {ω | t ≤ subMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := by
    have := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := μ.restrict {ω | t ≤ subMax f n ω})
      (f := f n) (hsub.integrable n).integrableOn (ae_of_all _ (hnonneg n))
    exact this
  have hm' : ENNReal.ofReal t * μ {ω | t ≤ subMax f n ω} ≤
      ENNReal.ofReal (∫ ω in {ω | t ≤ subMax f n ω}, f n ω ∂μ) := hm
  rwa [hconv] at hm'

/-- `∫_0^c p t^{p-1} dt = c^p` for `p > 1`. It is stated for every real `c`;
for `c ≥ 0` it is the usual power integral. -/
theorem integral_rpow_sub_one {p c : ℝ} (hp : 1 < p) :
    ∫ t in (0:ℝ)..c, p * t ^ (p - 1) = c ^ p := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have h1 : (p - 1) + 1 = p := by ring
  rw [h1, Real.zero_rpow (by linarith : p ≠ 0)]
  field_simp

/-- `∫_0^c p t^{p-2} dt = (p/(p-1)) c^{p-1}` for `p > 1`, stated for every
real `c`; for `c ≥ 0` it is the usual power integral. -/
theorem integral_rpow_sub_two {p c : ℝ} (hp : 1 < p) :
    ∫ t in (0:ℝ)..c, p * t ^ (p - 2) = p / (p - 1) * c ^ (p - 1) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have h1 : (p - 2) + 1 = p - 1 := by ring
  rw [h1, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  field_simp

omit [IsFiniteMeasure μ] in
/-- Layer cake for the truncated maximal function. -/
theorem layer_cake_subMax {p : ℝ} (hp : 1 < p) (hnonneg : 0 ≤ f) (n m : ℕ)
    (hM : Measurable (subMax f n)) :
    ∫⁻ ω, ENNReal.ofReal ((min (subMax f n ω) (m:ℝ)) ^ p) ∂μ =
      ∫⁻ t in Ioi (0 : ℝ),
        μ {ω | t ≤ min (subMax f n ω) (m:ℝ)} * ENNReal.ofReal (p * t ^ (p - 1)) := by
  set Mm : Ω → ℝ := fun ω => min (subMax f n ω) (m:ℝ) with hMm
  have hMm_meas : Measurable Mm := hM.min measurable_const
  have hMm_nonneg : ∀ ω, 0 ≤ Mm ω := fun ω =>
    le_min (subMax_nonneg hnonneg n ω) (Nat.cast_nonneg m)
  have hg_int : ∀ t > 0, IntervalIntegrable (fun t => p * t ^ (p - 1)) volume 0 t :=
    fun t _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < p - 1)).const_mul p
  have hg_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ p * t ^ (p - 1) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      mul_nonneg (by linarith : (0:ℝ) ≤ p) (Real.rpow_nonneg ht.le _))
  have key := MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul (μ := μ) (f := Mm)
    (g := fun t => p * t ^ (p - 1)) (Filter.Eventually.of_forall hMm_nonneg)
    hMm_meas.aemeasurable hg_int hg_nn
  rw [show (∫⁻ t in Ioi (0:ℝ), μ {a : Ω | t ≤ Mm a} * ENNReal.ofReal (p * t ^ (p - 1)))
      = ∫⁻ t in Ioi (0:ℝ), μ {ω | t ≤ min (subMax f n ω) (m:ℝ)} *
          ENNReal.ofReal (p * t ^ (p - 1)) from rfl] at key
  rw [← key]
  apply lintegral_congr
  intro ω
  rw [integral_rpow_sub_one hp]

/-- `Ioi 0 ∩ Iic c` agrees almost everywhere with `Ioc 0 c`. -/
theorem ae_eq_Ioi_inter_Iic (c : ℝ) :
    (Ioi (0:ℝ) ∩ Iic c : Set ℝ) =ᶠ[ae volume] (Ioc 0 c) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ (by simp : volume ({c} : Set ℝ) = 0)
    rintro x ⟨⟨h1, h2⟩, h3⟩
    simp only [mem_Ioi, mem_Iic, mem_Ioc, mem_singleton_iff] at h1 h2 h3 ⊢
    rcases lt_or_eq_of_le h2 with h | h
    · exact absurd ⟨h1, le_of_lt h⟩ h3
    · exact h
  · have hsub : Ioc (0:ℝ) c ⊆ Ioi 0 ∩ Iic c := fun x hx => ⟨hx.1, hx.2⟩
    have hE : Ioc (0:ℝ) c \ (Ioi 0 ∩ Iic c) = ∅ := Set.diff_eq_empty.mpr hsub
    rw [hE]
    simp

/-- The power integral over the interval `(0, c]`, as an extended integral. -/
theorem lintegral_Iic_rpow {p : ℝ} (hp : 1 < p) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ t in Ioi (0:ℝ) ∩ Iic c, ENNReal.ofReal (p * t ^ (p - 2)) =
      ENNReal.ofReal (p / (p - 1) * c ^ (p - 1)) := by
  have hii : IntervalIntegrable (fun t : ℝ => p * t ^ (p - 2)) volume 0 c :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < p - 2)).const_mul p
  have hint : IntegrableOn (fun t : ℝ => p * t ^ (p - 2)) (Ioc 0 c) volume := by
    rw [intervalIntegrable_iff] at hii
    simpa [uIoc_of_le hc] using hii
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] fun t : ℝ => p * t ^ (p - 2) :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
      mul_nonneg (by linarith : (0:ℝ) ≤ p) (Real.rpow_nonneg ht.1.le _))
  rw [Measure.restrict_congr_set (ae_eq_Ioi_inter_Iic c),
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hc, integral_rpow_sub_two hp]

/-- Pointwise comparison of the layer-cake integrands against the weak-type bound. -/
theorem integrand_le (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {p : ℝ} (_hp : 1 < p)
    (n m : ℕ) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ min (subMax f n ω) (m:ℝ)} * ENNReal.ofReal (p * t ^ (p - 1)) ≤
      ENNReal.ofReal (p * t ^ (p - 2)) *
        ∫⁻ ω in {ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}, ENNReal.ofReal (f n ω) ∂μ := by
  rcases le_or_lt t (m:ℝ) with htm | htm
  · have hset : {ω : Ω | t ≤ min (subMax f n ω) (m:ℝ)} = {ω | t ≤ subMax f n ω} := by
      ext ω; simp [le_min_iff, htm]
    have hset2 : ({ω : Ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}) =
        {ω | t ≤ subMax f n ω} := by
      ext ω; simp [htm]
    rw [hset, hset2]
    have hrw : t ^ (p - 1) = t * t ^ (p - 2) := by
      have h : p - 1 = (p - 2) + 1 := by ring
      rw [h, Real.rpow_add_one ht.ne']
      ring
    have hfact : ENNReal.ofReal (p * t ^ (p - 1)) =
        ENNReal.ofReal t * ENNReal.ofReal (p * t ^ (p - 2)) := by
      rw [← ENNReal.ofReal_mul (le_of_lt ht)]
      congr 1
      rw [hrw]; ring
    calc μ {ω : Ω | t ≤ subMax f n ω} * ENNReal.ofReal (p * t ^ (p - 1))
        = ENNReal.ofReal (p * t ^ (p - 2)) *
            (ENNReal.ofReal t * μ {ω : Ω | t ≤ subMax f n ω}) := by
          rw [hfact]; ring
      _ ≤ ENNReal.ofReal (p * t ^ (p - 2)) *
            ∫⁻ ω in {ω : Ω | t ≤ subMax f n ω}, ENNReal.ofReal (f n ω) ∂μ :=
          mul_le_mul_left' (submartingale_weak_type hsub hnonneg ht n) _
  · have hempty : {ω : Ω | t ≤ min (subMax f n ω) (m:ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      rintro ω hω
      simp only [mem_setOf_eq] at hω
      have hle : min (subMax f n ω) (m:ℝ) ≤ (m:ℝ) := min_le_right (subMax f n ω) (m:ℝ)
      linarith
    rw [hempty]
    simp

/-- Kernel of the double integral in the Tonelli step. -/
noncomputable def truncKernel (M : Ω → ℝ) (G : Ω → ℝ≥0∞) (m : ℕ) (p : ℝ) :
    ℝ × Ω → ℝ≥0∞ :=
  {q : ℝ × Ω | q.1 ∈ Ioi (0:ℝ) ∩ Iic (min (M q.2) (m:ℝ))}.indicator
    (fun q : ℝ × Ω => ENNReal.ofReal (p * q.1 ^ (p - 2)) * G q.2)

theorem measurable_truncKernel {M : Ω → ℝ} {G : Ω → ℝ≥0∞} (hM : Measurable M)
    (hG : Measurable G) (m : ℕ) (p : ℝ) : Measurable (truncKernel M G m p) := by
  unfold truncKernel
  refine Measurable.indicator ?_ ?_
  · exact (by measurability : Measurable fun q : ℝ × Ω => ENNReal.ofReal (p * q.1 ^ (p - 2))).mul
      (hG.comp measurable_snd)
  · have hset : {q : ℝ × Ω | q.1 ∈ Ioi (0:ℝ) ∩ Iic (min (M q.2) (m:ℝ))}
        = {q : ℝ × Ω | 0 < q.1} ∩ {q | q.1 ≤ M q.2} ∩ {q | q.1 ≤ (m:ℝ)} := by
      ext q; simp [le_min_iff, and_assoc]
    rw [hset]
    exact ((measurable_fst measurableSet_Ioi).inter
      (measurableSet_le measurable_fst (hM.comp measurable_snd))).inter
      (measurable_fst measurableSet_Iic)

/-- Tonelli step: the double integral of the weak-type bound. -/
theorem tonelli_trunc (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {p : ℝ} (hp : 1 < p)
    (n m : ℕ) (hM : Measurable (subMax f n)) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (p * t ^ (p - 2)) *
        ∫⁻ ω in {ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}, ENNReal.ofReal (f n ω) ∂μ
      = ENNReal.ofReal (p / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
          (ENNReal.ofReal (min (subMax f n ω) (m:ℝ))) ^ (p - 1) ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  have hG : Measurable (fun ω : Ω => ENNReal.ofReal (f n ω)) :=
    ((hsub.stronglyMeasurable n).measurable.mono (𝒢.le n) le_rfl).ennreal_ofReal
  have hf : Measurable (fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 2))) := by measurability
  set K : ℝ × Ω → ℝ≥0∞ :=
    truncKernel (subMax f n) (fun ω : Ω => ENNReal.ofReal (f n ω)) m p with hKdef
  have hK : Measurable K := measurable_truncKernel hM hG m p
  have hu : ∀ (t : ℝ) (ω : Ω), K (t, ω) =
      if t ∈ Ioi (0:ℝ) ∩ Iic (min (subMax f n ω) (m:ℝ)) then
        ENNReal.ofReal (p * t ^ (p - 2)) * ENNReal.ofReal (f n ω) else 0 := by
    intro t ω; simp [hKdef, truncKernel, Set.indicator]
  have hmem : ∀ {t : ℝ}, 0 < t → ∀ ω : Ω,
      (t ∈ Ioi (0:ℝ) ∩ Iic (min (subMax f n ω) (m:ℝ))) ↔
        (ω ∈ {ω : Ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}) := by
    intro t ht ω
    simp only [mem_inter_iff, mem_Ioi, mem_Iic, mem_setOf_eq, le_min_iff]
    tauto
  have hinner : ∀ t ∈ Ioi (0:ℝ), ∫⁻ ω, K (t, ω) ∂μ =
      ENNReal.ofReal (p * t ^ (p - 2)) *
        ∫⁻ ω in {ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}, ENNReal.ofReal (f n ω) ∂μ := by
    intro t ht
    have hset : MeasurableSet ({ω : Ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}) :=
      (hM measurableSet_Ici).inter (by by_cases h : t ≤ (m:ℝ) <;> simp [h])
    have hpiece : ∀ ω, K (t, ω) = ({ω : Ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}).indicator
            (fun ω => ENNReal.ofReal (p * t ^ (p - 2)) * ENNReal.ofReal (f n ω)) ω := by
      intro ω
      rw [hu t ω]
      by_cases h : ω ∈ {ω : Ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}
      · rw [Set.indicator_of_mem h, if_pos ((hmem ht ω).mpr h)]
      · rw [Set.indicator_of_not_mem h, if_neg (fun hh => h ((hmem ht ω).mp hh))]
    simp only [hpiece]
    rw [lintegral_indicator hset, lintegral_const_mul _ hG]
  have hinnerω : ∀ ω : Ω, ∫⁻ t, K (t, ω) =
      ENNReal.ofReal (p / (p - 1)) *
        (ENNReal.ofReal (f n ω) * (ENNReal.ofReal (min (subMax f n ω) (m:ℝ))) ^ (p - 1)) := by
    intro ω
    have hc : 0 ≤ min (subMax f n ω) (m:ℝ) :=
      le_min (subMax_nonneg hnonneg n ω) (Nat.cast_nonneg m)
    have hpiece : (fun t => K (t, ω)) = (Ioi (0:ℝ) ∩ Iic (min (subMax f n ω) (m:ℝ))).indicator
            (fun t => ENNReal.ofReal (p * t ^ (p - 2)) * ENNReal.ofReal (f n ω)) := by
      funext t
      rw [hu t ω]
      simp [Set.indicator]
    rw [hpiece, lintegral_indicator (measurableSet_Ioi.inter measurableSet_Iic),
      lintegral_mul_const _ hf, lintegral_Iic_rpow hp hc, ENNReal.ofReal_mul (le_of_lt hp'0),
      ENNReal.ofReal_rpow_of_nonneg hc (by linarith : (0:ℝ) ≤ p - 1)]
    ring
  have hleft : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (p * t ^ (p - 2)) *
        ∫⁻ ω in {ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ t in Ioi (0:ℝ), (∫⁻ ω, K (t, ω) ∂μ) := by
    apply lintegral_congr_ae
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall ?_)
    intro t ht
    exact (hinner t ht).symm
  have hfull : ∫⁻ t in Ioi (0:ℝ), (∫⁻ ω, K (t, ω) ∂μ) = ∫⁻ t, (∫⁻ ω, K (t, ω) ∂μ) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_not_mem ht]
      have hzero : (fun ω => K (t, ω)) = fun _ => 0 := by
        funext ω; rw [hu t ω, if_neg (fun hh => ht hh.1)]
      rw [hzero, lintegral_zero]
  have hswap : ∫⁻ t, (∫⁻ ω, K (t, ω) ∂μ) = ∫⁻ ω, (∫⁻ t, K (t, ω)) ∂μ := by
    refine lintegral_lintegral_swap (f := fun t ω => K (t, ω)) ?_
    simpa [Function.uncurry] using hK.aemeasurable
  have hright : ∫⁻ ω, (∫⁻ t, K (t, ω)) ∂μ =
      ENNReal.ofReal (p / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
          (ENNReal.ofReal (min (subMax f n ω) (m:ℝ))) ^ (p - 1) ∂μ := by
    rw [← lintegral_const_mul _ (hG.mul (by measurability))]
    exact lintegral_congr hinnerω
  rw [hleft, hfull, hswap, hright]

set_option maxHeartbeats 800000 in
/-- Doob's `L^p` maximal inequality: the sharp moment bound for the maximal
function of a nonnegative submartingale. -/
theorem submartingale_moment_maximal_le (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((subMax f n ω) ^ p) ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  have hM : Measurable (subMax f n) :=
    measurable_subMax (fun k => (hsub.stronglyMeasurable k).measurable.mono (𝒢.le k) le_rfl) n
  have hG : Measurable (fun ω : Ω => ENNReal.ofReal (f n ω)) :=
    ((hsub.stronglyMeasurable n).measurable.mono (𝒢.le n) le_rfl).ennreal_ofReal
  have hpq : p.HolderConjugate (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    rw [inv_div]
    field_simp
  have hexp1 : 1 / p + 1 / (p / (p - 1)) = 1 := by
    rw [one_div, one_div, hpq.inv_add_inv_eq_one]
  have hstep : ∀ m : ℕ, ∫⁻ ω, ENNReal.ofReal ((min (subMax f n ω) (m:ℝ)) ^ p) ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ := by
    intro m
    set Am := ∫⁻ ω, ENNReal.ofReal ((min (subMax f n ω) (m:ℝ)) ^ p) ∂μ with hAmdef
    set B := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ with hBdef
    have hAm_top : Am < ⊤ := by
      calc Am ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((m:ℝ) ^ p) ∂μ :=
            lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow (le_min (subMax_nonneg hnonneg n ω) (Nat.cast_nonneg m))
                (min_le_right _ _) hp0.le))
        _ = ENNReal.ofReal ((m:ℝ) ^ p) * μ univ := lintegral_const _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
    have hchain : Am ≤ ENNReal.ofReal (p / (p - 1)) *
        (B ^ (1 / p) * Am ^ (1 / (p / (p - 1)))) := by
      calc Am = ∫⁻ t in Ioi (0:ℝ),
            μ {ω | t ≤ min (subMax f n ω) (m:ℝ)} * ENNReal.ofReal (p * t ^ (p - 1)) :=
            layer_cake_subMax hp hnonneg n m hM
        _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (p * t ^ (p - 2)) *
              ∫⁻ ω in {ω | t ≤ subMax f n ω} ∩ {_ω : Ω | t ≤ (m:ℝ)},
                ENNReal.ofReal (f n ω) ∂μ := by
            apply lintegral_mono_ae
            refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall ?_)
            intro t ht
            exact integrand_le hsub hnonneg hp n m ht
        _ = ENNReal.ofReal (p / (p - 1)) *
              ∫⁻ ω, ENNReal.ofReal (f n ω) *
                (ENNReal.ofReal (min (subMax f n ω) (m:ℝ))) ^ (p - 1) ∂μ :=
            tonelli_trunc hsub hnonneg hp n m hM
        _ ≤ ENNReal.ofReal (p / (p - 1)) *
              (B ^ (1 / p) * Am ^ (1 / (p / (p - 1)))) := by
            refine mul_le_mul_left' ?_ _
            have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hG.aemeasurable
              (by measurability : AEMeasurable (fun ω : Ω =>
                (ENNReal.ofReal (min (subMax f n ω) (m:ℝ))) ^ (p - 1)) μ)
            refine hholder.trans (le_of_eq ?_)
            have hB : (∫⁻ ω, ENNReal.ofReal (f n ω) ^ p ∂μ) = B := by
              rw [hBdef]
              apply lintegral_congr
              intro ω
              rw [ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp0.le]
            have hA : (∫⁻ ω, ((ENNReal.ofReal (min (subMax f n ω) (m:ℝ))) ^ (p - 1)) ^
                (p / (p - 1)) ∂μ) = Am := by
              rw [hAmdef]
              apply lintegral_congr
              intro ω
              have hc : 0 ≤ min (subMax f n ω) (m:ℝ) :=
                le_min (subMax_nonneg hnonneg n ω) (Nat.cast_nonneg m)
              have hxx : (p - 1) * (p / (p - 1)) = p := by
                rw [mul_comm]
                exact div_mul_cancel₀ p (by linarith : (p - 1) ≠ 0)
              rw [← ENNReal.rpow_mul, hxx, ENNReal.ofReal_rpow_of_nonneg hc hp0.le]
            rw [hB, hA]
    by_cases hA0 : Am = 0
    · rw [hA0]
      exact zero_le _
    have hkey : Am ^ (1 / p) ≤ ENNReal.ofReal (p / (p - 1)) * B ^ (1 / p) := by
      have hApos : 0 < Am := lt_of_le_of_ne (zero_le Am) (Ne.symm hA0)
      have hAne : Am ^ (1 / (p / (p - 1))) ≠ 0 :=
        ne_of_gt (ENNReal.rpow_pos hApos (ne_of_lt hAm_top))
      have hAtop : Am ^ (1 / (p / (p - 1))) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (p / (p - 1)))
          (ne_of_lt hAm_top)
      have hsplit : Am ^ (1 / p) * Am ^ (1 / (p / (p - 1))) = Am := by
        rw [← ENNReal.rpow_add (1 / p) (1 / (p / (p - 1))) hA0 (ne_of_lt hAm_top),
          hexp1, ENNReal.rpow_one]
      have hmono : Am ^ (1 / p) * Am ^ (1 / (p / (p - 1))) ≤
          (ENNReal.ofReal (p / (p - 1)) * B ^ (1 / p)) * Am ^ (1 / (p / (p - 1))) := by
        rw [hsplit]
        exact hchain.trans_eq (by ring)
      exact (ENNReal.mul_le_mul_right hAne hAtop).1 hmono
    calc Am = (Am ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal (p / (p - 1)) * B ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow hkey hp0.le
      _ = ENNReal.ofReal (p / (p - 1)) ^ p * (B ^ (1 / p)) ^ p :=
          ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (p / (p - 1))) (B ^ (1 / p)) hp0.le
      _ = ENNReal.ofReal ((p / (p - 1)) ^ p) * B := by
          rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hp'0) hp0.le, ← ENNReal.rpow_mul,
            one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hsup : ∫⁻ ω, ENNReal.ofReal ((subMax f n ω) ^ p) ∂μ =
      ⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal ((min (subMax f n ω) (m:ℝ)) ^ p) ∂μ := by
    let F (m : ℕ) (ω : Ω) := ENNReal.ofReal ((min (subMax f n ω) (m:ℝ)) ^ p)
    have hF (mm : ℕ) : Measurable (F mm) := by measurability
    have hmono : Monotone F := by
      intro i j hij ω
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow _ _ hp0.le
      · exact le_min (subMax_nonneg hnonneg n ω) (Nat.cast_nonneg i)
      · exact min_le_min_left _ (Nat.cast_le.mpr hij)
    have hpoint : ∀ ω : Ω, (⨆ mm, F mm ω) = ENNReal.ofReal ((subMax f n ω) ^ p) := by
      intro ω
      obtain ⟨mm, hmm⟩ := exists_nat_ge (subMax f n ω)
      apply le_antisymm
      · exact iSup_le (fun mm => ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (le_min (subMax_nonneg hnonneg n ω) (Nat.cast_nonneg mm))
            (min_le_left _ _) hp0.le))
      · exact le_iSup_of_le mm (by simp [F, min_eq_left hmm])
    change ∫⁻ ω, ENNReal.ofReal ((subMax f n ω) ^ p) ∂μ = ⨆ mm, ∫⁻ ω, F mm ω ∂μ
    rw [← lintegral_iSup hF hmono]
    exact lintegral_congr (fun ω => (hpoint ω).symm)
  rw [hsup]
  exact iSup_le hstep

set_option maxHeartbeats 800000 in
/-- **Doob's `L^p` maximal inequality** for a nonnegative submartingale, with the
sharp constant `p/(p-1)`. -/
theorem submartingale_eLpNorm_maximal_le (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    {p : ℝ} (hp : 1 < p) (n : ℕ) :
    eLpNorm (subMax f n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hM0 : ∀ ω, 0 ≤ subMax f n ω := subMax_nonneg hnonneg n
  have hg0 : ∀ ω, 0 ≤ f n ω := hnonneg n
  have hMn : eLpNorm (subMax f n) (ENNReal.ofReal p) μ =
      (∫⁻ ω, ENNReal.ofReal ((subMax f n ω) ^ p) ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hpne hptop, ENNReal.toReal_ofReal hp0.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_of_nonneg (hM0 ω), ENNReal.ofReal_rpow_of_nonneg (hM0 ω) hp0.le]
  have hgn : eLpNorm (f n) (ENNReal.ofReal p) μ =
      (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hpne hptop, ENNReal.toReal_ofReal hp0.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_of_nonneg (hg0 ω), ENNReal.ofReal_rpow_of_nonneg (hg0 ω) hp0.le]
  rw [hMn, hgn]
  calc (∫⁻ ω, ENNReal.ofReal ((subMax f n ω) ^ p) ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal ((p / (p - 1)) ^ p) *
          ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (submartingale_moment_maximal_le hsub hnonneg hp n)
          (by positivity : (0:ℝ) ≤ 1 / p)
    _ = ENNReal.ofReal ((p / (p - 1)) ^ p) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / p)
    _ = ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) := by
        have hratio : ((p / (p - 1)) ^ p) ^ (1 / p) = p / (p - 1) := by
          rw [← Real.rpow_mul (le_of_lt hp'0), mul_one_div_cancel hp0.ne', Real.rpow_one]
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ (p / (p - 1)) ^ p)
          (by positivity : (0:ℝ) ≤ 1 / p), hratio]

/-- **Doob's `L^p` maximal inequality** for a nonnegative martingale, with the
sharp constant `p/(p-1)`. -/
theorem martingale_eLpNorm_maximal_le (hmart : Martingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    {p : ℝ} (hp : 1 < p) (n : ℕ) :
    eLpNorm (subMax f n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ :=
  submartingale_eLpNorm_maximal_le hmart.submartingale hnonneg hp n

end WeightedBMO
