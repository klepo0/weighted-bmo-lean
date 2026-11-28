import WeightedBMO.EstSmaximal

/-!
# `est.X2` and `est.X3`

Khoa Lê, *Maximal inequalities, weighted BMO processes and the largest-jump normaliser*
(arXiv:2211.15550), Theorem 1.1.  These are the normalized and exponential
forms of the maximal inequality.  With the sharp maximal function `ψ` supplied
as a hypothesis (as in `WeightedBMO/EstSmaximal.lean`):

* `estX2` (equation (X2)): for every `p > 0` and every `ε > 0`,

  `‖sup_t d(X_0,X_t) / (ε + sup_{s≤t} ψ_s)‖_p ≤ 2 c_p p ‖1‖`,

  uniformly in `ε`.  It is `est.jnweight2` applied with the weight `2ψ`, whose
  oscillation modulus is at most `1`, together with the observation that
  `sup_{s≤t}(2ψ_s) = 2 sup_{s≤t} ψ_s` bounds the denominator from below.

* `estX3` (equation (X3)): the exponential form

  `∫ exp(λ sup_t d(X_0,X_t)/(ε + sup_{s≤t} ψ_s)) ≤ M μ(univ)` for every
  `λ ≤ (2e³)⁻¹`,

  where `M = exponentialBound`.  It follows from `estX2` at integer moments:
  dividing the maximal function by `2` brings the moment bound to exactly
  `c_n n ‖1‖`, so the exponential series of `WeightedBMO/GridExponential.lean`
  applies, and the factor `2` moves into the rate, giving `(2e³)⁻¹`.

The measurability of the normalized maximal function needs the cumulative
supremum `t ↦ sup_{s≤t} ψ_s` of an RCLL weight to be right-continuous, which is
`continuousWithinAt_intervalSup_cumul`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ m}

/-- Auxiliary: `a/(ε+S) ≤ 2 (a/S')` when `S' ≤ 2S`. -/
theorem div_le_two_div {a S S' ε : ℝ} (ha : 0 ≤ a) (_hS : 0 < S) (hS' : 0 < S')
    (hSS' : S' ≤ 2 * S) (hε : 0 < ε) : a / (ε + S) ≤ 2 * (a / S') := by
  have h1 : a / (ε + S) ≤ a / (S' / 2) :=
    div_le_div_of_nonneg_left ha (by positivity) (by linarith)
  have h2 : a / (S' / 2) = 2 * (a / S') := by
    field_simp
    ring
  rwa [h2] at h1

/-- The cumulative supremum of a right-continuous path is right-continuous. -/
theorem continuousWithinAt_intervalSup_cumul {f : ℝ → ℝ} {T u : ℝ}
    (hcont : ∀ t ∈ Ico 0 T, ContinuousWithinAt f (Ici t) t)
    (hbdd : ∀ t, t ≤ T → BddAbove (f '' Icc 0 t)) (hu : u ∈ Ico 0 T) :
    ContinuousWithinAt (fun t => intervalSup f 0 t) (Ici u) u := by
  have hsub : Icc u T ∈ 𝓝[Ici u] u :=
    mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨T, hu.2, fun x hx => hx⟩
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro b hb
    filter_upwards [hsub] with t ht
    exact lt_of_lt_of_le hb (weight_mono le_rfl hu.1 ht.1 (hbdd t ht.2))
  · intro b hb
    have hfu : f u < b :=
      (le_intervalSup (s := 0) (t := u) (u := u) (hbdd u hu.2.le) ⟨hu.1, le_rfl⟩).trans_lt hb
    obtain ⟨δ, hδ, hsubδ⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
      ((hcont u hu).eventually (Iio_mem_nhds (show f u < (f u + b) / 2 by linarith)))
    filter_upwards [hsub,
      mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨δ, hδ, subset_rfl⟩] with t ht htδ
    refine lt_of_le_of_lt ?_ (max_lt hb (by linarith : (f u + b) / 2 < b))
    refine intervalSup_le (s := 0) (t := t)
      (c := max (intervalSup f 0 u) ((f u + b) / 2)) (by linarith [hu.1, ht.1]) ?_
    intro s hs
    rcases le_or_lt s u with hsu | hsu
    · exact (le_intervalSup (s := 0) (t := u) (u := s) (hbdd u hu.2.le) ⟨hs.1, hsu⟩).trans
        (le_max_left _ _)
    · exact (hsubδ ⟨le_of_lt hsu, hs.2.trans htδ.2⟩).le.trans (le_max_right _ _)


/-- **`est.X2`**: the normalized maximal function is bounded by `2 c_p p` on
every `p > 0`, uniformly in the regularizing parameter `ε`.

Stated for a finite measure, the constant carries the factor `‖1‖_p`; on a
probability measure `eLpNorm_one` shows `‖1‖_p = 1` and the bound is the
paper's bare constant `2 c_m m` (see `Theorem11.cor_maximaldagger`). -/
theorem estX2 {E : Type*} [PseudoMetricSpace E]
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
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * goodLambdaConstant p) *
        eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal p) μ := by
  -- the two paths and their boundedness
  have hcont_v : ∀ ω u, u ∈ Ico 0 T →
      ContinuousWithinAt (fun t => dist (X ω 0) (X ω t)) (Ici u) u :=
    fun ω u hu => continuousWithinAt_const.dist (cX ω u hu)
  have hl_v : ∀ ω u, u ∈ Ioc 0 T →
      Tendsto (fun t => dist (X ω 0) (X ω t)) (𝓝[<] u) (𝓝 (dist (X ω 0) (Xl ω u))) :=
    fun ω u hu => tendsto_const_nhds.dist (lX ω u hu)
  have hv : ∀ ω, BddAbove ((fun u => |dist (X ω 0) (X ω u)|) '' Icc 0 T) :=
    fun ω => cadlag_bounded (hcont_v ω) (fun u hu => ⟨_, hl_v ω u hu⟩)
  have hψbd : ∀ ω, BddAbove ((fun u => |ψ ω u|) '' Icc 0 T) :=
    fun ω => cadlag_bounded (cw ω) (lw ω)
  have hψbd' : ∀ ω t, t ≤ T → BddAbove ((fun u => ψ ω u) '' Icc 0 t) := by
    intro ω t ht
    obtain ⟨d, hd⟩ := hψbd ω
    refine ⟨d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (le_abs_self _).trans (hd (mem_image_of_mem _ ⟨hu.1, hu.2.trans ht⟩))
  have hφ : ∀ ω u, u ∈ Icc 0 T → 0 < 2 * ψ ω u := fun ω u hu =>
    mul_pos (by norm_num) (hψpos ω u hu)
  have hφbdd : ∀ ω, BddAbove ((fun u => 2 * ψ ω u) '' Icc 0 T) := by
    intro ω
    obtain ⟨d, hd⟩ := hψbd ω
    refine ⟨2 * d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hd (mem_image_of_mem _ hu)))
      (by norm_num)
  have hmw : ∀ u ∈ Icc 0 T, Measurable[ℱ u] (fun ω => 2 * ψ ω u) := by
    intro u hu
    have h := (hψmeas u hu).const_mul (2 : ℝ)
    simpa [mul_comm] using h
  have hcw : ∀ ω u, u ∈ Ico 0 T → ContinuousWithinAt (fun t => 2 * ψ ω t) (Ici u) u :=
    fun ω u hu => (cw ω u hu).const_mul 2
  have hlw : ∀ ω u, u ∈ Ioc 0 T → ∃ l, Tendsto (fun t => 2 * ψ ω t) (𝓝[<] u) (𝓝 l) := by
    intro ω u hu
    obtain ⟨l, hl⟩ := lw ω u hu
    exact ⟨2 * l, hl.const_mul 2⟩
  -- `est.jnweight2` with the weight `2ψ`
  have hB := weightedBMOOfSharpMaximal (ℱ := ℱ) X Xl ψ hψpos hdom hdomL hdata
  have hmean := stoppedBound_of_bmo hB le_rfl le_rfl hφ hφbdd
  have hmain := real_interval_moments (μ := μ) ℱ hℱ
    (fun ω t => dist (X ω 0) (X ω t)) (fun ω t => dist (X ω 0) (Xl ω t))
    (fun ω t => 2 * ψ ω t) (r := 0) (T := T) (c := 1) hT (by norm_num) hp
    hv hφbdd hφ mv hmw hcont_v hcw hl_v hmean (E := univ) MeasurableSet.univ
  have hnm : (fun ω => normalizedMaximum (fun t => dist (X ω 0) (X ω t))
        (fun t => 2 * ψ ω t) 0 T / 1) =
      fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
        intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T := by
    funext ω
    simp only [normalizedMaximum, div_one]
    congr 1
    funext t
    rw [dist_self, sub_zero, abs_of_nonneg dist_nonneg]
  rw [hnm, Measure.restrict_univ] at hmain
  -- pointwise comparison with the weight's running supremum
  have hv' : ∀ ω, BddAbove ((fun u => |dist (X ω 0) (X ω u)|) '' Icc 0 T) := hv
  have hratio : ∀ ω, BddAbove ((fun u => dist (X ω 0) (X ω u) /
      intervalSup (fun s => 2 * ψ ω s) 0 u) '' Icc 0 T) := by
    intro ω
    have h := ratio_bounded (v := fun u => dist (X ω 0) (X ω u))
      (φ := fun u => 2 * ψ ω u) (s := 0) (t := T) (hφ ω 0 ⟨le_rfl, hT⟩) (hv' ω) (hφbdd ω)
    simpa [dist_self, sub_zero] using h
  have hpt : ∀ ω, intervalSup (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T ≤
      2 * intervalSup (fun t => dist (X ω 0) (X ω t) /
        intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T := by
    intro ω
    apply intervalSup_le hT
    intro t ht
    have hS : 0 < intervalSup (fun s => ψ ω s) 0 t :=
      (hψpos ω 0 ⟨le_rfl, hT⟩).trans_le (le_intervalSup (hψbd' ω t ht.2) ⟨le_rfl, ht.1⟩)
    have hφbdd' : BddAbove ((fun u => 2 * ψ ω u) '' Icc 0 t) :=
      (hφbdd ω).mono (image_mono (Icc_subset_Icc le_rfl ht.2))
    have hS' : 0 < intervalSup (fun s => 2 * ψ ω s) 0 t :=
      (hφ ω 0 ⟨le_rfl, hT⟩).trans_le (le_intervalSup hφbdd' ⟨le_rfl, ht.1⟩)
    have hSS' : intervalSup (fun s => 2 * ψ ω s) 0 t ≤ 2 * intervalSup (fun s => ψ ω s) 0 t := by
      apply intervalSup_le ht.1
      intro u hu
      have h := le_intervalSup (hψbd' ω t ht.2) hu
      linarith
    refine (div_le_two_div dist_nonneg hS hS' hSS' hε).trans ?_
    gcongr
    exact le_intervalSup (hratio ω) ht
  -- assemble
  have hleft0 : ∀ ω, 0 ≤ intervalSup (fun t => dist (X ω 0) (X ω t) /
      (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T := by
    intro ω
    apply Real.sSup_nonneg
    rintro _ ⟨u, hu, rfl⟩
    exact div_nonneg dist_nonneg (by
      have hS0 : 0 < intervalSup (fun s => ψ ω s) 0 u :=
        (hψpos ω 0 ⟨le_rfl, hT⟩).trans_le (le_intervalSup (hψbd' ω u hu.2) ⟨le_rfl, hu.1⟩)
      linarith)
  have hright0 : ∀ ω, 0 ≤ intervalSup (fun t => dist (X ω 0) (X ω t) /
      intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T := by
    intro ω
    apply Real.sSup_nonneg
    rintro _ ⟨u, hu, rfl⟩
    exact div_nonneg dist_nonneg (by
      have hb : BddAbove ((fun s => 2 * ψ ω s) '' Icc 0 u) :=
        (hφbdd ω).mono (image_mono (Icc_subset_Icc le_rfl hu.2))
      have hS0 : 0 < intervalSup (fun s => 2 * ψ ω s) 0 u :=
        (hφ ω 0 ⟨le_rfl, hT⟩).trans_le (le_intervalSup hb ⟨le_rfl, hu.1⟩)
      linarith)
  have hmono : eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => 2 * intervalSup (fun t => dist (X ω 0) (X ω t) /
        intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hleft0 ω),
      abs_of_nonneg (by linarith [hright0 ω])]
    exact hpt ω
  have hscale : eLpNorm (fun ω => 2 * intervalSup (fun t => dist (X ω 0) (X ω t) /
        intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) (ENNReal.ofReal p) μ =
      ENNReal.ofReal 2 * eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
        intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) (ENNReal.ofReal p) μ := by
    rw [show (fun ω => 2 * intervalSup (fun t => dist (X ω 0) (X ω t) /
        intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) =
        (2 : ℝ) • (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
          intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun ω => 2 * intervalSup (fun t => dist (X ω 0) (X ω t) /
          intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) (ENNReal.ofReal p) μ := hmono
    _ = ENNReal.ofReal 2 * eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
          intervalSup (fun s => 2 * ψ ω s) 0 t) 0 T) (ENNReal.ofReal p) μ := hscale
    _ ≤ ENNReal.ofReal 2 *
          (ENNReal.ofReal (goodLambdaConstant p) *
            eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal p) μ) :=
        mul_le_mul_left' hmain _
    _ = ENNReal.ofReal (2 * goodLambdaConstant p) *
          eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal p) μ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        ring

/-- **`est.X3`**: the exponential form, at the rate `λ ≤ (2e³)⁻¹`, with the
bound `M · μ(univ)`. On a probability measure the factor `μ(univ)` is one and
this is the paper's `M`, the constant of `def.M` (`exponentialBound`; its term of
index zero is one, so it is `1 + Σ_{m ≥ 1} (c_m m)^m e^{-3m}/m!`). -/
theorem estX3 {E : Type*} [PseudoMetricSpace E]
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
    {ε : ℝ} (hε : 0 < ε) {rate : ℝ} (hrate : rate ≤ (2 * Real.exp 3)⁻¹) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (rate * intervalSup (fun t =>
        dist (X ω 0) (X ω t) / (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T)) ∂μ) ≤
      ENNReal.ofReal exponentialBound * μ univ := by
  have harg : ∀ u ∈ Icc 0 T, Measurable[ℱ u] (fun ω => dist (X ω 0) (X ω u)) := mv
  have hcont_v : ∀ ω u, u ∈ Ico 0 T →
      ContinuousWithinAt (fun t => dist (X ω 0) (X ω t)) (Ici u) u :=
    fun ω u hu => continuousWithinAt_const.dist (cX ω u hu)
  have hl_v : ∀ ω u, u ∈ Ioc 0 T →
      Tendsto (fun t => dist (X ω 0) (X ω t)) (𝓝[<] u) (𝓝 (dist (X ω 0) (Xl ω u))) :=
    fun ω u hu => tendsto_const_nhds.dist (lX ω u hu)
  have hv : ∀ ω, BddAbove ((fun u => dist (X ω 0) (X ω u)) '' Icc 0 T) := by
    intro ω
    obtain ⟨d, hd⟩ := cadlag_bounded (hcont_v ω) (fun u hu => ⟨_, hl_v ω u hu⟩)
    refine ⟨d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (le_abs_self _).trans (hd (mem_image_of_mem _ hu))
  have hψbd : ∀ ω, BddAbove ((fun u => |ψ ω u|) '' Icc 0 T) :=
    fun ω => cadlag_bounded (cw ω) (lw ω)
  have hψbdT : ∀ ω, BddAbove ((fun u => ψ ω u) '' Icc 0 T) := by
    intro ω
    obtain ⟨d, hd⟩ := hψbd ω
    refine ⟨d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (le_abs_self _).trans (hd (mem_image_of_mem _ hu))
  have hψbd' : ∀ ω t, t ≤ T → BddAbove ((fun u => ψ ω u) '' Icc 0 t) := fun ω t ht =>
    (hψbdT ω).mono (image_mono (Icc_subset_Icc le_rfl ht))
  have hrmeas : ∀ u ∈ Icc 0 T, Measurable (fun ω => dist (X ω 0) (X ω u) /
      (ε + intervalSup (fun s => ψ ω s) 0 u)) := by
    intro u hu
    have hs : Measurable (fun ω => intervalSup (fun s => ψ ω s) 0 u) :=
      measurable_intervalSup hu.1 (fun ω => hψbd' ω u hu.2)
        (fun s hs => (hψmeas s ⟨hs.1, hs.2.trans hu.2⟩).mono (ℱ.le s) le_rfl)
        (fun ω s hs => cw ω s ⟨hs.1, lt_of_lt_of_le hs.2 hu.2⟩)
    exact ((mv u hu).mono (ℱ.le u) le_rfl).div (measurable_const.add hs)
  have hSpos : ∀ ω t, t ∈ Icc 0 T → 0 < intervalSup (fun s => ψ ω s) 0 t := by
    intro ω t ht
    exact (hψpos ω 0 ⟨le_rfl, hT⟩).trans_le
      (le_intervalSup (s := 0) (t := t) (u := 0) (hψbd' ω t ht.2) ⟨le_rfl, ht.1⟩)
  have hrpos : ∀ ω t, t ∈ Icc 0 T → 0 < ε + intervalSup (fun s => ψ ω s) 0 t := by
    intro ω t ht
    linarith [hSpos ω t ht, hε]
  have hrcont : ∀ ω u, u ∈ Ico 0 T →
      ContinuousWithinAt (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) (Ici u) u := by
    intro ω u hu
    have h1 : ContinuousWithinAt (fun t => dist (X ω 0) (X ω t)) (Ici u) u :=
      continuousWithinAt_const.dist (cX ω u hu)
    have h2 : ContinuousWithinAt (fun t => intervalSup (fun s => ψ ω s) 0 t) (Ici u) u :=
      continuousWithinAt_intervalSup_cumul (cw ω)
        (fun t ht => (hψbdT ω).mono (image_mono (Icc_subset_Icc le_rfl ht))) hu
    have h3 : ContinuousWithinAt (fun t => ε + intervalSup (fun s => ψ ω s) 0 t) (Ici u) u :=
      continuousWithinAt_const.add h2
    exact h1.div h3 (hrpos ω u ⟨hu.1, hu.2.le⟩).ne'
  have hrbound : ∀ ω, BddAbove ((fun t => dist (X ω 0) (X ω t) /
      (ε + intervalSup (fun s => ψ ω s) 0 t)) '' Icc 0 T) := by
    intro ω
    obtain ⟨d, hd⟩ := hv ω
    refine ⟨d / ε, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 : dist (X ω 0) (X ω u) ≤ d := hd (mem_image_of_mem _ hu)
    have h2 : 0 ≤ intervalSup (fun s => ψ ω s) 0 u := (hSpos ω u hu).le
    rw [div_le_div_iff₀ (by positivity) hε]
    nlinarith [dist_nonneg (x := X ω 0) (y := X ω u)]
  have hZmeas : Measurable (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
      (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) :=
    measurable_intervalSup hT hrbound hrmeas hrcont
  have hZ0 : ∀ ω, 0 ≤ intervalSup (fun t => dist (X ω 0) (X ω t) /
      (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T := by
    intro ω
    apply Real.sSup_nonneg
    rintro _ ⟨u, hu, rfl⟩
    exact div_nonneg dist_nonneg (hrpos ω u hu).le
  have hmom : ∀ n : ℕ, 0 < n → eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T / 2) (ENNReal.ofReal n) μ ≤
      ENNReal.ofReal (goodLambdaConstant n) *
        eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal n) μ := by
    intro n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have h2 := estX2 (ℱ := ℱ) X Xl ψ hT hℱ hψpos hψmeas hdom hdomL hdata mv cX lX cw lw hε hn'
    calc eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
          (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T / 2) (ENNReal.ofReal n) μ
        = ENNReal.ofReal (1/2) * eLpNorm (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
            (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) (ENNReal.ofReal n) μ := by
          rw [show (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
              (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T / 2) =
              (1/2 : ℝ) • (fun ω => intervalSup (fun t => dist (X ω 0) (X ω t) /
                (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T) from by
            funext ω; simp [div_eq_mul_inv, mul_comm],
            eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      _ ≤ ENNReal.ofReal (1/2) * (ENNReal.ofReal (2 * goodLambdaConstant n) *
            eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal n) μ) := mul_le_mul_left' h2 _
      _ = ENNReal.ofReal (goodLambdaConstant n) *
            eLpNorm (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal n) μ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
          congr 2
          ring
  have hexp := exponential_of_moments (μ := μ) (b := 3) (by norm_num)
    (hZmeas.div_const 2) (fun ω => div_nonneg (hZ0 ω) (by norm_num)) hmom
  have hrate' : rate ≤ Real.exp (-3) / 2 := by
    have h : (2 * Real.exp 3)⁻¹ = Real.exp (-3) / 2 := by
      rw [Real.exp_neg]
      field_simp
      ring
    rwa [h] at hrate
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (rate * intervalSup (fun t => dist (X ω 0) (X ω t) /
        (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.exp (-3) *
          (intervalSup (fun t => dist (X ω 0) (X ω t) /
            (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T / 2))) ∂μ := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        rw [show Real.exp (-3) * (intervalSup (fun t => dist (X ω 0) (X ω t) /
            (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T / 2) =
            (Real.exp (-3) / 2) * intervalSup (fun t => dist (X ω 0) (X ω t) /
              (ε + intervalSup (fun s => ψ ω s) 0 t)) 0 T from by ring]
        exact mul_le_mul_of_nonneg_right hrate' (hZ0 ω)
    _ ≤ ENNReal.ofReal exponentialBound * μ univ := hexp


end WeightedBMO
