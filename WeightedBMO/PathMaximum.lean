import WeightedBMO.ConditionalBound

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

/-- Supremum of a real path on a nonempty closed time interval. -/
noncomputable def intervalSup (f : ℝ → ℝ) (s t : ℝ) := sSup (f '' Icc s t)

/-- The pathwise random variable inside (1.9) and (1.10). -/
noncomputable def normalizedMaximum (v φ : ℝ → ℝ) (s t : ℝ) :=
  intervalSup (fun u => |v u - v s| / intervalSup φ s u) s t

private theorem le_intervalSup {f : ℝ → ℝ} {s t u : ℝ} (hb : BddAbove (f '' Icc s t))
    (hu : u ∈ Icc s t) : f u ≤ intervalSup f s t := le_csSup hb (mem_image_of_mem _ hu)

private theorem intervalSup_le {f : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (h : ∀ u ∈ Icc s t, f u ≤ c) : intervalSup f s t ≤ c :=
  csSup_le ((nonempty_Icc.mpr hst).image _) (by rintro _ ⟨u, hu, rfl⟩; exact h u hu)

private theorem weight_mono {φ : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hb : BddAbove (φ '' Icc a d)) : intervalSup φ b c ≤ intervalSup φ a d :=
  intervalSup_le hbc fun _ hu => le_intervalSup hb ⟨hab.trans hu.1, hu.2.trans hcd⟩

private theorem ratio_bounded {v φ : ℝ → ℝ} {s t : ℝ} (hp : 0 < φ s)
    (hv : BddAbove ((fun u => |v u|) '' Icc s t)) (hw : BddAbove (φ '' Icc s t)) :
    BddAbove ((fun u => |v u - v s| / intervalSup φ s u) '' Icc s t) := by
  obtain ⟨B,hB⟩ := hv
  refine ⟨(B + |v s|) / φ s, ?_⟩
  rintro _ ⟨u,hu,rfl⟩
  have hsu := le_intervalSup (hw.mono (image_mono (Icc_subset_Icc le_rfl hu.2))) (left_mem_Icc.mpr hu.1)
  exact div_le_div₀ (by exact add_nonneg ((abs_nonneg (v u)).trans (hB (mem_image_of_mem _ hu))) (abs_nonneg _))
    ((abs_sub _ _).trans (add_le_add_right (hB (mem_image_of_mem _ hu)) _)) hp hsu

theorem normalizedMaximum_self (v φ : ℝ → ℝ) (s : ℝ) : normalizedMaximum v φ s s = 0 := by
  simp [normalizedMaximum, intervalSup]

theorem normalizedMaximum_nonneg {v φ : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) (hp : 0 < φ s)
    (hv : BddAbove ((fun u => |v u|) '' Icc s t)) (hw : BddAbove (φ '' Icc s t)) :
    0 ≤ normalizedMaximum v φ s t := by
  simpa using le_intervalSup (ratio_bounded hp hv hw) (left_mem_Icc.mpr hst)

theorem normalizedMaximum_split {v φ : ℝ → ℝ} {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t)
    (hr : 0 < φ r) (hs : 0 < φ s)
    (hv : BddAbove ((fun u => |v u|) '' Icc r t)) (hw : BddAbove (φ '' Icc r t)) :
    normalizedMaximum v φ r t ≤ normalizedMaximum v φ r s + normalizedMaximum v φ s t := by
  have leftSub : Icc r s ⊆ Icc r t := Icc_subset_Icc le_rfl hst
  have rightSub : Icc s t ⊆ Icc r t := Icc_subset_Icc hrs le_rfl
  have L := ratio_bounded hr (hv.mono (image_mono leftSub)) (hw.mono (image_mono leftSub))
  have R := ratio_bounded hs (hv.mono (image_mono rightSub)) (hw.mono (image_mono rightSub))
  apply intervalSup_le (hrs.trans hst)
  intro u hu
  by_cases hus : u ≤ s
  · exact (le_intervalSup L ⟨hu.1, hus⟩).trans (le_add_of_nonneg_right
      (normalizedMaximum_nonneg hst hs (hv.mono (image_mono rightSub)) (hw.mono (image_mono rightSub))))
  have hsu := le_of_not_ge hus
  have wu := hw.mono (image_mono (Icc_subset_Icc le_rfl hu.2))
  have Wr := le_intervalSup (hw.mono (image_mono leftSub)) (left_mem_Icc.mpr hrs)
  have Ws := le_intervalSup (wu.mono (image_mono (Icc_subset_Icc hrs le_rfl))) (left_mem_Icc.mpr hsu)
  have ml := weight_mono le_rfl hrs hsu wu
  have mr := weight_mono hrs hsu le_rfl wu
  calc
    _ ≤ (|v s - v r| + |v u - v s|) / intervalSup φ r u := by
      apply div_le_div_of_nonneg_right _ ((hr.trans_le Wr).le.trans ml)
      simpa [add_comm] using abs_sub_le (v u) (v s) (v r)
    _ = _ := add_div _ _ _
    _ ≤ _ := add_le_add
      ((div_le_div_of_nonneg_left (abs_nonneg _) (hr.trans_le Wr) ml).trans
        (le_intervalSup (f := fun x => |v x - v r| / intervalSup φ r x) L (right_mem_Icc.mpr hrs)))
      ((div_le_div_of_nonneg_left (abs_nonneg _) (hs.trans_le Ws) mr).trans
        (le_intervalSup (f := fun x => |v x - v s| / intervalSup φ s x) R ⟨hsu, hu.2⟩))

open Filter Topology

/-- A strict crossing by a right-continuous path is detected at a rational
time or at the right endpoint itself. -/
theorem intervalSup_crossing {f : ℝ → ℝ} {s t b : ℝ} (hst : s ≤ t)
    (hb : BddAbove (f '' Icc s t))
    (hc : ∀ u ∈ Ico s t, ContinuousWithinAt f (Ici u) u) :
    b < intervalSup f s t ↔ b < f t ∨ ∃ q : ℚ, (q : ℝ) ∈ Icc s t ∧ b < f q := by
  constructor
  · intro h
    obtain ⟨_, ⟨u, hu, rfl⟩, hfu⟩ := (lt_csSup_iff hb ((nonempty_Icc.mpr hst).image _)).1 h
    rcases hu.2.eq_or_lt with heq | hut
    · exact Or.inl (heq ▸ hfu)
    have he := (hc u ⟨hu.1,hut⟩).tendsto (Ioi_mem_nhds hfu)
    obtain ⟨x,hx,hsub⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hut).1 he
    obtain ⟨q,hq,hqx⟩ := exists_rat_btwn hx.1
    exact Or.inr ⟨q, ⟨hu.1.trans hq.le,hqx.le.trans hx.2⟩, hsub ⟨hq.le,hqx⟩⟩
  · rintro (ht | ⟨q,hq,hf⟩)
    · exact ht.trans_le (le_intervalSup hb (right_mem_Icc.mpr hst))
    · exact hf.trans_le (le_intervalSup hb hq)

theorem measurable_intervalSup {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    {s t : ℝ} (hst : s ≤ t) (hb : ∀ ω, BddAbove (f ω '' Icc s t))
    (hm : ∀ u ∈ Icc s t, Measurable (fun ω => f ω u))
    (hc : ∀ ω u, u ∈ Ico s t → ContinuousWithinAt (f ω) (Ici u) u) :
    Measurable (fun ω => intervalSup (f ω) s t) := by
  apply measurable_of_Ioi
  intro b
  rw [show (fun ω => intervalSup (f ω) s t) ⁻¹' Ioi b =
    {ω | b < f ω t} ∪ ⋃ (q : ℚ) (_ : (q : ℝ) ∈ Icc s t), {ω | b < f ω q} by
      ext ω; simp [intervalSup_crossing hst (hb ω) (hc ω)]]
  exact (measurableSet_lt measurable_const (hm _ (right_mem_Icc.mpr hst))).union
    (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      measurableSet_lt measurable_const (hm _ hq))

theorem continuousWithinAt_runningSup {φ : ℝ → ℝ} {s u t : ℝ} (hsu : s ≤ u) (hut : u < t)
    (hb : BddAbove (φ '' Icc s t)) (hc : ContinuousWithinAt φ (Ici u) u) :
    ContinuousWithinAt (intervalSup φ s) (Ici u) u := by
  have hu := hb.mono (image_mono (Icc_subset_Icc le_rfl hut.le))
  apply tendsto_order.2
  constructor
  · intro b h
    filter_upwards [Ico_mem_nhdsGE hut] with x hx
    exact h.trans_le (weight_mono le_rfl hsu hx.1 (hb.mono (image_mono (Icc_subset_Icc le_rfl hx.2.le))))
  · intro b h
    obtain ⟨d,hd,hdb⟩ := exists_between h
    have hf := (le_intervalSup hu (right_mem_Icc.mpr hsu)).trans_lt hd
    obtain ⟨y,hy,hsub⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hut).1
      (hc.tendsto (Iio_mem_nhds hf))
    filter_upwards [Ico_mem_nhdsGE hy.1] with x hx
    apply lt_of_le_of_lt _ hdb
    apply intervalSup_le (hsu.trans hx.1)
    intro z hz
    by_cases hzu : z ≤ u
    · exact (le_intervalSup hu ⟨hz.1,hzu⟩).trans hd.le
    · exact (show φ z < d from hsub ⟨(le_of_not_ge hzu),hz.2.trans_lt hx.2⟩).le

theorem measurable_normalizedMaximum {Ω : Type*} [MeasurableSpace Ω] {v φ : Ω → ℝ → ℝ}
    {s t : ℝ} (hst : s ≤ t) (hbv : ∀ ω, BddAbove ((fun x => |v ω x|) '' Icc s t))
    (hbφ : ∀ ω, BddAbove (φ ω '' Icc s t)) (hp : ∀ ω, 0 < φ ω s)
    (mv : ∀ u ∈ Icc s t, Measurable (fun ω => v ω u))
    (mw : ∀ u ∈ Icc s t, Measurable (fun ω => φ ω u))
    (cv : ∀ ω u, u ∈ Ico s t → ContinuousWithinAt (v ω) (Ici u) u)
    (cw : ∀ ω u, u ∈ Ico s t → ContinuousWithinAt (φ ω) (Ici u) u) :
    Measurable (fun ω => normalizedMaximum (v ω) (φ ω) s t) := by
  apply measurable_intervalSup hst (fun ω => ratio_bounded (hp ω) (hbv ω) (hbφ ω))
  · intro u hu
    exact (continuous_abs.measurable.comp ((mv u hu).sub (mv s (left_mem_Icc.mpr hst)))).div
      (measurable_intervalSup hu.1 (fun ω => (hbφ ω).mono (image_mono (Icc_subset_Icc le_rfl hu.2)))
        (fun x hx => mw x ⟨hx.1,hx.2.trans hu.2⟩)
        (fun ω x hx => cw ω x ⟨hx.1,hx.2.trans_le hu.2⟩))
  · intro ω u hu
    apply ((cv ω u hu).sub continuousWithinAt_const).abs.div
      (continuousWithinAt_runningSup hu.1 hu.2 (hbφ ω) (cw ω u hu))
    exact ((hp ω).trans_le (le_intervalSup ((hbφ ω).mono (image_mono (Icc_subset_Icc le_rfl hu.2.le)))
      (left_mem_Icc.mpr hu.1))).ne'

/-- The conditional exponential bound for the paper's normalized maximum,
using the initial-event integer moment form of (1.9). -/
theorem path_exponential_of_interval_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℝ m)
    (v φ : Ω → ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) {a T rate : ℝ}
    (hv : ∀ ω, BddAbove ((fun u => |v ω u|) '' Icc a T))
    (hw : ∀ ω, BddAbove (φ ω '' Icc a T))
    (hp : ∀ ω u, u ∈ Icc a T → 0 < φ ω u)
    (mv : ∀ u ∈ Icc a T, Measurable[ℱ u] (fun ω => v ω u))
    (mw : ∀ u ∈ Icc a T, Measurable[ℱ u] (fun ω => φ ω u))
    (cv : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (v ω) (Ici u) u)
    (cw : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (φ ω) (Ici u) u)
    (hmom : ∀ s t, a ≤ s → s ≤ t → t ≤ T → ∀ c : ℝ, 0 < c → ρ s t ≤ c →
      ∀ E : Set Ω, MeasurableSet[ℱ s] E → ∀ n : ℕ, 0 < n →
      eLpNorm (fun ω => normalizedMaximum (v ω) (φ ω) s t / c) (ENNReal.ofReal n) (μ.restrict E) ≤
        ENNReal.ofReal (goodLambdaConstant n) *
          eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal n) (μ.restrict E))
    (hb : (smallScaleBounds ρ a T).Nonempty)
    (hend : rate * sInf (smallScaleBounds ρ a T) ≤ Real.exp (-3)) :
    (⨆ r : Icc a T, eLpNorm
      (μ[fun ω => Real.exp (rate * normalizedMaximum (v ω) (φ ω) r T)|ℱ r]) ⊤ μ) < ⊤ := by
  apply conditional_exponential_of_interval_moments μ ℱ
    (fun s t ω => normalizedMaximum (v ω) (φ ω) s t) ρ _ _ _ _ hmom hb hend
  · intro s t ha hst ht
    have hsub : Icc s t ⊆ Icc a T := Icc_subset_Icc ha ht
    exact @measurable_normalizedMaximum Ω (ℱ t) v φ s t hst (fun ω => (hv ω).mono (image_mono hsub))
      (fun ω => (hw ω).mono (image_mono hsub)) (fun ω => hp ω s (hsub (left_mem_Icc.mpr hst)))
      (fun u hu => (mv u (hsub hu)).mono (ℱ.mono hu.2) le_rfl)
      (fun u hu => (mw u (hsub hu)).mono (ℱ.mono hu.2) le_rfl)
      (fun ω u hu => cv ω u ⟨ha.trans hu.1, hu.2.trans_le ht⟩)
      (fun ω u hu => cw ω u ⟨ha.trans hu.1, hu.2.trans_le ht⟩)
  · intro s t ω ha hst ht
    exact normalizedMaximum_nonneg hst (hp ω s ⟨ha,hst.trans ht⟩)
      ((hv ω).mono (image_mono (Icc_subset_Icc ha ht)))
      ((hw ω).mono (image_mono (Icc_subset_Icc ha ht)))
  · exact fun r _ ω => normalizedMaximum_self _ _ r
  · intro r s t ω ha hrs hst ht
    exact normalizedMaximum_split hrs hst (hp ω r ⟨ha,hrs.trans (hst.trans ht)⟩)
      (hp ω s ⟨ha.trans hrs,hst.trans ht⟩) ((hv ω).mono (image_mono (Icc_subset_Icc ha ht)))
      ((hw ω).mono (image_mono (Icc_subset_Icc ha ht)))

end WeightedBMO
