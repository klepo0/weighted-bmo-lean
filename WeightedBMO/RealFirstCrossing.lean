import WeightedBMO.PathMaximum

open MeasureTheory Set Filter Topology

namespace WeightedBMO

/-- Real-time first strict crossing capped at the terminal time. -/
noncomputable def crossingTime (f : ℝ → ℝ) (r T b : ℝ) :=
  sInf (insert T {u ∈ Icc r T | b < f u})

private theorem crossing_lowerBounds {f : ℝ → ℝ} {r T b : ℝ} (hr : r ≤ T) :
    r ∈ lowerBounds (insert T {u ∈ Icc r T | b < f u}) := by
  rintro _ (rfl | hu)
  · exact hr
  · exact hu.1.1

theorem crossingTime_mem {f : ℝ → ℝ} {r T b : ℝ} (hr : r ≤ T) :
    crossingTime f r T b ∈ Icc r T :=
  ⟨le_csInf (insert_nonempty _ _) (crossing_lowerBounds hr),
   csInf_le ⟨r,crossing_lowerBounds hr⟩ (mem_insert _ _)⟩

theorem crossingTime_mono {f : ℝ → ℝ} {r T b d : ℝ} (hr : r ≤ T) (h : b ≤ d) :
    crossingTime f r T b ≤ crossingTime f r T d := by
  apply le_csInf (insert_nonempty _ _)
  rintro x (rfl | hx)
  · exact (crossingTime_mem hr).2
  · exact csInf_le ⟨r,crossing_lowerBounds hr⟩ (mem_insert_of_mem _ ⟨hx.1,h.trans_lt hx.2⟩)

theorem crossingTime_lt_iff {f : ℝ → ℝ} {r T b i : ℝ} (hr : r ≤ T) (hi : i ≤ T)
    (hc : ∀ u ∈ Ico r T, ContinuousWithinAt f (Ici u) u) :
    crossingTime f r T b < i ↔ ∃ q : ℚ, (q : ℝ) ∈ Ico r i ∧ b < f q := by
  rw [crossingTime, csInf_lt_iff ⟨r,crossing_lowerBounds hr⟩ (insert_nonempty _ _)]
  constructor
  · rintro ⟨u,hu,hui⟩
    rcases hu with rfl | hu
    · exact (not_lt_of_ge hi hui).elim
    have he := (hc u ⟨hu.1.1,hui.trans_le hi⟩).tendsto (Ioi_mem_nhds hu.2)
    obtain ⟨x,hx,hsub⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hui).1 he
    obtain ⟨q,hq,hqx⟩ := exists_rat_btwn hx.1
    exact ⟨q,⟨hu.1.1.trans hq.le,hqx.trans_le hx.2⟩,hsub ⟨hq.le,hqx⟩⟩
  · rintro ⟨q,hq,hf⟩
    exact ⟨q,mem_insert_of_mem _ ⟨⟨hq.1,hq.2.le.trans hi⟩,hf⟩,hq.2⟩

/-- Right continuity of the filtration in event form. -/
def RightContinuousFiltration {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ m) :=
  ∀ i E, (∀ j, i < j → MeasurableSet[ℱ j] E) → MeasurableSet[ℱ i] E

theorem isStoppingTime_crossingTime {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℝ m) (hℱ : RightContinuousFiltration ℱ)
    {f : Ω → ℝ → ℝ} {r T : ℝ} (hr : r ≤ T) (b : ℝ)
    (hm : ∀ u ∈ Icc r T, Measurable[ℱ u] (fun ω => f ω u))
    (hc : ∀ ω u, u ∈ Ico r T → ContinuousWithinAt (f ω) (Ici u) u) :
    IsStoppingTime ℱ (fun ω => crossingTime (f ω) r T b) := by
  let S := fun ω => crossingTime (f ω) r T b
  have ltMeas (i : ℝ) : MeasurableSet[ℱ i] {ω | S ω < i} := by
    by_cases hi : i ≤ T
    · rw [show {ω | S ω < i} = ⋃ (q : ℚ) (_ : (q : ℝ) ∈ Ico r i), {ω | b < f ω q} by
            ext ω; simp [S,crossingTime_lt_iff hr hi (hc ω)]]
      exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
        ℱ.mono hq.2.le _ (measurableSet_lt measurable_const (hm q ⟨hq.1,hq.2.le.trans hi⟩))
    · rw [show {ω | S ω < i} = univ from eq_univ_of_forall fun ω =>
            (crossingTime_mem (f := f ω) (b := b) hr).2.trans_lt (lt_of_not_ge hi)]
      exact MeasurableSet.univ
  intro i
  apply hℱ
  intro j hij
  rw [show {ω | crossingTime (f ω) r T b ≤ i} =
      ⋂ (q : ℚ) (_ : (q : ℝ) ∈ Ioo i j), {ω | S ω < q} by
        ext ω
        simp only [mem_setOf_eq, mem_iInter]
        constructor
        · exact fun h q hq => h.trans_lt hq.1
        · intro h
          by_contra! hle
          obtain ⟨q,hq,hq'⟩ := exists_rat_btwn (lt_min hij hle)
          exact (not_lt_of_ge (le_of_lt (hq'.trans_le (min_le_right _ _)))) (h q ⟨hq,hq'.trans_le (min_le_left _ _)⟩)]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
    ℱ.mono hq.2.le _ (ltMeas q)


theorem le_threshold_before_crossing {f : ℝ → ℝ} {r T b u : ℝ} (hr : r ≤ T)
    (hu : u ∈ Icc r T) (hlt : u < crossingTime f r T b) : f u ≤ b := by
  by_contra! h
  exact not_le_of_gt hlt (csInf_le ⟨r,crossing_lowerBounds hr⟩ (mem_insert_of_mem _ ⟨hu,h⟩))

theorem threshold_le_at_crossing {f : ℝ → ℝ} {r T b : ℝ} (hr : r ≤ T)
    (hc : ∀ u ∈ Ico r T, ContinuousWithinAt f (Ici u) u) (hit : ∃ u ∈ Icc r T, b < f u) :
    b ≤ f (crossingTime f r T b) := by
  let S := crossingTime f r T b
  have hS : S ∈ Icc r T := crossingTime_mem hr
  obtain ⟨u,hu,hfu⟩ := hit
  have hSu : S ≤ u := csInf_le ⟨r,crossing_lowerBounds hr⟩ (mem_insert_of_mem _ ⟨hu,hfu⟩)
  rcases hSu.eq_or_lt with heq | hlt
  · simpa only [← heq] using hfu.le
  by_contra! h
  obtain ⟨x,hx,hsub⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).1
    ((hc S ⟨hS.1,hlt.trans_le hu.2⟩).tendsto (Iio_mem_nhds h))
  obtain ⟨z,hz,hzx⟩ := exists_lt_of_csInf_lt (insert_nonempty T {u ∈ Icc r T | b < f u}) hx.1
  have hSz : S ≤ z := csInf_le ⟨r,crossing_lowerBounds hr⟩ hz
  rcases hz with rfl | hz
  · exact (hzx.trans_le (hx.2.trans hu.2)).false
  · exact not_le_of_gt hz.2 (show f z < b from hsub ⟨hSz,hzx⟩).le

theorem measurableSet_crossing_hit {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℝ m) {f : Ω → ℝ → ℝ} {r T b : ℝ} (hr : r ≤ T)
    (hb : ∀ ω, BddAbove (f ω '' Icc r T))
    (hm : ∀ u ∈ Icc r T, Measurable[ℱ u] (fun ω => f ω u))
    (hc : ∀ ω u, u ∈ Ico r T → ContinuousWithinAt (f ω) (Ici u) u)
    (hS : IsStoppingTime ℱ (fun ω => crossingTime (f ω) r T b)) :
    MeasurableSet[hS.measurableSpace] {ω | b < intervalSup (f ω) r T} := by
  intro i
  by_cases hi : T ≤ i
  · exact ((ℱ.mono hi) _ (measurableSet_lt measurable_const
      (@measurable_intervalSup Ω (ℱ T) f r T hr hb
        (fun u hu => (hm u hu).mono (ℱ.mono hu.2) le_rfl) hc))).inter (hS i)
  · rw [inter_eq_right.mpr (show {ω | crossingTime (f ω) r T b ≤ i} ⊆ _ from ?_)]
    · exact hS i
    · intro ω hω
      obtain ⟨q,hq,hf⟩ := (crossingTime_lt_iff hr le_rfl (hc ω)).1
        ((show crossingTime (f ω) r T b ≤ i from hω).trans_lt (lt_of_not_ge hi))
      exact (intervalSup_crossing hr (hb ω) (hc ω)).2 (Or.inr ⟨q,⟨hq.1,hq.2.le⟩,hf⟩)

end WeightedBMO
