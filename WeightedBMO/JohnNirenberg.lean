import WeightedBMO.RealJohnNirenberg

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

/-- Event form of weighted BMO with bound B (Definition 1.2).
The stopped weight is positive and known at S. -/
def WeightedBMOOn {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℝ m) (v vLeft φ : Ω → ℝ → ℝ) (a T B : ℝ) :=
  0 ≤ B ∧ ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
    (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
    ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
      (∫⁻ ω in G, ENNReal.ofReal (|v ω (U ω) - vLeft ω (S ω)| / φ ω (S ω)) ∂μ) ≤
        ENNReal.ofReal B * μ G

/-- The least nonnegative uniform bound for all stopped oscillation tests. -/
noncomputable def oscillationModulus {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℝ m) (v vLeft φ : Ω → ℝ → ℝ) (s t : ℝ) :=
  sInf {c | 0 ≤ c ∧ StoppedOscillationBound μ ℱ v vLeft φ s t c}

private theorem stoppedBound_of_bmo {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : Filtration ℝ m} {v vLeft φ : Ω → ℝ → ℝ} {a T s t B : ℝ}
    (h : WeightedBMOOn μ ℱ v vLeft φ a T B) (ha : a ≤ s) (ht : t ≤ T)
    (hp : ∀ ω u, u ∈ Icc a T → 0 < φ ω u) (hw : ∀ ω, BddAbove (φ ω '' Icc a T)) :
    StoppedOscillationBound μ ℱ v vLeft φ s t B := by
  intro S U hS hU hs hsu hu G hG
  apply le_trans (lintegral_mono _) (h.2 S U hS hU (fun ω => ha.trans (hs ω)) hsu
    (fun ω => (hu ω).trans ht) G hG)
  intro ω
  have hl := ha.trans (hs ω)
  have hh := (hu ω).trans ht
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (abs_nonneg _)
    (hp ω _ ⟨hl,(hsu ω).trans hh⟩) (le_intervalSup ((hw ω).mono (image_mono (Icc_subset_Icc hl hh)))
      (left_mem_Icc.mpr (hsu ω))))

private theorem stoppedBound_of_modulus {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {ℱ : Filtration ℝ m} {v vLeft φ : Ω → ℝ → ℝ} {s t B c : ℝ}
    (hB : 0 ≤ B) (hb : StoppedOscillationBound μ ℱ v vLeft φ s t B)
    (hc : oscillationModulus μ ℱ v vLeft φ s t ≤ c) : StoppedOscillationBound μ ℱ v vLeft φ s t c := by
  intro S U hS hU hs hsu hu G hG
  let I := ∫⁻ ω in G, ENNReal.ofReal (|v ω (U ω) - vLeft ω (S ω)| / intervalSup (φ ω) (S ω) (U ω)) ∂μ
  have hi : I ≤ ENNReal.ofReal B * μ G := hb S U hS hU hs hsu hu G hG
  have hfin := hi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  by_cases hG0 : μ G = 0
  · simpa only [hG0,mul_zero] using hi.trans_eq (by simp [hG0] : ENNReal.ofReal B * μ G = ENNReal.ofReal c * μ G)
  have hpos := ENNReal.toReal_pos hG0 (measure_ne_top μ G)
  have hlow : I.toReal / (μ G).toReal ≤ oscillationModulus μ ℱ v vLeft φ s t := by
    unfold oscillationModulus
    apply le_csInf (s := {d | 0 ≤ d ∧ StoppedOscillationBound μ ℱ v vLeft φ s t d}) ⟨B,hB,hb⟩
    intro d hd
    have he := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ G)).ne
      (hd.2 S U hS hU hs hsu hu G hG)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.1] at he
    exact (div_le_iff₀ hpos).2 he
  have hreal := (div_le_iff₀ hpos).1 (hlow.trans hc)
  have hc0 : 0 ≤ c := (div_nonneg ENNReal.toReal_nonneg hpos.le).trans (hlow.trans hc)
  change I ≤ _
  rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_toReal (measure_ne_top μ G),
    ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal hreal

/-- A real càdlàg path on a compact time interval is bounded. -/
theorem cadlag_bounded {f : ℝ → ℝ} {a T : ℝ}
    (hc : ∀ u ∈ Ico a T, ContinuousWithinAt f (Ici u) u)
    (hl : ∀ u ∈ Ioc a T, ∃ l, Tendsto f (𝓝[<] u) (𝓝 l)) :
    BddAbove ((fun u => |f u|) '' Icc a T) := by
  apply isCompact_Icc.induction_on (p := fun s => BddAbove ((fun u => |f u|) '' s))
  · simp
  · exact fun _ _ h hb => hb.mono (image_mono h)
  · intro s t hs ht
    simpa [image_union] using hs.union ht
  intro x hx
  obtain ⟨l, hleft⟩ : ∃ l : ℝ, ∀ᶠ u in 𝓝[Icc a T ∩ Iio x] x, |f u| ≤ l := by
    rcases hx.1.eq_or_lt with he | hlt
    · have heq : Icc a T ∩ Iio x = ∅ := eq_empty_iff_forall_not_mem.2 fun u h =>
        (not_lt_of_ge (he ▸ h.1.1)) h.2
      exact ⟨0,by simp [heq]⟩
    obtain ⟨l,hl⟩ := hl x ⟨hlt,hx.2⟩
    exact ⟨|l|+1, ((hl.abs.eventually (ge_mem_nhds (by linarith : |l| < |l|+1)))).filter_mono
      (nhdsWithin_mono _ inter_subset_right)⟩
  obtain ⟨d, hright⟩ : ∃ d : ℝ, ∀ᶠ u in 𝓝[Icc a T ∩ Ici x] x, |f u| ≤ d := by
    rcases hx.2.eq_or_lt with he | hlt
    · exact ⟨|f x|, mem_of_superset self_mem_nhdsWithin fun u hu => by
        have eq : u = x := le_antisymm (hu.1.2.trans he.ge) hu.2
        simp [eq]⟩
    exact ⟨|f x|+1, (((hc x ⟨hx.1,hlt⟩).tendsto.abs.eventually
      (ge_mem_nhds (by linarith : |f x| < |f x|+1)))).filter_mono (nhdsWithin_mono _ inter_subset_right)⟩
  let U := {u | |f u| ≤ max l d}
  refine ⟨U, ?_, ⟨max l d, ?_⟩⟩
  · have eq : Icc a T = (Icc a T ∩ Iio x) ∪ (Icc a T ∩ Ici x) := by
      rw [← inter_union_distrib_left,Iio_union_Ici,inter_univ]
    rw [eq,nhdsWithin_union]
    exact ⟨hleft.mono (fun _ h => h.trans (le_max_left _ _)),
      hright.mono (fun _ h => h.trans (le_max_right _ _))⟩
  · rintro _ ⟨u,hu,rfl⟩
    exact hu

/-- The small-scale oscillation modulus in (1.10). -/
noncomputable def smallScaleModulus (ρ : ℝ → ℝ → ℝ) (a T : ℝ) :=
  sInf (smallScaleBounds ρ a T)

/-- Supremum of oscillations on subintervals of length at most h. -/
noncomputable def meshOscillation (ρ : ℝ → ℝ → ℝ) (a T h : ℝ) :=
  sSup {z | ∃ s t, a ≤ s ∧ s ≤ t ∧ t ≤ T ∧ t-s ≤ h ∧ z = ρ s t}

/-- The infimum of local upper bounds equals the paper's right-hand mesh limit. -/
theorem tendsto_meshOscillation {ρ : ℝ → ℝ → ℝ} {a T B : ℝ} (ha : a ≤ T)
    (h0 : ∀ s t, a ≤ s → s ≤ t → t ≤ T → 0 ≤ ρ s t)
    (hB : ∀ s t, a ≤ s → s ≤ t → t ≤ T → ρ s t ≤ B) :
    Tendsto (meshOscillation ρ a T) (𝓝[>] (0 : ℝ)) (𝓝 (smallScaleModulus ρ a T)) := by
  let A (h : ℝ) : Set ℝ := {z | ∃ s t, a ≤ s ∧ s ≤ t ∧ t ≤ T ∧ t-s ≤ h ∧ z = ρ s t}
  have bounded h : BddAbove (A h) := by
    refine ⟨B,?_⟩
    rintro _ ⟨s,t,hs,hst,ht,_,rfl⟩
    exact hB s t hs hst ht
  have diag h (hh : 0 ≤ h) : ρ a a ∈ A h := ⟨a,a,le_rfl,le_rfl,ha,by simpa using hh,rfl⟩
  have hb : (smallScaleBounds ρ a T).Nonempty := ⟨B,(h0 a a le_rfl le_rfl ha).trans
    (hB a a le_rfl le_rfl ha),1,zero_lt_one,fun s t hs hst ht _ => hB s t hs hst ht⟩
  apply tendsto_order.2
  constructor
  · intro d hd
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hm : sSup (A h) ∈ smallScaleBounds ρ a T := by
      refine ⟨(h0 a a le_rfl le_rfl ha).trans (le_csSup (bounded h) (diag h hh'.le)),h,hh',?_⟩
      intro s t hs hst ht hlen
      exact le_csSup (bounded h) ⟨s,t,hs,hst,ht,hlen,rfl⟩
    exact hd.trans_le (csInf_le ⟨0,fun d hd => hd.1⟩ hm)
  · intro d hd
    obtain ⟨c,hc,hcd⟩ := exists_lt_of_csInf_lt hb hd
    obtain ⟨_,δ,hδ,hmesh⟩ := hc
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with h hpos hlt
    apply lt_of_le_of_lt _ hcd
    apply csSup_le ⟨_,diag h (le_of_lt (show 0 < h from hpos))⟩
    rintro _ ⟨s,t,hs,hst,ht,hlen,rfl⟩
    exact hmesh s t hs hst ht (hlen.trans (le_of_lt (show h < δ from hlt)))

/-- Equation (1.10) on [a,T] for a weighted BMO process, including the endpoint rate.
The stopping-time BMO hypothesis is in initial-event integral form. -/
theorem weightedBMO_exponential {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℝ m) (hℱ : RightContinuousFiltration ℱ)
    (v vLeft φ : Ω → ℝ → ℝ) {a T rate B : ℝ}
    (hB : WeightedBMOOn μ ℱ v vLeft φ a T B)
    (hp : ∀ ω u, u ∈ Icc a T → 0 < φ ω u)
    (mv : ∀ u ∈ Icc a T, Measurable[ℱ u] (fun ω => v ω u))
    (mw : ∀ u ∈ Icc a T, Measurable[ℱ u] (fun ω => φ ω u))
    (cv : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (v ω) (Ici u) u)
    (cw : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (φ ω) (Ici u) u)
    (lv : ∀ ω u, u ∈ Ioc a T → Tendsto (v ω) (𝓝[<] u) (𝓝 (vLeft ω u)))
    (lw : ∀ ω u, u ∈ Ioc a T → ∃ l, Tendsto (φ ω) (𝓝[<] u) (𝓝 l))
    (hend : rate * smallScaleModulus (oscillationModulus μ ℱ v vLeft φ) a T ≤ Real.exp (-3)) :
    (⨆ r : Icc a T, eLpNorm
      (μ[fun ω => Real.exp (rate * normalizedMaximum (v ω) (φ ω) r T)|ℱ r]) ⊤ μ) < ⊤ := by
  have hv ω := cadlag_bounded (cv ω) (fun u hu => ⟨_,lv ω u hu⟩)
  have hw ω : BddAbove (φ ω '' Icc a T) := by
    obtain ⟨d,hd⟩ := cadlag_bounded (cw ω) (lw ω)
    refine ⟨d,?_⟩
    rintro _ ⟨u,hu,rfl⟩
    exact (le_abs_self _).trans (hd (mem_image_of_mem _ hu))
  have bound s t (ha : a ≤ s) (ht : t ≤ T) := stoppedBound_of_bmo hB (s := s) (t := t) ha ht hp hw
  apply path_exponential_of_interval_moments μ ℱ v φ (oscillationModulus μ ℱ v vLeft φ)
    hv hw hp mv mw cv cw _ _ hend
  · intro s t ha hst ht c hc hρ E hE n hn
    have sub : Icc s t ⊆ Icc a T := Icc_subset_Icc ha ht
    exact real_interval_moments μ ℱ hℱ v vLeft φ hst hc (by exact_mod_cast hn)
      (fun ω => (hv ω).mono (image_mono sub)) (fun ω => (hw ω).mono (image_mono sub))
      (fun ω u hu => hp ω u (sub hu)) (fun u hu => mv u (sub hu)) (fun u hu => mw u (sub hu))
      (fun ω u hu => cv ω u ⟨ha.trans hu.1,hu.2.trans_le ht⟩)
      (fun ω u hu => cw ω u ⟨ha.trans hu.1,hu.2.trans_le ht⟩)
      (fun ω u hu => lv ω u ⟨ha.trans_lt hu.1,hu.2.trans ht⟩)
      (stoppedBound_of_modulus hB.1 (bound s t ha ht) hρ) hE
  · refine ⟨B,hB.1,1,zero_lt_one,?_⟩
    intro s t ha _ ht _
    exact csInf_le ⟨0, fun d hd => hd.1⟩ ⟨hB.1,bound s t ha ht⟩

end WeightedBMO
