import WeightedBMO.ContinuousDoob
import WeightedBMO.SupermartingaleWeakType

/-!
# Dyadic lift of the weak-type maximal inequality

`supermartingale_max_le_of_measurableSet_zero` gives the weak-type inequality
for a nonnegative supermartingale on a finite grid, tested on an event of
`ℱ 0`.  Here it is lifted to the supremum over a real interval: for `α > 0` and
`G` measurable at time `0`,

  `α · μ({α < sup_t M_t} ∩ G) ≤ ∫_G M_0`,

where `supOn M T` is the supremum over the dyadic grids of `[0,T]` (equal to the
supremum over `[0,T]` for right-continuous paths, by `ofReal_le_supOn`).

Each dyadic grid carries a finite-time supermartingale — the sampled process
`k ↦ M(kT/2^n)` with the filtration `ℱ(kT/2^n)` — so the discrete inequality
applies at every scale.  The localisation `1_G · M` is carried out *on the
discrete grid*, where all the sample times `kT/2^n` are `≥ 0`; this is what
makes the argument work, since an event of `ℱ 0` need not be measurable with
respect to `ℱ t` for `t < 0`, so `1_G · M` is not a supermartingale indexed by
all of `ℝ`.

The sets `{α < max over the n-th grid} ∩ G` increase to
`{α < sup_t M_t} ∩ G` because `α < ⨆ n x_n` implies `α < x_n` for some `n`, and
`μ` is continuous from below.  The strict inequality `<` is what the
layer-cake formula consumes.

The special case `G = Ω` is `supermartingale_max_le_supOn`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ m}

/-- **The dyadic lift, tested on an event of `ℱ 0`.** -/
theorem supermartingale_max_le_supOn_of_measurableSet_zero [SigmaFiniteFiltration μ ℱ]
    {M : ℝ → Ω → ℝ} (hM : Supermartingale M ℱ μ) {T : ℝ} (hT : 0 ≤ T)
    (hM0 : ∀ t ω, t ∈ Icc 0 T → 0 ≤ M t ω) {α : ℝ} (hα : 0 < α) {G : Set Ω}
    (hG : MeasurableSet[ℱ 0] G) :
    ENNReal.ofReal α * μ ({ω | ENNReal.ofReal α < supOn M T ω} ∩ G) ≤
      ENNReal.ofReal (∫ ω in G, M 0 ω ∂μ) := by
  have hgrid : ∀ n : ℕ, ENNReal.ofReal α *
      μ ({ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)} ∩ G) ≤
      ENNReal.ofReal (∫ ω in G, M 0 ω ∂μ) := by
    intro n
    set t : ℕ → ℝ := fun k => min (dyadicTime T n k) T with ht
    have htmono : Monotone t := by
      intro i j hij
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      simp only [t, dyadicTime]
      exact min_le_min (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hij' hT)
        (by positivity)) le_rfl
    set 𝒢 : Filtration ℕ m :=
      ⟨fun k => ℱ (t k), fun i j hij => ℱ.mono (htmono hij), fun k => ℱ.le (t k)⟩ with h𝒢
    set X : ℕ → Ω → ℝ := fun k => M (t k) with hX
    have hXsup : Supermartingale X 𝒢 μ := by
      refine ⟨fun k => hM.adapted (t k), ?_, fun k => hM.integrable (t k)⟩
      intro i j hij
      exact hM.2.1 (t i) (t j) (htmono hij)
    have ht0 : t 0 = 0 := by
      simp only [t, dyadicTime, Nat.cast_zero, zero_mul, zero_div]
      exact min_eq_left hT
    have hG' : MeasurableSet[𝒢 0] G := by
      show MeasurableSet[ℱ (t 0)] G
      rw [ht0]
      exact hG
    have htmem : ∀ k : ℕ, t k ∈ Icc 0 T := by
      intro k
      refine ⟨?_, ?_⟩
      · simp only [t, dyadicTime]
        positivity
      · exact min_le_right _ _
    have hmain := supermartingale_max_le_of_measurableSet_zero (ℱ := 𝒢) (X := X) hXsup
      (fun k ω => hM0 (t k) ω (htmem k)) hα (2 ^ n) (G := G) hG'
    have htmin : ∀ k ≤ 2 ^ n, t k = dyadicTime T n k := by
      intro k hk
      simp only [t]
      apply min_eq_left
      have hpos : (0:ℝ) < (2:ℝ) ^ n := by positivity
      have hk' : (k : ℝ) ≤ (2:ℝ) ^ n := by
        have hk'' : ((k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hk
        simpa using hk''
      rw [dyadicTime]
      refine (div_le_iff₀ hpos).2 ?_
      calc (k : ℝ) * T ≤ (2:ℝ) ^ n * T := mul_le_mul_of_nonneg_right hk' hT
        _ = T * (2:ℝ) ^ n := by ring
    have hsub : subMax X (2 ^ n) = dyadicMax M T n := by
      funext ω
      apply le_antisymm
      · apply Finset.sup'_le
        intro k hk
        have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (by simpa using hk)
        show M (t k) ω ≤ dyadicMax M T n ω
        rw [htmin k hk']
        exact Finset.le_sup' (f := fun k => M (dyadicTime T n k) ω) hk
      · apply Finset.sup'_le
        intro k hk
        have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (by simpa using hk)
        show M (dyadicTime T n k) ω ≤ subMax X (2 ^ n) ω
        rw [← htmin k hk']
        exact Finset.le_sup' (f := fun k => X k ω) hk
    have hX0 : X 0 = M 0 := by
      funext ω
      show M (t 0) ω = M 0 ω
      rw [ht0]
    rw [hsub, hX0] at hmain
    -- a strict `ofReal` bound implies the non-strict real bound
    refine le_trans (mul_le_mul_left' (measure_mono ?_) _) hmain
    refine Set.inter_subset_inter ?_ subset_rfl
    intro ω hω
    simp only [mem_setOf_eq] at hω ⊢
    by_contra hcon
    push_neg at hcon
    exact absurd hω (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon.le))
  -- pass to the supremum, keeping the intersection with `G`
  have hsets : ∀ n, MeasurableSet {ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)} :=
    fun n => measurableSet_lt measurable_const
      ((measurable_dyadicMax (fun t => (hM.adapted t).measurable.mono (ℱ.le t) le_rfl) T n).ennreal_ofReal)
  have hmono : Monotone fun n => {ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)} := by
    intro i j hij ω
    simp only [mem_setOf_eq]
    exact fun h => lt_of_lt_of_le h (ENNReal.ofReal_le_ofReal (dyadicMax_mono ω hij))
  have hunion : (⋃ n, {ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)}) =
      {ω | ENNReal.ofReal α < supOn M T ω} := by
    ext ω
    simp only [mem_iUnion, mem_setOf_eq, supOn]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le hn (le_iSup (fun n => ENNReal.ofReal (dyadicMax M T n ω)) n)
    · intro h
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp h
      exact ⟨n, hn⟩
  have hunionG : (⋃ n, {ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)} ∩ G) =
      {ω | ENNReal.ofReal α < supOn M T ω} ∩ G := by
    rw [← Set.iUnion_inter, hunion]
  have hmonoG : Monotone fun n => {ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)} ∩ G :=
    fun i j hij => Set.inter_subset_inter (hmono hij) subset_rfl
  have hlim : ENNReal.ofReal α * μ ({ω | ENNReal.ofReal α < supOn M T ω} ∩ G) =
      ⨆ n, ENNReal.ofReal α *
        μ ({ω | ENNReal.ofReal α < ENNReal.ofReal (dyadicMax M T n ω)} ∩ G) := by
    rw [← hunionG, hmonoG.measure_iUnion, ENNReal.mul_iSup]
  rw [hlim]
  exact iSup_le hgrid

/-- **Dyadic lift of the global weak-type inequality.** -/
theorem supermartingale_max_le_supOn [SigmaFiniteFiltration μ ℱ]
    {M : ℝ → Ω → ℝ} (hM : Supermartingale M ℱ μ) {T : ℝ} (hT : 0 ≤ T)
    (hM0 : ∀ t ω, t ∈ Icc 0 T → 0 ≤ M t ω) {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal α * μ {ω | ENNReal.ofReal α < supOn M T ω} ≤
      ENNReal.ofReal (∫ ω, M 0 ω ∂μ) := by
  have h := supermartingale_max_le_supOn_of_measurableSet_zero hM hT hM0 hα
    (G := univ) MeasurableSet.univ
  simpa using h

end WeightedBMO
