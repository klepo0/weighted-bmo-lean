import WeightedBMO.DoobMaximal

/-!
# The global weak-type maximal inequality for a nonnegative supermartingale

Mathlib has the weak-type maximal inequality for nonnegative *sub*martingales
(`MeasureTheory.maximal_ineq`) but not for supermartingales.  This file supplies
the discrete-time supermartingale form, which is the input to the
`p < 1` (`est.Smax01`) branch of Theorem 1.1 in Khoa Lê,
*Maximal inequalities, weighted BMO processes and the largest-jump normaliser* (arXiv:2211.15550):

  `α · μ{α ≤ max_{k ≤ N} X_k} ≤ ∫ X_0`  for `α > 0`.

The proof is the first-passage argument.  Let `S` be the first index at which
`X` reaches `α` (capped at `N`), so that `{α ≤ max_{k≤N} X_k}` is the event
`{S ≤ N}` and `X_S ≥ α` there.  Then `∫ X_S ≤ ∫ X_0` by optional stopping at
the bounded stopping time `S`, which mathlib provides for submartingales
(`Submartingale.expected_stoppedValue_mono`); applying it to `-X`, a
submartingale because `X` is a supermartingale, gives the inequality.  All the
bookkeeping about the stopped value (`measurability`, `integrability`,
`stoppedValue X S = X ∘ S`) is inherited from mathlib's API, and the only new
content is that `S` *is* a stopping time:
`{S ≤ n} = {∃ k ≤ n, α ≤ X k}`, which is known at time `n`.

The `p < 1` branch of Theorem 1.1 needs the *event-tested* form of this
inequality, with the right-hand side integrated over the event:

  `α μ({sup X > α} ∩ G) ≤ ∫_G X₀`  for `G` measurable at time `0`.

That is `supermartingale_max_le_of_measurableSet_zero` below.  It is not a
consequence of the global inequality alone (the global one integrates over all
of `Ω`, and `‖·‖_p ≤ ‖·‖₁` would lose the sharp constant).  The proof localises
the process: `ind = 1_G` is `ℱ 0`-measurable, hence `ℱ k`-measurable for every
`k`, so `MG k = ind * X k` is again a supermartingale by the pull-out property
of the conditional expectation (`condExp_mul_of_stronglyMeasurable_left`), and
the global inequality applied to `MG` *is* the tested one, because
`{α ≤ max MG} = {α ≤ max X} ∩ G` (`ind * M` vanishes off `G` and `α > 0`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {X : ℕ → Ω → ℝ}

/-- The event of having passed the level `α` by time `n`. -/
def passed (α : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) : Set Ω := {ω | ∃ k ≤ n, α ≤ X k ω}

theorem measurableSet_passed {α : ℝ} (hXa : ∀ k, Measurable[ℱ k] (X k)) (n : ℕ) :
    MeasurableSet[ℱ n] (passed α X n) := by
  have h : passed α X n = ⋃ k ∈ Finset.range (n + 1), {ω | α ≤ X k ω} := by
    ext ω
    simp only [passed, mem_setOf_eq, mem_iUnion, exists_prop, Finset.mem_range]
    exact ⟨fun ⟨k, hk, hα⟩ => ⟨k, Nat.lt_succ_of_le hk, hα⟩,
      fun ⟨k, hk, hα⟩ => ⟨k, Nat.lt_succ_iff.mp hk, hα⟩⟩
  rw [h]
  refine Finset.measurableSet_biUnion _ (fun k hk => ?_)
  exact ((hXa k).mono (ℱ.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) le_rfl)
    measurableSet_Ici

omit m in
theorem passed_eq_subMax {α : ℝ} (n : ℕ) : passed α X n = {ω | α ≤ subMax X n ω} := by
  ext ω
  constructor
  · rintro ⟨k, hk, hα⟩
    exact hα.trans (Finset.le_sup' (f := fun k => X k ω) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  · intro h
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_succ (fun k => X k ω)
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), by rw [← hkeq]; exact h⟩

/-- The first index at which `X` reaches `α`, capped at `N`. -/
noncomputable def firstPassage (α : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ k, k ≤ N ∧ α ≤ X k ω then Nat.find h else N

omit m in
theorem firstPassage_le (N : ℕ) (ω : Ω) : firstPassage α X N ω ≤ N := by
  unfold firstPassage
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

omit m in
theorem firstPassage_pass (N : ℕ) (ω : Ω) (hω : ∃ k, k ≤ N ∧ α ≤ X k ω) :
    α ≤ X (firstPassage α X N ω) ω := by
  unfold firstPassage
  rw [dif_pos hω]
  exact (Nat.find_spec hω).2

omit m in
theorem firstPassage_le_iff (N : ℕ) (ω : Ω) (n : ℕ) (hn : n < N) :
    firstPassage α X N ω ≤ n ↔ ∃ k ≤ n, α ≤ X k ω := by
  unfold firstPassage
  by_cases hex : ∃ k, k ≤ N ∧ α ≤ X k ω
  · rw [dif_pos hex, Nat.find_le_iff]
    constructor
    · rintro ⟨m, hm, hN, hαm⟩
      exact ⟨m, hm, hαm⟩
    · rintro ⟨k, hk, hαk⟩
      exact ⟨k, hk, hk.trans hn.le, hαk⟩
  · rw [dif_neg hex]
    constructor
    · intro h
      exact absurd h (not_le.mpr hn)
    · rintro ⟨k, hk, hαk⟩
      exact absurd ⟨k, hk.trans hn.le, hαk⟩ hex


omit [IsFiniteMeasure μ] in
/-- **Global weak-type maximal inequality for a nonnegative supermartingale.**
First-passage argument, with optional stopping taken from mathlib. -/
theorem supermartingale_max_le [SigmaFiniteFiltration μ ℱ]
    (hX : Supermartingale X ℱ μ) (hX0 : ∀ k ω, 0 ≤ X k ω)
    {α : ℝ} (_hα : 0 < α) (N : ℕ) :
    ENNReal.ofReal α * μ {ω | α ≤ subMax X N ω} ≤
      ENNReal.ofReal (∫ ω, X 0 ω ∂μ) := by
  classical
  have hS_eq : ∀ n, n < N → {ω | firstPassage α X N ω ≤ n} = passed α X n := by
    intro n hn
    ext ω
    exact firstPassage_le_iff N ω n hn
  have hS_stop : IsStoppingTime ℱ (firstPassage α X N) := by
    intro n
    by_cases hn : n < N
    · rw [hS_eq n hn]
      exact measurableSet_passed (fun k => (hX.adapted k).measurable) n
    · have heq : {ω | firstPassage α X N ω ≤ n} = univ := by
        ext ω
        simp only [mem_setOf_eq, mem_univ, iff_true]
        exact le_trans (firstPassage_le N ω) (le_of_not_gt hn)
      rw [heq]
      exact MeasurableSet.univ
  -- the stopped value is the value at the passage time
  have hSval : stoppedValue X (firstPassage α X N) =
      fun ω => X (firstPassage α X N ω) ω := rfl
  -- optional stopping for the supermartingale
  have hmono := Submartingale.expected_stoppedValue_mono (f := -X) (τ := fun _ => 0)
    (π := firstPassage α X N) (N := N) hX.neg (isStoppingTime_const ℱ 0) hS_stop
    (fun ω => Nat.zero_le _) (fun ω => firstPassage_le N ω)
  have hzero : stoppedValue (-X) (fun _ : Ω => 0) = fun ω => -X 0 ω := by
    rw [stoppedValue_const]; rfl
  have hSneg : stoppedValue (-X) (firstPassage α X N) =
      fun ω => -X (firstPassage α X N ω) ω := by
    funext ω
    rfl
  have hXint : ∫ ω, X (firstPassage α X N ω) ω ∂μ ≤ ∫ ω, X 0 ω ∂μ := by
    rw [hzero, hSneg, integral_neg, integral_neg] at hmono
    linarith
  have hS_int : Integrable (fun ω => X (firstPassage α X N ω) ω) μ := by
    have h := Submartingale.integrable_stoppedValue hX.neg hS_stop
      (N := N) (fun ω => firstPassage_le N ω)
    rw [hSneg] at h
    have h2 := h.neg
    have h3 : -(fun ω => -X (firstPassage α X N ω) ω) =
        fun ω => X (firstPassage α X N ω) ω := by
      funext ω
      simp
    rwa [h3] at h2
  -- assembly
  have hAeq : {ω | α ≤ subMax X N ω} = passed α X N := (passed_eq_subMax (X := X) (α := α) N).symm
  have hAmeas : MeasurableSet {ω | α ≤ subMax X N ω} := by
    have h := measurableSet_passed (X := X) (α := α) (fun k => (hX.adapted k).measurable) N
    rw [passed_eq_subMax (X := X) (α := α) N] at h
    exact ℱ.le N _ h
  have hstep : ∀ ω ∈ {ω | α ≤ subMax X N ω}, ω ∈ passed α X N := by
    intro ω hω
    rw [← hAeq]
    exact hω
  have step1 : ENNReal.ofReal α * μ {ω | α ≤ subMax X N ω} ≤
      ∫⁻ ω, ENNReal.ofReal (X (firstPassage α X N ω) ω) ∂μ := by
    rw [show ENNReal.ofReal α * μ {ω | α ≤ subMax X N ω} =
        ∫⁻ ω in {ω | α ≤ subMax X N ω}, ENNReal.ofReal α ∂μ from by
          rw [lintegral_const, Measure.restrict_apply_univ]]
    calc ∫⁻ ω in {ω | α ≤ subMax X N ω}, ENNReal.ofReal α ∂μ
        ≤ ∫⁻ ω in {ω | α ≤ subMax X N ω}, ENNReal.ofReal (X (firstPassage α X N ω) ω) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hAmeas] with ω hω
          exact ENNReal.ofReal_le_ofReal (firstPassage_pass N ω (hstep ω hω))
      _ ≤ ∫⁻ ω, ENNReal.ofReal (X (firstPassage α X N ω) ω) ∂μ := by
          simpa using lintegral_mono_set (subset_univ {ω | α ≤ subMax X N ω})
            (f := fun ω => ENNReal.ofReal (X (firstPassage α X N ω) ω))
  calc ENNReal.ofReal α * μ {ω | α ≤ subMax X N ω}
      ≤ ∫⁻ ω, ENNReal.ofReal (X (firstPassage α X N ω) ω) ∂μ := step1
    _ = ENNReal.ofReal (∫ ω, X (firstPassage α X N ω) ω ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hS_int
          (ae_of_all _ fun ω => hX0 _ ω)).symm
    _ ≤ ENNReal.ofReal (∫ ω, X 0 ω ∂μ) := ENNReal.ofReal_le_ofReal hXint


omit [IsFiniteMeasure μ] in
/-- **Weak-type inequality tested on an event of `ℱ 0`.**  The global inequality
applied to the localised process `1_G · X`. -/
theorem supermartingale_max_le_of_measurableSet_zero {ℱ : Filtration ℕ m} {X : ℕ → Ω → ℝ}
    [SigmaFiniteFiltration μ ℱ]
    (hX : Supermartingale X ℱ μ) (hX0 : ∀ k ω, 0 ≤ X k ω)
    {α : ℝ} (hα : 0 < α) (N : ℕ) {G : Set Ω} (hG : MeasurableSet[ℱ 0] G) :
    ENNReal.ofReal α * μ ({ω | α ≤ subMax X N ω} ∩ G) ≤
      ENNReal.ofReal (∫ ω in G, X 0 ω ∂μ) := by
  classical
  set ind : Ω → ℝ := G.indicator (fun _ => 1) with hind
  set MG : ℕ → Ω → ℝ := fun k ω => ind ω * X k ω with hMG
  have hGm : MeasurableSet G := ℱ.le 0 G hG
  have hind_eq : ∀ ω, ind ω = if ω ∈ G then 1 else 0 := by
    intro ω
    rw [hind]
    by_cases h : ω ∈ G
    · rw [Set.indicator_of_mem h]; simp [h]
    · rw [Set.indicator_of_not_mem h]; simp [h]
  have hind_nonneg : ∀ ω, 0 ≤ ind ω := fun ω => by rw [hind_eq ω]; split_ifs <;> norm_num
  have hind_sm : ∀ k : ℕ, StronglyMeasurable[ℱ k] ind := fun k =>
    StronglyMeasurable.indicator stronglyMeasurable_const ((ℱ.mono (Nat.zero_le k)) G hG)
  have hMG_nonneg : ∀ k ω, 0 ≤ MG k ω := fun k ω =>
    mul_nonneg (hind_nonneg ω) (hX0 k ω)
  have hMG_eq : ∀ k, MG k = G.indicator (X k) := by
    intro k
    funext ω
    simp only [hMG, hind_eq ω, Set.indicator_apply]
    by_cases h : ω ∈ G <;> simp [h]
  have hMG_int : ∀ k, Integrable (MG k) μ := by
    intro k
    rw [hMG_eq k]
    exact (hX.integrable k).indicator hGm
  have hMG_adapted : Adapted ℱ MG := fun k => by
    rw [hMG_eq k]
    exact StronglyMeasurable.indicator (hX.adapted k) ((ℱ.mono (Nat.zero_le k)) G hG)
  have hMG_sup : Supermartingale MG ℱ μ := by
    refine ⟨hMG_adapted, ?_, hMG_int⟩
    intro i j hij
    have hstep : μ[MG j | ℱ i] =ᵐ[μ] fun ω => ind ω * μ[X j | ℱ i] ω := by
      have h := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (μ := μ)
        (f := ind) (g := X j) (hind_sm i) (by simpa [hMG] using hMG_int j) (hX.integrable j)
      simpa [hMG, Pi.mul_apply] using h
    filter_upwards [hstep, hX.condExp_ae_le hij] with ω h1 h2
    rw [h1, hMG]
    exact mul_le_mul_of_nonneg_left h2 (hind_nonneg ω)
  have hmain := supermartingale_max_le (X := MG) hMG_sup hMG_nonneg hα N
  -- identify the two sides
  have hkey : ∀ ω ∈ G, subMax MG N ω = subMax X N ω := by
    intro ω hω
    have hfun : (fun k => MG k ω) = (fun k => X k ω) := by
      funext k
      simp only [hMG, hind_eq ω, if_pos hω, one_mul]
    simp only [subMax, hfun]
  have hzero : ∀ ω ∉ G, subMax MG N ω = 0 := by
    intro ω hω
    refine le_antisymm ?_ (subMax_nonneg hMG_nonneg N ω)
    refine Finset.sup'_le _ _ fun k _ => ?_
    simp only [hMG, hind_eq ω, if_neg hω, zero_mul, le_refl]
  have hset : {ω | α ≤ subMax MG N ω} = {ω | α ≤ subMax X N ω} ∩ G := by
    ext ω
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · intro h
      by_cases hω : ω ∈ G
      · exact ⟨hkey ω hω ▸ h, hω⟩
      · rw [hzero ω hω] at h; linarith
    · rintro ⟨h1, h2⟩
      exact (hkey ω h2).symm ▸ h1
  have hMG0 : ∫ ω, MG 0 ω ∂μ = ∫ ω in G, X 0 ω ∂μ := by
    rw [hMG_eq 0, integral_indicator hGm]
  rw [hset, hMG0] at hmain
  exact hmain

end WeightedBMO
