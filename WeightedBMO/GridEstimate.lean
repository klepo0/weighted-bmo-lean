import WeightedBMO.GoodLambda
import WeightedBMO.FirstCrossing

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

/-- A finite-grid maximal estimate under a stopped-increment integral bound.
The probability measure can be restricted to an initial event. The path
`v` is centered at the start of the grid. The positive pair weight `D`
bounds the stopped increment in conditional mean on every stopped event.
The envelope `w` controls the denominator of the maximum; `X` bounds
the ratio of the pair weight to that envelope. -/
theorem grid_maximal_eLpNorm_le {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (N : ℕ)
    (v w : ℕ → Ω → ℝ) (D : ℕ → ℕ → Ω → ℝ) {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hX₀ : ∀ ω, 0 ≤ X ω)
    (hY₀ : ∀ ω, 0 ≤ Y ω) (hv : ∀ ω, v 0 ω = 0)
    (hw : ∀ ω, Monotone (fun i => w i ω)) (hw₀ : ∀ i ω, 0 < w i ω)
    (had : ∀ t i, MeasurableSet[ℱ i] {ω | t * w i ω < |v i ω|})
    (hmax : ∀ t ω, t < Y ω ↔ ∃ i ≤ N, t * w i ω < |v i ω|)
    (hD : ∀ i j ω, i ≤ j → j ≤ N → 0 < D i j ω ∧ D i j ω ≤ X ω * w j ω)
    (hmean : ∀ (S T : Ω → ℕ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ T →
      (∀ ω, S ω ≤ T ω) → (∀ ω, T ω ≤ N) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫⁻ ω in G, ENNReal.ofReal (|v (T ω) ω - v (S ω - 1) ω| / D (S ω) (T ω) ω) ∂μ)
          ≤ μ G)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm Y (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (goodLambdaConstant p) * eLpNorm X (ENNReal.ofReal p) μ := by
  apply goodLambda_eLpNorm_le μ hX hY hX₀ hY₀ hp
  intro a b θ ha hb hθ _
  let A (t : ℝ) (i : ℕ) := {ω | t * w i ω < |v i ω|}
  let H (t : ℝ) := {ω | t < Y ω}
  let τ (t : ℝ) (ω : Ω) := firstCrossing N (fun i => ω ∈ A t i)
  have hτ (t : ℝ) : IsStoppingTime ℱ (τ t) := isStoppingTime_firstCrossing (had t) N
  have hHN (t : ℝ) : H t = {ω | ∃ i ≤ N, ω ∈ A t i} := Set.ext (hmax t)
  have hst (ω : Ω) : τ a ω ≤ τ (a + b) ω := by
    by_cases hh : a + b < Y ω
    · exact (firstCrossing_jump (hv ω) (hw ω) (fun i => hw₀ i ω) ha hb ((hmax _ ω).mp hh)).2.1
    · have hnone := mt (hmax _ ω).mpr hh
      simpa [τ, A, firstCrossing, hnone] using
        (firstCrossing_le N (fun i => ω ∈ A a i))
  have hcap (ω : Ω) : τ (a + b) ω ≤ N := firstCrossing_le _ _
  have hG : MeasurableSet[(hτ a).measurableSpace] (H a) := by
    rw [hHN]; exact measurableSet_hitAtFirstCrossing (had a) N
  let B := {ω | a + b < Y ω ∧ X ω ≤ θ * b}
  have hB : MeasurableSet B := (measurableSet_lt measurable_const hY).inter
    (measurableSet_le hX measurable_const)
  have hsub : B ⊆ H a := fun ω hh => lt_trans (lt_add_of_pos_right a hb) hh.1
  let J (ω : Ω) := |v (τ (a + b) ω) ω - v (τ a ω - 1) ω| / D (τ a ω) (τ (a + b) ω) ω
  have hlarge (ω : Ω) (hh : ω ∈ B) : 1 / θ ≤ J ω := by
    have hj := (firstCrossing_jump (hv ω) (hw ω) (fun i => hw₀ i ω) ha hb
      ((hmax _ ω).mp hh.1)).2.2.2
    change b * w (τ (a + b) ω) ω < |v (τ (a + b) ω) ω - v (τ a ω - 1) ω| at hj
    obtain ⟨hd₀, hd⟩ := hD _ _ ω (hst ω) (hcap ω)
    apply (div_le_div_iff₀ hθ hd₀).mpr
    rw [one_mul]
    exact hd.trans (((mul_le_mul_of_nonneg_right hh.2 (hw₀ _ ω).le)).trans
      (by rw [mul_assoc, mul_comm θ]; exact mul_le_mul_of_nonneg_right hj.le hθ.le))
  have hsmall : ENNReal.ofReal (1 / θ) * μ B ≤ μ (H a) := by
    calc
      _ = ∫⁻ _ in B, ENNReal.ofReal (1 / θ) ∂μ := by simp
      _ ≤ ∫⁻ ω in B, ENNReal.ofReal (J ω) ∂μ :=
        lintegral_mono_ae ((ae_restrict_iff' hB).mpr (Filter.Eventually.of_forall
          fun ω hω => ENNReal.ofReal_le_ofReal (hlarge ω hω)))
      _ ≤ ∫⁻ ω in H a, ENNReal.ofReal (J ω) ∂μ := lintegral_mono_set hsub
      _ ≤ _ := hmean _ _ (hτ a) (hτ _) hst hcap _ hG
  have hcancel := mul_le_mul_left' hsmall (ENNReal.ofReal θ)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hθ.le, mul_one_div_cancel hθ.ne',
    ENNReal.ofReal_one, one_mul] at hcancel
  have cover : H (a + b) ⊆ B ∪ {ω | θ * b < X ω} := by
    intro ω hh
    by_cases hx : X ω ≤ θ * b
    · exact Or.inl ⟨hh, hx⟩
    · exact Or.inr (lt_of_not_ge hx)
  exact (measure_mono cover).trans ((measure_union_le _ _).trans (add_le_add_right hcancel _))

end WeightedBMO
