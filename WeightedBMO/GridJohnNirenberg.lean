import WeightedBMO.GridEstimate

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

/-- Maximum on the integer interval [i,j], using the endpoint j for an empty interval. -/
def gridMax (f : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (insert j (Finset.Icc i j)).sup' ⟨j, Finset.mem_insert_self _ _⟩ f

private theorem gridMax_le {f : ℕ → ℝ} {i j : ℕ} {c : ℝ}
    (hj : f j ≤ c) (h : ∀ k, i ≤ k → k ≤ j → f k ≤ c) : gridMax f i j ≤ c := by
  apply Finset.sup'_le
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact hj
  · exact h k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

private theorem le_gridMax {f : ℕ → ℝ} {i j k : ℕ} (hi : i ≤ k) (hj : k ≤ j) :
    f k ≤ gridMax f i j :=
  Finset.le_sup' _ (Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨hi,hj⟩))

private theorem lt_gridMax_zero {f : ℕ → ℝ} {j : ℕ} {a : ℝ} :
    a < gridMax f 0 j ↔ ∃ k ≤ j, a < f k := by
  unfold gridMax
  rw [Finset.lt_sup'_iff]
  simp [Finset.insert_eq_of_mem (Finset.mem_Icc.mpr ⟨Nat.zero_le j, le_rfl⟩)]

private theorem measurable_max {Ω : Type*} [MeasurableSpace Ω] {f : ℕ → Ω → ℝ}
    (n : ℕ) (hf : ∀ i ≤ n, Measurable (f i)) :
    Measurable (fun ω => gridMax (fun i => f i ω) 0 n) := by
  apply measurable_of_Ioi
  intro a
  rw [show (fun ω => gridMax (fun i => f i ω) 0 n) ⁻¹' Ioi a =
    ⋃ i ≤ n, {ω | a < f i ω} by ext; simp [lt_gridMax_zero]]
  exact MeasurableSet.biUnion (Set.to_countable _) fun i hi =>
    measurableSet_lt measurable_const (hf i hi)

/-- Event-testing form of a unit bound on the weighted oscillation modulus.
The pair weight is the running maximum of the positive weight on [S,T].
The path v denotes the oscillation from the initial time. -/
def UnitGridOscillation {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ m) (N : ℕ) (v φ : ℕ → Ω → ℝ) : Prop :=
  ∀ (S T : Ω → ℕ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ T →
    (∀ ω, S ω ≤ T ω) → (∀ ω, T ω ≤ N) →
    ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
    (∫⁻ ω in G, ENNReal.ofReal (|v (T ω) ω - v (S ω - 1) ω| /
      gridMax (fun i => φ i ω) (S ω) (T ω)) ∂μ) ≤ μ G

private theorem UnitGridOscillation.restrict {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ} {v φ : ℕ → Ω → ℝ}
    (h : UnitGridOscillation μ ℱ N v φ) {E : Set Ω} (hE : MeasurableSet[ℱ 0] E) :
    UnitGridOscillation (μ.restrict E) ℱ N v φ := by
  intro S T hS hT hST hN G hG
  have hm := hS.measurableSpace_le _ hG
  rw [Measure.restrict_restrict hm, Measure.restrict_apply hm]
  exact h S T hS hT hST hN _ (hG.inter
    ((hS.le_measurableSpace_of_const_le (fun ω => Nat.zero_le (S ω))) _ hE))

/-- Finite-grid versions of (1.8) and (1.9) for unit oscillation, tested
on each initial measurable event. In the second bound the constant function
one supplies the mass of the testing event. -/
theorem grid_johnNirenberg {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (N : ℕ) (v φ : ℕ → Ω → ℝ)
    (hv : ∀ i, Measurable[ℱ i] (v i)) (hφ : ∀ i, Measurable[ℱ i] (φ i))
    (hv₀ : ∀ ω, v 0 ω = 0) (hpos : ∀ i ω, 0 < φ i ω)
    (h : UnitGridOscillation μ ℱ N v φ) {E : Set Ω} (hE : MeasurableSet[ℱ 0] E)
    {p : ℝ} (hp : 0 < p) :
    let W := fun j ω => gridMax (fun i => φ i ω) 0 j
    let V := fun ω => gridMax (fun i => |v i ω|) 0 N
    let Z := fun ω => gridMax (fun i => |v i ω| / W i ω) 0 N
    let norm := fun f : Ω → ℝ => eLpNorm f (ENNReal.ofReal p) (μ.restrict E)
    norm V ≤ ENNReal.ofReal (goodLambdaConstant p) * norm (W N) ∧
      norm Z ≤ ENNReal.ofReal (goodLambdaConstant p) * norm (fun _ => 1) := by
  let W := fun (j : ℕ) (ω : Ω) => gridMax (fun i => φ i ω) 0 j
  have mW (i : ℕ) : Measurable[ℱ i] (W i) := @measurable_max Ω (ℱ i) φ i
    (fun j hj => (hφ j).mono (ℱ.mono hj) le_rfl)
  have posW (i : ℕ) (ω : Ω) : 0 < W i ω :=
    (hpos i ω).trans_le (le_gridMax (f := fun k => φ k ω) (Nat.zero_le i) le_rfl)
  have monoW (ω : Ω) : Monotone (fun i => W i ω) := by
    intro i j hij
    exact gridMax_le (le_gridMax (f := fun k => φ k ω) (Nat.zero_le i) hij)
      (fun k hk hki => le_gridMax (f := fun k => φ k ω) hk (hki.trans hij))
  have pair (i j : ℕ) (ω : Ω) (hij : i ≤ j) :
      0 < gridMax (fun k => φ k ω) i j ∧ gridMax (fun k => φ k ω) i j ≤ W j ω :=
    ⟨(hpos j ω).trans_le (le_gridMax (f := fun k => φ k ω) hij le_rfl),
      gridMax_le (le_gridMax (f := fun k => φ k ω) (Nat.zero_le j) le_rfl)
        (fun k _ hkj => le_gridMax (f := fun k => φ k ω) (Nat.zero_le k) hkj)⟩
  have mabs (i : ℕ) : Measurable[ℱ i] (fun ω => |v i ω|) := continuous_abs.measurable.comp (hv i)
  have mv (i : ℕ) := (mabs i).mono (ℱ.le i) le_rfl
  have mw (i : ℕ) := (mW i).mono (ℱ.le i) le_rfl
  constructor
  · apply grid_maximal_eLpNorm_le (μ.restrict E) ℱ N v (fun _ _ => 1)
      (fun i j ω => gridMax (fun k => φ k ω) i j) (mw N)
      (measurable_max N (fun i _ => mv i)) (fun ω => (posW N ω).le)
      (fun ω => (abs_nonneg (v N ω)).trans (le_gridMax (f := fun i => |v i ω|) (Nat.zero_le N) le_rfl))
      hv₀ (fun _ _ _ _ => le_rfl) (fun _ _ => zero_lt_one)
    · intro t i; simpa using measurableSet_lt (measurable_const (a := t)) (mabs i)
    · intro t ω; simp [lt_gridMax_zero]
    · intro i j ω hij hj
      simpa using ⟨(pair i j ω hij).1, (pair i j ω hij).2.trans (monoW ω hj)⟩
    · exact h.restrict hE
    · exact hp
  · apply grid_maximal_eLpNorm_le (μ.restrict E) ℱ N v W
      (fun i j ω => gridMax (fun k => φ k ω) i j) measurable_const
      (measurable_max N (fun i _ => (mv i).div (mw i)))
      (fun _ => zero_le_one)
      (fun ω => (div_nonneg (abs_nonneg _) (posW N ω).le).trans (le_gridMax (f := fun i => |v i ω| / W i ω) (Nat.zero_le N) le_rfl))
      hv₀ monoW posW
    · intro t i; exact measurableSet_lt (measurable_const.mul (mW i)) (mabs i)
    · intro t ω; simp only [lt_gridMax_zero, lt_div_iff₀ (posW _ ω)]
    · intro i j ω hij _; simpa using pair i j ω hij
    · exact h.restrict hE
    · exact hp

end WeightedBMO
