import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Probability.Process.Stopping

open MeasureTheory Set

namespace WeightedBMO

/-- First strict crossing on a finite grid, capped at the terminal index. -/
noncomputable def firstCrossing (N : ℕ) (P : ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ i ≤ N, P i then Nat.find h else N

theorem firstCrossing_le (N : ℕ) (P : ℕ → Prop) : firstCrossing N P ≤ N := by
  classical
  unfold firstCrossing
  split
  next h => exact (Nat.find_spec h).1
  next => exact le_rfl

theorem firstCrossing_spec {N : ℕ} {P : ℕ → Prop} (h : ∃ i ≤ N, P i) :
    P (firstCrossing N P) := by
  classical
  simpa [firstCrossing, h] using (Nat.find_spec h).2

/-- For times strictly before the cap, this identity gives measurability of
the crossing event from adaptedness of the individual tests. -/
theorem firstCrossing_le_iff {N k : ℕ} (hk : k < N) (P : ℕ → Prop) :
    firstCrossing N P ≤ k ↔ ∃ i ≤ k, P i := by
  classical
  by_cases h : ∃ i ≤ N, P i
  · constructor
    · intro hs
      exact ⟨_, hs, firstCrossing_spec h⟩
    · rintro ⟨i, hi, hPi⟩
      simpa [firstCrossing, h] using
        (Nat.find_min' h ⟨hi.trans hk.le, hPi⟩).trans hi
  · simp only [firstCrossing, dif_neg h, Nat.not_le.mpr hk, false_iff]
    rintro ⟨i, hi, hPi⟩
    exact h ⟨i, hi.trans hk.le, hPi⟩

section Filtration

variable {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet[ℱ i] (A i))

include hA

private theorem measurableSet_hitBy {n k : ℕ} (hnk : n ≤ k) :
    MeasurableSet[ℱ k] {ω | ∃ i ≤ n, ω ∈ A i} := by
  rw [show {ω | ∃ i ≤ n, ω ∈ A i} = ⋃ i ≤ n, A i by ext; simp]
  exact MeasurableSet.biUnion (Set.to_countable _) fun i hi =>
    ℱ.mono (le_trans (show i ≤ n from hi) hnk) _ (hA i)

/-- First passage of adapted events up to a deterministic horizon. -/
theorem isStoppingTime_firstCrossing (N : ℕ) :
    IsStoppingTime ℱ (fun ω => firstCrossing N (fun i => ω ∈ A i)) := by
  intro k
  by_cases hk : k < N
  · simp_rw [firstCrossing_le_iff hk]
    exact measurableSet_hitBy hA le_rfl
  · have hall (ω : Ω) := (firstCrossing_le N (fun i => ω ∈ A i)).trans (le_of_not_gt hk)
    simp [hall]

/-- The event of an actual hit belongs to the stopped σ-algebra, including
when the first hit occurs exactly at the cap. -/
theorem measurableSet_hitAtFirstCrossing (N : ℕ) :
    MeasurableSet[(isStoppingTime_firstCrossing hA N).measurableSpace]
      {ω | ∃ i ≤ N, ω ∈ A i} := by
  intro k
  by_cases hk : k < N
  · have heq : {ω | ∃ i ≤ N, ω ∈ A i} ∩
        {ω | firstCrossing N (fun i => ω ∈ A i) ≤ k} = {ω | ∃ i ≤ k, ω ∈ A i} := by
      ext ω
      change (_ ∧ firstCrossing N _ ≤ k) ↔ _
      rw [firstCrossing_le_iff hk]
      exact ⟨And.right, fun h => ⟨by obtain ⟨i, hi, hm⟩ := h; exact ⟨i, hi.trans hk.le, hm⟩, h⟩⟩
    rw [heq]
    exact measurableSet_hitBy hA le_rfl
  · exact (measurableSet_hitBy hA (le_of_not_gt hk)).inter (isStoppingTime_firstCrossing hA N k)

end Filtration

/-- The jump estimate behind the two finite-grid good-λ arguments.
Use the constant envelope one for raw oscillation, or the running maximum
of a positive weight for normalized oscillation. The path is centered at
its starting value. -/
theorem firstCrossing_jump {N : ℕ} {v w : ℕ → ℝ} (hv : v 0 = 0)
    (hw : Monotone w) (hw₀ : ∀ i, 0 < w i) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hit : ∃ i ≤ N, (a + b) * w i < |v i|) :
    let S := firstCrossing N (fun i => a * w i < |v i|)
    let T := firstCrossing N (fun i => (a + b) * w i < |v i|)
    0 < S ∧ S ≤ T ∧ T ≤ N ∧ b * w T < |v T - v (S - 1)| := by
  classical
  let P := fun i => a * w i < |v i|
  let Q := fun i => (a + b) * w i < |v i|
  let S := firstCrossing N P
  let T := firstCrossing N Q
  change 0 < S ∧ S ≤ T ∧ T ≤ N ∧ b * w T < |v T - v (S - 1)|
  have ht : (a + b) * w T < |v T| := firstCrossing_spec hit
  have htN : T ≤ N := firstCrossing_le _ _
  have hPt : P T := (mul_lt_mul_of_pos_right (lt_add_of_pos_right a hb) (hw₀ T)).trans ht
  have hex : ∃ i ≤ N, P i := ⟨T, htN, hPt⟩
  have hs : 0 < S := by
    by_contra! hz
    have hz' : S = 0 := Nat.eq_zero_of_le_zero hz
    have hPs : a * w S < |v S| := firstCrossing_spec hex
    rw [hz', hv, abs_zero] at hPs
    exact (not_lt_of_ge (mul_pos ha (hw₀ 0)).le) hPs
  have hst : S ≤ T := by
    simpa [S, firstCrossing, hex] using Nat.find_min' hex ⟨htN, hPt⟩
  have hpred : S - 1 < S := Nat.sub_lt hs Nat.zero_lt_one
  have hprev : |v (S - 1)| ≤ a * w (S - 1) := by
    apply le_of_not_gt
    intro h
    have hm := Nat.find_min' (m := S - 1) hex ⟨hpred.le.trans (firstCrossing_le N P), h⟩
    have : S ≤ S - 1 := by simpa [S, firstCrossing, hex] using hm
    omega
  have hsmall := hprev.trans (mul_le_mul_of_nonneg_left (hw (hpred.le.trans hst)) ha.le)
  have htri : |v T| ≤ |v T - v (S - 1)| + |v (S - 1)| := by
    simpa using abs_add_le (v T - v (S - 1)) (v (S - 1))
  exact ⟨hs, hst, htN, by linarith [ht, hsmall, htri]⟩

end WeightedBMO
