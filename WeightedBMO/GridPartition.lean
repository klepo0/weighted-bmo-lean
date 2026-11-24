import WeightedBMO.GridExponential
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

/-- An event-tested bound also holds after multiplication by any nonnegative
weight measurable at the start of the block. -/
theorem weighted_test {Ω : Type*} [m : MeasurableSpace Ω] {s : MeasurableSpace Ω}
    (hs : s ≤ m) (μ : @Measure Ω m) {f g : Ω → ℝ≥0∞} (hf : Measurable[m] f)
    (hg : Measurable[s] g) (C : ℝ≥0∞)
    (h : ∀ A, MeasurableSet[s] A → (∫⁻ ω in A, f ω ∂μ) ≤ C * μ A) :
    (∫⁻ ω, (f * g) ω ∂μ) ≤ C * ∫⁻ ω, g ω ∂μ := by
  let ν : @Measure Ω m := C • μ
  have hle : (μ.withDensity f).trim hs ≤ ν.trim hs := by
    apply Measure.le_iff.mpr
    intro A hA
    simpa [ν, trim_measurableSet_eq hs hA, withDensity_apply f (hs _ hA),
      Measure.smul_apply, smul_eq_mul] using h A hA
  rw [← lintegral_withDensity_eq_lintegral_mul μ hf (hg.mono hs le_rfl),
    ← lintegral_trim hs hg]
  exact (lintegral_mono' hle (fun _ => le_rfl)).trans_eq
    ((lintegral_trim hs hg).trans (lintegral_smul_measure C g))

/-- Shift a filtration to the start of a deterministic block. -/
def shiftFiltration {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m)
    (s : ℕ) : Filtration ℕ m :=
  ⟨fun i => ℱ (s+i), fun _ _ h => ℱ.mono (Nat.add_le_add_left h s), fun i => ℱ.le (s+i)⟩

/-- Maximum of centered increments on a block, normalized at each time by
the running maximum of the weight since the start of that block. -/
noncomputable def blockMax (v φ : ℕ → ℝ) (s n : ℕ) : ℝ :=
  gridMax (fun i => |v (s+i) - v s| / gridMax (fun k => φ (s+k)) 0 i) 0 n

private theorem block_nonneg (v φ : ℕ → ℝ) (s n : ℕ) (hp : ∀ k, 0 < φ k) :
    0 ≤ blockMax v φ s n := by
  apply le_trans _ (le_gridMax (f := fun i => |v (s+i)-v s| /
    gridMax (fun k => φ (s+k)) 0 i) (Nat.zero_le n) le_rfl)
  exact div_nonneg (abs_nonneg _) ((hp (s+n)).le.trans
    (le_gridMax (f := fun k => φ (s+k)) (Nat.zero_le n) le_rfl))

/-- Splitting at s costs at most the normalized maximum on the new block. -/
theorem blockMax_split (v φ : ℕ → ℝ) (s n : ℕ) (hp : ∀ k, 0 < φ k) :
    blockMax v φ 0 (s+n) ≤ blockMax v φ 0 s + blockMax v φ s n := by
  let W := fun i => gridMax φ 0 i
  have pos (i : ℕ) : 0 < W i := (hp i).trans_le (le_gridMax (Nat.zero_le i) le_rfl)
  have old (i : ℕ) (hi : i ≤ s) : |v i-v 0| / W i ≤ blockMax v φ 0 s := by
    simpa [blockMax, W] using le_gridMax (f := fun k => |v k-v 0| / W k) (Nat.zero_le i) hi
  have single (i : ℕ) (hi : i ≤ s+n) :
      |v i-v 0| / W i ≤ blockMax v φ 0 s + blockMax v φ s n := by
    by_cases his : i ≤ s
    · exact (old i his).trans (le_add_of_nonneg_right (block_nonneg v φ s n hp))
    let j := i-s
    have hi' : s+j = i := by dsimp [j]; omega
    have hj : j ≤ n := by dsimp [j]; omega
    let B := gridMax (fun k => φ (s+k)) 0 j
    have posB : 0 < B := (hp (s+j)).trans_le (le_gridMax (f := fun k => φ (s+k)) (Nat.zero_le j) le_rfl)
    have mono (k : ℕ) (hk : k ≤ i) := le_gridMax (f := φ) (Nat.zero_le k) hk
    have hsw : W s ≤ W i := gridMax_le (mono _ (by omega)) (fun _ _ hk => mono _ (by omega))
    have hbw : B ≤ W i := gridMax_le (mono _ hi'.le) (fun _ _ hk => mono _ (by omega))
    have hb := le_gridMax (f := fun k => |v (s+k)-v s| /
      gridMax (fun l => φ (s+l)) 0 k) (Nat.zero_le j) hj
    change |v (s+j)-v s| / B ≤ blockMax v φ s n at hb
    rw [hi'] at hb
    have htri : |v i-v 0| ≤ |v s-v 0| + |v i-v s| := by
      simpa [add_comm] using abs_sub_le (v i) (v s) (v 0)
    calc
      _ ≤ (|v s-v 0| + |v i-v s|) / W i := div_le_div_of_nonneg_right htri (pos i).le
      _ = _ := add_div _ _ _
      _ ≤ _ := add_le_add
        ((div_le_div_of_nonneg_left (abs_nonneg _) (pos s) hsw).trans (old s le_rfl))
        ((div_le_div_of_nonneg_left (abs_nonneg _) posB hbw).trans hb)
  simpa [blockMax, W] using gridMax_le (f := fun k => |v k-v 0| / W k)
    (single _ le_rfl) (fun _ _ hk => single _ hk)

section Partition

variable {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    {v φ : ℕ → Ω → ℝ}

private theorem measurable_block (hv : ∀ i, Measurable[ℱ i] (v i))
    (hφ : ∀ i, Measurable[ℱ i] (φ i)) (s n : ℕ) :
    Measurable[ℱ (s+n)] (fun ω => blockMax (fun i => v i ω) (fun i => φ i ω) s n) := by
  apply @measurable_gridMax Ω (ℱ (s+n))
  intro i hi
  have hm (k : ℕ) (hk : k ≤ n) := ℱ.mono (Nat.add_le_add_left hk s)
  exact (continuous_abs.measurable.comp (((hv _).mono (hm i hi) le_rfl).sub
    ((hv s).mono (ℱ.mono (Nat.le_add_right s n)) le_rfl))).div
    (@measurable_gridMax Ω (ℱ (s+n)) _ i
      (fun k hk => (hφ _).mono (hm k (hk.trans hi)) le_rfl))

/-- A local oscillation bound c on the block of length n starting at s.
Rescale the centered path by c⁻¹ to use the unit event-testing formulation. -/
def BlockOscillationBound (μ : Measure Ω) (ℱ : Filtration ℕ m) (s n : ℕ)
    (v φ : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  UnitGridOscillation μ (shiftFiltration ℱ s) n
    (fun i ω => c⁻¹ * (v (s+i) ω - v s ω)) (fun i => φ (s+i))

private theorem local_exponential (μ : Measure Ω) [IsFiniteMeasure μ]
    (hv : ∀ i, Measurable[ℱ i] (v i)) (hφ : ∀ i, Measurable[ℱ i] (φ i))
    (hp : ∀ i ω, 0 < φ i ω) {s n : ℕ} {c rate : ℝ} (hc : 0 < c)
    (h : BlockOscillationBound μ ℱ s n v φ c) (hr : rate*c ≤ Real.exp (-3))
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    (∫⁻ ω in A, ENNReal.ofReal (Real.exp (rate *
      blockMax (fun i => v i ω) (fun i => φ i ω) s n)) ∂μ) ≤
      ENNReal.ofReal exponentialBound * μ A := by
  have he := grid_exponential μ (shiftFiltration ℱ s) n _ _
    (fun i => measurable_const.mul ((hv (s+i)).sub ((hv s).mono
      (ℱ.mono (Nat.le_add_right s i)) le_rfl))) (fun i => hφ (s+i))
    (fun ω => by simp) (fun i => hp (s+i)) h (by simpa [shiftFiltration] using hA) hr
  let L : ℝ →o ℝ := ⟨fun x => c⁻¹*x, fun _ _ hxy => mul_le_mul_of_nonneg_left hxy (inv_pos.mpr hc).le⟩
  have scale (q : Finset ℕ) (hq : q.Nonempty) (f : ℕ → ℝ) :
      c⁻¹ * q.sup' hq f = q.sup' hq (fun k => c⁻¹ * f k) := map_finset_sup' L hq f
  convert he using 2
  dsimp [blockMax, gridMax]
  simp only [abs_mul, abs_of_pos (inv_pos.mpr hc), mul_div_assoc,
    ← scale, ← mul_assoc, mul_inv_cancel_right₀ hc.ne']

/-- A deterministic finite partition gives M^K for K blocks, tested on
every initial event. Block lengths and oscillation bounds may vary. -/
theorem grid_partition_exponential (μ : Measure Ω) [IsFiniteMeasure μ]
    (hv : ∀ i, Measurable[ℱ i] (v i)) (hφ : ∀ i, Measurable[ℱ i] (φ i))
    (hp : ∀ i ω, 0 < φ i ω) (t : ℕ → ℕ) (ht : Monotone t) (ht₀ : t 0 = 0)
    (K : ℕ) (c : ℕ → ℝ) {rate : ℝ} (hrate : 0 ≤ rate)
    (hc : ∀ k < K, 0 < c k) (hr : ∀ k < K, rate * c k ≤ Real.exp (-3))
    (h : ∀ k < K, BlockOscillationBound μ ℱ (t k) (t (k+1)-t k) v φ (c k))
    {E : Set Ω} (hE : MeasurableSet[ℱ 0] E) :
    (∫⁻ ω in E, ENNReal.ofReal (Real.exp (rate *
      blockMax (fun i => v i ω) (fun i => φ i ω) 0 (t K))) ∂μ) ≤
      ENNReal.ofReal exponentialBound ^ K * μ E := by
  let Z (s n : ℕ) (ω : Ω) := blockMax (fun i => v i ω) (fun i => φ i ω) s n
  let F (s n : ℕ) (ω : Ω) := ENNReal.ofReal (Real.exp (rate * Z s n ω))
  have hF (s n : ℕ) : Measurable[ℱ (s+n)] (F s n) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul
      (measurable_block hv hφ s n))).ennreal_ofReal
  change (∫⁻ ω in E, F 0 (t K) ω ∂μ) ≤ _
  induction K with
  | zero => simp [ht₀, F, Z, blockMax, gridMax]
  | succ k ih =>
    have hk := Nat.lt_succ_self k
    let s := t k
    let n := t (k+1)-s
    have hend : s+n = t (k+1) := Nat.add_sub_of_le (ht (Nat.le_succ k))
    have hprev : Measurable[ℱ s] (F 0 s) := by simpa using hF 0 s
    have hb : ∀ A, MeasurableSet[ℱ s] A →
        (∫⁻ ω in A, F s n ω ∂μ.restrict E) ≤ ENNReal.ofReal exponentialBound * μ.restrict E A := by
      intro A hA
      rw [Measure.restrict_restrict (ℱ.le s _ hA), Measure.restrict_apply (ℱ.le s _ hA)]
      exact local_exponential μ hv hφ hp (hc k hk) (h k hk) (hr k hk)
        (hA.inter (ℱ.mono (Nat.zero_le s) _ hE))
    have prod := weighted_test (ℱ.le s) (μ.restrict E)
      ((hF s n).mono (ℱ.le _) le_rfl) hprev _ hb
    have bound := ih (fun j hj => hc j (Nat.lt_succ_of_lt hj))
      (fun j hj => hr j (Nat.lt_succ_of_lt hj)) (fun j hj => h j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ ∫⁻ ω in E, (F s n * F 0 s) ω ∂μ := by
        apply lintegral_mono
        intro ω
        change ENNReal.ofReal (Real.exp _) ≤ ENNReal.ofReal (Real.exp _) * ENNReal.ofReal (Real.exp _)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← mul_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hrate
        rw [← hend, add_comm (Z s n ω)]
        exact blockMax_split _ _ s n (fun i => hp i ω)
      _ ≤ _ := prod
      _ ≤ _ := (mul_le_mul_left' bound _).trans_eq (by rw [pow_succ']; ac_rfl)

end Partition
end WeightedBMO
