import WeightedBMO.GridExponential

namespace WeightedBMO

/-- Uniform upper bounds on the interval modulus at some positive mesh size. -/
def smallScaleBounds (ρ : ℝ → ℝ → ℝ) (a T : ℝ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ T → t-s ≤ δ → ρ s t ≤ c}

/-- Choose a common number of blocks for every initial time in [a,T].
The strict slack between exp(-3) and exp(-5/2) includes the equality case
in the rate hypothesis. The local exponential series still converges at
the larger coefficient by `summable_exponential_coefficients`. -/
theorem partition_of_smallScale {ρ : ℝ → ℝ → ℝ} {a T rate : ℝ}
    (hbounded : (smallScaleBounds ρ a T).Nonempty) (hr : 0 ≤ rate)
    (hend : rate * sInf (smallScaleBounds ρ a T) ≤ Real.exp (-3)) :
    ∃ c > 0, rate*c < Real.exp (-(5/2 : ℝ)) ∧ ∃ K : ℕ,
      ∀ r ∈ Set.Icc a T, ∃ t : ℕ → ℝ, Monotone t ∧ t 0 = r ∧ t K = T ∧
        ∀ i < K, ρ (t i) (t (i+1)) ≤ c := by
  let B := smallScaleBounds ρ a T
  have hκ : 0 ≤ sInf B := le_csInf hbounded (fun x hx => hx.1)
  have hgap : 0 < Real.exp (-(5/2 : ℝ)) - Real.exp (-3) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))
  let ε := (Real.exp (-(5/2 : ℝ)) - Real.exp (-3)) / (rate+1)
  have he : 0 < ε := div_pos hgap (by linarith)
  have heq : ε*(rate+1) = Real.exp (-(5/2 : ℝ)) - Real.exp (-3) :=
    div_mul_cancel₀ _ (by linarith)
  have hlt : sInf B < sInf B + ε := lt_add_of_pos_right _ he
  obtain ⟨d, hd, hdlt⟩ := exists_lt_of_csInf_lt hbounded hlt
  obtain ⟨_, δ, hδ, hmesh⟩ := hd
  obtain ⟨K, hK⟩ := exists_nat_ge ((T-a)/δ)
  refine ⟨sInf B + ε, by linarith, ?_, K, ?_⟩
  · change rate * sInf B ≤ _ at hend
    nlinarith [heq, he]
  intro r hr'
  let t (i : ℕ) := min T (r + (i : ℝ)*δ)
  have hm : Monotone t := fun i j hij => min_le_min_left _ (by gcongr)
  have ht0 : t 0 = r := by simp [t, min_eq_right hr'.2]
  refine ⟨t, hm, ht0, min_eq_left (by linarith [(div_le_iff₀ hδ).mp hK, hr'.1]), ?_⟩
  intro i _
  apply le_trans _ hdlt.le
  apply hmesh
  · exact hr'.1.trans (ht0 ▸ hm (Nat.zero_le i))
  · exact hm (Nat.le_succ i)
  · exact min_le_left _ _
  · dsimp [t]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rcases le_total T (r + (i : ℝ)*δ) with h | h
    · rw [min_eq_left h]
      linarith [min_le_left T (r + ((i:ℝ)*δ + δ))]
    · rw [min_eq_right h]
      linarith [min_le_right T (r + ((i:ℝ)*δ + δ))]

end WeightedBMO
