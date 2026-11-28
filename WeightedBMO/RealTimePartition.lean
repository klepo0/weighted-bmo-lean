import WeightedBMO.SmallScale
import WeightedBMO.GridPartition

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

/-- Uniform event-testing version of the implication `est.jnweight2` ⇒ `est.jnexpwei`.
Z is the normalized interval maximum. Its zero-length and splitting laws
are explicit so the integration argument is independent of path regularity.
The moment hypothesis is `est.jnweight2` tested on events at the interval start. -/
theorem uniform_exponential_of_interval_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℝ m)
    (Z : ℝ → ℝ → Ω → ℝ) (ρ : ℝ → ℝ → ℝ) {a T rate : ℝ}
    (hm : ∀ s t, a ≤ s → s ≤ t → t ≤ T → Measurable[ℱ t] (Z s t))
    (hz : ∀ s t ω, a ≤ s → s ≤ t → t ≤ T → 0 ≤ Z s t ω)
    (hzero : ∀ r ∈ Icc a T, ∀ ω, Z r r ω = 0)
    (hsplit : ∀ r s t ω, a ≤ r → r ≤ s → s ≤ t → t ≤ T →
      Z r t ω ≤ Z r s ω + Z s t ω)
    (hmom : ∀ s t, a ≤ s → s ≤ t → t ≤ T → ∀ c : ℝ, 0 < c → ρ s t ≤ c →
      ∀ E : Set Ω, MeasurableSet[ℱ s] E → ∀ n : ℕ, 0 < n →
      eLpNorm (fun ω => Z s t ω / c) (ENNReal.ofReal n) (μ.restrict E) ≤
        ENNReal.ofReal (goodLambdaConstant n) *
          eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal n) (μ.restrict E))
    (hb : (smallScaleBounds ρ a T).Nonempty)
    (hend : rate * sInf (smallScaleBounds ρ a T) ≤ Real.exp (-3)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r ∈ Icc a T, ∀ E : Set Ω, MeasurableSet[ℱ r] E →
      (∫⁻ ω in E, ENNReal.ofReal (Real.exp (rate * Z r T ω)) ∂μ) ≤ C * μ E := by
  by_cases hr : 0 ≤ rate
  case neg =>
    refine ⟨1, by simp, fun r hr' E _ => ?_⟩
    calc
      _ ≤ ∫⁻ _ in E, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun ω => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr) (hz _ _ _ hr'.1 hr'.2 le_rfl)))
      _ = _ := by simp
  obtain ⟨c, hc, hrate, K, part⟩ := partition_of_smallScale hb hr hend
  let b := (5/2 : ℝ)
  let M := ENNReal.ofReal (∑' n : ℕ, (Real.exp (-b) * goodLambdaConstant n)^n / n.factorial)
  let F (s t : ℝ) (ω : Ω) := ENNReal.ofReal (Real.exp (rate * Z s t ω))
  have hF s t (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
      Measurable[ℱ t] (F s t) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul (hm _ _ hs hst ht))).ennreal_ofReal
  refine ⟨M^K, ENNReal.pow_lt_top ENNReal.ofReal_lt_top, ?_⟩
  intro r hR E hE
  obtain ⟨t, hmono, h0, hK, hlocal⟩ := part r hR
  have hstart (k : ℕ) : r ≤ t k := h0 ▸ hmono (Nat.zero_le k)
  have hstop (k : ℕ) (hk : k ≤ K) : t k ≤ T := hK ▸ hmono hk
  have hind (k : ℕ) (hk : k ≤ K) : (∫⁻ ω in E, F r (t k) ω ∂μ) ≤ M^k * μ E := by
    induction k with
    | zero => simp [F, h0, hzero _ hR]
    | succ k ih =>
      have hsk := hmono (Nat.le_succ k)
      have ha := hR.1.trans (hstart k)
      have ht := hstop _ hk
      have localBound (A : Set Ω) (hA : MeasurableSet[ℱ (t k)] A) :
          (∫⁻ ω in A, F (t k) (t (k+1)) ω ∂μ.restrict E) ≤ M * μ.restrict E A := by
        rw [Measure.restrict_restrict (ℱ.le _ _ hA), Measure.restrict_apply (ℱ.le _ _ hA)]
        have he := exponential_of_moments (μ.restrict (A ∩ E)) (b := b) (by norm_num [b])
          (((hm _ _ ha hsk ht).mono (ℱ.le _) le_rfl).div_const c)
          (fun ω => div_nonneg (hz _ _ ω ha hsk ht) hc.le)
          (hmom _ _ ha hsk ht c hc (hlocal _ hk) _ (hA.inter (ℱ.mono (hstart k) _ hE)))
        simp only [Measure.restrict_apply_univ] at he
        apply le_trans (lintegral_mono _) he
        intro ω
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        rw [← mul_div_assoc, le_div_iff₀ hc]
        calc
          _ = (rate*c) * Z (t k) (t (k+1)) ω := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hrate.le (hz _ _ _ ha hsk ht)
      have prod := weighted_test (ℱ.le (t k)) (μ.restrict E)
        ((hF _ _ ha hsk ht).mono (ℱ.le _) le_rfl)
        (hF _ _ hR.1 (hstart k) (hstop _ (Nat.le_of_succ_le hk))) M localBound
      refine (le_trans (lintegral_mono ?_) prod).trans ?_
      · intro ω
        change ENNReal.ofReal (Real.exp _) ≤ ENNReal.ofReal (Real.exp _) * ENNReal.ofReal (Real.exp _)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← mul_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hr
        exact (hsplit _ _ _ _ hR.1 (hstart k) hsk ht).trans_eq (add_comm _ _)
      · exact (mul_le_mul_left' (ih (Nat.le_of_succ_le hk)) _).trans_eq (by rw [pow_succ']; ac_rfl)
  simpa [hK, F] using hind K le_rfl

end WeightedBMO
