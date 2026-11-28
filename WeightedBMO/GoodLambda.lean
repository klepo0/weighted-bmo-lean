import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A good-λ inequality for moments

Lemma 2.1 of Khoa Lê, *Maximal inequalities, weighted BMO processes and the largest-jump normaliser*,
arXiv:2211.15550.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The full coefficient `p * c_p` in Lemma 2.1, with `c_p` from `def.M`. -/
noncomputable def goodLambdaConstant (p : ℝ) : ℝ :=
  p * (p * (1 + 1 / p) ^ ((p + 1) ^ (2 : ℕ))) ^ (1 / p)

private def upperTail (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  μ {ω | t < f ω}

private theorem measurable_upperTail (μ : Measure Ω) (f : Ω → ℝ) :
    Measurable (upperTail μ f) :=
  Antitone.measurable (fun _ _ h ↦ measure_mono (fun _ hw ↦ h.trans_lt hw))

private theorem lintegral_le_of_upperTail_le (μ : Measure Ω)
    {f g k : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hf₀ : ∀ ω, 0 ≤ f ω) (hg₀ : ∀ ω, 0 ≤ g ω) (hk₀ : ∀ ω, 0 ≤ k ω)
    (θ : ℝ≥0∞)
    (htail : ∀ t > 0, upperTail μ f t ≤ θ * upperTail μ g t + upperTail μ k t) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤
      θ * (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) + (∫⁻ ω, ENNReal.ofReal (k ω) ∂μ) := by
  rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all μ hf₀) hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt μ (ae_of_all μ hg₀) hg.aemeasurable,
    lintegral_eq_lintegral_meas_lt μ (ae_of_all μ hk₀) hk.aemeasurable]
  change (∫⁻ t in Ioi (0 : ℝ), upperTail μ f t) ≤
    θ * (∫⁻ t in Ioi (0 : ℝ), upperTail μ g t) +
      (∫⁻ t in Ioi (0 : ℝ), upperTail μ k t)
  rw [← lintegral_const_mul θ (measurable_upperTail μ g),
    ← lintegral_add_left (measurable_const.mul (measurable_upperTail μ g))]
  exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall htail))

private noncomputable def moment (μ : Measure Ω) (p : ℝ) (f : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ

private theorem moment_div (μ : Measure Ω) {p d : ℝ} (hp : 0 < p) (hd : 0 < d)
    {f : Ω → ℝ} (hf : Measurable f) (hf₀ : ∀ ω, 0 ≤ f ω) :
    moment μ p (fun ω ↦ f ω / d) = ENNReal.ofReal (d ^ (-p)) * moment μ p f := by
  unfold moment
  have hpow : Measurable (fun ω ↦ ENNReal.ofReal (f ω ^ p)) :=
    ((Real.continuous_rpow_const hp.le).measurable.comp hf).ennreal_ofReal
  rw [← lintegral_const_mul _ hpow]
  apply lintegral_congr
  intro ω
  rw [Real.div_rpow (hf₀ ω) hd.le, Real.rpow_neg hd.le, div_eq_inv_mul,
    ENNReal.ofReal_mul (by positivity)]

private theorem upperTail_div_rpow (μ : Measure Ω) {p d t : ℝ}
    (hp : 0 < p) (hd : 0 < d) (ht : 0 < t) {f : Ω → ℝ} (hf₀ : ∀ ω, 0 ≤ f ω) :
    upperTail μ (fun ω ↦ (f ω / d) ^ p) t =
      upperTail μ f (d * t ^ (1 / p)) := by
  have htroot : 0 ≤ t ^ (1 / p) := Real.rpow_nonneg ht.le _
  have htback : (t ^ (1 / p)) ^ p = t := by
    rw [← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  unfold upperTail
  congr 1
  ext ω
  change (t < (f ω / d) ^ p) ↔ d * t ^ (1 / p) < f ω
  calc
    t < (f ω / d) ^ p ↔ t ^ (1 / p) < f ω / d := by
      conv_lhs => lhs; rw [← htback]
      exact Real.rpow_lt_rpow_iff htroot (div_nonneg (hf₀ ω) hd.le) hp
    _ ↔ d * t ^ (1 / p) < f ω := by rw [lt_div_iff₀ hd, mul_comm]

private theorem truncated_moment_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ ω, 0 ≤ X ω) (hY₀ : ∀ ω, 0 ≤ Y ω)
    {p h θ : ℝ} (hp : 0 < p) (hh : 0 < h) (hθ : 0 < θ)
    (htail : ∀ a b : ℝ, 0 < a → 0 < b →
      upperTail μ Y (a + b) ≤ ENNReal.ofReal θ * upperTail μ Y a +
        upperTail μ X (θ * b))
    (n : ℕ) (hdiff : θ ≤ (1 + h) ^ (-p)) :
    ENNReal.ofReal ((1 + h) ^ (-p) - θ) * moment μ p (fun ω ↦ min (Y ω) n) ≤
      ENNReal.ofReal ((θ * h) ^ (-p)) * moment μ p X := by
  let Z : Ω → ℝ := fun ω ↦ min (Y ω) n
  have hZ : Measurable Z := hY.min measurable_const
  have hZ₀ (ω : Ω) : 0 ≤ Z ω := le_min (hY₀ ω) (Nat.cast_nonneg n)
  have hZY (ω : Ω) : Z ω ≤ Y ω := min_le_left _ _
  have hZn (ω : Ω) : Z ω ≤ n := min_le_right _ _
  have hq : 0 < 1 + h := by linarith
  have hs : 0 < θ * h := mul_pos hθ hh
  have hscaled : moment μ p (fun ω ↦ Z ω / (1 + h)) ≤
      ENNReal.ofReal θ * moment μ p Z + moment μ p (fun ω ↦ X ω / (θ * h)) := by
    have hpow : Measurable (fun x : ℝ ↦ x ^ p) :=
      (Real.continuous_rpow_const hp.le).measurable
    apply lintegral_le_of_upperTail_le μ
      (hpow.comp (hZ.div_const _)) (hpow.comp hZ) (hpow.comp (hX.div_const _))
      (fun ω ↦ Real.rpow_nonneg (div_nonneg (hZ₀ ω) hq.le) _)
      (fun ω ↦ Real.rpow_nonneg (hZ₀ ω) _)
      (fun ω ↦ Real.rpow_nonneg (div_nonneg (hX₀ ω) hs.le) _)
    intro t ht
    change upperTail μ (fun ω ↦ (Z ω / (1 + h)) ^ p) t ≤
      ENNReal.ofReal θ * upperTail μ (fun ω ↦ Z ω ^ p) t +
        upperTail μ (fun ω ↦ (X ω / (θ * h)) ^ p) t
    have hmid : upperTail μ (fun ω ↦ Z ω ^ p) t = upperTail μ Z (t ^ (1 / p)) := by
      simpa using upperTail_div_rpow μ hp zero_lt_one ht hZ₀
    rw [upperTail_div_rpow μ hp hq ht hZ₀, hmid, upperTail_div_rpow μ hp hs ht hX₀]
    let a := t ^ (1 / p)
    have ha : 0 < a := Real.rpow_pos_of_pos ht _
    change upperTail μ Z ((1 + h) * a) ≤
      ENNReal.ofReal θ * upperTail μ Z a + upperTail μ X ((θ * h) * a)
    by_cases han : a < n
    · have heq : upperTail μ Z a = upperTail μ Y a := by
        unfold upperTail
        congr 1
        ext ω
        change a < min (Y ω) n ↔ a < Y ω
        simp [lt_min_iff, han]
      rw [heq, add_mul, one_mul, mul_assoc]
      exact (measure_mono (fun ω hω ↦ hω.trans_le (hZY ω))).trans
        (htail a (h * a) ha (mul_pos hh ha))
    · have hempty : {ω | (1 + h) * a < Z ω} = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro ω hω
        have hbound : (n : ℝ) ≤ (1 + h) * a :=
          (le_of_not_gt han).trans (by nlinarith [mul_pos hh ha])
        exact (not_lt_of_ge ((hZn ω).trans hbound)) hω
      simp [upperTail, hempty]
  rw [moment_div μ hp hq hZ hZ₀, moment_div μ hp hs hX hX₀] at hscaled
  have hsplit : ENNReal.ofReal ((1 + h) ^ (-p)) =
      ENNReal.ofReal θ + ENNReal.ofReal ((1 + h) ^ (-p) - θ) := by
    rw [← ENNReal.ofReal_add hθ.le (sub_nonneg.mpr hdiff)]
    congr 1
    ring
  have hfinite : moment μ p Z < ∞ := by
    calc
      moment μ p Z ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((n : ℝ) ^ p) ∂μ :=
        lintegral_mono (fun ω ↦ ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (hZ₀ ω) (hZn ω) hp.le))
      _ < ∞ := by rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
  rw [hsplit, add_mul] at hscaled
  exact ENNReal.le_of_add_le_add_left
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite).ne hscaled


private theorem moment_eq_iSup_truncations (μ : Measure Ω) {Y : Ω → ℝ}
    (hY : Measurable Y) (hY₀ : ∀ ω, 0 ≤ Y ω) {p : ℝ} (hp : 0 < p) :
    moment μ p Y = ⨆ n : ℕ, moment μ p (fun ω ↦ min (Y ω) n) := by
  let F (n : ℕ) (ω : Ω) := ENNReal.ofReal (min (Y ω) (n : ℝ) ^ p)
  have hF (n : ℕ) : Measurable (F n) :=
    ((Real.continuous_rpow_const hp.le).measurable.comp
      (hY.min measurable_const)).ennreal_ofReal
  have hmono : Monotone F := by
    intro m n hmn ω
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
      (le_min (hY₀ ω) (Nat.cast_nonneg m)) (min_le_min_left _ (Nat.cast_le.mpr hmn)) hp.le)
  have hpoint (ω : Ω) : (⨆ n, F n ω) = ENNReal.ofReal (Y ω ^ p) := by
    obtain ⟨n, hn⟩ := exists_nat_ge (Y ω)
    apply le_antisymm
    · exact iSup_le (fun m ↦ ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
        (le_min (hY₀ ω) (Nat.cast_nonneg m)) (min_le_left _ _) hp.le))
    · simpa [F, min_eq_left hn] using (le_iSup (fun m ↦ F m ω) n)
  change (∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ) = ⨆ n, ∫⁻ ω, F n ω ∂μ
  simp_rw [← lintegral_iSup hF hmono, hpoint]

private theorem eLpNorm_eq_moment_rpow {μ : Measure Ω} {f : Ω → ℝ}
    (hf₀ : ∀ ω, 0 ≤ f ω) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ = moment μ p f ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  unfold moment
  simp_rw [Real.enorm_of_nonneg (hf₀ _), ENNReal.ofReal_rpow_of_nonneg (hf₀ _) hp.le]

/-- **Lemma 2.1** of *Maximal inequalities, weighted BMO processes and the largest-jump normaliser*.

A good-λ tail bound for two nonnegative random variables implies a bound on
their extended `Lᵖ` seminorms. No moment finiteness hypothesis is required. -/
theorem goodLambda_eLpNorm_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ ω, 0 ≤ X ω) (hY₀ : ∀ ω, 0 ≤ Y ω)
    {p : ℝ} (hp : 0 < p)
    (htail : ∀ a b θ : ℝ, 0 < a → 0 < b → 0 < θ → θ < 1 →
      μ {ω | a + b < Y ω} ≤ ENNReal.ofReal θ * μ {ω | a < Y ω} +
        μ {ω | θ * b < X ω}) :
    eLpNorm Y (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (goodLambdaConstant p) * eLpNorm X (ENNReal.ofReal p) μ := by
  let h : ℝ := 1 / p
  let q : ℝ := 1 + h
  let θ : ℝ := q ^ (-(p + 1))
  let s : ℝ := θ * h
  have hh : 0 < h := one_div_pos.mpr hp
  have hq : 1 < q := lt_add_of_pos_right 1 hh
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hθ : 0 < θ := Real.rpow_pos_of_pos hq₀ _
  have hθ₁ : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hs : 0 < s := mul_pos hθ hh
  have hA : q ^ (-p) = θ * q := by
    dsimp [θ]
    rw [← Real.rpow_add_one hq₀.ne', show -(p + 1) + 1 = -p by ring]
  have hdiff : q ^ (-p) - θ = s := by
    rw [hA]
    dsimp [q, s]
    ring
  have hθle : θ ≤ q ^ (-p) := sub_nonneg.mp (hdiff ▸ hs.le)
  have hC : 0 < goodLambdaConstant p := by unfold goodLambdaConstant; positivity
  have hsInv : s⁻¹ = p * q ^ (p + 1) := by
    rw [show s = θ / p by simp [s, h, div_eq_mul_inv], inv_div, div_eq_mul_inv]
    simp [θ, Real.rpow_neg hq₀.le]
  have hCpow : goodLambdaConstant p ^ p = s ^ (-(p + 1)) := by
    unfold goodLambdaConstant
    change (p * (p * q ^ ((p + 1) ^ (2 : ℕ))) ^ (1 / p)) ^ p = _
    rw [Real.mul_rpow hp.le (by positivity), ← Real.rpow_mul (by positivity),
      one_div_mul_cancel hp.ne', Real.rpow_one, Real.rpow_neg hs.le,
      ← Real.inv_rpow hs.le, hsInv, Real.mul_rpow hp.le (by positivity),
      ← Real.rpow_mul hq₀.le, ← pow_two, Real.rpow_add_one hp.ne']
    ring
  have hsPow : s ^ (-p) = s * goodLambdaConstant p ^ p := by
    rw [hCpow, mul_comm, ← Real.rpow_add_one hs.ne', show -(p + 1) + 1 = -p by ring]
  have hm : moment μ p Y ≤ ENNReal.ofReal (goodLambdaConstant p ^ p) * moment μ p X := by
    rw [moment_eq_iSup_truncations μ hY hY₀ hp]
    apply iSup_le
    intro n
    have hn := truncated_moment_bound μ hX hY hX₀ hY₀ hp hh hθ
      (fun a b ha hb ↦ htail a b θ ha hb hθ hθ₁) n hθle
    change ENNReal.ofReal (q ^ (-p) - θ) * _ ≤ ENNReal.ofReal (s ^ (-p)) * _ at hn
    rw [hdiff, hsPow, ENNReal.ofReal_mul hs.le, mul_assoc] at hn
    exact (ENNReal.mul_le_mul_left (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top).mp hn
  rw [eLpNorm_eq_moment_rpow hY₀ hp, eLpNorm_eq_moment_rpow hX₀ hp]
  have hroot := (ENNReal.rpow_le_rpow_iff (one_div_pos.mpr hp)).2 hm
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
    ← ENNReal.ofReal_rpow_of_nonneg hC.le hp.le, ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one] at hroot

end WeightedBMO
