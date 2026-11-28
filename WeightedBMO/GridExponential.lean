import WeightedBMO.GridJohnNirenberg
import Mathlib.Analysis.SpecialFunctions.Exponential

open MeasureTheory Set Filter
open scoped ENNReal

namespace WeightedBMO

private noncomputable def expTerm (b : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-b) * goodLambdaConstant n) ^ n / n.factorial

/-- The constant M in `def.M`. The term of index zero is one. -/
noncomputable def exponentialBound : ℝ := ∑' n, expTerm 3 n

private theorem constant_nonneg (n : ℕ) : 0 ≤ goodLambdaConstant n := by
  unfold goodLambdaConstant
  positivity

private theorem term_nonneg (b : ℝ) (n : ℕ) : 0 ≤ expTerm b n := by
  unfold expTerm
  have := constant_nonneg n
  positivity

/-- The moment series has room beyond the endpoint exp(-3) in `est.jnexpwei`. -/
theorem summable_exponential_coefficients {b : ℝ} (hb : 2 < b) :
    Summable (fun n : ℕ => (Real.exp (-b) * goodLambdaConstant n)^n / n.factorial) := by
  have hg := (summable_pow_mul_geometric_of_norm_lt_one 1
    (r := Real.exp (2-b)) (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith))).mul_right (Real.exp 3)
  apply Summable.of_norm_bounded_eventually _ hg
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hpow : goodLambdaConstant n ^ n =
      (n : ℝ)^n * ((n : ℝ) * (1 + 1 / (n : ℝ)) ^ (((n : ℝ) + 1)^2)) := by
    unfold goodLambdaConstant
    rw [mul_pow, ← Real.rpow_natCast (_ ^ (1 / (n : ℝ))) n, ← Real.rpow_mul (by positivity),
      one_div_mul_cancel hn₀.ne', Real.rpow_one]
  have hq : (1 + 1 / (n : ℝ)) ^ (((n : ℝ) + 1)^2) ≤ Real.exp ((n : ℝ) + 3) := by
    calc
      _ ≤ (Real.exp (1 / (n : ℝ))) ^ (((n : ℝ) + 1)^2) := Real.rpow_le_rpow (by positivity)
        (by linarith [Real.add_one_le_exp (1 / (n : ℝ))]) (sq_nonneg _)
      _ ≤ _ := by
        rw [← Real.exp_mul, Real.exp_le_exp]
        rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hn₀]
        nlinarith
  have hp : 0 ≤ (Real.exp (-b) * goodLambdaConstant n)^n / n.factorial := by
    have := constant_nonneg n
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hp, mul_pow, hpow, pow_one]
  calc
    _ = (n : ℝ)^n / n.factorial * (1 + 1 / (n : ℝ)) ^ (((n : ℝ) + 1)^2) *
        (Real.exp (-b)) ^ n * n := by ring
    _ ≤ Real.exp n * Real.exp ((n : ℝ) + 3) * Real.exp (-b) ^ n * n := by
      gcongr
      exact Real.pow_div_factorial_le_exp (n : ℝ) hn₀.le n
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      rw [show (n : ℝ) + (n + 3) + n * (-b) = n * (2-b) + 3 by ring, Real.exp_add]
      ring

private theorem summable_expTerm : Summable (expTerm 3) :=
  summable_exponential_coefficients (b := 3) (by norm_num)

/-- Convergence of the defining series for M, including its constant term. -/
theorem hasSum_exponentialBound :
    HasSum (fun n : ℕ => (Real.exp (-3) * goodLambdaConstant n)^n / n.factorial)
      exponentialBound := summable_expTerm.hasSum

private theorem moment_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z : Ω → ℝ} (hZ : ∀ ω, 0 ≤ Z ω) {n : ℕ} (hn : 0 < n) :
    (∫⁻ ω, ENNReal.ofReal (Z ω ^ n) ∂μ) = eLpNorm Z (ENNReal.ofReal n) μ ^ n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hn') ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hn'.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    one_div_mul_cancel hn'.ne', ENNReal.rpow_one]
  simp_rw [Real.enorm_of_nonneg (hZ _), ENNReal.rpow_natCast, ENNReal.ofReal_pow (hZ _)]

/-- Exponential integrability from the integer moment estimates, for every b > 2. -/
theorem exponential_of_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {b : ℝ} (hb₂ : 2 < b)
    {Z : Ω → ℝ} (hm : Measurable Z) (hz : ∀ ω, 0 ≤ Z ω)
    (hb : ∀ n : ℕ, 0 < n → eLpNorm Z (ENNReal.ofReal n) μ ≤
      ENNReal.ofReal (goodLambdaConstant n) * eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal n) μ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (Real.exp (-b) * Z ω)) ∂μ) ≤
      ENNReal.ofReal (∑' n : ℕ, (Real.exp (-b) * goodLambdaConstant n)^n / n.factorial) * μ univ := by
  let a (n : ℕ) := Real.exp (-b) ^ n / (n.factorial : ℝ)
  have ha (n : ℕ) : 0 ≤ a n := by unfold a; positivity
  have hseries (ω : Ω) : ENNReal.ofReal (Real.exp (Real.exp (-b) * Z ω)) =
      ∑' n, ENNReal.ofReal (a n) * ENNReal.ofReal (Z ω ^ n) := by
    have expansion (x : ℝ) : Real.exp x = ∑' n : ℕ, x^n / n.factorial := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    let x := Real.exp (-b) * Z ω
    have hx : 0 ≤ x := mul_nonneg (Real.exp_pos _).le (hz ω)
    rw [expansion x, ENNReal.ofReal_tsum_of_nonneg
      (fun n => div_nonneg (pow_nonneg hx n) (Nat.cast_nonneg n.factorial))
      (Real.summable_pow_div_factorial x)]
    apply tsum_congr
    intro n
    rw [← ENNReal.ofReal_mul (ha n)]
    dsimp [x]
    rw [mul_pow]
    congr 1
    unfold a
    ring
  simp_rw [hseries]
  rw [lintegral_tsum (fun n => (measurable_const.mul ((hm.pow_const n).ennreal_ofReal)).aemeasurable)]
  change _ ≤ ENNReal.ofReal (∑' n, expTerm b n) * μ univ
  rw [ENNReal.ofReal_tsum_of_nonneg (term_nonneg b) (summable_exponential_coefficients hb₂),
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [lintegral_const_mul _ ((hm.pow_const n).ennreal_ofReal)]
  cases n with
  | zero => simp [a, expTerm]
  | succ k =>
    let n := k + 1
    have hn : 0 < n := Nat.zero_lt_succ _
    have hpower := pow_le_pow_left' (hb n hn) n
    rw [mul_pow, ← moment_eq μ (fun _ => zero_le_one) hn] at hpower
    simp only [one_pow, ENNReal.ofReal_one, lintegral_const, one_mul] at hpower
    change ENNReal.ofReal (a n) * _ ≤ ENNReal.ofReal (expTerm b n) * _
    rw [moment_eq μ hz hn]
    refine (mul_le_mul_left' hpower _).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_pow (constant_nonneg n), ← ENNReal.ofReal_mul (ha n)]
    congr 2
    unfold expTerm a
    rw [mul_pow]
    ring

/-- The exponential moment of the normalized grid maximum on any initial
event is bounded by the paper's constant M times the mass of the event.
This is the single-interval estimate at unit oscillation. -/
theorem grid_exponential {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (N : ℕ) (v φ : ℕ → Ω → ℝ)
    (hv : ∀ i, Measurable[ℱ i] (v i)) (hφ : ∀ i, Measurable[ℱ i] (φ i))
    (hv₀ : ∀ ω, v 0 ω = 0) (hpos : ∀ i ω, 0 < φ i ω)
    (h : UnitGridOscillation μ ℱ N v φ) {E : Set Ω} (hE : MeasurableSet[ℱ 0] E)
    {rate : ℝ} (hrate : rate ≤ Real.exp (-3)) :
    let W := fun j ω => gridMax (fun i => φ i ω) 0 j
    let Z := fun ω => gridMax (fun i => |v i ω| / W i ω) 0 N
    (∫⁻ ω in E, ENNReal.ofReal (Real.exp (rate * Z ω)) ∂μ) ≤
      ENNReal.ofReal exponentialBound * μ E := by
  let W := fun j (ω : Ω) => gridMax (fun i => φ i ω) 0 j
  let Z := fun (ω : Ω) => gridMax (fun i => |v i ω| / W i ω) 0 N
  have hW (j : ℕ) : Measurable (W j) :=
    measurable_gridMax j (fun i _ => (hφ i).mono (ℱ.le i) le_rfl)
  have hm : Measurable Z := measurable_gridMax N (fun i _ =>
    (continuous_abs.measurable.comp ((hv i).mono (ℱ.le i) le_rfl)).div (hW i))
  have hz (ω : Ω) : 0 ≤ Z ω := by
    have hw : 0 ≤ W N ω := (hpos N ω).le.trans
      (le_gridMax (f := fun i => φ i ω) (Nat.zero_le N) le_rfl)
    exact (div_nonneg (abs_nonneg _) hw).trans
      (le_gridMax (f := fun i => |v i ω| / W i ω) (Nat.zero_le N) le_rfl)
  have he := exponential_of_moments (μ.restrict E) (b := 3) (by norm_num) hm hz (fun n hn =>
    (grid_johnNirenberg μ ℱ N v φ hv hφ hv₀ hpos h hE (Nat.cast_pos.mpr hn)).2)
  simp only [Measure.restrict_apply_univ] at he
  exact (lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (hz ω))))).trans he

end WeightedBMO
