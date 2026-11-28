import WeightedBMO.JohnNirenberg
import WeightedBMO.DoobMaximal

/-!
# Theorem 1.1 of *Maximal inequalities, weighted BMO processes and the largest-jump normaliser*

Khoa Lê, arXiv:2211.15550, deduces the maximal inequality
`est.upperbound`/`est.Smaximal` for an RCLL adapted integrable process `X` in a
metric space from the John--Nirenberg inequality `ineq.JNweighted` applied to the path
`V_t = d(X_a, X_t)`. Its two ingredients are:

* (b) `V` lies in weighted BMO with weight `2X^♯`, where
  `X^♯_{s,T} = sup_{t∈[s,T]} E_s d(X_{t-}, X_T)` is the sharp maximal function.
  The paper derives this from the two estimates
  `E_S d(X_U, X_T) ≤ E_S X^♯_{S,T}` and `E_S d(X_{S-}, X_T) ≤ E_S X^♯_{S,T}`,
  so we take a process `ψ` with those two domination properties as a
  hypothesis instead of proving the measurability of the supremum over times
  (which needs an RCLL version of `t ↦ E_t X^♯_{t,T}`, Dellacherie--Meyer II
  (2.9), not available here).

* (c) Doob's `L^p` maximal inequality, supplied by `WeightedBMO/DoobMaximal.lean`,
  turns `‖sup_t E_t X^♯_{t,T}‖_p` into `p/(p-1) ‖X^♯_T‖_p`.

This file proves both steps. `weightedBMOOfSharpMaximal` is (b).
`sharpMaximal_eLpNorm_le` is `ineq.JNweighted` for the path of increments, with the exact
costant `goodLambdaConstant p = p c_p` on the weight `2ψ`.
`martingale_eLpNorm_maximal_le_of_terminal` is Doob's step in the form the
paper uses. The continuous-time formulation of the Doob step still needs a
maximal inequality for RCLL martingales, which mathlib does not have.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ m}

/-- **Step (b) of Theorem 1.1.** If `ψ` dominates, on every event known at a
stopping time `S`, the conditional means of both `d(X_U, X_T)` (for stopping
times `S ≤ U ≤ T`) and `d(X_{S-}, X_T)`, then the path `t ↦ d(X_a, X_t)` lies
in `bmo` with weight `2ψ` and bound `1`. -/
theorem weightedBMOOfSharpMaximal {E : Type*} [PseudoMetricSpace E]
    (X Xl : Ω → ℝ → E) (ψ : Ω → ℝ → ℝ) {a T : ℝ}
    (hψpos : ∀ ω t, t ∈ Icc a T → 0 < ψ ω t)
    (hdom : ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
      (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫ ω in G, dist (X ω (U ω)) (X ω T) ∂μ) ≤ ∫ ω in G, ψ ω (S ω) ∂μ)
    (hdomL : ∀ (S : Ω → ℝ) (hS : IsStoppingTime ℱ S),
      (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ T) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫ ω in G, dist (Xl ω (S ω)) (X ω T) ∂μ) ≤ ∫ ω in G, ψ ω (S ω) ∂μ)
    (hdata : ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
      (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
      Measurable[hS.measurableSpace] (fun ω => ψ ω (S ω)) ∧
      Measurable[m] (fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|) ∧
      Integrable (fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|) μ ∧
      Integrable (fun ω => dist (X ω (U ω)) (X ω T)) μ ∧
      Integrable (fun ω => dist (Xl ω (S ω)) (X ω T)) μ ∧
      Integrable (fun ω => ψ ω (S ω)) μ) :
    WeightedBMOOn μ ℱ (fun ω t => dist (X ω a) (X ω t)) (fun ω t => dist (X ω a) (Xl ω t))
      (fun ω t => 2 * ψ ω t) a T 1 := by
  refine ⟨by norm_num, ?_⟩
  intro S U hS hU ha hsu huT G hG
  obtain ⟨hψSm, hΔm, hΔi, hfi, hgi, hψSi⟩ := hdata S U hS hU ha hsu huT
  -- (i) conditional means of the two increments are dominated by `ψ S`
  have hFs : μ[fun ω => dist (X ω (U ω)) (X ω T) | hS.measurableSpace] ≤ᵐ[μ] fun ω => ψ ω (S ω) := by
    refine ae_le_of_ae_le_trim (hm := hS.measurableSpace_le) ?_
    apply ae_le_of_forall_setIntegral_le
      (integrable_condExp.trim hS.measurableSpace_le stronglyMeasurable_condExp)
      (hψSi.trim hS.measurableSpace_le hψSm.stronglyMeasurable)
    intro W hW _
    rw [← setIntegral_trim hS.measurableSpace_le stronglyMeasurable_condExp hW,
      setIntegral_condExp hS.measurableSpace_le hfi hW,
      ← setIntegral_trim hS.measurableSpace_le hψSm.stronglyMeasurable hW]
    exact hdom S U hS hU ha hsu huT W hW
  have hGs : μ[fun ω => dist (Xl ω (S ω)) (X ω T) | hS.measurableSpace] ≤ᵐ[μ] fun ω => ψ ω (S ω) := by
    refine ae_le_of_ae_le_trim (hm := hS.measurableSpace_le) ?_
    apply ae_le_of_forall_setIntegral_le
      (integrable_condExp.trim hS.measurableSpace_le stronglyMeasurable_condExp)
      (hψSi.trim hS.measurableSpace_le hψSm.stronglyMeasurable)
    intro W hW _
    rw [← setIntegral_trim hS.measurableSpace_le stronglyMeasurable_condExp hW,
      setIntegral_condExp hS.measurableSpace_le hgi hW,
      ← setIntegral_trim hS.measurableSpace_le hψSm.stronglyMeasurable hW]
    exact hdomL S hS ha (fun ω => (hsu ω).trans (huT ω)) W hW
  -- (ii) reverse triangle inequality, then monotonicity of the conditional mean
  have htri : (fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|) ≤ᵐ[μ]
      fun ω => dist (X ω (U ω)) (X ω T) + dist (Xl ω (S ω)) (X ω T) :=
    Eventually.of_forall fun ω => by
      calc |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|
          = |dist (X ω (U ω)) (X ω a) - dist (Xl ω (S ω)) (X ω a)| := by
            simp only [dist_comm (X ω a)]
        _ ≤ dist (X ω (U ω)) (Xl ω (S ω)) := abs_dist_sub_le _ _ _
        _ ≤ dist (X ω (U ω)) (X ω T) + dist (Xl ω (S ω)) (X ω T) :=
            dist_triangle_right _ _ _
  have hcomb : μ[fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))| | hS.measurableSpace]
      ≤ᵐ[μ] fun ω => 2 * ψ ω (S ω) := by
    have hmono := condExp_mono (m := hS.measurableSpace) hΔi (hfi.add hgi) htri
    have hadd := condExp_add hfi hgi hS.measurableSpace
    filter_upwards [hmono, hadd, hFs, hGs] with ω h1 h2 h3 h4
    rw [h2] at h1
    simp only [Pi.add_apply] at h1
    linarith
  -- (iii) the weighted BMO test follows from the weighted conditional mean bound
  let F : Ω → ℝ := fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|
  let W : Ω → ℝ := fun ω => 2 * ψ ω (S ω)
  have hpos : ∀ ω, 0 < W ω := fun ω =>
    mul_pos (by norm_num) (hψpos ω (S ω) ⟨ha ω, (hsu ω).trans (huT ω)⟩)
  have hWm : Measurable[hS.measurableSpace] W := by
    have h := hψSm.const_mul (2 : ℝ)
    simpa [W, mul_comm] using h
  have hFm : Measurable[m] F := hΔm
  have hneg : ∀ᵐ ω ∂μ, 0 ≤ MeasureTheory.condExp hS.measurableSpace μ F ω :=
    condExp_nonneg (ae_of_all μ fun ω => abs_nonneg _)
  have hcond : eLpNorm (fun ω => MeasureTheory.condExp hS.measurableSpace μ F ω / W ω) ⊤ μ ≤
      ENNReal.ofReal 1 := by
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [hcomb, hneg] with ω h1 h2
    rw [Real.enorm_of_nonneg (div_nonneg h2 (hpos ω).le)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_one (hpos ω)]
    exact h1
  have htest := (@weighted_condExp_iff_event_tests Ω m hS.measurableSpace hS.measurableSpace_le μ _
    F W hFm hΔi (fun ω => abs_nonneg _) hWm hpos 1).1 hcond
  exact htest G hG

/-- **`est.upperbound` of Theorem 1.1** with the sharp maximal function as a
hypothesis: on every initial event, the maximal function of the path
`t ↦ d(X_a, X_t)` is controlled by the supremum of `2ψ` with the paper's
constant (`goodLambdaConstant p` is `p * c_p`). -/
theorem sharpMaximal_eLpNorm_le {E : Type*} [PseudoMetricSpace E]
    (X Xl : Ω → ℝ → E) (ψ : Ω → ℝ → ℝ) {a T : ℝ} (haT : a ≤ T)
    (hℱ : RightContinuousFiltration ℱ)
    (hψpos : ∀ ω t, t ∈ Icc a T → 0 < ψ ω t)
    (hψmeas : ∀ t ∈ Icc a T, Measurable[ℱ t] (fun ω => ψ ω t))
    (hdom : ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
      (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫ ω in G, dist (X ω (U ω)) (X ω T) ∂μ) ≤ ∫ ω in G, ψ ω (S ω) ∂μ)
    (hdomL : ∀ (S : Ω → ℝ) (hS : IsStoppingTime ℱ S),
      (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ T) →
      ∀ G : Set Ω, MeasurableSet[hS.measurableSpace] G →
        (∫ ω in G, dist (Xl ω (S ω)) (X ω T) ∂μ) ≤ ∫ ω in G, ψ ω (S ω) ∂μ)
    (hdata : ∀ (S U : Ω → ℝ) (hS : IsStoppingTime ℱ S), IsStoppingTime ℱ U →
      (∀ ω, a ≤ S ω) → (∀ ω, S ω ≤ U ω) → (∀ ω, U ω ≤ T) →
      Measurable[hS.measurableSpace] (fun ω => ψ ω (S ω)) ∧
      Measurable[m] (fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|) ∧
      Integrable (fun ω => |dist (X ω a) (X ω (U ω)) - dist (X ω a) (Xl ω (S ω))|) μ ∧
      Integrable (fun ω => dist (X ω (U ω)) (X ω T)) μ ∧
      Integrable (fun ω => dist (Xl ω (S ω)) (X ω T)) μ ∧
      Integrable (fun ω => ψ ω (S ω)) μ)
    (mv : ∀ u ∈ Icc a T, Measurable[ℱ u] (fun ω => dist (X ω a) (X ω u)))
    (cX : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (X ω) (Ici u) u)
    (lX : ∀ ω u, u ∈ Ioc a T → Tendsto (X ω) (𝓝[<] u) (𝓝 (Xl ω u)))
    (cw : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (ψ ω) (Ici u) u)
    (lw : ∀ ω u, u ∈ Ioc a T → ∃ l, Tendsto (ψ ω) (𝓝[<] u) (𝓝 l))
    {p : ℝ} (hp : 0 < p) {E₀ : Set Ω} (hE : MeasurableSet[ℱ a] E₀) :
    eLpNorm (fun ω => intervalSup (fun u => dist (X ω a) (X ω u)) a T) (ENNReal.ofReal p)
        (μ.restrict E₀) ≤
      ENNReal.ofReal (goodLambdaConstant p) *
        eLpNorm (fun ω => intervalSup (fun u => 2 * ψ ω u) a T) (ENNReal.ofReal p)
          (μ.restrict E₀) := by
  have hB := weightedBMOOfSharpMaximal (ℱ := ℱ) X Xl ψ hψpos hdom hdomL hdata
  have hφ : ∀ ω u, u ∈ Icc a T → 0 < 2 * ψ ω u := fun ω u hu =>
    mul_pos (by norm_num) (hψpos ω u hu)
  have hψbdd : ∀ ω, BddAbove ((fun u => 2 * ψ ω u) '' Icc a T) := by
    intro ω
    obtain ⟨d, hd⟩ := cadlag_bounded (cw ω) (lw ω)
    refine ⟨2 * d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact mul_le_mul_of_nonneg_left
      ((le_abs_self (ψ ω u)).trans (hd (mem_image_of_mem _ hu))) (by norm_num)
  have hcw : ∀ ω u, u ∈ Ico a T → ContinuousWithinAt (fun t => 2 * ψ ω t) (Ici u) u :=
    fun ω u hu => (cw ω u hu).const_mul 2
  have hlw : ∀ ω u, u ∈ Ioc a T → ∃ l, Tendsto (fun t => 2 * ψ ω t) (𝓝[<] u) (𝓝 l) := by
    intro ω u hu
    obtain ⟨l, hl⟩ := lw ω u hu
    exact ⟨2 * l, hl.const_mul 2⟩
  have hmw : ∀ u ∈ Icc a T, Measurable[ℱ u] (fun ω => 2 * ψ ω u) := by
    intro u hu
    have h := (hψmeas u hu).const_mul (2 : ℝ)
    simpa [mul_comm] using h
  have hcv : ∀ ω u, u ∈ Ico a T →
      ContinuousWithinAt (fun t => dist (X ω a) (X ω t)) (Ici u) u :=
    fun ω u hu => continuousWithinAt_const.dist (cX ω u hu)
  have hlv : ∀ ω u, u ∈ Ioc a T →
      Tendsto (fun t => dist (X ω a) (X ω t)) (𝓝[<] u) (𝓝 (dist (X ω a) (Xl ω u))) :=
    fun ω u hu => tendsto_const_nhds.dist (lX ω u hu)
  have hρ : oscillationModulus μ ℱ (fun ω t => dist (X ω a) (X ω t))
      (fun ω t => dist (X ω a) (Xl ω t)) (fun ω t => 2 * ψ ω t) a T ≤ 1 :=
    csInf_le ⟨0, fun c hc => hc.1⟩ ⟨by norm_num, stoppedBound_of_bmo hB le_rfl le_rfl hφ hψbdd⟩
  have hmain := weightedBMO_maximal_moments (μ := μ) ℱ hℱ
    (fun ω t => dist (X ω a) (X ω t)) (fun ω t => dist (X ω a) (Xl ω t))
    (fun ω t => 2 * ψ ω t) (r := a) (T := T) (B := 1) haT hp hB hφ mv hmw hcv hcw hlv hlw hE
  have hC : 0 ≤ goodLambdaConstant p := by
    unfold goodLambdaConstant
    positivity
  have hconst : ENNReal.ofReal (goodLambdaConstant p *
      oscillationModulus μ ℱ (fun ω t => dist (X ω a) (X ω t))
        (fun ω t => dist (X ω a) (Xl ω t)) (fun ω t => 2 * ψ ω t) a T) ≤
      ENNReal.ofReal (goodLambdaConstant p) := by
    apply ENNReal.ofReal_le_ofReal
    calc goodLambdaConstant p *
          oscillationModulus μ ℱ (fun ω t => dist (X ω a) (X ω t))
            (fun ω t => dist (X ω a) (Xl ω t)) (fun ω t => 2 * ψ ω t) a T
        ≤ goodLambdaConstant p * 1 := mul_le_mul_of_nonneg_left hρ hC
      _ = goodLambdaConstant p := mul_one _
  have hfun : ∀ ω, (fun u => |dist (X ω a) (X ω u) - dist (X ω a) (X ω a)|) =
      fun u => dist (X ω a) (X ω u) := by
    intro ω
    funext u
    rw [dist_self, sub_zero, abs_of_nonneg dist_nonneg]
  have hmain' : eLpNorm (fun ω => intervalSup (fun u => dist (X ω a) (X ω u)) a T)
      (ENNReal.ofReal p) (μ.restrict E₀) ≤
      ENNReal.ofReal (goodLambdaConstant p *
        oscillationModulus μ ℱ (fun ω t => dist (X ω a) (X ω t))
          (fun ω t => dist (X ω a) (Xl ω t)) (fun ω t => 2 * ψ ω t) a T) *
        eLpNorm (fun ω => intervalSup (fun u => 2 * ψ ω u) a T) (ENNReal.ofReal p)
          (μ.restrict E₀) := by
    simpa only [hfun] using hmain
  exact hmain'.trans (mul_le_mul_right' hconst _)

/-- **Step (c) of Theorem 1.1** (Doob's step), in the form the paper uses: a
nonnegative martingale whose terminal value is `Ψ` has maximal function
controlled by `p/(p-1) ‖Ψ‖_p`. In the paper `M_t = E_t X^♯_τ` and
`Ψ = X^♯_τ`, which is `ℱ_τ`-measurable, so `M_τ = Ψ`.

This is the discrete-time form of the step; the continuous-time version needs
a maximal inequality for RCLL martingales (optional sampling), which is not
available here. -/
theorem martingale_eLpNorm_maximal_le_of_terminal {𝒢 : Filtration ℕ m} {f : ℕ → Ω → ℝ}
    (hmart : Martingale f 𝒢 μ) (hnonneg : 0 ≤ f) {Ψ : Ω → ℝ} {N : ℕ}
    (hΨ : f N =ᵐ[μ] Ψ) {p : ℝ} (hp : 1 < p) :
    eLpNorm (subMax f N) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm Ψ (ENNReal.ofReal p) μ :=
  ((martingale_eLpNorm_maximal_le hmart hnonneg hp N).trans_eq (by
    rw [eLpNorm_congr_ae hΨ])).trans_eq (by rfl)

end WeightedBMO
