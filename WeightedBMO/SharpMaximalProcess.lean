import WeightedBMO.PathMaximum

/-!
# The sharp maximal function `X^♯`

`def.dagger` of Khoa Lê, *Maximal inequalities and weighted BMO processes*
(arXiv:2211.15550v3):

  `X^♯_{t,τ} = sup_{s∈[t,τ]} E_s d(X_{s-}, X_τ)`,   `X^♯_τ = X^♯_{0,τ}`,

where `E_· Ξ` denotes a right-continuous version of `t ↦ E_t Ξ`.

This file makes `X^♯_{t,τ}` an object of the formalization: `sharpMaximal` takes
the supremum of the conditional-expectation process over the *rational* grid,
`sup_{q ∈ ℚ ∩ [t,τ]} E_q d(X_{q-}, X_τ)`, read in `ℝ≥0∞`.  A supremum over `ℚ`
is countable, hence:

* `measurable_sharpMaximal`: it is measurable with **no** regularity assumption
  on the paths (a condExp is always strongly measurable, and a countable supremum
  of measurable functions is measurable);
* `sharpMaximal_antitone`: it decreases in `t`, since `[t₂,τ] ⊆ [t₁,τ]` for
  `t₁ ≤ t₂` — this is the monotonicity that makes `E_t X^♯_{t,τ}` a
  supermartingale in the paper.

For right-continuous paths the rational supremum agrees with the supremum over
all of `[t,τ]`, so this is the paper's `X^♯_{t,τ}` up to a null set; making that
precise, and obtaining the *right-continuous* version of `t ↦ E_t X^♯_{t,τ}`,
is the regularisation theorem of Dellacherie--Meyer II (2.9).  Mathlib has no
such theorem (no RCLL/càdlàg modification of a martingale or supermartingale,
and optional sampling only in discrete time), so the theorems of this
development still take `ψ_t = E_t X^♯_{t,τ}` and `Ψ = X^♯_τ` as hypotheses;
`sharpMaximal` records what those hypotheses are hypotheses *about*.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} {E : Type*} [PseudoMetricSpace E] [m : MeasurableSpace Ω]
  {μ : Measure Ω} {ℱ : Filtration ℝ m}

/-- `X^♯_{t,τ} = sup_{s∈[t,τ]} E_s d(X_{s-}, X_τ)`, taken over the rational grid
and read in `ℝ≥0∞`. -/
noncomputable def sharpMaximal (X Xl : Ω → ℝ → E) (τ t : ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ q : {q : ℚ // (q : ℝ) ∈ Icc t τ},
    ENNReal.ofReal (μ[fun ω' => dist (Xl ω' (q : ℝ)) (X ω' τ) | ℱ (q : ℝ)] ω)

/-- `X^♯_τ = X^♯_{0,τ}`, the sharp maximal function at the horizon. -/
noncomputable def sharpMaximalAt (X Xl : Ω → ℝ → E) (τ : ℝ) : Ω → ℝ≥0∞ :=
  sharpMaximal (μ := μ) (ℱ := ℱ) X Xl τ 0

/-- `X^♯_{t,τ}` is measurable — no regularity of the paths is needed, because the
supremum is over the countable set `ℚ ∩ [t,τ]` and a conditional expectation is
strongly measurable. -/
theorem measurable_sharpMaximal (X Xl : Ω → ℝ → E) (τ t : ℝ) :
    Measurable (sharpMaximal (μ := μ) (ℱ := ℱ) X Xl τ t) :=
  Measurable.iSup fun q =>
    ENNReal.measurable_ofReal.comp
      ((stronglyMeasurable_condExp (μ := μ) (m := ℱ (q : ℝ))).measurable.mono (ℱ.le _) le_rfl)

theorem measurable_sharpMaximalAt (X Xl : Ω → ℝ → E) (τ : ℝ) :
    Measurable (sharpMaximalAt (μ := μ) (ℱ := ℱ) X Xl τ) :=
  measurable_sharpMaximal X Xl τ 0

theorem sharpMaximal_nonneg (X Xl : Ω → ℝ → E) (τ t : ℝ) (ω : Ω) :
    0 ≤ sharpMaximal (μ := μ) (ℱ := ℱ) X Xl τ t ω := zero_le _

/-- `X^♯_{·,τ}` decreases: `[t₂,τ] ⊆ [t₁,τ]` for `t₁ ≤ t₂`.  This is the
monotonicity behind the supermartingale property of `E_t X^♯_{t,τ}`. -/
theorem sharpMaximal_antitone (X Xl : Ω → ℝ → E) (τ : ℝ) :
    Antitone (sharpMaximal (μ := μ) (ℱ := ℱ) X Xl τ) := by
  intro t₁ t₂ ht ω
  refine iSup_le fun q => ?_
  exact le_iSup (fun q : {q : ℚ // (q : ℝ) ∈ Icc t₁ τ} =>
    ENNReal.ofReal (μ[fun ω' => dist (Xl ω' (q : ℝ)) (X ω' τ) | ℱ (q : ℝ)] ω))
    ⟨q.1, ⟨ht.trans q.2.1, q.2.2⟩⟩

/-- Each term of the supremum is dominated by `X^♯_{t,τ}`. -/
theorem condExp_le_sharpMaximal (X Xl : Ω → ℝ → E) {τ t : ℝ} (q : ℚ) (hq : (q : ℝ) ∈ Icc t τ)
    (ω : Ω) :
    ENNReal.ofReal (μ[fun ω' => dist (Xl ω' (q : ℝ)) (X ω' τ) | ℱ (q : ℝ)] ω) ≤
      sharpMaximal (μ := μ) (ℱ := ℱ) X Xl τ t ω :=
  le_iSup (fun q : {q : ℚ // (q : ℝ) ∈ Icc t τ} =>
    ENNReal.ofReal (μ[fun ω' => dist (Xl ω' (q : ℝ)) (X ω' τ) | ℱ (q : ℝ)] ω))
    ⟨q, hq⟩

end WeightedBMO
