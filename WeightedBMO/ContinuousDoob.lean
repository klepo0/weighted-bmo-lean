import WeightedBMO.DoobMaximal

/-!
# The continuous-time Doob step

The last step of Theorem 1.1 in Khoa Lê, *Maximal inequalities and weighted
BMO processes* (arXiv:2211.15550v3) is Doob's maximal inequality for the
nonnegative martingale `M_t = E_t X^♯_τ`, whose terminal value is `X^♯_τ`:

  `‖sup_{t∈[0,T]} M_t‖_p ≤ p/(p-1) ‖X^♯_τ‖_p`  for `p > 1`.

Mathlib has optional sampling only in discrete time. Rather than build
continuous-time optional sampling, we run the argument on the dyadic grids:
for each `n` the sampled process `k ↦ M(kT/2^n)` is a finite-time nonnegative
martingale, so the discrete first-passage inequality `MeasureTheory.maximal_ineq`
(and hence the discrete `L^p` bound of `WeightedBMO/DoobMaximal.lean`) applies.
The dyadic maximal functions increase to the maximal function over `[0,T]`
(for right-continuous paths), so monotone convergence gives the
continuous-time bound with the same constant.

Main results: `eLpNorm_supOn_le`, its terminal-value form
`eLpNorm_supOn_le_of_terminal`, and `ofReal_le_supOn`, which identifies the
dyadic supremum `supOn` with the supremum over the interval.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WeightedBMO

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The `k`-th point of the `n`-th dyadic grid of `[0,T]`. -/
noncomputable def dyadicTime (T : ℝ) (n k : ℕ) : ℝ := k * T / 2 ^ n

/-- The maximum of `M` over the `n`-th dyadic grid of `[0,T]`. -/
noncomputable def dyadicMax (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_succ fun k => M (dyadicTime T n k) ω

/-- The supremum of `M` over `[0,T]`, as an extended nonnegative number.  For a
right-continuous `M` this is `sup_{t∈[0,T]} M_t` (see `ofReal_le_supOn`). -/
noncomputable def supOn (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (dyadicMax M T n ω)

theorem measurable_dyadicMax {M : ℝ → Ω → ℝ} (hM : ∀ t, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable (dyadicMax M T n) :=
  Finset.measurable_range_sup'' (fun _ _ => hM _)

theorem measurable_supOn {M : ℝ → Ω → ℝ} (hM : ∀ t, Measurable (M t)) (T : ℝ) :
    Measurable (supOn M T) :=
  Measurable.iSup fun n => (measurable_dyadicMax hM T n).ennreal_ofReal

omit m in
theorem dyadicMax_nonneg {M : ℝ → Ω → ℝ} (h0 : ∀ t ω, 0 ≤ M t ω) (T : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicMax M T n ω :=
  (h0 _ ω).trans (Finset.le_sup' (f := fun k => M (dyadicTime T n k) ω)
    (Finset.mem_range.mpr (Nat.succ_pos _)))

omit m in
/-- Dyadic grids are nested, so the grid maxima increase. -/
theorem dyadicMax_mono {M : ℝ → Ω → ℝ} {T : ℝ} (ω : Ω) :
    Monotone fun n => dyadicMax M T n ω := by
  intro i j hij
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ 2 ^ i := Nat.lt_succ_iff.mp (by simpa using hk)
  have hle : k * 2 ^ (j - i) < 2 ^ j + 1 := by
    have h2 : k * 2 ^ (j - i) ≤ 2 ^ j := by
      calc k * 2 ^ (j - i) ≤ 2 ^ i * 2 ^ (j - i) := Nat.mul_le_mul_right _ hk'
        _ = 2 ^ j := by rw [← pow_add, Nat.add_sub_of_le hij]
    exact Nat.lt_succ_of_le h2
  have htime : dyadicTime T i k = dyadicTime T j (k * 2 ^ (j - i)) := by
    simp only [dyadicTime]
    push_cast
    rw [show j = i + (j - i) from (Nat.add_sub_of_le hij).symm, pow_add]
    field_simp
    ring
  calc M (dyadicTime T i k) ω = M (dyadicTime T j (k * 2 ^ (j - i))) ω := by rw [htime]
    _ ≤ dyadicMax M T j ω := Finset.le_sup' (f := fun k => M (dyadicTime T j k) ω)
        (Finset.mem_range.mpr hle)

/-- Supremum of `x ↦ x ^ p` over an arbitrary index set, for `p > 0`. -/
theorem iSup_rpow_eq {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hp.le)
  have hle : (⨆ i, f i) ≤ (⨆ i, f i ^ p) ^ (1 / p) := by
    apply iSup_le
    intro i
    rw [← ENNReal.rpow_le_rpow_iff hp]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    exact le_iSup (fun i => f i ^ p) i
  calc (⨆ i, f i) ^ p ≤ ((⨆ i, f i ^ p) ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow hle hp.le
    _ = ⨆ i, f i ^ p := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

omit [IsFiniteMeasure μ] in
/-- Raising an `eLpNorm` bound to the `p`-th power, for nonnegative functions. -/
theorem lintegral_rpow_le_of_eLpNorm_le {f g : Ω → ℝ} (_hf : Measurable f) (_hg : Measurable g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ ≤
      ENNReal.ofReal (C ^ p) * ∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂μ := by
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf' : eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hpne hptop, ENNReal.toReal_ofReal hp.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_of_nonneg (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hp.le]
  have hg' : eLpNorm g (ENNReal.ofReal p) μ = (∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hpne hptop, ENNReal.toReal_ofReal hp.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_of_nonneg (hg0 ω), ENNReal.ofReal_rpow_of_nonneg (hg0 ω) hp.le]
  rw [hf', hg'] at h
  have h2 := ENNReal.rpow_le_rpow h hp.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg hC hp.le] at h2
  have e1 : ((∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) ^ (1 / p)) ^ p =
      ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  have e2 : ((∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂μ) ^ (1 / p)) ^ p =
      ∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂μ := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  rw [e1, e2] at h2
  exact h2


variable {ℱ : Filtration ℝ m}

/-- **The continuous-time Doob step.** For a nonnegative martingale `M` with a
right-continuous filtration, the maximal function over the dyadic grids is
controlled by `p/(p-1)` times the `Lᵖ` norm of the terminal value `M T`. -/
theorem eLpNorm_supOn_le {M : ℝ → Ω → ℝ}
    (hM : ∀ t, Measurable (M t)) (hmart : Martingale M ℱ μ)
    (h0 : ∀ t ω, 0 ≤ M t ω) {T : ℝ} (hT : 0 ≤ T) {p : ℝ} (hp : 1 < p) :
    eLpNorm (supOn M T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (M T) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  -- Each dyadic grid is a finite-time martingale, so the discrete bound applies.
  have hgrid : ∀ n : ℕ, eLpNorm (dyadicMax M T n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (M T) (ENNReal.ofReal p) μ := by
    intro n
    set tt : ℕ → ℝ := fun k => min (dyadicTime T n k) T with htt
    have hmono : Monotone tt := by
      intro i j hij
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      simp only [tt, dyadicTime]
      exact min_le_min (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hij' hT)
        (by positivity)) le_rfl
    set 𝒢 : Filtration ℕ m :=
      ⟨fun k => ℱ (tt k), fun i j hij => ℱ.mono (hmono hij), fun k => ℱ.le (tt k)⟩ with h𝒢
    set X : ℕ → Ω → ℝ := fun k => M (tt k) with hX
    have hXm : Martingale X 𝒢 μ := by
      refine ⟨fun k => ?_, ?_⟩
      · exact hmart.1 (tt k)
      · intro i j hij
        exact hmart.2 (tt i) (tt j) (hmono hij)
    have hstep := submartingale_eLpNorm_maximal_le (μ := μ) (𝒢 := 𝒢) (f := X)
      hXm.submartingale (fun k ω => h0 _ ω) hp (2 ^ n)
    have hmin : ∀ k ≤ 2 ^ n, tt k = dyadicTime T n k := by
      intro k hk
      simp only [tt]
      apply min_eq_left
      have hpos : (0:ℝ) < (2:ℝ) ^ n := by positivity
      have hk' : (k : ℝ) ≤ (2:ℝ) ^ n := by
        have hk'' : ((k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hk
        simpa using hk''
      rw [dyadicTime]
      refine (div_le_iff₀ hpos).2 ?_
      calc (k : ℝ) * T ≤ (2:ℝ) ^ n * T := mul_le_mul_of_nonneg_right hk' hT
        _ = T * (2:ℝ) ^ n := by ring
    have hsub : subMax X (2 ^ n) = dyadicMax M T n := by
      funext ω
      apply le_antisymm
      · apply Finset.sup'_le
        intro k hk
        have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (by simpa using hk)
        show M (tt k) ω ≤ dyadicMax M T n ω
        rw [hmin k hk']
        exact Finset.le_sup' (f := fun k => M (dyadicTime T n k) ω) hk
      · apply Finset.sup'_le
        intro k hk
        have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (by simpa using hk)
        show M (dyadicTime T n k) ω ≤ subMax X (2 ^ n) ω
        rw [← hmin k hk']
        exact Finset.le_sup' (f := fun k => X k ω) hk
    have hter : X (2 ^ n) = M T := by
      funext ω
      show M (tt (2 ^ n)) ω = M T ω
      have h2 : tt (2 ^ n) = T := by
        refine min_eq_right ?_
        have hpos : (0:ℝ) < (2:ℝ) ^ n := by positivity
        have hcast : ((2 ^ n : ℕ) : ℝ) = (2:ℝ) ^ n := by push_cast; ring
        rw [dyadicTime, hcast]
        refine (le_div_iff₀ hpos).2 ?_
        rw [mul_comm ((2:ℝ) ^ n) T]
      rw [h2]
    rw [hsub, hter] at hstep
    exact hstep
  -- Pass to the supremum over all scales.
  have hmoment : ∫⁻ ω, (supOn M T ω) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal ((M T ω) ^ p) ∂μ := by
    have hF : ∀ n, Measurable fun ω => (ENNReal.ofReal (dyadicMax M T n ω)) ^ p := fun n =>
      ((measurable_dyadicMax hM T n).ennreal_ofReal).pow_const p
    have hmonoF : Monotone fun n (ω : Ω) => (ENNReal.ofReal (dyadicMax M T n ω)) ^ p := by
      intro i j hij ω
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (dyadicMax_mono ω hij)) hp0.le
    have hsup : ∀ ω, supOn M T ω = ⨆ n, ENNReal.ofReal (dyadicMax M T n ω) := fun ω => rfl
    calc ∫⁻ ω, (supOn M T ω) ^ p ∂μ
        = ∫⁻ ω, ⨆ n, (ENNReal.ofReal (dyadicMax M T n ω)) ^ p ∂μ := by
          apply lintegral_congr
          intro ω
          rw [hsup ω, iSup_rpow_eq _ hp0]
      _ = ⨆ n, ∫⁻ ω, (ENNReal.ofReal (dyadicMax M T n ω)) ^ p ∂μ :=
          lintegral_iSup hF hmonoF
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) *
            ∫⁻ ω, ENNReal.ofReal ((M T ω) ^ p) ∂μ := by
          apply iSup_le
          intro n
          have hg := lintegral_rpow_le_of_eLpNorm_le (μ := μ)
            (measurable_dyadicMax hM T n) (hM T)
            (dyadicMax_nonneg h0 T n) (h0 T) hp0 (le_of_lt hp'0) (hgrid n)
          refine (le_of_eq ?_).trans hg
          apply lintegral_congr
          intro ω
          exact ENNReal.ofReal_rpow_of_nonneg (dyadicMax_nonneg h0 T n ω) hp0.le
  -- Rewrite both sides as `eLpNorm`s.
  have hY : eLpNorm (supOn M T) (ENNReal.ofReal p) μ =
      (∫⁻ ω, (supOn M T ω) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    simp
  have hMT : eLpNorm (M T) (ENNReal.ofReal p) μ =
      (∫⁻ ω, ENNReal.ofReal ((M T ω) ^ p) ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_of_nonneg (h0 T ω), ENNReal.ofReal_rpow_of_nonneg (h0 T ω) hp0.le]
  rw [hY, hMT]
  calc (∫⁻ ω, (supOn M T ω) ^ p ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal ((p / (p - 1)) ^ p) *
          ∫⁻ ω, ENNReal.ofReal ((M T ω) ^ p) ∂μ) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmoment (by positivity)
    _ = ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((M T ω) ^ p) ∂μ) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / p),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity : (0:ℝ) ≤ 1 / p)]
        have hratio : (((p / (p - 1)) ^ p) ^ (1 / p)) = p / (p - 1) := by
          rw [← Real.rpow_mul (le_of_lt hp'0), mul_one_div_cancel hp0.ne', Real.rpow_one]
        rw [hratio]

/-- The last dyadic grid point is the endpoint. -/
theorem dyadicTime_pow (T : ℝ) (n : ℕ) : dyadicTime T n (2 ^ n) = T := by
  have hpos : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have hcast : ((2 ^ n : ℕ) : ℝ) = (2:ℝ) ^ n := by push_cast; ring
  rw [dyadicTime, hcast]
  field_simp

omit m in
/-- Every value on the interval is bounded by the dyadic supremum, for a
right-continuous path: the dyadic grids become dense from the right. -/
theorem ofReal_le_supOn {M : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcont : ∀ ω, ∀ t ∈ Ico 0 T, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (ω : Ω) :
    ENNReal.ofReal (M t ω) ≤ supOn M T ω := by
  have hterm : ∀ n k, k ≤ 2 ^ n → ENNReal.ofReal (M (dyadicTime T n k) ω) ≤ supOn M T ω := by
    intro n k hk
    refine le_trans ?_ (le_iSup (fun n => ENNReal.ofReal (dyadicMax M T n ω)) n)
    exact ENNReal.ofReal_le_ofReal (Finset.le_sup' (f := fun k => M (dyadicTime T n k) ω)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  rcases lt_or_eq_of_le ht.2 with htT | htT
  · -- dyadic points decrease to `t` from the right
    set k : ℕ → ℕ := fun n => ⌈t * 2 ^ n / T⌉₊ with hk
    have hTpos : 0 < T := lt_of_le_of_lt ht.1 htT
    have hkmem : ∀ n, k n ≤ 2 ^ n := by
      intro n
      rw [hk, Nat.ceil_le, div_le_iff₀ hTpos]
      have h2 : (0:ℝ) < (2:ℝ) ^ n := by positivity
      have hcast : ((2 ^ n : ℕ) : ℝ) = (2:ℝ) ^ n := by push_cast; ring
      rw [hcast]
      calc t * (2:ℝ) ^ n ≤ T * (2:ℝ) ^ n := mul_le_mul_of_nonneg_right ht.2 h2.le
        _ = (2:ℝ) ^ n * T := by ring
    have hge : ∀ n, t ≤ dyadicTime T n (k n) := by
      intro n
      have h2 : (0:ℝ) < (2:ℝ) ^ n := by positivity
      have hc : t * (2:ℝ) ^ n / T ≤ ((k n : ℕ) : ℝ) := Nat.le_ceil _
      have hmul : t * (2:ℝ) ^ n ≤ ((k n : ℕ) : ℝ) * T := by
        have := mul_le_mul_of_nonneg_right hc hTpos.le
        rwa [div_mul_cancel₀ _ hTpos.ne'] at this
      rw [dyadicTime]
      rw [le_div_iff₀ h2]
      exact hmul
    have hlt : ∀ n, dyadicTime T n (k n) < t + T / 2 ^ n := by
      intro n
      have h2 : (0:ℝ) < (2:ℝ) ^ n := by positivity
      have hx0 : (0:ℝ) ≤ t * (2:ℝ) ^ n / T :=
        div_nonneg (mul_nonneg ht.1 h2.le) hTpos.le
      have hc : ((k n : ℕ) : ℝ) < t * (2:ℝ) ^ n / T + 1 := Nat.ceil_lt_add_one hx0
      have hmul : ((k n : ℕ) : ℝ) * T < t * (2:ℝ) ^ n + T := by
        have := mul_lt_mul_of_pos_right hc hTpos
        rwa [add_mul, one_mul, div_mul_cancel₀ _ hTpos.ne'] at this
      rw [dyadicTime, div_lt_iff₀ h2]
      calc ((k n : ℕ) : ℝ) * T < t * (2:ℝ) ^ n + T := hmul
        _ = (t + T / 2 ^ n) * (2:ℝ) ^ n := by
            rw [add_mul, div_mul_cancel₀ _ h2.ne', add_comm]
    have hlim : Tendsto (fun n => dyadicTime T n (k n)) atTop (𝓝 t) := by
      rw [tendsto_order]
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · filter_upwards with n
        linarith [hge n]
      · have hinv : Tendsto (fun n : ℕ => (2:ℝ) ^ n) atTop atTop :=
          tendsto_pow_atTop_atTop_of_one_lt one_lt_two
        have hz : Tendsto (fun n : ℕ => T / (2:ℝ) ^ n) atTop (𝓝 0) := by
          have := hinv.const_div_atTop T
          simpa [div_eq_mul_inv, mul_comm] using this
        have hb' : ∀ᶠ n : ℕ in atTop, T / (2:ℝ) ^ n < b - t :=
          hz (Iio_mem_nhds (by linarith))
        filter_upwards [hb'] with n hn
        have := hlt n
        have : T / 2 ^ n = T / (2:ℝ) ^ n := rfl
        linarith [this ▸ hn, hlt n]
    have hseq : Tendsto (fun n => dyadicTime T n (k n)) atTop (𝓝[Ici t] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n => hge n⟩
    have hM : Tendsto (fun n => M (dyadicTime T n (k n)) ω) atTop (𝓝 (M t ω)) :=
      ((hcont ω t ⟨ht.1, htT⟩).tendsto).comp hseq
    have hE : Tendsto (fun n => ENNReal.ofReal (M (dyadicTime T n (k n)) ω)) atTop
        (𝓝 (ENNReal.ofReal (M t ω))) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hM
    exact le_of_tendsto' hE fun n => hterm n (k n) (hkmem n)
  · -- the endpoint
    subst htT
    have h0 : dyadicTime t 0 (2 ^ 0) = t := dyadicTime_pow t 0
    have h := hterm 0 (2 ^ 0) (le_refl _)
    rwa [h0] at h

/-- The continuous-time Doob step with a named terminal value `Ψ`. -/
theorem eLpNorm_supOn_le_of_terminal {M : ℝ → Ω → ℝ} {Ψ : Ω → ℝ}
    (hM : ∀ t, Measurable (M t)) (hmart : Martingale M ℱ μ)
    (h0 : ∀ t ω, 0 ≤ M t ω) {T : ℝ} (hT : 0 ≤ T) (hΨ : M T =ᵐ[μ] Ψ)
    {p : ℝ} (hp : 1 < p) :
    eLpNorm (supOn M T) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm Ψ (ENNReal.ofReal p) μ := by
  rw [← eLpNorm_congr_ae hΨ]
  exact eLpNorm_supOn_le hM hmart h0 hT hp

end WeightedBMO
