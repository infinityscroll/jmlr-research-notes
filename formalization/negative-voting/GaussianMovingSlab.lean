import GaussianFanMassJacobian

/-!
Differentiation of an actual integral over a moving slab.  The locally frozen
integrand condition is the precise condition later discharged by strict
inequalities on a Gaussian facet; it is not a derivative or Hessian assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology Interval

namespace NegativeVotingMovingSlab

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]

/-- A parameter-dependent oriented interval integral is genuinely measurable. -/
theorem measurable_moving_interval (g : Y → ℝ → ℝ) (a b : Y → ℝ)
    (hg : Measurable (Function.uncurry g)) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun y => ∫ s in a y..b y, g y s) := by
  have hAB : MeasurableSet {p : Y × ℝ | a p.1 < p.2 ∧ p.2 ≤ b p.1} :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  have hBA : MeasurableSet {p : Y × ℝ | b p.1 < p.2 ∧ p.2 ≤ a p.1} :=
    (measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (ha.comp measurable_fst))
  have h₁ := (hg.indicator hAB).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))
  have h₂ := (hg.indicator hBA).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))
  have he (y : Y) : (∫ s in a y..b y, g y s) =
      (∫ s, {p : Y × ℝ | a p.1 < p.2 ∧ p.2 ≤ b p.1}.indicator
        (Function.uncurry g) (y,s)) -
      (∫ s, {p : Y × ℝ | b p.1 < p.2 ∧ p.2 ≤ a p.1}.indicator
        (Function.uncurry g) (y,s)) := by
    rw [intervalIntegral]
    congr 1 <;> rw [← integral_indicator measurableSet_Ioc] <;>
      apply integral_congr_ae <;> filter_upwards with s <;>
      simp [Set.indicator_apply, Set.mem_Ioc]
  simp_rw [he]
  exact (h₁.sub h₂).measurable

/-- Local constancy of the rest of the constraints permits freezing them on
the whole shrinking normal interval, before differentiation. -/
theorem moving_slab_eventually_frozen
    (g : P → ℝ → ℝ) (z : P → ℝ) (p₀ : P) (a : ℝ)
    (hz : ContinuousAt z p₀) (hz₀ : z p₀ = a)
    (hfreeze : ∃ ε > 0, ∀ p, ‖p-p₀‖ < ε → ∀ s, |s-a| < ε → g p s = g p₀ s) :
    (fun p => ∫ s in a..z p, g p s) =ᶠ[𝓝 p₀]
      (fun p => ∫ s in a..z p, g p₀ s) := by
  obtain ⟨ε,hε,hf⟩ := hfreeze
  have hp : ∀ᶠ p in 𝓝 p₀, ‖p-p₀‖ < ε := by
    change {p : P | ‖p-p₀‖ < ε} ∈ 𝓝 p₀
    simpa only [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds p₀ hε
  have hzp : ∀ᶠ p in 𝓝 p₀, |z p-a| < ε := by
    simpa only [hz₀, Metric.mem_ball, Real.dist_eq] using
      hz.tendsto.eventually (Metric.ball_mem_nhds (z p₀) hε)
  filter_upwards [hp,hzp] with p hpp hzp
  apply intervalIntegral.integral_congr
  intro s hs
  apply hf p hpp s
  have hs' : s ∈ Icc (min a (z p)) (max a (z p)) := hs
  have hlow : a-ε < s := lt_of_lt_of_le
    (lt_min (by linarith) (by have := (abs_lt.mp hzp).1; linarith)) hs'.1
  have hupp : s < a+ε := lt_of_le_of_lt hs'.2
    (max_lt (by linarith) (by have := (abs_lt.mp hzp).2; linarith))
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- An explicit moving-slab differentiation theorem.  Its conclusion is the
actual Fréchet derivative of the double Bochner integral. -/
theorem hasFDerivAt_integral_moving_slab
    (g : P → Y → ℝ → ℝ) (z : P → Y → ℝ) (a : Y → ℝ)
    (z' : Y → P →L[ℝ] ℝ) (p₀ : P) (U : Set P) (hU : U ∈ 𝓝 p₀)
    (K L : Y → ℝ)
    (hg : ∀ p, Measurable (Function.uncurry (g p)))
    (hz : ∀ p, Measurable (z p)) (ha : Measurable a)
    (hbase : ∀ y, z p₀ y = a y)
    (hderiv : ∀ᵐ y ∂μ, HasFDerivAt (fun p => z p y) (z' y) p₀)
    (hcont : ∀ᵐ y ∂μ, ContinuousAt (g p₀ y) (a y))
    (hfreeze : ∀ᵐ y ∂μ, ∃ ε > 0, ∀ p, ‖p-p₀‖ < ε → ∀ s,
      |s-a y| < ε → g p y s = g p₀ y s)
    (hK : ∀ y, 0 ≤ K y)
    (hbound : ∀ p ∈ U, ∀ y s, |g p y s| ≤ K y)
    (hshift : ∀ p ∈ U, ∀ y, |z p y-a y| ≤ L y * ‖p-p₀‖)
    (hint : Integrable (fun y => K y * L y) μ)
    (hmeas' : AEStronglyMeasurable (fun y => g p₀ y (a y) • z' y) μ) :
    HasFDerivAt (fun p => ∫ y, (∫ s in a y..z p y, g p y s) ∂μ)
      (∫ y, g p₀ y (a y) • z' y ∂μ) p₀ := by
  let F : P → Y → ℝ := fun p y => ∫ s in a y..z p y, g p y s
  have h₀ : Integrable (F p₀) μ := by
    simp only [F,hbase,intervalIntegral.integral_same]
    exact integrable_zero Y ℝ μ
  have hd : ∀ᵐ y ∂μ, HasFDerivAt (fun p => F p y) (g p₀ y (a y) • z' y) p₀ := by
    filter_upwards [hderiv,hcont,hfreeze] with y hy hc hf
    have hm : StronglyMeasurable (g p₀ y) :=
      ((hg p₀).comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
    have hdg : HasDerivAt (fun u => ∫ s in a y..u, g p₀ y s) (g p₀ y (a y)) (a y) :=
      intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
        hm.stronglyMeasurableAtFilter hc
    have hdz : HasFDerivAt (fun p => ∫ s in a y..z p y, g p₀ y s)
        (g p₀ y (a y) • z' y) p₀ := by
      have hdg' : HasDerivAt (fun u => ∫ s in a y..u, g p₀ y s)
          (g p₀ y (a y)) (z p₀ y) := by rw [hbase]; exact hdg
      simpa only [Function.comp_def] using hdg'.comp_hasFDerivAt p₀ hy
    exact hdz.congr_of_eventuallyEq
      (moving_slab_eventually_frozen (fun p s => g p y s) (fun p => z p y) p₀
        (a y) hy.continuousAt (hbase y) hf)
  have hb : ∀ᵐ y ∂μ, ∀ p ∈ U, ‖F p y-F p₀ y‖ ≤ K y * L y * ‖p-p₀‖ := by
    filter_upwards with y
    intro p hp
    simp only [F,hbase,intervalIntegral.integral_same,sub_zero]
    calc
      _ ≤ K y * |z p y-a y| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hbound p hp y s
      _ ≤ K y * (L y * ‖p-p₀‖) := mul_le_mul_of_nonneg_left (hshift p hp y) (hK y)
      _ = _ := by ring
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip' hU
    (fun p _ => (measurable_moving_interval (g p) a (z p) (hg p) ha (hz p)).aestronglyMeasurable)
    h₀ hmeas' hb hint hd).2

end NegativeVotingMovingSlab
