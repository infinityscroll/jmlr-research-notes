import GaussianEhrhardMomentBridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open OAI.GaussianPropeller.Quantile

namespace NegativeVotingEhrhard

/-- The coefficient in the exact conditional covariance–mean inequality. -/
def ehrhardCoefficient (p : ℝ) : ℝ := 1 + p * q p / φ (q p)

theorem integrable_mul_phi : Integrable (fun x : ℝ => x * φ x) := by
  have h := integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
  have heq : (fun x : ℝ => x * φ x) =
      (fun x : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * (x * Real.exp (-(1/2:ℝ)*x^2))) := by
    funext x
    unfold φ
    rw [show -x^2/2 = -(1/2:ℝ)*x^2 by ring]
    ring
  rw [heq]
  exact h.const_mul _

theorem phi_tendsto_atBot : Tendsto φ atBot (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (f' := fun x : ℝ => -(x * φ x))
  · intro x _
    convert hasDerivAt_φ x using 1
    ring
  · exact integrable_mul_phi.neg.integrableOn
  · exact integrable_φ.integrableOn

theorem phi_truncated_first_moment (a : ℝ) :
    (∫ x in Iic a, x * φ x) = -φ a := by
  have hd (x : ℝ) (_hx : x ∈ Iic a) :
      HasDerivAt (fun y => -φ y) (x * φ x) x := by
    simpa only [Pi.neg_def, neg_mul, neg_neg] using (hasDerivAt_φ x).neg
  have hl : Tendsto (fun x => -φ x) atBot (𝓝 0) := by
    simpa only [neg_zero] using phi_tendsto_atBot.neg
  simpa using integral_Iic_of_hasDerivAt_of_tendsto' hd integrable_mul_phi.integrableOn hl

theorem integrable_gaussian_tail_gap (a : ℝ) :
    Integrable (fun x : ℝ => (-a - x) * φ x) := by
  have heq : (fun x : ℝ => (-a - x) * φ x) = (fun x => -a * φ x - x * φ x) := by
    funext x
    ring
  rw [heq]
  exact (integrable_φ.const_mul (-a)).sub integrable_mul_phi

/-- Exact positive-gap integral behind the covariance correction. -/
theorem gaussian_tail_gap_identity (a : ℝ) :
    (∫ x in Iic (-a), (-a-x)*φ x) = φ a - a*Φ (-a) := by
  have heq : (fun x : ℝ => (-a - x) * φ x) = (fun x => -a * φ x - x * φ x) := by
    funext x
    ring
  rw [heq, integral_sub (integrable_φ.const_mul (-a)).integrableOn
    integrable_mul_phi.integrableOn, integral_const_mul, phi_truncated_first_moment, φ_neg]
  change -a * Φ (-a) - -φ a = _
  ring

/-- On a short interval at distance at most 2/(1+a) from a, the Gaussian
 density loses at most the fixed factor exp(-4). -/
theorem phi_short_interval_lower (a δ x : ℝ) (ha : 0 ≤ a)
    (hδ : δ = 1/(1+a)) (hx : x ∈ Icc (-a-2*δ) (-a-δ)) :
    Real.exp (-4) * φ a ≤ φ x := by
  have hd0 : 0 < δ := by rw [hδ]; positivity
  have hd1 : δ ≤ 1 := by rw [hδ]; exact (div_le_one (by linarith)).mpr (by linarith)
  have had : a * δ ≤ 1 := by rw [hδ, mul_one_div]; exact (div_le_one (by linarith)).mpr (by linarith)
  have hsquare : x^2 ≤ a^2 + 8 := by
    have hx0 : x ≤ 0 := by linarith [hx.2]
    have habs : -x ≤ a + 2*δ := by linarith [hx.1]
    have hsq := sq_le_sq₀ (neg_nonneg.mpr hx0) (by positivity : 0 ≤ a+2*δ) |>.mpr habs
    have hd2 : δ^2 ≤ 1 := by nlinarith [mul_self_le_mul_self hd0.le hd1]
    nlinarith
  have hexp : -4 + -a^2/2 ≤ -x^2/2 := by nlinarith
  have he := Real.exp_le_exp.mpr hexp
  unfold φ
  rw [← mul_assoc, mul_comm (Real.exp (-4)), mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left he (by positivity)

/-- Quantitative inverse-Mills gap from a literal Gaussian interval, without
assuming or importing a refined Mills-ratio estimate. -/
theorem gaussian_tail_gap_lower (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-4) / (1+a)^2 * φ a ≤ φ a - a*Φ (-a) := by
  let δ : ℝ := 1/(1+a)
  let S : Set ℝ := Icc (-a-2*δ) (-a-δ)
  let f : ℝ → ℝ := fun x => (-a-x)*φ x
  have hd0 : 0 < δ := by dsimp [δ]; positivity
  have hs : MeasurableSet S := measurableSet_Icc
  have hab : -a-2*δ ≤ -a-δ := by linarith
  have hb (x : ℝ) (hx : x ∈ S) : δ * (Real.exp (-4) * φ a) ≤ f x := by
    have hxgap : δ ≤ -a-x := by dsimp [S] at hx; linarith [hx.2]
    have hphi := phi_short_interval_lower a δ x ha rfl hx
    exact mul_le_mul hxgap hphi (mul_nonneg (Real.exp_pos _).le (φ_pos _).le) (by linarith)
  have hcompare : (∫ x in S, δ * (Real.exp (-4) * φ a)) ≤ ∫ x in S, f x :=
    setIntegral_mono_on (integrableOn_const (by simp [S]))
      (integrable_gaussian_tail_gap a).integrableOn hs hb
  have hconst : (∫ x in S, δ * (Real.exp (-4) * φ a)) = δ^2 * Real.exp (-4) * φ a := by
    rw [setIntegral_const]
    simp only [S, Real.volume_Icc, measureReal_def, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]
    ring
  have hsubset : S ⊆ Iic (-a) := by
    intro x hx
    dsimp [S] at hx
    change x ≤ -a
    linarith [hx.2]
  have hnonneg : ∀ᵐ x ∂volume.restrict (Iic (-a)), 0 ≤ f x := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact mul_nonneg (by exact sub_nonneg.mpr hx) (φ_pos x).le
  have hlarge := setIntegral_mono_set (integrable_gaussian_tail_gap a).integrableOn hnonneg
    (ae_of_all _ (fun _ hx => hsubset hx))
  rw [hconst] at hcompare
  have hh := hcompare.trans hlarge
  change δ^2 * Real.exp (-4) * φ a ≤ ∫ x in Iic (-a), (-a-x)*φ x at hh
  rw [gaussian_tail_gap_identity] at hh
  convert hh using 1
  dsimp [δ]
  field_simp

/-- A uniform, explicit lower bound on the Ehrhard coefficient at negative
quantile -a. -/
theorem ehrhardCoefficient_cdf_neg_lower (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-4) / (2*(1+a^2)) ≤ ehrhardCoefficient (Φ (-a)) := by
  have hgap := gaussian_tail_gap_lower a ha
  have hden : (1+a)^2 ≤ 2*(1+a^2) := by nlinarith [sq_nonneg (a-1)]
  have hrecip : 1/(2*(1+a^2)) ≤ 1/(1+a)^2 :=
    one_div_le_one_div_of_le (by positivity) hden
  have hsmall := mul_le_mul_of_nonneg_left hrecip (Real.exp_pos (-4)).le
  have hφ := φ_pos a
  have hdiv : Real.exp (-4)/(1+a)^2 ≤ (φ a-a*Φ (-a))/φ a :=
    (le_div_iff₀ hφ).mpr hgap
  calc
    _ ≤ Real.exp (-4)/(1+a)^2 := by simpa only [mul_one_div] using hsmall
    _ ≤ (φ a-a*Φ (-a))/φ a := hdiv
    _ = ehrhardCoefficient (Φ (-a)) := by
      rw [ehrhardCoefficient, q_Φ, φ_neg]
      field_simp
      ring

/-- The inverse-CDF normalization is exactly the standard Gaussian CDF. -/
theorem cdf_eq_gaussianReal_mass (t : ℝ) : Φ t = ((gaussianReal 0 1) (Iic t)).toReal := by
  have hpdf : φ = gaussianPDFReal 0 1 := by
    funext x
    norm_num [φ, gaussianPDFReal]
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (Iic t), ← hpdf]
  exact (ENNReal.toReal_ofReal (Φ_pos t).le).symm

/-- An actual Gaussian Chernoff bound, used only to convert the quantile square
into a logarithm of the cell mass. -/
theorem gaussian_cdf_neg_le_exp (a : ℝ) (ha : 0 ≤ a) : Φ (-a) ≤ Real.exp (-a^2/2) := by
  have hh := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id)
    (t := -a) (-a) (neg_nonpos.mpr ha) (integrable_exp_mul_gaussianReal (-a))
  rw [cdf_eq_gaussianReal_mass]
  have heq : -(-a) * (-a) + (0 : ℝ) * (-a) + (1 : ℝ) * (-a)^2/2 = -a^2/2 := by ring
  have hs : {x : ℝ | x ≤ -a} = Iic (-a) := by ext x; rfl
  simpa only [measureReal_def, id_eq, mgf_id_gaussianReal, NNReal.coe_one,
    ← Real.exp_add, ← add_assoc, heq, hs] using hh

/-- The exact coefficient is strictly positive for every nontrivial mass, with
an explicit bound in terms of its Gaussian quantile. -/
theorem ehrhardCoefficient_quantile_lower {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.exp (-4) / (2*(1+(q p)^2)) ≤ ehrhardCoefficient p := by
  by_cases hq : q p ≤ 0
  · have hh := ehrhardCoefficient_cdf_neg_lower (-q p) (neg_nonneg.mpr hq)
    simpa only [neg_neg, Φ_q hp, neg_sq] using hh
  · have hq0 : 0 ≤ q p := (lt_of_not_ge hq).le
    have hc : 1 ≤ ehrhardCoefficient p := by
      unfold ehrhardCoefficient
      exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hp.1.le hq0) (φ_pos _).le)
    apply le_trans ?_ hc
    have he : Real.exp (-4 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg (q p)]

/-- The logarithmic lower bound needed for nearly balanced Gaussian cells. -/
theorem ehrhardCoefficient_log_mass_lower {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.exp (-4) / (2*(1+2*Real.log (1/p))) ≤ ehrhardCoefficient p := by
  have hlog : 0 ≤ Real.log (1/p) := Real.log_nonneg ((one_le_div hp.1).mpr hp.2.le)
  by_cases hq : q p ≤ 0
  · have htail := gaussian_cdf_neg_le_exp (-q p) (neg_nonneg.mpr hq)
    rw [neg_neg, Φ_q hp] at htail
    have hl := Real.log_le_log hp.1 htail
    rw [Real.log_exp] at hl
    have hloginv : Real.log (1/p) = -Real.log p := by rw [one_div, Real.log_inv]
    have hsq : (q p)^2 ≤ 2 * Real.log (1/p) := by
      rw [hloginv]
      nlinarith
    apply le_trans ?_ (ehrhardCoefficient_quantile_lower hp)
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (by nlinarith)
  · have hc : 1 ≤ ehrhardCoefficient p := by
      unfold ehrhardCoefficient
      exact le_add_of_nonneg_right (div_nonneg
        (mul_nonneg hp.1.le (lt_of_not_ge hq).le) (φ_pos _).le)
    apply le_trans ?_ hc
    have he : Real.exp (-4 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    apply (div_le_one (by positivity)).mpr
    linarith

theorem ehrhardCoefficient_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < ehrhardCoefficient p :=
  lt_of_lt_of_le (by positivity) (ehrhardCoefficient_quantile_lower hp)

/-- If a cell has mass at least 1/M, the coefficient has a uniform explicit
lower bound involving only M. -/
theorem ehrhardCoefficient_lower_of_mass_lower {p M : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hM : 1 ≤ M) (hmass : 1/M ≤ p) :
    Real.exp (-4) / (2*(1+2*Real.log M)) ≤ ehrhardCoefficient p := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hinv : 1/p ≤ M := (div_le_iff₀ hp.1).mpr (by
    simpa only [mul_comm] using (div_le_iff₀ hMp).mp hmass)
  have hlog := Real.log_le_log (div_pos zero_lt_one hp.1) hinv
  have hpLog : 0 ≤ Real.log (1/p) := Real.log_nonneg ((one_le_div hp.1).mpr hp.2.le)
  apply le_trans ?_ (ehrhardCoefficient_log_mass_lower hp)
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (by nlinarith)

/-- The literal conditional variance receives the explicit logarithmic
rank-one mean correction. All Gaussian analytic hypotheses are discharged. -/
theorem gaussian_polyhedron_quantitative_variance_le {ι J : Type*} [Fintype ι] [Fintype J]
    (w : J → EuclideanSpace ℝ ι) (b : J → ℝ)
    (hp : polyhedronMass w b ∈ Ioo (0 : ℝ) 1) (v : EuclideanSpace ℝ ι) :
    polyhedronConditionalVariance w b v ≤ ‖v‖^2 -
      (Real.exp (-4) / (2*(1+2*Real.log (1/polyhedronMass w b)))) *
        (polyhedronMoment w b v 1 / polyhedronMass w b)^2 := by
  apply (gaussian_polyhedron_ehrhard_conditional_variance_le w b hp v).trans
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_right (ehrhardCoefficient_log_mass_lower hp) (sq_nonneg _)

end NegativeVotingEhrhard
