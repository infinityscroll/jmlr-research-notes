import GaussianSmoothingComposition
import GaussianSwitchingLpCap

/-! Variable-exponent sharp Gaussian normal trace and exact cancellation of
its affine-offset growth against the Gaussian surface density. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin NegativeVotingHypercontractivity
open NegativeVotingNormalTrace
open scoped ENNReal NNReal
namespace NegativeVotingNormalTraceAllExponents

/-- Exact cancellation; no bound on the signed affine offset is required. -/
theorem surface_density_row_cancel (τ q a : ℝ) (hq : 1 < q)
    (ht : τ^2 = 1/(2*q-1)) :
    (gaussianPDFReal 0 1 a)^(1/q)*normalRowSquare τ a =
      (gaussianPDFReal 0 1 0)^(1/q)*
        (Real.sqrt (1-τ^2))⁻¹*(Real.sqrt (1+τ^2))⁻¹ := by
  have hq0 : q ≠ 0 := by linarith
  have hd : 2*q-1 ≠ 0 := by linarith
  have hu : 1+τ^2 ≠ 0 := ne_of_gt (by positivity)
  have he : τ^2/(1+τ^2) = 1/(2*q) := by rw [ht]; field_simp; ring
  have hg : gaussianPDFReal 0 1 a = gaussianPDFReal 0 1 0*Real.exp (-(a^2)/2) := by
    simp [gaussianPDFReal]
  rw [hg,Real.mul_rpow (gaussianPDFReal_nonneg _ _ _) (Real.exp_pos _).le,←Real.exp_mul]
  unfold normalRowSquare
  have ha : τ^2*a^2/(1+τ^2) = a^2/(2*q) := by
    calc
      _ = a^2*(τ^2/(1+τ^2)) := by ring
      _ = _ := by rw [he]; ring
  rw [ha]
  calc
    _ = (gaussianPDFReal 0 1 0)^(1/q)*(Real.sqrt (1-τ^2))⁻¹*
        (Real.sqrt (1+τ^2))⁻¹*(Real.exp (-(a^2)/2*(1/q))*Real.exp (a^2/(2*q))) := by ring
    _ = _ := by
      rw [←Real.exp_add]
      have hz : -(a^2)/2*(1/q)+a^2/(2*q)=0 := by ring
      rw [hz,Real.exp_zero,mul_one]

/-- A fixed bound for every offset at the exact hypercontractive time. -/
theorem surface_density_row_le_two (τ q a : ℝ) (hq : 2 ≤ q)
    (ht : τ^2 = 1/(2*q-1)) :
    (gaussianPDFReal 0 1 a)^(1/q)*normalRowSquare τ a ≤ 2 := by
  rw [surface_density_row_cancel τ q a (by linarith) ht]
  have hpdf : gaussianPDFReal 0 1 0 ≤ 1 := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,zero_pow (by decide : (2:ℕ)≠0),
      neg_zero,zero_div,Real.exp_zero,mul_one]
    have hs : 1 ≤ Real.sqrt (2*Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    simpa only [one_div_one,one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs
  have hpdfq : (gaussianPDFReal 0 1 0)^(1/q) ≤ 1 := by
    simpa using Real.rpow_le_rpow (gaussianPDFReal_nonneg _ _ _) hpdf (by positivity : 0≤1/q)
  have ht3 : τ^2 ≤ 1/3 := by
    rw [ht]
    apply (div_le_div_iff₀ (by linarith : 0<2*q-1) (by norm_num : (0:ℝ)<3)).mpr
    nlinarith
  have hsm : (1/2:ℝ) ≤ Real.sqrt (1-τ^2) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hsp : 1 ≤ Real.sqrt (1+τ^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg τ]
  have him : (Real.sqrt (1-τ^2))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0:ℝ)<1/2) hsm
  have hip : (Real.sqrt (1+τ^2))⁻¹ ≤ 1 := by
    simpa using inv_anti₀ (by norm_num : (0:ℝ)<1) hsp
  have hp := mul_le_mul hpdfq him (by positivity) (by norm_num : (0:ℝ)≤1)
  have hp2 := mul_le_mul hp hip (by positivity) (by norm_num : (0:ℝ)≤1*2)
  norm_num at hp2
  simpa only [one_div] using hp2

/-- Restriction Holder for the square, in the exact 2q exponent used by the trace. -/
theorem set_integral_sq_le_l2q {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) (q : ℝ) (hq : 1 ≤ q)
    (v : X → ℝ) (hv : MemLp v (ENNReal.ofReal (2*q)) μ) :
    (∫ x in E,(v x)^2 ∂μ) ≤
      (eLpNorm v (ENNReal.ofReal (2*q)) μ).toReal^2*(μ E).toReal^(1-1/q) := by
  have hq0 : 0 ≤ q := by linarith
  have hp : eLpNorm (fun x => ‖v x‖^(2:ℝ)) (ENNReal.ofReal q) μ =
      eLpNorm v (ENNReal.ofReal (2*q)) μ^(2:ℝ) := by
    rw [eLpNorm_norm_rpow v hv.aestronglyMeasurable (by norm_num)]
    rw [←ENNReal.ofReal_mul hq0]
    rw [mul_comm q (2:ℝ)]
  have hmem : MemLp (fun x => ‖v x‖^(2:ℝ)) (ENNReal.ofReal q) μ := by
    change eLpNorm _ _ _ < ∞
    rw [hp]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv.eLpNorm_ne_top
  have hh := NegativeVotingSwitchingLp.set_integral_abs_le_lq E q hq hmem
  rw [hp,←ENNReal.toReal_rpow] at hh
  simpa only [Real.norm_eq_abs,Real.rpow_two,abs_pow,abs_abs,sq_abs] using hh

/-- Actual factored normal Gaussian integral restricted to any measurable
part of its containing plane. The only remaining offset factor is explicit. -/
theorem normalTrace_subset_square_le {n : ℕ} (τ q a : ℝ) (hτ : 0 < τ)
    (hq : 2 ≤ q) (ht : τ^2 = 1/(2*q-1))
    (E : Set (Fin n → ℝ)) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    (∫ x in E,(normalTrace τ a f x)^2 ∂γFin n) ≤
      (γFin n E).toReal^(1-1/q)*normalRowSquare τ a*
        ∫ z,(f z)^2 ∂(γFin n).prod (gaussianReal 0 1) := by
  have hd : 0 < 2*q-1 := by linarith
  have hs : τ^2 < 1 := by rw [ht]; apply (div_lt_one hd).mpr; linarith
  have hτ1 : τ<1 := by nlinarith
  have he : 1+(τ^2)⁻¹=2*q := by rw [ht]; field_simp; ring
  have hn := NegativeVotingSmoothingComposition.normalTrace_lq_bound_sharp hτ hτ1 a f hf
  rw [he] at hn
  have hN := (normalSection_memLp_and_integral_sq_le hs a f hf).1
  have hv := memLp_gaussian_average_higher_integrability τ hτ hτ1 _ hN
  change MemLp (normalTrace τ a f) (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) at hv
  rw [he] at hv
  have hh := set_integral_sq_le_l2q (γFin n) E q (by linarith) _ hv
  have hfin : ENNReal.ofReal (Real.sqrt (normalRowSquare τ a))*
      eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hnr := ENNReal.toReal_mono hfin hn
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hnr
  have hsquare := pow_le_pow_left₀ (ENNReal.toReal_nonneg) hnr 2
  rw [mul_pow,Real.sq_sqrt (normalRowSquare_nonneg τ a)] at hsquare
  have hi := NegativeVotingSwitchingLp.integral_abs_rpow_eq_norm (2:ℝ) (by norm_num)
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
  norm_num only [ENNReal.ofReal_ofNat,Real.rpow_two,sq_abs] at hi
  rw [←hi] at hsquare
  have hscaled := mul_le_mul_of_nonneg_right hsquare
    (Real.rpow_nonneg (show 0 ≤ (γFin n E).toReal from ENNReal.toReal_nonneg) (1-1/q))
  exact hh.trans (by nlinarith only [hscaled])

/-- Exact Gaussian surface-weighted trace on an arbitrary part of an affine
plane. The constant is independent of the offset, the subset probability,
and the tangential dimension. -/
theorem normalTrace_surface_subset_le {n : ℕ} (τ q a : ℝ) (hτ : 0 < τ)
    (hq : 2 ≤ q) (ht : τ^2 = 1/(2*q-1))
    (E : Set (Fin n → ℝ)) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    gaussianPDFReal 0 1 a*(∫ x in E,(normalTrace τ a f x)^2 ∂γFin n) ≤
      2*(gaussianPDFReal 0 1 a*(γFin n E).toReal)^(1-1/q)*
        ∫ z,(f z)^2 ∂(γFin n).prod (gaussianReal 0 1) := by
  have hp := gaussianPDFReal_pos 0 1 a (by norm_num)
  have hh := mul_le_mul_of_nonneg_left (normalTrace_subset_square_le τ q a hτ hq ht E f hf) hp.le
  have hs : (gaussianPDFReal 0 1 a)^(1-1/q)*(gaussianPDFReal 0 1 a)^(1/q)=
      gaussianPDFReal 0 1 a := by
    rw [←Real.rpow_add hp]
    have he : (1-1/q)+(1/q)=(1:ℝ) := by ring
    rw [he,Real.rpow_one]
  have hc : gaussianPDFReal 0 1 a*(γFin n E).toReal^(1-1/q)*normalRowSquare τ a =
      (gaussianPDFReal 0 1 a*(γFin n E).toReal)^(1-1/q)*
        ((gaussianPDFReal 0 1 a)^(1/q)*normalRowSquare τ a) := by
    rw [Real.mul_rpow hp.le ENNReal.toReal_nonneg]
    calc
      _ = ((gaussianPDFReal 0 1 a)^(1-1/q)*(gaussianPDFReal 0 1 a)^(1/q))*
          (γFin n E).toReal^(1-1/q)*normalRowSquare τ a := by rw [hs]
      _ = _ := by ring
  have hb := mul_le_mul_of_nonneg_left (surface_density_row_le_two τ q a hq ht)
    (Real.rpow_nonneg (mul_nonneg hp.le (show 0 ≤ (γFin n E).toReal from ENNReal.toReal_nonneg)) (1-1/q))
  have hi : 0 ≤ ∫ z,(f z)^2 ∂(γFin n).prod (gaussianReal 0 1) :=
    integral_nonneg (fun z=>sq_nonneg _)
  have hbi := mul_le_mul_of_nonneg_right hb hi
  calc
    _ ≤ (gaussianPDFReal 0 1 a*(γFin n E).toReal^(1-1/q)*normalRowSquare τ a)*
        ∫ z,(f z)^2 ∂(γFin n).prod (gaussianReal 0 1) := by nlinarith only [hh]
    _ = _ := by rw [hc]
    _ ≤ _ := by nlinarith only [hbi]

/-- The same result for the literal product-Gaussian noise integral. -/
theorem actual_product_surface_subset_le {n : ℕ} (τ q a : ℝ) (hτ : 0 < τ)
    (hq : 2 ≤ q) (ht : τ^2 = 1/(2*q-1))
    (E : Set (Fin n → ℝ)) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    gaussianPDFReal 0 1 a*(∫ x in E,(∫ z : (Fin n → ℝ) × ℝ,
      f ((fun j=>τ*x j+Real.sqrt (1-τ^2)*z.1 j),
        τ*a+Real.sqrt (1-τ^2)*z.2) ∂(γFin n).prod (gaussianReal 0 1))^2 ∂γFin n) ≤
      2*(gaussianPDFReal 0 1 a*(γFin n E).toReal)^(1-1/q)*
        ∫ z,(f z)^2 ∂(γFin n).prod (gaussianReal 0 1) := by
  have hs : τ^2 < 1 := by
    rw [ht]
    apply (div_lt_one (by linarith : 0<2*q-1)).mpr
    linarith
  have hτ1 : τ<1 := by nlinarith
  have he := normalTrace_eq_product_ae hτ hτ1 a f hf
  have hi := integral_congr_ae (μ:=(γFin n).restrict E)
    ((ae_restrict_of_ae he).mono (fun x hx=>congrArg (fun t:ℝ=>t^2) hx))
  rw [←hi]
  exact normalTrace_surface_subset_le τ q a hτ hq ht E f hf

end NegativeVotingNormalTraceAllExponents
