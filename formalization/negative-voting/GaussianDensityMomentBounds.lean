import GaussianHazardIntegrability
import GaussianDiagonalWinnerIntegral
import GaussianTailRatio

/-! Actual Gaussian polynomial moments with explicit shift and scale costs.
These provide integrable envelopes for the whole-threshold split; no
normalized hazard-moment estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Classical
namespace NegativeVotingDensityMomentBounds
open WeakSimplex NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardIntegrability
  NegativeVotingDiagonalWinnerIntegral NegativeVotingGaussianTail

def standardPolynomialMoment (k : ℕ) : ℝ := ∫x:ℝ,(1+|x|)^k ∂gaussianReal 0 1

lemma integrable_standard_polynomial (k : ℕ) :
    Integrable (fun x:ℝ=>(1+|x|)^k) (gaussianReal 0 1) := by
  have hm0 := (memLp_id_gaussianReal' (μ:=0) (v:=1) k (by simp)).norm
  simp only [id_eq,Real.norm_eq_abs] at hm0
  have hm : MemLp (fun x:ℝ=>1+|x|) (k:ℝ≥0∞) (gaussianReal 0 1) := by
    convert (memLp_const (1:ℝ)).add hm0 using 1
  convert hm.integrable_norm_pow' using 1
  funext x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+|x|)]

lemma standardPolynomialMoment_nonneg (k : ℕ) : 0 ≤ standardPolynomialMoment k :=
  integral_nonneg fun x=>by positivity

lemma standardPolynomialMoment_ge_one (k : ℕ) : 1 ≤ standardPolynomialMoment k := by
  have hh := integral_mono (integrable_const (1:ℝ)) (integrable_standard_polynomial k)
    (fun x=>one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg x)))
  simpa only [integral_const,probReal_univ,one_smul,standardPolynomialMoment] using hh

lemma affine_polynomial_le (σ h x : ℝ) (hσ : 0 ≤ σ) (k : ℕ) :
    (1+|σ*x+h|)^k ≤ (1+|h|+σ)^k*(1+|x|)^k := by
  have hh : 1+|σ*x+h| ≤ (1+|h|+σ)*(1+|x|) := by
    have ha := abs_add_le (σ*x) h
    rw [abs_mul,abs_of_nonneg hσ] at ha
    nlinarith [abs_nonneg x,abs_nonneg h,mul_nonneg (abs_nonneg h) (abs_nonneg x)]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+|σ*x+h|) hh k

/-- The constant depends only on the fixed moment order. -/
theorem density_polynomial_integral_le (σ h : ℝ) (hσ : 0 < σ) (k : ℕ) :
    (∫x:ℝ,gaussianDensity σ h x*(1+|x|)^k) ≤
      standardPolynomialMoment k*(1+|h|+σ)^k := by
  rw [←gaussian_affine_integral σ h hσ]
  have hh := integral_mono_of_nonneg (ae_of_all _ fun x=>by positivity :
      0 ≤ᵐ[gaussianReal 0 1] fun x:ℝ=>(1+|σ*x+h|)^k)
    ((integrable_standard_polynomial k).const_mul ((1+|h|+σ)^k))
    (ae_of_all _ fun x=>affine_polynomial_le σ h x hσ.le k)
  change (∫x:ℝ,(1+|σ*x+h|)^k ∂gaussianReal 0 1) ≤
    ∫x:ℝ,(1+|h|+σ)^k*(1+|x|)^k ∂gaussianReal 0 1 at hh
  rw [integral_const_mul] at hh
  simpa only [standardPolynomialMoment,mul_comm] using hh

lemma gaussian_exp_kernel_eq (S H lam x : ℝ) (hS : 0 < S) (hlam : 0 < lam) :
    Real.exp (-lam*((x-H)/S)^2/2)=
      (S/(Real.sqrt lam*normalPDF 0))*gaussianDensity (S/Real.sqrt lam) H x := by
  have hs := Real.sqrt_pos.mpr hlam
  have he : ((x-H)/(S/Real.sqrt lam))^2=lam*((x-H)/S)^2 := by
    field_simp
    nlinarith [Real.sq_sqrt hlam.le]
  rw [gaussianDensity,normalPDF_ratio 0 ((x-H)/(S/Real.sqrt lam)),he]
  simp only [zero_pow (by norm_num : 2≠0),zero_sub]
  field_simp [hs.ne',(normalPDF_pos 0).ne',hS.ne']

lemma integrable_gaussian_exp_kernel_polynomial (S H lam : ℝ) (hS : 0 < S)
    (hlam : 0 < lam) (k : ℕ) :
    Integrable (fun x:ℝ=>Real.exp (-lam*((x-H)/S)^2/2)*(1+|x|)^k) volume := by
  have hh := (integrable_density_polynomial (S/Real.sqrt lam) H 1
    (div_pos hS (Real.sqrt_pos.mpr hlam)) (by norm_num) k).const_mul
      (S/(Real.sqrt lam*normalPDF 0))
  convert hh using 1
  funext x
  rw [gaussian_exp_kernel_eq S H lam x hS hlam]
  ring

theorem gaussian_exp_kernel_polynomial_integral_le (S H lam : ℝ) (hS : 0 < S)
    (hlam : 0 < lam) (k : ℕ) :
    (∫x:ℝ,Real.exp (-lam*((x-H)/S)^2/2)*(1+|x|)^k) ≤
      (S/(Real.sqrt lam*normalPDF 0))*standardPolynomialMoment k*
        (1+|H|+S/Real.sqrt lam)^k := by
  have he : (fun x:ℝ=>Real.exp (-lam*((x-H)/S)^2/2)*(1+|x|)^k)=
      fun x=>(S/(Real.sqrt lam*normalPDF 0))*(gaussianDensity (S/Real.sqrt lam) H x*(1+|x|)^k) := by
    funext x
    rw [gaussian_exp_kernel_eq S H lam x hS hlam]
    ring
  rw [he,integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left
    (density_polynomial_integral_le (S/Real.sqrt lam) H (div_pos hS (Real.sqrt_pos.mpr hlam)) k)
    (by positivity [normalPDF_pos 0] : 0 ≤ S/(Real.sqrt lam*normalPDF 0))
  simpa only [mul_assoc] using hh

end NegativeVotingDensityMomentBounds
