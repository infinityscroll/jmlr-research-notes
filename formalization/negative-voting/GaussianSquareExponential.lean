import GaussianCapTailAndStrip
import NegativeVoting.RegularSimplex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Explicit Gaussian square-exponential moments for bounded-variance affine
scores. These are actual integrals, including degenerate scalar scores. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical NNReal ENNReal
namespace NegativeVotingSquareExponential
open NegativeVotingCapTail NegativeVoting

theorem gaussian_density_square_exp (x : ℝ) :
    gaussianPDFReal 0 1 x*Real.exp (x^2/4)=
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(1/4:ℝ)*x^2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem gaussian_square_exp_integrable :
    Integrable (fun x : ℝ => Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0)≠0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF,smul_eq_mul,gaussian_density_square_exp]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul _

theorem integral_gaussian_square_exp_le_two :
    (∫x : ℝ,Real.exp (x^2/4) ∂gaussianReal 0 1) ≤ 2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  simp_rw [smul_eq_mul,gaussian_density_square_exp]
  rw [integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have hs := Real.sqrt_pos.mpr (show 0<2*Real.pi by positivity)
  have hle : Real.sqrt (Real.pi/(1/4:ℝ)) ≤ 2*Real.sqrt (2*Real.pi) := by
    have h1 := Real.sq_sqrt (show 0 ≤ Real.pi/(1/4:ℝ) by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    nlinarith [Real.sqrt_nonneg (Real.pi/(1/4:ℝ)),Real.sqrt_nonneg (2*Real.pi)]
  calc (Real.sqrt (2*Real.pi))⁻¹*Real.sqrt (Real.pi/(1/4:ℝ)) ≤
      (Real.sqrt (2*Real.pi))⁻¹*(2*Real.sqrt (2*Real.pi)) :=
        mul_le_mul_of_nonneg_left hle (inv_pos.mpr hs).le
    _ = 2 := by field_simp

theorem affine_square_exp_pointwise (a s x : ℝ) (hs : |s| ≤ 1) :
    Real.exp ((a+s*x)^2/8) ≤ Real.exp (a^2/4)*Real.exp (x^2/4) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs2 : s^2 ≤ 1 := by
    have hh := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ 1+|s| by positivity)
    nlinarith [sq_abs s]
  nlinarith [sq_nonneg (a-s*x),mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg x)]

theorem affine_square_exp_integrable (a s : ℝ) (hs : |s| ≤ 1) :
    Integrable (fun x : ℝ => Real.exp ((a+s*x)^2/8)) (gaussianReal 0 1) := by
  apply (gaussian_square_exp_integrable.const_mul (Real.exp (a^2/4))).mono'
    (by fun_prop)
  filter_upwards with x
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using affine_square_exp_pointwise a s x hs

theorem integral_affine_square_exp_le (a s : ℝ) (hs : |s| ≤ 1) :
    (∫x : ℝ,Real.exp ((a+s*x)^2/8) ∂gaussianReal 0 1) ≤ 2*Real.exp (a^2/4) := by
  calc (∫x : ℝ,Real.exp ((a+s*x)^2/8) ∂gaussianReal 0 1) ≤
      ∫x : ℝ,Real.exp (a^2/4)*Real.exp (x^2/4) ∂gaussianReal 0 1 :=
        integral_mono (affine_square_exp_integrable a s hs)
          (gaussian_square_exp_integrable.const_mul _) (fun x => affine_square_exp_pointwise a s x hs)
    _ ≤ 2*Real.exp (a^2/4) := by
      rw [integral_const_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        integral_gaussian_square_exp_le_two (Real.exp_pos (a^2/4)).le

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_inner_scaled_law (v : E) :
    HasLaw (fun x : ℝ => ‖v‖*x) (gaussianReal 0 ((‖v‖^2).toNNReal)) (gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero,mul_one]
  congr 1
  ext
  simp only [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

theorem gaussian_inner_law (v : E) :
    HasLaw (fun x : E => inner ℝ v x) (gaussianReal 0 ((‖v‖^2).toNNReal)) (stdGaussian E) :=
  ⟨by fun_prop,gaussian_inner_map v⟩

theorem affine_inner_square_exp_integrable (v : E) (hv : ‖v‖ ≤ 1) (a : ℝ) :
    Integrable (fun x => Real.exp ((a+inner ℝ v x)^2/8)) (stdGaussian E) := by
  have hi := affine_square_exp_integrable a ‖v‖ (by simpa only [abs_of_nonneg (norm_nonneg _)] using hv)
  have hlaw := gaussian_inner_scaled_law v
  have hi' : Integrable (fun z : ℝ => Real.exp ((a+z)^2/8))
      (gaussianReal 0 ((‖v‖^2).toNNReal)) := by
    rw [← hlaw.map_eq]
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hi
  exact (gaussian_inner_law v).integrable_comp hi'

theorem integral_affine_inner_square_exp_le (v : E) (hv : ‖v‖ ≤ 1) (a : ℝ) :
    (∫x,Real.exp ((a+inner ℝ v x)^2/8) ∂stdGaussian E) ≤ 2*Real.exp (a^2/4) := by
  have h1 := (gaussian_inner_law v).integral_comp
    (f:=fun z : ℝ => Real.exp ((a+z)^2/8)) (by fun_prop)
  have h2 := (gaussian_inner_scaled_law v).integral_comp
    (f:=fun z : ℝ => Real.exp ((a+z)^2/8)) (by fun_prop)
  change (∫x,Real.exp ((a+inner ℝ v x)^2/8) ∂stdGaussian E)=_ at h1
  change (∫x : ℝ,Real.exp ((a+‖v‖*x)^2/8) ∂gaussianReal 0 1)=_ at h2
  rw [h1,← h2]
  exact integral_affine_square_exp_le a ‖v‖ (by simpa only [abs_of_nonneg (norm_nonneg _)] using hv)

section FiniteFamily
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def affineMaxAbs (B : ι → E) (a : ι → ℝ) (x : E) : ℝ :=
  maxScore (fun i => |a i+inner ℝ (B i) x|)

@[fun_prop] theorem measurable_affineMaxAbs (B : ι → E) (a : ι → ℝ) :
    Measurable (affineMaxAbs B a) :=
  measurable_finite_max (fun x i => |a i+inner ℝ (B i) x|)
    Finset.univ Finset.univ_nonempty (fun i _ => by fun_prop)

theorem max_square_exp_le_sum (B : ι → E) (a : ι → ℝ) (x : E) :
    Real.exp ((affineMaxAbs B a x)^2/8) ≤ ∑i,Real.exp ((a i+inner ℝ (B i) x)^2/8) := by
  let k := chosenWinner (fun i => |a i+inner ℝ (B i) x|)
  have he : affineMaxAbs B a x=|a k+inner ℝ (B k) x| :=
    finite_max_eq_chosenWinner _
  rw [he,sq_abs]
  exact Finset.single_le_sum (fun i _ => (Real.exp_pos ((a i+inner ℝ (B i) x)^2/8)).le)
    (Finset.mem_univ k)

theorem max_square_exp_integrable (B : ι → E) (hv : ∀i,‖B i‖ ≤ 1) (a : ι → ℝ) :
    Integrable (fun x => Real.exp ((affineMaxAbs B a x)^2/8)) (stdGaussian E) := by
  have hi : Integrable (fun x => ∑i,Real.exp ((a i+inner ℝ (B i) x)^2/8)) (stdGaussian E) :=
    integrable_finsetSum _ (fun i _ => affine_inner_square_exp_integrable (B i) (hv i) (a i))
  apply hi.mono' (by fun_prop)
  filter_upwards with x
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using max_square_exp_le_sum B a x

theorem integral_max_square_exp_le (B : ι → E) (hv : ∀i,‖B i‖ ≤ 1) (a : ι → ℝ) :
    (∫x,Real.exp ((affineMaxAbs B a x)^2/8) ∂stdGaussian E) ≤
      2*∑i,Real.exp ((a i)^2/4) := by
  calc (∫x,Real.exp ((affineMaxAbs B a x)^2/8) ∂stdGaussian E) ≤
      ∫x,∑i,Real.exp ((a i+inner ℝ (B i) x)^2/8) ∂stdGaussian E :=
        integral_mono (max_square_exp_integrable B hv a)
          (integrable_finsetSum _ (fun i _ => affine_inner_square_exp_integrable (B i) (hv i) (a i)))
          (max_square_exp_le_sum B a)
    _ = ∑i,∫x,Real.exp ((a i+inner ℝ (B i) x)^2/8) ∂stdGaussian E :=
      integral_finsetSum _ (fun i _ => affine_inner_square_exp_integrable (B i) (hv i) (a i))
    _ ≤ ∑i,2*Real.exp ((a i)^2/4) :=
      Finset.sum_le_sum (fun i _ => integral_affine_inner_square_exp_le (B i) (hv i) (a i))
    _ = _ := (Finset.mul_sum ..).symm

/-- Exact Lq normalization of the exponential maximum. No independence of the
scores is needed: every score is an actual bounded-norm Gaussian functional. -/
theorem max_square_exp_q_norm (B : ι → E) (hv : ∀i,‖B i‖ ≤ 1) (a : ι → ℝ)
    (q : ℝ) (hq : 0<q) :
    eLpNorm (fun x => Real.exp ((affineMaxAbs B a x)^2/(8*q))) (ENNReal.ofReal q) (stdGaussian E)=
      ENNReal.ofReal (∫x,Real.exp ((affineMaxAbs B a x)^2/8) ∂stdGaussian E) ^ (1/q) := by
  let G := fun x => Real.exp ((affineMaxAbs B a x)^2/8)
  have hi : Integrable G (stdGaussian E) := max_square_exp_integrable B hv a
  have he : (fun x => Real.exp ((affineMaxAbs B a x)^2/(8*q)))=
      (fun x => ‖G x‖ ^ (1/q)) := by
    funext x
    simp only [G,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_mul]
    congr 1
    field_simp
  have hp : ENNReal.ofReal q*ENNReal.ofReal (1/q)=1 := by
    rw [← ENNReal.ofReal_mul hq.le]
    simp [hq.ne']
  rw [he,eLpNorm_norm_rpow G hi.aestronglyMeasurable (one_div_pos.mpr hq),hp,
    eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  congr 2
  apply integral_congr_ae
  filter_upwards with x
  simp only [G,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem max_square_exp_q_memLp (B : ι → E) (hv : ∀i,‖B i‖ ≤ 1) (a : ι → ℝ)
    (q : ℝ) (hq : 0<q) :
    MemLp (fun x => Real.exp ((affineMaxAbs B a x)^2/(8*q)))
      (ENNReal.ofReal q) (stdGaussian E) := by
  rw [memLp_iff,max_square_exp_q_norm B hv a q hq]
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_pos.mpr hq).le ENNReal.ofReal_ne_top

theorem max_square_exp_q_norm_le (B : ι → E) (hv : ∀i,‖B i‖ ≤ 1) (a : ι → ℝ)
    (q : ℝ) (hq : 0<q) :
    eLpNorm (fun x => Real.exp ((affineMaxAbs B a x)^2/(8*q)))
      (ENNReal.ofReal q) (stdGaussian E) ≤
        ENNReal.ofReal (2*∑i,Real.exp ((a i)^2/4)) ^ (1/q) := by
  rw [max_square_exp_q_norm B hv a q hq]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (integral_max_square_exp_le B hv a))
    (one_div_pos.mpr hq).le

/-- At logarithmic exponents the maximum of any finite family of bounded-variance
Gaussian scores has a dimension-independent exponential norm. The means may
grow like the square root of the logarithm of the family size. -/
theorem max_square_exp_q_norm_le_uniform (B : ι → E) (hv : ∀i,‖B i‖ ≤ 1)
    (a : ι → ℝ) (D q : ℝ) (hD : 0 ≤ D)
    (ha : ∀ i, (a i)^2 ≤ D*(1+Real.log (Fintype.card ι : ℝ)))
    (hq : 1+Real.log (Fintype.card ι : ℝ) ≤ q) :
    eLpNorm (fun x => Real.exp ((affineMaxAbs B a x)^2/(8*q)))
      (ENNReal.ofReal q) (stdGaussian E) ≤ ENNReal.ofReal (Real.exp (1+D/4)) := by
  have hm : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hm1 : 1 ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := ι)))
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg hm1
  have hq0 : 0 < q := by linarith
  have hs : (∑ i, Real.exp ((a i)^2/4)) ≤
      (Fintype.card ι : ℝ)*Real.exp (D*(1+Real.log (Fintype.card ι : ℝ))/4) := by
    calc
      _ ≤ ∑ _i : ι, Real.exp (D*(1+Real.log (Fintype.card ι : ℝ))/4) :=
        Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by linarith [ha i]))
      _ = _ := by simp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hb : 2*∑ i, Real.exp ((a i)^2/4) ≤ Real.exp ((1+D/4)*q) := by
    calc
      _ ≤ 2*((Fintype.card ι : ℝ)*
          Real.exp (D*(1+Real.log (Fintype.card ι : ℝ))/4)) := by linarith
      _ ≤ Real.exp 1*((Fintype.card ι : ℝ)*
          Real.exp (D*(1+Real.log (Fintype.card ι : ℝ))/4)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp ((1+D/4)*(1+Real.log (Fintype.card ι : ℝ))) := by
        rw [← Real.exp_log hm]
        simp only [Real.log_exp]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq (by positivity))
  apply (max_square_exp_q_norm_le B hv a q hq0).trans
  calc
    _ ≤ ENNReal.ofReal (Real.exp ((1+D/4)*q)) ^ (1/q) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hb) (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      field_simp
end FiniteFamily
end Euclidean
end NegativeVotingSquareExponential
