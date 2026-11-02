import GaussianAffineOperatorDerivative
import GaussianConditionalSecondMoment
import GaussianRegularFacetMean

/-! Dimension-independent control of the actual affine Gaussian logarithmic
mass derivative by conditional first and second moments. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffineLogMassBound
open NegativeVotingAffineOperatorDerivative NegativeVotingConditionalSecondMoment
  NegativeVotingRegularFacetMean
variable {d : ℕ}

def operatorEntries (A : FSC.Coord d →L[ℝ] FSC.Coord d) (j k : Fin d) : ℝ :=
  (A (EuclideanSpace.basisFun (Fin d) ℝ j)) k

def operatorHilbertSchmidt (A : FSC.Coord d →L[ℝ] FSC.Coord d) : ℝ :=
  Real.sqrt (∑ j,∑ k,(operatorEntries A j k)^2)

theorem quadratic_score_eq_entries (A : FSC.Coord d →L[ℝ] FSC.Coord d) (x : FSC.Coord d) :
    inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap=
      ∑ j,∑ k,operatorEntries A j k*(x j*x k-(if j=k then 1 else 0)) := by
  have hi (j : Fin d) : inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ j)) x=
      ∑ k,(A (EuclideanSpace.basisFun (Fin d) ℝ j)) k*x k := by
    simp only [PiLp.inner_apply,Real.inner_apply]
  rw [←basis_quadratic_sum A x,←basis_trace_sum A]
  simp only [hi,EuclideanSpace.basisFun_inner,EuclideanSpace.inner_basisFun_real]
  simp only [Finset.sum_mul,mul_sub,Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [operatorEntries]
    ring
  · simp [operatorEntries]

theorem coordinate_quadratic_integrable (s : Set (FSC.Coord d)) (j k : Fin d) :
    Integrable (fun x : FSC.Coord d=>x j*x k-(if j=k then 1 else 0))
      ((stdGaussian (FSC.Coord d)).restrict s) := by
  have hh := bilinear_integrable s (EuclideanSpace.basisFun (Fin d) ℝ j)
    (EuclideanSpace.basisFun (Fin d) ℝ k)
  simp only [EuclideanSpace.basisFun_inner] at hh
  exact hh.sub (integrable_const _)

theorem quadratic_score_integrable (s : Set (FSC.Coord d))
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    Integrable (fun x : FSC.Coord d=>inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)
      ((stdGaussian (FSC.Coord d)).restrict s) := by
  simp_rw [quadratic_score_eq_entries]
  exact integrable_finsetSum _ fun j _=>integrable_finsetSum _ fun k _=>
    (coordinate_quadratic_integrable s j k).const_mul _

theorem conditional_quadratic_pairing (s : Set (FSC.Coord d))
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    (∫ x in s,(inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)
      ∂stdGaussian (FSC.Coord d))/(stdGaussian (FSC.Coord d) s).toReal=
      ∑ j,∑ k,operatorEntries A j k*euclideanConditionalQuadraticTensor s j k := by
  simp_rw [quadratic_score_eq_entries]
  rw [integral_finsetSum Finset.univ (fun j _=>integrable_finsetSum _ fun k _=>
    (coordinate_quadratic_integrable s j k).const_mul _),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _=>(coordinate_quadratic_integrable s j k).const_mul _),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  unfold euclideanConditionalQuadraticTensor
  ring

theorem tensor_pairing_cauchy (A Q : Fin d → Fin d → ℝ) :
    |∑ j,∑ k,A j k*Q j k| ≤
      Real.sqrt (∑ j,∑ k,(A j k)^2)*Real.sqrt (∑ j,∑ k,(Q j k)^2) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d×Fin d))
    (fun p=>A p.1 p.2) (fun p=>Q p.1 p.2)
  simp only [Fintype.sum_prod_type] at hh
  have hs := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs,Real.sqrt_mul (Finset.sum_nonneg (fun j _=>
    Finset.sum_nonneg (fun k _=>sq_nonneg _)))] at hs
  exact hs

/-- The literal Gaussian quadratic score is controlled by the actual event
probability and Hilbert--Schmidt norm, with no dimension factor. -/
theorem conditional_quadratic_score_bound (s : Set (FSC.Coord d)) (hs : MeasurableSet s)
    (hp : 0 < (stdGaussian (FSC.Coord d) s).toReal)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    |(∫ x in s,(inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)
      ∂stdGaussian (FSC.Coord d))/(stdGaussian (FSC.Coord d) s).toReal| ≤
      4*Real.exp 1*(1+Real.log (1/(stdGaussian (FSC.Coord d) s).toReal))*operatorHilbertSchmidt A := by
  rw [conditional_quadratic_pairing]
  have hc := tensor_pairing_cauchy (operatorEntries A) (euclideanConditionalQuadraticTensor s)
  have hq := euclidean_conditional_quadratic_frobenius_bound s hs hp
  have hh := mul_le_mul_of_nonneg_left hq
    (Real.sqrt_nonneg (∑ j,∑ k,(operatorEntries A j k)^2))
  exact hc.trans (by simpa only [operatorHilbertSchmidt,mul_comm] using hh)

/-- Conditional Gaussian means, directly in terms of the actual probability. -/
theorem conditional_mean_probability_bound (s : Set (FSC.Coord d)) (hs : MeasurableSet s)
    (hp : 0 < (stdGaussian (FSC.Coord d) s).toReal) :
    ‖((stdGaussian (FSC.Coord d) s).toReal)⁻¹ • (∫ x in s,x ∂stdGaussian (FSC.Coord d))‖ ≤
      2*Real.sqrt (Real.log (1/(stdGaussian (FSC.Coord d) s).toReal))+
        (Real.sqrt (2*Real.pi))⁻¹ := by
  let p := (stdGaussian (FSC.Coord d) s).toReal
  have hp' : 0 < p := hp
  have hp1 : p ≤ 1 := measureReal_le_one
  have hm : 1 ≤ 1/p := (le_div_iff₀ hp').mpr (by simpa using hp1)
  have hl : 1/(1/p)^2 ≤ p := by
    simp only [one_div,inv_pow,inv_inv]
    have hh := mul_nonneg hp'.le (sub_nonneg.mpr hp1)
    nlinarith
  exact gaussian_set_conditional_mean_bound s hs (1/p) hm hp hl

/-- The actual logarithmic Gaussian mass derivative is bounded by the
Hilbert--Schmidt deformation and translation scales, uniformly in dimension. -/
theorem affine_log_mass_derivative_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1) (b : ι → ℝ)
    (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    |deriv (fun t : ℝ=>Real.log ((stdGaussian (FSC.Coord d)
      ((fun x=>x+t • A x+t • z) ⁻¹' FSC.cap w b)).toReal)) 0| ≤
      4*Real.exp 1*(1+Real.log (1/FSC.capMass w b))*operatorHilbertSchmidt A+
        ‖z‖*(2*Real.sqrt (Real.log (1/FSC.capMass w b))+(Real.sqrt (2*Real.pi))⁻¹) := by
  let C := FSC.cap w b
  let p := FSC.capMass w b
  let μ := stdGaussian (FSC.Coord d)
  have hq := conditional_quadratic_score_bound C (FSC.measurableSet_cap w b) hp A
  have hm := conditional_mean_probability_bound C (FSC.measurableSet_cap w b) hp
  have hi : Integrable (fun x : FSC.Coord d=>inner ℝ x (A x)) (μ.restrict C) := by
    have hh := (quadratic_score_integrable C A).add
      (integrable_const (LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap))
    simpa only [Pi.add_def,sub_add_cancel] using hh
  have hI : (∫ x in C,inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap ∂μ)=
      (∫ x in C,inner ℝ x (A x) ∂μ)-p*LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap := by
    rw [integral_sub hi (integrable_const _),setIntegral_const]
    rfl
  have hlin : (∫ x in C,inner ℝ z x ∂μ)/p=
      inner ℝ z (p⁻¹ • (∫ x in C,x ∂μ)) := by
    have hv : Integrable (fun x : FSC.Coord d=>x) (μ.restrict C) := IsGaussian.integrable_id.restrict
    have hh := integral_inner (𝕜:=ℝ) hv z
    change (∫ x in C,inner ℝ z x ∂μ)=inner ℝ z (∫ x in C,x ∂μ) at hh
    rw [hh,real_inner_smul_right]
    ring
  have hscore : ((∫ x in C,inner ℝ x (A x) ∂μ)-p*LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap+
      (∫ x in C,inner ℝ z x ∂μ))/p=
      (∫ x in C,inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap ∂μ)/p+
      inner ℝ z (p⁻¹ • (∫ x in C,x ∂μ)) := by rw [hI,←hlin]; ring
  rw [(hasDerivAt_log_affine_gaussian_mass w hw b hb hp A z).deriv]
  change |((∫ x in C,inner ℝ x (A x) ∂μ)-p*LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap+
    (∫ x in C,inner ℝ z x ∂μ))/p| ≤ _
  rw [hscore]
  have hlinear := (abs_real_inner_le_norm z (p⁻¹ • (∫ x in C,x ∂μ))).trans
    (mul_le_mul_of_nonneg_left hm (norm_nonneg z))
  exact (abs_add_le _ _).trans (add_le_add hq hlinear)

end NegativeVotingAffineLogMassBound
