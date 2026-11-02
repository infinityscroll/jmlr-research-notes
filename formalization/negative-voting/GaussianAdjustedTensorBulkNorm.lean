import GaussianTensorFacetAggregation

/-! Actual Gaussian bulk estimates after subtracting the mass-adjoint scalar
from a centered quadratic label test. The scalar coefficient is arbitrary;
no estimate for the mass adjoint is assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical ENNReal

namespace NegativeVotingAdjustedTensorBulkNorm
open NegativeVotingFan NegativeVotingFanMassSecondDerivative NegativeVotingQuadraticBulkNorm
  NegativeVotingQuadraticTensorBulkNorm NegativeVotingPolynomialDegree
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingTensorFacetAggregation
  NegativeVotingWeightedFacet NegativeVotingDisintegration NegativeVotingFanJacobian
  NegativeVotingAffineLogMassBound NegativeVotingPolynomialFacetLogBound
variable {d : ℕ}

def adjustedTensorBulk (U : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z x : FSC.Coord d) : ℝ :=
  tensorBulk U A z x-c*massBulk A z x

theorem massBulk_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : MemLp (massBulk A z) 2 μ := by
  have hq := (quadraticScore_memLp_four μ A).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hh := hq.add ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) z)
  convert hh using 1
  funext x
  simp only [massBulk,quadraticScore,Pi.add_apply,id_eq]
  ring

theorem adjustedTensorBulk_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) (z : FSC.Coord d) :
    MemLp (adjustedTensorBulk U c A z) 2 μ :=
  (tensorBulk_memLp_two μ U A z).sub ((massBulk_memLp_two μ A z).const_mul c)

theorem adjustedTensorBulk_degree {κ : Type*} [Fintype κ]
    (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) (z : FSC.Coord d) :
    (fun x=>adjustedTensorBulk U c A z (R x))∈polynomialSpace 4 := by
  exact (polynomialSpace 4).sub_mem (tensorBulk_degree R U A z)
    ((polynomialSpace 4).smul_mem c (polynomialSpace_mono (by decide : 2≤4)
      (massBulk_expression_mem R A z)))

/-- Uniform ambient energy of the literal adjoint-adjusted bulk. -/
theorem adjustedTensorBulk_integral_sq_le
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) (z : FSC.Coord d) :
    (∫ x,(adjustedTensorBulk U c A z x)^2 ∂stdGaussian (FSC.Coord d))≤
      20736*((operatorHilbertSchmidt U)^2+c^2)*((operatorHilbertSchmidt A)^2+‖z‖^2) := by
  let μ := stdGaussian (FSC.Coord d)
  have hf := (tensorBulk_memLp_two μ U A z).integrable_sq
  have hg := (massBulk_memLp_two μ A z).integrable_sq
  have hab := (adjustedTensorBulk_memLp_two μ U A c z).integrable_sq
  have hm := integral_mono hab ((hf.const_mul 2).add (hg.const_mul (2*c^2)))
    (fun x=>by
      dsimp only [adjustedTensorBulk,Pi.add_apply]
      nlinarith only [sq_nonneg (tensorBulk U A z x+c*massBulk A z x)])
  simp only [Pi.add_apply] at hm
  rw [integral_add (hf.const_mul 2) (hg.const_mul (2*c^2)),
    integral_const_mul,integral_const_mul] at hm
  have ht := tensorBulk_integral_sq_le U A z
  have hs := massBulk_integral_sq_le A z
  change (∫ x,(massBulk A z x)^2 ∂μ)≤_ at hs
  have h := add_le_add (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left hs (by positivity : 0≤2*c^2))
  refine hm.trans (h.trans ?_)
  nlinarith only [mul_nonneg (sq_nonneg c)
    (add_nonneg (sq_nonneg (operatorHilbertSchmidt A)) (sq_nonneg ‖z‖))]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The mass-adjusted tensor remainder is summed through actual facet degree,
with no label-count or ambient-dimension factor. -/
theorem affineWeightedFacetEnergy_adjustedTensorBulk_le
    (B : ι→FSC.Coord d) (h : ι→ℝ)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d) (c : ι→ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0≤degree)
    (hinj : Function.Injective B)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j)≤degree) :
    affineWeightedFacetEnergy B h (fun i=>adjustedTensorBulk (U i) (c i) A z)≤
      20736*degree*quarticLogConstant a*(1+Real.log m)^4*
        ((operatorHilbertSchmidt A)^2+‖z‖^2)*
          ∑ i,((operatorHilbertSchmidt (U i))^2+(c i)^2) := by
  have hb := affineWeightedFacetEnergy_polynomial_log_le B h
    (fun i=>adjustedTensorBulk (U i) (c i) A z) a m degree hm hinj
    (fun i=>by unfold adjustedTensorBulk tensorBulk massBulk quadraticScore; fun_prop)
    (fun i j _=>adjustedTensorBulk_degree _ (U i) A (c i) z) hprob ha hdegree
  refine hb.trans ?_
  calc
    _ ≤ degree*quarticLogConstant a*(1+Real.log m)^4*
        ∑ i,20736*((operatorHilbertSchmidt (U i))^2+(c i)^2)*
          ((operatorHilbertSchmidt A)^2+‖z‖^2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _=>adjustedTensorBulk_integral_sq_le (U i) A (c i) z)
        (by unfold quarticLogConstant; positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end NegativeVotingAdjustedTensorBulkNorm
