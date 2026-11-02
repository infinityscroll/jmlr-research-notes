import GaussianBalancedFacetHessian

/-! The actual mass adjoint is an energy projection of quadratic facet jumps.
The centered spectral-gap estimate is kept as an explicit geometric premise. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingMassAdjointEnergy
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanJacobian
  NegativeVotingFanHessian NegativeVotingSecondChaosFacetGradient
  NegativeVotingSecondChaosMassAdjoint NegativeVotingGlobalTensorTransport
  NegativeVotingWeightedFacet NegativeVotingCapTail NegativeVotingFacetDegree
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The literal quadratic-label jump energy under actual Gaussian face laws. -/
def quadraticJumpEnergy (B : ι→FSC.Coord d) (h : ι→ℝ) : ℝ :=
  (1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j
    (fun x=>(quadraticLabelTest B h i x-quadraticLabelTest B h j x)^2)

def adjointEnergy (B : ι→FSC.Coord d) (h : ι→ℝ) : ℝ :=
  massAdjoint B h ⬝ᵥ (offsetJacobian B h *ᵥ massAdjoint B h)

theorem quadraticJumpEnergy_nonneg (B : ι→FSC.Coord d) (h : ι→ℝ) :
    0 ≤ quadraticJumpEnergy B h := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>
    surfaceIntegral_nonneg B h i j _ (fun _=>sq_nonneg _)

theorem adjointEnergy_nonneg (B : ι→FSC.Coord d) (h : ι→ℝ) : 0 ≤ adjointEnergy B h := by
  unfold adjointEnergy
  rw [offsetJacobian_energy]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>
    mul_nonneg (facetWeight_nonneg B h i j) (sq_nonneg _))

/-- The mass-adjoint equation pairs with its own potential to give the exact
cross energy, including the ordered-pair factor one half. -/
theorem adjointEnergy_cross (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    adjointEnergy B h=(1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j
      (fun x=>(massAdjoint B h i-massAdjoint B h j)*
        (quadraticLabelTest B h i x-quadraticLabelTest B h j x)) := by
  rw [adjointEnergy,massAdjoint_equation B h σ hσ hlower]
  simp only [dotProduct,massGradient_surface_divergence B h σ hσ hlower]
  conv_lhs => simp only [Finset.mul_sum]
  conv_lhs => simp only [←surfaceIntegral_const_mul]
  apply surface_sum_label_gap
  · intro i j x
    ring
  · intro i j k
    let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
    letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
    exact (((quadraticLabelTest_memLp B h i μ).sub (quadraticLabelTest_memLp B h j μ)).integrable
      (by norm_num)).const_mul _

/-- Pointwise Young's inequality integrated against one actual face. -/
theorem surface_young_constant (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (F : FSC.Coord d→ℝ) (c : ℝ)
    (hF : MemLp F 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    2*surfaceIntegral B h i j (fun x=>c*F x) ≤
      surfaceIntegral B h i j (fun x=>(F x)^2)+facetWeight B h i j*c^2 := by
  letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
  have hF2 : Integrable (fun x=>(F x)^2)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
    convert hF.integrable_mul hF using 1
    funext x
    exact pow_two (F x)
  have hL : Integrable (fun x=>2*(c*F x))
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) :=
    ((hF.integrable (by norm_num)).const_mul c).const_mul 2
  have hR : Integrable (fun x=>(F x)^2+c^2)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := hF2.add (integrable_const _)
  have hh : surfaceIntegral B h i j (fun x=>2*(c*F x)) ≤
      surfaceIntegral B h i j (fun x=>(F x)^2+c^2) := by
    unfold surfaceIntegral
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    exact integral_mono hL.restrict hR.restrict (fun x=>by nlinarith [sq_nonneg (F x-c)])
  rwa [surfaceIntegral_const_mul,surfaceIntegral_add B h i j _ _ hF2 (integrable_const _),
    surfaceIntegral_const] at hh

/-- The actual adjoint energy is at most the actual quadratic jump energy.
No pseudoinverse operator-norm estimate is used. -/
theorem adjointEnergy_le_quadraticJumpEnergy (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    adjointEnergy B h ≤ quadraticJumpEnergy B h := by
  have hy := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _=>
      surface_young_constant B h i j
        (fun x=>quadraticLabelTest B h i x-quadraticLabelTest B h j x)
        (massAdjoint B h i-massAdjoint B h j) (by
          let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
          letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
          exact (quadraticLabelTest_memLp B h i μ).sub (quadraticLabelTest_memLp B h j μ))))
  simp only [←Finset.mul_sum,Finset.sum_add_distrib] at hy
  have hc := adjointEnergy_cross B h σ hσ hlower
  have he := offsetJacobian_energy B h (massAdjoint B h)
  change adjointEnergy B h=(1/2:ℝ)*∑ i,∑ j,
    facetWeight B h i j*(massAdjoint B h i-massAdjoint B h j)^2 at he
  unfold quadraticJumpEnergy
  linarith

/-- A lower spectral gap on the actual centered graph turns the energy
projection estimate into the required small-adjoint norm bound. -/
theorem massAdjoint_norm_sq_le (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (gap : ℝ) (hgap : 0<gap)
    (hlaplacian : ∀ v:ι→ℝ,(∑ i,v i)=0 →
      gap*(∑ i,(v i)^2) ≤ v ⬝ᵥ (offsetJacobian B h *ᵥ v)) :
    (∑ i,(massAdjoint B h i)^2) ≤ quadraticJumpEnergy B h/gap := by
  have hh := hlaplacian (massAdjoint B h) (massAdjoint_centered B h σ hσ hlower)
  have hb := adjointEnergy_le_quadraticJumpEnergy B h σ hσ hlower
  apply (le_div_iff₀ hgap).mpr
  change _ ≤ adjointEnergy B h at hh
  nlinarith

end NegativeVotingMassAdjointEnergy
