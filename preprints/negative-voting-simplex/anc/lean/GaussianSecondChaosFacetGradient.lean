import GaussianSecondChaosMassAdjoint
import GaussianFanQuadraticHessian

/-! The mass adjoint's source is the literal divergence of quadratic Gaussian
facet tests. All tensor tests, integrability, and derivative identifications
are derived from the actual allocation, not supplied as surface data. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped RealInnerProductSpace BigOperators ENNReal Topology Classical
namespace NegativeVotingSecondChaosFacetGradient
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanQuadraticMoments
  NegativeVotingFanMovingCells NegativeVotingFanHessian NegativeVotingSecondChaosMassAdjoint
  NegativeVotingFanJacobian NegativeVotingCapTail NegativeVotingWeightedFacet
  NegativeVotingDisintegration NegativeVotingPolyhedral
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

 theorem tensorTest_memLp (μ : Measure (FSC.Coord d)) [IsGaussian μ] (j k : Fin d) :
    MemLp (tensorTest j k) 2 μ := by
  haveI : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have hj : MemLp (fun x : FSC.Coord d=>x j) 4 μ := by
    simpa only [id_eq,EuclideanSpace.basisFun_inner] using
      (IsGaussian.memLp_id μ 4 (by norm_num)).const_inner (𝕜:=ℝ)
        (EuclideanSpace.basisFun (Fin d) ℝ j)
  have hk : MemLp (fun x : FSC.Coord d=>x k) 4 μ := by
    simpa only [id_eq,EuclideanSpace.basisFun_inner] using
      (IsGaussian.memLp_id μ 4 (by norm_num)).const_inner (𝕜:=ℝ)
        (EuclideanSpace.basisFun (Fin d) ℝ k)
  unfold tensorTest
  simpa only [Pi.sub_def,Pi.mul_def] using
    (hj.mul hk).sub (memLp_const (if j=k then (1:ℝ) else 0))

 def quadraticLabelTest (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) : ℝ :=
   ∑ j,∑ k,secondMomentTensor B h i j k*tensorTest j k x

 def quadraticLabelBound (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) : ℝ :=
   ∑ j,∑ k,|secondMomentTensor B h i j k|

 theorem quadraticLabelBound_nonneg (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    0 ≤ quadraticLabelBound B h i :=
   Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>abs_nonneg _))

 theorem quadraticLabelTest_growth (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    |quadraticLabelTest B h i x| ≤ quadraticLabelBound B h i*(1+‖x‖^2) := by
  unfold quadraticLabelTest quadraticLabelBound
  calc
    _ ≤ ∑ j,∑ k,|secondMomentTensor B h i j k*tensorTest j k x| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _=>Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ j,∑ k,|secondMomentTensor B h i j k| *(1+‖x‖^2) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (tensorTest_growth j k x) (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

 theorem quadraticLabelTest_continuous (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    Continuous (quadraticLabelTest B h i) := by
  unfold quadraticLabelTest tensorTest
  fun_prop

 theorem quadraticLabelTest_memLp (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι)
    (μ : Measure (FSC.Coord d)) [IsGaussian μ] : MemLp (quadraticLabelTest B h i) 2 μ :=
   memLp_finsetSum Finset.univ (fun j _=>memLp_finsetSum Finset.univ
     (fun k _=>(tensorTest_memLp μ j k).const_mul (secondMomentTensor B h i j k)))

 theorem integral_quadraticLabelTest (B C : ι→FSC.Coord d) (h e : ι→ℝ) (i : ι) :
    (∫ x in winningCell C e i,quadraticLabelTest B h i x ∂stdGaussian (FSC.Coord d))=
      ∑ j,∑ k,secondMomentTensor B h i j k*secondMomentTensor C e i j k := by
  unfold quadraticLabelTest
  rw [integral_finsetSum Finset.univ (fun j _=>integrable_finsetSum Finset.univ
    (fun k _=>((tensorTest_memLp (stdGaussian (FSC.Coord d)) j k).integrable (by norm_num)).const_mul
      (secondMomentTensor B h i j k) |>.restrict))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _=>
    ((tensorTest_memLp (stdGaussian (FSC.Coord d)) j k).integrable (by norm_num)).const_mul
      (secondMomentTensor B h i j k) |>.restrict)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  rfl

 theorem secondEnergyDerivative_eq_quadraticLabelTests (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    secondEnergyDerivative B h=∑ i,testedCellDerivative B h i (quadraticLabelTest B h i) := by
  have hd := HasFDerivAt.sum (u:=Finset.univ) (fun i _=>
    NegativeVotingFanQuadraticMoments.hasFDerivAt_testedCell B h σ hσ hlower i
      (quadraticLabelTest B h i) (quadraticLabelTest_continuous B h i)
      (quadraticLabelBound B h i) (quadraticLabelBound_nonneg B h i)
      (quadraticLabelTest_growth B h i))
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun i _=>
    HasFDerivAt.sum (u:=Finset.univ) (fun j _=>
      HasFDerivAt.sum (u:=Finset.univ) (fun k _=>
        (hasFDerivAt_secondMomentTensor B h σ hσ hlower i j k).const_smul
          (secondMomentTensor B h i j k))))
  have hs' : HasFDerivAt (fun p : Parameters d ι=>
      ∑ i,∫ x in winningCell p.1 p.2 i,quadraticLabelTest B h i x ∂stdGaussian (FSC.Coord d))
      (secondEnergyDerivative B h) (B,h) := by
    apply hs.congr_of_eventuallyEq
    filter_upwards with p
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,integral_quadraticLabelTest]
  have hd' : HasFDerivAt (fun p : Parameters d ι=>
      ∑ i,∫ x in winningCell p.1 p.2 i,quadraticLabelTest B h i x ∂stdGaussian (FSC.Coord d))
      (∑ i,testedCellDerivative B h i (quadraticLabelTest B h i)) (B,h) := by
    apply hd.congr_of_eventuallyEq
    filter_upwards with p
    simp only [Finset.sum_apply]
  exact hs'.unique hd'

 theorem testedCellDerivative_apply_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d→ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x,|F x| ≤ C*(1+‖x‖^2)) (D : ι→FSC.Coord d) (v : ι→ℝ) :
    testedCellDerivative B h i F (D,v)=∑ j,surfaceIntegral B h i j
      (fun x=>F x*(affineScore D v i x-affineScore D v j x)) := by
  rw [NegativeVotingFanQuadraticMoments.testedCellDerivative_apply_ambient B h σ hσ hlower i F hFc C hC hF]
  have he (j : ι) : (fun x : FSC.Coord d=>F x*(inner ℝ (D i-D j) x+v i-v j))=
      fun x=>F x*(affineScore D v i x-affineScore D v j x) := by
    funext x
    simp only [affineScore,inner_sub_left]
    ring
  simp_rw [he]
  change (∑ j : {j : ι // j ≠ i},surfaceIntegral B h j.1 i
    (fun x=>F x*(affineScore D v i x-affineScore D v j.1 x)))=_
  calc
    _ = ∑ j : {j : ι // j ≠ i},surfaceIntegral B h i j.1
        (fun x=>F x*(affineScore D v i x-affineScore D v j.1 x)) :=
      Finset.sum_congr rfl (fun j _=>surfaceIntegral_reverse B h i j.1 _)
    _ = _ := by
      rw [←Finset.sum_subtype (p:=fun j : ι=>j≠i) (Finset.univ.erase i)
        (fun j=>by simp) (fun j=>surfaceIntegral B h i j
          (fun x=>F x*(affineScore D v i x-affineScore D v j x)))]
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro j _ hj
      have hji : j=i := by simpa using hj
      rw [hji,surfaceIntegral_diagonal]

 theorem secondEnergyDerivative_surface_formula (B D : ι→FSC.Coord d) (h v : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    secondEnergyDerivative B h (D,v)=∑ i,∑ j,surfaceIntegral B h i j
      (fun x=>quadraticLabelTest B h i x*(affineScore D v i x-affineScore D v j x)) := by
  rw [secondEnergyDerivative_eq_quadraticLabelTests B h σ hσ hlower]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact testedCellDerivative_apply_surface B h σ hσ hlower i (quadraticLabelTest B h i)
    (quadraticLabelTest_continuous B h i) (quadraticLabelBound B h i)
    (quadraticLabelBound_nonneg B h i) (quadraticLabelTest_growth B h i) D v

 theorem surfaceIntegral_const_mul (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (F : FSC.Coord d→ℝ) (c : ℝ) :
    surfaceIntegral B h i j (fun x=>c*F x)=c*surfaceIntegral B h i j F := by
  unfold surfaceIntegral
  rw [integral_const_mul]
  ring

 theorem surfaceIntegral_mul_const (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (F : FSC.Coord d→ℝ) (c : ℝ) :
    surfaceIntegral B h i j (fun x=>F x*c)=surfaceIntegral B h i j F*c := by
  unfold surfaceIntegral
  rw [integral_mul_const]
  ring

 theorem surfaceIntegral_quadratic_sub (B : ι→FSC.Coord d) (h : ι→ℝ) (i j a b : ι) :
    surfaceIntegral B h i j (fun x=>quadraticLabelTest B h a x-quadraticLabelTest B h b x)=
      surfaceIntegral B h i j (quadraticLabelTest B h a)-
        surfaceIntegral B h i j (quadraticLabelTest B h b) := by
  letI := sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
  unfold surfaceIntegral
  rw [integral_sub ((quadraticLabelTest_memLp B h a _).integrable (by norm_num)).restrict
    ((quadraticLabelTest_memLp B h b _).integrable (by norm_num)).restrict,mul_sub]

 theorem secondEnergyDerivative_offsets_surface (B : ι→FSC.Coord d) (h v : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    secondEnergyDerivative B h (0,v)=∑ i,(∑ j,surfaceIntegral B h i j
      (fun x=>quadraticLabelTest B h i x-quadraticLabelTest B h j x))*v i := by
  rw [secondEnergyDerivative_surface_formula B 0 h v σ hσ hlower]
  simp only [affineScore,Pi.zero_apply,inner_zero_left,zero_add]
  simp_rw [surfaceIntegral_mul_const,surfaceIntegral_quadratic_sub]
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [surfaceIntegral_reverse]

/-- The actual offset gradient is exactly the divergence of the literal
quadratic facet tests, including their full Gaussian surface normalization. -/
 theorem massGradient_surface_divergence (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    massGradient B h i=∑ j,surfaceIntegral B h i j
      (fun x=>quadraticLabelTest B h i x-quadraticLabelTest B h j x) := by
  unfold massGradient offsetCoefficients
  rw [secondEnergyDerivative_offsets_surface B h _ σ hσ hlower]
  simp [Pi.single_apply]

end NegativeVotingSecondChaosFacetGradient
