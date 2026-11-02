import GaussianQuadraticMovingCap
import GaussianFanMovingCells
import GaussianConditionalSecondMoment
import GaussianFanJointMass

/-! Literal affine Gaussian cell second-moment tensors and their actual joint
score/offset derivatives, with exact degree-two Hermite normalization. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators ENNReal Topology Classical
namespace NegativeVotingFanQuadraticMoments
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingMovingCap NegativeVotingDisintegration
  NegativeVotingWeightedFacet NegativeVotingFanMovingCells
  NegativeVotingModern NegativeVotingConditionalSecondMoment NegativeVotingFanTestedCells
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem hasFDerivAt_testedCell (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖^2)) :
    HasFDerivAt (fun p : Parameters d ι =>
      ∫ x in winningCell p.1 p.2 i, F x ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i F) (B,h) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have hd := NegativeVotingQuadraticMovingCap.hasFDerivAt_capTest (cellNormals B i)
    (cellNormals_unit B σ hσ hlower i) (cellSupports B h i)
    (cellNormals_noCoincident B h σ hσ hlower i) F hFc C hC hF
  rw [← fanParameterMap_base B h i] at hd
  have hh := hd.comp (B,h) (fanParameterMap B i).hasFDerivAt
  have he : (fun p : Parameters d ι => capTest (fanParameterMap B i p) F) =
      (fun p : Parameters d ι =>
        ∫ x in winningCell p.1 p.2 i, F x ∂stdGaussian (FSC.Coord d)) := by
    funext p
    unfold capTest
    rw [normalized_cap_eq_winningCell B hB]
  change HasFDerivAt (fun p => capTest (fanParameterMap B i p) F)
    (testedCellDerivative B h i F) (B,h) at hh
  rw [he] at hh
  exact hh

theorem testedCellDerivative_apply (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖^2)) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ =
      ∑ j : {j : ι // j ≠ i}, WeakSimplex.normalPDF (cellSupports B h i j) / ‖B j.1-B i‖ *
        ∫ y in tangentFace (cellNormals B i) (cellSupports B h i) j,
          F (outwardFacetPoint B h i j y) *
            (inner ℝ (δ.1 i-δ.1 j.1) (outwardFacetPoint B h i j y) + δ.2 i-δ.2 j.1)
          ∂stdGaussian (tangentSpace (cellNormals B i j)) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i) F (fanParameterMap B i δ) = _
  rw [NegativeVotingQuadraticMovingCap.capJointDerivative_apply _ (cellNormals_unit B σ hσ hlower i) _ F hFc C hC hF]
  apply Finset.sum_congr rfl
  intro j hj
  have he (x : FSC.Coord d) :
      F x * ((fanParameterMap B i δ).2 j - inner ℝ ((fanParameterMap B i δ).1 j) x) =
        (F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1)) / ‖B j.1-B i‖ := by
    rw [fanParameterMap_support, fanParameterMap_normal, real_inner_smul_left]
    simp only [inner_sub_left, div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [integral_div]
  unfold outwardFacetPoint
  ring

theorem testedCellDerivative_apply_ambient (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖^2)) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ =
      ∑ j : {j : ι // j ≠ i}, gaussianPDFReal 0 1 (pairOffset B h j.1 i) / ‖B j.1-B i‖ *
        ∫ x in affineFacet B h j.1 i,
          F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1)
          ∂FSC.sliceLaw (pairNormal B j.1 i) (pairOffset B h j.1 i) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  rw [testedCellDerivative_apply B h σ hσ hlower i F hFc C hC hF]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tangentFace_integral_eq_surface B h hB i j
    (fun x => F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1))
    (by fun_prop)]
  rfl

def centeredBilinearTest (u v x : FSC.Coord d) : ℝ :=
  inner ℝ u x * inner ℝ v x-inner ℝ u v

 theorem centeredBilinearTest_growth (u v x : FSC.Coord d) :
    |centeredBilinearTest u v x| ≤ (‖u‖*‖v‖)*(1+‖x‖^2) := by
  unfold centeredBilinearTest
  calc
    _ ≤ |inner ℝ u x*inner ℝ v x|+|inner ℝ u v| := abs_sub _ _
    _ ≤ (‖u‖*‖x‖)*(‖v‖*‖x‖)+‖u‖*‖v‖ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
        (abs_nonneg _) (by positivity)) (abs_real_inner_le_norm _ _)
    _ = _ := by ring

 def tensorTest (j k : Fin d) (x : FSC.Coord d) : ℝ :=
   x j*x k-(if j=k then 1 else 0)

 theorem centeredBilinearTest_basis (j k : Fin d) (x : FSC.Coord d) :
    centeredBilinearTest (EuclideanSpace.basisFun (Fin d) ℝ j)
      (EuclideanSpace.basisFun (Fin d) ℝ k) x=tensorTest j k x := by
  unfold centeredBilinearTest tensorTest
  rw [EuclideanSpace.basisFun_inner (Fin d) ℝ x j,EuclideanSpace.basisFun_inner (Fin d) ℝ x k,
    (EuclideanSpace.basisFun (Fin d) ℝ).inner_eq_ite]

 theorem tensorTest_growth (j k : Fin d) (x : FSC.Coord d) :
    |tensorTest j k x| ≤ 1+‖x‖^2 := by
  have hh := centeredBilinearTest_growth (EuclideanSpace.basisFun (Fin d) ℝ j)
    (EuclideanSpace.basisFun (Fin d) ℝ k) x
  simpa only [centeredBilinearTest_basis,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,
    one_mul] using hh

 def secondMomentTensor (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) (j k : Fin d) : ℝ :=
   ∫ x in winningCell B h i,tensorTest j k x ∂stdGaussian (FSC.Coord d)

 theorem hasFDerivAt_secondMomentTensor (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i : ι) (j k : Fin d) :
    HasFDerivAt (fun p : Parameters d ι => secondMomentTensor p.1 p.2 i j k)
      (testedCellDerivative B h i (tensorTest j k)) (B,h) := by
  exact hasFDerivAt_testedCell B h σ hσ hlower i (tensorTest j k)
    (by unfold tensorTest; fun_prop) 1 (by norm_num)
    (fun x => by simpa only [one_mul] using tensorTest_growth j k x)

 def secondEnergy (B : ι → FSC.Coord d) (h : ι → ℝ) : ℝ :=
   (1/2:ℝ)*∑ i,∑ j,∑ k,(secondMomentTensor B h i j k)^2

 def secondEnergyDerivative (B : ι → FSC.Coord d) (h : ι → ℝ) : Parameters d ι →L[ℝ] ℝ :=
   ∑ i,∑ j,∑ k,secondMomentTensor B h i j k • testedCellDerivative B h i (tensorTest j k)

 theorem hasFDerivAt_secondEnergy (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt (fun p : Parameters d ι => secondEnergy p.1 p.2)
      (secondEnergyDerivative B h) (B,h) := by
  have hh := HasFDerivAt.sum (u:=Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u:=Finset.univ) (fun j _ =>
      HasFDerivAt.sum (u:=Finset.univ) (fun k _ =>
        (hasFDerivAt_secondMomentTensor B h σ hσ hlower i j k).pow 2)))
  have hf := hh.const_smul (1/2:ℝ)
  have hg : (1/2:ℝ) • (∑ i,∑ j,∑ k,
      ((2:ℕ) • secondMomentTensor B h i j k ^ (2-1)) •
        testedCellDerivative B h i (tensorTest j k))=secondEnergyDerivative B h := by
    simp only [secondEnergyDerivative,Finset.smul_sum,smul_smul,Nat.reduceSub,pow_one,
      nsmul_eq_mul,Nat.cast_ofNat,←mul_assoc,show (1/2:ℝ)*2=1 by norm_num,one_mul]
  rw [hg] at hf
  apply hf.congr_of_eventuallyEq
  filter_upwards with p
  simp only [secondEnergy,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

 theorem quadraticMoment_weights_toLp (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) (i : ι) (j k : Fin d) :
    quadraticMoment (fun x => weights B h (MeasurableEquiv.toLp 2 (Fin d→ℝ) x) i) j k=
      secondMomentTensor B h i j k := by
  have hh := (gaussian_toLp_measurePreserving d).integral_comp'
    (fun x : FSC.Coord d => weights B h x i*tensorTest j k x)
  change (∫ x,weights B h (MeasurableEquiv.toLp 2 (Fin d→ℝ) x) i*tensorTest j k
      (MeasurableEquiv.toLp 2 (Fin d→ℝ) x) ∂GaussianFin.γFin d)=_ at hh
  rw [integral_weights_mul_eq_cell B hB h i] at hh
  exact hh

 theorem secondEnergy_eq_actual_chaos (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) :
    secondEnergy B h=chaosEnergy
      (fun x : Fin d→ℝ => weights B h (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2 := by
  rw [chaosEnergy_two]
  simp only [quadraticMoment_weights_toLp B hB h,secondEnergy]

 theorem hasFDerivAt_actual_second_chaos (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt (fun p : Parameters d ι => chaosEnergy
      (fun x : Fin d→ℝ => weights p.1 p.2 (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2)
      (secondEnergyDerivative B h) (B,h) := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  apply (hasFDerivAt_secondEnergy B h σ hσ hlower).congr_of_eventuallyEq
  filter_upwards [NegativeVotingFanJointMass.eventually_injective_rows B hB h] with p hp
  exact (secondEnergy_eq_actual_chaos p.1 hp p.2).symm

end NegativeVotingFanQuadraticMoments
