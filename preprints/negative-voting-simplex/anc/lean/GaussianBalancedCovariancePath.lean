import GaussianBalancedOffsetPath
import GaussianCovarianceOffsets

/-! The actual covariance-coordinate balancing path, with exact physical and
label derivative norm transfer for the Gaussian continuation argument. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedCovariancePath
open NegativeVotingBalancedOffsetPath NegativeVotingCovarianceOffsets
  NegativeVotingFanInverse NegativeVotingFanSelectedOffsets NegativeVotingBalancedReference
  NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingAffineBasisLower NegativeVotingFanCovarianceValue NegativeVotingFanJointInverse
  NegativeVotingFacetConditionalPlane NegativeVotingLocalCovarianceFactor
variable {n d : ℕ}

def covarianceLineLabels (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) : centeredGauge (Fin (n+2)) :=
  operatorOffsets b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)

def covarianceLineShift (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) : FSC.Coord d :=
  physicalOffsetMap b (covarianceLineLabels b H t)

theorem operatorOffsets_eq_selected_factor (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (C : FSC.Coord d →L[ℝ] FSC.Coord d)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C) :
    operatorOffsets b (uniformMass n) C=
      selectedOffsets (fun i=>R (b i)) (uniformMass n) := by
  let bR := mappedBasis b R
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound bR
  have hg := factor_gram b C R hR hRC
  unfold operatorOffsets
  rw [←hg]
  change covarianceOffsets (Matrix.gram ℝ (bR : Fin (n+2) → FSC.Coord d)) (uniformMass n)=
    selectedOffsets bR (uniformMass n)
  exact covarianceOffsets_gram bR σ hσ hlower _ (uniformMass_pos n) (uniformMass_sum n)

theorem covarianceLineShift_zero (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) : covarianceLineShift b H 0=0 := by
  have hh := operatorOffsets_eq_selected_factor b (ContinuousLinearMap.id ℝ (FSC.Coord d))
    (ContinuousLinearEquiv.refl ℝ (FSC.Coord d)) (by intro x y; rfl) (by ext x; rfl)
  unfold covarianceLineShift covarianceLineLabels
  have hz : ContinuousLinearMap.id ℝ (FSC.Coord d)+(0 : ℝ) • H=ContinuousLinearMap.id ℝ (FSC.Coord d) := by module
  rw [hz,hh]
  simpa only [balancedOffset,ContinuousLinearMap.id_apply,ContinuousLinearEquiv.refl_apply] using balancedOffset_identity b hG

theorem covarianceLineLabels_contDiffAt (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) (t : ℝ)
    (hC : (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)∈pdCone) :
    ContDiffAt ℝ 1 (covarianceLineLabels b H) t := by
  let I : SymmetricOperators (FSC.Coord d) := symmetricIdentity
  let K : SymmetricOperators (FSC.Coord d) := ⟨H,hH.isSelfAdjoint⟩
  have hc : ContDiffAt ℝ 1 (fun u : ℝ=>(I+u • K,(0 : centeredGauge (Fin (n+2))))) t := by
    fun_prop
  have hj := operatorOffsets_joint_C1 b (uniformMass n) (uniformMass_pos n)
    (uniformMass_sum n) (I+t • K) hC
  have hh := hj.comp t hc
  unfold covarianceLineLabels
  simpa only [Function.comp_def,Prod.fst,Prod.snd,
    Submodule.coe_zero,add_zero,Submodule.coe_add,Submodule.coe_smul,I,K,symmetricIdentity] using hh

theorem covarianceLineShift_contDiffAt (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) (t : ℝ)
    (hC : (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)∈pdCone) :
    ContDiffAt ℝ 1 (covarianceLineShift b H) t :=
  (physicalOffsetMap b).contDiff.contDiffAt.comp t (covarianceLineLabels_contDiffAt b H hH t hC)

theorem covarianceLineShift_scoreOffsets (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) :
    scoreOffsets b (covarianceLineShift b H t)=(covarianceLineLabels b H t : Fin (n+2) → ℝ) :=
  scoreOffsets_physicalOffsetMap b hG _

/-- Exact Euclidean derivative transfer, with no Pi supremum norm loss. -/
theorem covarianceLineShift_derivative_norm_sq (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) (t : ℝ)
    (hC : (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)∈pdCone) :
    ‖deriv (covarianceLineShift b H) t‖^2=
      ∑ i,(deriv (fun s : ℝ=>(operatorOffsets b (uniformMass n)
        ((ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)+s • H) : Fin (n+2) → ℝ)) 0 i)^2 := by
  have hd := (covarianceLineLabels_contDiffAt b H hH t hC).differentiableAt (by norm_num)
  have hp := ((physicalOffsetMap b).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
  have hr := ((centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
  change deriv (covarianceLineShift b H) t=physicalOffsetMap b (deriv (covarianceLineLabels b H) t) at hp
  change deriv (fun u : ℝ=>(covarianceLineLabels b H u : Fin (n+2) → ℝ)) t=
    ((deriv (covarianceLineLabels b H) t : centeredGauge (Fin (n+2))) : Fin (n+2) → ℝ) at hr
  rw [hp,physicalOffsetMap_norm_sq b hG,←hr]
  have he : (fun s : ℝ=>(operatorOffsets b (uniformMass n)
      ((ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)+s • H) : Fin (n+2) → ℝ))=
      fun s=>(covarianceLineLabels b H (t+s) : Fin (n+2) → ℝ) := by
    funext s
    unfold covarianceLineLabels
    congr 2 <;> module
  rw [he]
  have ht : deriv (fun s : ℝ=>(covarianceLineLabels b H (t+s) : Fin (n+2) → ℝ)) 0=
      deriv (fun u : ℝ=>(covarianceLineLabels b H u : Fin (n+2) → ℝ)) t := by
    simpa only [add_zero] using deriv_comp_const_add
      (fun u : ℝ=>(covarianceLineLabels b H u : Fin (n+2) → ℝ)) t 0
  rw [ht]

end NegativeVotingBalancedCovariancePath
