import GaussianCovarianceSegment
import GaussianFanSelectedOffsets
import GaussianRegularFacetNeighborhood

/-! The actual globally selected balanced offset, reconstructed in the physical
regular score space by a continuous linear map, with no dimension loss. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedOffsetPath
open NegativeVotingCovarianceSegment NegativeVotingFanSelectedOffsets NegativeVotingFanInverse
  NegativeVotingFan NegativeVotingFanJointInverse NegativeVotingCapTail
  NegativeVotingCenteredParseval NegativeVotingBalancedReference NegativeVotingFacetConditionalPlane
variable {n d : ℕ}

def physicalOffsetMap (B : Fin (n+2) → FSC.Coord d) :
    centeredGauge (Fin (n+2)) →L[ℝ] FSC.Coord d :=
  ∑ i,((ContinuousLinearMap.proj i : (Fin (n+2) → ℝ) →L[ℝ] ℝ).comp
    (centeredGauge (Fin (n+2))).subtypeL).smulRight (B i)

@[simp] theorem physicalOffsetMap_apply (B : Fin (n+2) → FSC.Coord d)
    (u : centeredGauge (Fin (n+2))) : physicalOffsetMap B u=∑ i,(u : Fin (n+2) → ℝ) i • B i := by
  simp [physicalOffsetMap]

theorem physicalOffsetMap_norm_sq (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (u : centeredGauge (Fin (n+2))) : ‖physicalOffsetMap B u‖^2=∑ i,((u : Fin (n+2) → ℝ) i)^2 := by
  rw [physicalOffsetMap_apply,weighted_norm_sq B (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG)]
  rw [u.property]
  simp

theorem scoreOffsets_physicalOffsetMap (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (u : centeredGauge (Fin (n+2))) : scoreOffsets B (physicalOffsetMap B u)=u := by
  ext i
  rw [scoreOffsets,physicalOffsetMap_apply,real_inner_comm,
    weighted_inner B (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG),u.property]
  simp

def balancedOffset (B : Fin (n+2) → FSC.Coord d)
    (S : FSC.Coord d →L[ℝ] FSC.Coord d) : FSC.Coord d :=
  physicalOffsetMap B (selectedOffsets (fun i=>S (B i)) (uniformMass n))

theorem mapped_regular_lower (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hM : ‖M.symm.toContinuousLinearMap‖ ≤ 2) :
    CenteredSingularLowerBound (fun i=>M (B i)) (1/2) := by
  intro c hc
  have hh := (M.symm.toContinuousLinearMap.le_opNorm (M (∑ i,c i • B i))).trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  simp only [ContinuousLinearEquiv.coe_coe,M.symm_apply_apply] at hh
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*‖M (∑ i,c i • B i)‖)).mpr hh
  rw [weighted_norm_sq B (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG),hc] at hs
  have he : ∑ i,c i • M (B i)=M (∑ i,c i • B i) := by simp only [map_sum,map_smul]
  rw [he]
  norm_num at hs ⊢
  nlinarith

theorem balancedOffset_mass (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) :
    mass (fun i=>M (B i)) (scoreOffsets B (balancedOffset B M.toContinuousLinearMap))=uniformMass n := by
  rw [balancedOffset,scoreOffsets_physicalOffsetMap B hG]
  apply selectedOffsets_mass
  · intro i j he
    by_contra hij
    exact regular_gram_rows_ne B _ hG i j hij (M.injective he)
  · exact uniformMass_pos n
  · exact uniformMass_sum n

theorem balancedOffset_identity (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    balancedOffset B (ContinuousLinearMap.id ℝ (FSC.Coord d))=0 := by
  have hh := selectedOffsets_eq B (uniformMass n) 1 (by norm_num)
    (centered_singular_one B (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG))
    0 (regular_fan_mass B hG)
  change physicalOffsetMap B (selectedOffsets B (uniformMass n))=0
  rw [hh,map_zero]

theorem selectedOffsets_contDiffAt_path (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) (hS : ContDiffAt ℝ 1 S t)
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hM : M.toContinuousLinearMap=S t)
    (hMi : ‖M.symm.toContinuousLinearMap‖ ≤ 2) :
    ContDiffAt ℝ 1 (fun u=>selectedOffsets (fun i=>S u (B i)) (uniformMass n)) t := by
  have hlow : CenteredSingularLowerBound (fun i=>S t (B i)) (1/2) := by
    simpa only [←hM,ContinuousLinearEquiv.coe_coe] using mapped_regular_lower B hG M hMi
  have hj := selectedOffsets_joint_C1 (fun i=>S t (B i)) (1/2) (by norm_num)
    hlow (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
  have hc : ContDiffAt ℝ 1 (fun u : ℝ=>
      ((fun i=>S u (B i)),(0 : centeredGauge (Fin (n+2))))) t := by
    apply ContDiffAt.prodMk
    · apply contDiffAt_pi.mpr
      intro i
      exact hS.clm_apply contDiffAt_const
    · exact contDiffAt_const
  have hh := hj.comp t hc
  simpa only [Function.comp_def,Prod.fst,Prod.snd,Submodule.coe_zero,add_zero] using hh

theorem balancedOffset_contDiffAt_path (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) (hS : ContDiffAt ℝ 1 S t)
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hM : M.toContinuousLinearMap=S t)
    (hMi : ‖M.symm.toContinuousLinearMap‖ ≤ 2) :
    ContDiffAt ℝ 1 (fun u=>balancedOffset B (S u)) t :=
  (physicalOffsetMap B).contDiff.contDiffAt.comp t
    (selectedOffsets_contDiffAt_path B hG S t hS M hM hMi)

theorem balancedOffset_derivative (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) (hS : ContDiffAt ℝ 1 S t)
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hM : M.toContinuousLinearMap=S t)
    (hMi : ‖M.symm.toContinuousLinearMap‖ ≤ 2) :
    deriv (fun u=>balancedOffset B (S u)) t=physicalOffsetMap B
      (deriv (fun u=>selectedOffsets (fun i=>S u (B i)) (uniformMass n)) t) := by
  have hd := (selectedOffsets_contDiffAt_path B hG S t hS M hM hMi).differentiableAt (by norm_num)
  exact ((physicalOffsetMap B).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv

end NegativeVotingBalancedOffsetPath
