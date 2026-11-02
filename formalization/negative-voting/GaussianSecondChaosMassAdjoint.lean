import GaussianFanQuadraticMoments
import GaussianFanJacobianPseudoInverse

/-! The actual second-chaos mass-Laplacian adjoint. Its right-hand side is
the derived derivative of the literal Gaussian second chaos; compatibility
with the constant kernel is proved from actual offset translation invariance.
No selected-offset acceleration or second differentiability is assumed. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped RealInnerProductSpace BigOperators ENNReal Topology Classical
namespace NegativeVotingSecondChaosMassAdjoint
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanQuadraticMoments
  NegativeVotingFanJacobian NegativeVotingFanPseudoInverse NegativeVotingFanInverse
  NegativeVotingFanJointMass NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

 def offsetCoefficients (L : Parameters d ι →L[ℝ] ℝ) (i : ι) : ℝ :=
   L (0,Pi.single i 1)

 theorem apply_offset_as_sum (L : Parameters d ι →L[ℝ] ℝ) (k : ι→ℝ) :
    L (0,k)=∑ i,offsetCoefficients L i*k i := by
  have he : (0,k)=(∑ i,k i • ((0,Pi.single i 1) : Parameters d ι)) := by
    ext <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [offsetCoefficients,smul_eq_mul,mul_comm]

 theorem winningCell_add_constant (B : ι→FSC.Coord d) (h : ι→ℝ) (t : ℝ) (i : ι) :
    winningCell B (fun j=>h j+t) i=winningCell B h i := by
  ext x
  simp only [winningCell,Set.mem_setOf_eq,scores]
  apply forall_congr'
  intro j
  constructor <;> intro hh <;> linarith

 theorem secondEnergy_add_constant (B : ι→FSC.Coord d) (h : ι→ℝ) (t : ℝ) :
    secondEnergy B (fun j=>h j+t)=secondEnergy B h := by
  simp only [secondEnergy,secondMomentTensor,winningCell_add_constant]

 def massGradient (B : ι→FSC.Coord d) (h : ι→ℝ) : ι→ℝ :=
   offsetCoefficients (secondEnergyDerivative B h)

 theorem massGradient_sum_zero (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ∑ i,massGradient B h i=0 := by
  have hp : HasDerivAt (fun t : ℝ => (B,fun i=>h i+t))
      ((0,fun _=>1) : Parameters d ι) 0 :=
    (hasDerivAt_const (0:ℝ) B).prodMk
      (hasDerivAt_pi.mpr (fun i=>(hasDerivAt_id (0:ℝ)).const_add (h i)))
  have hd : HasDerivAt (fun t : ℝ => secondEnergy B (fun i=>h i+t))
      (secondEnergyDerivative B h (0,fun _=>1)) 0 := by
    have hD : HasFDerivAt (fun p : Parameters d ι => secondEnergy p.1 p.2)
        (secondEnergyDerivative B h) (B,fun i=>h i+(0:ℝ)) := by
      simpa only [add_zero] using hasFDerivAt_secondEnergy B h σ hσ hlower
    exact hD.comp_hasDerivAt 0 hp
  have hc : HasDerivAt (fun t : ℝ => secondEnergy B (fun i=>h i+t)) 0 0 := by
    simpa only [secondEnergy_add_constant] using hasDerivAt_const (0:ℝ) (secondEnergy B h)
  have hz := hd.unique hc
  rw [apply_offset_as_sum] at hz
  simpa only [mul_one,massGradient] using hz

 theorem jointMassDerivative_offset (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (k : ι→ℝ) :
    jointMassDerivative B h (0,k)=offsetJacobian B h *ᵥ k := by
  have hp : HasFDerivAt (fun v : ι→ℝ => (B,v))
      (ContinuousLinearMap.inr ℝ (ι→FSC.Coord d) (ι→ℝ)) h :=
    (hasFDerivAt_const B h).prodMk (hasFDerivAt_id h)
  have he := ((hasFDerivAt_mass_joint B h σ hσ hlower).comp h hp).unique
    (hasFDerivAt_mass_vector B σ hσ hlower h)
  have hea := congrArg (fun L : (ι→ℝ)→L[ℝ](ι→ℝ) => L k) he
  ext i
  have hi := congrFun hea i
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.pi_apply,massDerivative_eq_offsetJacobian B σ hσ hlower h] using hi

 def massAdjoint (B : ι→FSC.Coord d) (h : ι→ℝ) : ι→ℝ :=
   (offsetJacobian B h).covariancePseudoInverse *ᵥ massGradient B h

 theorem massAdjoint_centered (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ∑ i,massAdjoint B h i=0 :=
   pseudoinverse_sum_mulVec B (affineIndependent_of_centered_lower B σ hσ hlower) h _

 theorem massAdjoint_equation (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    offsetJacobian B h *ᵥ massAdjoint B h=massGradient B h := by
  unfold massAdjoint
  rw [Matrix.mulVec_mulVec,offsetJacobian_pseudoinverse_mulVec B
    (affineIndependent_of_centered_lower B σ hσ hlower)]
  ext i
  change massGradient B h i-(∑ j,massGradient B h j)/(Fintype.card ι:ℝ)=massGradient B h i
  rw [massGradient_sum_zero B h σ hσ hlower,zero_div,sub_zero]

 theorem adjoint_pairing (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (k : ι→ℝ) :
    (∑ i,massAdjoint B h i*(jointMassDerivative B h (0,k)) i)=
      secondEnergyDerivative B h (0,k) := by
  rw [jointMassDerivative_offset B h σ hσ hlower,apply_offset_as_sum]
  have hsym (i j : ι) : offsetJacobian B h i j=offsetJacobian B h j i := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M i j) (offsetJacobian_isHermitian B h).eq
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh.symm
  calc
    _ = ∑ j,(offsetJacobian B h *ᵥ massAdjoint B h) j*k j := by
      simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hsym i j]
      ring
    _ = _ := by rw [massAdjoint_equation B h σ hσ hlower]; rfl

 def correctedDerivative (B : ι→FSC.Coord d) (h : ι→ℝ) : Parameters d ι →L[ℝ] ℝ :=
   secondEnergyDerivative B h-
     (∑ i,massAdjoint B h i • (ContinuousLinearMap.proj i)).comp (jointMassDerivative B h)

 theorem correctedDerivative_apply (B : ι→FSC.Coord d) (h : ι→ℝ) (v : Parameters d ι) :
    correctedDerivative B h v=secondEnergyDerivative B h v-
      ∑ i,massAdjoint B h i*(jointMassDerivative B h v) i := by
  simp only [correctedDerivative,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul]

/-- The literal coefficient of every offset acceleration vanishes after
subtracting the derived mass adjoint. No acceleration exists as a premise. -/
 theorem correctedDerivative_annihilates_offsets (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (k : ι→ℝ) :
    correctedDerivative B h (0,k)=0 := by
  rw [correctedDerivative_apply,adjoint_pairing B h σ hσ hlower,sub_self]

 theorem correctedDerivative_depends_only_rows (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    correctedDerivative B h (D,k)=correctedDerivative B h (D,0) := by
  have he : ((D,k) : Parameters d ι)=(D,0)+(0,k) := by simp
  rw [he,map_add,correctedDerivative_annihilates_offsets B h σ hσ hlower,add_zero]

/-- Actual balanced first variation, with the offset response eliminated by
the real Gaussian mass derivative rather than a supplied Schur identity. -/
 theorem secondEnergyDerivative_of_balanced_velocity (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (hbalance : jointMassDerivative B h (D,k)=0) :
    secondEnergyDerivative B h (D,k)=correctedDerivative B h (D,0) := by
  rw [←correctedDerivative_depends_only_rows B D h k σ hσ hlower,correctedDerivative_apply,hbalance]
  simp

end NegativeVotingSecondChaosMassAdjoint
