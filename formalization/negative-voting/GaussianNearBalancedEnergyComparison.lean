import GaussianNearBalancedHighTailComparison
import GaussianNearRegularEnergyComparison
import GaussianNearRegularEnergyLogBound

/-! Actual second-chaos energy comparison with both row and mass errors.
The pure mass path uses the literal selected offsets, its Jacobian equation,
and the actual mass adjoint. No desired energy estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingNearBalancedEnergyComparison
open NegativeVotingNearBalancedSourceInputs NegativeVotingNearBalancedHighTailComparison
  NegativeVotingNearRegularEnergyComparison NegativeVotingNearRegularNormalizedBounds
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularGraphGap
  NegativeVotingFan NegativeVotingFanScore NegativeVotingFanSelectedOffsets
  NegativeVotingFanInverse NegativeVotingFanJacobian NegativeVotingFanQuadraticMoments
  NegativeVotingBalancedMomentComparison NegativeVotingBalancedMomentGeometry
  NegativeVotingMomentResponseBound NegativeVotingReferenceJumpComparison
  NegativeVotingRegularReferenceJumpBound NegativeVotingSecondChaosMassAdjoint
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingWeightedFacet
  NegativeVotingDisintegration NegativeVotingPolynomialFacetLogBound
  NegativeVotingRegularQuadraticRepresentation NegativeVotingFanMovingCells
  NegativeVotingFanHessian NegativeVotingRegularFacetCancellation
  NegativeVotingNearRegularEnergyLogBound NegativeVotingRegularCoefficientBound
variable {d m : ℕ} [NeZero m]

/-- The finite tensor derivative along a genuine varying-mass selected path. -/
theorem mass_momentVector_hasDerivAt
    (B : Fin m → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (p : Fin m → ℝ) (v : centeredGauge (Fin m)) (hp : ∑ i,p i=1)
    (t : ℝ) (hpos : ∀ i,0 < massLine p v t i) :
    HasDerivAt (fun s : ℝ => momentVector B (offsetLine B p v s))
      (responseVector B (offsetLine B p v t)
        (0,((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ))) t := by
  have hc:=offsetLine_C1 B σ hσ hlower p v hp t hpos
  have hd:HasDerivAt (offsetLine B p v) (deriv (offsetLine B p v) t) t :=
    (hc.differentiableAt (by norm_num)).hasDerivAt
  have hs:HasDerivAt (fun s : ℝ => (offsetLine B p v s : Fin m → ℝ))
      ((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ) t :=
    (centeredGauge (Fin m)).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
  have hh:=HasDerivAt.fun_sum (u:=Finset.univ)
    (fun q : Fin m × Fin d × Fin d => fun _ =>
      ((hasFDerivAt_secondMomentTensor B (offsetLine B p v t) σ hσ hlower
        q.1 q.2.1 q.2.2).comp_hasDerivAt t ((hasDerivAt_const t B).prodMk hs)).smul_const
          (EuclideanSpace.basisFun (Fin m × Fin d × Fin d) ℝ q))
  convert! hh using 1

def massMomentCoefficient (m : ℕ) (α e : ℝ) : ℝ :=
  4*massDegree e*quarticLogConstant 2*(1+Real.log (m:ℝ))^4*(massGap m α e)⁻¹

theorem massMomentCoefficient_nonneg (α e : ℝ) (hα : 0 < α) (he : 0 < e) :
    0 ≤ massMomentCoefficient m α e := by
  unfold massMomentCoefficient quarticLogConstant
  positivity [massDegree_pos e he,massGap_pos (m:=m) α e hα he]

/-- Dimension-free tensor-norm control of the actual pure mass change. -/
theorem near_mass_momentDifference_le (hm : 3 ≤ m) (R D : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : centeredGauge (Fin m)) (hv : ∀ i,|(v : Fin m → ℝ) i| ≤ 1/(2*(m:ℝ))) :
    momentDifferenceEnergy (α•R+D) (α•R+D)
      (selectedOffsets (α•R+D) ((fun _ => (m:ℝ)⁻¹)+(v : Fin m → ℝ)))
      (selectedOffsets (α•R+D) (fun _ => (m:ℝ)⁻¹)) ≤
        massMomentCoefficient m α e*∑ i,((v : Fin m → ℝ) i)^2 := by
  let B:=α•R+D
  let p : Fin m → ℝ:=fun _ => (m:ℝ)⁻¹
  let f:=fun t : ℝ => momentVector B (offsetLine B p v t)
  let f':=fun t : ℝ => responseVector B (offsetLine B p v t)
    (0,((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ))
  let C:=massMomentCoefficient m α e*∑ i,((v : Fin m → ℝ) i)^2
  have hC:0 ≤ C:=mul_nonneg (massMomentCoefficient_nonneg α e hα he)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hm0:(0:ℝ) < m:=Nat.cast_pos.mpr (NeZero.pos m)
  have hm1:(1:ℝ) ≤ m:=by exact_mod_cast (show 1 ≤ m by omega)
  have hp:∑ i,p i=1:=by simp [p,NeZero.ne m]
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hinj:Function.Injective B:=fun i j heq => by
    by_contra hij
    exact centered_singular_rows_ne B (α/2) (by positivity) hg.1 i j hij heq
  have hpos t (ht : t ∈ Icc (0:ℝ) 1) : ∀ i,0 < massLine p v t i:=fun i =>
    lt_of_lt_of_le (by positivity) (uniform_massLine_box v hv t ht i).1
  have hd t (ht : t ∈ Icc (0:ℝ) 1) : HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t:=
    (mass_momentVector_hasDerivAt B (α/2) (by positivity) hg.1 p v hp t (hpos t ht)).hasDerivWithinAt
  have hb t (ht : t ∈ Ico (0:ℝ) 1) : ‖f' t‖ ≤ Real.sqrt C:=by
    have htc:t ∈ Icc (0:ℝ) 1:=⟨ht.1,ht.2.le⟩
    have hbox:=uniform_massLine_box v hv t htc
    have hdeg i:=near_mass_degree hm R D hG α hα hD e he hscale
      (massLine p v t) (hpos t htc) (massLine_sum p v hp t) (fun i => (hbox i).2) i
    have hprob:=near_mass_probability hm R D hG α hα hD
      (massLine p v t) (hpos t htc) (massLine_sum p v hp t) (fun i => (hbox i).1)
    have hoff:=near_mass_pairOffset hm R D hG α hα hD
      (massLine p v t) (hpos t htc) (massLine_sum p v hp t) (fun i => (hbox i).1)
    have hJ:=offsetLine_jacobian_response B (α/2) (by positivity) hg.1 p v hp t (hpos t htc)
    have hgap:=near_mass_gap hm R D hG α hα hD e he hscale
      (massLine p v t) (hpos t htc) (massLine_sum p v hp t)
      (fun i => (hbox i).1) (fun i => (hbox i).2)
      (deriv (offsetLine B p v) t : centeredGauge (Fin m)) (deriv (offsetLine B p v) t).property
    have hpair:=inverse_pairing_le B (offsetLine B p v t)
      (deriv (offsetLine B p v) t : centeredGauge (Fin m)) v (massGap m α e)
      (massGap_pos α e hα he) hgap hJ
    have henergy:quadraticForm B (offsetLine B p v t) (0 : Fin m → FSC.Coord d)
        ((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ) ≤
        (massGap m α e)⁻¹*∑ i,((v : Fin m → ℝ) i)^2:=by
      rw [quadraticForm_offsets,hJ]
      exact hpair
    have hh:=responseEnergy_log_le B (offsetLine B p v t) (α/2) (by positivity) hg.1
      (0,((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ))
      2 (m:ℝ) (massDegree e) hm1 (massDegree_pos e he).le hprob hoff hdeg
    rw [edgeScoreEnergy_eq_twice_quadraticForm _ _ _ _ hinj] at hh
    have hcoef:0 ≤ 2*massDegree e*quarticLogConstant 2*(1+Real.log (m:ℝ))^4:=by
      unfold quarticLogConstant;positivity [massDegree_pos e he]
    have hsq:‖f' t‖^2 ≤ C:=by
      rw [responseVector_norm_sq]
      exact hh.trans ((mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left henergy (show (0:ℝ) ≤ 2 by norm_num)) hcoef).trans_eq
          (by dsimp only [C,massMomentCoefficient];ring))
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt hC];exact hsq)
  have hb':=norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  have hsq:=pow_le_pow_left₀ (norm_nonneg (f 1-f 0)) hb' 2
  rw [Real.sq_sqrt hC] at hsq
  dsimp only [f] at hsq
  rw [momentVector_difference_norm_sq] at hsq
  simpa only [momentDifferenceEnergy,offsetLine,massLine,zero_smul,one_smul,add_zero,p,B,C] using hsq


def totalMomentCoefficient (m : ℕ) (α e : ℝ) : ℝ :=
  2*(momentComparisonCoefficient m e+massMomentCoefficient m α e)

def totalOffsetCoefficient (m : ℕ) (α e : ℝ) : ℝ :=
  2*(offsetCoefficient m α e+((massGap m α e)⁻¹)^2)

theorem near_balanced_momentDifference_le (hm : 3 ≤ m) (R D : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : centeredGauge (Fin m)) (hv : ∀ i,|(v : Fin m → ℝ) i| ≤ 1/(2*(m:ℝ))) :
    momentDifferenceEnergy (α•R+D) R
      (selectedOffsets (α•R+D) ((fun _ => (m:ℝ)⁻¹)+(v : Fin m → ℝ))) 0 ≤
      totalMomentCoefficient m α e*((∑ i,‖D i‖^2)+(∑ i,((v : Fin m → ℝ) i)^2)) := by
  let B:=α•R+D
  let h:Fin m → ℝ:=selectedOffsets B ((fun _ => (m:ℝ)⁻¹)+(v : Fin m → ℝ))
  let h₀:Fin m → ℝ:=selectedOffsets B (fun _ => (m:ℝ)⁻¹)
  have hr:=selected_momentDifference_le hm R D hG α hα hD e he hscale 0
  simp only [sub_zero] at hr
  have hvary:=near_mass_momentDifference_le hm R D hG α hα hD e he hscale v hv
  have htri:momentDifferenceEnergy B R h 0 ≤
      2*momentDifferenceEnergy B B h h₀+2*momentDifferenceEnergy B R h₀ 0:=by
    unfold momentDifferenceEnergy
    simp_rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum;intro i _
    apply Finset.sum_le_sum;intro j _
    apply Finset.sum_le_sum;intro k _
    nlinarith [sq_nonneg (secondMomentTensor B h i j k-2*secondMomentTensor B h₀ i j k+
      secondMomentTensor R 0 i j k)]
  have hF:0 ≤ ∑ i,‖D i‖^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hZ:0 ≤ ∑ i,((v : Fin m → ℝ) i)^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM:=momentComparisonCoefficient_nonneg m e
  have hT:=massMomentCoefficient_nonneg (m:=m) α e hα he
  change momentDifferenceEnergy B R h 0 ≤ _
  have hmid:=htri.trans (add_le_add (mul_le_mul_of_nonneg_left hvary (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)))
  refine hmid.trans ?_
  unfold totalMomentCoefficient
  nlinarith [mul_nonneg hM hZ,mul_nonneg hT hF]

theorem near_balanced_offset_le (hm : 3 ≤ m) (R D : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : centeredGauge (Fin m)) (hv : ∀ i,|(v : Fin m → ℝ) i| ≤ 1/(2*(m:ℝ))) :
    (∑ i,((selectedOffsets (α•R+D) ((fun _ => (m:ℝ)⁻¹)+(v : Fin m → ℝ)) : Fin m → ℝ) i)^2) ≤
      totalOffsetCoefficient m α e*((∑ i,‖D i‖^2)+(∑ i,((v : Fin m → ℝ) i)^2)) := by
  have hh:=near_balanced_selected_offset_sq_le hm R D hG α hα hD e he hscale v hv
  have hO:=offsetCoefficient_nonneg m α e hα he
  have hF:0 ≤ ∑ i,‖D i‖^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hZ:0 ≤ ∑ i,((v : Fin m → ℝ) i)^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  refine hh.trans ?_
  unfold totalOffsetCoefficient
  nlinarith [mul_nonneg hO hZ,mul_nonneg (sq_nonneg ((massGap m α e)⁻¹)) hF]

def massAdjointCoefficient (n : ℕ) (α e : ℝ) : ℝ :=
  (512*massDegree e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4*
      (momentCoefficient n/α)^2*(1+totalOffsetCoefficient (n+2) α e)+
    8*massDegree e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4*
      totalMomentCoefficient (n+2) α e)/massGap (n+2) α e

theorem massAdjointCoefficient_nonneg (n : ℕ) (α e : ℝ) (hα : 0 < α) (he : 0 < e) :
    0 ≤ massAdjointCoefficient n α e := by
  have hO:=offsetCoefficient_nonneg (n+2) α e hα he
  have hM:=momentComparisonCoefficient_nonneg (n+2) e
  have hT:=massMomentCoefficient_nonneg (m:=n+2) α e hα he
  unfold massAdjointCoefficient totalOffsetCoefficient totalMomentCoefficient quarticLogConstant
  positivity [massDegree_pos e he,massGap_pos (m:=n+2) α e hα he]

/-- The actual mass adjoint is controlled at every near-balanced mass vector. -/
theorem near_balanced_massAdjoint_sq_le {n : ℕ} (hn : 1 ≤ n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2)
    (v : centeredGauge (Fin (n+2)))
    (hv : ∀ i,|(v : Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ))) :
    (∑ i,(massAdjoint (α•R+D)
      (selectedOffsets (α•R+D) ((fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ))) i)^2) ≤
      massAdjointCoefficient n α e*((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2)) := by
  let B:=α•R+D
  let p:Fin (n+2) → ℝ:=(fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ)
  let h:Fin (n+2) → ℝ:=selectedOffsets B p
  have hm:3 ≤ n+2:=by omega
  have hm0:(0:ℝ) < (n+2:ℕ):=by positivity
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hbox:∀ i,1/(2*((n+2:ℕ):ℝ)) ≤ p i ∧ p i ≤ 2/((n+2:ℕ):ℝ):=by
    simpa only [massLine,one_smul,p] using uniform_massLine_box v hv 1 ⟨by norm_num,le_rfl⟩
  have hp:∀ i,0 < p i:=fun i => lt_of_lt_of_le (by positivity) (hbox i).1
  have hs:∑ i,p i=1:=by
    have hv0:∑ i,(v : Fin (n+2) → ℝ) i=0:=v.property
    simp only [p,Pi.add_apply,Finset.sum_add_distrib,hv0,add_zero,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ hm0.ne'
  have hdeg i:(∑ j,facetWeight B h i j) ≤ massDegree e:=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),facetWeight_self,add_zero]
    exact near_mass_degree hm R D hG α hα hD e he hscale p hp hs (fun i => (hbox i).2) i
  have hh:=massAdjoint_norm_sq_regular_log_le hn B R hG h α hα.ne'
    (α/2) (by positivity) hg.1 (massGap (n+2) α e) (massGap_pos α e hα he)
    (near_mass_gap hm R D hG α hα hD e he hscale p hp hs (fun i => (hbox i).1) (fun i => (hbox i).2))
    2 ((n+2:ℕ):ℝ) (massDegree e) (by exact_mod_cast (show 1 ≤ n+2 by omega)) (massDegree_pos e he).le
    (near_mass_probability hm R D hG α hα hD p hp hs (fun i => (hbox i).1))
    (near_mass_pairOffset hm R D hG α hα hD p hp hs (fun i => (hbox i).1)) hdeg 0 0
  have ho:=near_balanced_offset_le hm R D hG α hα hD e he hscale v hv
  have hq:=near_balanced_momentDifference_le hm R D hG α hα hD e he hscale v hv
  have hrow i:rowError B R α i=D i:=by simp [rowError,B]
  simp only [hrow,sub_zero] at hh
  have hF:0 ≤ ∑ i,‖D i‖^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hZ:0 ≤ ∑ i,((v : Fin (n+2) → ℝ) i)^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum:(∑ i,‖D i‖^2)+(∑ i,h i^2) ≤
      (1+totalOffsetCoefficient (n+2) α e)*((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2)):=by
    change (∑ i,h i^2) ≤ _ at ho
    linarith
  have hcoef:0 ≤ 512*massDegree e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4*
      (momentCoefficient n/α)^2:=by unfold quarticLogConstant;positivity [massDegree_pos e he]
  have hcoef':0 ≤ 8*massDegree e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4:=by
    unfold quarticLogConstant;positivity [massDegree_pos e he]
  refine hh.trans ?_
  have hb:=div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hsum hcoef) (mul_le_mul_of_nonneg_left hq hcoef'))
    (massGap_pos (m:=n+2) α e hα he).le
  exact hb.trans_eq (by dsimp only [massAdjointCoefficient];ring)


/-- The actual energy derivative along the mass path pairs the actual adjoint
with the prescribed mass velocity. -/
theorem mass_secondEnergy_hasDerivAt
    (B : Fin m → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (p : Fin m → ℝ) (v : centeredGauge (Fin m)) (hp : ∑ i,p i=1)
    (t : ℝ) (hpos : ∀ i,0 < massLine p v t i) :
    HasDerivAt (fun s : ℝ => secondEnergy B (offsetLine B p v s))
      (∑ i,massAdjoint B (offsetLine B p v t) i*(v : Fin m → ℝ) i) t := by
  have hc:=offsetLine_C1 B σ hσ hlower p v hp t hpos
  have hd:HasDerivAt (offsetLine B p v) (deriv (offsetLine B p v) t) t :=
    (hc.differentiableAt (by norm_num)).hasDerivAt
  have hs:HasDerivAt (fun s : ℝ => (offsetLine B p v s : Fin m → ℝ))
      ((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ) t :=
    (centeredGauge (Fin m)).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
  have hh:=(hasFDerivAt_secondEnergy B (offsetLine B p v t) σ hσ hlower).comp_hasDerivAt t
    ((hasDerivAt_const t B).prodMk hs)
  have ha:=adjoint_pairing B (offsetLine B p v t) σ hσ hlower
    ((deriv (offsetLine B p v) t : centeredGauge (Fin m)) : Fin m → ℝ)
  rw [jointMassDerivative_offset B (offsetLine B p v t) σ hσ hlower,
    offsetLine_jacobian_response B σ hσ hlower p v hp t hpos] at ha
  simpa only [Function.comp_def,←ha] using hh

/-- The pure mass contribution is quadratic in the joint row/mass error.
The first-order cancellation at the regular uniform reference is retained
through the actual mass-adjoint bound. -/
theorem near_mass_energy_abs_le {n : ℕ} (hn : 1 ≤ n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2)
    (v : centeredGauge (Fin (n+2)))
    (hv : ∀ i,|(v : Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ))) :
    |secondEnergy (α•R+D)
      (selectedOffsets (α•R+D) ((fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ)))-
      secondEnergy (α•R+D) (selectedOffsets (α•R+D) (fun _ => ((n+2:ℕ):ℝ)⁻¹))| ≤
      (1+massAdjointCoefficient n α e)*((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2)) := by
  let B:=α•R+D
  let p:Fin (n+2) → ℝ:=fun _ => ((n+2:ℕ):ℝ)⁻¹
  let f:=fun t : ℝ => secondEnergy B (offsetLine B p v t)
  let f':=fun t : ℝ => ∑ i,massAdjoint B (offsetLine B p v t) i*(v : Fin (n+2) → ℝ) i
  let F:=∑ i,‖D i‖^2
  let Z:=∑ i,((v : Fin (n+2) → ℝ) i)^2
  let C:=massAdjointCoefficient n α e
  have hF:0 ≤ F:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hZ:0 ≤ Z:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hC:0 ≤ C:=massAdjointCoefficient_nonneg n α e hα he
  have hm:3 ≤ n+2:=by omega
  have hm0:(0:ℝ) < (n+2:ℕ):=by positivity
  have hp:∑ i,p i=1:=by
    simp only [p,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ hm0.ne'
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hd t (ht : t ∈ Icc (0:ℝ) 1) : HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t:=by
    have hpos:∀ i,0 < massLine p v t i:=fun i =>
      lt_of_lt_of_le (by positivity) (uniform_massLine_box v hv t ht i).1
    exact (mass_secondEnergy_hasDerivAt B (α/2) (by positivity) hg.1 p v hp t hpos).hasDerivWithinAt
  have hb t (ht : t ∈ Ico (0:ℝ) 1) : ‖f' t‖ ≤ (1+C)*(F+Z):=by
    have htc:t ∈ Icc (0:ℝ) 1:=⟨ht.1,ht.2.le⟩
    have hbnd:=scaled_mass_error_bounds v hv t htc
    have ha:=near_balanced_massAdjoint_sq_le hn R D hG α hα hD e he hscale (t•v) hbnd.1
    have ha':(∑ i,(massAdjoint B (offsetLine B p v t) i)^2) ≤ C*(F+Z):=by
      have ha'':(∑ i,(massAdjoint B (offsetLine B p v t) i)^2) ≤
          C*(F+(∑ i,(((t•v : centeredGauge (Fin (n+2))) : Fin (n+2) → ℝ) i)^2)):=by
        simpa only [C,F,B,offsetLine,massLine,p,Submodule.coe_smul] using ha
      exact ha''.trans (mul_le_mul_of_nonneg_left (by dsimp only [Z];linarith [hbnd.2]) hC)
    have hcs:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => massAdjoint B (offsetLine B p v t) i) (v : Fin (n+2) → ℝ)
    have hs:(f' t)^2 ≤ C*(F+Z)*Z:=hcs.trans (mul_le_mul_of_nonneg_right ha' hZ)
    have hZZ:Z ≤ F+Z:=by linarith
    have hs':(f' t)^2 ≤ C*(F+Z)^2:=hs.trans
      (by nlinarith [mul_le_mul_of_nonneg_left hZZ (mul_nonneg hC (add_nonneg hF hZ))])
    have hright:0 ≤ (1+C)*(F+Z):=by positivity
    have hCC:C ≤ (1+C)^2:=by nlinarith [sq_nonneg C]
    have hs'':(f' t)^2 ≤ ((1+C)*(F+Z))^2:=hs'.trans
      (by nlinarith [mul_le_mul_of_nonneg_right hCC (sq_nonneg (F+Z))])
    rw [Real.norm_eq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hright).mp (by simpa only [sq_abs] using hs'')
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa only [f,offsetLine,massLine,one_smul,zero_smul,add_zero,B,p,F,Z,C,Real.norm_eq_abs] using hh

/-- Actual second-chaos energy comparison for the full near-balanced fan.
All selected-offset, facet, graph, tensor and adjoint estimates are derived. -/
theorem near_balanced_selected_energy_abs_le {n : ℕ} (hn : 1 ≤ n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2)
    (v : centeredGauge (Fin (n+2)))
    (hv : ∀ i,|(v : Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ))) :
    |secondEnergy (α•R+D)
      (selectedOffsets (α•R+D) ((fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ)))-
      secondEnergy R 0| ≤
      energyComparisonCoefficient n α e (∑ i,‖D i‖^2)*(∑ i,‖D i‖^2)+
      (1+massAdjointCoefficient n α e)*((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2)) := by
  have hm:=near_mass_energy_abs_le hn R D hG α hα hD e he hscale v hv
  have hr:=near_regular_selected_energy_abs_le hn R D hG α hα hD e he hscale
  exact (abs_sub_le _ (secondEnergy (α•R+D)
    (selectedOffsets (α•R+D) (fun _ => ((n+2:ℕ):ℝ)⁻¹))) _).trans
      (by linarith)


def massTraceBase (e : ℝ) : ℝ:=massDegree e*quarticLogConstant 2
def massInverseBase (e H : ℝ) : ℝ:=2048*Real.pi^2*massDegree e*H^2
def massMomentBase (e H : ℝ) : ℝ:=4*massTraceBase e*massInverseBase e H
def totalMomentBase (e H : ℝ) : ℝ:=2*(momentBase e+massMomentBase e H)
def totalOffsetBase (e H : ℝ) : ℝ:=2*(offsetBase e H+(massInverseBase e H)^2)
def massAdjointBase (e H : ℝ) : ℝ:=
  (512*massTraceBase e*(ratioBase e)^2*(1+totalOffsetBase e H)+
    8*massTraceBase e*totalMomentBase e H)*massInverseBase e H

def fullEnergyLogConstant (e H B : ℝ) : ℝ:=energyLogConstant e H B+1+massAdjointBase e H

theorem mass_bases_nonneg (e H : ℝ) (he : 0 < e) :
    0 ≤ massTraceBase e ∧ 0 ≤ massInverseBase e H ∧ 0 ≤ massMomentBase e H ∧
      0 ≤ totalMomentBase e H ∧ 0 ≤ totalOffsetBase e H ∧ 0 ≤ massAdjointBase e H := by
  have hb:=base_nonneg e H 0 he le_rfl
  have hO:=hb.2.2.1
  have hM:=hb.2.2.2.1
  have hU:=hb.2.2.2.2.1
  dsimp only [massTraceBase,massInverseBase,massMomentBase,totalMomentBase,totalOffsetBase,massAdjointBase,
    quarticLogConstant]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> positivity [massDegree_pos e he]

/-- The inverse graph scale and regular moment scale cancel exactly; the
remaining mass-adjoint coefficient costs only a fixed logarithmic power. -/
theorem massAdjointCoefficient_log_le (n : ℕ) (hn : 1 ≤ n)
    (α e H : ℝ) (hα : 0 < α) (he : 0 < e) (hH : 0 ≤ H)
    (hlower : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2)
    (hupper : α ≤ H*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ))
    (hγ : |momentCoefficient n| ≤ 30*(1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)) :
    massAdjointCoefficient n α e ≤ massAdjointBase e H*(1+Real.log ((n+2:ℕ):ℝ))^13 := by
  let m:ℝ:=(n+2:ℕ)
  let L:=1+Real.log m
  have hm:(1:ℝ) ≤ m:=by dsimp [m];exact_mod_cast (show 1 ≤ n+2 by omega)
  have hm0:0 < m:=lt_of_lt_of_le zero_lt_one hm
  have hL:1 ≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hL0:0 ≤ L:=by linarith
  have hs:1 ≤ Real.sqrt L:=(Real.le_sqrt (by norm_num) hL0).mpr (by simpa using hL)
  have hsmall:e/m ≤ α:=by
    have hh:e/m ≤ e*Real.sqrt L/m:=div_le_div_of_nonneg_right (by nlinarith) hm0.le
    linarith
  have hu:|momentCoefficient n/α| ≤ ratioBase e*L:=by
    rw [abs_div,abs_of_pos hα]
    calc
      _ ≤ (30*L/m)/α:=div_le_div_of_nonneg_right hγ hα.le
      _ ≤ (30*L/m)/(e/m):=div_le_div_of_nonneg_left (by positivity) (div_pos he hm0) hsmall
      _ = ratioBase e*L:=by dsimp [ratioBase];field_simp
  have hγsq:(momentCoefficient n/α)^2 ≤ (ratioBase e*L)^2:=by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu 2
  obtain ⟨hT,hI,hM,hTM,hTO,hA⟩:=mass_bases_nonneg e H he
  have ho0:0 ≤ offsetBase e H:=(base_nonneg e H 0 he le_rfl).2.2.1
  have hm0':0 ≤ momentBase e:=(base_nonneg e H 0 he le_rfl).2.2.2.1
  have hratio:0 ≤ ratioBase e:=(base_nonneg e H 0 he le_rfl).2.2.2.2.1
  have hgap:(massGap (n+2) α e)⁻¹ ≤ massInverseBase e H*L:=
    massGap_inv_le α e H hα he hH (by omega) hupper
  have hgap0:0 ≤ (massGap (n+2) α e)⁻¹:=(inv_pos.mpr (massGap_pos α e hα he)).le
  have hnear:(nearGap (n+2) α e)⁻¹ ≤ gapBase e H*L:=
    nearGap_inv_le α e H hα he hH (by omega) hupper
  have htrace0:0 ≤ traceBase e:=(base_nonneg e H 0 he le_rfl).1
  have hO:offsetCoefficient (n+2) α e ≤ offsetBase e H*L^5:=by
    calc
      _ = (4*traceBase e*L^4)*(nearGap (n+2) α e)⁻¹:=by
        dsimp [offsetCoefficient,traceBase,L,m];ring
      _ ≤ (4*traceBase e*L^4)*(gapBase e H*L):=mul_le_mul_of_nonneg_left hnear (by positivity)
      _ = offsetBase e H*L^5:=by dsimp [offsetBase];ring
  have hMM:massMomentCoefficient (n+2) α e ≤ massMomentBase e H*L^5:=by
    calc
      _ = (4*massTraceBase e*L^4)*(massGap (n+2) α e)⁻¹:=by
        dsimp [massMomentCoefficient,massTraceBase,L,m];ring
      _ ≤ (4*massTraceBase e*L^4)*(massInverseBase e H*L):=mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = massMomentBase e H*L^5:=by dsimp [massMomentBase];ring
  have htotM:totalMomentCoefficient (n+2) α e ≤ totalMomentBase e H*L^8:=by
    have hMexact:momentComparisonCoefficient (n+2) e=momentBase e*L^8:=by
      dsimp [momentComparisonCoefficient,momentBase,traceBase,L,m];ring
    have hMM':massMomentCoefficient (n+2) α e ≤ massMomentBase e H*L^8:=hMM.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 5 ≤ 8 by omega)) hM)
    dsimp only [totalMomentCoefficient,totalMomentBase]
    rw [hMexact]
    nlinarith only [hMM']
  have htotO:totalOffsetCoefficient (n+2) α e ≤ totalOffsetBase e H*L^5:=by
    have hgapsq:=pow_le_pow_left₀ hgap0 hgap 2
    have hgap':((massGap (n+2) α e)⁻¹)^2 ≤ (massInverseBase e H)^2*L^5:=by
      calc
        _ ≤ (massInverseBase e H*L)^2:=hgapsq
        _ = (massInverseBase e H)^2*L^2:=by ring
        _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 2 ≤ 5 by omega)) (sq_nonneg _)
    dsimp only [totalOffsetCoefficient,totalOffsetBase]
    nlinarith only [hO,hgap']
  have hone:1+totalOffsetCoefficient (n+2) α e ≤ (1+totalOffsetBase e H)*L^5:=
    one_add_bound hL hTO htotO
  have htotalO0:0 ≤ totalOffsetCoefficient (n+2) α e:=by
    unfold totalOffsetCoefficient
    positivity [offsetCoefficient_nonneg (n+2) α e hα he]
  calc
    _ = (512*(massTraceBase e*L^4)*(momentCoefficient n/α)^2*
          (1+totalOffsetCoefficient (n+2) α e)+
        8*(massTraceBase e*L^4)*totalMomentCoefficient (n+2) α e)*(massGap (n+2) α e)⁻¹:=by
      dsimp [massAdjointCoefficient,massTraceBase,L,m];ring
    _ ≤ (512*(massTraceBase e*L^4)*(ratioBase e*L)^2*((1+totalOffsetBase e H)*L^5)+
        8*(massTraceBase e*L^4)*(totalMomentBase e H*L^8))*(massInverseBase e H*L):=by
      gcongr
    _ = (512*massTraceBase e*(ratioBase e)^2*(1+totalOffsetBase e H)*massInverseBase e H)*L^12+
        (8*massTraceBase e*totalMomentBase e H*massInverseBase e H)*L^13:=by ring
    _ ≤ (512*massTraceBase e*(ratioBase e)^2*(1+totalOffsetBase e H)*massInverseBase e H)*L^13+
        (8*massTraceBase e*totalMomentBase e H*massInverseBase e H)*L^13:=by
      have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 12 ≤ 13 by omega))
        (show 0 ≤ 512*massTraceBase e*(ratioBase e)^2*(1+totalOffsetBase e H)*massInverseBase e H by positivity)
      linarith only [hh]
    _ = massAdjointBase e H*L^13:=by dsimp [massAdjointBase];ring

/-- One scalar threshold precedes every ambient dimension, row family,
regular scale and near-balanced mass vector. -/
theorem exists_dimension_uniform_energy_log_le :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n → ∀ d : ℕ,∀ R D : Fin (n+2) → FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ)) →
      ∀ α e H B : ℝ,0 < α → 0 < e → 0 ≤ H → 0 ≤ B →
      (∑ i,‖D i‖^2) ≤ α^2/256 →
      e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2 →
      α ≤ H*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) →
      (∑ i,‖D i‖^2) ≤ B^2/((n+2:ℕ):ℝ)^2 →
      ∀ v : centeredGauge (Fin (n+2)),
      (∀ i,|(v : Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ))) →
      |secondEnergy (α•R+D)
        (selectedOffsets (α•R+D) ((fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ)))-
        secondEnergy R 0| ≤
        fullEnergyLogConstant e H B*(1+Real.log ((n+2:ℕ):ℝ))^16*
          ((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2)) := by
  obtain ⟨N,hN⟩:=eventually_atTop.mp eventually_momentCoefficient_log_bound
  refine ⟨N+1,?_⟩
  intro n hn d R D hG α e H B hα he hH hB hD hlower hupper hsize v hv
  have hn1:1 ≤ n:=by omega
  have hγ:|momentCoefficient n| ≤ 30*(1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hN n (by omega)
  have hF:0 ≤ ∑ i,‖D i‖^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hZ:0 ≤ ∑ i,((v : Fin (n+2) → ℝ) i)^2:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hrow:=coefficient_log_le_of_moment_bound n hn1 α e H B _ hα he hH hB hF hlower hupper hsize hγ
  have hmass:=massAdjointCoefficient_log_le n hn1 α e H hα he hH hlower hupper hγ
  have hh:=near_balanced_selected_energy_abs_le hn1 R D hG α hα hD e he hlower v hv
  let L:=1+Real.log ((n+2:ℕ):ℝ)
  have hL:1 ≤ L:=by
    dsimp [L]
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (n+2:ℕ) by exact_mod_cast (show 1 ≤ n+2 by omega))]
  have hA:0 ≤ massAdjointBase e H:=(mass_bases_nonneg e H he).2.2.2.2.2
  have hE:0 ≤ energyLogConstant e H B:=(base_nonneg e H B he hB).2.2.2.2.2.2
  have hmass':1+massAdjointCoefficient n α e ≤ (1+massAdjointBase e H)*L^16:=by
    have hpow:1 ≤ L^16:=one_le_pow₀ hL
    have hh':massAdjointBase e H*L^13 ≤ massAdjointBase e H*L^16:=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 13 ≤ 16 by omega)) hA
    linarith
  refine hh.trans ?_
  have h1:=mul_le_mul_of_nonneg_right hrow hF
  have h2:=mul_le_mul_of_nonneg_right hmass' (add_nonneg hF hZ)
  have h3:=mul_nonneg (mul_nonneg hE (pow_nonneg (le_trans zero_le_one hL) 16)) hZ
  dsimp only [fullEnergyLogConstant]
  nlinarith only [h1,h2,h3]

end NegativeVotingNearBalancedEnergyComparison
