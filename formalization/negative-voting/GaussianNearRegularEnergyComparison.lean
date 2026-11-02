import GaussianNearRegularNormalizedBounds
import GaussianRegularTransportBound
import GaussianBoundedHessianRemainder
import GaussianBalancedEnergyComparison

/-! Actual finite second-chaos comparison near a scaled regular Gaussian fan.
The coefficient remains explicit; no supplied Hessian, graph, moment, offset,
or facet estimate is an assumption of the final comparison. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNearRegularEnergyComparison
open NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanQuadraticMoments
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularGraphGap
  NegativeVotingNearRegularNormalizedBounds NegativeVotingRegularReferenceNormalization
  NegativeVotingReferenceJumpComparison NegativeVotingRegularQuadraticRepresentation
  NegativeVotingSecondChaosMassAdjoint NegativeVotingCapTail NegativeVotingFacetDegree
  NegativeVotingWeightedFacet NegativeVotingDisintegration
  NegativeVotingPolynomialFacetLogBound NegativeVotingBalancedMomentGeometry
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingRegularFacetCancellation
  NegativeVotingBoundedCoherentLift NegativeVotingBoundedHessianRemainder
  NegativeVotingBalancedOffsetComparison NegativeVotingFanCanonicalOffset
  NegativeVotingMomentResponseBound NegativeVotingBalancedFacetHessian
  NegativeVotingFanScore NegativeVotingFanQuadraticTransport NegativeVotingFanJacobian
  NegativeVotingHessianReferenceRemainder NegativeVotingRegularTransportBound
  NegativeVotingRegularTransportProducts NegativeVotingBalancedEnergyComparison
variable {d n : ℕ}

def traceCoefficient (m : ℕ) (e : ℝ) : ℝ :=
  degreeBound e*quarticLogConstant 2*(1+Real.log (m:ℝ))^4

def energyComparisonCoefficient (n : ℕ) (α e F : ℝ) : ℝ :=
  momentComparisonCoefficient (n+2) e+
    8192*traceCoefficient (n+2) e*|momentCoefficient n/α| *
      (1+Real.sqrt ((1+offsetCoefficient (n+2) α e)*F)/(α/2))*
      (1+offsetCoefficient (n+2) α e)+
    (520*traceCoefficient (n+2) e/(α/2))*
      Real.sqrt ((momentComparisonCoefficient (n+2) e+adjointCoefficient n α e)*F)*
      (1+offsetCoefficient (n+2) α e)

theorem traceCoefficient_nonneg (m : ℕ) (e : ℝ) (he : 0<e) :
    0 ≤ traceCoefficient m e := by
  unfold traceCoefficient quarticLogConstant
  positivity [degreeBound_pos e he]

theorem offsetCoefficient_nonneg (m : ℕ) [NeZero m] (α e : ℝ)
    (hα : 0<α) (he : 0<e) : 0 ≤ offsetCoefficient m α e := by
  unfold offsetCoefficient
  exact div_nonneg (by unfold quarticLogConstant; positivity [degreeBound_pos e he])
    (nearGap_pos α e hα he).le

theorem momentComparisonCoefficient_nonneg (m : ℕ) (e : ℝ) :
    0 ≤ momentComparisonCoefficient m e := by
  unfold momentComparisonCoefficient
  positivity

theorem adjointCoefficient_nonneg (n : ℕ) (α e : ℝ) (hα : 0<α) (he : 0<e) :
    0 ≤ adjointCoefficient n α e := by
  have ho:=offsetCoefficient_nonneg (n+2) α e hα he
  have hm:=momentComparisonCoefficient_nonneg (n+2) e
  unfold adjointCoefficient quarticLogConstant
  positivity [degreeBound_pos e he,nearGap_pos (m:=n+2) α e hα he]

theorem energyComparisonCoefficient_nonneg (n : ℕ) (α e F : ℝ)
    (hα : 0<α) (he : 0<e) : 0 ≤ energyComparisonCoefficient n α e F := by
  have ht:=traceCoefficient_nonneg (n+2) e he
  have ho:=offsetCoefficient_nonneg (n+2) α e hα he
  have hm:=momentComparisonCoefficient_nonneg (n+2) e
  unfold energyComparisonCoefficient
  positivity

def nearRegularLift (hn : 1 ≤ n) (R D : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑i,‖D i‖^2 ≤ α^2/256) :
    (Fin (n+2)→ℝ)→L[ℝ]FSC.Coord d :=
  boundedScoreLift (α•R+D) (α/2) (by positivity)
    (by simpa only [one_smul] using
      (segment_geometry (by omega : 3 ≤ n+2) R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩).1) 0

theorem nearRegularLift_coherent (hn : 1 ≤ n) (R D : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑i,‖D i‖^2 ≤ α^2/256) :
    NegativeVotingCoherentLiftHessian.CoherentLift (α•R+D) (nearRegularLift hn R D hG α hα hD) := by
  unfold nearRegularLift
  exact boundedScoreLift_coherent _ _ _ _ _

/-- Literal balanced Hessian at the selected equal-mass offsets. The tangent
rows are arbitrary; all analytic data are derived from the row neighborhood. -/
theorem selected_endpoint_hessian_abs_le (hn : 1 ≤ n)
    (R D Z : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2)
    (F : ℝ) (hF : ∑i,‖D i‖^2 ≤ F) :
    let B:=α•R+D
    let h:Fin (n+2)→ℝ:=selectedOffsets B (fun _=>((n+2:ℕ):ℝ)⁻¹)
    |balancedFacetHessianValue B h (nearRegularLift hn R D hG α hα hD)
      (massAdjoint B h) (Z,canonicalOffsetVariation B h Z)| ≤ 
      energyComparisonCoefficient n α e F*∑i,‖Z i‖^2 := by
  dsimp only
  let B:=α•R+D
  let h:Fin (n+2)→ℝ:=selectedOffsets B (fun _=>((n+2:ℕ):ℝ)⁻¹)
  let k:=canonicalOffsetVariation B h Z
  let δ:Parameters d (Fin (n+2)):=(Z,k)
  let L:=nearRegularLift hn R D hG α hα hD
  let K:=traceCoefficient (n+2) e
  let O:=offsetCoefficient (n+2) α e
  let M:=momentComparisonCoefficient (n+2) e
  let A:=adjointCoefficient n α e
  let S:=∑i,‖Z i‖^2
  let T:=rowScoreEnergy Z k 0 0
  let E:=rowScoreEnergy (rowError B R α) h 0 0
  have hm3 : 3 ≤ n+2 := by omega
  have hm1 : (1:ℝ) ≤ ((n+2:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ n+2 by omega)
  have hσ : 0<α/2 := by positivity
  have hlower : CenteredSingularLowerBound B (α/2) := by
    simpa only [one_smul,B] using
      (segment_geometry hm3 R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩).1
  have hL:=nearRegularLift_coherent hn R D hG α hα hD
  have hK : 0 ≤ K:=traceCoefficient_nonneg _ e he
  have hO : 0 ≤ O:=offsetCoefficient_nonneg _ α e hα he
  have hM : 0 ≤ M:=momentComparisonCoefficient_nonneg _ e
  have hA : 0 ≤ A:=adjointCoefficient_nonneg _ α e hα he
  have hS : 0 ≤ S:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hF0 : 0 ≤ F:=(Finset.sum_nonneg fun i _=>sq_nonneg ‖D i‖).trans hF
  have hT : 0 ≤ T := by
    unfold T rowScoreEnergy
    exact add_nonneg (Finset.sum_nonneg fun i _=>sq_nonneg _)
      (Finset.sum_nonneg fun i _=>sq_nonneg _)
  have hE : 0 ≤ E := by
    unfold E rowScoreEnergy
    exact add_nonneg (Finset.sum_nonneg fun i _=>sq_nonneg _)
      (Finset.sum_nonneg fun i _=>sq_nonneg _)
  have hp : ∀i j:Fin (n+2),i≠j→((n+2:ℕ):ℝ)^(-4096:ℝ) ≤ 
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal := by
    intro i j hij
    have ht:=selected_segment_probability hm3 R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩ i j hij
    have hb : α•R+(1:ℝ)•D=B:=by simp [B]
    dsimp only [selectedRowOffsets] at ht
    rw [hb] at ht
    exact ht
  have ha:=selected_endpoint_pairOffset hm3 R D hG α hα hD
  have hd i:=selected_segment_degree_all hm3 R D hG α hα hD e he hscale 1 ⟨by norm_num,le_rfl⟩ i
  simp only [one_smul,selectedRowOffsets] at hd
  have hd' i : (∑j∈Finset.univ.erase i,facetWeight B h i j) ≤ degreeBound e := by
    calc
      _ ≤ ∑j,facetWeight B h i j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _=>facetWeight_nonneg _ _ _ _)
      _ ≤ _:=hd i
  have hgraph : ∀v:Fin (n+2)→ℝ,(∑i,v i)=0→
      nearGap (n+2) α e*(∑i,v i^2) ≤ v ⬝ᵥ (NegativeVotingFanJacobian.offsetJacobian B h *ᵥ v) := by
    intro v hv
    simpa only [one_smul,selectedRowOffsets,B,h] using
      selected_segment_graph_gap hm3 R D hG α hα hD e he hscale 1 ⟨by norm_num,le_rfl⟩ v hv
  have hk:=canonicalOffset_norm_sq_log_le B Z h (α/2) hσ hlower
    (nearGap (n+2) α e) (nearGap_pos α e hα he) hgraph
    2 ((n+2:ℕ):ℝ) (degreeBound e) hm1 hp ha hd 0
  simp only [sub_zero] at hk
  have hTbound : T ≤ (1+O)*S := by
    change (∑i,k i^2) ≤ O*S at hk
    simp only [T,rowScoreEnergy,sub_zero]
    dsimp only [S]
    nlinarith only [hk]
  have ho:=selected_offset_sq_le hm3 R D hG α hα hD e he hscale 0
  simp only [sub_zero] at ho
  have hrow i : rowError B R α i=D i := by simp [rowError,B]
  have hEbound : E ≤ (1+O)*F := by
    have he0 : E ≤ (1+O)*∑i,‖D i‖^2 := by
      simp only [E,rowScoreEnergy,hrow,sub_zero]
      change (∑i,h i^2) ≤ O*∑i,‖D i‖^2 at ho
      nlinarith only [ho]
    exact he0.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  have hq:=selected_momentDifference_le hm3 R D hG α hα hD e he hscale 0
  simp only [sub_zero] at hq
  have hc:=selected_massAdjoint_sq_le hn R D hG α hα hD e he hscale
  have hrem : momentDifferenceEnergy B R h 0+(∑i,(massAdjoint B h i)^2) ≤ (M+A)*F := by
    have hh:=add_le_add hq hc
    change momentDifferenceEnergy B R h 0+(∑i,(massAdjoint B h i)^2) ≤ 
      M*(∑i,‖D i‖^2)+A*(∑i,‖D i‖^2) at hh
    rw [←add_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hF (add_nonneg hM hA))
  have hr:=responseEnergy_log_le B h (α/2) hσ hlower δ 2 ((n+2:ℕ):ℝ)
    (degreeBound e) hm1 (degreeBound_pos e he).le hp ha hd'
  have heq:=canonical_edgeScoreEnergy_log_le B Z h (α/2) hσ hlower
    2 ((n+2:ℕ):ℝ) (degreeBound e) hm1 hp ha hd 0
  simp only [sub_zero] at heq
  have hresponse : responseEnergy B h δ ≤ M*S := by
    refine hr.trans ((mul_le_mul_of_nonneg_left heq (by
      unfold quarticLogConstant; positivity [degreeBound_pos e he])).trans_eq ?_)
    dsimp only [M,S,momentComparisonCoefficient]
    ring
  have hv : velocityEnergy (velocityMap L δ).1 (velocityMap L δ).2 ≤ T/(α/2)^2 := by
    exact bounded_velocity_energy_le B (α/2) hσ hlower 0 δ 0 0
  have hreference:=referenceTransport_regular_log_le hn B R hG h α hα.ne'
    (α/2) hσ hlower L hL δ 2 ((n+2:ℕ):ℝ) (degreeBound e)
    hm1 (degreeBound_pos e he).le hp ha hd 0 0 0 0
  have hmix : Real.sqrt (velocityEnergy (velocityMap L δ).1 (velocityMap L δ).2)*
      Real.sqrt E*Real.sqrt T ≤ Real.sqrt ((1+O)*F)/(α/2)*T := by
    have hh:=sqrt_velocity_product_le 1 _ E T (α/2) (by norm_num) hE hT hσ hv
    simp only [one_mul,one_div] at hh
    refine hh.trans ?_
    have hs:=mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hEbound) hσ.le) hT
    convert hs using 1 <;> ring
  have href : |referenceTransport B R h 0 L δ| ≤ 
      8192*K*|momentCoefficient n/α| *(1+Real.sqrt ((1+O)*F)/(α/2))*(1+O)*S := by
    change |referenceTransport B R h 0 L δ| ≤ 
      8192*degreeBound e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4*
        |momentCoefficient n/α| *(T+Real.sqrt (velocityEnergy (velocityMap L δ).1 (velocityMap L δ).2)*
          Real.sqrt E*Real.sqrt T) at hreference
    calc
      _ ≤ 8192*K*|momentCoefficient n/α| *((1+Real.sqrt ((1+O)*F)/(α/2))*T) := by
        refine hreference.trans ?_
        have hb:=mul_le_mul_of_nonneg_left (add_le_add_left hmix T)
          (show 0 ≤ 8192*K*|momentCoefficient n/α| by positivity)
        convert hb using 1 <;> dsimp only [K,traceCoefficient] <;> ring
      _ ≤ 8192*K*|momentCoefficient n/α| *((1+Real.sqrt ((1+O)*F)/(α/2))*((1+O)*S)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTbound (by positivity))
          (by positivity)
      _=_:=by ring
  have hb:=balancedFacetHessianValue_boundedLift_reference_abs_le B R h 0
    (α/2) hσ hlower 0 (massAdjoint B h) δ 2 ((n+2:ℕ):ℝ) (degreeBound e)
    hm1 (degreeBound_pos e he).le hp ha hd 0 0
  have heK : 520*degreeBound e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4=520*K := by
    dsimp only [K,traceCoefficient]
    ring
  dsimp only at hb
  rw [heK] at hb
  change |balancedFacetHessianValue B h L (massAdjoint B h) δ| ≤ 
    responseEnergy B h δ+|referenceTransport B R h 0 L δ|+
      (520*K/(α/2))*Real.sqrt (momentDifferenceEnergy B R h 0+∑i,(massAdjoint B h i)^2)*T at hb
  have hremain : (520*K/(α/2))*Real.sqrt (momentDifferenceEnergy B R h 0+∑i,(massAdjoint B h i)^2)*T ≤ 
      (520*K/(α/2))*Real.sqrt ((M+A)*F)*(1+O)*S := by
    calc
      _ ≤ (520*K/(α/2))*Real.sqrt ((M+A)*F)*T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrem)
          (by positivity)) hT
      _ ≤ (520*K/(α/2))*Real.sqrt ((M+A)*F)*((1+O)*S) :=
        mul_le_mul_of_nonneg_left hTbound (by positivity)
      _=_:=by ring
  refine hb.trans ((add_le_add (add_le_add hresponse href) hremain).trans_eq ?_)
  dsimp only [energyComparisonCoefficient,K,O,M,A,S]
  ring

/-- Squared row energy decreases along the closed unit segment. -/
theorem segment_rowEnergy_le (D : Fin (n+2)→FSC.Coord d) (t : ℝ)
    (ht : t∈Icc (0:ℝ) 1) : (∑i,‖(t • D) i‖^2) ≤ ∑i,‖D i‖^2 := by
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact pow_le_pow_left₀ (mul_nonneg ht.1 (norm_nonneg _))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (D i))) 2

/-- Finite ACTUAL second-energy comparison, in any ambient dimension. There
are no assumed derivatives, trace bounds, moment bounds or offset estimates.
The explicit coefficient may subsequently be bounded by a fixed logarithmic
power under the indicated row/scale regime. -/
theorem near_regular_selected_energy_abs_le (hn : 1 ≤ n)
    (R D : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2) :
    |secondEnergy (α•R+D) (selectedOffsets (α•R+D) (fun _=>((n+2:ℕ):ℝ)⁻¹))-
      secondEnergy R 0| ≤
      energyComparisonCoefficient n α e (∑i,‖D i‖^2)*(∑i,‖D i‖^2) := by
  let L : ℝ→(Fin (n+2)→ℝ)→L[ℝ]FSC.Coord d := fun t=>
    if ht : t∈Icc (0:ℝ) 1 then
      nearRegularLift hn R (t • D) hG α hα ((segment_rowEnergy_le D t ht).trans hD)
    else 0
  have hlower : ∀t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (α•R+t•D) (α/2) := by
    intro t ht
    exact (segment_geometry (by omega : 3 ≤ n+2) R D hG α hα hD t ht).1
  have hL : ∀t∈Icc (0:ℝ) 1,
      NegativeVotingCoherentLiftHessian.CoherentLift (α•R+t•D) (L t) := by
    intro t ht
    dsimp only [L]
    rw [dif_pos ht]
    exact nearRegularLift_coherent hn R (t • D) hG α hα _
  apply selected_regular_energy_abs_le hn R D hG α hα (α/2) (by positivity)
    hlower L hL
  · exact mul_nonneg (energyComparisonCoefficient_nonneg n α e _ hα he)
      (Finset.sum_nonneg fun i _=>sq_nonneg _)
  · intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hDt := (segment_rowEnergy_le D t ht').trans hD
    have hb:=selected_endpoint_hessian_abs_le hn R (t • D) D hG α hα hDt e he hscale
      (∑i,‖D i‖^2) (segment_rowEnergy_le D t ht')
    simpa only [selectedRowOffsets,L,dif_pos ht'] using hb

end NegativeVotingNearRegularEnergyComparison
