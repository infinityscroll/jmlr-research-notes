import GaussianNearRegularGraphGap
import GaussianRegularReferenceNormalization
import GaussianRegularReferenceJumpBound

/-! Actual offset, moment and mass-adjoint estimates with the scaled regular
reference normalized exactly. Every geometric premise is derived from the
same explicit row neighborhood and uniform Gaussian masses. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNearRegularNormalizedBounds
open NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanQuadraticMoments
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularGraphGap
  NegativeVotingRegularReferenceNormalization NegativeVotingReferenceJumpComparison
  NegativeVotingRegularReferenceJumpBound NegativeVotingRegularQuadraticRepresentation
  NegativeVotingSecondChaosMassAdjoint NegativeVotingCapTail NegativeVotingFacetDegree
  NegativeVotingWeightedFacet NegativeVotingDisintegration
  NegativeVotingPolynomialFacetLogBound NegativeVotingBalancedMomentGeometry
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingRegularFacetCancellation
variable {d m : ℕ} [NeZero m]

def offsetCoefficient (m : ℕ) (α e : ℝ) : ℝ :=
  4*degreeBound e*quarticLogConstant 2*(1+Real.log (m:ℝ))^4/nearGap m α e

def momentComparisonCoefficient (m : ℕ) (e : ℝ) : ℝ :=
  16*(degreeBound e)^2*(quarticLogConstant 2)^2*(1+Real.log (m:ℝ))^8

theorem nearGap_inv (α e : ℝ) (hα : 0 < α) (he : 0 < e) :
    (nearGap m α e)⁻¹=512*Real.pi^2*degreeBound e*((m:ℝ)*α)^2 := by
  have hm : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hd := (degreeBound_pos e he).ne'
  unfold nearGap NegativeVotingFanRetained.retainedGapCoefficient
  field_simp
  <;> ring

theorem nearGap_inv_le (α e A : ℝ) (hα : 0 < α) (he : 0 < e) (hA : 0 ≤ A)
    (hm : 1 ≤ m) (hscale : α ≤ A*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)) :
    (nearGap m α e)⁻¹ ≤ 512*Real.pi^2*degreeBound e*A^2*(1+Real.log (m:ℝ)) := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hL : 0 ≤ 1+Real.log (m:ℝ) := by positivity [Real.log_nonneg hmR]
  have hs := (le_div_iff₀ hm0).mp hscale
  have hs2 := pow_le_pow_left₀ (mul_nonneg hα.le hm0.le) hs 2
  simp only [mul_pow,Real.sq_sqrt hL] at hs2
  rw [nearGap_inv α e hα he]
  have hc : 0 ≤ 512*Real.pi^2*degreeBound e := by positivity [degreeBound_pos e he]
  convert mul_le_mul_of_nonneg_left hs2 hc using 1 <;> ring

theorem selected_offset_sq_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : FSC.Coord d) :
    (∑ i,((selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹) : Fin m→ℝ) i)^2) ≤
      offsetCoefficient m α e*∑ i,‖D i-v‖^2 := by
  have hh := near_regular_selected_offset_difference_sq_le hm R D hG α hα hD e he hscale v
  rw [selected_regular_scaled_zero R hG α hα] at hh
  simpa only [Pi.zero_apply,sub_zero,offsetCoefficient] using hh

theorem selected_momentDifference_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : FSC.Coord d) :
    momentDifferenceEnergy (α•R+D) R (selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹)) 0 ≤
      momentComparisonCoefficient m e*∑ i,‖D i-v‖^2 := by
  have hh := near_regular_selected_moment_difference_sq_le hm R D hG α hα hD e he hscale v
  rw [selected_regular_scaled_zero R hG α hα] at hh
  simp only [secondMomentTensor_scaled_zero R α hα] at hh
  exact hh

theorem selected_endpoint_pairOffset
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (i j : Fin m) (hij : i≠j) :
    |pairOffset (α•R+D) (selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹)) i j| ≤
      2*Real.sqrt (1+Real.log (m:ℝ)) := by
  have hlower : CenteredSingularLowerBound (α•R+D) (α/2) := by
    simpa only [one_smul] using (segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩).1
  have hinj : Function.Injective (α•R+D) := fun a b hh=>by
    by_contra hab
    exact centered_singular_rows_ne _ (α/2) (by positivity) hlower a b hab hh
  simpa only [Fintype.card_fin] using pairOffset_le_of_uniform_mass (α•R+D)
    (selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹)) hinj
    (fun a=>by simpa only [Fintype.card_fin] using (congrFun (selected_uniform_mass (α•R+D) hinj) a).ge)
    i j hij

def adjointCoefficient (n : ℕ) (α e : ℝ) : ℝ :=
  (512*degreeBound e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4*
      (momentCoefficient n/α)^2*(1+offsetCoefficient (n+2) α e)+
    8*degreeBound e*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4*
      momentComparisonCoefficient (n+2) e)/nearGap (n+2) α e

/-- All graph, moment, offset, facet-probability and mass premises in the
actual adjoint estimate are discharged. The coefficient is explicit. -/
theorem selected_massAdjoint_sq_le {n : ℕ} (hn : 1 ≤ n)
    (R D : Fin (n+2)→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2) :
    (∑ i,(massAdjoint (α•R+D) (selectedOffsets (α•R+D) (fun _=>((n+2:ℕ):ℝ)⁻¹)) i)^2) ≤
      adjointCoefficient n α e*∑ i,‖D i‖^2 := by
  let B := α•R+D
  let h := (selectedOffsets B (fun _=>((n+2:ℕ):ℝ)⁻¹) : Fin (n+2)→ℝ)
  have hm3 : 3 ≤ n+2 := by omega
  have hlower : CenteredSingularLowerBound B (α/2) := by
    simpa only [one_smul,B] using (segment_geometry hm3 R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩).1
  have hgap := nearGap_pos (m:=n+2) α e hα he
  have hgraph : ∀ v:Fin (n+2)→ℝ,(∑ i,v i)=0 →
      nearGap (n+2) α e*(∑ i,v i^2) ≤ v ⬝ᵥ (NegativeVotingFanJacobian.offsetJacobian B h *ᵥ v) := by
    intro v hv
    simpa only [one_smul,selectedRowOffsets,B,h] using
      selected_segment_graph_gap hm3 R D hG α hα hD e he hscale 1 ⟨by norm_num,le_rfl⟩ v hv
  have hp : ∀ i j:Fin (n+2),i≠j→((n+2:ℕ):ℝ)^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal := by
    intro i j hij
    have ht := selected_segment_probability hm3 R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩ i j hij
    have heq : α•R+(1:ℝ)•D=B := by simp [B]
    dsimp only [selectedRowOffsets] at ht
    rw [heq] at ht
    exact ht
  have hd i := selected_segment_degree_all hm3 R D hG α hα hD e he hscale 1 ⟨by norm_num,le_rfl⟩ i
  simp only [one_smul,selectedRowOffsets] at hd
  have hh := massAdjoint_norm_sq_regular_log_le hn B R hG h α hα.ne'
    (α/2) (by positivity) hlower (nearGap (n+2) α e) hgap hgraph
    2 ((n+2:ℕ):ℝ) (degreeBound e) (by exact_mod_cast (show 1 ≤ n+2 by omega))
    (degreeBound_pos e he).le hp (selected_endpoint_pairOffset hm3 R D hG α hα hD) hd 0 0
  have ho := selected_offset_sq_le hm3 R D hG α hα hD e he hscale 0
  have hq := selected_momentDifference_le hm3 R D hG α hα hD e he hscale 0
  have hrow i : rowError B R α i=D i := by simp [rowError,B]
  simp only [hrow,Pi.zero_apply,sub_zero] at hh ho hq
  refine hh.trans ?_
  have hprod : 0 ≤ 512*degreeBound e*quarticLogConstant 2*
      (1+Real.log ((n+2:ℕ):ℝ))^4*(momentCoefficient n/α)^2 := by
    unfold quarticLogConstant;positivity [degreeBound_pos e he]
  have hprod' : 0 ≤ 8*degreeBound e*quarticLogConstant 2*
      (1+Real.log ((n+2:ℕ):ℝ))^4 := by
    unfold quarticLogConstant;positivity [degreeBound_pos e he]
  have hs : (∑ i,‖D i‖^2)+(∑ i,h i^2) ≤
      (1+offsetCoefficient (n+2) α e)*∑ i,‖D i‖^2 := by
    change (∑ i,h i^2) ≤ offsetCoefficient (n+2) α e*∑ i,‖D i‖^2 at ho
    nlinarith [ho]
  have hq' : momentDifferenceEnergy B R h (fun _=>0) ≤
      momentComparisonCoefficient (n+2) e*∑ i,‖D i‖^2 := hq
  have hb := div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hs hprod)
      (mul_le_mul_of_nonneg_left hq' hprod')) hgap.le
  exact hb.trans_eq (by dsimp only [adjointCoefficient];ring)

end NegativeVotingNearRegularNormalizedBounds
