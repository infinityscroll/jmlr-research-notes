import GaussianNearRegularBalancedGeometry
import GaussianBalancedOffsetComparison
import GaussianFanRetainedGap

/-! Actual Gaussian graph gap and finite selected-offset bound throughout
the explicit regular score neighborhood. No spectral-gap premise remains. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNearRegularGraphGap
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingFanSelectedOffsets NegativeVotingFanRetained
  NegativeVotingFiniteGraph NegativeVotingNearRegularBalancedGeometry
  NegativeVotingBalancedMomentGeometry NegativeVotingBalancedOffsetComparison
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingPolynomialFacetLogBound
  NegativeVotingWeightedFacet
variable {d m : ℕ} [NeZero m]

def degreeBound (e : ℝ) : ℝ := 32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e

def nearGap (m : ℕ) (α e : ℝ) : ℝ :=
  retainedGapCoefficient (m:ℝ)⁻¹ (2*α) (degreeBound e)

theorem degreeBound_pos (e : ℝ) (he : 0 < e) : 0 < degreeBound e := by
  unfold degreeBound
  positivity

theorem nearGap_pos (α e : ℝ) (hα : 0 < α) (he : 0 < e) : 0 < nearGap m α e :=
  retainedGapCoefficient_pos _ _ _ (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos m))) (by positivity) (degreeBound_pos e he)

theorem selected_segment_degree_all (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (i : Fin m) :
    (∑ j,facetWeight (α•R+t•D)
      (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) i j) ≤ degreeBound e := by
  have hh := selected_segment_degree hm R D hG α hα hD e he hscale t ht i
  rwa [←Finset.sum_erase_add _ _ (Finset.mem_univ i),facetWeight_self,add_zero]

theorem selected_segment_graph_gap (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (v : Fin m→ℝ) (hv : ∑ i,v i=0) :
    nearGap m α e*(∑ i,(v i)^2) ≤ v ⬝ᵥ
      (offsetJacobian (α•R+t•D) (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) *ᵥ v) := by
  let B := α•R+t•D
  let h := selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t
  have hg := segment_geometry hm R D hG α hα hD t ht
  have hinj : Function.Injective B := fun i j heq=>by
    by_contra hij
    exact centered_singular_rows_ne B (α/2) (by positivity) hg.1 i j hij heq
  have hmasses : ∀ i,(m:ℝ)⁻¹ ≤ mass B h i := by
    intro i
    have hh := congrFun (selected_uniform_mass B hinj) i
    simpa only [Fintype.card_fin,selectedRowOffsets,B,h] using hh.ge
  have hh := gaussian_retained_rayleigh B h hinj (m:ℝ)⁻¹ (2*α) 0 (degreeBound e)
    (by positivity) (by positivity) (by norm_num) (degreeBound_pos e he) hmasses
    (fun i j _=>hg.2.2.2.2 i j)
    (selected_segment_degree_all hm R D hG α hα hD e he hscale t ht)
    (by simp only [zero_mul];positivity) v hv
  rw [offsetJacobian_energy]
  simpa only [nearGap,retainedWeight,ite_eq_left (facetWeight_nonneg B h _ _)] using hh

/-- The finite offset error has only the displayed Gaussian graph coefficient;
the graph gap, masses, offsets, facet probabilities and degrees are all derived. -/
theorem near_regular_selected_offset_difference_sq_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : FSC.Coord d) :
    (∑ i,((selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹) : Fin m→ℝ) i-
      (selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹) : Fin m→ℝ) i)^2) ≤
      4*degreeBound e*quarticLogConstant 2*(1+Real.log (m:ℝ))^4/nearGap m α e*
        ∑ i,‖D i-v‖^2 := by
  have hlower t (ht : t∈Icc (0:ℝ) 1) := (segment_geometry hm R D hG α hα hD t ht).1
  apply selected_offset_difference_sq_le (α•R) D (α/2) (by positivity) hlower
    (fun _=>(m:ℝ)⁻¹) (fun _=>by positivity)
    (by simp [NeZero.ne m]) (nearGap m α e) (nearGap_pos α e hα he)
    (fun t ht=>selected_segment_graph_gap hm R D hG α hα hD e he hscale t ⟨ht.1,ht.2.le⟩)
    2 m (degreeBound e) (by exact_mod_cast (show 1 ≤ m by omega)) (degreeBound_pos e he).le
    (fun t ht=>selected_segment_probability hm R D hG α hα hD t ⟨ht.1,ht.2.le⟩)
    ?_ (fun t ht=>selected_segment_degree_all hm R D hG α hα hD e he hscale t ⟨ht.1,ht.2.le⟩) v
  intro t ht i j hij
  let B := α•R+t•D
  have hinj : Function.Injective B := fun a b heq=>by
    by_contra hab
    exact centered_singular_rows_ne B (α/2) (by positivity)
      (hlower t ⟨ht.1,ht.2.le⟩) a b hab heq
  have hh := pairOffset_le_of_uniform_mass B (selectedOffsets B (fun _=>(m:ℝ)⁻¹)) hinj
    (fun a=>by simpa only [Fintype.card_fin] using (congrFun (selected_uniform_mass B hinj) a).ge)
    i j hij
  simpa only [Fintype.card_fin,selectedRowOffsets,B] using hh

end NegativeVotingNearRegularGraphGap
