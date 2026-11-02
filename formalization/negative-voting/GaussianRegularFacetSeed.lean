import GaussianBalancedReference
import GaussianFanCentroidBoundary
import GaussianRegularSecondGap

/-! Exact genuine Gaussian surface weights of a regular fan. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetSeed
open NegativeVotingCenteredParseval NegativeVotingBalancedReference
  NegativeVotingFanCentroid NegativeVotingFanJacobian NegativeVotingFanScore
  NegativeVotingWeightedFacet NegativeVotingFan NegativeVotingCapTail NegativeVotingDisintegration
variable {n d : ℕ}

/-- Pairing the actual centroid-boundary identity with a different regular
score row isolates a single literal Gaussian facet weight. -/
theorem regular_facetWeight (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    facetWeight B 0 i j=referenceScale n/((n:ℝ)+2) := by
  have hG' : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hh := congrArg (fun x : FSC.Coord d=>inner ℝ x (B j))
    (centroid_eq_boundary_laplacian B 0 1 (by norm_num) (centered_singular_one B hG') i)
  have he (k : Fin (n+2)) : inner ℝ (B i-B k) (B j)=(if k=j then -1 else 0) := by
    rw [inner_sub_left,hG,hG]
    by_cases hkj : k=j <;> simp [hij,hkj] <;> ring
  rw [regular_fan_centroid hn B hG i,real_inner_smul_left,hG,if_neg hij] at hh
  simp_rw [sum_inner,real_inner_smul_left,he] at hh
  simp only [mul_ite,mul_neg_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  simp only [div_eq_mul_inv] at hh ⊢
  linarith

/-- At the actual self-centroid regular optimizer every off-diagonal
surface weight is exactly 1/m. -/
theorem scaled_regular_facetWeight (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    facetWeight (fun k=>referenceScale n • B k) 0 i j=1/((n:ℝ)+2) := by
  have ha := referenceScale_pos n
  have hh := congrArg (fun x : FSC.Coord d=>inner ℝ x (B j))
    (centroid_eq_boundary_laplacian (fun k=>referenceScale n • B k) 0
      (referenceScale n) ha (scaled_centered_singular B hG _) i)
  have he (k : Fin (n+2)) :
      inner ℝ (referenceScale n • B i-referenceScale n • B k) (B j)=
        referenceScale n*(if k=j then -1 else 0) := by
    rw [←smul_sub,real_inner_smul_left,inner_sub_left,hG,hG]
    by_cases hkj : k=j <;> simp [hij,hkj] <;> ring
  rw [scaled_regular_self_centroid hn B hG i,real_inner_smul_left,hG,if_neg hij] at hh
  simp_rw [sum_inner,real_inner_smul_left,he] at hh
  simp only [mul_ite,mul_neg_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  have hh' : referenceScale n*facetWeight (fun k=>referenceScale n • B k) 0 i j=
      referenceScale n*(1/((n:ℝ)+2)) := by nlinarith
  exact (mul_left_cancel₀ (ne_of_gt ha)) hh'

theorem regular_edge_norm (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) : ‖B i-B j‖=Real.sqrt 2 := by
  have hi : ‖B i‖^2=1-1/((n:ℝ)+2) := by simpa using hG i i
  have hj : ‖B j‖^2=1-1/((n:ℝ)+2) := by simpa using hG j j
  have hh : ‖B i-B j‖^2=2 := by rw [norm_sub_sq_real,hi,hj,hG,if_neg hij]; ring
  calc
    ‖B i-B j‖=Real.sqrt (‖B i-B j‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _=Real.sqrt 2 := by rw [hh]

/-- The genuine intrinsic Gaussian facet probability, with its exact
normal-density normalization. -/
theorem regular_intrinsicFacet_mass (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B 0 i j)).toReal=
      referenceScale n*Real.sqrt 2/(((n:ℝ)+2)*gaussianPDFReal 0 1 0) := by
  have hh := regular_facetWeight hn B hG i j hij
  unfold facetWeight at hh
  simp only [pairOffset,Pi.zero_apply,sub_self,zero_div,regular_edge_norm B hG i j hij] at hh
  have hφ : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hm : 0 < (n:ℝ)+2 := by positivity
  apply (eq_div_iff (ne_of_gt (mul_pos hm hφ))).mpr
  field_simp [ne_of_gt hφ,ne_of_gt hs,ne_of_gt hm] at hh
  nlinarith

end NegativeVotingRegularFacetSeed
