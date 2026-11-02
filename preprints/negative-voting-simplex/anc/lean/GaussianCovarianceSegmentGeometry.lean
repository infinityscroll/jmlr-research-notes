import GaussianBalancedCovariancePath

/-! Actual positive-definite factors and regular-edge lower bounds on the
complete small covariance segment used by the balancing continuation. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingCovarianceSegmentGeometry
open NegativeVotingCovarianceSegment NegativeVotingPositiveCovariance
  NegativeVotingRegularFacetSeed NegativeVotingFacetConditionalPlane
variable {n d : ℕ}

theorem symmetric_inverse (M : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hM : M.toLinearMap.IsSymmetric) : M.symm.toLinearMap.IsSymmetric := by
  intro x y
  have hh := hM (M.symm x) (M.symm y)
  change inner ℝ (M (M.symm x)) (M.symm y)=inner ℝ (M.symm x) (M (M.symm y)) at hh
  change inner ℝ (M.symm x) y=inner ℝ x (M.symm y)
  simpa only [M.apply_symm_apply] using hh.symm

theorem symmetric_square_positive (M : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hM : M.toLinearMap.IsSymmetric) :
    M.toContinuousLinearMap.comp M.toContinuousLinearMap∈pdCone := by
  refine ⟨?_,?_⟩
  · intro x y
    exact (hM (M x) y).trans (hM x (M y))
  · intro x hx
    have he : M x≠0 := by intro hh; exact hx (M.injective (by simpa only [map_zero] using hh))
    change 0 < inner ℝ x (M (M x))
    have hi := hM x (M x)
    change inner ℝ (M x) (M x)=inner ℝ x (M (M x)) at hi
    rw [←hi,real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr he)

/-- A pointwise actual factor is available everywhere on the full segment,
with the inverse and proximity bounds needed by the response theorem. -/
theorem exists_segment_factor (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hH : H.toLinearMap.IsSymmetric) (hsize : ‖H‖ ≤ 1/8)
    (t : ℝ) (ht : t∈Icc 0 1) :
    ∃ M : FSC.Coord d ≃L[ℝ] FSC.Coord d,
      M.toLinearMap.IsSymmetric ∧ M.symm.toLinearMap.IsSymmetric ∧
      M.toContinuousLinearMap.comp M.toContinuousLinearMap=
        ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H ∧
      ‖M.symm.toContinuousLinearMap‖ ≤ 2 ∧
      ‖M.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 1/4 ∧
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)∈pdCone := by
  obtain ⟨S,V,_,hpsd,hall⟩ := exists_covariance_segment H hH hsize
  have ht' : |t| ≤ 2 := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  obtain ⟨hsq,_,_,hclose,M,hM,hMi,_,_⟩ := hall t ht'
  have hsym : M.toLinearMap.IsSymmetric := by
    intro x y
    have hh := (hpsd t).1 x y
    change inner ℝ (M x) y=inner ℝ x (M y)
    change inner ℝ (S t x) y=inner ℝ x (S t y) at hh
    simpa only [←hM,ContinuousLinearEquiv.coe_coe] using hh
  have hRC : M.toContinuousLinearMap.comp M.toContinuousLinearMap=
      ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H := by rw [hM]; exact hsq
  have hnear : ‖M.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 1/4 := by
    rw [hM]
    linarith
  have hC := symmetric_square_positive M hsym
  rw [hRC] at hC
  exact ⟨M,hsym,symmetric_inverse M hsym,hRC,hMi,hnear,hC⟩

theorem mapped_regular_edge_lower (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hM : ‖M.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 1/4)
    (i j : Fin (n+2)) (hij : i≠j) : 1 ≤ ‖M (B i)-M (B j)‖ := by
  let x := B i-B j
  have hx : ‖x‖=Real.sqrt 2 := regular_edge_norm B hG i j hij
  have hi : M x-(M.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)) x=x := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearEquiv.coe_coe]
    abel
  have ht := norm_sub_le (M x) ((M.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)) x)
  rw [hi] at ht
  have hb := ((M.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg x))
  have hs : (4/3:ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hh : 1 ≤ ‖M x‖ := by rw [hx] at ht hb; nlinarith
  simpa only [x,map_sub] using hh

end NegativeVotingCovarianceSegmentGeometry
