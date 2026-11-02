import GaussianCovarianceSegmentGeometry
import GaussianBalancedOffsetEstimate

/-! Actual balanced-offset continuation on the entire covariance segment.
The boundary derivative estimate is derived from the actual Gaussian fan. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedFacetBootstrap
open NegativeVotingCovarianceSegmentGeometry NegativeVotingBalancedCovariancePath
  NegativeVotingBalancedOffsetPath NegativeVotingBalancedOffsetEstimate
  NegativeVotingRegularFacetNeighborhood NegativeVotingFacetConditionalPlane
  NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl NegativeVotingRayDeficit
  NegativeVotingBalancedReference NegativeVotingFanJacobian NegativeVotingFanSelectedOffsets
  NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingFanInverse NegativeVotingCovarianceOffsets
variable {n d : ℕ}

/-- The actual selected physical offset remains in the strict improvement
neighborhood throughout the covariance segment; no response/weight estimate
is supplied as a hypothesis. -/
theorem balanced_covariance_shift_bound
    (hn : 0 < n) (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (hsmall : operatorHilbertSchmidt H ≤ facetRadius 64/(1+Real.log ((n:ℝ)+2))) :
    ∀ t∈Icc (0:ℝ) 1,‖covarianceLineShift b H t‖ ≤
      64*Real.sqrt (1+Real.log ((n:ℝ)+2))*operatorHilbertSchmidt H*t := by
  let L := 1+Real.log ((n:ℝ)+2)
  let ε := operatorHilbertSchmidt H
  let f := covarianceLineShift b H
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    dsimp only [L]
    linarith
  have hLp : 0 < L := by linarith
  have hε : 0 ≤ ε := operatorHilbertSchmidt_nonneg H
  have hop : ‖H‖ ≤ ε := operator_norm_le_HilbertSchmidt H
  have hc := facetRadius_bounds 64 (by norm_num)
  have hεL : ε*L ≤ facetRadius 64 := (le_div_iff₀ hLp).mp hsmall
  have hεc : ε ≤ facetRadius 64 := by
    have hh := mul_le_mul_of_nonneg_left hL hε
    nlinarith
  have hsize : ‖H‖ ≤ 1/8 := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hh := mul_le_mul_of_nonneg_right he hc.1.le
    nlinarith [hc.2.2.1]
  have hC (t : ℝ) (ht : t∈Icc 0 1) :
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H)∈pdCone := by
    obtain ⟨M,_,_,_,_,_,hpd⟩ := exists_segment_factor H hH hsize t ht
    exact hpd
  have hd (t : ℝ) (ht : t∈Icc 0 1) : DifferentiableAt ℝ f t :=
    (covarianceLineShift_contDiffAt b H hH t (hC t ht)).differentiableAt (by norm_num)
  have hf0 : f 0=0 := covarianceLineShift_zero b hG H
  by_cases hz : ε=0
  · have hHz : H=0 := norm_eq_zero.mp (by rw [hz] at hop; exact le_antisymm hop (norm_nonneg H))
    intro t ht
    have heq : f t=f 0 := by
      dsimp only [f,covarianceLineShift,covarianceLineLabels]
      congr 2
      rw [hHz]
      module
    change ‖f t‖ ≤ 64*Real.sqrt L*ε*t
    rw [heq,hf0,norm_zero,hz,mul_zero,zero_mul]
  have hεp : 0 < ε := lt_of_le_of_ne hε (Ne.symm hz)
  have hcont : ContinuousOn f (Icc 0 1) := fun t ht=>(hd t ht).continuousAt.continuousWithinAt
  have hbound (t : ℝ) (ht : t∈Ico 0 1)
      (hboundary : ‖f t‖=64*Real.sqrt L*ε*t) :
      ‖deriv f t‖ < 64*Real.sqrt L*ε := by
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    obtain ⟨M,hM,hMi,hRC,hN,hnear,hpd⟩ := exists_segment_factor H hH hsize t ht'
    have herr : covarianceError M=t • H := by
      unfold covarianceError covariance
      rw [hRC]
      module
    have heps : operatorHilbertSchmidt (covarianceError M)=t*ε := by
      rw [herr,operatorHilbertSchmidt_smul,abs_of_nonneg ht.1]
    have hsmallt : operatorHilbertSchmidt (covarianceError M) ≤ facetRadius 64/L := by
      rw [heps]
      exact (mul_le_of_le_one_left hε ht.2.le).trans hsmall
    have hshift : ‖f t‖ ≤ 64*Real.sqrt L*operatorHilbertSchmidt (covarianceError M) := by
      rw [heps,hboundary]
      apply le_of_eq
      ring
    have hscores : scoreOffsets b (f t)=
        (selectedOffsets (mappedBasis b M) (uniformMass n) : Fin (n+2) → ℝ) := by
      change scoreOffsets b (covarianceLineShift b H t)=_
      rw [covarianceLineShift_scoreOffsets b hG]
      unfold covarianceLineLabels
      rw [operatorOffsets_eq_selected_factor b _ M hM hRC]
      rfl
    have hrows : transportedRows M (b : Fin (n+2) → FSC.Coord d)=mappedBasis b M := rfl
    have hweights (i j : Fin (n+2)) (hij : i≠j) :=
      regular_facetWeight_neighborhood 64 (by norm_num) hn hmean b hG M hM
        hsmallt (f t) hshift i j hij
    have hlow (i j : Fin (n+2)) (hij : i≠j) : (referenceScale n/((n:ℝ)+2))/2 ≤
        facetWeight (mappedBasis b M) (selectedOffsets (mappedBasis b M) (uniformMass n)) i j := by
      have hh := (hweights i j hij).1.le
      simpa only [hrows,hscores] using hh
    have hupp (i j : Fin (n+2)) (hij : i≠j) :
        facetWeight (mappedBasis b M) (selectedOffsets (mappedBasis b M) (uniformMass n)) i j ≤
          2*(referenceScale n/((n:ℝ)+2)) := by
      have hh := (hweights i j hij).2.le
      simpa only [hrows,hscores] using hh
    have hedge (i j : Fin (n+2)) (hij : i≠j) : 1 ≤ ‖mappedBasis b M i-mappedBasis b M j‖ :=
      mapped_regular_edge_lower b hG M hnear i j hij
    have hr := balanced_operator_offset_l2_bound n d b hP hmean
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H) H hH M hM hMi hRC hN hlow hupp hedge
    have heq := covarianceLineShift_derivative_norm_sq b hG H hH t hpd
    rw [←heq,Real.sqrt_sq (norm_nonneg _)] at hr
    change ‖deriv f t‖ ≤ 32*Real.sqrt L*ε at hr
    have hp : 0 < Real.sqrt L*ε := mul_pos (Real.sqrt_pos.mpr hLp) hεp
    nlinarith
  have hf := image_norm_le_of_norm_deriv_right_lt_deriv_boundary
    (f':=deriv f) hcont
    (fun t ht=>(hd t ⟨ht.1,ht.2.le⟩).hasDerivAt.hasDerivWithinAt)
    (B:=fun t : ℝ=>64*Real.sqrt L*ε*t) (B':=fun _ : ℝ=>64*Real.sqrt L*ε)
    (show ‖f 0‖ ≤ 64*Real.sqrt L*ε*0 by rw [hf0]; simp)
    (fun t=>by simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul (64*Real.sqrt L*ε))
    hbound
  exact fun t ht=>hf ht

end NegativeVotingBalancedFacetBootstrap
