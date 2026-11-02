import GaussianProcrustesDistance
import GaussianCovarianceMixedEstimate
import GaussianFanSelectedOffsets
import NegativeVoting.EdgeEnergy

/-! The quantitative local covariance curvature algebra. Literal facet-weight
lower bounds remain explicit until the separate Gaussian bootstrap supplies them. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingLocalCurvatureAlgebra
open NegativeVoting NegativeVotingProcrustes NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound NegativeVotingPositiveCovariance
  NegativeVotingCovarianceRefinement NegativeVotingCovarianceMixed
  NegativeVotingFanCycleHessian NegativeVotingFanCycleBridge NegativeVotingFan
  NegativeVotingFanCovarianceEnvelope NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceConcavity NegativeVotingCovariancePath
  NegativeVotingFanInverse NegativeVotingAffineBasisLower NegativeVotingFanSelectedOffsets
  NegativeVotingFanJacobian
variable {m d : ℕ} [NeZero m]

theorem frame_edge_energy_lower (b : Fin m → FSC.Coord d)
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    4*(operatorHilbertSchmidt H)^2 ≤
      ∑ i, ∑ j, (inner ℝ (b i-b j) (H (b i-b j)))^2 := by
  have hsym (i j) : inner ℝ (b i) (H (b j))=inner ℝ (b j) (H (b i)) :=
    (hH (b i) (b j)).symm.trans (real_inner_comm _ _)
  have hrow (i) : (∑ j, inner ℝ (b i) (H (b j)))=0 := by
    rw [← inner_sum,← map_sum,hb,map_zero,inner_zero_right]
  have hh := frobenius_energy_le_ordered_edge_energy
    (fun i j => inner ℝ (b i) (H (b j))) hsym hrow
  rw [← scoreGram_HilbertSchmidt_sq b hP H] at hh
  have he (i j) : inner ℝ (b i-b j) (H (b i-b j)) =
      inner ℝ (b i) (H (b i))+inner ℝ (b j) (H (b j))-
        2*inner ℝ (b i) (H (b j)) := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    rw [hsym j i]
    ring
  simpa only [he] using hh

def conjugatedDirection (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) : FSC.Coord d →L[ℝ] FSC.Coord d :=
  R.symm.toContinuousLinearMap.comp (H.comp R.symm.toContinuousLinearMap)

theorem conjugatedDirection_factor (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (x : FSC.Coord d) :
    conjugatedDirection R H (R x)=R.symm (H x) := by
  simp [conjugatedDirection]

theorem factor_inner_conjugated (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (x : FSC.Coord d) : inner ℝ (R x) (conjugatedDirection R H (R x)) =
      inner ℝ x (H x) := by
  rw [conjugatedDirection_factor]
  have hh := hR x (R.symm (H x))
  simpa using hh

theorem mapped_normal_strain (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (i j : Fin m) (hij : i ≠ j) :
    ‖(NegativeVotingFanCycle.faceDirection (mappedBasis b R) {i,j}).starProjection
      (rowsOfOperator (mappedBasis b R) (conjugatedDirection R H) i-
        rowsOfOperator (mappedBasis b R) (conjugatedDirection R H) j)‖^2 =
      (inner ℝ (b i-b j) (H (b i-b j)))^2/‖R (b i-b j)‖^2 := by
  rw [normal_projection_pair_sq _ i j hij]
  change (inner ℝ (‖R (b i)-R (b j)‖⁻¹ • (R (b i)-R (b j)))
    (conjugatedDirection R H (R (b i))-conjugatedDirection R H (R (b j))))^2 = _
  rw [← map_sub (conjugatedDirection R H) (R (b i)) (R (b j)),
    ← map_sub R (b i) (b j),real_inner_smul_left]
  rw [factor_inner_conjugated R hR H]
  simp only [mul_pow,inv_pow,div_eq_mul_inv]
  ring

theorem regular_edge_norm_sq (b : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (i j : Fin m) (hij : i ≠ j) : ‖b i-b j‖^2=2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,hG,ite_true,if_neg hij,if_neg hij.symm]
  ring

theorem near_identity_operator_norm (C : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hC : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/8) :
    ‖C‖ ≤ 9/8 := by
  have he : C=(C-ContinuousLinearMap.id ℝ (FSC.Coord d))+ContinuousLinearMap.id ℝ (FSC.Coord d) := by abel
  have hn := norm_add_le (C-ContinuousLinearMap.id ℝ (FSC.Coord d))
    (ContinuousLinearMap.id ℝ (FSC.Coord d))
  rw [← he] at hn
  have hop := (operator_norm_le_HilbertSchmidt _).trans hC
  have hid : ‖ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith

theorem near_identity_mapped_edge_norm_sq (b : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hC : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/8)
    (i j : Fin m) (hij : i ≠ j) : ‖R (b i-b j)‖^2 ≤ 3 := by
  let x := b i-b j
  have hx : ‖x‖^2=2 := regular_edge_norm_sq b hG i j hij
  have he : ‖R x‖^2=inner ℝ x (C x) := by
    rw [← real_inner_self_eq_norm_sq]
    have hh := hR x (R x)
    change inner ℝ (R x) (R x)=inner ℝ x (R.toContinuousLinearMap.comp R.toContinuousLinearMap x) at hh
    rwa [hRR] at hh
  have hin := real_inner_le_norm x (C x)
  have hop := mul_le_mul_of_nonneg_left (C.le_opNorm x) (norm_nonneg x)
  have hcn := mul_le_mul_of_nonneg_right (near_identity_operator_norm C hC) (sq_nonneg ‖x‖)
  rw [he]
  nlinarith

theorem normal_edge_energy_lower (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (h : Fin m → ℝ) (w0 : ℝ) (hw0 : 0 ≤ w0)
    (hweights : ∀ i j, i ≠ j → w0 ≤ facetWeight (mappedBasis b R) h i j)
    (hedges : ∀ i j, i ≠ j → ‖R (b i-b j)‖^2 ≤ 3) :
    (2*w0/3)*(operatorHilbertSchmidt H)^2 ≤
      normalEdgeEnergy (mappedBasis b R) h (rowsOfOperator (mappedBasis b R) (conjugatedDirection R H)) := by
  have hp (i j : Fin m) : (w0/3)*(inner ℝ (b i-b j) (H (b i-b j)))^2 ≤
      NegativeVotingFanCycle.cycleEdgeWeight (mappedBasis b R) h i j *
      ‖(NegativeVotingFanCycle.faceDirection (mappedBasis b R) {i,j}).starProjection
        (rowsOfOperator (mappedBasis b R) (conjugatedDirection R H) i-
          rowsOfOperator (mappedBasis b R) (conjugatedDirection R H) j)‖^2 := by
    by_cases hij : i=j
    · subst j;simp
    have hvec : R (b i-b j) ≠ 0 := by
      intro hz
      have hh := congrArg R.symm hz
      have he : b i-b j=0 := by simpa using hh
      exact hij (b.ind.injective (sub_eq_zero.mp he))
    have hden : 0 < ‖R (b i-b j)‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hvec)
    have hw : w0 ≤ NegativeVotingFanCycle.cycleEdgeWeight (mappedBasis b R) h i j := by
      rw [cycleEdgeWeight_eq_facetWeight _ _ i j hij]
      exact hweights i j hij
    rw [mapped_normal_strain b R hR H i j hij]
    calc
      _ = w0*((inner ℝ (b i-b j) (H (b i-b j)))^2/3) := by ring
      _ ≤ w0*((inner ℝ (b i-b j) (H (b i-b j)))^2/‖R (b i-b j)‖^2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg _) hden (hedges i j hij)) hw0
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (div_nonneg (sq_nonneg _) hden.le)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))
  simp only [← Finset.mul_sum] at hs
  have he := mul_le_mul_of_nonneg_left (frame_edge_energy_lower b hb hP H hH)
    (div_nonneg hw0 (by norm_num : (0:ℝ) ≤ 3))
  unfold normalEdgeEnergy
  nlinarith

theorem actual_second_derivative_of_weight_bound
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRi : R.symm.toLinearMap.IsSymmetric)
    (C H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hH : H.toLinearMap.IsSymmetric) (h : centeredGauge (Fin m))
    (hm : mass (mappedBasis b R) h=p) (w0 : ℝ) (hw0 : 0 ≤ w0)
    (hweights : ∀ i j, i ≠ j → w0 ≤ facetWeight (mappedBasis b R) h i j)
    (hedges : ∀ i j, i ≠ j → ‖R (b i-b j)‖^2 ≤ 3) :
    deriv (deriv (fun t : ℝ => operatorValue b p (C+t • H))) 0 ≤
      -(w0/6)*(operatorHilbertSchmidt H)^2 := by
  have hsym : (conjugatedDirection R H).toLinearMap.IsSymmetric :=
    symmetric_conjugate _ _ hRi hH
  obtain ⟨h0,hm0,_,hd2,hq⟩ := exists_actual_covariance_derivatives (mappedBasis b R)
    p hp hs (conjugatedDirection R H) hsym
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound (mappedBasis b R)
  have heqoff : h0=h := Subtype.ext (NegativeVotingFanInverse.centered_offsets_unique
    (mappedBasis b R) σ hσ hlower _ _ h0.property h.property (hm0.trans hm.symm))
  subst h0
  have heq : (fun t : ℝ => operatorValue b p (C+t • H)) =
      (fun t : ℝ => covarianceValue (Matrix.gram ℝ (mappedBasis b R)+
        t • gramVelocity (mappedBasis b R) (conjugatedDirection R H)) p) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    congr 1
    have hG := factor_gram b C R hR hRR
    have hV := conjugate_gramVelocity b H R hR
    change Matrix.gram ℝ (mappedBasis b R)=gramVelocity b C at hG
    change gramVelocity (mappedBasis b R) (conjugatedDirection R H)=gramVelocity b H at hV
    rw [hG,hV]
  rw [heq,hd2.deriv]
  have hn := normal_edge_energy_lower b hb hP R hR H hH h w0 hw0 hweights hedges
  nlinarith

theorem actual_second_derivative_of_nearby_weights
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (hG : ∀ i j, inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRi : R.symm.toLinearMap.IsSymmetric)
    (C H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hC : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/8)
    (hH : H.toLinearMap.IsSymmetric) (h : centeredGauge (Fin m))
    (hm : mass (mappedBasis b R) h=p) (a : ℝ) (ha : 0 ≤ a)
    (hweights : ∀ i j, i ≠ j → a/(2*m) ≤ facetWeight (mappedBasis b R) h i j) :
    deriv (deriv (fun t : ℝ => operatorValue b p (C+t • H))) 0 ≤
      -(a/(12*m))*(operatorHilbertSchmidt H)^2 := by
  have hh := actual_second_derivative_of_weight_bound b hb hP p hp hs R hR hRi C H
    hRR hH h hm (a/(2*m)) (div_nonneg ha (by positivity)) hweights
    (near_identity_mapped_edge_norm_sq b hG R hR C hRR hC)
  convert hh using 1 <;> ring

/-- The ray module's exact local Gaussian curvature predicate follows from
literal selected-offset facet bounds. No differentiation or cycle premise remains. -/
theorem localGaussianCurvature_of_selected_weights
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (hG : ∀ i j, inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1)
    (radius a : ℝ) (hradius : radius ≤ 1/8) (ha : 0 ≤ a)
    (hweights : ∀ (C : FSC.Coord d →L[ℝ] FSC.Coord d), C ∈ pdCone →
      operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ radius →
      ∀ (R : FSC.Coord d ≃L[ℝ] FSC.Coord d), R.toLinearMap.IsSymmetric →
        R.toContinuousLinearMap.comp R.toContinuousLinearMap=C →
        ∀ i j, i ≠ j → a/(2*m) ≤ facetWeight (mappedBasis b R)
          (selectedOffsets (mappedBasis b R) p) i j) :
    NegativeVotingRayDeficit.LocalGaussianCurvature b p radius (a/(12*m)) := by
  intro C H hC hnear hH
  obtain ⟨R,hR,hRi,hRR⟩ := exists_positive_factor C hC
  exact actual_second_derivative_of_nearby_weights b hb hP hG p hp hs R hR hRi C H
    hRR (hnear.trans hradius) hH (selectedOffsets (mappedBasis b R) p)
    (selectedOffsets_mass _ (mappedBasis b R).ind.injective p hp hs) a ha
    (hweights C hC hnear R hR hRR)

end NegativeVotingLocalCurvatureAlgebra
