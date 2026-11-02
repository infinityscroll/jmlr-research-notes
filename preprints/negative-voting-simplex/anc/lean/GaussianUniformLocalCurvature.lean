import GaussianBalancedFacetBootstrap
import GaussianLocalCurvatureAlgebra

/-! Uniform local curvature at the actual balanced regular Gaussian fan.
The selected offsets and the literal facet weights are controlled by the
proved balancing continuation; no analytic curvature or facet hypothesis
is supplied. The radius constant is chosen before dimension and frame. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical RealInnerProductSpace
namespace NegativeVotingUniformLocalCurvature
open NegativeVoting NegativeVotingGaussianMaximum NegativeVotingRegularSecondGap
  NegativeVotingBalancedReference NegativeVotingFan NegativeVotingFanJacobian
  NegativeVotingFanSelectedOffsets NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceOffsets NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingBalancedOffsetPath NegativeVotingBalancedCovariancePath
  NegativeVotingBalancedFacetBootstrap NegativeVotingRegularFacetNeighborhood
  NegativeVotingRegularFacetStability NegativeVotingFacetConditionalPlane
  NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound NegativeVotingRayDeficit
  NegativeVotingLocalCurvatureAlgebra

 theorem balanced_selected_weights_near_identity {n d : ℕ} (hn : 0<n)
    (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,∑ i,inner ℝ (b i) x • b i=x)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈pdCone)
    (hnear : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d))  ≤ 
      facetRadius 64/(1+Real.log ((n:ℝ)+2)))
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (i j : Fin (n+2)) (hij : i≠j) :
    (referenceScale n/((n:ℝ)+2))/2 <
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) (uniformMass n)) i j ∧
    facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) (uniformMass n)) i j <
      2*(referenceScale n/((n:ℝ)+2)) := by
  let H := C-ContinuousLinearMap.id ℝ (FSC.Coord d)
  have hH : H.toLinearMap.IsSymmetric := by
    intro x y
    have hh := hC.1 x y
    change inner ℝ (C x) y=inner ℝ x (C y) at hh
    change inner ℝ ((C-ContinuousLinearMap.id ℝ (FSC.Coord d)) x) y=
      inner ℝ x ((C-ContinuousLinearMap.id ℝ (FSC.Coord d)) y)
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      inner_sub_left,inner_sub_right]
    rw [hh]
  have hline : ContinuousLinearMap.id ℝ (FSC.Coord d)+(1:ℝ) • H=C := by
    dsimp [H]
    module
  have herr : covarianceError R=H := by
    unfold covarianceError NegativeVotingFacetConditionalPlane.covariance
    rw [hRR]
  let z := covarianceLineShift b H 1
  have hz : ‖z‖ ≤ 64*Real.sqrt (1+Real.log ((n:ℝ)+2))*operatorHilbertSchmidt (covarianceError R) := by
    rw [herr]
    simpa only [mul_one] using
      balanced_covariance_shift_bound hn hmean b hG hP H hH hnear 1 (by norm_num)
  have hscores : scoreOffsets b z=
      (selectedOffsets (mappedBasis b R) (uniformMass n) : Fin (n+2) → ℝ) := by
    rw [show scoreOffsets b z=(covarianceLineLabels b H 1 : Fin (n+2) → ℝ) from
      covarianceLineShift_scoreOffsets b hG H 1]
    unfold covarianceLineLabels
    rw [hline,operatorOffsets_eq_selected_factor b C R hR hRR]
    rfl
  have hrows : transportedRows R b=(mappedBasis b R : Fin (n+2) → FSC.Coord d) := rfl
  have hw := regular_facetWeight_neighborhood 64 (by norm_num) hn hmean b hG R hR
    (by simpa only [herr] using hnear) z hz i j hij
  simpa only [hrows,hscores] using hw

 theorem uniform_local_curvature {n d : ℕ} (hn : 0<n) (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑ i,b i=0)
    (hP : ∀ x,∑ i,inner ℝ (b i) x • b i=x)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    LocalGaussianCurvature b (uniformMass n)
      (facetRadius 64/(1+Real.log ((n:ℝ)+2)))
      (referenceScale n/(12*((n:ℝ)+2))) := by
  have hc := facetRadius_bounds 64 (by norm_num)
  have hL : 1 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    linarith
  have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).2 (by norm_num)
  have hc8 : facetRadius 64 ≤ (1:ℝ)/8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hc.1.le,hc.2.2.1]
  have hr : facetRadius 64/(1+Real.log ((n:ℝ)+2)) ≤ (1:ℝ)/8 :=
    (div_le_self hc.1.le hL).trans hc8
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hh := localGaussianCurvature_of_selected_weights b hb hP hG' (uniformMass n)
    (uniformMass_pos n) (uniformMass_sum n)
    (facetRadius 64/(1+Real.log ((n:ℝ)+2))) (referenceScale n) hr (referenceScale_pos n).le
    (by
      intro C hC hnear R hR hRR i j hij
      have hw := (balanced_selected_weights_near_identity hn hmean b hG hP C hC hnear R hR hRR i j hij).1.le
      simpa only [Nat.cast_add,Nat.cast_ofNat,div_div,mul_comm] using hw)
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

/-- One strictly positive absolute radius constant, with the threshold before
ambient dimension, the actual Parseval frame, covariance, and direction. -/
 theorem eventually_uniform_local_curvature :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,∀ (d : ℕ)
      (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑ i,b i=0)
      (hP : ∀ x,∑ i,inner ℝ (b i) x • b i=x)
      (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)),
      LocalGaussianCurvature b (uniformMass n) (c/(1+Real.log ((n:ℝ)+2)))
        (referenceScale n/(12*((n:ℝ)+2))) := by
  refine ⟨facetRadius 64,(facetRadius_bounds 64 (by norm_num)).1,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximum_mean_sq_ge_one] with n hn hsq
  intro d b hb hP hG
  have hmean : 1 ≤ maximumMean n :=
    (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1) (maximumMean_pos n).le).mp (by simpa using hsq)
  exact uniform_local_curvature hn hmean b hb hP hG

end NegativeVotingUniformLocalCurvature
