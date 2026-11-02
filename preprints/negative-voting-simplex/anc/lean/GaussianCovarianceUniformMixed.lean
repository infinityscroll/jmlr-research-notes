import GaussianCovarianceOptimizerConstants
import GaussianCovarianceOptimizerEdges
import GaussianCovarianceMixedDerivative
import GaussianCovarianceOptimizerDegree

/-! Actual uniform logarithmic mixed-curvature control at covariance optimizers.
All mass, edge, retention, degree and factor inputs are discharged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open Set
open scoped BigOperators Topology RealInnerProductSpace NNReal
namespace NegativeVotingCovarianceUniformMixed
open NegativeVotingOptimizerConstants NegativeVotingCovarianceBoundary
  NegativeVotingCovarianceOptimizer NegativeVotingPositiveCovariance
  NegativeVotingCovarianceOptimizerDegree NegativeVotingCovarianceMixedDerivative
  NegativeVotingFanRetained NegativeVotingFanMassContinuity NegativeVotingCovarianceOffsets
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
variable {m d : ℕ} [NeZero m]

theorem operatorEdgeLength_eq_symmetric_factor_norm
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (C R : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRC : R.comp R=C) (i j : Fin m) :
    operatorEdgeLength b C i j=‖R (b i)-R (b j)‖ := by
  have he : inner ℝ (b i-b j) (C (b i-b j))=‖R (b i-b j)‖^2 := by
    rw [←hRC]
    change inner ℝ (b i-b j) (R (R (b i-b j)))=‖R (b i-b j)‖^2
    have hh := hR (b i-b j) (R (b i-b j))
    change inner ℝ (R (b i-b j)) (R (b i-b j))=inner ℝ (b i-b j) (R (R (b i-b j))) at hh
    rw [←hh,real_inner_self_eq_norm_sq]
  unfold operatorEdgeLength
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),map_sub]

/-- The numerical logarithmic bound also holds at nearby points satisfying
relaxed mass and degree bounds. It assumes the displayed geometry here; the
next theorem derives that geometry for every actual optimizer. -/
theorem offset_derivative_bound_of_relaxed_geometry
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (hm : numericThreshold ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i,0 < p i) (hs : ∑ i,p i=1)
    (C A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : A.toLinearMap.IsSymmetric)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hmass : ∀ i,massLower (m:ℝ) ≤ p i)
    (hlow : ∀ i j,i≠j → edgeLower (m:ℝ) ≤ ‖mappedBasis b R i-mappedBasis b R j‖)
    (hhigh : ∀ i j,i≠j → ‖mappedBasis b R i-mappedBasis b R j‖ ≤ edgeUpper (m:ℝ))
    (hdegree : ∀ i,(∑ j,NegativeVotingFanJacobian.facetWeight (mappedBasis b R)
      (NegativeVotingFanSelectedOffsets.selectedOffsets (mappedBasis b R) p) i j) ≤ 2) :
    (∑ i,(deriv (fun t : ℝ => (operatorOffsets b p (C+t • A) : Fin m → ℝ)) 0 i)^2) ≤
      mixedConstant*(1+Real.log (m:ℝ))^2 *
        (-deriv (deriv (fun t : ℝ => operatorValue b p (C+t • A))) 0) := by
  obtain ⟨hm3,ht,hratio⟩ := numericThreshold_spec m hm
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨hp0,hmin,hmax,hτ⟩ := scalar_positive (m:ℝ) hm0
  have ht' : retention (m:ℝ)*(m:ℝ) ≤ (massLower (m:ℝ)/(2*Real.pi*edgeUpper (m:ℝ)))/2 := by
    convert ht using 1 <;> ring
  have hcontrol := operator_offsets_derivative_control b hm3 p hp hs
    C A hA R hR hRi hRC (massLower (m:ℝ)) (edgeLower (m:ℝ)) (edgeUpper (m:ℝ))
    (retention (m:ℝ)) 2 hp0 hmin hmax hτ (by norm_num) hmass hlow hhigh hdegree ht'
  let G := retainedGapCoefficient (massLower (m:ℝ)) (edgeUpper (m:ℝ)) 2
  let K := retainedCoefficientCeiling (massLower (m:ℝ)) (retention (m:ℝ)) (edgeLower (m:ℝ))
  let Q := -deriv (deriv (fun t : ℝ => operatorValue b p (C+t • A))) 0
  let S := ∑ i,(deriv (fun t : ℝ => (operatorOffsets b p (C+t • A) : Fin m → ℝ)) 0 i)^2
  change G*S ≤ K*Q at hcontrol
  have hGpos : 0 < G := retainedGapCoefficient_pos _ _ _ hp0 hmax (by norm_num)
  have hKpos : 0 < K := by dsimp [K,retainedCoefficientCeiling]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hQ : 0 ≤ Q := nonneg_of_mul_nonneg_right ((mul_nonneg hGpos.le hS).trans hcontrol) hKpos
  change S ≤ mixedConstant*(1+Real.log (m:ℝ))^2*Q
  calc
    S ≤ (K*Q)/G := (le_div_iff₀ hGpos).2 (by simpa only [mul_comm G S] using hcontrol)
    _=(K/G)*Q := by ring
    _≤ mixedConstant*(1+Real.log (m:ℝ))^2*Q := mul_le_mul_of_nonneg_right hratio hQ

/-- One absolute constant and one numerical alphabet threshold suffice. For
any exact centered Parseval reference in dimension at least two, every actual
optimizer at a sufficiently small positive floor has the same logarithmic
mixed bound, uniformly over the whole first mass window. -/
theorem uniform_optimizer_offset_derivative_bound
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (hdim : 2 ≤ d) (hm : numericThreshold ≤ m) :
    ∃ δ : ℝ,0 < δ ∧ ∀ ε : ℝ,0 < ε → ε < δ →
      ∀ p : PositiveMassVector (Fin m),p∈positiveMassBox (actualMassLower (m:ℝ)) (2/(m:ℝ)) →
      ∀ C : FSC.Coord d →L[ℝ] FSC.Coord d,
      C∈lowerCovarianceCone ε → IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C →
      ∀ A : FSC.Coord d →L[ℝ] FSC.Coord d,A.toLinearMap.IsSymmetric →
      (∑ i,(deriv (fun t : ℝ => (operatorOffsets b p (C+t • A) : Fin m → ℝ)) 0 i)^2) ≤
        mixedConstant*(1+Real.log (m:ℝ))^2 *
          (-deriv (deriv (fun t : ℝ => operatorValue b p (C+t • A))) 0) := by
  obtain ⟨hm3,ht,hratio⟩ := numericThreshold_spec m hm
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : 0 < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hpActual : 0 < actualMassLower (m:ℝ) := by unfold actualMassLower; positivity
  obtain ⟨δ,hδ,hgeometry⟩ := uniform_small_floor_edge_bounds b hG hP hdim
    (actualMassLower (m:ℝ)) (m:ℝ) 2 hpActual hm1 (by norm_num)
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ p hp C hC hopt A hA
  have hCpsd : C∈psdCone := lowerCovarianceCone_subset_psd hε.le hC
  let Cpsd : PSDCovariance d := ⟨C,hCpsd⟩
  let εnn : ℝ≥0 := ⟨ε,hε.le⟩
  have hstate : IsOptimizerState b (εnn,(p,Cpsd)) := ⟨hC,hopt⟩
  have hedge := hgeometry εnn hεδ p hp Cpsd hstate
  obtain ⟨R,hR,hRi,hRC,hdegree⟩ := exists_optimizer_factor_degree_le_one b hG p
    p.property.1 p.property.2 ε hε C hC hopt
  have hnorm : ∀ i j,operatorEdgeLength b C i j=‖mappedBasis b R i-mappedBasis b R j‖ := by
    intro i j
    exact operatorEdgeLength_eq_symmetric_factor_norm b C R.toContinuousLinearMap hR hRC i j
  have hminEq : edgeLower (m:ℝ)=Real.sqrt (2*Real.pi)*(actualMassLower (m:ℝ))^2/2 := by
    dsimp [edgeLower,actualMassLower]
    field_simp
    <;> ring
  have hlow : ∀ i j,i≠j → edgeLower (m:ℝ) ≤ ‖mappedBasis b R i-mappedBasis b R j‖ := by
    intro i j hij
    rw [←hnorm,hminEq]
    exact (hedge i j hij).1.le
  have hhigh : ∀ i j,i≠j → ‖mappedBasis b R i-mappedBasis b R j‖ ≤ edgeUpper (m:ℝ) := by
    intro i j hij
    rw [←hnorm]
    exact (hedge i j hij).2.le
  have hmass : ∀ i,massLower (m:ℝ) ≤ (p:Fin m→ℝ) i := by
    intro i
    apply le_trans (b:=actualMassLower (m:ℝ)) ?_ (hp i).1
    unfold massLower actualMassLower
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact offset_derivative_bound_of_relaxed_geometry b hm p p.property.1 p.property.2
    C A hA R hR hRi hRC hmass hlow hhigh (fun i => (hdegree i).trans (by norm_num))

end NegativeVotingCovarianceUniformMixed
