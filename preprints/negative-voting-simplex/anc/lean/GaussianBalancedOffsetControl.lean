import GaussianFacetMeanBound
import GaussianFanCycleHessian
import GaussianCovarianceMixedDerivative
import GaussianProcrustesDistance
import GaussianFiniteGraphRayleigh

/-! Literal Euclidean offset-response bounds from actual Gaussian surface
geometry. All response equations and conditional moments are proved inputs. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingBalancedOffset
open NegativeVotingFan NegativeVotingFacetMean NegativeVotingFanCycle NegativeVotingFanCycleHessian
  NegativeVotingFanCycleBridge NegativeVotingFanHessian NegativeVotingFanCanonicalOffset
  NegativeVotingFanJacobian NegativeVotingFanScore NegativeVotingFanCovarianceEnvelope
  NegativeVotingFanSelectedOffsets NegativeVotingCovarianceOffsetResponse
  NegativeVotingCovarianceMixedDerivative NegativeVotingCovarianceOffsets
  NegativeVotingCovarianceConcavity NegativeVotingPositiveCovariance
  NegativeVotingAffineBasisLower NegativeVotingProcrustes NegativeVotingFiniteGraphRayleigh
  NegativeVotingAffineNormControl NegativeVotingAffineLogMassBound
  NegativeVotingFanCovarianceValue
variable {m d:ℕ} [NeZero m]

/-- A deliberately slack complete-pair bound, uniform in the dimension. -/
theorem pair_norm_energy_bound (D:Fin m→FSC.Coord d):
    (∑i,∑j,‖D i-D j‖^2)≤4*(m:ℝ)*(∑i,‖D i‖^2):=by
  have hp (i j:Fin m):‖D i-D j‖^2≤2*‖D i‖^2+2*‖D j‖^2:=by
    have h:=norm_sub_le (D i) (D j)
    have hsq:=pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖D i‖-‖D j‖)]
  have hs:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>
    Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>hp i j))
  have he:(∑i:Fin m,∑j:Fin m,(2*‖D i‖^2+2*‖D j‖^2))=
      4*(m:ℝ)*(∑i,‖D i‖^2):=by
    simp_rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←Finset.mul_sum]
    ring
  exact hs.trans_eq he

/-- The real fan Jacobian has the complete-graph gap supplied by its smallest
actual off-diagonal weight. The norm is the literal sum of squares. -/
theorem jacobian_complete_gap (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (h v:Fin m→ℝ)
    (hv:∑i,v i=0) (wmin:ℝ)
    (hlower:∀i j,i≠j→wmin≤ facetWeight b h i j):
    wmin*(m:ℝ)*(∑i,(v i)^2)≤ v ⬝ᵥ (offsetJacobian b h *ᵥ v):=by
  have hs:wmin*(∑i,∑j,(v i-v j)^2)≤
      ∑i,∑j,facetWeight b h i j*(v i-v j)^2:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij:i=j
    · simp [hij]
    · exact mul_le_mul_of_nonneg_right (hlower i j hij) (sq_nonneg _)
  rw [centered_pair_energy v hv] at hs
  rw [offsetJacobian_energy]
  simp only [Fintype.card_fin] at hs
  nlinarith

/-- The actual Gaussian row-only Hessian is bounded using its proved
conditional covariance and actual first-moment bounds. -/
theorem row_quadratic_upper (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (h:Fin m→ℝ)
    (D:Fin m→FSC.Coord d) (M wmax:ℝ) (hM:0≤ M) (hwmax:0≤ wmax)
    (hupper:∀i j,i≠j→facetWeight b h i j≤ wmax)
    (hmean:∀i j,i≠j→∀u:FSC.Coord d,|stratumMeanPairing b h {i,j} i u|≤ M*‖u‖):
    quadraticForm b h D 0≤2*(m:ℝ)*wmax*(1+M^2)*(∑i,‖D i‖^2):=by
  have hp (i j:Fin m):
      surfaceIntegral b h i j (fun x=>(affineScore D 0 i x-affineScore D 0 j x)^2)≤
      wmax*(1+M^2)*‖D i-D j‖^2:=by
    by_cases hij:i=j
    · simp [hij,surfaceIntegral_diagonal]
    · rw [surface_gap_square,cycleEdgeWeight_eq_facetWeight b h i j hij]
      simp only [Pi.zero_apply,add_zero,sub_zero,cycleMeanEdge]
      have hv: stratumDirectionalVariance b h {i,j} i (D i-D j)≤‖D i-D j‖^2:=
        (stratumDirectionalVariance_le_projector b h {i,j} i (by simp) _).trans
          (pow_le_pow_left₀ (norm_nonneg _)
            ((faceDirection b {i,j})ᗮ.norm_starProjection_apply_le _) 2)
      have hm: (stratumMeanPairing b h {i,j} i (D i-D j))^2≤ M^2*‖D i-D j‖^2:=by
        have hh:=pow_le_pow_left₀ (abs_nonneg _) (hmean i j hij (D i-D j)) 2
        simpa only [sq_abs,mul_pow] using hh
      calc
        _ ≤ facetWeight b h i j*((1+M^2)*‖D i-D j‖^2):=
          mul_le_mul_of_nonneg_left (by nlinarith) (facetWeight_nonneg b h i j)
        _ ≤ wmax*((1+M^2)*‖D i-D j‖^2):=
          mul_le_mul_of_nonneg_right (hupper i j hij) (by positivity)
        _ = _:=by ring
  have hs:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>
    Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>hp i j))
  simp only [←Finset.mul_sum] at hs
  have hv:=mul_le_mul_of_nonneg_left (pair_norm_energy_bound D)
    (show 0≤ wmax*(1+M^2) by positivity)
  unfold quadraticForm
  nlinarith

/-- Actual canonical offsets, with the mean premise fully discharged from
positive surface-weight and edge-length bounds. -/
theorem canonical_offset_l2_bound (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (h:Fin m→ℝ)
    (D:Fin m→FSC.Coord d) (wmin wmax ell:ℝ)
    (hwmin:0<wmin) (hwmax:0≤ wmax) (hell:0<ell)
    (hlower:∀i j,i≠j→wmin≤ facetWeight b h i j)
    (hupper:∀i j,i≠j→facetWeight b h i j≤ wmax)
    (hedge:∀i j,i≠j→ell≤‖b i-b j‖):
    wmin*(∑i,(canonicalOffsetVariation b h D i)^2)≤
      2*wmax*(1+(5*Real.sqrt (1+Real.log (1/(wmin*ell))))^2)*(∑i,‖D i‖^2):=by
  let v:=canonicalOffsetVariation b h D
  let M:=5*Real.sqrt (1+Real.log (1/(wmin*ell)))
  obtain ⟨σ,hσ,hl⟩:=exists_centeredSingularLowerBound b
  have hv:∑i,v i=0:=canonicalOffsetVariation_centered b D h σ hσ hl
  have hgap:=jacobian_complete_gap b h v hv wmin hlower
  have hrem:=canonicalOffset_remainder b D h σ hσ hl 0
  simp only [zero_sub,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg] at hrem
  have hnonneg:=quadraticForm_nonneg b D h v
  have henergy:v ⬝ᵥ (offsetJacobian b h *ᵥ v)≤ quadraticForm b h D 0:=by
    change quadraticForm b h D 0=quadraticForm b h D v+v ⬝ᵥ (offsetJacobian b h *ᵥ v) at hrem
    linarith
  have hmean:∀i j,i≠j→∀u:FSC.Coord d,|stratumMeanPairing b h {i,j} i u|≤ M*‖u‖:=by
    intro i j hij u
    exact facet_directional_mean_log_bound b h i j hij (wmin*ell) (mul_pos hwmin hell)
      (mul_le_mul (hlower i j hij) (hedge i j hij) hell.le (facetWeight_nonneg b h i j)) u
  have hu:=row_quadratic_upper b h D M wmax (by dsimp [M];positivity) hwmax hupper hmean
  have hm:0<(m:ℝ):=Nat.cast_pos.mpr (NeZero.pos m)
  change wmin*(∑i,(v i)^2)≤2*wmax*(1+M^2)*(∑i,‖D i‖^2)
  apply (mul_le_mul_iff_right₀ hm).mp
  nlinarith

/-- The literal intrinsic covariance-offset derivative, measured in Euclidean
label coordinates, with every response/moment premise derived. -/
theorem intrinsic_offset_l2_bound (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (H:FSC.Coord d→L[ℝ]FSC.Coord d) (hH:H.toLinearMap.IsSymmetric)
    (wmin wmax ell:ℝ) (hwmin:0<wmin) (hwmax:0≤ wmax) (hell:0<ell)
    (hlower:∀i j,i≠j→wmin≤ facetWeight b (selectedOffsets b p) i j)
    (hupper:∀i j,i≠j→facetWeight b (selectedOffsets b p) i j≤ wmax)
    (hedge:∀i j,i≠j→ell≤‖b i-b j‖):
    wmin*(∑i,(deriv (fun t:ℝ=>(covarianceOffsets
      (Matrix.gram ℝ b+t • gramVelocity b H) p:Fin m→ℝ)) 0 i)^2)≤
      (wmax/2)*(1+(5*Real.sqrt (1+Real.log (1/(wmin*ell))))^2)*
        (∑i,‖H (b i)‖^2):=by
  obtain ⟨σ,hσ,hl⟩:=exists_centeredSingularLowerBound b
  have hb:=canonical_offset_l2_bound b (selectedOffsets b p) (rowsOfOperator b H)
    wmin wmax ell hwmin hwmax hell hlower hupper hedge
  rw [(hasDerivAt_covarianceOffsets_line b σ hσ hl p hp hs H hH).deriv]
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,←Finset.mul_sum]
  change wmin*(∑i,(canonicalOffsetVariation b (selectedOffsets b p) (rowsOfOperator b H) i)^2)≤
    2*wmax*(1+(5*Real.sqrt (1+Real.log (1/(wmin*ell))))^2)*(∑i,‖H (b i)‖^2) at hb
  nlinarith

/-- Original covariance coordinates, with the true symmetric factor and its
inverse norm explicit. There is no dimension factor in the label norm. -/
theorem operator_offset_l2_bound (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (C A:FSC.Coord d→L[ℝ]FSC.Coord d) (hA:A.toLinearMap.IsSymmetric)
    (R:FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR:R.toLinearMap.IsSymmetric) (hRi:R.symm.toLinearMap.IsSymmetric)
    (hRC:R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (N:ℝ) (hN:‖R.symm.toContinuousLinearMap‖≤ N)
    (wmin wmax ell:ℝ) (hwmin:0<wmin) (hwmax:0≤ wmax) (hell:0<ell)
    (hlower:∀i j,i≠j→wmin≤ facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j)
    (hupper:∀i j,i≠j→facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j≤ wmax)
    (hedge:∀i j,i≠j→ell≤‖mappedBasis b R i-mappedBasis b R j‖):
    wmin*(∑i,(deriv (fun t:ℝ=>(operatorOffsets b p (C+t • A):Fin m→ℝ)) 0 i)^2)≤
      (wmax/2)*(1+(5*Real.sqrt (1+Real.log (1/(wmin*ell))))^2)*N^2*
        (operatorHilbertSchmidt A)^2:=by
  let H:=R.symm.toContinuousLinearMap.comp (A.comp R.symm.toContinuousLinearMap)
  have hH:H.toLinearMap.IsSymmetric:=symmetric_conjugate _ _ hRi hA
  have hb:=intrinsic_offset_l2_bound (mappedBasis b R) p hp hs H hH
    wmin wmax ell hwmin hwmax hell hlower hupper hedge
  have hrows (i:Fin m):H (mappedBasis b R i)=
      (R.symm.toContinuousLinearMap.comp A) (b i):=by
    simp [H]
  have hsum:(∑i,‖H (mappedBasis b R i)‖^2)≤ N^2*(operatorHilbertSchmidt A)^2:=by
    simp_rw [hrows]
    rw [←parseval_operator_HilbertSchmidt_sq b hP]
    have hc:operatorHilbertSchmidt (R.symm.toContinuousLinearMap.comp A)≤
        N*operatorHilbertSchmidt A:=
      (operatorHilbertSchmidt_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hN (operatorHilbertSchmidt_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (operatorHilbertSchmidt_nonneg _) hc 2
  have hh:=hb.trans (mul_le_mul_of_nonneg_left hsum
    (show 0≤(wmax/2)*(1+(5*Real.sqrt (1+Real.log (1/(wmin*ell))))^2) by positivity))
  simpa only [operatorOffsets,operator_line_gram b C A R hR hRC,H,mul_assoc] using hh

/-- The actual offset derivative remains centered; this is proved from the
canonical Gaussian response, not assumed for a selected inverse. -/
theorem operator_offset_derivative_centered (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (C A:FSC.Coord d→L[ℝ]FSC.Coord d) (hA:A.toLinearMap.IsSymmetric)
    (R:FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR:R.toLinearMap.IsSymmetric) (hRi:R.symm.toLinearMap.IsSymmetric)
    (hRC:R.toContinuousLinearMap.comp R.toContinuousLinearMap=C):
    (∑i,deriv (fun t:ℝ=>(operatorOffsets b p (C+t • A):Fin m→ℝ)) 0 i)=0:=by
  let H:=R.symm.toContinuousLinearMap.comp (A.comp R.symm.toContinuousLinearMap)
  have hH:H.toLinearMap.IsSymmetric:=symmetric_conjugate _ _ hRi hA
  obtain ⟨σ,hσ,hl⟩:=exists_centeredSingularLowerBound (mappedBasis b R)
  have hd:=hasDerivAt_covarianceOffsets_line (mappedBasis b R) σ hσ hl p hp hs H hH
  simp only [operatorOffsets,operator_line_gram b C A R hR hRC]
  rw [hd.deriv]
  simp only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,
    canonicalOffsetVariation_centered (mappedBasis b R) (rowsOfOperator (mappedBasis b R) H)
      (selectedOffsets (mappedBasis b R) p) σ hσ hl,mul_zero]

end NegativeVotingBalancedOffset
