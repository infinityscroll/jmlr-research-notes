import GaussianRegularCapProbability

/-! Actual finite relative-weight estimate for a deformed regular Gaussian
facet, with the conditional Gaussian factor and mean displayed explicitly. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetLogComparison
open NegativeVotingFacetConditionalPlane NegativeVotingRegularCapProbability
  NegativeVotingRegularFacetSeed NegativeVotingBalancedReference NegativeVotingFan
  NegativeVotingFanJacobian NegativeVotingAffineLogScale NegativeVotingAffineLogMassBound
  NegativeVotingAffinePathDerivative NegativeVotingAffinePositiveMass NegativeVotingAffineNormControl
variable {n d : ℕ}

theorem normalPDF_ratio (a : ℝ) :
    gaussianPDFReal 0 1 a=gaussianPDFReal 0 1 0*Real.exp (-(a^2/2)) := by
  simp [gaussianPDFReal,neg_div]

/-- A direct estimate for the literal surface weight, not a supplied
conditional-moment or face-probability bound. The remaining factor proximity
is a finite-dimensional metric condition on the actual Schur square root. -/
theorem regular_facetWeight_log_ratio_bound
    (hn : 0 < n) (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hS : S.toLinearMap.IsSymmetric)
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=
      extendedCovariance S (pairNormal B i j))
    (hsmall : 4*Real.exp 1*operatorHilbertSchmidt
      (R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1) :
    |Real.log (facetWeight (transportedRows S B) (scoreOffsets B h) i j /
      (referenceScale n/((n:ℝ)+2)))| ≤
      (transportedLevel S (pairNormal B i j) h)^2/2+
        |Real.log ‖S (pairNormal B i j)‖|+
        128*(Real.exp 1)^3*(operatorHilbertSchmidt
          (R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d))*(1+Real.log ((n:ℝ)+2))+
          ‖conditionalMean S (pairNormal B i j) h‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+
          ‖conditionalMean S (pairNormal B i j) h‖^2) := by
  let N := pairNormal B i j
  let β := conditionalMean S N h
  let a := transportedLevel S N h
  let s := ‖S N‖
  let W := regularFacetNormal B i j
  let A := R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)
  let p0 := FSC.capMass W 0
  let p1 := affineMass W 0 R.toContinuousLinearMap β
  have hN : ‖N‖=1 := pairNormal_norm B i j (regular_gram_rows_ne B _ hG i j hij)
  have hs : 0 < s := transformed_normal_norm_pos S N hN
  have hp0 : 0 < p0 := regularCap_mass_pos hn B hG i j hij
  have hp1 : 0 < p1 := affineMass_pos W (regularFacetNormal_unit B _ hG i j hij)
    0 hp0 R β
  have hφ : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have hsqrt : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hm : 0 < (n:ℝ)+2 := by positivity
  have href : referenceScale n/((n:ℝ)+2)=gaussianPDFReal 0 1 0/Real.sqrt 2*p0 := by
    dsimp only [p0,W]
    rw [regularCap_mass_eq hn B hG i j hij]
    field_simp
  have hw := regularFacetWeight_eq_affineCap S hS B _ hG h i j hij R hR hRR
  change facetWeight (transportedRows S B) (scoreOffsets B h) i j=
    gaussianPDFReal 0 1 a/(Real.sqrt 2*s)*p1 at hw
  have he : lineMass W 0 A β 1=p1 := by
    unfold lineMass nearIdentityMap
    dsimp only [A,p1]
    congr 1 <;> module
  have hcap := regularCap_affine_log_ratio_bound hn hmean B hG i j hij A hsmall β
  change |Real.log (lineMass W 0 A β 1/p0)| ≤ _ at hcap
  rw [he] at hcap
  have hratio : facetWeight (transportedRows S B) (scoreOffsets B h) i j /
      (referenceScale n/((n:ℝ)+2))=Real.exp (-(a^2/2))/s*(p1/p0) := by
    rw [hw,href,normalPDF_ratio]
    field_simp
  have hlog : Real.log (facetWeight (transportedRows S B) (scoreOffsets B h) i j /
      (referenceScale n/((n:ℝ)+2)))= -(a^2/2)-Real.log s+Real.log (p1/p0) := by
    rw [hratio,Real.log_mul (div_ne_zero (Real.exp_ne_zero _) hs.ne') (div_ne_zero hp1.ne' hp0.ne'),
      Real.log_div (Real.exp_ne_zero _) hs.ne',Real.log_exp]
  rw [hlog]
  have hh := abs_add_le (-(a^2/2)-Real.log s) (Real.log (p1/p0))
  have hsub := abs_add_le (-(a^2/2)) (-Real.log s)
  have habs : |-(a^2/2)|=a^2/2 := by rw [abs_neg,abs_of_nonneg (by positivity)]
  rw [habs,abs_neg] at hsub
  change |-(a^2/2)-Real.log s| ≤ a^2/2+|Real.log s| at hsub
  change |-(a^2/2)-Real.log s+Real.log (p1/p0)| ≤
    a^2/2+|Real.log s|+128*(Real.exp 1)^3*
      (operatorHilbertSchmidt A*(1+Real.log ((n:ℝ)+2))+
        ‖β‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖β‖^2)
  linarith

end NegativeVotingRegularFacetLogComparison
