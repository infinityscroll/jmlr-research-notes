import GaussianRegularFacetRangeGeometry
import GaussianRegularFacetLogComparison

/-! Global range-based comparison of literal regular-facet Gaussian weights.
The Gaussian cap is sandwiched using a common shift of norm O(score range),
so no ambient or score-span dimension is lost. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetRange
open NegativeVoting NegativeVotingFacetConditionalPlane NegativeVotingRegularCapProbability
  NegativeVotingAffinePathDerivative NegativeVotingBalancedReference
  NegativeVotingAffineLogScale NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl NegativeVotingAffinePositiveMass
  NegativeVotingRegularFacetLogComparison NegativeVotingFanJacobian NegativeVotingFan
  NegativeVotingRegularFacetSeed
variable {n d : ℕ}

theorem regularCap_translation_log_bound_of_norm (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (H : ℝ) (hH : 0 ≤ H)
    (z : FSC.Coord d) (hz : ‖z‖ ≤ 2*H) :
    |Real.log (affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) z/
      FSC.capMass (regularFacetNormal B i j) 0)| ≤
      512*(Real.exp 1)^3*(H*Real.sqrt (1+Real.log ((n:ℝ)+2))+H^2) := by
  have hzero : operatorHilbertSchmidt (0 : FSC.Coord d →L[ℝ] FSC.Coord d)=0 := by
    simp [operatorHilbertSchmidt,operatorEntries]
  have hh := regularCap_affine_log_ratio_bound hn hmean B hG i j hij
    (0 : FSC.Coord d →L[ℝ] FSC.Coord d) (by simp [hzero]) z
  simp only [hzero,zero_mul,zero_add,lineMass,nearIdentityMap,smul_zero,add_zero,one_smul] at hh
  have hs := (sq_le_sq₀ (norm_nonneg z) (by positivity : 0 ≤ 2*H)).mpr hz
  have hl := mul_le_mul_of_nonneg_right hz (Real.sqrt_nonneg (1+Real.log ((n:ℝ)+2)))
  have hb : ‖z‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖z‖^2 ≤
      4*(H*Real.sqrt (1+Real.log ((n:ℝ)+2))+H^2) := by
    nlinarith [mul_nonneg hH (Real.sqrt_nonneg (1+Real.log ((n:ℝ)+2)))]
  have hc := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 128*(Real.exp 1)^3)
  exact hh.trans (by nlinarith)

/-- The actual translated cap ratio is controlled by score range, even when
the translating vector has arbitrarily large spectator components. -/
theorem regularCap_range_log_bound (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    |Real.log (affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h/
      FSC.capMass (regularFacetNormal B i j) 0)| ≤
      512*(Real.exp 1)^3*(utilityRange (scoreOffsets B h)*Real.sqrt (1+Real.log ((n:ℝ)+2))+
        (utilityRange (scoreOffsets B h))^2) := by
  let W := regularFacetNormal B i j
  let z := facetRangeShift B h i j
  let H := utilityRange (scoreOffsets B h)
  have hH : 0 ≤ H := utilityRange_nonneg _
  have hz : ‖z‖ ≤ 2*H := facetRangeShift_norm_le B hG h i j hij
  have hp0 := regularCap_mass_pos hn B hG i j hij
  have hp (v : FSC.Coord d) : 0<affineMass W 0 (ContinuousLinearMap.id ℝ _) v :=
    affineMass_pos W (regularFacetNormal_unit B _ hG i j hij) 0 hp0
      (ContinuousLinearEquiv.refl ℝ _) v
  have hl := regularCap_translation_log_bound_of_norm hn hmean B hG i j hij H hH z hz
  have hu := regularCap_translation_log_bound_of_norm hn hmean B hG i j hij H hH (-z)
    (by simpa only [norm_neg] using hz)
  obtain ⟨hlo,hhi⟩ := common_shift_mass_sandwich B hG h i j hij
  have hloglo := Real.log_le_log (div_pos (hp z) hp0)
    (div_le_div_of_nonneg_right hlo hp0.le)
  have hloghi := Real.log_le_log (div_pos (hp h) hp0)
    (div_le_div_of_nonneg_right hhi hp0.le)
  exact abs_le.mpr ⟨(abs_le.mp hl).1.trans hloglo,hloghi.trans (abs_le.mp hu).2⟩

theorem conditionalMean_id_eq_projection (N h : FSC.Coord d) (hN : ‖N‖=1) :
    conditionalMean (ContinuousLinearEquiv.refl ℝ _) N h=normalProjection N h := by
  change h-(inner ℝ N h/inner ℝ N N) • N=normalProjection N h
  rw [real_inner_self_eq_norm_sq,hN,one_pow,div_one,normalProjection_apply]

theorem regularFacetNormal_inner_conditionalMean_id (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) (k : FacetLabels i j) :
    inner ℝ (regularFacetNormal B i j k)
      (conditionalMean (ContinuousLinearEquiv.refl ℝ _) (pairNormal B i j) h)=
      inner ℝ (regularFacetNormal B i j k) h := by
  have hn := pairNormal_norm B i j (regular_gram_rows_ne B _ hG i j hij)
  have hw : inner ℝ (regularFacetNormal B i j k) (pairNormal B i j)=0 := by
    rw [real_inner_comm,regularFacetNormal,real_inner_smul_right,
      regularFacetRawNormal_mem_plane B _ hG i j hij k,mul_zero]
  rw [conditionalMean_id_eq_projection _ h hn,normalProjection_apply,
    inner_sub_right,real_inner_smul_right,hw,mul_zero,sub_zero]

/-- Exact density times actual fixed-cap translation; the normal projection
of the mean is removed because every literal cap normal is tangent. -/
theorem regular_facetWeight_shift_formula (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    facetWeight B (scoreOffsets B h) i j=
      gaussianPDFReal 0 1 (-inner ℝ (pairNormal B i j) h)/Real.sqrt 2*
        affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h := by
  let I := ContinuousLinearEquiv.refl ℝ (FSC.Coord d)
  have hI : I.toLinearMap.IsSymmetric := by intro x y;rfl
  have hn := pairNormal_norm B i j (regular_gram_rows_ne B _ hG i j hij)
  have hRR : I.toContinuousLinearMap.comp I.toContinuousLinearMap=
      extendedCovariance I (pairNormal B i j) := by
    rw [extendedCovariance_eq_id I _ hn (by ext x;rfl)]
    ext x;rfl
  have hh := regularFacetWeight_eq_affineCap I hI B _ hG h i j hij I hI hRR
  have he : affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _)
      (conditionalMean I (pairNormal B i j) h)=
      affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h := by
    unfold affineMass
    congr 2
    ext x
    change (∀k,inner ℝ (regularFacetNormal B i j k)
      (x+conditionalMean I (pairNormal B i j) h) ≤ 0) ↔
      ∀k,inner ℝ (regularFacetNormal B i j k) (x+h) ≤ 0
    simp only [inner_add_right,I,regularFacetNormal_inner_conditionalMean_id B hG h i j hij]
  change facetWeight B (scoreOffsets B h) i j=
    gaussianPDFReal 0 1 (transportedLevel I (pairNormal B i j) h)/
      (Real.sqrt 2*‖I (pairNormal B i j)‖)*
      affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _)
        (conditionalMean I (pairNormal B i j) h) at hh
  rw [he] at hh
  simpa only [transportedLevel,I,ContinuousLinearEquiv.refl_apply,hn,mul_one,div_one] using hh

def rangeFacetConstant : ℝ := 512*(Real.exp 1)^3+1

theorem rangeFacetConstant_pos : 0<rangeFacetConstant := by
  unfold rangeFacetConstant
  positivity

theorem normal_density_range_bound (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    (inner ℝ (pairNormal B i j) h)^2/2 ≤ (utilityRange (scoreOffsets B h))^2 := by
  have hd : |inner ℝ (B i-B j) h| ≤ utilityRange (scoreOffsets B h) := by
    simpa only [inner_sub_left,scoreOffsets] using
      abs_sub_le_utilityRange (scoreOffsets B h) i j
  have hd2 := (sq_le_sq₀ (abs_nonneg (inner ℝ (B i-B j) h))
    (utilityRange_nonneg (scoreOffsets B h))).mpr hd
  rw [sq_abs] at hd2
  have he : (inner ℝ (B i-B j) h)^2=2*(inner ℝ (pairNormal B i j) h)^2 := by
    rw [edge_eq_norm_smul_pairNormal B i j (regular_gram_rows_ne B _ hG i j hij),
      real_inner_smul_left,regular_gram_edge_norm B _ hG i j hij,mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [sq_nonneg (utilityRange (scoreOffsets B h))]

theorem regular_facetWeight_shift_pos (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    0<facetWeight B (scoreOffsets B h) i j := by
  rw [regular_facetWeight_shift_formula B hG h i j hij]
  apply mul_pos
  · exact div_pos (gaussianPDFReal_pos 0 1 _ (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  · exact affineMass_pos _ (regularFacetNormal_unit B _ hG i j hij) 0
      (regularCap_mass_pos hn B hG i j hij) (ContinuousLinearEquiv.refl ℝ _) h

/-- The exact normal-density correction and cap-ratio logarithm. -/
theorem regular_facetWeight_shift_log_eq (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    Real.log (facetWeight B (scoreOffsets B h) i j/(referenceScale n/((n:ℝ)+2)))=
      -(inner ℝ (pairNormal B i j) h)^2/2+
        Real.log (affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h/
          FSC.capMass (regularFacetNormal B i j) 0) := by
  let W := regularFacetNormal B i j
  let p0 := FSC.capMass W 0
  let p1 := affineMass W 0 (ContinuousLinearMap.id ℝ _) h
  have hp0 : 0<p0 := regularCap_mass_pos hn B hG i j hij
  have hp1 : 0<p1 := affineMass_pos W (regularFacetNormal_unit B _ hG i j hij) 0 hp0
    (ContinuousLinearEquiv.refl ℝ _) h
  have hφ : 0<gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have hroot : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have href : referenceScale n/((n:ℝ)+2)=gaussianPDFReal 0 1 0/Real.sqrt 2*p0 := by
    have hh := regular_facetWeight_shift_formula B hG (0 : FSC.Coord d) i j hij
    have hoff : scoreOffsets B (0 : FSC.Coord d)=0 := by ext k;simp [scoreOffsets]
    rw [hoff,regular_facetWeight hn B hG i j hij] at hh
    have hid : ((fun x : FSC.Coord d => x) ⁻¹' FSC.cap (regularFacetNormal B i j) 0)=
        FSC.cap (regularFacetNormal B i j) 0 := rfl
    simpa only [inner_zero_right,neg_zero,affineMass,ContinuousLinearMap.id_apply,
      add_zero,FSC.capMass,hid,W,p0] using hh
  have hratio : facetWeight B (scoreOffsets B h) i j/(referenceScale n/((n:ℝ)+2))=
      Real.exp (-((inner ℝ (pairNormal B i j) h)^2/2))*(p1/p0) := by
    rw [regular_facetWeight_shift_formula B hG h i j hij,href,
      normalPDF_ratio (-inner ℝ (pairNormal B i j) h)]
    simp only [neg_sq]
    change (gaussianPDFReal 0 1 0*Real.exp (-((inner ℝ (pairNormal B i j) h)^2/2))/
      Real.sqrt 2*p1)/(gaussianPDFReal 0 1 0/Real.sqrt 2*p0)=_
    field_simp [hp0.ne',hφ.ne',hroot.ne']
  rw [hratio,Real.log_mul (Real.exp_ne_zero _) (div_ne_zero hp1.ne' hp0.ne'),Real.log_exp]
  simp only [neg_div,p1,p0,W]

/-- A global range envelope for the literal surface weight, with the exact
balanced scale. It becomes equality at zero score range; there is no additive
error floor and no factor depending on ambient or score-span dimension. -/
theorem regular_facetWeight_range_log_bound (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    |Real.log (facetWeight B (scoreOffsets B h) i j/(referenceScale n/((n:ℝ)+2)))| ≤
      rangeFacetConstant*(utilityRange (scoreOffsets B h)*Real.sqrt (1+Real.log ((n:ℝ)+2))+
        (utilityRange (scoreOffsets B h))^2) := by
  rw [regular_facetWeight_shift_log_eq hn B hG h i j hij]
  have ha := normal_density_range_bound B hG h i j hij
  have hc := regularCap_range_log_bound hn hmean B hG h i j hij
  have hh := abs_add_le (-(inner ℝ (pairNormal B i j) h)^2/2)
    (Real.log (affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h/
      FSC.capMass (regularFacetNormal B i j) 0))
  have habs : |-(inner ℝ (pairNormal B i j) h)^2/2|=(inner ℝ (pairNormal B i j) h)^2/2 := by
    rw [abs_div,abs_neg,abs_of_nonneg (sq_nonneg _)]
    norm_num
  rw [habs] at hh
  have hz := mul_nonneg (utilityRange_nonneg (scoreOffsets B h))
    (Real.sqrt_nonneg (1+Real.log ((n:ℝ)+2)))
  unfold rangeFacetConstant
  nlinarith

/-- Both exponential sides follow for actual positive regular facet weights. -/
theorem regular_facetWeight_range_bounds (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    let Q := rangeFacetConstant*(utilityRange (scoreOffsets B h)*Real.sqrt (1+Real.log ((n:ℝ)+2))+
      (utilityRange (scoreOffsets B h))^2)
    (referenceScale n/((n:ℝ)+2))*Real.exp (-Q) ≤ facetWeight B (scoreOffsets B h) i j ∧
      facetWeight B (scoreOffsets B h) i j ≤ (referenceScale n/((n:ℝ)+2))*Real.exp Q := by
  dsimp only
  have hw := regular_facetWeight_shift_pos hn B hG h i j hij
  have hw0 : 0<referenceScale n/((n:ℝ)+2) := div_pos (referenceScale_pos n) (by positivity)
  have hh := abs_le.mp (regular_facetWeight_range_log_bound hn hmean B hG h i j hij)
  have hlo := Real.exp_le_exp.mpr hh.1
  have hhi := Real.exp_le_exp.mpr hh.2
  rw [Real.exp_log (div_pos hw hw0)] at hlo hhi
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hw0).mp hlo
  · simpa only [mul_comm] using (div_le_iff₀ hw0).mp hhi

end NegativeVotingRegularFacetRange
