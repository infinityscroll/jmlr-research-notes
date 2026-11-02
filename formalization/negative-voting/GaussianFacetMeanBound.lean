import GaussianAffineLogMassBound
import GaussianFanCycleAnalyticBridge

/-! Actual conditional Gaussian first moments on arbitrary affine facets,
controlled by the actual facet weight and edge length. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingFacetMean
open NegativeVotingFan NegativeVotingFanCycle NegativeVotingFanCycleBridge NegativeVotingFacetDegree
  NegativeVotingFanJacobian NegativeVotingAffineLogMassBound NegativeVotingMovingCap
  NegativeVotingRegularFacetMean NegativeVotingWeightedFacet NegativeVotingDisintegration
variable {d:ℕ} {V:Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A real Gaussian stratum mean is controlled by its normal anchor and the
conditional centroid of its actual intrinsic cap. -/
theorem stratum_directional_mean_bound (b:AffineBasis V ℝ (FSC.Coord d)) (h:V→ℝ)
    (S:Set V) (i:V) (hi:i∈S) (v:FSC.Coord d):
    |stratumMeanPairing b h S i v|≤
      (‖faceAnchor b h S‖+2*Real.sqrt (Real.log (1/
        FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)))+
        (Real.sqrt (2*Real.pi))⁻¹)*‖v‖:=by
  let C:=coordinateCap b h S i
  let p:=FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)
  let μ:=stdGaussian (FaceCoordinates b S)
  let u:FaceCoordinates b S:=p⁻¹ • (∫x in C,x ∂μ)
  have hp:0<p:=coordinateCap_mass_pos b h S i hi
  have hm:=conditional_mean_probability_bound C
    (FSC.measurableSet_cap _ _) hp
  change ‖u‖≤2*Real.sqrt (Real.log (1/p))+(Real.sqrt (2*Real.pi))⁻¹ at hm
  have hd:‖coordinateDual b S v‖≤‖v‖:=by
    rw [coordinateDual_norm]
    exact (faceDirection b S)ᗮ.norm_starProjection_apply_le v
  have he:(∫x in C,inner ℝ (coordinateDual b S v) x ∂μ)/p=
      inner ℝ (coordinateDual b S v) u:=by
    have hv:Integrable (fun x:FaceCoordinates b S=>x) (μ.restrict C):=
      IsGaussian.integrable_id.restrict
    have hh:=integral_inner (𝕜:=ℝ) hv (coordinateDual b S v)
    change (∫x in C,inner ℝ (coordinateDual b S v) x ∂μ)=
      inner ℝ (coordinateDual b S v) (∫x in C,x ∂μ) at hh
    rw [hh]
    simp only [u,real_inner_smul_right,div_eq_mul_inv,mul_comm]
  rw [stratumMeanPairing_eq b h S i hi]
  change |inner ℝ v (faceAnchor b h S)+(∫x in C,inner ℝ (coordinateDual b S v) x ∂μ)/p|≤_
  rw [he]
  calc
    _ ≤ |inner ℝ v (faceAnchor b h S)|+|inner ℝ (coordinateDual b S v) u|:=abs_add_le _ _
    _ ≤ ‖v‖*‖faceAnchor b h S‖+‖coordinateDual b S v‖*‖u‖:=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖v‖*‖faceAnchor b h S‖+‖v‖*(2*Real.sqrt (Real.log (1/p))+
        (Real.sqrt (2*Real.pi))⁻¹):=
      add_le_add le_rfl (mul_le_mul hd hm (norm_nonneg _) (norm_nonneg _))
    _ = _:=by dsimp [p];ring

def facetMeanScale (θ:ℝ):ℝ:=
  Real.sqrt (2*Real.log (1/θ))+2*Real.sqrt (Real.log (1/θ))+
    (Real.sqrt (2*Real.pi))⁻¹

/-- Actual facet probability and offset control follow from w_e ell_e≥θ.
No conditional-mean hypothesis is supplied. -/
theorem facet_directional_mean_bound (b:AffineBasis V ℝ (FSC.Coord d)) (h:V→ℝ)
    (i j:V) (hij:i≠j) (θ:ℝ) (hθ:0<θ)
    (hweight:θ≤ facetWeight b h i j*‖b i-b j‖) (v:FSC.Coord d):
    |stratumMeanPairing b h {i,j} i v|≤ facetMeanScale θ*‖v‖:=by
  let p:=FSC.capMass (coordinateCapNormal b {i,j} i) (intrinsicCapOffset b h {i,j} i)
  let q:=pairOffset b h i j
  have hp:0<p:=coordinateCap_mass_pos b h {i,j} i (by simp)
  have hp1:p≤1:=measureReal_le_one
  have hedge:‖b i-b j‖≠0:=norm_ne_zero_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij))
  have hw:facetWeight b h i j*‖b i-b j‖=gaussianPDFReal 0 1 q*p:=by
    rw [←cycleEdgeWeight_eq_facetWeight b h i j hij,cycleEdgeWeight,if_neg hij,
      div_mul_cancel₀ _ hedge,stratumMassAt,stratumDensityFactor_pair b h i j hij]
  have hprod:θ≤ gaussianPDFReal 0 1 q*p:=by rwa [hw] at hweight
  have hpdf1:gaussianPDFReal 0 1 q≤1:=
    (normalPDF_le_zero q).trans normalPDF_zero_le_one
  have hθp:θ≤ p:=hprod.trans (mul_le_of_le_one_left hp.le hpdf1)
  have hθ1:θ≤1:=hθp.trans hp1
  have hθpdf:θ≤ gaussianPDFReal 0 1 q:=hprod.trans
    (mul_le_of_le_one_right (gaussianPDFReal_nonneg _ _ _) hp1)
  have hθexp:θ≤ Real.exp (-(q^2)/2):=by
    apply hθpdf.trans
    rw [show gaussianPDFReal 0 1 q=gaussianPDFReal 0 1 0*Real.exp (-(q^2)/2) from normalPDF_factor q]
    exact mul_le_of_le_one_left (Real.exp_pos _).le normalPDF_zero_le_one
  have hlog:0≤ Real.log (1/θ):=Real.log_nonneg ((le_div_iff₀ hθ).mpr (by simpa using hθ1))
  have hq2:q^2≤2*Real.log (1/θ):=by
    have hh:=Real.log_le_log hθ hθexp
    rw [Real.log_exp] at hh
    simp only [one_div,Real.log_inv]
    linarith
  have hqabs:|q|≤ Real.sqrt (2*Real.log (1/θ)):=by
    apply (sq_le_sq₀ (abs_nonneg q) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt (mul_nonneg (by norm_num) hlog)]
    exact hq2
  have hanchor:‖faceAnchor b h {i,j}‖≤ Real.sqrt (2*Real.log (1/θ)):=by
    rw [faceAnchor_pair b h i j hij,norm_smul,Real.norm_eq_abs,
      pairNormal_norm b i j (b.ind.injective.ne hij),mul_one]
    exact hqabs
  have hlogp:Real.log (1/p)≤ Real.log (1/θ):=
    Real.log_le_log (div_pos zero_lt_one hp) (one_div_le_one_div_of_le hθ hθp)
  have hsqrt:=Real.sqrt_le_sqrt hlogp
  have hh:=stratum_directional_mean_bound b h {i,j} i (by simp) v
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  change ‖faceAnchor b h {i,j}‖+2*Real.sqrt (Real.log (1/p))+
    (Real.sqrt (2*Real.pi))⁻¹≤ facetMeanScale θ
  unfold facetMeanScale
  linarith

theorem facetMeanScale_le (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1):
    facetMeanScale θ≤5*Real.sqrt (1+Real.log (1/θ)):=by
  have hlog:0≤ Real.log (1/θ):=Real.log_nonneg ((le_div_iff₀ hθ).mpr (by simpa using hθ1))
  have hc:(Real.sqrt (2*Real.pi))⁻¹≤1:=by
    simpa [gaussianPDFReal] using normalPDF_zero_le_one
  have h1:1≤ Real.sqrt (1+Real.log (1/θ)):=by
    have hh:=Real.sq_sqrt (show 0≤1+Real.log (1/θ) by linarith)
    have hp:=Real.sqrt_nonneg (1+Real.log (1/θ))
    nlinarith
  have hs:Real.sqrt (Real.log (1/θ))≤ Real.sqrt (1+Real.log (1/θ)):=
    Real.sqrt_le_sqrt (by linarith)
  have hs2:Real.sqrt (2*Real.log (1/θ))≤2*Real.sqrt (1+Real.log (1/θ)):=by
    calc
      _ ≤ Real.sqrt (4*(1+Real.log (1/θ))):=Real.sqrt_le_sqrt (by linarith)
      _ = _:=by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)];norm_num
  unfold facetMeanScale
  linarith

theorem facetWeight_mul_edge_le_one (b:AffineBasis V ℝ (FSC.Coord d)) (h:V→ℝ)
    (i j:V) (hij:i≠j):facetWeight b h i j*‖b i-b j‖≤1:=by
  have hedge:‖b i-b j‖≠0:=norm_ne_zero_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij))
  rw [←cycleEdgeWeight_eq_facetWeight b h i j hij,cycleEdgeWeight,if_neg hij,
    div_mul_cancel₀ _ hedge,stratumMassAt,stratumDensityFactor_pair b h i j hij]
  have hp:FSC.capMass (coordinateCapNormal b {i,j} i) (intrinsicCapOffset b h {i,j} i)≤1:=
    measureReal_le_one
  have hφ:gaussianPDFReal 0 1 (pairOffset b h i j)≤1:=
    (normalPDF_le_zero _).trans normalPDF_zero_le_one
  exact (mul_le_of_le_one_right (gaussianPDFReal_nonneg _ _ _) hp).trans hφ

/-- Explicit logarithmic control from actual surface geometry alone. -/
theorem facet_directional_mean_log_bound (b:AffineBasis V ℝ (FSC.Coord d)) (h:V→ℝ)
    (i j:V) (hij:i≠j) (θ:ℝ) (hθ:0<θ)
    (hweight:θ≤facetWeight b h i j*‖b i-b j‖) (v:FSC.Coord d):
    |stratumMeanPairing b h {i,j} i v|≤
      (5*Real.sqrt (1+Real.log (1/θ)))*‖v‖:=by
  exact (facet_directional_mean_bound b h i j hij θ hθ hweight v).trans
    (mul_le_mul_of_nonneg_right
      (facetMeanScale_le θ hθ (hweight.trans (facetWeight_mul_edge_le_one b h i j hij)))
      (norm_nonneg v))

end NegativeVotingFacetMean
