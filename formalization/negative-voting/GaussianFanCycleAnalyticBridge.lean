import GaussianFanCycleForms
import GaussianFanQuadraticHessian
import GaussianFanCycleMoments

/-! Identifying the geometric two-cell strata with the actual affine-facet
slice measure used by the Gaussian Hessian and offset Jacobian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanCycleBridge
open NegativeVotingFanCycle NegativeVotingFan NegativeVotingFanHessian
  NegativeVotingFanJacobian NegativeVotingWeightedFacet NegativeVotingDisintegration
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The two geometric definitions describe exactly the same closed face. -/
theorem winnerStratum_pair (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (i j : V) :
    winnerStratum b h {i,j} = affineFacet b h i j := by
  ext x
  constructor
  · intro hx
    exact ⟨le_antisymm (hx j (by simp) i) (hx i (by simp) j), hx i (by simp)⟩
  · rintro ⟨he,hc⟩ k hk l
    rcases Set.mem_insert_iff.mp hk with rfl | hk
    · exact hc l
    · have hk' : k = j := Set.mem_singleton_iff.mp hk
      subst k
      exact (hc l).trans_eq he

/-- The pair direction is precisely the normal line of the analytic facet. -/
theorem faceDirection_pair_normal (b : AffineBasis V ℝ (FSC.Coord d)) (i j : V) (hij : i ≠ j) :
    faceDirection b {i,j} = ℝ ∙ pairNormal b i j := by
  have hn : ‖b i-b j‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij))
  simp only [faceDirection,Set.image_insert_eq,Set.image_singleton,vectorSpan_pair,vsub_eq_sub,pairNormal]
  exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn)) _).symm

theorem pairNormal_apex (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (i j : V) :
    inner ℝ (pairNormal b i j) (affineFanApex b h) = pairOffset b h i j := by
  have he : inner ℝ (b i-b j) (affineFanApex b h) = h j-h i := by
    calc
      _ = inner ℝ (affineFanApex b h) (b i-b j) := real_inner_comm _ _
      _ = _ := affineFanApex_edge b h i j
  rw [pairNormal,real_inner_smul_left,he]
  simp [pairOffset,div_eq_mul_inv,mul_comm]

theorem faceAnchor_pair (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (i j : V) (hij : i ≠ j) :
    faceAnchor b h {i,j} = pairOffset b h i j • pairNormal b i j := by
  simp only [faceAnchor,faceDirection_pair_normal b i j hij,
    Submodule.starProjection_unit_singleton ℝ (pairNormal_norm b i j (b.ind.injective.ne hij)),pairNormal_apex]

/-- The full pushed-forward intrinsic Gaussian is the literal affine slice law. -/
theorem coordinateEmbed_pair_map (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) :
    (stdGaussian (FaceCoordinates b {i,j})).map (coordinateEmbed b h {i,j}) =
      FSC.sliceLaw (pairNormal b i j) (pairOffset b h i j) := by
  have hm : Measurable (fun y : (faceDirection b {i,j})ᗮ =>
      faceAnchor b h {i,j} + (y : FSC.Coord d)) := by fun_prop
  have he : coordinateEmbed b h {i,j} =
      (fun y : (faceDirection b {i,j})ᗮ => faceAnchor b h {i,j} + (y : FSC.Coord d)) ∘
        (faceCoordinates b {i,j}).symm := rfl
  rw [he,← Measure.map_map hm (by fun_prop),stdGaussian_map]
  rw [faceAnchor_pair b h i j hij]
  rw [FSC.sliceLaw,gaussian_affine_slice_map _ (pairNormal_norm b i j (b.ind.injective.ne hij))]
  simp only [tangentSpace]
  exact congrArg (fun T : Submodule ℝ (FSC.Coord d) =>
    (stdGaussian Tᗮ).map (fun y : Tᗮ => pairOffset b h i j • pairNormal b i j + (y : FSC.Coord d)))
    (faceDirection_pair_normal b i j hij)

theorem coordinateEmbed_preimage_affineFacet (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) :
    (coordinateEmbed b h {i,j}) ⁻¹' affineFacet b h i j = coordinateCap b h {i,j} i := by
  ext x
  exact (by simpa only [winnerStratum_pair,Set.mem_preimage] using
    coordinateEmbed_mem_winnerStratum_iff b h {i,j} i (by simp) x)

/-- The boundary-measure identity transfers every continuous ambient test. -/
theorem affineFacet_integral_eq_stratum (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) (F : FSC.Coord d → ℝ) (hF : Continuous F) :
    (∫ x in affineFacet b h i j, F x ∂FSC.sliceLaw (pairNormal b i j) (pairOffset b h i j)) =
      ∫ x in coordinateCap b h {i,j} i, F (coordinateEmbed b h {i,j} x)
        ∂stdGaussian (FaceCoordinates b {i,j}) := by
  rw [← coordinateEmbed_pair_map b h i j hij]
  rw [setIntegral_map (isClosed_affineFacet b h i j).measurableSet
    hF.measurable.aestronglyMeasurable (coordinateEmbed_isometry b h {i,j}).continuous.aemeasurable]
  rw [coordinateEmbed_preimage_affineFacet]

theorem stratumDensityFactor_pair (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) :
    stratumDensityFactor b h {i,j} = gaussianPDFReal 0 1 (pairOffset b h i j) := by
  have hw := pairNormal_norm b i j (b.ind.injective.ne hij)
  have hn : pairNormal b i j ≠ 0 := by intro hz; simp [hz] at hw
  rw [stratumDensityFactor,faceDirection_pair_normal b i j hij,
    finrank_span_singleton hn,faceAnchor_pair b h i j hij]
  simp only [pow_one,norm_smul,hw,mul_one,Real.norm_eq_abs,sq_abs]
  simp [gaussianPDFReal,div_eq_mul_inv,mul_comm,mul_left_comm]

/-- The analytic surface form uses exactly the same geometric Gaussian mass. -/
theorem surfaceIntegral_eq_stratum (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) (F : FSC.Coord d → ℝ) (hF : Continuous F) :
    surfaceIntegral b h i j F = stratumDensityFactor b h {i,j} / ‖b i-b j‖ *
      ∫ x in coordinateCap b h {i,j} i, F (coordinateEmbed b h {i,j} x)
        ∂stdGaussian (FaceCoordinates b {i,j}) := by
  rw [surfaceIntegral,affineFacet_integral_eq_stratum b h i j hij F hF,
    stratumDensityFactor_pair b h i j hij]

theorem cycleEdgeWeight_eq_facetWeight (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) : cycleEdgeWeight b h i j = facetWeight b h i j := by
  have hs := surfaceIntegral_eq_stratum b h i j hij (fun _ => 1) continuous_const
  rw [surfaceIntegral_const] at hs
  have hc : (∫ x in coordinateCap b h {i,j} i, (1:ℝ)
      ∂stdGaussian (FaceCoordinates b {i,j})) =
      FSC.capMass (coordinateCapNormal b {i,j} i) (intrinsicCapOffset b h {i,j} i) := by
    simp [FSC.capMass,coordinateCap,Measure.real]
  rw [hc,mul_one] at hs
  rw [cycleEdgeWeight,if_neg hij,stratumMassAt,hs]
  ring

/-- The geometric conditional mean is the actual analytic facet first moment. -/
theorem surfaceIntegral_inner (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) (v : FSC.Coord d) :
    surfaceIntegral b h i j (fun x => inner ℝ v x) =
      cycleEdgeWeight b h i j * stratumMeanPairing b h {i,j} i v := by
  rw [surfaceIntegral_eq_stratum b h i j hij _ (by fun_prop),
    cycleEdgeWeight,if_neg hij,stratumMassAt,stratumMeanPairing]
  have hp := ne_of_gt (coordinateCap_mass_pos b h {i,j} i (by simp))
  field_simp [hp]

/-- Every affine score-difference test agrees with the actual cycle flux. -/
theorem surfaceIntegral_affine (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) (v : FSC.Coord d) (c : ℝ) :
    surfaceIntegral b h i j (fun x => inner ℝ v x + c) =
      cycleEdgeWeight b h i j * (stratumMeanPairing b h {i,j} i v + c) := by
  haveI : IsGaussian (FSC.sliceLaw (pairNormal b i j) (pairOffset b h i j)) :=
    NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  have hi : Integrable (fun x : FSC.Coord d => inner ℝ v x)
      (FSC.sliceLaw (pairNormal b i j) (pairOffset b h i j)) :=
    IsGaussian.integrable_dual _ (innerSL ℝ v)
  rw [surfaceIntegral_add b h i j _ _ hi (integrable_const c),
    surfaceIntegral_inner b h i j hij v,surfaceIntegral_const,
    ← cycleEdgeWeight_eq_facetWeight b h i j hij]
  ring

end NegativeVotingFanCycleBridge
