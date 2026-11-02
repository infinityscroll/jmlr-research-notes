import GaussianFanCycleStrata
import GaussianCapFirstMoment

/-! Actual Gaussian coordinate transfer for affine winner strata. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open Module
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

abbrev FaceCoordinates (b : AffineBasis V ℝ E) (S : Set V) :=
  FSC.Coord (Module.finrank ℝ (faceDirection b S)ᗮ)

def faceCoordinates (b : AffineBasis V ℝ E) (S : Set V) :
    (faceDirection b S)ᗮ ≃ₗᵢ[ℝ] FaceCoordinates b S :=
  (stdOrthonormalBasis ℝ (faceDirection b S)ᗮ).repr

def coordinateCapNormal (b : AffineBasis V ℝ E) (S : Set V) (i : V)
    (k : {k : V // k ∉ S}) : FaceCoordinates b S :=
  faceCoordinates b S (intrinsicCapNormal b S i k)

def coordinateEmbed (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (x : FaceCoordinates b S) : E := embedFace b h S ((faceCoordinates b S).symm x)

def coordinateCap (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) (i : V) :
    Set (FaceCoordinates b S) :=
  FSC.cap (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)

theorem coordinateCapNormal_norm (b : AffineBasis V ℝ E) (S : Set V) (i : V)
    (hi : i ∈ S) (k : {k : V // k ∉ S}) : ‖coordinateCapNormal b S i k‖ = 1 := by
  rw [coordinateCapNormal, LinearIsometryEquiv.norm_map]
  exact intrinsicCapNormal_norm b S i hi k

theorem coordinateCapNormal_NoCoincident (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) :
    FSC.NoCoincident (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) := by
  intro k l hkl
  constructor
  · intro he
    exfalso
    apply intrinsicCapNormal_ne_smul b S i hi k l hkl 1
    rw [one_smul]
    exact (faceCoordinates b S).injective he
  · intro he
    exfalso
    apply intrinsicCapNormal_ne_smul b S i hi k l hkl (-1)
    apply (faceCoordinates b S).injective
    simpa only [map_smul, map_neg, neg_one_smul, coordinateCapNormal] using he

theorem coordinateCap_mem_iff (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (x : FaceCoordinates b S) :
    x ∈ coordinateCap b h S i ↔
      (faceCoordinates b S).symm x ∈ intrinsicWinnerCap b h S i := by
  change (∀ k, ⟪faceCoordinates b S (intrinsicCapNormal b S i k),x⟫ ≤ _) ↔ _
  have he (k : {k : V // k ∉ S}) :
      ⟪faceCoordinates b S (intrinsicCapNormal b S i k),x⟫ =
        ⟪intrinsicCapNormal b S i k,(faceCoordinates b S).symm x⟫ := by
    rw [← (faceCoordinates b S).inner_map_map]
    simp
  simp only [he]
  rfl

theorem coordinateEmbed_mem_winnerStratum_iff (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (x : FaceCoordinates b S) :
    coordinateEmbed b h S x ∈ winnerStratum b h S ↔ x ∈ coordinateCap b h S i := by
  rw [coordinateEmbed, embedFace_mem_winnerStratum_iff b h S i hi, coordinateCap_mem_iff]

theorem coordinateEmbed_isometry (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) :
    Isometry (coordinateEmbed b h S) :=
  (embedFace_isometry b h S).comp (faceCoordinates b S).symm.isometry

/-- Positive Gaussian mass is derived from the constructed strict point. -/
theorem coordinateCap_gaussian_pos (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) :
    0 < stdGaussian (FaceCoordinates b S) (coordinateCap b h S i) := by
  classical
  let x0 := faceCoordinates b S (intrinsicStrictPoint b h S)
  let U : Set (FaceCoordinates b S) := {x | ∀ k,
    ⟪coordinateCapNormal b S i k,x⟫ < intrinsicCapOffset b h S i k}
  have hopen : IsOpen U := by
    dsimp [U]
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const
  have hx0 : x0 ∈ U := by
    intro k
    change ⟪faceCoordinates b S (intrinsicCapNormal b S i k),
      faceCoordinates b S (intrinsicStrictPoint b h S)⟫ < _
    rw [(faceCoordinates b S).inner_map_map]
    exact intrinsicStrictPoint_strict b h S i hi k
  have hsub : U ⊆ coordinateCap b h S i := fun x hx k => le_of_lt (hx k)
  exact lt_of_lt_of_le (FSC.stdGaussian_pos_of_isOpen hopen ⟨x0,hx0⟩) (measure_mono hsub)

theorem coordinateCap_mass_pos (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) :
    0 < FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) := by
  exact ENNReal.toReal_pos (ne_of_gt (coordinateCap_gaussian_pos b h S i hi))
    (measure_ne_top _ _)

/-- Actual Gaussian boundary first moment for these derived score-stratum coordinates. -/
theorem coordinateCap_first_moment (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (v : FaceCoordinates b S) :
    (∫ x in coordinateCap b h S i, ⟪v,x⟫ ∂stdGaussian (FaceCoordinates b S)) =
      -(∑ k, WeakSimplex.normalPDF (intrinsicCapOffset b h S i k) *
        FSC.sliceMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) k *
        ⟪coordinateCapNormal b S i k,v⟫) := by
  classical
  exact NegativeVotingPolyhedral.gaussian_cap_first_moment _
    (coordinateCapNormal_norm b S i hi) _ (coordinateCapNormal_NoCoincident b h S i hi) v

/-- The actual coordinate image of the tangent projection of an ambient test vector. -/
def coordinateDual (b : AffineBasis V ℝ E) (S : Set V) (v : E) : FaceCoordinates b S :=
  faceCoordinates b S ((faceDirection b S)ᗮ.orthogonalProjectionOnto v)

theorem coordinateDual_pairing (b : AffineBasis V ℝ E) (S : Set V)
    (v : E) (x : FaceCoordinates b S) :
    ⟪coordinateDual b S v,x⟫ = ⟪v,((faceCoordinates b S).symm x : E)⟫ := by
  unfold coordinateDual
  calc
    _ = ⟪(faceDirection b S)ᗮ.orthogonalProjectionOnto v,(faceCoordinates b S).symm x⟫ := by
      rw [← (faceCoordinates b S).inner_map_map]
      simp
    _ = _ := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right _ _

theorem coordinateDual_norm (b : AffineBasis V ℝ E) (S : Set V) (v : E) :
    ‖coordinateDual b S v‖ = ‖(faceDirection b S)ᗮ.starProjection v‖ := by
  rw [coordinateDual, LinearIsometryEquiv.norm_map]
  rfl

theorem coordinateEmbed_pairing (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (v : E) (x : FaceCoordinates b S) :
    ⟪v,coordinateEmbed b h S x⟫ =
      ⟪v,faceAnchor b h S⟫+⟪coordinateDual b S v,x⟫ := by
  rw [coordinateEmbed, embedFace, inner_add_right, coordinateDual_pairing]

theorem coordinateEmbed_pairing_integrable (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (v : E) :
    Integrable (fun x => ⟪v,coordinateEmbed b h S x⟫)
      ((stdGaussian (FaceCoordinates b S)).restrict (coordinateCap b h S i)) := by
  simp_rw [coordinateEmbed_pairing]
  exact (integrable_const _).add
    ((IsGaussian.integrable_dual (stdGaussian (FaceCoordinates b S))
      (innerSL ℝ (coordinateDual b S v))).restrict)

theorem coordinateEmbed_integral_pairing (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (v : E) :
    (∫ x in coordinateCap b h S i, ⟪v,coordinateEmbed b h S x⟫
      ∂stdGaussian (FaceCoordinates b S)) =
      FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)*⟪v,faceAnchor b h S⟫+
      ∫ x in coordinateCap b h S i, ⟪coordinateDual b S v,x⟫
        ∂stdGaussian (FaceCoordinates b S) := by
  simp_rw [coordinateEmbed_pairing]
  have hg : Integrable (fun x : FaceCoordinates b S => ⟪coordinateDual b S v,x⟫)
      ((stdGaussian (FaceCoordinates b S)).restrict (coordinateCap b h S i)) :=
    (IsGaussian.integrable_dual _ (innerSL ℝ (coordinateDual b S v))).restrict
  rw [integral_add (integrable_const _) hg, integral_const]
  simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  rfl

/-- Literal ambient directional mean under the intrinsic Gaussian law of the actual stratum. -/
def stratumMeanPairing (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) (i : V) (v : E) : ℝ :=
  (∫ x in coordinateCap b h S i, ⟪v,coordinateEmbed b h S x⟫
    ∂stdGaussian (FaceCoordinates b S)) /
    FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)

def stratumDirectionalVariance (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (v : E) : ℝ :=
  (∫ x in coordinateCap b h S i,
    (⟪v,coordinateEmbed b h S x⟫-stratumMeanPairing b h S i v)^2
    ∂stdGaussian (FaceCoordinates b S)) /
    FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)

theorem stratumMeanPairing_eq (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (v : E) :
    stratumMeanPairing b h S i v = ⟪v,faceAnchor b h S⟫+
      (∫ x in coordinateCap b h S i, ⟪coordinateDual b S v,x⟫
        ∂stdGaussian (FaceCoordinates b S)) /
      FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) := by
  have hp := ne_of_gt (coordinateCap_mass_pos b h S i hi)
  rw [stratumMeanPairing, coordinateEmbed_integral_pairing]
  field_simp

/-- Genuine covariance domination by the actual tangent projector for every score stratum. -/
theorem stratumDirectionalVariance_le_projector (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (v : E) :
    stratumDirectionalVariance b h S i v ≤ ‖(faceDirection b S)ᗮ.starProjection v‖^2 := by
  unfold stratumDirectionalVariance
  simp_rw [coordinateEmbed_pairing, stratumMeanPairing_eq b h S i hi,
    add_sub_add_left_eq_sub]
  rw [← coordinateDual_norm]
  exact NegativeVotingPolyhedral.gaussian_cap_conditional_variance_le _ _
    (coordinateCap_mass_pos b h S i hi) (coordinateDual b S v)

theorem coordinateEmbed_norm_sq (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (x : FaceCoordinates b S) :
    ‖coordinateEmbed b h S x‖^2 = ‖faceAnchor b h S‖^2+‖x‖^2 := by
  have hq : faceAnchor b h S ∈ faceDirection b S :=
    ((faceDirection b S).orthogonalProjectionOnto (affineFanApex b h)).property
  have hz := ((faceCoordinates b S).symm x).property
  have ho := Submodule.inner_right_of_mem_orthogonal hq hz
  rw [coordinateEmbed, embedFace, norm_add_sq_real, ho]
  have hn : ‖((faceCoordinates b S).symm x : E)‖ = ‖x‖ :=
    (faceCoordinates b S).symm.norm_map x
  rw [hn]
  ring

/-- The actual normal Gaussian density factor on the affine stratum. -/
def stratumDensityFactor (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹ ^ Module.finrank ℝ (faceDirection b S) *
    Real.exp (-‖faceAnchor b h S‖^2/2)

theorem stratumDensityFactor_pos (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) :
    0 < stratumDensityFactor b h S := by
  unfold stratumDensityFactor
  positivity

/-- Pointwise Gaussian density factorization on the actual isometric stratum coordinates. -/
theorem coordinateEmbed_gaussian_density (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (x : FaceCoordinates b S) :
    (Real.sqrt (2*Real.pi))⁻¹ ^ Module.finrank ℝ E *
      Real.exp (-‖coordinateEmbed b h S x‖^2/2) =
      stratumDensityFactor b h S * (FSC.standardDensity x).toReal := by
  rw [coordinateEmbed_norm_sq, ← (faceDirection b S).finrank_add_finrank_orthogonal,
    pow_add, FSC.toReal_standardDensity, stratumDensityFactor]
  have he : -(‖faceAnchor b h S‖^2+‖x‖^2)/2 =
      -‖faceAnchor b h S‖^2/2 + -‖x‖^2/2 := by ring
  rw [he, Real.exp_add]
  ring

end NegativeVotingFanCycle
