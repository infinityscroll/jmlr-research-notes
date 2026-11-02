import GaussianFanCover

/-!
# Actual Gaussian tangent-normal transport and facet disintegration

Projection laws and independence are proved for the concrete standard Gaussian.
The resulting integral formulas do not assume a conditional Gaussian law or a
normal-slice disintegration hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators Classical
namespace NegativeVotingDisintegration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal projection sends the actual standard Gaussian to the standard
Gaussian on the target subspace. This is a measure identity, not a law premise. -/
theorem gaussian_projection_map (T : Submodule ℝ E) :
    (stdGaussian E).map T.orthogonalProjectionOnto = stdGaussian T := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map T.orthogonalProjectionOnto.continuous.aemeasurable
    (by fun_prop)]
  simp_rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  change charFun (stdGaussian E) (t : E) = charFun (stdGaussian T) t
  rw [charFun_stdGaussian, charFun_stdGaussian]
  rfl

def tangentSpace (w : E) : Submodule ℝ E := (ℝ ∙ w)ᗮ

def tangentNormal (w : E) : E → tangentSpace w × ℝ :=
  fun x => ((tangentSpace w).orthogonalProjectionOnto x, inner ℝ w x)

def normalReconstruct (w : E) : tangentSpace w × ℝ → E :=
  fun q => (q.1 : E) + q.2 • w

/-- Gaussianity of the joint linear map is established before using the
zero cross-covariance criterion for independence. -/
theorem tangent_normal_independent (w : E) :
    IndepFun (tangentSpace w).orthogonalProjectionOnto (fun x => inner ℝ w x) (stdGaussian E) := by
  have hjoint : HasGaussianLaw (fun x => ((tangentSpace w).orthogonalProjectionOnto x, inner ℝ w x)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map ((tangentSpace w).orthogonalProjectionOnto.prod (innerSL ℝ w))
  apply hjoint.indepFun_of_covariance_inner
  intro u v
  simp_rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have heq : (fun x : E => inner ℝ v (inner ℝ w x)) = fun x => inner ℝ (v • w) x := by
    funext x
    simp only [Real.inner_apply, real_inner_smul_left]
  rw [heq, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, real_inner_smul_right]
  have hu : inner ℝ (u : E) w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.property
  rw [hu, mul_zero]

/-- Unit normal coordinates have exactly the scalar N(0,1) law. -/
theorem gaussian_unit_normal_map (w : E) (hw : ‖w‖ = 1) :
    (stdGaussian E).map (fun x => inner ℝ w x) = gaussianReal 0 1 := by
  simpa only [hw, one_pow, Real.toNNReal_one] using NegativeVotingCapTail.gaussian_inner_map w

/-- Exact joint tangent-normal Gaussian law, with independence derived. -/
theorem tangentNormal_map (w : E) (hw : ‖w‖ = 1) :
    (stdGaussian E).map (tangentNormal w) = (stdGaussian (tangentSpace w)).prod (gaussianReal 0 1) := by
  have hh := IndepFun.map_prod_eq_prod_map_map
    (show AEMeasurable (tangentSpace w).orthogonalProjectionOnto (stdGaussian E) by fun_prop)
    (show AEMeasurable (fun x => inner ℝ w x) (stdGaussian E) by fun_prop)
    (tangent_normal_independent w)
  rw [gaussian_projection_map, gaussian_unit_normal_map w hw] at hh
  exact hh

omit [MeasurableSpace E] [BorelSpace E] in
/-- Reconstruction is the actual orthogonal decomposition of every point. -/
theorem normalReconstruct_tangentNormal (w : E) (hw : ‖w‖ = 1) (x : E) :
    normalReconstruct w (tangentNormal w x) = x := by
  unfold normalReconstruct tangentNormal tangentSpace
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hw]
  exact sub_add_cancel _ _


omit [MeasurableSpace E] [BorelSpace E] in
/-- Explicit ambient formula for the intrinsic tangent projection. -/
theorem tangent_projection_formula (w : E) (hw : ‖w‖ = 1) (x : E) :
    ((tangentSpace w).orthogonalProjectionOnto x : E) = x - inner ℝ w x • w := by
  have hh := normalReconstruct_tangentNormal w hw x
  exact eq_sub_iff_add_eq.mpr hh

/-- Identification of the ambient pushforward slice measure with the translated
intrinsic tangent Gaussian. This supplies the law comparison needed when a
normal-slice formula is written using ambient projected variables. -/
theorem gaussian_affine_slice_map (w : E) (hw : ‖w‖ = 1) (a : ℝ) :
    (stdGaussian E).map (fun x => a • w + (x - inner ℝ w x • w)) =
      (stdGaussian (tangentSpace w)).map (fun y : tangentSpace w => a • w + (y : E)) := by
  rw [← gaussian_projection_map (tangentSpace w), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  dsimp only [Function.comp_def]
  rw [tangent_projection_formula w hw]

/-- Recombining independent tangent and normal Gaussians recovers the exact
ambient Gaussian measure. -/
theorem normalReconstruct_map (w : E) (hw : ‖w‖ = 1) :
    ((stdGaussian (tangentSpace w)).prod (gaussianReal 0 1)).map (normalReconstruct w) = stdGaussian E := by
  rw [← tangentNormal_map w hw, Measure.map_map]
  · have heq : normalReconstruct w ∘ tangentNormal w = id := by
      funext x
      exact normalReconstruct_tangentNormal w hw x
    rw [heq, Measure.map_id]
  · unfold normalReconstruct
    fun_prop
  · unfold tangentNormal
    fun_prop

/-- Integrability is transported from the actual ambient Gaussian. -/
theorem integrable_normalReconstruct (w : E) (hw : ‖w‖ = 1) (f : E → ℝ)
    (hf : Integrable f (stdGaussian E)) :
    Integrable (fun q => f (normalReconstruct w q))
      ((stdGaussian (tangentSpace w)).prod (gaussianReal 0 1)) := by
  have hp : MeasurePreserving (normalReconstruct w)
      ((stdGaussian (tangentSpace w)).prod (gaussianReal 0 1)) (stdGaussian E) :=
    ⟨by unfold normalReconstruct; fun_prop, normalReconstruct_map w hw⟩
  exact (hp.integrable_comp hf.aestronglyMeasurable).mpr hf

/-- Fubini disintegration for every genuinely integrable ambient function. -/
theorem integral_tangent_normal (w : E) (hw : ‖w‖ = 1) (f : E → ℝ)
    (hf : Integrable f (stdGaussian E)) :
    (∫ x, f x ∂stdGaussian E) =
      ∫ y : tangentSpace w, ∫ t : ℝ, f ((y : E) + t • w) ∂gaussianReal 0 1
        ∂stdGaussian (tangentSpace w) := by
  have hmap := normalReconstruct_map w hw
  calc
    _ = ∫ x, f x ∂(((stdGaussian (tangentSpace w)).prod (gaussianReal 0 1)).map (normalReconstruct w)) := by rw [hmap]
    _ = ∫ q, f (normalReconstruct w q) ∂(stdGaussian (tangentSpace w)).prod (gaussianReal 0 1) :=
      integral_map (by unfold normalReconstruct; fun_prop)
        (by rw [hmap]; exact hf.aestronglyMeasurable)
    _ = _ := integral_prod _ (integrable_normalReconstruct w hw f hf)

/-- Shift to the pair plane at normal offset a. The Gaussian factor is
φ(a+z), and the normal cost coordinate is z, exactly as in the fibre estimates. -/
theorem integral_shifted_pair_plane (w : E) (hw : ‖w‖ = 1) (a : ℝ) (f : E → ℝ)
    (hf : Integrable f (stdGaussian E)) :
    (∫ x, f x ∂stdGaussian E) =
      ∫ y : tangentSpace w, (∫ z : ℝ,
        gaussianPDFReal 0 1 (a + z) * f ((y : E) + (a + z) • w))
        ∂stdGaussian (tangentSpace w) := by
  rw [integral_tangent_normal w hw f hf]
  apply integral_congr_ae
  filter_upwards with y
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  exact (integral_add_left_eq_self (μ := volume)
    (fun z => gaussianPDFReal 0 1 z * f ((y : E) + z • w)) a).symm



section Coordinates
variable {κ : Type*} [Fintype κ]

/-- Any explicit orthonormal coordinate isometry sends the actual Gaussian
to the independent scalar Gaussian coordinate law used by NormalTrace. -/
theorem gaussian_coordinate_isometry_map (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    (stdGaussian E).map (fun x => (e x).ofLp) = NegativeVoting.standardGaussian κ := by
  calc
    _ = ((stdGaussian E).map e).map (fun x : EuclideanSpace ℝ κ => x.ofLp) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (stdGaussian (EuclideanSpace ℝ κ)).map (fun x => x.ofLp) := by rw [stdGaussian_map e]
    _ = ((NegativeVoting.standardGaussian κ).map (WithLp.toLp 2)).map (fun x => x.ofLp) := by
      rw [map_pi_eq_stdGaussian]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [Function.comp_def, Measure.map_id']

/-- A canonical isometry always exists, with exactly the tangent dimension. -/
def canonicalTangentCoordinates (w : E) :
    tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (tangentSpace w))) :=
  (stdOrthonormalBasis ℝ (tangentSpace w)).repr

def coordinateTangentNormal (w : E) (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    E → (κ → ℝ) × ℝ :=
  fun x => ((e ((tangentSpace w).orthogonalProjectionOnto x)).ofLp, inner ℝ w x)

def coordinateReconstruct (w : E) (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    (κ → ℝ) × ℝ → E :=
  fun q => (e.symm (WithLp.toLp 2 q.1) : E) + q.2 • w

/-- Literal γ-coordinate × scalar-normal law, matching NormalTrace's domain. -/
theorem coordinateTangentNormal_map (w : E) (hw : ‖w‖ = 1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    (stdGaussian E).map (coordinateTangentNormal w e) =
      (NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1) := by
  have heq : coordinateTangentNormal w e =
      Prod.map (fun y : tangentSpace w => (e y).ofLp) id ∘ tangentNormal w := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by unfold tangentNormal; fun_prop), tangentNormal_map w hw,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), gaussian_coordinate_isometry_map e, Measure.map_id]

omit [MeasurableSpace E] [BorelSpace E] in
theorem coordinateReconstruct_coordinateTangentNormal (w : E) (hw : ‖w‖ = 1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) (x : E) :
    coordinateReconstruct w e (coordinateTangentNormal w e x) = x := by
  unfold coordinateReconstruct coordinateTangentNormal
  simp only [WithLp.toLp_ofLp, LinearIsometryEquiv.symm_apply_apply]
  exact normalReconstruct_tangentNormal w hw x

/-- The coordinate reconstruction has the ambient Gaussian as its actual law. -/
theorem coordinateReconstruct_map (w : E) (hw : ‖w‖ = 1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    ((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)).map (coordinateReconstruct w e) =
      stdGaussian E := by
  rw [← coordinateTangentNormal_map w hw e, Measure.map_map]
  · have heq : coordinateReconstruct w e ∘ coordinateTangentNormal w e = id := by
      funext x
      exact coordinateReconstruct_coordinateTangentNormal w hw e x
    rw [heq, Measure.map_id]
  · unfold coordinateReconstruct
    fun_prop
  · unfold coordinateTangentNormal
    fun_prop

/-- Genuine ambient Lp inputs become genuine product-Gaussian Lp inputs under
the chart, with no dimension or angle loss in the norm. -/
theorem coordinateReconstruct_memLp_and_norm (w : E) (hw : ‖w‖ = 1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) (f : E → ℝ) (p : ℝ≥0∞)
    (hf : MemLp f p (stdGaussian E)) :
    MemLp (fun q => f (coordinateReconstruct w e q)) p
        ((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)) ∧
      eLpNorm (fun q => f (coordinateReconstruct w e q)) p
        ((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)) = eLpNorm f p (stdGaussian E) := by
  have hp : MeasurePreserving (coordinateReconstruct w e)
      ((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)) (stdGaussian E) :=
    ⟨by unfold coordinateReconstruct; fun_prop, coordinateReconstruct_map w hw e⟩
  exact ⟨hf.comp_measurePreserving hp, eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hp⟩

/-- The shifted-plane integral in literal independent Gaussian coordinates. -/
theorem integral_coordinate_shifted_plane (w : E) (hw : ‖w‖ = 1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) (a : ℝ) (f : E → ℝ)
    (hf : Integrable f (stdGaussian E)) :
    (∫ x, f x ∂stdGaussian E) =
      ∫ y : κ → ℝ, (∫ z : ℝ,
        gaussianPDFReal 0 1 (a + z) * f (coordinateReconstruct w e (y, a + z)))
        ∂NegativeVoting.standardGaussian κ := by
  have hmap := coordinateReconstruct_map w hw e
  have hp : MeasurePreserving (coordinateReconstruct w e)
      ((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)) (stdGaussian E) :=
    ⟨by unfold coordinateReconstruct; fun_prop, hmap⟩
  have hi : Integrable (fun q => f (coordinateReconstruct w e q))
      ((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)) :=
    (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  have heq : (∫ x, f x ∂stdGaussian E) =
      ∫ y : κ → ℝ, ∫ t : ℝ, f (coordinateReconstruct w e (y, t)) ∂gaussianReal 0 1
        ∂NegativeVoting.standardGaussian κ := by
    calc
      _ = ∫ x, f x ∂(((NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1)).map (coordinateReconstruct w e)) := by rw [hmap]
      _ = ∫ q, f (coordinateReconstruct w e q) ∂(NegativeVoting.standardGaussian κ).prod (gaussianReal 0 1) :=
        integral_map (by unfold coordinateReconstruct; fun_prop)
          (by rw [hmap]; exact hf.aestronglyMeasurable)
      _ = _ := integral_prod _ hi
  rw [heq]
  apply integral_congr_ae
  filter_upwards with y
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  exact (integral_add_left_eq_self (μ := volume)
    (fun z => gaussianPDFReal 0 1 z * f (coordinateReconstruct w e (y, z))) a).symm

end Coordinates
end NegativeVotingDisintegration
