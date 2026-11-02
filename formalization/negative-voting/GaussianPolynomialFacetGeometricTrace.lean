import GaussianPolynomialFacetLogBound
import GaussianQuadraticAffineTransport

/-! Exact transfer of the finite-coordinate polynomial trace to the actual
Euclidean affine-plane Gaussian. The algebraic cutoff for the transport bulk
is proved from its literal formula, rather than supplied as a Hermite premise. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical ENNReal
open NegativeVotingDisintegration NegativeVotingWeightedFacet
open NegativeVotingPolynomialDegree NegativeVotingPolynomialFacetLogBound
open NegativeVotingSmoothingComposition GaussianFin

namespace NegativeVotingPolynomialFacetGeometricTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {n : ℕ}

def tangentCoordinatesInverse (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) : tangentSpace w := e.symm (WithLp.toLp 2 x)

theorem tangentCoordinatesInverse_map (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (γFin n).map (tangentCoordinatesInverse w e) = stdGaussian (tangentSpace w) := by
  unfold tangentCoordinatesInverse
  change (γFin n).map (e.symm ∘ WithLp.toLp 2) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  change ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)).map e.symm = _
  rw [map_pi_eq_stdGaussian, stdGaussian_map]

/-- The actual ambient reconstruction is linear in all n+1 scalar coordinates. -/
def reconstructLinear (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] E where
  toFun x := coordinateReconstruct w e (normalCoordinates x)
  map_add' x y := by
    simp only [coordinateReconstruct, normalCoordinates_apply, Pi.add_apply]
    change ((e.symm (WithLp.toLp 2 (fun j => x j.succ) +
      WithLp.toLp 2 (fun j => y j.succ)) : tangentSpace w) : E) +
      (x 0+y 0) • w = _
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    simp only [coordinateReconstruct, normalCoordinates_apply, Pi.smul_apply,
      RingHom.id_apply]
    change ((e.symm (c • WithLp.toLp 2 (fun j => x j.succ)) : tangentSpace w) : E) +
      (c * x 0) • w = _
    simp [smul_add, mul_smul]

@[simp] theorem reconstructLinear_apply (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x : Fin (n+1) → ℝ) :
    reconstructLinear w e x = coordinateReconstruct w e (normalCoordinates x) := rfl

theorem reconstructLinear_map (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (γFin (n+1)).map (reconstructLinear w e) = stdGaussian E := by
  change (γFin (n+1)).map (coordinateReconstruct w e ∘ normalCoordinates) = _
  rw [← Measure.map_map (by unfold coordinateReconstruct; fun_prop)
    normalCoordinates.measurable, normalCoordinates_measurePreserving.map_eq]
  exact coordinateReconstruct_map w hw e

/-- A coordinate-free affine-plane estimate. All measures are the concrete
standard Gaussians, and the only polynomial premise is pointwise algebraic degree. -/
theorem plane_integral_sq_log_m (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : E → ℝ) (hfc : Continuous f)
    (hf : (fun x => f (reconstructLinear w e x)) ∈ polynomialSpace 4)
    (a A m : ℝ) (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (hm : 1 ≤ m) (hprob : m ^ (-4096 : ℝ) ≤ ((stdGaussian (tangentSpace w)) F).toReal)
    (ha : |a| ≤ A*Real.sqrt (1+Real.log m)) :
    (∫ y in F, f ((y:E)+a • w)^2 ∂stdGaussian (tangentSpace w)) ≤
      ((stdGaussian (tangentSpace w)) F).toReal * quarticLogConstant A *
        (1+Real.log m)^4 * ∫ x, f x^2 ∂stdGaussian E := by
  let T := tangentCoordinatesInverse w e
  have hT : Measurable T := by unfold T tangentCoordinatesInverse; fun_prop
  have hp : (γFin n) (T ⁻¹' F) = (stdGaussian (tangentSpace w)) F := by
    rw [← tangentCoordinatesInverse_map w e, Measure.map_apply hT hF]
  have hi : (∫ y in F, f ((y:E)+a • w)^2 ∂stdGaussian (tangentSpace w)) =
      ∫ y in T ⁻¹' F, f ((T y:E)+a • w)^2 ∂γFin n := by
    rw [← tangentCoordinatesInverse_map w e]
    exact setIntegral_map hF (by fun_prop) hT.aemeasurable
  have hb : (∫ x, f x^2 ∂stdGaussian E) =
      ∫ x, f (reconstructLinear w e x)^2 ∂γFin (n+1) := by
    rw [← reconstructLinear_map w hw e]
    exact integral_map (reconstructLinear w e).continuous_of_finiteDimensional.aemeasurable
      (by fun_prop)
  have htrace := polynomial_face_integral_sq_log_m hf a A m (T ⁻¹' F) hm
    (by simpa only [hp] using hprob) ha
  have he (y : Fin n → ℝ) :
      normalLift (fun x => f (reconstructLinear w e x)) (y,a) = f ((T y:E)+a • w) := by
    simp only [normalLift, Function.comp_apply, reconstructLinear_apply,
      MeasurableEquiv.apply_symm_apply]
    rfl
  simp_rw [he] at htrace
  rw [hp, ← hb, ← hi] at htrace
  exact htrace

section Algebra
variable {κ : Type*} [Fintype κ]

theorem linear_mul_mem {k : ℕ} {f : (κ→ℝ)→ℝ}
    (hf : f ∈ polynomialSpace k) (l : (κ→ℝ)→ₗ[ℝ] ℝ) :
    (fun x => l x*f x) ∈ polynomialSpace (k+1) := by
  let c : κ→ℝ := fun i => l (fun j => if i=j then 1 else 0)
  have he : l = affineFunction c 0 := by
    funext x
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [affineFunction, zero_add, smul_eq_mul, c, mul_comm]
  rw [he]
  exact affine_mul_mem hf c 0

theorem inner_mul_mem {k : ℕ} {f : (κ→ℝ)→ℝ}
    (hf : f ∈ polynomialSpace k) (R : (κ→ℝ)→ₗ[ℝ] E) (v : E) :
    (fun x => inner ℝ v (R x)*f x) ∈ polynomialSpace (k+1) :=
  linear_mul_mem hf ((innerSL ℝ v).toLinearMap.comp R)

theorem inner_mem (R : (κ→ℝ)→ₗ[ℝ] E) (v : E) :
    (fun x => inner ℝ v (R x)) ∈ polynomialSpace 1 := by
  simpa only [mul_one] using inner_mul_mem (one_mem (κ:=κ) 0) R v

theorem affine_score_mem (R : (κ→ℝ)→ₗ[ℝ] E) (v : E) (c : ℝ) :
    (fun x => inner ℝ v (R x)+c) ∈ polynomialSpace 1 := by
  convert (polynomialSpace 1).add_mem (inner_mem R v)
    ((polynomialSpace 1).smul_mem c (one_mem (κ:=κ) 1)) using 1
  funext x
  simp

theorem quadratic_mem (R : (κ→ℝ)→ₗ[ℝ] E) (v y : E) :
    (fun x => inner ℝ v (R x)*inner ℝ y (R x)) ∈ polynomialSpace 2 :=
  inner_mul_mem (inner_mem R y) R v

theorem quartic_mem (R : (κ→ℝ)→ₗ[ℝ] E) (u v y a : E) :
    (fun x => inner ℝ u (R x)*(inner ℝ v (R x)*inner ℝ y (R x)*inner ℝ a (R x)))
      ∈ polynomialSpace 4 := by
  have h3 := inner_mul_mem (quadratic_mem R y a) R v
  have h4 := inner_mul_mem h3 R u
  simpa only [mul_assoc] using h4

open NegativeVotingQuadraticAffineTransport
variable {d : ℕ}

/-- The quadratic form in the constant-test transport score is a finite
sum of products of linear scores, including for nonsymmetric operators. -/
theorem quadratic_form_mem (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d)
    (T : FSC.Coord d→L[ℝ] FSC.Coord d) :
    (fun x => inner ℝ (R x) (T (R x))) ∈ polynomialSpace 2 := by
  have hh := (polynomialSpace 2).sum_mem (fun a (_:a∈Finset.univ) =>
    quadratic_mem R (T (EuclideanSpace.basisFun (Fin d) ℝ a))
      (EuclideanSpace.basisFun (Fin d) ℝ a))
  convert hh using 1
  funext x
  simpa only [Finset.sum_apply] using
    (NegativeVotingAffineOperatorDerivative.basis_quadratic_sum T (R x)).symm

theorem massBulk_expression_mem (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d)
    (T : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (fun x => inner ℝ (R x) (T (R x))+inner ℝ z (R x)-
      LinearMap.trace ℝ (FSC.Coord d) T.toLinearMap) ∈ polynomialSpace 2 := by
  convert (polynomialSpace 2).sub_mem
    ((polynomialSpace 2).add_mem (quadratic_form_mem R T)
      (polynomialSpace_mono (by decide : 1≤2) (inner_mem R z)))
    ((polynomialSpace 2).smul_mem (LinearMap.trace ℝ (FSC.Coord d) T.toLinearMap)
      (one_mem (κ:=κ) 2)) using 1
  funext x
  simp

theorem rankOneBulk_mem (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d) (v y u a z : FSC.Coord d) :
    (fun x => rankOneBulk v y u a z (R x)) ∈ polynomialSpace 4 := by
  have h1 (q : FSC.Coord d) := inner_mem R q
  have h2 (q r : FSC.Coord d) := quadratic_mem R q r
  have hG := ((polynomialSpace 2).add_mem
    ((polynomialSpace 2).smul_mem (inner ℝ u v) (h2 y a))
    ((polynomialSpace 2).smul_mem (inner ℝ u y) (h2 v a)))
  have hG' := (polynomialSpace 2).add_mem hG
    ((polynomialSpace 2).smul_mem (inner ℝ u a) (h2 v y))
  have hZ := inner_mul_mem (h2 v y) R z
  have hL := (polynomialSpace 1).add_mem
    ((polynomialSpace 1).smul_mem (inner ℝ z v) (h1 y))
    ((polynomialSpace 1).smul_mem (inner ℝ z y) (h1 v))
  exact (polynomialSpace 4).sub_mem
    ((polynomialSpace 4).add_mem
      ((polynomialSpace 4).sub_mem (quartic_mem R u v y a)
        (polynomialSpace_mono (by decide : 2≤4) hG'))
      (polynomialSpace_mono (by decide : 3≤4) hZ))
    (polynomialSpace_mono (by decide : 1≤4) hL)

/-- The actual nonsymmetric affine transport bulk has degree at most four. -/
theorem affineBulk_mem (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d) (v y : FSC.Coord d)
    (T : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (fun x => affineBulk v y T z (R x)) ∈ polynomialSpace 4 := by
  have hh := (polynomialSpace 4).add_mem
    ((polynomialSpace 4).sum_mem (fun a (_:a∈Finset.univ) => rankOneBulk_mem R v y
      (T (EuclideanSpace.basisFun (Fin d) ℝ a)) (EuclideanSpace.basisFun (Fin d) ℝ a) 0))
    (rankOneBulk_mem R v y 0 0 z)
  convert hh using 1
  funext x
  simpa only [Pi.add_apply, Finset.sum_apply] using affineBulk_decomposition v y T z (R x)
end Algebra

/-- Affine scores in the actual facet first variation satisfy the same bound. -/
theorem plane_affine_score_integral_sq_log_m (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (v : E) (c : ℝ)
    (a A m : ℝ) (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (hm : 1 ≤ m) (hprob : m ^ (-4096 : ℝ) ≤ ((stdGaussian (tangentSpace w)) F).toReal)
    (ha : |a| ≤ A*Real.sqrt (1+Real.log m)) :
    (∫ z in F, (inner ℝ v ((z:E)+a • w)+c)^2 ∂stdGaussian (tangentSpace w)) ≤
      ((stdGaussian (tangentSpace w)) F).toReal * quarticLogConstant A *
        (1+Real.log m)^4 * ∫ x, (inner ℝ v x+c)^2 ∂stdGaussian E :=
  plane_integral_sq_log_m w hw e (fun x => inner ℝ v x+c) (by fun_prop)
    (polynomialSpace_mono (by decide : 1≤4) (affine_score_mem (reconstructLinear w e) v c))
    a A m F hF hm hprob ha

/-- Quadratic scores require no supplied polynomial representation. -/
theorem plane_quadratic_integral_sq_log_m (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (v y : E)
    (a A m : ℝ) (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (hm : 1 ≤ m) (hprob : m ^ (-4096 : ℝ) ≤ ((stdGaussian (tangentSpace w)) F).toReal)
    (ha : |a| ≤ A*Real.sqrt (1+Real.log m)) :
    (∫ z in F, (inner ℝ v ((z:E)+a • w)*inner ℝ y ((z:E)+a • w))^2
      ∂stdGaussian (tangentSpace w)) ≤
      ((stdGaussian (tangentSpace w)) F).toReal * quarticLogConstant A *
        (1+Real.log m)^4 * ∫ x, (inner ℝ v x*inner ℝ y x)^2 ∂stdGaussian E :=
  plane_integral_sq_log_m w hw e (fun x => inner ℝ v x*inner ℝ y x) (by fun_prop)
    (polynomialSpace_mono (by decide : 2≤4) (quadratic_mem (reconstructLinear w e) v y))
    a A m F hF hm hprob ha

/-- Four-linear scores also meet the exact cutoff, independently of dimension. -/
theorem plane_quartic_integral_sq_log_m (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (u v y b : E)
    (a A m : ℝ) (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (hm : 1 ≤ m) (hprob : m ^ (-4096 : ℝ) ≤ ((stdGaussian (tangentSpace w)) F).toReal)
    (ha : |a| ≤ A*Real.sqrt (1+Real.log m)) :
    (∫ z in F, (inner ℝ u ((z:E)+a • w)*(inner ℝ v ((z:E)+a • w)*
      inner ℝ y ((z:E)+a • w)*inner ℝ b ((z:E)+a • w)))^2
      ∂stdGaussian (tangentSpace w)) ≤
      ((stdGaussian (tangentSpace w)) F).toReal * quarticLogConstant A *
        (1+Real.log m)^4 *
        ∫ x, (inner ℝ u x*(inner ℝ v x*inner ℝ y x*inner ℝ b x))^2 ∂stdGaussian E :=
  plane_integral_sq_log_m w hw e
    (fun x => inner ℝ u x*(inner ℝ v x*inner ℝ y x*inner ℝ b x)) (by fun_prop)
    (quartic_mem (reconstructLinear w e) u v y b) a A m F hF hm hprob ha

section ActualFacets
open NegativeVotingFan NegativeVotingQuadraticAffineTransport
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The slice law in the actual facet derivative is precisely the chart law. -/
theorem sliceLaw_eq_facetChart_map (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (hij : B i ≠ B j) :
    FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) =
      (stdGaussian (tangentSpace (pairNormal B i j))).map (facetChart B h i j) := by
  unfold FSC.sliceLaw
  rw [gaussian_affine_slice_map _ (pairNormal_norm B i j hij)]
  congr 1
  funext y
  exact add_comm _ _

/-- Exact intrinsic-facet estimate for the literal quartic Hessian transport
bulk. The canonical tangent isometry exists for every ambient dimension. -/
theorem facet_affineBulk_integral_sq_log_m
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i ≠ B j)
    (v y : FSC.Coord d) (T : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (A m : ℝ) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤
      ((stdGaussian (tangentSpace (pairNormal B i j))) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j| ≤ A*Real.sqrt (1+Real.log m)) :
    (∫ q in intrinsicFacet B h i j,
      affineBulk v y T z (facetChart B h i j q)^2
      ∂stdGaussian (tangentSpace (pairNormal B i j))) ≤
      ((stdGaussian (tangentSpace (pairNormal B i j))) (intrinsicFacet B h i j)).toReal *
        quarticLogConstant A * (1+Real.log m)^4 *
        ∫ x, affineBulk v y T z x^2 ∂stdGaussian (FSC.Coord d) := by
  exact plane_integral_sq_log_m _ (pairNormal_norm B i j hij)
    (canonicalTangentCoordinates (pairNormal B i j)) (affineBulk v y T z)
    (by unfold affineBulk; fun_prop)
    (affineBulk_mem _ v y T z) (pairOffset B h i j) A m
    (intrinsicFacet B h i j) (isClosed_intrinsicFacet B h i j).measurableSet hm hprob ha

/-- Ambient form of the same estimate, using exactly FSC.sliceLaw and
affineFacet from the moving-cell derivative, with no conditional-law premise. -/
theorem affineFacet_affineBulk_integral_sq_log_m
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i ≠ B j)
    (v y : FSC.Coord d) (T : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (A m : ℝ) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal)
    (ha : |pairOffset B h i j| ≤ A*Real.sqrt (1+Real.log m)) :
    (∫ x in affineFacet B h i j, affineBulk v y T z x^2
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal *
        quarticLogConstant A * (1+Real.log m)^4 *
        ∫ x, affineBulk v y T z x^2 ∂stdGaussian (FSC.Coord d) := by
  have hmChart : Measurable (facetChart B h i j) := by unfold facetChart; fun_prop
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    Measure.map_apply hmChart (isClosed_affineFacet B h i j).measurableSet] at hprob ⊢
  rw [setIntegral_map (isClosed_affineFacet B h i j).measurableSet
    (by unfold affineBulk; fun_prop) hmChart.aemeasurable]
  exact facet_affineBulk_integral_sq_log_m B h i j hij v y T z A m hm hprob ha
end ActualFacets

end NegativeVotingPolynomialFacetGeometricTrace
