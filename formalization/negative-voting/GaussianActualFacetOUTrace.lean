import GaussianNormalTraceAllExponents
import GaussianPolynomialFacetGeometricTrace

/-! The sharp arbitrary-offset Gaussian OU restriction bound on actual ambient
hyperplanes, obtained by exact orthogonal Gaussian coordinate transport. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped RealInnerProductSpace ENNReal NNReal
namespace NegativeVotingActualFacetOUTrace
open NegativeVotingDisintegration NegativeVotingWeightedFacet
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingNormalTraceAllExponents
  NegativeVotingSmoothingComposition NegativeVotingHypercontractivity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {n : ℕ}

def ambientAverage (τ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ y,f (τ • x+Real.sqrt (1-τ^2) • y) ∂stdGaussian E

theorem ambientAverage_measurable (τ : ℝ) (f : E → ℝ) (hf : Measurable f) :
    Measurable (ambientAverage τ f) := by
  have hh : StronglyMeasurable (fun p:E×E=>f (τ • p.1+Real.sqrt (1-τ^2) • p.2)) :=
    (hf.comp (by fun_prop)).stronglyMeasurable
  exact hh.integral_prod_right'.measurable

/-- Literal equality with the Gaussian averaging operator used by the main
noise formalization, when the ambient space has Euclidean coordinates. -/
theorem ambientAverage_eq_gaussianAverage {d : ℕ} (τ : ℝ) (f : FSC.Coord d → ℝ)
    (x : FSC.Coord d) :
    ambientAverage τ f x=gaussianAverage τ (fun y=>f (WithLp.toLp 2 y)) x.ofLp := by
  unfold ambientAverage gaussianAverage
  change _=∫ y,f (WithLp.toLp 2 (fun j=>τ*x.ofLp j+Real.sqrt (1-τ^2)*y j))
    ∂NegativeVoting.standardGaussian (Fin d)
  rw [NegativeVoting.integral_standardGaussian_eq_euclidean]
  apply integral_congr_ae
  filter_upwards with y
  congr 1

theorem coordinateReconstruct_mix (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (τ s : ℝ) (p z : (Fin n → ℝ) × ℝ) :
    coordinateReconstruct w e ((fun j=>τ*p.1 j+s*z.1 j),τ*p.2+s*z.2)=
      τ • coordinateReconstruct w e p+s • coordinateReconstruct w e z := by
  unfold coordinateReconstruct
  change ((e.symm (τ • WithLp.toLp 2 p.1+s • WithLp.toLp 2 z.1) : tangentSpace w):E)+
    (τ*p.2+s*z.2) • w = _
  simp only [map_add,map_smul,Submodule.coe_add,Submodule.coe_smul,add_smul,smul_add,mul_smul]
  module

/-- Exact change of variables for the actual noise integral. -/
theorem ambientAverage_coordinateReconstruct (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (τ : ℝ) (f : E → ℝ) (hf : Measurable f) (p : (Fin n → ℝ) × ℝ) :
    ambientAverage τ f (coordinateReconstruct w e p)=
      productGaussianAverage τ (fun z=>f (coordinateReconstruct w e z)) p := by
  unfold ambientAverage
  rw [←coordinateReconstruct_map w hw e]
  rw [integral_map (f:=fun y:E=>f (τ • coordinateReconstruct w e p+Real.sqrt (1-τ^2) • y))
    (by unfold coordinateReconstruct; fun_prop)
    ((hf.comp (by fun_prop)).aestronglyMeasurable)]
  unfold productGaussianAverage
  apply integral_congr_ae
  filter_upwards with z
  rw [coordinateReconstruct_mix]

/-- Actual Gaussian surface restriction with no lower facet mass, offset
bound, or ambient-dimensional constant. -/
theorem plane_surface_square_le (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (τ q a : ℝ) (hτ : 0<τ) (hq : 2≤q) (ht : τ^2=1/(2*q-1))
    (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (f : E → ℝ) (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian E)) :
    gaussianPDFReal 0 1 a*(∫ y in F,(ambientAverage τ f ((y:E)+a • w))^2
      ∂stdGaussian (tangentSpace w)) ≤
      2*(gaussianPDFReal 0 1 a*((stdGaussian (tangentSpace w)) F).toReal)^(1-1/q)*
        ∫ x,(f x)^2 ∂stdGaussian E := by
  let T := tangentCoordinatesInverse w e
  let g := fun z : (Fin n → ℝ) × ℝ=>f (coordinateReconstruct w e z)
  have hT : Measurable T := by unfold T tangentCoordinatesInverse; fun_prop
  have hp : (γFin n) (T ⁻¹' F)=(stdGaussian (tangentSpace w)) F := by
    rw [←tangentCoordinatesInverse_map w e,Measure.map_apply hT hF]
  have hmem := (coordinateReconstruct_memLp_and_norm w hw e f 2 hf).1
  change MemLp g 2 ((γFin n).prod (gaussianReal 0 1)) at hmem
  have hb : (∫ z,(g z)^2 ∂(γFin n).prod (gaussianReal 0 1))=
      ∫ x,(f x)^2 ∂stdGaussian E := by
    rw [←coordinateReconstruct_map w hw e]
    exact (integral_map (by unfold coordinateReconstruct; fun_prop)
      (hfM.pow_const 2).aestronglyMeasurable).symm
  have hi : (∫ y in F,(ambientAverage τ f ((y:E)+a • w))^2
      ∂stdGaussian (tangentSpace w)) =
      ∫ y in T ⁻¹' F,(productGaussianAverage τ g (y,a))^2 ∂γFin n := by
    rw [←tangentCoordinatesInverse_map w e]
    rw [setIntegral_map hF (by
      exact (((ambientAverage_measurable τ f hfM).comp (by fun_prop)).pow_const 2).aestronglyMeasurable)
      hT.aemeasurable]
    apply integral_congr_ae
    filter_upwards with y
    have hc : ((T y:E)+a • w)=coordinateReconstruct w e (y,a) := rfl
    rw [hc,ambientAverage_coordinateReconstruct w hw e τ f hfM]
  have hh := actual_product_surface_subset_le τ q a hτ hq ht (T ⁻¹' F) g hmem
  change gaussianPDFReal 0 1 a*(∫ y in T ⁻¹' F,(productGaussianAverage τ g (y,a))^2 ∂γFin n)≤_ at hh
  rw [hp,hb,←hi] at hh
  exact hh

end NegativeVotingActualFacetOUTrace
