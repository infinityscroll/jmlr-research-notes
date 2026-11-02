import GaussianCovarianceZeroFloorBound
import GaussianFractionalMassEnergy

/-! Exact transport from the product-Gaussian assignment coordinates used by
the spectral theorem to Euclidean Gaussian centroid optimization.  Arbitrary
finite coordinate types and completed-measurable fractional assignments are
retained. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical Topology

namespace NegativeVotingAssignmentCoordinateBridge
open NegativeVoting NegativeVotingFractionalMass NegativeVotingMassCentroid
  NegativeVotingAssignmentDuality NegativeVotingCentroidOptimization
  NegativeVotingCovarianceZeroFloorBound NegativeVotingCovarianceOptimizer
  NegativeVotingCovarianceStrict

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι] {d : ℕ}

theorem coordinate_map_measurePreserving
    (e : FSC.Coord d ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    MeasurePreserving (fun x : FSC.Coord d => (e x).ofLp)
      (stdGaussian (FSC.Coord d)) (standardGaussian κ) := by
  have he : MeasurePreserving e (stdGaussian (FSC.Coord d))
      (stdGaussian (EuclideanSpace ℝ κ)) := ⟨e.continuous.measurable, stdGaussian_map e⟩
  exact gaussian_ofLp_measurePreserving.comp he

theorem coordinate_integral (e : FSC.Coord d ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (g : (κ → ℝ) → ℝ) (hg : AEStronglyMeasurable g (standardGaussian κ)) :
    (∫ x : FSC.Coord d, g (e x).ofLp ∂stdGaussian (FSC.Coord d)) =
      ∫ x, g x ∂standardGaussian κ := by
  have hm := coordinate_map_measurePreserving e
  have hs : AEStronglyMeasurable g
      ((stdGaussian (FSC.Coord d)).map (fun x => (e x).ofLp)) := by
    simpa only [hm.map_eq] using hg
  simpa only [hm.map_eq] using (integral_map hm.measurable.aemeasurable hs).symm

def coordinateRule (e : FSC.Coord d ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (f : (κ → ℝ) → ι → ℝ) : FSC.Coord d → ι → ℝ := fun x => f (e x).ofLp

theorem coordinateRule_feasible (e : FSC.Coord d ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    Feasible (assignmentMass f) (coordinateRule e f) := by
  have hm := coordinate_map_measurePreserving e
  refine ⟨fun i => (hf i).aestronglyMeasurable.comp_measurePreserving hm |>.aemeasurable,
    hm.quasiMeasurePreserving.ae hp, fun i => ?_⟩
  exact coordinate_integral e (fun x => f x i) (hf i).aestronglyMeasurable

theorem coordinate_centroid_norm_sq
    (e : FSC.Coord d ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) (f : (κ → ℝ) → ℝ)
    (hf : AEMeasurable f (standardGaussian κ))
    (h01 : ∀ᵐ x ∂standardGaussian κ, 0 ≤ f x ∧ f x ≤ 1) :
    ‖gaussianCentroid (fun x : FSC.Coord d => f (e x).ofLp)‖^2 =
      ∑ j, (∫ x, x j*f x ∂standardGaussian κ)^2 := by
  let F : FSC.Coord d → ℝ := fun x => f (e x).ofLp
  have hm := coordinate_map_measurePreserving e
  have hF : AEMeasurable F (stdGaussian (FSC.Coord d)) :=
    (hf.aestronglyMeasurable.comp_measurePreserving hm).aemeasurable
  have hF01 : ∀ᵐ x ∂stdGaussian (FSC.Coord d), 0 ≤ F x ∧ F x ≤ 1 :=
    hm.quasiMeasurePreserving.ae h01
  have hV := fractional_vector_integrable F hF hF01
  have hcoord (j : κ) : (e (gaussianCentroid F)) j =
      ∫ x, x j*f x ∂standardGaussian κ := by
    let L : FSC.Coord d →L[ℝ] ℝ := (EuclideanSpace.proj (𝕜:=ℝ) j).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap
    calc
      _ = ∫ x : FSC.Coord d, L (F x • x) ∂stdGaussian (FSC.Coord d) :=
        (L.integral_comp_comm hV).symm
      _ = ∫ x : FSC.Coord d, F x*(e x) j ∂stdGaussian (FSC.Coord d) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [map_smul]
        rfl
      _ = _ := by
        simpa only [F, mul_comm] using coordinate_integral e (fun x => f x*x j)
          (hf.aestronglyMeasurable.mul (measurable_pi_apply j).aestronglyMeasurable)
  change ‖gaussianCentroid F‖^2 = _
  calc
    _ = ‖e (gaussianCentroid F)‖^2 := by rw [e.norm_map]
    _ = _ := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp_rw [hcoord]

theorem coordinateRule_centroidEnergy
    (e : FSC.Coord d ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    centroidEnergy (coordinateRule e f) = assignmentFirstEnergy f := by
  unfold centroidEnergy rowEnergy centroidRows assignmentFirstEnergy coordinateRule
  apply Finset.sum_congr rfl
  intro i _
  exact coordinate_centroid_norm_sq e (fun x => f x i) (hf i)
    (fractional_coordinate_bounds f hp i)

/-- Every finite product-Gaussian rule has an actual Euclidean representative
with exactly the same masses and first-chaos energy. -/
theorem exists_feasible_centroid_representation (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    ∃ D : ℕ, ∃ F : FSC.Coord D → ι → ℝ,
      Feasible (assignmentMass f) F ∧ centroidEnergy F = assignmentFirstEnergy f := by
  let D := Module.finrank ℝ (EuclideanSpace ℝ κ)
  let e : FSC.Coord D ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ κ)).repr.symm
  exact ⟨D, coordinateRule e f, coordinateRule_feasible e f hf hp,
    coordinateRule_centroidEnergy e f hf hp⟩

variable {m : ℕ} [NeZero m]

/-- A positive-floor covariance bound controls the actual spectral first energy
of every completed-measurable fractional rule in every finite dimension. -/
theorem assignmentFirstEnergy_bound_of_small_floors
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j, inner ℝ (b i) (b j) = (if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i) = x)
    (f : (κ → ℝ) → Fin m → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
    (hmass : ∀ i, 0 < assignmentMass f i)
    (B δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ C : FSC.Coord d →L[ℝ] FSC.Coord d, C ∈ lowerCovarianceCone ε →
      IsMaxOn (penalizedValue b (assignmentMass f)) (lowerCovarianceCone ε) C →
      penalizedValue b (assignmentMass f) C ≤ B) :
    assignmentFirstEnergy f ≤ B := by
  obtain ⟨D, F, hF, hE⟩ := exists_feasible_centroid_representation f hf hp
  rw [← hE]
  exact centroidEnergy_bound_of_small_floors b hG hP (assignmentMass f) hmass
    (assignmentMass_sum f hf hp) B δ hδ hbound F hF

end NegativeVotingAssignmentCoordinateBridge
