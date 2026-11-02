import GaussianCompetitiveParity
import GaussianMassProfileEnvelope

/-! Actual mass and first-chaos localization data for completed-measure
fractional Gaussian assignments in arbitrary finite dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical RealInnerProductSpace
namespace NegativeVotingFractionalMass
open NegativeVoting NegativeVotingMassCentroid NegativeVotingMassProfileEnvelope
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

def assignmentMass (f : (κ → ℝ) → ι → ℝ) (i : ι) : ℝ :=
  ∫ x, f x i ∂standardGaussian κ

def assignmentFirstEnergy (f : (κ → ℝ) → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (∫ x, x j*f x i ∂standardGaussian κ)^2

def massDeficit (n : ℕ) (f : (κ → ℝ) → Fin (n+2) → ℝ) : ℝ :=
  ∑ i, (assignmentMass f i-1/((n:ℝ)+2))^2

theorem fractional_coordinate_bounds (f : (κ → ℝ) → ι → ℝ)
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) (i : ι) :
    ∀ᵐ x ∂standardGaussian κ, 0 ≤ f x i ∧ f x i ≤ 1 :=
  hp.mono (fun x hx => ⟨hx.1 i,simplex_weight_le_one (f x) hx i⟩)

theorem fractional_coordinate_integrable (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) (i : ι) :
    Integrable (fun x => f x i) (standardGaussian κ) :=
  fractional_integrable _ _ (hf i) (fractional_coordinate_bounds f hp i)

theorem assignmentMass_mem_Icc (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) (i : ι) :
    assignmentMass f i ∈ Icc (0:ℝ) 1 := by
  have hb := fractional_coordinate_bounds f hp i
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ h => h.1),?_⟩
  have h := integral_mono_ae (fractional_coordinate_integrable f hf hp i)
    (integrable_const (1:ℝ)) (hb.mono fun _ h => h.2)
  simpa [assignmentMass] using h

theorem assignmentMass_sum (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    (∑ i, assignmentMass f i)=1 := by
  unfold assignmentMass
  rw [←integral_finsetSum Finset.univ (fun i _ => fractional_coordinate_integrable f hf hp i)]
  calc
    _ = ∫ _ : κ → ℝ, (1:ℝ) ∂standardGaussian κ :=
      integral_congr_ae (hp.mono fun _ h => h.2)
    _ = 1 := by simp

theorem mass_deviations_sum (n : ℕ) (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    (∑ i, (assignmentMass f i-1/((n:ℝ)+2)))=0 := by
  rw [Finset.sum_sub_distrib,assignmentMass_sum f hf hp]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  field_simp <;> ring

theorem massDeficit_eq (n : ℕ) (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    massDeficit n f=(∑ i, (assignmentMass f i)^2)-1/((n:ℝ)+2) := by
  have h (i : Fin (n+2)) : (assignmentMass f i-1/((n:ℝ)+2))^2=
      (assignmentMass f i)^2-(2/((n:ℝ)+2))*assignmentMass f i+(1/((n:ℝ)+2))^2 := by ring
  unfold massDeficit
  simp_rw [h]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
    assignmentMass_sum f hf hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  field_simp <;> ring

theorem gaussian_ofLp_measurePreserving :
    MeasurePreserving (fun x : EuclideanSpace ℝ κ => x.ofLp)
      (stdGaussian (EuclideanSpace ℝ κ)) (standardGaussian κ) := by
  refine ⟨by fun_prop,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,Measure.map_id']

theorem gaussian_ofLp_integral (g : (κ → ℝ) → ℝ)
    (hg : AEStronglyMeasurable g (standardGaussian κ)) :
    (∫ x : EuclideanSpace ℝ κ, g x.ofLp ∂stdGaussian (EuclideanSpace ℝ κ))=
      ∫ x, g x ∂standardGaussian κ := by
  have hm := gaussian_ofLp_measurePreserving (κ:=κ)
  have hs : AEStronglyMeasurable g
      ((stdGaussian (EuclideanSpace ℝ κ)).map (fun x => x.ofLp)) := by
    simpa only [hm.map_eq] using hg
  simpa only [hm.map_eq] using (integral_map hm.measurable.aemeasurable hs).symm

/-- A literal squared first-coordinate moment is bounded by the sharp profile.
The Euclidean vector centroid and its coordinate integrals are identified. -/
theorem fractional_coordinate_energy_le_profile (f : (κ → ℝ) → ℝ)
    (hf : AEMeasurable f (standardGaussian κ))
    (h01 : ∀ᵐ x ∂standardGaussian κ, 0 ≤ f x ∧ f x ≤ 1) :
    (∑ j, (∫ x, x j*f x ∂standardGaussian κ)^2) ≤
      gaussianMassProfile (∫ x, f x ∂standardGaussian κ)^2 := by
  let F : EuclideanSpace ℝ κ → ℝ := fun x => f x.ofLp
  have hm := gaussian_ofLp_measurePreserving (κ:=κ)
  have hF : AEMeasurable F (stdGaussian (EuclideanSpace ℝ κ)) :=
    (hf.aestronglyMeasurable.comp_measurePreserving hm).aemeasurable
  have hF01 : ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ κ), 0 ≤ F x ∧ F x ≤ 1 :=
    hm.quasiMeasurePreserving.ae h01
  have hV := fractional_vector_integrable F hF hF01
  have hcoord (j : κ) : (NegativeVotingMassCentroid.gaussianCentroid F) j=
      ∫ x, x j*f x ∂standardGaussian κ := by
    change (EuclideanSpace.proj (𝕜:=ℝ) j)
      (∫ x, F x • x ∂stdGaussian (EuclideanSpace ℝ κ))=_
    rw [←(EuclideanSpace.proj (𝕜:=ℝ) j).integral_comp_comm hV]
    change (∫ x : EuclideanSpace ℝ κ, F x*x j ∂stdGaussian (EuclideanSpace ℝ κ))=_
    simpa only [F,mul_comm] using gaussian_ofLp_integral (fun x => f x*x j)
      (hf.aestronglyMeasurable.mul (measurable_pi_apply j).aestronglyMeasurable)
  have hnorm : ‖NegativeVotingMassCentroid.gaussianCentroid F‖^2=
      ∑ j, (∫ x, x j*f x ∂standardGaussian κ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [hcoord]
  have hbound := gaussianCentroid_norm_le_profile F hF hF01
  have hmass : (∫ x, F x ∂stdGaussian (EuclideanSpace ℝ κ))=
      ∫ x, f x ∂standardGaussian κ := gaussian_ofLp_integral f hf.aestronglyMeasurable
  rw [hmass] at hbound
  nlinarith [norm_nonneg (NegativeVotingMassCentroid.gaussianCentroid F)]

theorem assignmentFirstEnergy_le_profiles (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    assignmentFirstEnergy f ≤ ∑ i, gaussianMassProfile (assignmentMass f i)^2 := by
  apply Finset.sum_le_sum
  intro i _
  exact fractional_coordinate_energy_le_profile (fun x => f x i) (hf i)
    (fractional_coordinate_bounds f hp i)

/-- Actual first-chaos energy has the manuscript's global quadratic mass
upper envelope, with no dimension or positive-cell-mass restriction. -/
theorem assignmentFirstEnergy_le_envelope (n : ℕ) (hn : 0 < n)
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    assignmentFirstEnergy f ≤ centroidEnvelope n+curvatureBound n*massDeficit n f := by
  apply (assignmentFirstEnergy_le_profiles f hf hp).trans
  calc
    _ ≤ ∑ i : Fin (n+2), (gaussianMassProfile (1/((n:ℝ)+2))^2+
        (2*NegativeVotingGaussianMaximum.upperQuantile n*
          WeakSimplex.normalPDF (NegativeVotingGaussianMaximum.upperQuantile n))*
            (assignmentMass f i-1/((n:ℝ)+2))+
        curvatureBound n*(assignmentMass f i-1/((n:ℝ)+2))^2) := by
      exact Finset.sum_le_sum (fun i _ => gaussianMassProfile_square_envelope n hn _
        (assignmentMass_mem_Icc f hf hp i))
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,mass_deviations_sum n f hf hp,
        mul_zero,add_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_ofNat,gaussianMassProfile_uniform,centroidEnvelope,massDeficit]

end NegativeVotingFractionalMass
