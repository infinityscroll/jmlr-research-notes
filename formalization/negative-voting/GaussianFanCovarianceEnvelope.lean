import GaussianFanEnvelope
import GaussianFanCanonicalOffset
import GaussianCovariancePathRegularity

/-! The true covariance-path envelope Hessian with its optimized-offset term.
All differential expressions are attached to the actual Gaussian potential. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanCovarianceEnvelope
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanGradient
  NegativeVotingFanHessian NegativeVotingFanEnvelope NegativeVotingFanCentroid
  NegativeVotingFanOffsetMinimization NegativeVotingFanJacobian NegativeVotingFacetDegree
  NegativeVotingCovariancePath NegativeVotingCapTail NegativeVotingFanCanonicalOffset
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Evaluate an actual operator simultaneously at all fan sites. -/
def rowsOfOperator (B : Rows d ι) :
    (FSC.Coord d →L[ℝ] FSC.Coord d) →L[ℝ] Rows d ι :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ (FSC.Coord d) (B i))

@[simp] theorem rowsOfOperator_apply (B : Rows d ι)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) : rowsOfOperator B A = fun i => A (B i) := rfl

/-- The exact negative interior term, including the ordered-edge factor. -/
theorem covariance_interior (B : Rows d ι) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    jointDerivative B h (rowsOfOperator B ((-1/4 : ℝ) • H.comp H),0) =
      (-1/8 : ℝ) * ∑ i, ∑ j, facetWeight B h i j * ‖H (B i-B j)‖^2 := by
  rw [jointDerivative_apply]
  simp only [rowsOfOperator_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Pi.zero_apply, mul_zero, add_zero, real_inner_smul_left]
  have he : (∑ i, inner ℝ (H (H (B i))) (centroid B h i)) =
      ∑ i, inner ℝ (centroid B h i) (H (H (B i))) :=
    Finset.sum_congr rfl (fun i _ => real_inner_comm _ _)
  have hs := centroid_symmetric_square_pairing B h σ hσ hlower H.toLinearMap hH
  change (∑ i, inner ℝ (centroid B h i) (H (H (B i)))) =
    (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * ‖H (B i-B j)‖^2 at hs
  rw [← Finset.mul_sum, he, hs]
  ring

/-- A differentiable path preserving the actual masses gives the global
minimizer of the single common offset quadratic form. -/
theorem mass_path_offset_minimizes (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (q : ℝ → Parameters d ι) (u : Parameters d ι)
    (hq0 : q 0 = (B,h)) (hq : HasDerivAt q u 0)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (q t).1 (q t).2 = p) :
    ∀ w : ι → ℝ, quadraticForm B h u.1 u.2 ≤ quadraticForm B h u.1 w := by
  apply quadraticForm_offset_minimizes B u.1 h u.2 σ hσ hlower
  intro i
  have hz := hessian_offset_zero_of_mass_path B h p σ hσ hlower q u hq0 hq hm (Pi.single i 1)
  rw [jointHessian_apply B h σ hσ hlower] at hz
  simpa only [hz] using hasDerivAt_mass_line B u.1 h u.2 σ hσ hlower i

/-- Every rescaling of an actual mass-preserving tangent has zero literal
cell-mass derivatives on the corresponding affine parameter line. -/
theorem mass_path_mass_derivatives_zero (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (q : ℝ → Parameters d ι) (u : Parameters d ι)
    (hq0 : q 0 = (B,h)) (hq : HasDerivAt q u 0)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (q t).1 (q t).2 = p) (c : ℝ) :
    ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•(c•u.1)) (h+t•(c•u.2)) i) 0 0 := by
  intro i
  have hz := hessian_offset_zero_of_mass_path B h p σ hσ hlower q u hq0 hq hm (Pi.single i 1)
  rw [jointHessian_apply B h σ hσ hlower] at hz
  have hd := hasDerivAt_mass_line B (c•u.1) h (c•u.2) σ hσ hlower i
  rw [mixedForm_smul_left B u.1 0 h u.2 (Pi.single i 1) σ hσ hlower c, hz, mul_zero] at hd
  exact hd

/-- The covariance derivative determines an actual zero-mass tangent with
row velocity H B and offset velocity twice the curve's offset derivative. -/
theorem covariance_mass_derivatives_zero
    (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (a : ℝ → ι → ℝ) (v : ι → ℝ)
    (hS0 : S 0 = ContinuousLinearMap.id ℝ (FSC.Coord d)) (ha0 : a 0 = h)
    (hS1 : HasDerivAt S ((1/2:ℝ) • H) 0) (ha : HasDerivAt a v 0)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (rowsOfOperator B (S t)) (a t) = p) :
    ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•rowsOfOperator B H) (h+t•((2:ℝ)•v)) i) 0 0 := by
  let q : ℝ → Parameters d ι := fun t => (rowsOfOperator B (S t),a t)
  have hq0 : q 0 = (B,h) := by simp [q, hS0, ha0]
  have hq : HasDerivAt q ((1/2:ℝ) • rowsOfOperator B H,v) 0 := by
    simpa only [map_smul, q, Function.comp_def] using
      ((rowsOfOperator B).hasFDerivAt.comp_hasDerivAt 0 hS1).prodMk ha
  have hz := mass_path_mass_derivatives_zero B h p σ hσ hlower q _ hq0 hq hm 2
  have hc : (2:ℝ)*(1/2)=1 := by norm_num
  simpa only [smul_smul, hc, one_smul] using hz

/-- Covariance jet evaluated on the actual mass-preserving curve. -/
theorem hasDerivAt_deriv_covariance_potential
    (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (a : ℝ → ι → ℝ)
    (hS0 : S 0 = ContinuousLinearMap.id ℝ (FSC.Coord d)) (ha0 : a 0 = h)
    (hS1 : HasDerivAt S ((1/2:ℝ) • H) 0)
    (hS2 : HasDerivAt (deriv S) ((-1/4:ℝ) • H.comp H) 0)
    (hS : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt S (deriv S t) t)
    (ha : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt a (deriv a t) t)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (rowsOfOperator B (S t)) (a t) = p) :
    HasDerivAt (deriv (fun t : ℝ => potential (rowsOfOperator B (S t)) p (a t)))
      ((1/4:ℝ) * (quadraticForm B h (rowsOfOperator B H) ((2:ℝ) • deriv a 0) -
        (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * ‖H (B i-B j)‖^2)) 0 := by
  let q : ℝ → Parameters d ι := fun t => (rowsOfOperator B (S t),a t)
  let q' : ℝ → Parameters d ι := fun t => (rowsOfOperator B (deriv S t),deriv a t)
  have hq0 : q 0 = (B,h) := by simp [q, hS0, ha0]
  have hq : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt q (q' t) t := by
    filter_upwards [hS,ha] with t ht hat
    exact ((rowsOfOperator B).hasFDerivAt.comp_hasDerivAt t ht).prodMk hat
  have hr : HasDerivAt (fun t => (q' t).1)
      (rowsOfOperator B ((-1/4:ℝ) • H.comp H)) 0 :=
    (rowsOfOperator B).hasFDerivAt.comp_hasDerivAt 0 hS2
  have hd := hasDerivAt_deriv_potential_path B h p σ hσ hlower q q'
    (rowsOfOperator B ((-1/4:ℝ) • H.comp H)) hq0 hq hm hr
  have hq' : (q' 0).1 = (1/2:ℝ) • rowsOfOperator B H := by
    simp [q',hS1.deriv]
  have hscale : quadraticForm B h (q' 0).1 (q' 0).2 =
      (1/4:ℝ) * quadraticForm B h (rowsOfOperator B H) ((2:ℝ) • deriv a 0) := by
    rw [hq']
    have hs := quadraticForm_smul B (rowsOfOperator B H) h ((2:ℝ) • deriv a 0) σ hσ hlower (1/2)
    norm_num only [smul_smul, one_smul] at hs
    exact hs
  rw [hscale, covariance_interior B h σ hσ hlower H hH] at hd
  convert hd using 1 <;> dsimp [q] <;> ring

/-- The actual covariance Hessian after eliminating all offset variables. -/
def covarianceHessianValue (B : Rows d ι) (h : ι → ℝ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) : ℝ :=
  (1/4:ℝ) * (quadraticForm B h (rowsOfOperator B H) 0 -
    rowMassVariation B h (rowsOfOperator B H) ⬝ᵥ
      ((offsetJacobian B h).covariancePseudoInverse *ᵥ rowMassVariation B h (rowsOfOperator B H)) -
    (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * ‖H (B i-B j)‖^2)

/-- The canonical pseudoinverse expression is the derivative of the actual
covariance potential along the actual prescribed-mass path. -/
theorem hasDerivAt_deriv_covariance_potential_canonical
    (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (a : ℝ → ι → ℝ)
    (hS0 : S 0 = ContinuousLinearMap.id ℝ (FSC.Coord d)) (ha0 : a 0 = h)
    (hS1 : HasDerivAt S ((1/2:ℝ) • H) 0)
    (hS2 : HasDerivAt (deriv S) ((-1/4:ℝ) • H.comp H) 0)
    (hS : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt S (deriv S t) t)
    (ha : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt a (deriv a t) t)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (rowsOfOperator B (S t)) (a t) = p) :
    HasDerivAt (deriv (fun t : ℝ => potential (rowsOfOperator B (S t)) p (a t)))
      (covarianceHessianValue B h H) 0 := by
  have hline := covariance_mass_derivatives_zero B h p σ hσ hlower H S a (deriv a 0)
    hS0 ha0 hS1 ha.self_of_nhds hm
  have he := mass_preserving_offset_elimination_formula B (rowsOfOperator B H)
    h ((2:ℝ) • deriv a 0) σ hσ hlower hline
  have hd := hasDerivAt_deriv_covariance_potential B h p σ hσ hlower H hH S a
    hS0 ha0 hS1 hS2 hS ha hm
  simpa only [covarianceHessianValue, he] using hd

end NegativeVotingFanCovarianceEnvelope
