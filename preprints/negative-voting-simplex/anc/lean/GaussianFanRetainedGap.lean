import GaussianFanRetainedCuts
import GaussianFiniteGraphRayleigh
import GaussianCovarianceMixedEstimate

/-! The actual retained Gaussian graph has a quantitative Rayleigh gap.
Its graph estimate discharges the mixed-curvature theorem's Rayleigh premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanRetained
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFiniteGraph
  NegativeVotingFiniteGraphRayleigh NegativeVotingCovarianceMixed
  NegativeVotingFanCanonicalOffset NegativeVotingFanCovarianceEnvelope
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The two proved geometric constants are retained: 2π in the cut bound and
32 in the post-deletion graph inequality. ellMax is an edge-length ceiling. -/
def retainedGapCoefficient (p0 ellMax D : ℝ) : ℝ :=
  (p0/(2*Real.pi*ellMax))^2/(32*D)

theorem retainedGapCoefficient_pos (p0 ellMax D : ℝ)
    (hp : 0<p0) (hell : 0<ellMax) (hD : 0<D) :
    0<retainedGapCoefficient p0 ellMax D := by
  unfold retainedGapCoefficient
  positivity

/-- Actual winning masses, edge lengths and degree bounds imply a retained
Rayleigh gap; there is no expansion or spectral-gap premise. -/
theorem gaussian_retained_rayleigh (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (p0 ellMax τ D : ℝ)
    (hp0 : 0 ≤ p0) (hell : 0<ellMax) (hτ : 0 ≤ τ) (hDpos : 0<D)
    (hmass : ∀i,p0 ≤ mass B h i) (hedge : ∀i j,i≠j→‖B i-B j‖ ≤ ellMax)
    (hD : ∀i,(∑j,facetWeight B h i j) ≤ D)
    (ht : τ*(Fintype.card V:ℝ) ≤ (p0/(2*Real.pi*ellMax))/2)
    (v : V → ℝ) (hv : ∑i,v i=0) :
    retainedGapCoefficient p0 ellMax D*(∑i,(v i)^2)  ≤ 
      (1/2:ℝ)*∑i,∑j,retainedWeight (facetWeight B h) τ i j*(v i-v j)^2 := by
  let w := retainedWeight (facetWeight B h) τ
  let k := (p0/(2*Real.pi*ellMax))/2
  have hw : ∀i j,0 ≤ w i j := retainedWeight_nonneg _ (facetWeight_nonneg B h) τ
  have hs : ∀i j,w i j=w j i := retainedWeight_symm _ (facetWeight_symm B h) τ
  have hk : 0 ≤ k := by dsimp [k];positivity
  have hc : ∀S : Finset V,k*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ cutWeight w S :=
    gaussian_retained_cut_expansion B h hinj p0 ellMax τ hp0 hell hτ hmass hedge ht
  have hr := rayleigh_coefficient_of_ordered_l1 w hw hs k D hk hDpos
    (retained_degree_le _ (facetWeight_nonneg B h) τ D hD)
    (weighted_l1_of_cut w k hk hs hc) v hv
  convert hr using 1 <;> dsimp [retainedGapCoefficient,k,w] <;> ring

/-- The Rayleigh lower bound uses precisely the retained energy in the actual
covariance-Hessian mixed estimate. Affine-basis injectivity is derived. -/
theorem affine_retained_energy_gap (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (p0 ellMax τ D : ℝ) (hp0 : 0 ≤ p0) (hell : 0<ellMax) (hτ : 0 ≤ τ) (hDpos : 0<D)
    (hmass : ∀i,p0 ≤ mass b h i) (hedge : ∀i j,i≠j→‖b i-b j‖ ≤ ellMax)
    (hD : ∀i,(∑j,facetWeight b h i j) ≤ D)
    (ht : τ*(Fintype.card V:ℝ) ≤ (p0/(2*Real.pi*ellMax))/2)
    (v : V → ℝ) (hv : ∑i,v i=0) :
    retainedGapCoefficient p0 ellMax D*(∑i,(v i)^2) ≤ retainedOffsetEnergy b h τ v := by
  have hh := gaussian_retained_rayleigh b h b.ind.injective p0 ellMax τ D
    hp0 hell hτ hDpos hmass hedge hD ht v hv
  simpa only [retainedOffsetEnergy,retainedWeight,ite_mul,zero_mul] using hh

/-- The retained-graph premise in mixed offset control is discharged by
actual Gaussian cell, edge, degree and threshold inequalities. -/
theorem canonicalOffset_control_from_actual_graph
    (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (hcard : 3 ≤ Fintype.card V)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (p0 ellMax τ D K : ℝ)
    (hp0 : 0 ≤ p0) (hell : 0<ellMax) (hτ : 0 ≤ τ) (hDpos : 0<D) (hK : 0 ≤ K)
    (hmass : ∀i,p0 ≤ mass b h i) (hedge : ∀i j,i≠j→‖b i-b j‖ ≤ ellMax)
    (hD : ∀i,(∑j,facetWeight b h i j) ≤ D)
    (ht : τ*(Fintype.card V:ℝ) ≤ (p0/(2*Real.pi*ellMax))/2)
    (hcoeff : ∀i j,i≠j→τ ≤ facetWeight b h i j→
      1/facetLogCoefficient b h i j+(NegativeVotingWeightedFacet.pairOffset b h i j)^2 ≤ K) :
    retainedGapCoefficient p0 ellMax D*
      (∑i,(canonicalOffsetVariation b h (rowsOfOperator b H) i/2)^2) ≤ 
        K*(-covarianceHessianValue b h H) :=
  canonicalOffset_half_sq_le_curvature b h hcard H τ K _ hK hcoeff
    (affine_retained_energy_gap b h p0 ellMax τ D hp0 hell hτ hDpos hmass hedge hD ht)

end NegativeVotingFanRetained
