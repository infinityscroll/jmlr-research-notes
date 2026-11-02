import GaussianBoundaryTraceAggregation
import GaussianBoundaryHighChaosTrace
import GaussianFanMassJacobian

/-! Actual Gaussian winning-fan OU traces. All plane symmetry and separation
are derived from the rows, and the degree is then discharged from actual
cell masses and Gram/singular geometry. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanOUTrace
open NegativeVotingFan NegativeVotingFacetDegree NegativeVotingWeightedFacet
  NegativeVotingDisintegration NegativeVotingFanJacobian
  NegativeVotingBoundaryTraceAggregation NegativeVotingActualFacetOUTrace
  NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def fanSurfaceMass (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) : ℝ :=
  planeSurfaceMass (pairNormal B) (pairOffset B h) (intrinsicFacet B h) i j

theorem fanSurfaceMass_div_edge (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) :
    fanSurfaceMass B h i j/‖B i-B j‖=facetWeight B h i j := by
  unfold fanSurfaceMass planeSurfaceMass facetWeight
  ring

theorem fanSurfaceMass_symm (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hB : Function.Injective B) (i j : ι) : fanSurfaceMass B h i j=fanSurfaceMass B h j i := by
  by_cases hij : i=j
  · subst j; rfl
  have hn : ‖B i-B j‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hB.ne hij))
  have hh := facetWeight_symm B h i j
  rw [←fanSurfaceMass_div_edge,←fanSurfaceMass_div_edge,norm_sub_rev (B j) (B i)] at hh
  exact (div_left_inj' hn).mp hh

def fanTraceEnergy (B : ι→FSC.Coord d) (h : ι→ℝ) (τ : ℝ)
    (f : ι→FSC.Coord d→ℝ) : ℝ :=
  ∑ i,∑ j∈Finset.univ.erase i,
    gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
      ∫ y in intrinsicFacet B h i j,
        (ambientAverage τ (fun x=>f i x-f j x)
          ((y:FSC.Coord d)+pairOffset B h i j • pairNormal B i j))^2
        ∂stdGaussian (tangentSpace (pairNormal B i j))

theorem fanTraceEnergy_le_of_degree (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (τ q G : ℝ) (hτ : 0<τ) (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hG : 0 ≤ G)
    (hdegree : ∀ i,intrinsicWeightedDegree B h i ≤ G)
    (f : ι→FSC.Coord d→ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d))) :
    fanTraceEnergy B h τ f  ≤  8*traceCoefficient (ι:=ι) σ G q*
      ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hB : Function.Injective B := fun i j hh=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij hh
  apply ambient_ordered_trace_energy_le
    (n := fun i j=>Module.finrank ℝ (tangentSpace (pairNormal B i j)))
    (pairNormal B) (pairOffset B h) (fun i j=>‖B i-B j‖) (intrinsicFacet B h)
    (fun i j _=>canonicalTangentCoordinates (pairNormal B i j))
    τ q σ G hτ hq ht hσ hG
    (fun i j hij=>pairNormal_norm B i j (hB.ne hij))
    (fun i j _=>(isClosed_intrinsicFacet B h i j).measurableSet)
    (fun i j hij=>centered_singular_pair_norm_lower B σ hσ hlower i j hij)
    (fanSurfaceMass_symm B h hB) (fun i j=>norm_sub_rev _ _)
    (fun i=>by
      change (∑ j ∈ Finset.univ.erase i, fanSurfaceMass B h i j/‖B i-B j‖) ≤ G
      simp_rw [fanSurfaceMass_div_edge]
      exact hdegree i) f hfM hf

/-- All trace geometry comes from the actual initial fan. -/
theorem fanTraceEnergy_le_of_gram (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ α : ℝ) (hσ : 0<σ) (hα : 0<α) (hlower : CenteredSingularLowerBound B σ)
    (e m L C : ℝ) (he : 0<e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L)
    (hC : 0 ≤ C) (hScale : e*Real.sqrt L/m ≤ σ)
    (hDiagLower : ∀ i,α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ i,inner ℝ (B i) (B i) ≤ 2*α^2)
    (hCross : ∀ i j,j≠i→inner ℝ (B j) (B i) ≤ α^2/4)
    (hmass : ∀ i,(stdGaussian (FSC.Coord d) (affineCell B h i)).toReal ≤ C/m)
    (τ q : ℝ) (hτ : 0<τ) (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1))
    (hqlog : Real.log ((Fintype.card ι:ℝ)/σ) ≤ q)
    (f : ι→FSC.Coord d→ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d))) :
    fanTraceEnergy B h τ f  ≤ 
      8*Real.exp 1*max 1 (32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*
        ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  let G := 32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e
  have hG : 0 ≤ G := by unfold G; positivity
  have hh := fanTraceEnergy_le_of_degree B h σ hσ hlower τ q G hτ hq ht hG
    (fun i=>intrinsicWeightedDegree_uniform_of_gram B h σ α hσ hα hlower i e m L C
      he hm hL hlog hC hScale (hDiagLower i) hDiagUpper (hCross i) (hmass i)) f hfM hf
  have hc := traceCoefficient_le_exp (ι:=ι) σ G q hσ hG (by linarith)
    (by exact_mod_cast Fintype.card_pos) hqlog
  have hE : 0  ≤  ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) :=
    Finset.sum_nonneg (fun i _=>integral_nonneg (fun _=>sq_nonneg _))
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hc hE])

/-- Actual winning-fan trace for arbitrary high-chaos input, with its original
Euclidean-coordinate Hermite vanishing. No plane-wise premise is assumed. -/
theorem fanTraceEnergy_highChaos_le_of_degree (B : ι→FSC.Coord d) (h : ι→ℝ)
    (ell0 : ℝ) (hell0 : 0 < ell0) (hlower : CenteredSingularLowerBound B ell0)
    (τ σ q G : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hG : 0 ≤ G)
    (hdegree : ∀ i,intrinsicWeightedDegree B h i ≤ G)
    (f : ι→FSC.Coord d→ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b,OAI.MinUncut.GaussianHermite.degree b < k →
      OAI.MinUncut.GaussianHermite.coeff (fun x : Fin d→ℝ=>f i (WithLp.toLp 2 x)) b=0) :
    fanTraceEnergy B h (τ*σ) f ≤ 8*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*
      ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hB : Function.Injective B := fun i j hh=>by
    by_contra hij
    exact centered_singular_rows_ne B ell0 hell0 hlower i j hij hh
  apply NegativeVotingBoundaryHighChaosTrace.ambient_ordered_highChaos_trace_energy_le
    (n := fun i j=>Module.finrank ℝ (tangentSpace (pairNormal B i j)))
    (pairNormal B) (pairOffset B h) (fun i j=>‖B i-B j‖) (intrinsicFacet B h)
    (fun i j _=>canonicalTangentCoordinates (pairNormal B i j))
    τ σ q ell0 G hτ hσ hσ1 hq ht hell0 hG
    (fun i j hij=>pairNormal_norm B i j (hB.ne hij))
    (fun i j _=>(isClosed_intrinsicFacet B h i j).measurableSet)
    (fun i j hij=>centered_singular_pair_norm_lower B ell0 hell0 hlower i j hij)
    (fanSurfaceMass_symm B h hB) (fun i j=>norm_sub_rev _ _)
    (fun i=>by
      change (∑ j ∈ Finset.univ.erase i, fanSurfaceMass B h i j/‖B i-B j‖) ≤ G
      simp_rw [fanSurfaceMass_div_edge]
      exact hdegree i) f hfM hf k hvanish

/-- Geometry-discharge version of the full high-chaos restriction estimate. -/
theorem fanTraceEnergy_highChaos_le_of_gram (B : ι→FSC.Coord d) (h : ι→ℝ)
    (ell0 α : ℝ) (hell0 : 0 < ell0) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound B ell0)
    (e m L C : ℝ) (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L)
    (hC : 0 ≤ C) (hScale : e*Real.sqrt L/m ≤ ell0)
    (hDiagLower : ∀ i,α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ i,inner ℝ (B i) (B i) ≤ 2*α^2)
    (hCross : ∀ i j,j≠i→inner ℝ (B j) (B i) ≤ α^2/4)
    (hmass : ∀ i,(stdGaussian (FSC.Coord d) (affineCell B h i)).toReal ≤ C/m)
    (τ σ q : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1))
    (hqlog : Real.log ((Fintype.card ι:ℝ)/ell0) ≤ q)
    (f : ι→FSC.Coord d→ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b,OAI.MinUncut.GaussianHermite.degree b < k →
      OAI.MinUncut.GaussianHermite.coeff (fun x : Fin d→ℝ=>f i (WithLp.toLp 2 x)) b=0) :
    fanTraceEnergy B h (τ*σ) f ≤
      8*Real.exp 1*max 1 (32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*(σ^2)^k*
        ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  let G := 32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e
  have hG : 0 ≤ G := by unfold G; positivity
  have hh := fanTraceEnergy_highChaos_le_of_degree B h ell0 hell0 hlower τ σ q G
    hτ hσ hσ1 hq ht hG
    (fun i=>intrinsicWeightedDegree_uniform_of_gram B h ell0 α hell0 hα hlower i e m L C
      he hm hL hlog hC hScale (hDiagLower i) hDiagUpper (hCross i) (hmass i))
    f hfM hf k hvanish
  have hc := traceCoefficient_le_exp (ι:=ι) ell0 G q hell0 hG (by linarith)
    (by exact_mod_cast Fintype.card_pos) hqlog
  have hE : 0 ≤ (σ^2)^k*∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) :=
    mul_nonneg (pow_nonneg (sq_nonneg σ) k)
      (Finset.sum_nonneg (fun i _=>integral_nonneg (fun _=>sq_nonneg _)))
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hc hE])

end NegativeVotingFanOUTrace
