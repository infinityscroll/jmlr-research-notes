import GaussianSwitchingCellCoordinates
import GaussianFacetDegree

/-! Complete actual old-cell pair bound: exact facet trace, geometric escape,
normal-envelope tail and ambient far-normal tail. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Classical ENNReal
namespace NegativeVotingSwitchingPair
open NegativeVotingFan NegativeVotingCapTail NegativeVotingWeightedFacet
  NegativeVotingDisintegration NegativeVotingFacetDegree NegativeVotingSwitchingCell
  NegativeVotingSwitchingFibre NegativeVotingSwitchingFibreIntegration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V]

def pairPlaneBase (B : V → E) (h : V → ℝ) (i j : V) : E :=
  pairOffset B h i j • pairNormal B i j

def pairPlaneForcing (B : V → E) (h : V → ℝ) (i j : V) (v : E → V → ℝ)
    (y : ((ℝ ∙ (B i-B j))ᗮ)) (z : ℝ) : ℝ :=
  v (pairPlaneBase B h i j+(y:E)+z • pairNormal B i j) i+
    v (pairPlaneBase B h i j+(y:E)+z • pairNormal B i j) j

def pairPlaneFacet (B : V → E) (h : V → ℝ) (i j : V) : Set ((ℝ ∙ (B i-B j))ᗮ) :=
  {y | pairPlaneBase B h i j+(y:E) ∈ affineFacet B h i j}

theorem pairPlaneBase_on_plane (B : V → E) (h : V → ℝ) (i j : V) (hij : B i ≠ B j) :
    affineScore B h i (pairPlaneBase B h i j)=affineScore B h j (pairPlaneBase B h i j) := by
  simpa only [facetChart,Submodule.coe_zero,zero_add,pairPlaneBase] using
    facetChart_on_pair_plane B h i j hij (0 : tangentSpace (pairNormal B i j))

theorem pairPlaneForcing_measurable (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (hv : Measurable (fun x => v x i+v x j)) :
    Measurable (Function.uncurry (pairPlaneForcing B h i j v)) := by
  have hc : Continuous (fun q : ((ℝ ∙ (B i-B j))ᗮ)×ℝ =>
      pairPlaneBase B h i j+(q.1:E)+q.2 • pairNormal B i j) := by fun_prop
  exact hv.comp hc.measurable

/-- The left side is the original ambient Gaussian reward on one old cell.
Every error term is explicit and retains its genuine amplitude power. -/
theorem integral_cellReward_pair_bound
    (B : V → E) (h : V → ℝ) (i j : V) (hij : i ≠ j)
    (σ D : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hD : ∀ k ∈ thirdLabels i j, ‖B i-B k‖ ≤ D)
    (v : E → V → ℝ) (hvM : Measurable (fun x => v x i+v x j))
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E))
    (θ M : ℝ) (hθ : 0 ≤ θ) (hM : 0 < M)
    (hη1 : θ*M/‖B i-B j‖ ≤ 1)
    (hsmall : (1+|pairOffset B h i j|)*(θ*M/‖B i-B j‖) ≤ 1/2)
    (W : ((ℝ ∙ (B i-B j))ᗮ) → ℝ) (hWM : Measurable W)
    (hW : MemLp W 32 (stdGaussian _)) (hW0 : ∀ y, 0 ≤ W y)
    (hcontrol : ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (pairPlaneForcing B h i j v y) (Icc (0:ℝ) 1) ∧
      (∀ z ∈ Icc (0:ℝ) 1, pairPlaneForcing B h i j v y z ≤ W y) ∧
      (∀ z ∈ Icc (0:ℝ) 1, |pairPlaneForcing B h i j v y z-
        pairPlaneForcing B h i j v y 0| ≤ W y*z)) :
    (∫ x,cellReward B h i j v θ x ∂stdGaussian E) ≤
      (gaussianPDFReal 0 1 (pairOffset B h i j)*θ^2/(2*‖B i-B j‖))*
        (∫ y in pairPlaneFacet B h i j, (max (pairPlaneForcing B h i j v y 0) 0)^2 ∂stdGaussian _) +
      (gaussianPDFReal 0 1 (pairOffset B h i j)*θ^2/(2*‖B i-B j‖))*M^2*
        (((Fintype.card V-2:ℕ):ℝ)*((θ*M/‖B i-B j‖)*D)/
          (Real.sqrt (2*Real.pi)*σ*Real.sqrt (3/2))) +
      gaussianPDFReal 0 1 (pairOffset B h i j)*(2+|pairOffset B h i j|)*θ^3*M^3/‖B i-B j‖^2 +
      θ*(M^31)⁻¹*(∫ y,W y^32 ∂stdGaussian _)+
      (θ^32/‖B i-B j‖^31)*(∫ x,|v x i+v x j|^32 ∂stdGaussian E) := by
  have hBi := centered_singular_rows_ne B σ hσ hlower i j hij
  have hell : 0 < ‖B i-B j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hBi)
  have hb := integral_unit_cell_reward_explicit_bound B h i j (pairPlaneBase B h i j)
    (pairNormal B i j) (pairPlaneForcing B h i j v) (pairOffset B h i j) θ M ‖B i-B j‖
    σ D hσ hlower hij (pairNormal_norm B i j hBi).le (pairPlaneBase_on_plane B h i j hBi) hD
    hθ hM hell hη1 hsmall (pairPlaneForcing_measurable B h i j v hvM) W hWM hW hW0 hcontrol
  have hn := integral_nearCellReward_edge_normal B h i j hBi v θ hθ hv
  have hc := integral_cellReward_le_near_add_power B h i j v θ ‖B i-B j‖ hθ hell hv
  rw [hn] at hc
  change (∫ x,cellReward B h i j v θ x ∂stdGaussian E) ≤ _ at hc
  change (∫ y : ((ℝ ∙ (B i-B j))ᗮ),unitCellReward B h i
    (pairPlaneBase B h i j+(y:E)) (pairNormal B i j) (pairPlaneForcing B h i j v y)
    (pairOffset B h i j) θ ‖B i-B j‖ ∂stdGaussian _) ≤ _ at hb
  exact hc.trans (add_le_add hb le_rfl)

end NegativeVotingSwitchingPair
