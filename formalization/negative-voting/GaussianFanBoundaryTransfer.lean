import GaussianFanCutFrontier
import GaussianWeightedFacetEnergy

/-! Actual affine-fan cut boundary bounds in the intrinsic Gaussian facet normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology RealInnerProductSpace BigOperators
namespace NegativeVotingFanBoundary
open NegativeVotingFan NegativeVotingWeightedFacet NegativeVotingDisintegration
open NegativeVotingGaussianTube
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance : (p : Prop) → Decidable p := Classical.propDecidable

theorem facetChart_projection_eq (B : V → E) (h : V → ℝ) (i j : V)
    (hij : B i ≠ B j) (x : E)
    (hx : ⟪pairNormal B i j,x⟫=pairOffset B h i j) :
    facetChart B h i j ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x)=x := by
  change ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x : E)+
    pairOffset B h i j • pairNormal B i j=x
  rw [← hx]
  exact normalReconstruct_tangentNormal _ (pairNormal_norm B i j hij) x

theorem affineFacet_eq_planePatch (B : V → E) (h : V → ℝ) (i j : V)
    (hij : B i ≠ B j) :
    affineFacet B h i j = planePatch (pairNormal B i j) (pairOffset B h i j)
      (intrinsicFacet B h i j) := by
  ext x
  constructor
  · intro hx
    have hg : ⟪B i-B j,x⟫=h j-h i := by
      have he := hx.1
      unfold affineScore at he
      rw [inner_sub_left]
      linarith
    have hn : ⟪pairNormal B i j,x⟫=pairOffset B h i j := by
      rw [pairNormal,real_inner_smul_left,hg,pairOffset]
      ring
    refine ⟨hn,?_⟩
    change facetChart B h i j ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x)
      ∈ affineFacet B h i j
    rw [facetChart_projection_eq B h i j hij x hn]
    exact hx
  · rintro ⟨hn,hx⟩
    change facetChart B h i j ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x)
      ∈ affineFacet B h i j at hx
    rwa [facetChart_projection_eq B h i j hij x hn] at hx

theorem affineFacet_eq_winner_pair (B : V → E) (h : V → ℝ) (i j : V) :
    affineFacet B h i j = winnerCell (affineScore B h) i ∩
      winnerCell (affineScore B h) j := by
  ext x
  change (affineScore B h i x=affineScore B h j x ∧
    ∀k,affineScore B h k x≤affineScore B h i x) ↔
    (∀k,affineScore B h k x≤affineScore B h i x) ∧
      ∀k,affineScore B h k x≤affineScore B h j x
  constructor
  · rintro ⟨he,hi⟩
    exact ⟨hi,fun k => (hi k).trans_eq he⟩
  · rintro ⟨hi,hj⟩
    exact ⟨le_antisymm (hj i) (hi j),hi⟩

/-- Literal density times the intrinsic Gaussian probability of the winning facet. -/
def facetSurfaceMass (B : V → E) (h : V → ℝ) (i j : V) : ℝ :=
  gaussianPDFReal 0 1 (pairOffset B h i j) *
    (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal

theorem facetSurfaceMass_nonneg (B : V → E) (h : V → ℝ) (i j : V) :
    0≤facetSurfaceMass B h i j := mul_nonneg (gaussianPDFReal_nonneg _ _ _) ENNReal.toReal_nonneg

def facetTubeMajorant (B : V → E) (h : V → ℝ) (i j : V) (ε : ℝ) : ℝ :=
  (stdGaussian (tangentSpace (pairNormal B i j))
    (thickening ε (intrinsicFacet B h i j))).toReal *
      ((gaussianReal 0 1 (Ioo (pairOffset B h i j-ε) (pairOffset B h i j+ε))).toReal/ε)

theorem facetTubeMajorant_tendsto (B : V → E) (h : V → ℝ) (i j : V) :
    Tendsto (facetTubeMajorant B h i j) (𝓝[>] 0) (𝓝 (2*facetSurfaceMass B h i j)) := by
  have ht := gaussian_tube_upper_tendsto (pairNormal B i j) (pairOffset B h i j)
    (intrinsicFacet B h i j) (isClosed_intrinsicFacet B h i j)
  unfold facetTubeMajorant
  simpa only [facetSurfaceMass,WeakSimplex.normalPDF,
    mul_assoc,mul_left_comm,mul_comm] using ht

theorem facet_tube_quotient_le (B : V → E) (h : V → ℝ) (i j : V)
    (hij : B i ≠ B j) (ε : ℝ) (hε : 0<ε) :
    (stdGaussian E (thickening ε (affineFacet B h i j))).toReal/ε ≤
      facetTubeMajorant B h i j ε := by
  rw [affineFacet_eq_planePatch B h i j hij]
  exact gaussian_tube_quotient_le _ (pairNormal_norm B i j hij) _ ε hε _

/-- The actual cut surface counts each crossing pair once. -/
def crossingFacetMass (B : V → E) (h : V → ℝ) (I : Set V) : ℝ :=
  ∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ}, facetSurfaceMass B h i j

theorem cut_shell_quotient_le (B : V → E) (h : V → ℝ) (hinj : Function.Injective B)
    (I : Set V) (ε : ℝ) (hε : 0<ε) :
    (stdGaussian E (thickening ε (cutRegion (affineScore B h) I) \
      cutRegion (affineScore B h) I)).toReal/ε ≤
      ∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ}, facetTubeMajorant B h i j ε := by
  have hm := cut_shell_measure_le (stdGaussian E) (affineScore B h)
    (fun i => by unfold affineScore; fun_prop) I ε
  have hr := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _))) hm
  have he : (∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ},
      stdGaussian E (thickening ε (winnerCell (affineScore B h) i ∩
        winnerCell (affineScore B h) j))).toReal =
      ∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ},
        (stdGaussian E (thickening ε (winnerCell (affineScore B h) i ∩
          winnerCell (affineScore B h) j))).toReal := by
    rw [ENNReal.toReal_sum (fun _ _ =>
      ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _))]
    apply Finset.sum_congr rfl
    intro i hi
    exact ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)
  rw [he] at hr
  have hd := div_le_div_of_nonneg_right hr hε.le
  simp_rw [Finset.sum_div] at hd
  refine hd.trans (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_)))
  rw [← affineFacet_eq_winner_pair]
  apply facet_tube_quotient_le B h i j _ ε hε
  apply hinj.ne
  intro hij
  exact j.property (hij ▸ i.property)

/-- A dimension-free geometric outer-boundary estimate. Its right side is the
actual intrinsic facet surface; no perimeter or boundary-transfer premise is supplied. -/
theorem cut_shell_quotient_eventually_le (B : V → E) (h : V → ℝ)
    (hinj : Function.Injective B) (I : Set V) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (stdGaussian E (thickening ε (cutRegion (affineScore B h) I) \
        cutRegion (affineScore B h) I)).toReal/ε ≤ 2*crossingFacetMass B h I+δ := by
  have ht : Tendsto (fun ε => ∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ},
      facetTubeMajorant B h i j ε) (𝓝[>] 0)
      (𝓝 (∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ}, 2*facetSurfaceMass B h i j)) :=
    tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _ (fun j _ =>
      facetTubeMajorant_tendsto B h i j))
  have he : (∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ}, 2*facetSurfaceMass B h i j) =
      2*crossingFacetMass B h I := by simp only [crossingFacetMass,Finset.mul_sum]
  rw [he] at ht
  have hu := (tendsto_order.1 ht).2 (2*crossingFacetMass B h I+δ) (by linarith)
  filter_upwards [hu,self_mem_nhdsWithin] with ε hε hpos
  exact (cut_shell_quotient_le B h hinj I ε hpos).trans hε.le

end NegativeVotingFanBoundary
