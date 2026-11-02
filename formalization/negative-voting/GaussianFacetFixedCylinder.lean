import GaussianFacetNormalExtension
import GaussianFanMassJacobian

/-! Exact fixed-cylinder representation of a moved affine fan facet. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace Topology
namespace NegativeVotingFacetConditionalPlane
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingWeightedFacet
  NegativeVotingPositiveCovariance
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def transportedRows (S : Ambient d ≃L[ℝ] Ambient d) (B : ι → Ambient d) : ι → Ambient d :=
  fun i => S (B i)

def scoreOffsets (B : ι → Ambient d) (h : Ambient d) : ι → ℝ := fun i => inner ℝ (B i) h

def fixedFacetCylinder (B : ι → Ambient d) (i j : ι) : Set (Ambient d) :=
  cylindricalEvent (pairNormal B i j) (affineFacet B 0 i j)

theorem edge_eq_norm_smul_pairNormal (B : ι → Ambient d) (i j : ι) (hij : B i≠B j) :
    B i-B j=‖B i-B j‖ • pairNormal B i j := by
  have hh := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  simp only [pairNormal,smul_smul,mul_inv_cancel₀ hh,one_smul]

theorem transported_edge_eq (S : Ambient d ≃L[ℝ] Ambient d)
    (B : ι → Ambient d) (i j : ι) (hij : B i≠B j) :
    transportedRows S B i-transportedRows S B j=
      ‖B i-B j‖ • S (pairNormal B i j) := by
  have hh := congrArg S (edge_eq_norm_smul_pairNormal B i j hij)
  simpa only [map_sub,map_smul,transportedRows] using hh

theorem transported_edge_norm (S : Ambient d ≃L[ℝ] Ambient d)
    (B : ι → Ambient d) (i j : ι) (hij : B i≠B j) :
    ‖transportedRows S B i-transportedRows S B j‖=
      ‖B i-B j‖*‖S (pairNormal B i j)‖ := by
  rw [transported_edge_eq S B i j hij,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

theorem pairNormal_transportedRows (S : Ambient d ≃L[ℝ] Ambient d)
    (B : ι → Ambient d) (i j : ι) (hij : B i≠B j) :
    pairNormal (transportedRows S B) i j=transportedNormal S (pairNormal B i j) := by
  have hl := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  have hn := transformed_normal_norm_pos S (pairNormal B i j) (pairNormal_norm B i j hij)
  change ‖transportedRows S B i-transportedRows S B j‖⁻¹ •
    (transportedRows S B i-transportedRows S B j)=
      ‖S (pairNormal B i j)‖⁻¹ • S (pairNormal B i j)
  rw [transported_edge_norm S B i j hij,transported_edge_eq S B i j hij,smul_smul]
  congr 1
  field_simp

theorem pairOffset_transportedRows (S : Ambient d ≃L[ℝ] Ambient d)
    (B : ι → Ambient d) (h : Ambient d) (i j : ι) (hij : B i≠B j) :
    pairOffset (transportedRows S B) (scoreOffsets B h) i j=
      transportedLevel S (pairNormal B i j) h := by
  have hl := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  have hn := transformed_normal_norm_pos S (pairNormal B i j) (pairNormal_norm B i j hij)
  have hg : inner ℝ (B j) h-inner ℝ (B i) h=
      -‖B i-B j‖*inner ℝ (pairNormal B i j) h := by
    have hh := congrArg (fun z => inner ℝ z h) (edge_eq_norm_smul_pairNormal B i j hij)
    rw [inner_sub_left,real_inner_smul_left] at hh
    linarith
  change (inner ℝ (B j) h-inner ℝ (B i) h)/
    ‖transportedRows S B i-transportedRows S B j‖=
      -inner ℝ (pairNormal B i j) h/‖S (pairNormal B i j)‖
  rw [hg,transported_edge_norm S B i j hij]
  field_simp

theorem affineScore_transportedRows (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (B : ι → Ambient d) (h x : Ambient d) (i : ι) :
    affineScore (transportedRows S B) (scoreOffsets B h) i x=
      affineScore B 0 i (S x+h) := by
  simp only [affineScore,transportedRows,scoreOffsets,Pi.zero_apply,add_zero,inner_add_right]
  congr 1
  exact hS _ _

theorem affineFacet_transportedRows (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (B : ι → Ambient d) (h : Ambient d) (i j : ι) :
    affineFacet (transportedRows S B) (scoreOffsets B h) i j=
      (fun x => S x+h) ⁻¹' affineFacet B 0 i j := by
  ext x
  simp only [affineFacet,Set.mem_setOf_eq,Set.mem_preimage,affineCell,
    affineScore_transportedRows S hS]

/-- Exact normal density, original edge length and fixed-cylinder probability. -/
theorem facetWeight_eq_fixedCylinder
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (B : ι → Ambient d) (h : Ambient d) (i j : ι) (hij : B i≠B j)
    (R : Ambient d ≃L[ℝ] Ambient d) (hR : R.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=
      extendedCovariance S (pairNormal B i j)) :
    facetWeight (transportedRows S B) (scoreOffsets B h) i j=
      gaussianPDFReal 0 1 (transportedLevel S (pairNormal B i j) h)/
        (‖B i-B j‖*‖S (pairNormal B i j)‖)*
      (((stdGaussian (Ambient d)).map
        (fun x => conditionalMean S (pairNormal B i j) h+R x))
        (fixedFacetCylinder B i j)).toReal := by
  have hn := pairNormal_norm B i j hij
  have hijS : transportedRows S B i≠transportedRows S B j := fun he => hij (S.injective he)
  have hlaw : FSC.sliceLaw (transportedNormal S (pairNormal B i j))
      (transportedLevel S (pairNormal B i j) h)
      (affineFacet (transportedRows S B) (scoreOffsets B h) i j)=
      transportedSliceLaw S (pairNormal B i j) h (affineFacet B 0 i j) := by
    rw [affineFacet_transportedRows S hS]
    unfold transportedSliceLaw
    rw [Measure.map_apply (by fun_prop) (isClosed_affineFacet B 0 i j).measurableSet]
  rw [facetWeight_eq_ambient _ _ i j hijS,pairNormal_transportedRows S B i j hij,
    pairOffset_transportedRows S B h i j hij,transported_edge_norm S B i j hij,hlaw,
    transportedSliceLaw_event_eq_cylinder S hS _ h hn R hR hRR _
      (isClosed_affineFacet B 0 i j).measurableSet]
  rfl

/-- The positive symmetric factor and the exact facet formula are obtained together. -/
theorem exists_psd_factor_facetWeight_eq_fixedCylinder
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (B : ι → Ambient d) (h : Ambient d) (i j : ι) (hij : B i≠B j) :
    ∃R : Ambient d ≃L[ℝ] Ambient d,
      R.toContinuousLinearMap∈psdCone ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=
        extendedCovariance S (pairNormal B i j) ∧
      facetWeight (transportedRows S B) (scoreOffsets B h) i j=
        gaussianPDFReal 0 1 (transportedLevel S (pairNormal B i j) h)/
          (‖B i-B j‖*‖S (pairNormal B i j)‖)*
        (((stdGaussian (Ambient d)).map
          (fun x => conditionalMean S (pairNormal B i j) h+R x))
          (fixedFacetCylinder B i j)).toReal := by
  obtain ⟨R,hR,hRR⟩ := exists_positive_psd_factor _
    (extendedCovariance_pd S hS _ (pairNormal_norm B i j hij))
  exact ⟨R,hR,hRR,facetWeight_eq_fixedCylinder S hS B h i j hij R hR.1 hRR⟩

end NegativeVotingFacetConditionalPlane
