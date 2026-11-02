import GaussianFacetFixedCylinder

/-! A regular reference facet becomes a fixed cylindrical Gaussian cap with
unit, pairwise noncoincident normals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace NegativeVotingFacetConditionalPlane
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingPositiveCovariance
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev FacetLabels (i j : ι) := {k : ι // k≠i ∧ k≠j}

def regularFacetRawNormal (B : ι → Ambient d) (i j : ι) (k : FacetLabels i j) : Ambient d :=
  B k-(1/2:ℝ) • (B i+B j)

def regularFacetNormal (B : ι → Ambient d) (i j : ι) (k : FacetLabels i j) : Ambient d :=
  (Real.sqrt (3/2:ℝ))⁻¹ • regularFacetRawNormal B i j k

theorem regular_gram_edge_norm (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) : ‖B i-B j‖=Real.sqrt 2 := by
  have hi : ‖B i‖^2=1-a := by simpa using hG i i
  have hj : ‖B j‖^2=1-a := by simpa using hG j j
  have he : ‖B i-B j‖^2=2 := by rw [norm_sub_sq_real,hi,hj,hG,if_neg hij];ring
  calc
    ‖B i-B j‖=Real.sqrt (‖B i-B j‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _=Real.sqrt 2 := by rw [he]

theorem regular_gram_rows_ne (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) : B i≠B j := by
  intro he
  have hn := regular_gram_edge_norm B a hG i j hij
  rw [he,sub_self,norm_zero] at hn
  have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  linarith

theorem regularFacetRawNormal_inner (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k l : FacetLabels i j) :
    inner ℝ (regularFacetRawNormal B i j k) (regularFacetRawNormal B i j l)=
      (if k=l then 3/2 else 1/2) := by
  have hik : i≠(k:ι) := Ne.symm k.property.1
  have hjk : j≠(k:ι) := Ne.symm k.property.2
  have hil : i≠(l:ι) := Ne.symm l.property.1
  have hjl : j≠(l:ι) := Ne.symm l.property.2
  simp only [regularFacetRawNormal,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right]
  simp only [hG,if_neg k.property.1,if_neg k.property.2,if_neg l.property.1,
    if_neg l.property.2,if_neg hik,if_neg hjk,if_neg hil,if_neg hjl,
    if_neg hij,if_neg (Ne.symm hij),ite_true]
  by_cases hkl : k=l
  · subst l
    simp
    ring
  · have hkvl : (k:ι)≠(l:ι) := fun he => hkl (Subtype.ext he)
    simp only [if_neg hkl,if_neg hkvl]
    ring

theorem regularFacetNormal_unit (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k : FacetLabels i j) :
    ‖regularFacetNormal B i j k‖=1 := by
  have hs : 0 < Real.sqrt (3/2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : ‖regularFacetRawNormal B i j k‖^2=3/2 := by
    rw [←real_inner_self_eq_norm_sq,regularFacetRawNormal_inner B a hG i j hij]
    simp
  have hn : ‖regularFacetRawNormal B i j k‖=Real.sqrt (3/2:ℝ) := by
    rw [←hsq,Real.sqrt_sq (norm_nonneg _)]
  simp only [regularFacetNormal,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,hn]
  exact inv_mul_cancel₀ hs.ne'

theorem regularFacetNormal_inner_ne (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k l : FacetLabels i j) (hkl : k≠l) :
    inner ℝ (regularFacetNormal B i j k) (regularFacetNormal B i j l)=1/3 := by
  have hs : 0 < Real.sqrt (3/2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤3/2)
  simp only [regularFacetNormal,real_inner_smul_left,real_inner_smul_right,
    regularFacetRawNormal_inner B a hG i j hij,if_neg hkl]
  field_simp
  nlinarith

theorem regularFacetNormal_noCoincident (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) : FSC.NoCoincident (regularFacetNormal B i j) 0 := by
  intro k l hkl
  have hu := regularFacetNormal_unit B a hG i j hij l
  have hp := regularFacetNormal_inner_ne B a hG i j hij k l hkl
  constructor
  · intro he
    rw [he,real_inner_self_eq_norm_sq,hu] at hp
    norm_num at hp
  · intro he
    rw [he,inner_neg_left,real_inner_self_eq_norm_sq,hu] at hp
    norm_num at hp

theorem regularFacetRawNormal_mem_plane (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k : FacetLabels i j) :
    inner ℝ (pairNormal B i j) (regularFacetRawNormal B i j k)=0 := by
  have hik : i≠(k:ι) := Ne.symm k.property.1
  have hjk : j≠(k:ι) := Ne.symm k.property.2
  simp only [pairNormal,real_inner_smul_left,regularFacetRawNormal,
    inner_sub_left,inner_sub_right,real_inner_smul_right,inner_add_right]
  simp only [hG,if_neg hik,if_neg hjk,if_neg hij,if_neg (Ne.symm hij),ite_true]
  ring

theorem regularFacetRawNormal_eq_projection (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k : FacetLabels i j) :
    normalProjection (pairNormal B i j) (B k-B i)=regularFacetRawNormal B i j k := by
  have hrow := regular_gram_rows_ne B a hG i j hij
  have hn := pairNormal_norm B i j hrow
  have hz : normalProjection (pairNormal B i j) (B i-B j)=0 := by
    rw [edge_eq_norm_smul_pairNormal B i j hrow,map_smul,normalProjection_apply,
      real_inner_self_eq_norm_sq,hn]
    simp
  have he : B k-B i=regularFacetRawNormal B i j k-(1/2:ℝ) • (B i-B j) := by
    dsimp [regularFacetRawNormal]
    module
  rw [he,map_sub,map_smul,hz,smul_zero,sub_zero,
    normalProjection_eq_self _ _ (regularFacetRawNormal_mem_plane B a hG i j hij k)]

/-- The fixed cylinder is a genuine finite cap, with redundant pinned labels removed. -/
theorem fixedFacetCylinder_eq_regularCap (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) :
    fixedFacetCylinder B i j=FSC.cap (regularFacetNormal B i j) 0 := by
  have hrow := regular_gram_rows_ne B a hG i j hij
  have hn := pairNormal_norm B i j hrow
  have hs : 0 < (Real.sqrt (3/2:ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  ext x
  let z := normalProjection (pairNormal B i j) x
  have ht : inner ℝ (B i) z=inner ℝ (B j) z := by
    have he : inner ℝ (B i-B j) z=0 := by
      rw [edge_eq_norm_smul_pairNormal B i j hrow,real_inner_smul_left]
      change ‖B i-B j‖*inner ℝ (pairNormal B i j)
        (normalProjection (pairNormal B i j) x)=0
      rw [normalProjection_mem_plane _ hn,mul_zero]
    rw [inner_sub_left] at he
    exact sub_eq_zero.mp he
  have hp (k : FacetLabels i j) : inner ℝ (regularFacetNormal B i j k) x≤0 ↔
      inner ℝ (B k) z≤ inner ℝ (B i) z := by
    have he : inner ℝ (regularFacetRawNormal B i j k) x=
        inner ℝ (B k-B i) z := by
      rw [←regularFacetRawNormal_eq_projection B a hG i j hij]
      simpa only [normalProjection_adjoint_apply] using
        (normalProjection (pairNormal B i j)).adjoint_inner_left x (B k-B i)
    rw [regularFacetNormal,real_inner_smul_left,he,inner_sub_left]
    have hm : (Real.sqrt (3/2:ℝ))⁻¹*(inner ℝ (B k) z-inner ℝ (B i) z) ≤
        (Real.sqrt (3/2:ℝ))⁻¹*0 ↔ inner ℝ (B k) z-inner ℝ (B i) z≤0 :=
      mul_le_mul_iff_right₀ hs
    simpa only [mul_zero] using hm.trans sub_nonpos
  change (inner ℝ (B i) z+0=inner ℝ (B j) z+0 ∧
      ∀k,inner ℝ (B k) z+0≤ inner ℝ (B i) z+0) ↔
    ∀k : FacetLabels i j,inner ℝ (regularFacetNormal B i j k) x≤0
  simp only [add_zero]
  constructor
  · intro hx k
    exact (hp k).2 (hx.2 k)
  · intro hx
    refine ⟨ht,fun k => ?_⟩
    by_cases hki : k=i
    · subst k;exact le_rfl
    by_cases hkj : k=j
    · subst k;exact ht.symm.le
    exact (hp ⟨k,hki,hkj⟩).1 (hx ⟨k,hki,hkj⟩)


/-- The regular-edge normalization is exactly sqrt(2), and the event is the
fixed unit-normal cap to which ordinary affine Gaussian estimates apply. -/
theorem regularFacetWeight_eq_affineCap
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (h : Ambient d) (i j : ι) (hij : i≠j)
    (R : Ambient d ≃L[ℝ] Ambient d) (hR : R.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=
      extendedCovariance S (pairNormal B i j)) :
    facetWeight (transportedRows S B) (scoreOffsets B h) i j=
      gaussianPDFReal 0 1 (transportedLevel S (pairNormal B i j) h)/
        (Real.sqrt 2*‖S (pairNormal B i j)‖)*
      ((stdGaussian (Ambient d)) {x | R x+conditionalMean S (pairNormal B i j) h∈
        FSC.cap (regularFacetNormal B i j) 0}).toReal := by
  rw [facetWeight_eq_fixedCylinder S hS B h i j
    (regular_gram_rows_ne B a hG i j hij) R hR hRR,
    regular_gram_edge_norm B a hG i j hij,
    fixedFacetCylinder_eq_regularCap B a hG i j hij,
    Measure.map_apply (by fun_prop) (FSC.measurableSet_cap _ _)]
  congr 3
  ext x
  simp only [Set.mem_preimage,Set.mem_setOf_eq,add_comm]

theorem exists_psd_factor_regularFacetWeight_eq_affineCap
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (B : ι → Ambient d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (h : Ambient d) (i j : ι) (hij : i≠j) :
    ∃R : Ambient d ≃L[ℝ] Ambient d,
      R.toContinuousLinearMap∈psdCone ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=
        extendedCovariance S (pairNormal B i j) ∧
      facetWeight (transportedRows S B) (scoreOffsets B h) i j=
        gaussianPDFReal 0 1 (transportedLevel S (pairNormal B i j) h)/
          (Real.sqrt 2*‖S (pairNormal B i j)‖)*
        ((stdGaussian (Ambient d)) {x | R x+conditionalMean S (pairNormal B i j) h∈
          FSC.cap (regularFacetNormal B i j) 0}).toReal := by
  obtain ⟨R,hR,hRR⟩ := exists_positive_psd_factor _ (extendedCovariance_pd S hS _
    (pairNormal_norm B i j (regular_gram_rows_ne B a hG i j hij)))
  exact ⟨R,hR,hRR,regularFacetWeight_eq_affineCap S hS B a hG h i j hij R hR.1 hRR⟩

end NegativeVotingFacetConditionalPlane
