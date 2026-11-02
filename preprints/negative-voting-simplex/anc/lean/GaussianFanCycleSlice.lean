import GaussianFanCycleNested
import GaussianFacetDisintegration

/-! Actual Gaussian law on each child stratum, derived from the parent normal slice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open Module
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem coordinateCapNormal_pairing (b : AffineBasis V ℝ E) (S : Set V)
    (i : V) (k : {k : V // k ∉ S}) (x : FaceCoordinates b S) :
    ⟪coordinateCapNormal b S i k,x⟫ =
      -⟪faceBoundaryNormal b S i k,((faceCoordinates b S).symm x : E)⟫ := by
  calc
    _ = ⟪intrinsicCapNormal b S i k,(faceCoordinates b S).symm x⟫ := by
      rw [← (faceCoordinates b S).inner_map_map]
      simp [coordinateCapNormal]
    _ = _ := by change ⟪-faceBoundaryNormal b S i k,_⟫ = _; rw [inner_neg_left]; rfl

/-- Parent normal-orthogonal slice coordinates, mapped into the actual child tangent space. -/
def parentSliceToChild (b : AffineBasis V ℝ E) (S : Set V) (i : V) (hi : i ∈ S)
    (k : {k : V // k ∉ S})
    (x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k)) :
    (faceDirection b (Set.insert k.1 S))ᗮ := by
  refine ⟨((faceCoordinates b S).symm (x : FaceCoordinates b S) : E),?_⟩
  apply (mem_child_tangent_iff b S i k hi k.property _).mpr
  refine ⟨((faceCoordinates b S).symm (x : FaceCoordinates b S)).property,?_⟩
  have he := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  rw [coordinateCapNormal_pairing] at he
  exact neg_eq_zero.mp he

def childToParentSlice (b : AffineBasis V ℝ E) (S : Set V) (i : V) (hi : i ∈ S)
    (k : {k : V // k ∉ S}) (z : (faceDirection b (Set.insert k.1 S))ᗮ) :
    NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k) := by
  let zp : (faceDirection b S)ᗮ :=
    ⟨(z : E),((mem_child_tangent_iff b S i k hi k.property z).mp z.property).1⟩
  refine ⟨faceCoordinates b S zp,?_⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [coordinateCapNormal_pairing]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact neg_eq_zero.mpr ((mem_child_tangent_iff b S i k hi k.property z).mp z.property).2

/-- A genuine linear isometry equivalence, with both maps constructed from actual projections. -/
def childSliceEquiv (b : AffineBasis V ℝ E) (S : Set V) (i : V) (hi : i ∈ S)
    (k : {k : V // k ∉ S}) :
    NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k) ≃ₗᵢ[ℝ]
      (faceDirection b (Set.insert k.1 S))ᗮ where
  toFun := parentSliceToChild b S i hi k
  invFun := childToParentSlice b S i hi k
  left_inv := by
    intro x
    apply Subtype.ext
    change faceCoordinates b S ((faceCoordinates b S).symm (x : FaceCoordinates b S)) = x
    exact (faceCoordinates b S).apply_symm_apply x
  right_inv := by
    intro z
    apply Subtype.ext
    simp only [parentSliceToChild,childToParentSlice,LinearIsometryEquiv.symm_apply_apply]
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [parentSliceToChild,Submodule.coe_add,map_add]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp only [parentSliceToChild,Submodule.coe_smul,map_smul,RingHom.id_apply]
  norm_map' := by
    intro x
    change ‖((faceCoordinates b S).symm (x : FaceCoordinates b S) : E)‖ = ‖x‖
    exact (faceCoordinates b S).symm.norm_map x

def childSliceCoordinates (b : AffineBasis V ℝ E) (S : Set V) (i : V) (hi : i ∈ S)
    (k : {k : V // k ∉ S}) :
    NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k) ≃ₗᵢ[ℝ]
      FaceCoordinates b (Set.insert k.1 S) :=
  (childSliceEquiv b S i hi k).trans (faceCoordinates b (Set.insert k.1 S))

/-- Parent pinned-coordinate and child stratum embeddings coincide pointwise. -/
theorem pinned_coordinateEmbed_eq_child (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k)) :
    coordinateEmbed b h S (intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+x) =
      coordinateEmbed b h (Set.insert k.1 S) (childSliceCoordinates b S i hi k x) := by
  have hc : (faceCoordinates b (Set.insert k.1 S)).symm (childSliceCoordinates b S i hi k x) =
      childSliceEquiv b S i hi k x := by
    change (faceCoordinates b (Set.insert k.1 S)).symm
      (faceCoordinates b (Set.insert k.1 S) (childSliceEquiv b S i hi k x)) = _
    exact (faceCoordinates b (Set.insert k.1 S)).symm_apply_apply _
  have hn : (faceCoordinates b S).symm (coordinateCapNormal b S i k) =
      intrinsicCapNormal b S i k := (faceCoordinates b S).symm_apply_apply _
  simp only [coordinateEmbed,embedFace,map_add,map_smul,hn,hc,
    Submodule.coe_add,Submodule.coe_smul]
  rw [faceAnchor_insert_outward b h S i hi k]
  change faceAnchor b h S+(intrinsicCapOffset b h S i k •
      (intrinsicCapNormal b S i k : E)+((faceCoordinates b S).symm (x : FaceCoordinates b S) : E)) =
    faceAnchor b h S+intrinsicCapOffset b h S i k •
      (intrinsicCapNormal b S i k : E)+((faceCoordinates b S).symm (x : FaceCoordinates b S) : E)
  abel

theorem childSliceCoordinates_gaussian_map (b : AffineBasis V ℝ E) (S : Set V)
    (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    (stdGaussian (NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k))).map
      (childSliceCoordinates b S i hi k) =
      stdGaussian (FaceCoordinates b (Set.insert k.1 S)) :=
  stdGaussian_map (childSliceCoordinates b S i hi k)

def coordinateFaceEvent (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (k : {k : V // k ∉ S}) : Set (FaceCoordinates b S) :=
  {x | ∀ l, l ≠ k → ⟪coordinateCapNormal b S i l,x⟫ ≤ intrinsicCapOffset b h S i l}

theorem measurableSet_coordinateFaceEvent (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (k : {k : V // k ∉ S}) :
    MeasurableSet (coordinateFaceEvent b h S i k) := by
  unfold coordinateFaceEvent
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    measurableSet_le (by fun_prop) measurable_const

theorem pinned_normal_eq_offset (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k)) :
    ⟪coordinateCapNormal b S i k,
      intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+x⟫ =
      intrinsicCapOffset b h S i k := by
  have ho := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    coordinateCapNormal_norm b S i hi k,ho]
  ring

theorem coordinateFaceEvent_pin_iff_cap (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k)) :
    intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+x ∈ coordinateFaceEvent b h S i k ↔
    intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+x ∈ coordinateCap b h S i := by
  constructor
  · intro he l
    by_cases hl : l = k
    · subst l
      rw [pinned_normal_eq_offset b h S i hi k x]
    · exact he l hl
  · intro he l _
    exact he l

theorem winnerStratum_insert_iff_of_tangent (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : V) (x : E)
    (ht : x-affineFanApex b h ∈ (faceDirection b (Set.insert k S))ᗮ) :
    x ∈ winnerStratum b h (Set.insert k S) ↔ x ∈ winnerStratum b h S := by
  constructor
  · intro hx j hj l
    exact hx j (Set.mem_insert_of_mem k hj) l
  · intro hx
    apply (mem_winnerStratum_iff_tangent_gaps b h (Set.insert k S) i (Set.mem_insert_of_mem k hi) x).mpr
    exact ⟨ht,fun l _ => (mem_winnerStratum_iff_apex b h S x).mp hx i hi l⟩

/-- The actual parent boundary event is exactly the child cap after the constructed isometry. -/
theorem coordinateFaceEvent_pin_iff_child (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k)) :
    intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+x ∈ coordinateFaceEvent b h S i k ↔
      childSliceCoordinates b S i hi k x ∈ coordinateCap b h (Set.insert k.1 S) i := by
  rw [coordinateFaceEvent_pin_iff_cap b h S i hi k x,
    ← coordinateEmbed_mem_winnerStratum_iff b h S i hi,
    pinned_coordinateEmbed_eq_child b h S i hi k x]
  have ht : coordinateEmbed b h (Set.insert k.1 S) (childSliceCoordinates b S i hi k x)-
      affineFanApex b h ∈ (faceDirection b (Set.insert k.1 S))ᗮ :=
    embedFace_sub_apex_mem b h (Set.insert k.1 S) _
  rw [← winnerStratum_insert_iff_of_tangent b h S i hi k _ ht,
    coordinateEmbed_mem_winnerStratum_iff b h (Set.insert k.1 S) i (Set.mem_insert_of_mem k.1 hi)]

theorem coordinate_sliceLaw (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    FSC.sliceLaw (coordinateCapNormal b S i k) (intrinsicCapOffset b h S i k) =
      (stdGaussian (NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k))).map
        (fun x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k) =>
          intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+(x : FaceCoordinates b S)) :=
  NegativeVotingDisintegration.gaussian_affine_slice_map _ (coordinateCapNormal_norm b S i hi k) _

/-- Exact shared child probability in the genuine parent Gaussian boundary formula. -/
theorem coordinate_sliceMass_eq_child (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    FSC.sliceMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) k =
      FSC.capMass (coordinateCapNormal b (Set.insert k.1 S) i)
        (intrinsicCapOffset b h (Set.insert k.1 S) i) := by
  change (FSC.sliceLaw (coordinateCapNormal b S i k) (intrinsicCapOffset b h S i k)
    (coordinateFaceEvent b h S i k)).toReal = _
  rw [coordinate_sliceLaw b h S i hi k,
    Measure.map_apply (by fun_prop) (measurableSet_coordinateFaceEvent b h S i k)]
  have he : (fun x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k) =>
      intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+(x : FaceCoordinates b S)) ⁻¹'
        coordinateFaceEvent b h S i k =
      childSliceCoordinates b S i hi k ⁻¹' coordinateCap b h (Set.insert k.1 S) i := by
    ext x
    exact coordinateFaceEvent_pin_iff_child b h S i hi k x
  have hcap : MeasurableSet (coordinateCap b h (Set.insert k.1 S) i) := FSC.measurableSet_cap _ _
  rw [he, ← Measure.map_apply (childSliceCoordinates b S i hi k).continuous.measurable
    hcap,childSliceCoordinates_gaussian_map]
  rfl

/-- Exact boundary integral transfer for every continuous ambient test function.
This uses the actual Gaussian map law, not a conditional-moment premise. -/
theorem coordinate_slice_integral (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (F : E → ℝ) (hF : Continuous F) :
    (∫ x in coordinateFaceEvent b h S i k, F (coordinateEmbed b h S x)
      ∂FSC.sliceLaw (coordinateCapNormal b S i k) (intrinsicCapOffset b h S i k)) =
    ∫ y in coordinateCap b h (Set.insert k.1 S) i,
      F (coordinateEmbed b h (Set.insert k.1 S) y)
      ∂stdGaussian (FaceCoordinates b (Set.insert k.1 S)) := by
  have ha := measurableSet_coordinateFaceEvent b h S i k
  have hb : MeasurableSet (coordinateCap b h (Set.insert k.1 S) i) := FSC.measurableSet_cap _ _
  rw [← integral_indicator ha, ← integral_indicator hb,coordinate_sliceLaw b h S i hi k]
  have hA : AEStronglyMeasurable
      ((coordinateFaceEvent b h S i k).indicator (fun x => F (coordinateEmbed b h S x)))
      ((stdGaussian (NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k))).map
        (fun x : NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k) =>
          intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+(x : FaceCoordinates b S))) :=
    ((hF.comp (coordinateEmbed_isometry b h S).continuous).aestronglyMeasurable).indicator ha
  rw [integral_map (by fun_prop) hA, ← childSliceCoordinates_gaussian_map b S i hi k]
  have hB : AEStronglyMeasurable
      ((coordinateCap b h (Set.insert k.1 S) i).indicator
        (fun y => F (coordinateEmbed b h (Set.insert k.1 S) y)))
      ((stdGaussian (NegativeVotingDisintegration.tangentSpace (coordinateCapNormal b S i k))).map
        (childSliceCoordinates b S i hi k)) :=
    ((hF.comp (coordinateEmbed_isometry b h (Set.insert k.1 S)).continuous).aestronglyMeasurable).indicator hb
  rw [integral_map (by fun_prop) hB]
  apply integral_congr_ae
  filter_upwards [] with x
  have he := coordinateFaceEvent_pin_iff_child b h S i hi k x
  by_cases hx : intrinsicCapOffset b h S i k • coordinateCapNormal b S i k+
      (x : FaceCoordinates b S) ∈ coordinateFaceEvent b h S i k
  · have hy := he.mp hx
    rw [Set.indicator_of_mem hx,Set.indicator_of_mem hy,
      pinned_coordinateEmbed_eq_child b h S i hi k x]
  · have hy := mt he.mpr hx
    rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hy]

/-- Intrinsic Gaussian stratum mass with the actual perpendicular-density normalization. -/
def stratumMassAt (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) (i : V) : ℝ :=
  stratumDensityFactor b h S *
    FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)

theorem stratumMassAt_pos (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) : 0 < stratumMassAt b h S i :=
  mul_pos (stratumDensityFactor_pos b h S) (coordinateCap_mass_pos b h S i hi)

/-- One shared child mass occurs in every genuine parent boundary formula. -/
theorem stratum_boundary_weight_eq_child (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    stratumDensityFactor b h S * WeakSimplex.normalPDF (intrinsicCapOffset b h S i k) *
      FSC.sliceMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) k =
      stratumMassAt b h (Set.insert k.1 S) i := by
  rw [coordinate_sliceMass_eq_child b h S i hi k,stratumMassAt,
    stratumDensityFactor_insert b h S i hi k]

/-- The same exact normalization transfers all continuous boundary test moments. -/
theorem stratum_boundary_integral_eq_child (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (F : E → ℝ) (hF : Continuous F) :
    stratumDensityFactor b h S * WeakSimplex.normalPDF (intrinsicCapOffset b h S i k) *
      (∫ x in coordinateFaceEvent b h S i k, F (coordinateEmbed b h S x)
        ∂FSC.sliceLaw (coordinateCapNormal b S i k) (intrinsicCapOffset b h S i k)) =
    stratumDensityFactor b h (Set.insert k.1 S) *
      ∫ y in coordinateCap b h (Set.insert k.1 S) i,
        F (coordinateEmbed b h (Set.insert k.1 S) y)
        ∂stdGaussian (FaceCoordinates b (Set.insert k.1 S)) := by
  rw [coordinate_slice_integral b h S i hi k F hF,stratumDensityFactor_insert b h S i hi k]

end NegativeVotingFanCycle
