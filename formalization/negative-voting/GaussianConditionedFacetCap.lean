import GaussianFacetConditionalPlane
import GaussianFanMassJacobian
import GaussianCapUnionLower

/-! A general actual affine facet is an explicit cylindrical Gaussian cap.
A literal high-margin point then gives an exponential probability lower bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace NegativeVotingConditionedFacet
open NegativeVotingFacetConditionalPlane NegativeVotingFan NegativeVotingWeightedFacet
  NegativeVotingDisintegration NegativeVotingCapShiftLower NegativeVotingCapUnionLower
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

abbrev OtherLabels (i j : V) := {k : V // k≠i ∧ k≠j}

def facetNormals (B : V → FSC.Coord d) (i j : V) (k : OtherLabels i j) : FSC.Coord d :=
  normalProjection (pairNormal B i j) (B k-B i)

def facetThresholds (B : V → FSC.Coord d) (h : V → ℝ) (i j : V)
    (k : OtherLabels i j) : ℝ :=
  h i-h k-pairOffset B h i j*inner ℝ (B k-B i) (pairNormal B i j)

def intrinsicProbability (B : V → FSC.Coord d) (h : V → ℝ) (i j : V) : ℝ :=
  (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal

theorem normalProjection_norm_le (n x : FSC.Coord d) (hn : ‖n‖=1) :
    ‖normalProjection n x‖ ≤ ‖x‖ := by
  have he : normalProjection n x=
      ((tangentSpace n).orthogonalProjectionOnto x : FSC.Coord d) := by
    rw [tangent_projection_formula n hn,normalProjection_apply]
  rw [he]
  exact (tangentSpace n).norm_orthogonalProjectionOnto_apply_le x

theorem normalProjection_inner (n x y : FSC.Coord d) :
    inner ℝ (normalProjection n x) y=inner ℝ x (normalProjection n y) := by
  simpa only [normalProjection_adjoint_apply] using
    (normalProjection n).adjoint_inner_left y x

theorem facetChart_projection_eq (B : V → FSC.Coord d) (h : V → ℝ) (i j : V)
    (hij : B i≠B j) (x : FSC.Coord d) :
    facetChart B h i j ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x)=
      normalProjection (pairNormal B i j) x+pairOffset B h i j • pairNormal B i j := by
  simp only [facetChart,tangent_projection_formula _ (pairNormal_norm B i j hij),
    normalProjection_apply]

theorem facetThreshold_gap (B : V → FSC.Coord d) (h : V → ℝ) (i j : V)
    (k : OtherLabels i j) (x : FSC.Coord d) :
    facetThresholds B h i j k-inner ℝ (facetNormals B i j k) x=
      affineScore B h i (normalProjection (pairNormal B i j) x+
        pairOffset B h i j • pairNormal B i j)-
      affineScore B h k (normalProjection (pairNormal B i j) x+
        pairOffset B h i j • pairNormal B i j) := by
  simp only [facetThresholds,facetNormals,normalProjection_inner,affineScore,
    inner_add_right,real_inner_smul_right,inner_sub_left]
  ring

/-- The tangent Gaussian probability equals an ordinary ambient cap probability;
the two pinned labels have been removed, not replaced by positive-margin assumptions. -/
theorem intrinsicProbability_eq_capMass (B : V → FSC.Coord d) (h : V → ℝ)
    (i j : V) (hij : B i≠B j) :
    intrinsicProbability B h i j=FSC.capMass (facetNormals B i j) (facetThresholds B h i j) := by
  unfold intrinsicProbability FSC.capMass
  rw [←gaussian_projection_map (tangentSpace (pairNormal B i j)),
    Measure.map_apply (by fun_prop) (isClosed_intrinsicFacet B h i j).measurableSet]
  congr 2
  ext x
  let z := normalProjection (pairNormal B i j) x+pairOffset B h i j • pairNormal B i j
  have ht : affineScore B h i z=affineScore B h j z := by
    simpa only [facetChart_projection_eq B h i j hij] using
      facetChart_on_pair_plane B h i j hij
        ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x)
  have hp (k : OtherLabels i j) :
      inner ℝ (facetNormals B i j k) x ≤ facetThresholds B h i j k ↔
        affineScore B h k z ≤ affineScore B h i z := by
    have he := facetThreshold_gap B h i j k x
    change facetThresholds B h i j k-inner ℝ (facetNormals B i j k) x=
      affineScore B h i z-affineScore B h k z at he
    constructor <;> intro hh <;> linarith
  change (facetChart B h i j ((tangentSpace (pairNormal B i j)).orthogonalProjectionOnto x)
      ∈affineFacet B h i j) ↔
    ∀k : OtherLabels i j,inner ℝ (facetNormals B i j k) x ≤ facetThresholds B h i j k
  rw [facetChart_projection_eq B h i j hij]
  change (affineScore B h i z=affineScore B h j z ∧ ∀k,affineScore B h k z ≤ affineScore B h i z) ↔ _
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

theorem facetNormals_norm_le (B : V → FSC.Coord d) (i j : V) (hij : B i≠B j)
    (k : OtherLabels i j) : ‖facetNormals B i j k‖ ≤ ‖B k-B i‖ :=
  normalProjection_norm_le _ _ (pairNormal_norm B i j hij)

theorem point_normal_coordinate (B : V → FSC.Coord d) (h : V → ℝ) (i j : V)
    (hij : B i≠B j) (x : FSC.Coord d)
    (hx : inner ℝ (B i-B j) x=h j-h i) :
    inner ℝ (pairNormal B i j) x=pairOffset B h i j := by
  simp only [pairNormal,real_inner_smul_left,hx,pairOffset]
  ring

theorem facetThreshold_gap_at_point (B : V → FSC.Coord d) (h : V → ℝ) (i j : V)
    (hij : B i≠B j) (x : FSC.Coord d) (hx : inner ℝ (B i-B j) x=h j-h i)
    (k : OtherLabels i j) :
    facetThresholds B h i j k-
      inner ℝ (facetNormals B i j k) (normalProjection (pairNormal B i j) x)=
      affineScore B h i x-affineScore B h k x := by
  have hn := pairNormal_norm B i j hij
  have hp : normalProjection (pairNormal B i j)
      (normalProjection (pairNormal B i j) x)=normalProjection (pairNormal B i j) x :=
    normalProjection_eq_self _ _ (normalProjection_mem_plane _ hn x)
  rw [facetThreshold_gap,hp,normalProjection_apply,point_normal_coordinate B h i j hij x hx]
  simp only [sub_add_cancel]

/-- A genuine point on the facet plane, with actual winning margins, supplies
an explicit exponential lower bound for the literal intrinsic facet probability. -/
theorem intrinsicProbability_lower_of_point (B : V → FSC.Coord d) (h : V → ℝ)
    (i j : V) (hij : B i≠B j) (D : ℝ) (hD : 0 < D)
    (hrow : ∀k : OtherLabels i j,‖B k-B i‖ ≤ D)
    (x : FSC.Coord d) (hx : inner ℝ (B i-B j) x=h j-h i)
    (hmargin : ∀k : OtherLabels i j,
      D*Real.sqrt (2*Real.log (2*((Fintype.card (OtherLabels i j) : ℝ)+1))) ≤
        affineScore B h i x-affineScore B h k x) :
    (1/4:ℝ)*Real.exp (-‖x‖^2) ≤ intrinsicProbability B h i j := by
  let v := normalProjection (pairNormal B i j) x
  let w := facetNormals B i j
  let b := facetThresholds B h i j
  let bshift := fun k => b k-inner ℝ (w k) v
  have hhalf : (1/2:ℝ) ≤ FSC.capMass w bshift := by
    apply cap_mass_half_of_margin w bshift D hD
    · intro k
      exact (facetNormals_norm_le B i j hij k).trans (hrow k)
    · intro k
      change D*Real.sqrt (2*Real.log (2*((Fintype.card (OtherLabels i j) : ℝ)+1))) ≤
        facetThresholds B h i j k-
          inner ℝ (facetNormals B i j k) (normalProjection (pairNormal B i j) x)
      rw [facetThreshold_gap_at_point B h i j hij x hx]
      exact hmargin k
  have hs := cap_shift_mass_lower w bshift v (-1)
  have hb : (fun k => bshift k-(-1)*inner ℝ (w k) v)=b := by
    funext k
    dsimp only [bshift]
    ring
  rw [hb] at hs
  norm_num only [neg_one_sq,one_mul] at hs
  have hv : ‖v‖ ≤ ‖x‖ := normalProjection_norm_le _ _ (pairNormal_norm B i j hij)
  have hex : Real.exp (-‖x‖^2) ≤ Real.exp (-‖v‖^2) := by
    apply Real.exp_le_exp.mpr
    have hh := pow_le_pow_left₀ (norm_nonneg _) hv 2
    linarith
  have hquarter : (1/4:ℝ) ≤ (FSC.capMass w bshift)^2 := by nlinarith
  calc
    (1/4:ℝ)*Real.exp (-‖x‖^2) ≤ (1/4:ℝ)*Real.exp (-‖v‖^2) :=
      mul_le_mul_of_nonneg_left hex (by norm_num)
    _ ≤ (FSC.capMass w bshift)^2*Real.exp (-‖v‖^2) :=
      mul_le_mul_of_nonneg_right hquarter (Real.exp_pos _).le
    _ ≤ FSC.capMass w b := hs
    _=intrinsicProbability B h i j := (intrinsicProbability_eq_capMass B h i j hij).symm

end NegativeVotingConditionedFacet
