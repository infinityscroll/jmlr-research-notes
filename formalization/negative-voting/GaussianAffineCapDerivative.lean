import GaussianMovingCap
import GaussianCapSecondMoment

/-! An actual Gaussian affine-transport derivative, derived from moving
polyhedra and Gaussian integration by parts, with no density-ratio premise. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory WeakSimplex Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingAffineCapDerivative
open NegativeVotingMovingCap NegativeVotingPolyhedral NegativeVotingDisintegration
  NegativeVotingFanScore
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tangentFace_integral_eq_slice (w : ι → FSC.Coord d) (b : ι → ℝ)
    (j : ι) (hw : ‖w j‖=1) (G : FSC.Coord d → ℝ) (hG : Continuous G) :
    (∫ y in tangentFace w b j,G ((y:FSC.Coord d)+b j•w j)
      ∂stdGaussian (tangentSpace (w j)))=
      ∫ x in faceEvent w b j,G x ∂FSC.sliceLaw (w j) (b j) := by
  rw [FSC.sliceLaw,gaussian_affine_slice_map _ hw,
    setIntegral_map (measurableSet_faceEvent w b j) hG.measurable.aestronglyMeasurable (by fun_prop)]
  have he : (fun y : tangentSpace (w j)=>b j•w j+(y:FSC.Coord d))=
      fun y : tangentSpace (w j)=>(y:FSC.Coord d)+b j•w j := funext (fun y=>add_comm _ _)
  rw [he]
  simp only [add_comm (b j•w j)]
  rfl

/-- Actual moving-cap mass derivative on the literal ambient Gaussian slices. -/
theorem capJointDerivative_one_ambient (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (δ : Parameters d ι) :
    capJointDerivative w b (fun _=>1) δ=
      ∑ j,normalPDF (b j)*∫ x in faceEvent w b j,
        (δ.2 j-inner ℝ (δ.1 j) x) ∂FSC.sliceLaw (w j) (b j) := by
  rw [capJointDerivative_apply w hw b (fun _=>1) continuous_const 1 (by norm_num)
    (fun x=>by simp)]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact tangentFace_integral_eq_slice w b j (hw j) (fun x=>δ.2 j-inner ℝ (δ.1 j) x) (by fun_prop)

def affineRankOneVelocity (w : ι → FSC.Coord d) (u v z : FSC.Coord d) : Parameters d ι :=
  (fun j=>inner ℝ (w j) u • v,fun j=>-inner ℝ (w j) z)

theorem face_affine_integral (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (u v z : FSC.Coord d) :
    (∫ x in faceEvent w b j,(-inner ℝ (w j) z-inner ℝ (w j) u*inner ℝ v x)
      ∂FSC.sliceLaw (w j) (b j))=
      -inner ℝ (w j) z*FSC.sliceMass w b j-
        inner ℝ (w j) u*(∫ x in faceEvent w b j,inner ℝ v x ∂FSC.sliceLaw (w j) (b j)) := by
  letI := sliceLaw_isGaussian (w j) (b j)
  have hi : Integrable (fun x : FSC.Coord d=>inner ℝ v x)
      ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j)) :=
    (IsGaussian.integrable_dual _ (innerSL ℝ v)).restrict
  rw [integral_sub (integrable_const _) (hi.const_mul _),integral_const_mul,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change (FSC.sliceMass w b j)*(-inner ℝ (w j) z)-_= _
  ring

/-- The quadratic-plus-linear Gaussian score is derived from the actual
first and second moment boundary formulas. -/
theorem capJointDerivative_rankOne (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (u v z : FSC.Coord d) :
    capJointDerivative w b (fun _=>1) (affineRankOneVelocity w u v z)=
      (∫ x in FSC.cap w b,inner ℝ u x*inner ℝ v x ∂stdGaussian (FSC.Coord d))-
        FSC.capMass w b*inner ℝ u v+
        (∫ x in FSC.cap w b,inner ℝ z x ∂stdGaussian (FSC.Coord d)) := by
  have h1 := gaussian_cap_first_moment w hw b hb z
  have h2 := gaussian_cap_bilinear_second_moment w hw b hb u v
  calc
    _ = ∑ j, (-(normalPDF (b j)*FSC.sliceMass w b j*inner ℝ (w j) z)-
        (normalPDF (b j)*inner ℝ (w j) u)*
          (∫ x in faceEvent w b j,inner ℝ v x ∂FSC.sliceLaw (w j) (b j))) := by
      rw [capJointDerivative_one_ambient w hw b]
      apply Finset.sum_congr rfl
      intro j _
      simp only [affineRankOneVelocity,real_inner_smul_left]
      rw [face_affine_integral]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib]
      linarith

theorem capTest_one (p : Parameters d ι) : capTest p (fun _=>1)=FSC.capMass p.1 p.2 := by
  rw [capTest,setIntegral_const]
  simp [FSC.capMass,Measure.real]

/-- The true mass derivative for simultaneous rank-one score and translation
motion; only the concrete unit-normal/noncoincident base cap is assumed. -/
theorem hasDerivAt_affine_rankOne_capMass (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (u v z : FSC.Coord d) :
    HasDerivAt (fun t : ℝ=>FSC.capMass
      (fun j=>w j+t • (inner ℝ (w j) u • v))
      (fun j=>b j-t*inner ℝ (w j) z))
      ((∫ x in FSC.cap w b,inner ℝ u x*inner ℝ v x ∂stdGaussian (FSC.Coord d))-
        FSC.capMass w b*inner ℝ u v+
        (∫ x in FSC.cap w b,inner ℝ z x ∂stdGaussian (FSC.Coord d))) 0 := by
  let δ := affineRankOneVelocity w u v z
  have hF := hasFDerivAt_capTest w hw b hb (fun _=>1) continuous_const 1 (by norm_num)
    (fun x=>by simp)
  have hp : HasDerivAt (fun t : ℝ=>(w,b)+t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const δ).const_add (w,b)
  have hF' : HasFDerivAt (fun p : Parameters d ι=>capTest p (fun _=>1))
      (capJointDerivative w b (fun _=>1)) ((w,b)+(0:ℝ) • δ) := by simpa using hF
  have hh := hF'.comp_hasDerivAt (0:ℝ) hp
  have he : (fun t : ℝ=>capTest ((w,b)+t • δ) (fun _=>1))=
      fun t : ℝ=>FSC.capMass (fun j=>w j+t • (inner ℝ (w j) u • v))
        (fun j=>b j-t*inner ℝ (w j) z) := by
    funext t
    rw [capTest_one]
    congr 1
    funext j
    simp [δ,affineRankOneVelocity,sub_eq_add_neg,mul_neg]
  change HasDerivAt (fun t : ℝ=>capTest ((w,b)+t • δ) (fun _=>1))
    (capJointDerivative w b (fun _=>1) δ) 0 at hh
  rw [he] at hh
  simpa only [δ,capJointDerivative_rankOne w hw b hb u v z] using hh

/-- The varying cap is exactly the pullback by the actual affine map,
not just a formal variation of its normals. -/
theorem affine_rankOne_cap_eq_preimage (w : ι → FSC.Coord d) (b : ι → ℝ)
    (u v z : FSC.Coord d) (t : ℝ) :
    FSC.cap (fun j=>w j+t • (inner ℝ (w j) u • v))
      (fun j=>b j-t*inner ℝ (w j) z)=
      (fun x=>x+t • (inner ℝ v x • u)+t • z) ⁻¹' FSC.cap w b := by
  ext x
  simp only [FSC.cap,Set.mem_setOf_eq,Set.mem_preimage,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right]
  apply forall_congr'
  intro j
  constructor <;> intro h <;> nlinarith

theorem hasDerivAt_affine_rankOne_gaussian_mass (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (u v z : FSC.Coord d) :
    HasDerivAt (fun t : ℝ=>(stdGaussian (FSC.Coord d)
      ((fun x=>x+t • (inner ℝ v x • u)+t • z) ⁻¹' FSC.cap w b)).toReal)
      ((∫ x in FSC.cap w b,inner ℝ u x*inner ℝ v x ∂stdGaussian (FSC.Coord d))-
        FSC.capMass w b*inner ℝ u v+
        (∫ x in FSC.cap w b,inner ℝ z x ∂stdGaussian (FSC.Coord d))) 0 := by
  simpa only [FSC.capMass,affine_rankOne_cap_eq_preimage] using
    hasDerivAt_affine_rankOne_capMass w hw b hb u v z

end NegativeVotingAffineCapDerivative
