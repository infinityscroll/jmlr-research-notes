import GaussianPolynomialFacetGeometricTrace
import GaussianRegularScoreLaw

/-! Two-normal Gaussian coordinates adapted to a current plane and a rotated
regular normal. Every measure identity refers to the actual Gaussian laws. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingRegularCrossPlaneGeometry
open NegativeVotingDisintegration NegativeVotingRegularScoreLaw GaussianFin

/-- Rotation of the two scalar normal coordinates. -/
def pairRotation (c s : ℝ) (q : ℝ×ℝ) : ℝ×ℝ :=
  (c*q.1-s*q.2,s*q.1+c*q.2)

theorem pairRotation_measurePreserving (c s : ℝ) (hcs : c^2+s^2=1) :
    MeasurePreserving (pairRotation c s)
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let B : Fin 2→Fin 2→ℝ := ![![c,-s],![s,c]]
  let C : Fin 2→Fin 2→ℝ := ![![1,0],![0,1]]
  have hg : ∀ i j, (∑ k,B i k*B j k)=∑ k,C i k*C j k := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [B,C,Fin.sum_univ_two] <;> nlinarith [hcs]
  have hh := coordinateScoreLaw_eq_of_gram B C hg
  have hc : coordinateScores C=id := by
    funext x
    ext i
    fin_cases i <;> simp [coordinateScores,C,Fin.sum_univ_two]
  rw [hc,Measure.map_id] at hh
  have hb : Measurable (coordinateScores B) := coordinateScores_measurable B
  have hp : MeasurePreserving (coordinateScores B) (γFin 2) (γFin 2) := ⟨hb,hh⟩
  have he := measurePreserving_finTwoArrow (gaussianReal 0 1)
  have hall := he.comp (hp.comp (he.symm MeasurableEquiv.finTwoArrow))
  convert hall using 1
  funext q
  simp [pairRotation,coordinateScores,B,Function.comp_def,Fin.sum_univ_two,
    MeasurableEquiv.finTwoArrow,MeasurableEquiv.piFinTwo,sub_eq_add_neg]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {n : ℕ}

/-- Every pair of unit normals fits such a frame, including parallel normals.
The dimension hypothesis is only used to choose a spare tangent direction. -/
theorem exists_normal_frame (w u : E) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ v : tangentSpace w, ‖v‖=1 ∧ ∃ c s : ℝ, c^2+s^2=1 ∧ u=c • w+s • (v:E) := by
  let c := inner ℝ w u
  let x : tangentSpace w := (tangentSpace w).orthogonalProjectionOnto u
  have hx : (x:E)=u-c • w := tangent_projection_formula w hw u
  have he : u=c • w+(x:E) := by rw [hx];abel
  have hnorm : c^2+‖x‖^2=1 := by
    change c^2+‖(x:E)‖^2=1
    have hcomm : inner ℝ u w=c := real_inner_comm w u
    rw [hx,norm_sub_sq_real,hu,norm_smul,hw,mul_one,Real.norm_eq_abs,sq_abs,
      real_inner_smul_right,hcomm]
    ring
  by_cases hx0 : x=0
  · have hdim' := (ℝ ∙ w).finrank_add_finrank_orthogonal
    have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
    rw [finrank_span_singleton hw0] at hdim'
    have hpos : 0 < Module.finrank ℝ (tangentSpace w) := by
      dsimp only [tangentSpace]
      omega
    letI : Nontrivial (tangentSpace w) := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨v,hv⟩ := exists_norm_eq (tangentSpace w) (by norm_num : (0:ℝ) ≤ 1)
    refine ⟨v,hv,c,0,?_,?_⟩
    · simpa [hx0] using hnorm
    · simpa [hx0] using he
  · refine ⟨‖x‖⁻¹ • x,norm_smul_inv_norm hx0,c,‖x‖,hnorm,?_⟩
    rw [Submodule.coe_smul,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0),one_smul]
    exact he

/-- Coordinates in the intersection of the two orthogonal complements. -/
def doubleTangent (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (t : Fin n→ℝ) : E :=
  ((e.symm (WithLp.toLp 2 t) : tangentSpace w) : E)

def frameReconstruct (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (q : (Fin n→ℝ)×(ℝ×ℝ)) : E :=
  doubleTangent w v e q.1+q.2.1 • w+q.2.2 • (v:E)

def planeReconstruct (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (A : ℝ)
    (q : (Fin n→ℝ)×ℝ) : E := doubleTangent w v e q.1+q.2 • (v:E)+A • w

/-- The two successive orthogonal disintegrations are actual product laws. -/
theorem frameReconstruct_map (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ((γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))).map
      (frameReconstruct w v e)=stdGaussian E := by
  have hvmap : MeasurePreserving (coordinateReconstruct v e)
      ((γFin n).prod (gaussianReal 0 1)) (stdGaussian (tangentSpace w)) :=
    ⟨by unfold coordinateReconstruct;fun_prop,coordinateReconstruct_map v hv e⟩
  have hwmap : MeasurePreserving (normalReconstruct w)
      ((stdGaussian (tangentSpace w)).prod (gaussianReal 0 1)) (stdGaussian E) :=
    ⟨by unfold normalReconstruct;fun_prop,normalReconstruct_map w hw⟩
  have hswap := (MeasurePreserving.id (γFin n)).prod
    (Measure.measurePreserving_swap (μ:=gaussianReal 0 1) (ν:=gaussianReal 0 1))
  have hassoc := (measurePreserving_prodAssoc (γFin n) (gaussianReal 0 1)
    (gaussianReal 0 1)).symm MeasurableEquiv.prodAssoc
  have hh := hwmap.comp ((hvmap.prod (MeasurePreserving.id (gaussianReal 0 1))).comp
    (hassoc.comp hswap))
  convert hh.map_eq using 1
  congr 1
  funext q
  simp [frameReconstruct,doubleTangent,normalReconstruct,coordinateReconstruct,
    Function.comp_def,MeasurableEquiv.prodAssoc,Prod.map,add_assoc,add_left_comm,add_comm]

/-- The current affine plane has its literal translated tangent Gaussian law. -/
theorem planeReconstruct_map (w : E) (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (A : ℝ) :
    ((γFin n).prod (gaussianReal 0 1)).map (planeReconstruct w v e A)=
      (stdGaussian (tangentSpace w)).map (fun y : tangentSpace w=>(y:E)+A • w) := by
  rw [←coordinateReconstruct_map v hv e,Measure.map_map (by fun_prop)
    (by unfold coordinateReconstruct;fun_prop)]
  rfl

def rotatedReconstruct (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (c s : ℝ)
    (q : (Fin n→ℝ)×(ℝ×ℝ)) : E := frameReconstruct w v e (q.1,pairRotation c s q.2)

theorem rotatedReconstruct_map (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (c s : ℝ) (hcs : c^2+s^2=1) :
    ((γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))).map
      (rotatedReconstruct w v e c s)=stdGaussian E := by
  have hrot := (MeasurePreserving.id (γFin n)).prod (pairRotation_measurePreserving c s hcs)
  have hframe : MeasurePreserving (frameReconstruct w v e)
      ((γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) (stdGaussian E) :=
    ⟨by unfold frameReconstruct doubleTangent;fun_prop,frameReconstruct_map w hw v hv e⟩
  exact (hframe.comp hrot).map_eq

/-- Exact radius identity, with no inverse sine or small-angle denominator. -/
theorem rotated_plane_radius (c s A z : ℝ) (hcs : c^2+s^2=1) :
    (c*A+s*z)^2+(-s*A+c*z)^2=A^2+z^2 := by
  calc
    _ = (c^2+s^2)*(A^2+z^2) := by ring
    _ = _ := by rw [hcs,one_mul]

/-- The same free tangent point parametrizes the current plane in the regular
normal coordinates. -/
theorem rotatedReconstruct_on_plane (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1) (A z : ℝ) (t : Fin n→ℝ) :
    rotatedReconstruct w v e c s (t,(c*A+s*z,-s*A+c*z))=
      planeReconstruct w v e A (t,z) := by
  have ha : c*(c*A+s*z)-s*(-s*A+c*z)=A := by nlinarith only [congrArg (fun x : ℝ => x*A) hcs]
  have hb : s*(c*A+s*z)+c*(-s*A+c*z)=z := by nlinarith only [congrArg (fun x : ℝ => x*z) hcs]
  simp only [rotatedReconstruct,frameReconstruct,pairRotation,ha,hb,planeReconstruct]
  abel
end NegativeVotingRegularCrossPlaneGeometry
