import GaussianRegularCrossPlaneGeometry
import GaussianActualFacetOUTrace

/-! Pointwise actual OU transport through the rank-two chart, and the exact
regular-normal reflection. No ambient-AE identity is restricted to a plane. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingRegularCrossPlaneOU
open NegativeVotingRegularCrossPlaneGeometry NegativeVotingDisintegration
  NegativeVotingActualFacetOUTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {n : ℕ}

 theorem rotatedReconstruct_measurable (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (c s : ℝ) :
    Measurable (rotatedReconstruct w v e c s) := by
  unfold rotatedReconstruct frameReconstruct doubleTangent pairRotation
  fun_prop

/-- Genuine ambient Lp inputs have exactly the same norm in the full chart. -/
theorem rotatedReconstruct_memLp_norm (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1) (f : E→ℝ) (p : ℝ≥0∞)
    (hf : MemLp f p (stdGaussian E)) :
    MemLp (fun q=>f (rotatedReconstruct w v e c s q)) p
      ((γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) ∧
    eLpNorm (fun q=>f (rotatedReconstruct w v e c s q)) p
      ((γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))=eLpNorm f p (stdGaussian E) := by
  have hp : MeasurePreserving (rotatedReconstruct w v e c s)
      ((γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) (stdGaussian E) :=
    ⟨rotatedReconstruct_measurable w v e c s,rotatedReconstruct_map w hw v hv e c s hcs⟩
  exact ⟨hf.comp_measurePreserving hp,eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hp⟩

def pairMix (τ r : ℝ) (p q : (Fin n→ℝ)×(ℝ×ℝ)) : (Fin n→ℝ)×(ℝ×ℝ) :=
  ((fun j=>τ*p.1 j+r*q.1 j),(τ*p.2.1+r*q.2.1,τ*p.2.2+r*q.2.2))

 theorem rotatedReconstruct_mix (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (c s τ r : ℝ)
    (p q : (Fin n→ℝ)×(ℝ×ℝ)) :
    rotatedReconstruct w v e c s (pairMix τ r p q)=
      τ • rotatedReconstruct w v e c s p+r • rotatedReconstruct w v e c s q := by
  unfold rotatedReconstruct frameReconstruct doubleTangent pairRotation pairMix
  change ((e.symm (τ • WithLp.toLp 2 p.1+r • WithLp.toLp 2 q.1) : tangentSpace w):E)+_+_= _
  simp only [map_add,map_smul,Submodule.coe_add,Submodule.coe_smul]
  module

/-- Exact pointwise change of variables in the actual ambient noise integral. -/
theorem ambientAverage_rotatedReconstruct (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1) (τ : ℝ) (f : E→ℝ) (hf : Measurable f)
    (p : (Fin n→ℝ)×(ℝ×ℝ)) :
    ambientAverage τ f (rotatedReconstruct w v e c s p)=
      ∫ q,f (rotatedReconstruct w v e c s (pairMix τ (Real.sqrt (1-τ^2)) p q))
        ∂(γFin n).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  unfold ambientAverage
  rw [←rotatedReconstruct_map w hw v hv e c s hcs]
  rw [integral_map (f:=fun y:E=>f (τ • rotatedReconstruct w v e c s p+Real.sqrt (1-τ^2) • y))
    (rotatedReconstruct_measurable w v e c s).aemeasurable
    ((hf.comp (by fun_prop)).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with q
  rw [rotatedReconstruct_mix]

 theorem doubleTangent_inner_w (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (t : Fin n→ℝ) :
    inner ℝ w (doubleTangent w v e t)=0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp (e.symm (WithLp.toLp 2 t)).val.property

 theorem doubleTangent_inner_v (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (t : Fin n→ℝ) :
    inner ℝ (v:E) (doubleTangent w v e t)=0 := by
  change inner ℝ v ((e.symm (WithLp.toLp 2 t)):tangentSpace w)=0
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (e.symm (WithLp.toLp 2 t)).property

 theorem inner_rotated_normal (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1) (p : (Fin n→ℝ)×(ℝ×ℝ)) :
    inner ℝ (c • w+s • (v:E)) (rotatedReconstruct w v e c s p)=p.2.1 := by
  have hwv : inner ℝ w (v:E)=0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property
  have hvw : inner ℝ (v:E) w=0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  have hww : inner ℝ w w=1 := by rw [real_inner_self_eq_norm_sq,hw];norm_num
  have hvv : inner ℝ (v:E) (v:E)=1 := by change inner ℝ v v=1;rw [real_inner_self_eq_norm_sq,hv];norm_num
  simp only [rotatedReconstruct,frameReconstruct,pairRotation,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,doubleTangent_inner_w,doubleTangent_inner_v,
    hww,hvv,hwv,hvw,mul_zero,add_zero,zero_add,mul_one]
  nlinarith only [congrArg (fun x : ℝ=>x*p.2.1) hcs]

/-- Flipping the regular normal coordinate is its actual Euclidean reflection. -/
theorem rotatedReconstruct_reflect (w : E) (v : tangentSpace w)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (c s a b : ℝ) (t : Fin n→ℝ) :
    rotatedReconstruct w v e c s (t,(-a,b))=
      rotatedReconstruct w v e c s (t,(a,b))-(2*a) • (c • w+s • (v:E)) := by
  unfold rotatedReconstruct frameReconstruct pairRotation
  module
end NegativeVotingRegularCrossPlaneOU
