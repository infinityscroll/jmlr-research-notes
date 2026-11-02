import GaussianBalancedReference
import GaussianFacetFixedCylinder
import GaussianHypercontractivityBridge

/-! The literal negative-correlation Gaussian average of a finite winner
assignment is an actual shifted-fan mass. Positive rescaling preserves the
pointwise symmetric tie rule, so the identities hold at every input point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingRegularOU
open NegativeVoting NegativeVotingFan NegativeVotingBalancedReference
  NegativeVotingFacetConditionalPlane NegativeVotingHypercontractivity
variable {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]

theorem negative_noise_scale_pos (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    0<Real.sqrt (1-r^2) := by
  apply Real.sqrt_pos.mpr
  have hp : 0<(1-r)*(1+r) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- Pointwise score rescaling; this does not discard or alter ties. -/
theorem negative_noise_weights (B : V → FSC.Coord d) (r : ℝ)
    (hr : 0<r) (hr1 : r<1) (x y : FSC.Coord d) (i : V) :
    weights B 0 ((-r) • x+Real.sqrt (1-r^2) • y) i=
      weights B (scoreOffsets B (-(r/Real.sqrt (1-r^2)) • x)) y i := by
  let a := Real.sqrt (1-r^2)
  have ha : 0<a := negative_noise_scale_pos r hr hr1
  have hs : scores B 0 ((-r) • x+a • y)=
      fun j => a*scores B (scoreOffsets B (-(r/a) • x)) y j := by
    funext j
    simp only [scores,Pi.zero_apply,add_zero,inner_add_right,real_inner_smul_right,
      scoreOffsets]
    field_simp [ha.ne']
    <;> ring
  change maxWeights (scores B 0 ((-r) • x+a • y)) i=
    maxWeights (scores B (scoreOffsets B (-(r/a) • x)) y) i
  rw [hs]
  exact maxWeights_mul_pos _ a ha i

/-- Exact negative correlation, in the finite-product coordinates used by the
actual averaging operator and Euclidean coordinates used by fan masses. -/
theorem gaussianAverage_negative_weights (B : V → FSC.Coord d) (r : ℝ)
    (hr : 0<r) (hr1 : r<1) (x : FSC.Coord d) (i : V) :
    gaussianAverage (-r) (fun y => weights B 0 (WithLp.toLp 2 y) i) x.ofLp=
      mass B (scoreOffsets B (-(r/Real.sqrt (1-r^2)) • x)) i := by
  unfold gaussianAverage
  change (∫y,weights B 0 (WithLp.toLp 2 (fun j =>
    (-r)*x.ofLp j+Real.sqrt (1-(-r)^2)*y j)) i ∂standardGaussian (Fin d))=_
  rw [integral_standardGaussian_eq_euclidean]
  unfold mass
  apply integral_congr_ae
  filter_upwards with y
  have hv : WithLp.toLp 2 (fun j =>
      (-r)*x.ofLp j+Real.sqrt (1-(-r)^2)*y.ofLp j)=
      (-r) • x+Real.sqrt (1-r^2) • y := by
    ext j
    change (-r)*x.ofLp j+Real.sqrt (1-(-r)^2)*y.ofLp j=
      (-r)*x.ofLp j+Real.sqrt (1-r^2)*y.ofLp j
    rw [neg_sq]
  rw [hv]
  exact negative_noise_weights B r hr hr1 x y i

theorem regularAssignment_ofLp_eq_weights {m : ℕ} [Nonempty (Fin m)]
    (B : Fin m → FSC.Coord d) (x : FSC.Coord d) (i : Fin m) :
    regularAssignment (fun j => (B j).ofLp) x.ofLp i=weights B 0 x i := by
  unfold regularAssignment weights scores
  congr 1
  funext j
  simp only [Pi.zero_apply,add_zero,PiLp.inner_apply,Real.inner_apply]

/-- The actual regular-assignment potential at correlation -r equals the
Gaussian winning mass at the explicit offsets -r/sqrt(1-r^2) times the score
vector. The identity itself works for arbitrary finite rows, in every ambient
dimension, without a regular-Gram, injectivity, or affine-basis hypothesis. -/
theorem gaussianAverage_negative_regularAssignment {m : ℕ} [Nonempty (Fin m)]
    (B : Fin m → FSC.Coord d) (r : ℝ) (hr : 0<r) (hr1 : r<1)
    (x : FSC.Coord d) (i : Fin m) :
    gaussianAverage (-r) (fun y => regularAssignment (fun j => (B j).ofLp) y i) x.ofLp=
      mass B (scoreOffsets B (-(r/Real.sqrt (1-r^2)) • x)) i := by
  have hf : (fun y => regularAssignment (fun j => (B j).ofLp) y i)=
      (fun y => weights B 0 (WithLp.toLp 2 y) i) := by
    funext y
    exact regularAssignment_ofLp_eq_weights B (WithLp.toLp 2 y) i
  rw [hf]
  exact gaussianAverage_negative_weights B r hr hr1 x i

/-- The same pointwise identity for the vector-valued noise operator appearing
in the actual noise-stability formulation. -/
theorem gaussianNoiseOperator_negative_regularAssignment {m : ℕ} [Nonempty (Fin m)]
    (B : Fin m → FSC.Coord d) (r : ℝ) (hr : 0<r) (hr1 : r<1)
    (x : FSC.Coord d) :
    gaussianNoiseOperator (-r) (regularAssignment (fun j => (B j).ofLp)) x.ofLp=
      mass B (scoreOffsets B (-(r/Real.sqrt (1-r^2)) • x)) := by
  funext i
  exact gaussianAverage_negative_regularAssignment B r hr hr1 x i

end NegativeVotingRegularOU
