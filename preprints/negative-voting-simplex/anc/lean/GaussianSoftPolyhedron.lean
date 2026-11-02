import OAI.Probability.GaussianPropeller.SmoothedConcavity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

namespace NegativeVotingEhrhard

/-- A smooth convex penalty whose derivative is the bounded sigmoid. -/
def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

theorem hasDerivAt_softplus (x : ℝ) : HasDerivAt softplus (Real.sigmoid x) x := by
  have h := ((Real.hasDerivAt_exp x).const_add 1).log (by positivity : 1 + Real.exp x ≠ 0)
  convert h using 1
  · rfl
  · rw [Real.sigmoid, Real.exp_neg]
    field_simp
    ring

theorem softplus_nonneg (x : ℝ) : 0 ≤ softplus x :=
  Real.log_nonneg (by have := Real.exp_pos x; linarith)

theorem self_le_softplus (x : ℝ) : x ≤ softplus x := by
  calc
    x = Real.log (Real.exp x) := (Real.log_exp x).symm
    _ ≤ softplus x := Real.log_le_log (Real.exp_pos x) (by linarith)

theorem softplus_le_log_two_of_nonpos {x : ℝ} (hx : x ≤ 0) : softplus x ≤ Real.log 2 := by
  apply Real.log_le_log (by positivity)
  have h := Real.exp_le_one_iff.mpr hx
  linarith

theorem convexOn_softplus : ConvexOn ℝ univ softplus := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (hasDerivAt_softplus x).differentiableAt)
  have heq : deriv softplus = Real.sigmoid := funext (fun x => (hasDerivAt_softplus x).deriv)
  rw [heq]
  exact Real.sigmoid_monotone

theorem sigmoid_curvature_bounds (x : ℝ) :
    0 ≤ Real.sigmoid x * (1 - Real.sigmoid x) ∧
    Real.sigmoid x * (1 - Real.sigmoid x) ≤ 1 := by
  have h0 := Real.sigmoid_nonneg x
  have h1 := Real.sigmoid_le_one x
  constructor
  · exact mul_nonneg h0 (sub_nonneg.mpr h1)
  · nlinarith [sq_nonneg (Real.sigmoid x)]

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scaled affine inequality violation. -/
def penaltyArgument (R : ℝ) (w : E) (b : ℝ) (x : E) : ℝ := R * (inner ℝ w x - b)

def penaltyGradient (R : ℝ) (w : E) (b : ℝ) (x : E) : E :=
  (R * Real.sigmoid (penaltyArgument R w b x)) • w

def penaltyHessian (R : ℝ) (w : E) (b : ℝ) (x : E) : E →L[ℝ] E :=
  (R ^ 2 * (Real.sigmoid (penaltyArgument R w b x) *
    (1 - Real.sigmoid (penaltyArgument R w b x)))) • (innerSL ℝ w).smulRight w

theorem hasFDerivAt_penaltyArgument (R : ℝ) (w : E) (b : ℝ) (x : E) :
    HasFDerivAt (penaltyArgument R w b) (R • innerSL ℝ w) x := by
  exact ((innerSL ℝ w).hasFDerivAt.sub_const b).const_mul R

theorem hasFDerivAt_softplus_penalty (R : ℝ) (w : E) (b : ℝ) (x : E) :
    HasFDerivAt (fun y => softplus (penaltyArgument R w b y))
      (innerSL ℝ (penaltyGradient R w b x)) x := by
  convert (hasDerivAt_softplus (penaltyArgument R w b x)).comp_hasFDerivAt x
    (hasFDerivAt_penaltyArgument R w b x) using 1
  · rfl
  · ext y
    simp [penaltyGradient]
    ring

theorem hasFDerivAt_penaltyGradient (R : ℝ) (w : E) (b : ℝ) (x : E) :
    HasFDerivAt (penaltyGradient R w b) (penaltyHessian R w b x) x := by
  have h := (((Real.hasDerivAt_sigmoid (penaltyArgument R w b x)).comp_hasFDerivAt x
    (hasFDerivAt_penaltyArgument R w b x)).const_mul R).smul_const w
  convert h using 1
  · rfl
  · ext y
    simp [penaltyHessian, smul_smul]
    congr 1
    ring

theorem continuous_penaltyHessian (R : ℝ) (w : E) (b : ℝ) :
    Continuous (penaltyHessian R w b) := by
  unfold penaltyHessian penaltyArgument
  fun_prop

theorem norm_penaltyGradient_le (R : ℝ) (hR : 0 ≤ R) (w : E) (b : ℝ) (x : E) :
    ‖penaltyGradient R w b x‖ ≤ R * ‖w‖ := by
  rw [penaltyGradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hR (Real.sigmoid_nonneg _))]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hR (Real.sigmoid_le_one _)) (norm_nonneg _)

theorem norm_penaltyHessian_le (R : ℝ) (w : E) (b : ℝ) (x : E) :
    ‖penaltyHessian R w b x‖ ≤ R ^ 2 * ‖w‖ ^ 2 := by
  have hb := sigmoid_curvature_bounds (penaltyArgument R w b x)
  rw [penaltyHessian, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg R) hb.1),
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (sq_nonneg R) hb.2) (mul_nonneg (norm_nonneg w) (norm_nonneg w))
  nlinarith only [hh]

variable {J : Type*} [Fintype J]

/-- A smooth concave approximation to the finite intersection of affine halfspaces. -/
def softPolyhedron (a R : ℝ) (w : J → E) (b : J → ℝ) (x : E) : ℝ :=
  a - ∑ j, softplus (penaltyArgument R (w j) (b j) x)

def softPolyhedronGradient (R : ℝ) (w : J → E) (b : J → ℝ) (x : E) : E :=
  -∑ j, penaltyGradient R (w j) (b j) x

def softPolyhedronHessian (R : ℝ) (w : J → E) (b : J → ℝ) (x : E) : E →L[ℝ] E :=
  -∑ j, penaltyHessian R (w j) (b j) x

theorem softPolyhedron_fderiv (a R : ℝ) (w : J → E) (b : J → ℝ) (x : E) :
    HasFDerivAt (softPolyhedron a R w b)
      (innerSL ℝ (softPolyhedronGradient R w b x)) x := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => hasFDerivAt_softplus_penalty R (w j) (b j) x)).const_sub a
  convert h using 1
  · rfl
  · ext y
    simp [softPolyhedronGradient]

theorem softPolyhedronGradient_fderiv (R : ℝ) (w : J → E) (b : J → ℝ) (x : E) :
    HasFDerivAt (softPolyhedronGradient R w b) (softPolyhedronHessian R w b x) x := by
  exact (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => hasFDerivAt_penaltyGradient R (w j) (b j) x)).neg

theorem continuous_softPolyhedronHessian (R : ℝ) (w : J → E) (b : J → ℝ) :
    Continuous (softPolyhedronHessian R w b) := by
  apply Continuous.neg
  exact continuous_finsetSum _ (fun j _ => continuous_penaltyHessian R (w j) (b j))

theorem norm_softPolyhedronGradient_le (R : ℝ) (hR : 0 ≤ R) (w : J → E) (b : J → ℝ) (x : E) :
    ‖softPolyhedronGradient R w b x‖ ≤ R * ∑ j, ‖w j‖ := by
  rw [softPolyhedronGradient, norm_neg]
  exact (norm_sum_le _ _).trans (by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => norm_penaltyGradient_le R hR (w j) (b j) x))

theorem norm_softPolyhedronHessian_le (R : ℝ) (w : J → E) (b : J → ℝ) (x : E) :
    ‖softPolyhedronHessian R w b x‖ ≤ R ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
  rw [softPolyhedronHessian, norm_neg]
  exact (norm_sum_le _ _).trans (by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => norm_penaltyHessian_le R (w j) (b j) x))

theorem concaveOn_softPolyhedron (a R : ℝ) (w : J → E) (b : J → ℝ) :
    ConcaveOn ℝ univ (softPolyhedron a R w b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hs : (∑ j, softplus (penaltyArgument R (w j) (b j) (u • x + v • y))) ≤
      u * ∑ j, softplus (penaltyArgument R (w j) (b j) x) +
      v * ∑ j, softplus (penaltyArgument R (w j) (b j) y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have heq : penaltyArgument R (w j) (b j) (u • x + v • y) =
        u * penaltyArgument R (w j) (b j) x + v * penaltyArgument R (w j) (b j) y := by
      unfold penaltyArgument
      calc
        _ = R * (u * inner ℝ (w j) x + v * inner ℝ (w j) y - (u + v) * b j) := by
          rw [huv]
          simp [inner_add_right, inner_smul_right]
        _ = _ := by ring
    rw [heq]
    exact convexOn_softplus.2 (mem_univ _) (mem_univ _) hu hv huv
  change u * softPolyhedron a R w b x + v * softPolyhedron a R w b y ≤ _
  unfold softPolyhedron
  have ha : (u + v) * a = a := by rw [huv, one_mul]
  nlinarith [ha]

end Euclidean
/-- The checked smooth Ehrhard theorem applies to every member of the explicit
polyhedral approximation family; all smoothness and global bounds are derived. -/
theorem qheat_softPolyhedron_concave {ι J : Type*} [Fintype ι] [Fintype J]
    (a R : ℝ) (hR : 0 ≤ R) (w : J → EuclideanSpace ℝ ι) (b : J → ℝ)
    (T : ℝ) (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (OAI.GaussianPropeller.EhrhardSmooth.qheat (softPolyhedron a R w b) T) := by
  apply OAI.GaussianPropeller.EhrhardSmooth.qheat_concave
    (softPolyhedron_fderiv a R w b) (softPolyhedronGradient_fderiv R w b)
    (continuous_softPolyhedronHessian R w b)
    (L := (R * ∑ j, ‖w j‖).toNNReal)
    (D := R ^ 2 * ∑ j, ‖w j‖ ^ 2) ?_ ?_ (concaveOn_softPolyhedron a R w b) hT
  · intro x
    simpa only [Real.coe_toNNReal', max_eq_left (mul_nonneg hR (Finset.sum_nonneg (fun j _ => norm_nonneg (w j))))]
      using norm_softPolyhedronGradient_le R hR w b x
  · exact norm_softPolyhedronHessian_le R w b

end NegativeVotingEhrhard
