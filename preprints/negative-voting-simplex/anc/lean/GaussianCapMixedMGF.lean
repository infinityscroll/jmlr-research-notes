import GaussianCapCovariance
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual mixed Gaussian cap moments differentiated under the integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal Topology
namespace NegativeVotingPolyhedral
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem cap_score_exp_memLp (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) :
    MemLp (fun x : FSC.Coord d => inner ℝ v x * Real.exp (t * inner ℝ v x)) 2
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have ht : 2*t ∈ interior (integrableExpSet (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet, interior_univ]
    exact mem_univ _
  have hi := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 2
  apply hi.congr
  filter_upwards [] with x
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

/-- No positivity, smooth-boundary, or extra moment assumption is required. -/
theorem hasDerivAt_cap_mixed_mgf (w : ι → FSC.Coord d) (b : ι → ℝ)
    (u v : FSC.Coord d) :
    HasDerivAt
      (fun t : ℝ => ∫ x in FSC.cap w b,
        inner ℝ u x * Real.exp (t * inner ℝ v x) ∂stdGaussian (FSC.Coord d))
      (∫ x in FSC.cap w b, inner ℝ u x * inner ℝ v x ∂stdGaussian (FSC.Coord d)) 0 := by
  let μ := (stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)
  have hu : MemLp (fun x : FSC.Coord d => inner ℝ u x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (cap_score_moment_integrable w b u 2)
  let D := fun t (x : FSC.Coord d) => inner ℝ u x * inner ℝ v x * Real.exp (t * inner ℝ v x)
  have hD (t : ℝ) : Integrable (D t) μ := by
    have hi := hu.integrable_mul (cap_score_exp_memLp w b v t)
    change Integrable (fun x => inner ℝ u x * (inner ℝ v x * Real.exp (t * inner ℝ v x))) μ at hi
    simpa only [D, mul_assoc] using hi
  let B := fun x => |D 1 x| + |D (-1) x|
  have hB : Integrable B μ := (hD 1).abs.add (hD (-1)).abs
  have hF0 : Integrable (fun x : FSC.Coord d => inner ℝ u x * Real.exp (0 * inner ℝ v x)) μ := by
    simpa using cap_score_moment_integrable w b u 1
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t (x : FSC.Coord d) => inner ℝ u x * Real.exp (t * inner ℝ v x))
    (F' := D) (s := Metric.ball (0 : ℝ) 1) (bound := B)
    (Metric.ball_mem_nhds 0 zero_lt_one) (by filter_upwards with t; fun_prop)
    hF0 (by dsimp [D]; fun_prop) ?_ hB ?_).2
  · simpa only [D, zero_mul, Real.exp_zero, mul_one, μ] using hh
  · filter_upwards with x
    intro t ht
    have ht' : |t| ≤ 1 := le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)
    have htb : t * inner ℝ v x ≤ |inner ℝ v x| := by
      calc
        _ ≤ |t * inner ℝ v x| := le_abs_self _
        _ = |t| * |inner ℝ v x| := abs_mul _ _
        _ ≤ 1 * |inner ℝ v x| := mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
        _ = _ := one_mul _
    have he : Real.exp (t * inner ℝ v x) ≤
        Real.exp (inner ℝ v x) + Real.exp (-inner ℝ v x) := by
      apply (Real.exp_le_exp.mpr htb).trans
      by_cases hx : 0 ≤ inner ℝ v x
      · rw [abs_of_nonneg hx]
        linarith [Real.exp_pos (-inner ℝ v x)]
      · rw [abs_of_neg (lt_of_not_ge hx)]
        linarith [Real.exp_pos (inner ℝ v x)]
    have hm := mul_le_mul_of_nonneg_left he (abs_nonneg (inner ℝ u x * inner ℝ v x))
    simpa only [D, B, Real.norm_eq_abs, abs_mul, Real.abs_exp, one_mul,
      neg_one_mul, mul_add, mul_assoc] using hm
  · filter_upwards with x
    intro t _
    simpa only [D, Function.comp_apply, id_eq, one_mul, mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_exp (t * inner ℝ v x)).comp t
        ((hasDerivAt_id t).mul_const (inner ℝ v x))).const_mul (inner ℝ u x)

end NegativeVotingPolyhedral
