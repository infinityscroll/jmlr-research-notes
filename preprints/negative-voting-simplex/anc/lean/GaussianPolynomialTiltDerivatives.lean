import GaussianCapMixedMGF

/-! Actual mixed polynomial/exponential derivatives under the integral.
A Gaussian or restricted-Gaussian exponential moment premise is discharged
by callers; the weighted polynomial derivative and domination are proved. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace NegativeVotingPolynomialTilt
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

 theorem pow_exp_memLp_two (V : X→ℝ) (hVm : Measurable V)
    (hV : integrableExpSet V μ=univ) (k : ℕ) (t : ℝ) :
    MemLp (fun x=>V x^k*Real.exp (t*V x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have ht : 2*t∈interior (integrableExpSet V μ) := by rw [hV,interior_univ]; trivial
  have hi := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht (k*2)
  apply hi.congr
  filter_upwards with x
  rw [mul_pow,←pow_mul,pow_two (Real.exp _),←Real.exp_add]
  congr 2
  ring

/-- All orders and every real tilt, including mixed polynomial weights U.
The derivative is derived by a fixed integrable two-sided exponential
majorant on a neighborhood of the tilt; no differentiation premise appears. -/
 theorem hasDerivAt_weighted_power_exp (U V : X→ℝ) (hU : MemLp U 2 μ)
    (hVm : Measurable V) (hV : integrableExpSet V μ=univ) (k : ℕ) (t₀ : ℝ) :
    HasDerivAt (fun t:ℝ=>∫ x,U x*V x^k*Real.exp (t*V x) ∂μ)
      (∫ x,U x*V x^(k+1)*Real.exp (t₀*V x) ∂μ) t₀ := by
  let F := fun t (x:X)=>U x*V x^k*Real.exp (t*V x)
  let D := fun t (x:X)=>U x*V x^(k+1)*Real.exp (t*V x)
  have hFi (t:ℝ) : Integrable (F t) μ := by
    simpa only [F,mul_assoc,Pi.mul_def] using hU.integrable_mul (pow_exp_memLp_two μ V hVm hV k t)
  have hDi (t:ℝ) : Integrable (D t) μ := by
    simpa only [D,mul_assoc,Pi.mul_def] using hU.integrable_mul (pow_exp_memLp_two μ V hVm hV (k+1) t)
  let bound := fun x=>|D (t₀+1) x|+|D (t₀-1) x|
  have hbound : Integrable bound μ := (hDi (t₀+1)).abs.add (hDi (t₀-1)).abs
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=D) (s:=Metric.ball t₀ 1) (bound:=bound)
    (Metric.ball_mem_nhds t₀ zero_lt_one)
    (Eventually.of_forall (fun t=>(hFi t).aestronglyMeasurable)) (hFi t₀)
    ((hDi t₀).aestronglyMeasurable) ?_ hbound ?_).2
  · exact hh
  · filter_upwards with x
    intro t ht
    have ht' : |t-t₀|≤1 := le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
    have htb := abs_le.mp ht'
    have he : Real.exp (t*V x)≤Real.exp ((t₀+1)*V x)+Real.exp ((t₀-1)*V x) := by
      by_cases hx : 0≤V x
      · have hmul : t*V x≤(t₀+1)*V x := mul_le_mul_of_nonneg_right (by linarith) hx
        have hh := Real.exp_le_exp.mpr hmul
        linarith [Real.exp_pos ((t₀-1)*V x)]
      · have hmul : t*V x≤(t₀-1)*V x := mul_le_mul_of_nonpos_right (by linarith) (le_of_not_ge hx)
        have hh := Real.exp_le_exp.mpr hmul
        linarith [Real.exp_pos ((t₀+1)*V x)]
    have hm := mul_le_mul_of_nonneg_left he (abs_nonneg (U x*V x^(k+1)))
    simpa only [D,bound,Real.norm_eq_abs,abs_mul,Real.abs_exp,mul_add,mul_assoc] using hm
  · filter_upwards with x
    intro t _
    have hd := ((Real.hasDerivAt_exp (t*V x)).comp t
      ((hasDerivAt_id t).mul_const (V x))).const_mul (U x*V x^k)
    convert hd using 1
    · rfl
    · dsimp [D]
      simp only [pow_succ,one_mul]
      ring

end NegativeVotingPolynomialTilt
