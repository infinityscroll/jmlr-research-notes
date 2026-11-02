import GaussianMaximumMomentComparison
import GaussianSquareExponential

/-! Explicit absolute upper-tail error for the actual iid Gaussian maximum.
The exponent is deliberately conservative and dimension enters only by the
finite Gaussian union sum. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal
namespace NegativeVotingMaximumUpperTail
open NegativeVoting NegativeVotingGaussianMaximum NegativeVotingSquareExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem scalar_upper_shortfall_exp (x T : ℝ) (hT : 0 ≤ T) :
    (max (x-T) 0)^2 ≤ 8*Real.exp (x^2/4)*Real.exp (-T^2/8) := by
  by_cases hx : x ≤ T
  · rw [max_eq_right (by linarith : x-T ≤ 0),zero_pow (by decide : 2≠0)]
    positivity
  · have hx0 : 0 ≤ x := by linarith
    have hsq : T^2 ≤ x^2 := pow_le_pow_left₀ hT (le_of_lt (lt_of_not_ge hx)) 2
    have hex := Real.add_one_le_exp (x^2/8)
    have hpow : (max (x-T) 0)^2 ≤ x^2 := by
      rw [max_eq_left (by linarith : 0 ≤ x-T)]
      nlinarith
    calc
      _ ≤ x^2 := hpow
      _ ≤ 8*Real.exp (x^2/8) := by linarith
      _ ≤ 8*Real.exp (x^2/4-T^2/8) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
      _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

theorem maximum_exp_le_sum (x : ι→ℝ) :
    Real.exp ((maximum x)^2/4) ≤ ∑ i,Real.exp ((x i)^2/4) := by
  let k := chosenWinner x
  have he : maximum x=x k := finite_max_eq_chosenWinner x
  rw [he]
  exact Finset.single_le_sum (fun i _=>(Real.exp_pos ((x i)^2/4)).le) (Finset.mem_univ k)

theorem iid_upper_shortfall_sq_le (T : ℝ) (hT : 0 ≤ T) :
    (∫ x : ι→ℝ,(max (maximum x-T) 0)^2 ∂standardGaussian ι) ≤
      16*(Fintype.card ι:ℝ)*Real.exp (-T^2/8) := by
  have hi (i : ι) : Integrable (fun x : ι→ℝ=>Real.exp ((x i)^2/4)) (standardGaussian ι) :=
    (measurePreserving_eval (μ:=fun _:ι=>gaussianReal 0 1) i).integrable_comp_of_integrable
      gaussian_square_exp_integrable
  have hsum : Integrable (fun x : ι→ℝ=>∑ i,Real.exp ((x i)^2/4)) (standardGaussian ι) :=
    integrable_finsetSum _ (fun i _=>hi i)
  have htail : Integrable (fun x : ι→ℝ=>(max (maximum x-T) 0)^2) (standardGaussian ι) :=
    ((maximum_memLp_two.sub (memLp_const T)).sup (memLp_const 0)).integrable_sq
  have hpoint (x : ι→ℝ) : (max (maximum x-T) 0)^2 ≤
      (8*Real.exp (-T^2/8))*(∑ i,Real.exp ((x i)^2/4)) := by
    have hs := scalar_upper_shortfall_exp (maximum x) T hT
    have hu := mul_le_mul_of_nonneg_left (maximum_exp_le_sum x)
      (show 0 ≤ 8*Real.exp (-T^2/8) by positivity)
    nlinarith only [hs,hu]
  have hm (i : ι) : (∫ x : ι→ℝ,Real.exp ((x i)^2/4) ∂standardGaussian ι) ≤ 2 := by
    have he := integral_map (μ:=standardGaussian ι) (φ:=fun x:ι→ℝ=>x i)
      (f:=fun z:ℝ=>Real.exp (z^2/4)) (measurable_pi_apply i).aemeasurable (by fun_prop)
    rw [(measurePreserving_eval (μ:=fun _:ι=>gaussianReal 0 1) i).map_eq] at he
    rw [←he]
    exact integral_gaussian_square_exp_le_two
  calc
    _ ≤ ∫ x : ι→ℝ,(8*Real.exp (-T^2/8))*(∑ i,Real.exp ((x i)^2/4)) ∂standardGaussian ι :=
      integral_mono htail (hsum.const_mul _) hpoint
    _ = (8*Real.exp (-T^2/8))*(∑ i,∫ x : ι→ℝ,Real.exp ((x i)^2/4) ∂standardGaussian ι) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)]
    _ ≤ (8*Real.exp (-T^2/8))*(∑ _i:ι,(2:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hm i)) (by positivity)
    _ = _ := by simp;ring

end NegativeVotingMaximumUpperTail
