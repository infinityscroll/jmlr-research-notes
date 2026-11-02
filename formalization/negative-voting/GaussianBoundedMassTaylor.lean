import GaussianBoundedOffsetResponse
import Mathlib.Analysis.Convex.Deriv

/-! A genuine lower Taylor estimate for the actual prescribed-mass Gaussian
value. The inverse-log gap has been integrated along the actual selected
offset curve; no Hessian or offset derivative bound is supplied as a premise. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingBoundedMassTaylor
open NegativeVotingBoundedOffsetResponse NegativeVotingFan NegativeVotingFanInverse
open NegativeVotingFanSelectedOffsets NegativeVotingAffineBasisLower NegativeVotingFanValue
open NegativeVotingFanMassValueGradient
variable {V:Type*} [Fintype V] [DecidableEq V] [Nonempty V] {d:ℕ}

theorem hasDerivAt_massLine_value (b:AffineBasis V ℝ (FSC.Coord d)) (p:V→ℝ)
    (v:centeredGauge V) (hp:∑i,p i=1) (t:ℝ) (hpos:∀i,0< massLine p v t i):
    HasDerivAt (fun s:ℝ=>optimizedValue b (massLine p v s))
      (massDerivative (v:V→ℝ) (offsetLine b p v t)) t:=by
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound b
  have hv:HasDerivAt (fun s:ℝ=>s • v) v t:=by
    simpa using (hasDerivAt_id t).smul_const v
  have hd:HasFDerivAt (fun u:centeredGauge V=>optimizedValue b (p+(u:V→ℝ)))
      (massDerivative (offsetLine b p v t)) (t • v):=
    selected_mass_derivative b σ hσ hlower p (t • v) hpos hp
  have hh:=hd.comp_hasDerivAt t hv
  apply HasDerivAt.of_isLittleO
  simpa only [Function.comp_def,massLine,offsetLine,massDerivative_apply,Submodule.coe_smul,mul_comm] using hh.isLittleO

/-- Actual mass-value curvature is bounded below uniformly in row rank.
The current theorem is differential on an affine basis; its constants
are suitable for taking limits to singular and duplicate-site systems. -/
theorem mass_value_lower_taylor (b:AffineBasis V ℝ (FSC.Coord d))
    (p:V→ℝ) (v:centeredGauge V) (hp:∑i,p i=1) (m:ℝ) (hm:1≤ m)
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log m)/m)
    (hbox:∀t∈Icc (0:ℝ) 1,∀i,1/(2*m)≤ massLine p v t i∧massLine p v t i≤(3/2)/m):
    optimizedValue b p-((selectedOffsets b p:V→ℝ) ⬝ᵥ (v:V→ℝ))-
      (16384*Real.pi^2*(1+Real.log m))*(∑i,((v:V→ℝ) i)^2)≤
      optimizedValue b (p+(v:V→ℝ)):=by
  let K:ℝ:=(32768*Real.pi^2*(1+Real.log m))*(∑i,((v:V→ℝ) i)^2)
  let f:ℝ→ℝ:=fun t=>optimizedValue b (massLine p v t)+(K/2)*t^2
  let g:ℝ→ℝ:=fun t=>massDerivative (v:V→ℝ) (offsetLine b p v t)+K*t
  let g':ℝ→ℝ:=fun t=>massDerivative (v:V→ℝ) (deriv (offsetLine b p v) t)+K
  have hpos (t:ℝ) (ht:t∈Icc (0:ℝ) 1):∀i,0< massLine p v t i:=
    fun i=>lt_of_lt_of_le (by positivity) (hbox t ht i).1
  have hf (t:ℝ) (ht:t∈Icc (0:ℝ) 1):HasDerivAt f (g t) t:=by
    have ha:=hasDerivAt_massLine_value b p v hp t (hpos t ht)
    have hpoly:HasDerivAt (fun s:ℝ=>(K/2)*s^2) (K*t) t:=by
      convert (hasDerivAt_pow 2 t).const_mul (K/2) using 1 <;> ring
    exact ha.add hpoly
  have hg (t:ℝ) (ht:t∈Icc (0:ℝ) 1):HasDerivAt g (g' t) t:=by
    have hd:HasDerivAt (offsetLine b p v) (deriv (offsetLine b p v) t) t:=
      ((offsetLine_C1 b p v hp t (hpos t ht)).differentiableAt (by norm_num)).hasDerivAt
    have hD:HasDerivAt (fun s:ℝ=>massDerivative (v:V→ℝ) (offsetLine b p v s))
        (massDerivative (v:V→ℝ) (deriv (offsetLine b p v) t)) t:=by
      simpa only [Function.comp_def] using (massDerivative (v:V→ℝ)).hasFDerivAt.comp_hasDerivAt t hd
    have hlin:HasDerivAt (fun s:ℝ=>K*s) K t:=by simpa using (hasDerivAt_id t).const_mul K
    exact hD.add hlin
  have hnonneg (t:ℝ) (ht:t∈Icc (0:ℝ) 1):0≤ g' t:=by
    have hh:=offsetLine_pairing_bound b p v hp m hm hB t (hbox t ht)
    change _≤ K at hh
    dsimp [g']
    rw [massDerivative_apply]
    simp only [dotProduct,mul_comm] at hh ⊢
    linarith
  have hconv:ConvexOn ℝ (Icc (0:ℝ) 1) f:=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0:ℝ) 1)
      (fun t ht=>(hf t ht).continuousAt.continuousWithinAt)
      (fun t ht=>(hf t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht=>(hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht=>hnonneg t (interior_subset ht))
  have hs:=hconv.le_slope_of_hasDerivAt (show (0:ℝ)∈Icc 0 1 by norm_num)
    (show (1:ℝ)∈Icc 0 1 by norm_num) (by norm_num) (hf 0 (by norm_num))
  have hf0:f 0=optimizedValue b p:=by simp [f,massLine]
  have hf1:f 1=optimizedValue b (p+(v:V→ℝ))+K/2:=by simp [f,massLine]
  have hg0:g 0=-((selectedOffsets b p:V→ℝ) ⬝ᵥ (v:V→ℝ)):=by
    simp [g,massDerivative_apply,offsetLine,massLine,dotProduct,mul_comm]
  rw [slope_def_field,hf1,hf0,hg0] at hs
  norm_num at hs
  dsimp [K] at hs
  linarith

end NegativeVotingBoundedMassTaylor
