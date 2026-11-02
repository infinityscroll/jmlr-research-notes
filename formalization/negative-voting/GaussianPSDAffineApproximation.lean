import GaussianPositiveCovarianceFactor
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit bounded affine-basis approximation of a PSD row realization.
The perturbation is S+tI, so no continuity of a chosen square root is needed. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingPSDAffineApproximation
open NegativeVotingPositiveCovariance
variable {V E:Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem positive_operator_injective (A:E→L[ℝ]E) (hA:A∈pdCone):Function.Injective A:=by
  intro x y hxy
  by_contra hne
  have hn:x-y≠0:=sub_ne_zero.mpr hne
  have hz:A (x-y)=0:=by rw [map_sub,hxy,sub_self]
  have hp:=hA.2 (x-y) hn
  rw [hz,inner_zero_right] at hp
  exact (lt_irrefl (0:ℝ)) hp

def positiveOperatorEquiv (A:E→L[ℝ]E) (hA:A∈pdCone):E≃L[ℝ]E:=
  ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr (positive_operator_injective A hA))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (positive_operator_injective A hA)))

@[simp] theorem positiveOperatorEquiv_apply (A:E→L[ℝ]E) (hA:A∈pdCone) (x:E):
    positiveOperatorEquiv A hA x=A x:=rfl

theorem exists_bounded_affine_approximation (b:AffineBasis V ℝ E)
    (hc:(∑i,b i)=0) (hu:∀i,‖b i‖≤1)
    (S:E→L[ℝ]E) (hS:S∈psdCone) (R:ℝ) (hR:0< R) (hrow:∀i,‖S (b i)‖≤ R):
    ∃a:ℕ→AffineBasis V ℝ E,
      (∀k,(∑i,a k i)=0)∧(∀k i,‖a k i‖≤2*R)∧
      Tendsto (fun k=>(a k:V→E)) atTop (𝓝 (fun i=>S (b i))):=by
  classical
  let ε:ℕ→ℝ:=fun k=>R/((k:ℝ)+1)
  have hε:∀k,0<ε k:=by intro k;dsimp [ε];positivity
  have hεle:∀k,ε k≤ R:=by
    intro k
    dsimp [ε]
    apply (div_le_iff₀ (show 0<(k:ℝ)+1 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hεlim:Tendsto ε atTop (𝓝 0):=by
    simpa only [mul_one_div,mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul R
  let Q:ℕ→E≃L[ℝ]E:=fun k=>positiveOperatorEquiv
    (S+ε k • ContinuousLinearMap.id ℝ E) (regularize_positive hS (hε k))
  let a:ℕ→AffineBasis V ℝ E:=fun k=>mappedBasis b (Q k)
  have ha (k:ℕ) (i:V):a k i=S (b i)+ε k • b i:=rfl
  refine ⟨a,?_,?_,?_⟩
  · intro k
    simp only [ha,Finset.sum_add_distrib,←map_sum,←Finset.smul_sum,hc,map_zero,smul_zero,zero_add]
  · intro k i
    rw [ha]
    calc
      _≤‖S (b i)‖+‖ε k • b i‖:=norm_add_le _ _
      _=‖S (b i)‖+ε k*‖b i‖:=by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hε k)]
      _≤ R+ε k*1:=add_le_add (hrow i) (mul_le_mul_of_nonneg_left (hu i) (hε k).le)
      _≤2*R:=by have hh:=hεle k;linarith
  · apply tendsto_pi_nhds.mpr
    intro i
    have hh:= (tendsto_const_nhds:Tendsto (fun _:ℕ=>S (b i)) atTop (𝓝 (S (b i)))).add
      (hεlim.smul_const (b i))
    simpa only [ha,zero_smul,add_zero] using hh

end NegativeVotingPSDAffineApproximation
