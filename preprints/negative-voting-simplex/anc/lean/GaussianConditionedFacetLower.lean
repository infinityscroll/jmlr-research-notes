import GaussianConditionedFacetWitness
import GaussianFanOffsetRange

/-! Explicit exponential and polynomial lower bounds for actual conditioned
Gaussian simplex facets, derived from actual cell masses and score geometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace NegativeVotingConditionedFacet
open NegativeVotingFan NegativeVotingCapTail
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- No offset-size or boundary-probability premise is supplied: both follow
from actual winning-cell masses and the displayed score condition bound. -/
theorem intrinsicProbability_exp_lower_of_masses
    (B : AffineBasis V ℝ (FSC.Coord d)) (hB : ∑i,B i=0)
    (hm : 3 ≤ Fintype.card V) (σ D : ℝ) (hσ : 0 < σ) (hD : 0 < D)
    (hlower : CenteredSingularLowerBound B σ) (hrow : ∀i j,‖B i-B j‖ ≤ D)
    (h : V → ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,1/(2*(Fintype.card V : ℝ)) ≤ mass B h i)
    (i j : V) (hij : i≠j) :
    (1/4:ℝ)*Real.exp (-(6*(2*offsetRadius (V:=V) D+unionRadius (V:=V) D)^2+
      2*(offsetRadius (V:=V) D)^2)/σ^2) ≤ intrinsicProbability B h i j := by
  apply intrinsicProbability_exp_lower_uniform B hB hm σ D _ hσ hD
    (offsetRadius_nonneg D hD.le) hlower hrow h
  exact centered_offsets_le_of_cell_masses B h B.ind.injective D hD.le hrow hs hmass
  exact hij

theorem offsetRadius_le_unionRadius (D : ℝ) (hD : 0 ≤ D) :
    offsetRadius (V:=V) D ≤ unionRadius (V:=V) D := by
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply mul_le_mul_of_nonneg_left _ hD
  apply Real.sqrt_le_sqrt
  have hh := Real.log_le_log (by positivity : 0 < 2*(Fintype.card V : ℝ))
    (show 2*(Fintype.card V : ℝ) ≤ 2*((Fintype.card V : ℝ)+1) by linarith)
  linarith

/-- A deliberately loose universal exponent budget; only the conditioning
ratio, not the ambient dimension, enters the estimate. -/
theorem witness_exponent_le_log (hm : 3 ≤ Fintype.card V) (σ D : ℝ)
    (hσ : 0 < σ) (hD : 0 < D) (hcond : D/σ ≤ 4) :
    (6*(2*offsetRadius (V:=V) D+unionRadius (V:=V) D)^2+
      2*(offsetRadius (V:=V) D)^2)/σ^2 ≤ 3584*Real.log (Fintype.card V : ℝ) := by
  let m : ℝ := Fintype.card V
  let H := offsetRadius (V:=V) D
  let U := unionRadius (V:=V) D
  have hm3 : (3:ℝ) ≤ m := by dsimp only [m];exact_mod_cast hm
  have hH : 0 ≤ H := offsetRadius_nonneg D hD.le
  have hU : 0 ≤ U := by dsimp [U,unionRadius];positivity
  have hHU : H ≤ U := offsetRadius_le_unionRadius D hD.le
  have hA : 0 ≤ 2*H+U := by positivity
  have hAU : 2*H+U ≤ 3*U := by linarith
  have hA2 := pow_le_pow_left₀ hA hAU 2
  have hH2 := pow_le_pow_left₀ hH hHU 2
  have hnum : 6*(2*H+U)^2+2*H^2 ≤ 56*U^2 := by nlinarith
  have hlog : 0 ≤ Real.log (2*(m+1)) := Real.log_nonneg (by linarith)
  have hU2 : U^2=D^2*(2*Real.log (2*(m+1))) := by
    dsimp [U,unionRadius]
    rw [mul_pow,Real.sq_sqrt (by change 0 ≤ 2*Real.log (2*(m+1));positivity)]
  have hDS : D ≤ 4*σ := (div_le_iff₀ hσ).mp hcond
  have hDS2 : D^2 ≤ 16*σ^2 := by
    have hh := pow_le_pow_left₀ hD.le hDS 2
    nlinarith
  have hm2 : 2*(m+1) ≤ m^2 := by nlinarith [sq_nonneg (m-3)]
  have hlogs : Real.log (2*(m+1)) ≤ 2*Real.log m := by
    have hh := Real.log_le_log (by positivity : 0 < 2*(m+1)) hm2
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hn1 : 6*(2*H+U)^2+2*H^2 ≤ 1792*σ^2*Real.log (2*(m+1)) := by
    rw [hU2] at hnum
    have hh := mul_le_mul_of_nonneg_right hDS2 hlog
    nlinarith
  have hn2 : (6*(2*H+U)^2+2*H^2)/σ^2 ≤ 1792*Real.log (2*(m+1)) := by
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    nlinarith
  change (6*(2*H+U)^2+2*H^2)/σ^2 ≤ 3584*Real.log m
  nlinarith

/-- Every actual facet has an absolute polynomial probability lower bound
under fixed score conditioning, actual positive cell masses, and centered offsets. -/
theorem intrinsicProbability_polynomial_lower
    (B : AffineBasis V ℝ (FSC.Coord d)) (hB : ∑i,B i=0)
    (hm : 3 ≤ Fintype.card V) (σ D : ℝ) (hσ : 0 < σ) (hD : 0 < D)
    (hlower : CenteredSingularLowerBound B σ) (hrow : ∀i j,‖B i-B j‖ ≤ D)
    (hcond : D/σ ≤ 4) (h : V → ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,1/(2*(Fintype.card V : ℝ)) ≤ mass B h i)
    (i j : V) (hij : i≠j) :
    (Fintype.card V : ℝ)^(-(4096:ℝ)) ≤ intrinsicProbability B h i j := by
  let m : ℝ := Fintype.card V
  let E := (6*(2*offsetRadius (V:=V) D+unionRadius (V:=V) D)^2+
    2*(offsetRadius (V:=V) D)^2)/σ^2
  have hm3 : (3:ℝ) ≤ m := by dsimp only [m];exact_mod_cast hm
  have hmpos : 0 < m := by linarith
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hE : E ≤ 3584*Real.log m := witness_exponent_le_log hm σ D hσ hD hcond
  have hquarter : Real.exp (-(2*Real.log m)) ≤ 1/4 := by
    have he : Real.exp (-(2*Real.log m))=(m^2)⁻¹ := by
      have hlp : Real.log (m^2)=2*Real.log m := Real.log_pow m 2
      rw [←hlp,Real.exp_neg,Real.exp_log (sq_pos_of_pos hmpos)]
    rw [he]
    have hm4 : (4:ℝ) ≤ m^2 := by nlinarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hm4
  have hp : (1/4:ℝ)*Real.exp (-E) ≤ intrinsicProbability B h i j := by
    simpa only [E,neg_div] using
      intrinsicProbability_exp_lower_of_masses B hB hm σ D hσ hD hlower hrow h hs hmass i j hij
  calc
    (Fintype.card V : ℝ)^(-(4096:ℝ))=Real.exp (-(4096*Real.log m)) := by
      rw [Real.rpow_def_of_pos hmpos]
      congr 1
      ring
    _ ≤ Real.exp (-(2*Real.log m))*Real.exp (-E) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ (1/4:ℝ)*Real.exp (-E) :=
      mul_le_mul_of_nonneg_right hquarter (Real.exp_pos _).le
    _ ≤ intrinsicProbability B h i j := hp


/-- The same bound in the actual cycle/Hessian facet-probability convention. -/
theorem cycleIntrinsicProbability_polynomial_lower
    (B : AffineBasis V ℝ (FSC.Coord d)) (hB : ∑i,B i=0)
    (hm : 3 ≤ Fintype.card V) (σ D : ℝ) (hσ : 0 < σ) (hD : 0 < D)
    (hlower : CenteredSingularLowerBound B σ) (hrow : ∀i j,‖B i-B j‖ ≤ D)
    (hcond : D/σ ≤ 4) (h : V → ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,1/(2*(Fintype.card V : ℝ)) ≤ mass B h i)
    (i j : V) (hij : i≠j) :
    (Fintype.card V : ℝ)^(-(4096:ℝ)) ≤
      NegativeVotingFanCycle.cycleIntrinsicProbability B h i j := by
  rw [NegativeVotingFanRetained.cycleProbability_eq_intrinsic_facet B h i j hij]
  exact intrinsicProbability_polynomial_lower B hB hm σ D hσ hD hlower hrow hcond h hs hmass i j hij

end NegativeVotingConditionedFacet
