import GaussianNearBalancedTailLogBound
import GaussianExteriorReferenceBounds
import GaussianSecondChaosAbsorption

/-! A single dimension-free threshold and explicit smoothing parameters for
all voting correlations. The estimate concerns the full signed chaos tail. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology
namespace NegativeVotingNearBalancedTailUniform
open NegativeVotingNearBalancedTailLogBound NegativeVotingNearBalancedHighTailComparison
  NegativeVotingSignedHighTailComparison NegativeVotingFan NegativeVotingFanSelectedOffsets
  NegativeVotingFanInverse NegativeVotingRegularReferenceNormalization
  NegativeVotingExteriorReference NegativeVotingSecondChaosAbsorption NegativeVotingBalancedReference

lemma trace_log_le (m α:ℝ) (hm:1≤ m) (hα:0<α)
    (hlo:Real.sqrt (1+Real.log m)/(2*m)≤ α) :
    Real.log (m/(α/2))≤4096*(1+Real.log m)+1 := by
  have hm0:0< m:=by linarith
  have hlog:0≤ Real.log m:=Real.log_nonneg hm
  have hs:1≤ Real.sqrt (1+Real.log m):=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have hsmall:1/(2*m)≤ α:=(div_le_div_of_nonneg_right hs (by positivity)).trans hlo
  have hh:m/(α/2)≤4*m^2:=by
    apply (div_le_iff₀ (by positivity)).mpr
    have ha:1≤ α*(2*m):=(div_le_iff₀ (by positivity)).mp hsmall
    nlinarith [mul_le_mul_of_nonneg_left ha hm0.le]
  have hl:=Real.log_le_log (show 0< m/(α/2) by positivity) hh
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  have h4:Real.log (4:ℝ)≤3:=by
    have hh:=Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
    norm_num at hh ⊢
    exact hh
  linarith

/-- Fixed universal constant, with the threshold chosen before the scale,
ambient dimension, row perturbation, mass perturbation and voting parameter. -/
theorem eventually_near_balanced_signed_tail_log_le :
    ∀ᶠ n:ℕ in atTop,∀ (d:ℕ) (R D:Fin (n+2)→FSC.Coord d),
    (∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ)) →
    2≤ Module.finrank ℝ (FSC.Coord d) →
    ∀α:ℝ,0<α →
    Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/(2*((n+2:ℕ):ℝ))≤ α →
    α≤10*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) →
    ∑i,‖D i‖^2≤ α^2/256 →
    ∀v:centeredGauge (Fin (n+2)),
    (∀i,|(v:Fin (n+2)→ℝ) i|≤1/(2*((n+2:ℕ):ℝ))) →
    ∀r:ℝ,0< r → r≤1/((n:ℝ)+1) →
    |cellTailEnergy (-r) 3
      (α•R+D,selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)→ℝ))) -
     cellTailEnergy (-r) 3 (α•R,selectedOffsets (α•R) (fun _=>((n+2:ℕ):ℝ)⁻¹))| ≤
      tailLogConstant*(1+Real.log ((n+2:ℕ):ℝ))^10*r^3*
        ((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_uniform_payment_small 0 0 (1/8193) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)] with n hn hsmall
  intro d R D hG hdim α hα hlo hhi hD v hv r hr hrange
  let m:ℝ:=(n+2:ℕ)
  let L:=1+Real.log m
  let q:=4096*L
  let b:=8192*L+1
  let τ:=Real.sqrt (1/b)
  let σ:=b*r
  have hm:1≤ m:=by dsimp [m];exact_mod_cast (show 1≤n+2 by omega)
  have hm0:0< m:=by linarith
  have hL:1≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hb:0< b:=by dsimp [b];linarith
  have hτ:0<τ:=Real.sqrt_pos.mpr (by positivity)
  have hτsq:τ^2=1/b:=Real.sq_sqrt (by positivity)
  have hτ1:τ≤1:=by
    have hh:1/b≤1:=(div_le_iff₀ hb).mpr (by dsimp [b];linarith)
    nlinarith [sq_nonneg (τ-1)]
  have hσ:0<σ:=mul_pos hb hr
  have hσbound:σ≤8193*L*r:=by dsimp [σ,b];nlinarith
  have hσ1:σ<1:=by
    have hh:=hsmall r hr.le hrange
    simp only [zero_mul,add_zero,mul_one] at hh
    have hh':r*L<1/8193:=by simpa [L,m,Nat.cast_add,Nat.cast_ofNat] using hh
    nlinarith only [hσbound,hh']
  have hq:2≤ q:=by dsimp [q];linarith
  have ht:τ^2=1/(2*q+1):=by rw [hτsq];dsimp [b,q];ring
  have hqlog:4096*Real.log m≤ q:=by dsimp [q,L];linarith
  have hτlog:τ^2*L≤1:=by
    rw [hτsq]
    calc
      1/b*L=L/b:=by ring
      _≤1:=(div_le_iff₀ hb).mpr (by dsimp [b];linarith)
  have hscale:(1/4)*Real.sqrt L/m≤ α/2:=by
    convert (div_le_div_of_nonneg_right hlo (show (0:ℝ)≤2 by norm_num)) using 1 <;> ring
  have htrace:Real.log (m/(α/2))≤ q+1:=trace_log_le m α hm hα hlo
  have hh:=near_balanced_signed_tail_abs_le (by omega:3≤ n+2) R D hG hdim α hα hD
    (1/4) (by norm_num) hscale v hv τ σ q hτ hσ hσ1 hq ht hqlog hτlog htrace
  have hsmooth:τ^2*σ=r:=by dsimp [σ];rw [hτsq];field_simp
  rw [hsmooth] at hh
  have hcoef:=coefficient_log_bound (n+2) α τ σ (∑i,‖D i‖^2)
    (∑i,((v:Fin (n+2)→ℝ) i)^2) hm hα hτ.le hτ1 hσ.le
    (by positivity) (by positivity) hlo hhi
  apply hh.trans (hcoef.trans ?_)
  have hc:0≤ tailBase:=base_pos.2.2.2.2.2.1.le
  calc
    _≤ tailBase*(8193*L*r)^3*L^7*((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2)):=by gcongr
    _=tailLogConstant*(1+Real.log ((n+2:ℕ):ℝ))^10*r^3*
      ((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2)):=by
        dsimp [tailLogConstant,L,m];ring

/-- The physical reference scale automatically lies in the scalar interval.
No numerical moment, trace, gap or smoothing premise remains. -/
theorem eventually_reference_near_balanced_signed_tail_log_le :
    ∀ᶠ n:ℕ in atTop,∀ (d:ℕ) (R D:Fin (n+2)→FSC.Coord d),
    (∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ)) →
    2≤ Module.finrank ℝ (FSC.Coord d) →
    ∑i,‖D i‖^2≤(referenceScale n)^2/256 →
    ∀v:centeredGauge (Fin (n+2)),
    (∀i,|(v:Fin (n+2)→ℝ) i|≤1/(2*((n+2:ℕ):ℝ))) →
    ∀r:ℝ,0< r → r≤1/((n:ℝ)+1) →
    |cellTailEnergy (-r) 3
      (referenceScale n•R+D,selectedOffsets (referenceScale n•R+D)
        ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)→ℝ))) -
     cellTailEnergy (-r) 3 (referenceScale n•R,
        selectedOffsets (referenceScale n•R) (fun _=>((n+2:ℕ):ℝ)⁻¹))| ≤
      tailLogConstant*(1+Real.log ((n+2:ℕ):ℝ))^10*r^3*
        ((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2)) := by
  filter_upwards [eventually_near_balanced_signed_tail_log_le,
    eventually_reference_scale_bounds] with n hn hscale
  intro d R D hG hdim hD v hv r hr hrange
  have ha:=referenceScale_pos n
  have hm:0<((n+2:ℕ):ℝ):=by positivity
  have hL:0≤1+Real.log ((n+2:ℕ):ℝ):=by
    positivity [Real.log_nonneg (show (1:ℝ)≤((n+2:ℕ):ℝ) by exact_mod_cast (show 1≤n+2 by omega))]
  have hs:=Real.sq_sqrt hL
  have hlo:Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/(2*((n+2:ℕ):ℝ))≤ referenceScale n:=by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh:(1+Real.log ((n+2:ℕ):ℝ))≤(referenceScale n)^2*((n+2:ℕ):ℝ)^2:=by
      apply (div_le_iff₀ (sq_pos_of_pos hm)).mp
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale.1
    nlinarith [Real.sqrt_nonneg (1+Real.log ((n+2:ℕ):ℝ)),
      mul_pos ha hm]
  have hhi:referenceScale n≤10*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ):=by
    apply (le_div_iff₀ hm).mpr
    have hh:(referenceScale n)^2*((n+2:ℕ):ℝ)^2≤20*(1+Real.log ((n+2:ℕ):ℝ)):=by
      apply (le_div_iff₀ (sq_pos_of_pos hm)).mp
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale.2
    nlinarith [Real.sqrt_nonneg (1+Real.log ((n+2:ℕ):ℝ)),mul_pos ha hm]
  exact hn d R D hG hdim (referenceScale n) ha hlo hhi hD v hv r hr hrange

end NegativeVotingNearBalancedTailUniform
