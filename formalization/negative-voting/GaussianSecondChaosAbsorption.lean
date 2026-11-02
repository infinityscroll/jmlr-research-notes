import GaussianCompetitiveSecondChaosComparison
import GaussianGlobalCovarianceDeficit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Scalar absorptions for the actual equal-row second-chaos estimate. The
sublinear alphabet power and the exterior absolute tail are kept separate. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set Asymptotics
open scoped Topology
namespace NegativeVotingSecondChaosAbsorption
open NegativeVotingGaussianMaximumSecondMoment

lemma payment_coefficient_bound (C δ m r:ℝ) (hC:0 ≤ C) (hδ:0 ≤ δ)
    (hm:1 ≤ m) (hl:1 ≤ Real.log m) (hr:0 ≤ r) (hrm:r ≤ 2/m) :
    r*(1+Real.log m)*(1+C*m^δ) ≤ 4*(1+C)*Real.log m/m^(1-δ) := by
  have hm0:0< m:=by linarith
  have hp:1 ≤ m^δ:=Real.one_le_rpow hm hδ
  have hL:0 ≤ 1+Real.log m:=by linarith
  have hL2:1+Real.log m ≤ 2*Real.log m:=by linarith
  have hfactor:1+C*m^δ ≤ (1+C)*m^δ:=by nlinarith
  have hx:r*(1+Real.log m)*(1+C*m^δ) ≤ (2/m)*(2*Real.log m)*((1+C)*m^δ):=by
    gcongr
  have he:m^δ/m=1/m^(1-δ):=by
    have hh:=Real.rpow_sub hm0 δ 1
    rw [Real.rpow_one] at hh
    rw [←hh,show δ-1=-(1-δ) by ring,Real.rpow_neg hm0.le,one_div]
  apply hx.trans_eq
  calc
    _ = 4*(1+C)*Real.log m*(m^δ/m):=by ring
    _ = _:=by rw [he];ring

theorem eventually_uniform_payment_small (C δ ε : ℝ)
    (hC:0 ≤ C) (hδ:0 ≤ δ) (hδ1:δ<1) (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀r:ℝ,0 ≤ r → r ≤ 1/((n:ℝ)+1) →
      r*(1+Real.log ((n:ℝ)+2))*(1+C*((n:ℝ)+2)^δ)<ε := by
  have ht:Tendsto (fun n:ℕ=>Real.log ((n:ℝ)+2)/((n:ℝ)+2)^(1-δ)) atTop (𝓝 0):=by
    convert ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (sub_pos.mpr hδ1)).tendsto_div_nhds_zero).comp
      size_tendsto using 1
    funext n;simp only [Function.comp_def,Real.rpow_one]
  have htC:Tendsto (fun n:ℕ=>4*(1+C)*(Real.log ((n:ℝ)+2)/((n:ℝ)+2)^(1-δ))) atTop (𝓝 0):=by
    simpa only [mul_zero] using ht.const_mul (4*(1+C))
  filter_upwards [htC.eventually (Iio_mem_nhds hε),
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1] with n hn hl
  intro r hr hrange
  have hm:(0:ℝ)<(n:ℝ)+2:=by positivity
  have hr2:r ≤ 2/((n:ℝ)+2):=hrange.trans ((div_le_div_iff₀ (by positivity) hm).mpr
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  exact (payment_coefficient_bound C δ ((n:ℝ)+2) r hC hδ
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hl hr hr2).trans_lt
    (by simpa only [mul_div_assoc,Function.comp_def] using hn)

lemma cutoff_tail_power_bound (m : ℝ) (hm : 1 ≤ m) :
    2160*(1+Real.log m)*Real.exp (-16*(1+Real.log m)) ≤ 2160/m^15 := by
  have hm0:0< m:=by linarith
  have hlog:=Real.log_nonneg hm
  have hL:0 ≤ 1+Real.log m:=by linarith
  have hLm:1+Real.log m ≤ m:=by linarith [Real.log_le_sub_one_of_pos hm0]
  have hexp:Real.exp (-16*(1+Real.log m)) ≤ 1/m^16:=by
    calc
      _ ≤ Real.exp (-16*Real.log m):=Real.exp_le_exp.mpr (by linarith)
      _ = _:=by
        rw [show -16*Real.log m=Real.log m*(-16:ℝ) by ring,←Real.rpow_def_of_pos hm0]
        rw [Real.rpow_neg hm0.le]
        norm_num
  have hh:=mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2160*(1+Real.log m) by positivity)
  have hh2:=mul_le_mul_of_nonneg_right hLm (show 0 ≤ 2160/m^16 by positivity)
  have he:2160/m^16*m=2160/m^15:=by field_simp <;> ring
  calc
    _ ≤ 2160*(1+Real.log m)*(1/m^16):=hh
    _ ≤ 2160/m^16*m:=by convert hh2 using 1 <;> ring
    _ = _:=he

lemma exterior_floor_fourth_power (c m J:ℝ) (hc:0<c) (hm:1 ≤ m)
    (hfloor:c/(m^3*Real.sqrt (1+Real.log m)) ≤ J) : c/m^4 ≤ J := by
  have hm0:0< m:=by linarith
  have hlog:=Real.log_nonneg hm
  have hL:0<1+Real.log m:=by linarith
  have hs:Real.sqrt (1+Real.log m) ≤ m:=by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hm0.le,by nlinarith [Real.log_le_sub_one_of_pos hm0]⟩
  apply le_trans _ hfloor
  apply div_le_div_of_nonneg_left hc.le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ m^3 by positivity)]

/-- The absolute cutoff tail is paid only on the exterior branch. This lemma
makes no local rigidity claim and remains valid as r tends to zero. -/
lemma cutoff_tail_paid (c m J:ℝ) (hc:0<c) (hm:1 ≤ m)
    (hfloor:c/(m^3*Real.sqrt (1+Real.log m)) ≤ J) :
    2160*(1+Real.log m)*Real.exp (-16*(1+Real.log m)) ≤ (2160/c/m^11)*J := by
  have hm0:0< m:=by linarith
  have hj:=exterior_floor_fourth_power c m J hc hm hfloor
  have hh:=mul_le_mul_of_nonneg_left hj (show 0 ≤ 2160/c/m^11 by positivity)
  have he:(2160/c/m^11)*(c/m^4)=2160/m^15:=by field_simp <;> ring
  rw [he] at hh
  exact (cutoff_tail_power_bound m hm).trans hh

theorem eventually_cutoff_tail_paid (c ε:ℝ) (hc:0<c) (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀J:ℝ,
      c/(((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2))) ≤ J →
      2160*(1+Real.log ((n:ℝ)+2))*Real.exp (-16*(1+Real.log ((n:ℝ)+2))) ≤ ε*J := by
  have ht:Tendsto (fun n:ℕ=>(2160/c)/((n:ℝ)+2)^11) atTop (𝓝 0):=
    ((tendsto_pow_atTop (by norm_num : (11:ℕ)≠0)).comp size_tendsto).const_div_atTop (2160/c)
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn
  intro J hj
  have hm:(1:ℝ) ≤ (n:ℝ)+2:=by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hJ:0 ≤ J:=(by positivity : 0 ≤ c/(((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2)))).trans hj
  exact (cutoff_tail_paid c ((n:ℝ)+2) J hc hm hj).trans
    (mul_le_mul_of_nonneg_right hn.le hJ)

lemma second_loss_absorption (r J D A T Q ε:ℝ) (hr:0 ≤ r) (hr1:r ≤ 1)
    (hJ:0 ≤ J) (hε:0 ≤ ε) (hD:D=r*J) (hQ:Q ≤ A*J+T)
    (hA:r*A ≤ ε/2) (hT:T ≤ (ε/2)*J) : r^2*Q ≤ ε*D := by
  have h1:=mul_le_mul_of_nonneg_left hQ (sq_nonneg r)
  have h2:=mul_le_mul_of_nonneg_right hA (show 0 ≤ r*J by positivity)
  have h3:=mul_le_mul_of_nonneg_left hT (sq_nonneg r)
  have h4:=mul_le_mul_of_nonneg_right (show r^2 ≤ r by nlinarith)
    (show 0 ≤ ε/2*J by positivity)
  rw [hD]
  nlinarith only [h1,h2,h3,h4]

end NegativeVotingSecondChaosAbsorption
