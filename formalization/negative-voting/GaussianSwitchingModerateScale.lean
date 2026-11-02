import GaussianSwitchingLabelSum

/-! Uniform scalar absorption on the moderate-amplitude interval.  The
exponent q is fixed by the alphabet, not chosen separately for the amplitude. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Topology
namespace NegativeVotingSwitchingModerate

theorem moderate_near_bound (m θ q A B : ℝ) (hm : 1 ≤ m) (hθ : 0 < θ)
    (hq : 0 ≤ q) (hA : 0 < A) (hB : 0 ≤ B)
    (hqlog : A*Real.log m ≤ q) (hfloor : m^(-B) ≤ θ) :
    m^(1/(q+1))*θ^(2*q/(q+1)) ≤ Real.exp ((1+2*B)/A)*θ^2 := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hqp : 0 < q+1 := by linarith
  have hneg : -(2:ℝ)/(q+1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hqp.le
  have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hm0 (-B)) hfloor hneg
  rw [←Real.rpow_mul hm0.le] at hp
  have he : (-B)*(-(2:ℝ)/(q+1))=2*B/(q+1) := by ring
  rw [he] at hp
  have hcoef : m^(1/(q+1))*θ^(-(2:ℝ)/(q+1)) ≤ Real.exp ((1+2*B)/A) := by
    have hb := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hm0.le (1/(q+1)))
    rw [←Real.rpow_add hm0] at hb
    have hadd : 1/(q+1)+2*B/(q+1)=(1+2*B)/(q+1) := by ring
    rw [hadd] at hb
    refine hb.trans ?_
    rw [Real.rpow_def_of_pos hm0]
    apply Real.exp_le_exp.mpr
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hqp hA).mpr
    have hC : 0 ≤ 1+2*B := by linarith
    have hmul := mul_le_mul_of_nonneg_left (hqlog.trans (by linarith : q≤q+1)) hC
    nlinarith
  have hsplit : θ^(2*q/(q+1))=θ^2*θ^(-(2:ℝ)/(q+1)) := by
    rw [←Real.rpow_two, ←Real.rpow_add hθ]
    congr 1
    field_simp
    ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg θ)]

theorem moderate_far_bound (m θ q δ : ℝ) (hm : 1 ≤ m) (hθ : 0 < θ)
    (hq : 2 ≤ q) (hδ : 0 < δ) (hexp : 1 ≤ δ*(q-2))
    (hceiling : θ ≤ m^(-1-δ)) :
    θ^q/(1/m)^(q-1) ≤ θ^2 := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hp := Real.rpow_le_rpow hθ.le hceiling (sub_nonneg.mpr hq)
  rw [←Real.rpow_mul hm0.le] at hp
  have hratio : θ^(q-2)/(1/m)^(q-1) ≤ 1 := by
    have hb := div_le_div_of_nonneg_right hp
      (Real.rpow_nonneg (by positivity : 0≤1/m) (q-1))
    have hinv : (1/m)^(q-1)=m^(-(q-1)) := by
      rw [one_div,Real.rpow_neg hm0.le,Real.inv_rpow hm0.le]
    rw [hinv,←Real.rpow_sub hm0] at hb
    have he : (-1-δ)*(q-2)-(-(q-1))=1-δ*(q-2) := by ring
    rw [he] at hb
    rw [hinv]
    exact hb.trans (by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hm (by linarith : 1-δ*(q-2)≤0))
  have he : θ^q=θ^2*θ^(q-2) := by
    rw [←Real.rpow_two,←Real.rpow_add hθ]
    congr 1
    ring
  rw [he,mul_div_assoc]
  nlinarith [mul_le_mul_of_nonneg_left hratio (sq_nonneg θ)]

/-- Joins the two scalar contributions of the finite-label integral bound. -/
theorem moderate_cap_bound (m θ q A B C δ : ℝ) (hm : 1 ≤ m) (hθ : 0 < θ)
    (hq : 2 ≤ q) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hqlog : A*Real.log m ≤ q) (hδ : 0 < δ) (hexp : 1 ≤ δ*(q-2))
    (hfloor : m^(-B) ≤ θ) (hceiling : θ ≤ m^(-1-δ)) :
    C*m^(1/(q+1))*θ^(2*q/(q+1))+θ^q/(1/m)^(q-1) ≤
      (C*Real.exp ((1+2*B)/A)+1)*θ^2 := by
  have hn := moderate_near_bound m θ q A B hm hθ (by linarith) hA hB hqlog hfloor
  have hf := moderate_far_bound m θ q δ hm hθ hq hδ hexp hceiling
  nlinarith [mul_le_mul_of_nonneg_left hn hC]

end NegativeVotingSwitchingModerate
