import Mathlib

/-! Scalar exterior absorption with the exact subquadratic alphabet exponent.
This module does not assert any Gaussian estimate; its scalar hypotheses are
instantiated from actual routing and covariance estimates in separate modules. -/
noncomputable section
set_option maxHeartbeats 2000000
open Filter
open scoped Topology
namespace NegativeVotingExteriorRelativeAlgebra

theorem sqrt_nested_product (C m L J : ℝ) (hC:0 ≤ C) (hm:0 < m)
    (hL:0 < L) (hJ:0 < J) :
    Real.sqrt (C*Real.sqrt (m^2*Real.sqrt m*L*J))=
      Real.sqrt C*m^(5/8:ℝ)*L^(1/4:ℝ)*J^(1/4:ℝ) := by
  rw [Real.sqrt_mul hC]
  have he : Real.sqrt (Real.sqrt (m^2*Real.sqrt m*L*J))=
      m^(5/8:ℝ)*L^(1/4:ℝ)*J^(1/4:ℝ) := by
    simp_rw [Real.sqrt_eq_rpow]
    rw [←Real.rpow_mul (by positivity),Real.mul_rpow (by positivity) hJ.le,
      Real.mul_rpow (by positivity) hL.le,Real.mul_rpow (by positivity) (by positivity),
      ←Real.rpow_natCast,←Real.rpow_mul hm.le,←Real.rpow_mul hm.le,
      ←Real.rpow_add hm]
    norm_num
  rw [he]
  ring

theorem floor_negative_power (m L c : ℝ) (hm:0 < m) (hL:0 < L) (hc:0 < c) :
    (c/(m^3*Real.sqrt L))^(-3/4:ℝ)=
      c^(-3/4:ℝ)*m^(9/4:ℝ)*L^(3/8:ℝ) := by
  rw [Real.div_rpow hc.le (by positivity),Real.mul_rpow (by positivity) (by positivity),
    Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hm.le,←Real.rpow_mul hL.le]
  norm_num
  rw [Real.rpow_neg hm.le,Real.rpow_neg hL.le]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

/-- Routing mismatch and the exterior deficit floor yield a linear J-bound.
After dividing the signed-tail coefficient by m, the power is 15/8 < 2. -/
theorem sqrt_mismatch_relative (C m L c J E : ℝ) (hC:0 ≤ C) (hm:1 ≤ m)
    (hL:1 ≤ L) (hc:0 < c) (hE:0 ≤ E)
    (hfloor:c/(m^3*Real.sqrt L) ≤ J)
    (hmis:E ≤ C*Real.sqrt (m^2*Real.sqrt m*L*J)) :
    Real.sqrt E ≤ Real.sqrt C*c^(-3/4:ℝ)*m^(23/8:ℝ)*L*J := by
  have hmp : 0 < m := by linarith
  have hLp : 0 < L := by linarith
  have hfp : 0 < c/(m^3*Real.sqrt L) := by positivity
  have hJ : 0 < J := hfp.trans_le hfloor
  have hJneg := Real.rpow_le_rpow_of_nonpos hfp hfloor (by norm_num : (-3/4:ℝ) ≤ 0)
  rw [floor_negative_power m L c hmp hLp hc] at hJneg
  have hJeq : J^(1/4:ℝ)=J*J^(-3/4:ℝ) := by
    have hh := Real.rpow_add hJ 1 (-3/4:ℝ)
    norm_num at hh
    simpa only [neg_div] using hh
  have hbase := Real.sqrt_le_sqrt hmis
  rw [sqrt_nested_product C m L J hC hmp hLp hJ,hJeq] at hbase
  have hcoeff : 0 ≤ Real.sqrt C*m^(5/8:ℝ)*L^(1/4:ℝ)*J := by positivity
  have hupper := mul_le_mul_of_nonneg_left hJneg hcoeff
  have hnorm : (Real.sqrt C*m^(5/8:ℝ)*L^(1/4:ℝ)*J)*
      (c^(-3/4:ℝ)*m^(9/4:ℝ)*L^(3/8:ℝ))=
      Real.sqrt C*c^(-3/4:ℝ)*m^(23/8:ℝ)*L^(5/8:ℝ)*J := by
    have hmEq : m^(5/8:ℝ)*m^(9/4:ℝ)=m^(23/8:ℝ) := by
      rw [←Real.rpow_add hmp];norm_num
    have hLEq : L^(1/4:ℝ)*L^(3/8:ℝ)=L^(5/8:ℝ) := by
      rw [←Real.rpow_add hLp];norm_num
    calc
      _ = Real.sqrt C*c^(-3/4:ℝ)*(m^(5/8:ℝ)*m^(9/4:ℝ))*
          (L^(1/4:ℝ)*L^(3/8:ℝ))*J := by ring
      _ = _ := by rw [hmEq,hLEq]
  rw [hnorm] at hupper
  have hLpow : L^(5/8:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (5/8:ℝ) ≤ 1)
  have hlast := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLpow (show 0 ≤ Real.sqrt C*c^(-3/4:ℝ)*m^(23/8:ℝ) by positivity)) hJ.le
  have hmid : Real.sqrt C*m^(5/8:ℝ)*L^(1/4:ℝ)*(J*J^(-3/4:ℝ)) ≤
      Real.sqrt C*c^(-3/4:ℝ)*m^(23/8:ℝ)*L^(5/8:ℝ)*J := by
    simpa only [mul_assoc] using hupper
  exact hbase.trans (hmid.trans hlast)

/-- The full cubic tail divided by the alphabet is absorbable relative to J. -/
theorem cubic_tail_relative (C K m L c J E H r : ℝ)
    (hC:0 ≤ C) (hK:0 ≤ K) (hm:1 ≤ m) (hL:1 ≤ L) (hc:0 < c)
    (hE:0 ≤ E) (hr:0 ≤ r) (hfloor:c/(m^3*Real.sqrt L) ≤ J)
    (hmis:E ≤ C*Real.sqrt (m^2*Real.sqrt m*L*J))
    (hH:|H| ≤ K*r^3*L^3*Real.sqrt E/m) :
    |H| ≤ (K*Real.sqrt C*c^(-3/4:ℝ))*r^3*m^(15/8:ℝ)*L^4*J := by
  have hmp : 0 < m := by linarith
  have hb := sqrt_mismatch_relative C m L c J E hC hm hL hc hE hfloor hmis
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ K*r^3*L^3/m by positivity)
  have he : m^(23/8:ℝ)/m=m^(15/8:ℝ) := by
    have hh := Real.rpow_sub hmp (23/8:ℝ) 1
    norm_num at hh
    exact hh.symm
  refine hH.trans ?_
  calc
    K*r^3*L^3*Real.sqrt E/m ≤ (K*r^3*L^3/m)*
        (Real.sqrt C*c^(-3/4:ℝ)*m^(23/8:ℝ)*L*J) := by convert hh using 1 <;> ring
    _ = (K*Real.sqrt C*c^(-3/4:ℝ))*r^3*(m^(23/8:ℝ)/m)*L^4*J := by ring
    _ = _ := by rw [he]

end NegativeVotingExteriorRelativeAlgebra
