import GaussianSecondChaosAbsorption

/-! Scalar consequences of the refined local covariance curvature. The
diagonal contribution costs only a square root of the alphabet size. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set Asymptotics
open scoped Topology
namespace NegativeVotingLocalRectangleAbsorption
open NegativeVotingGaussianMaximumSecondMoment

lemma refined_curvature_controls_rectangle (α a b m R : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 1 ≤ m)
    (hR : α^2*(a^2/96+b^2/(48*m)) ≤ R) :
    0 ≤ R ∧ α^2*a^2 ≤ 96*R ∧
      α^2*a*b ≤ 96*Real.sqrt m*R ∧
      α^2*(a^2+6*a*b) ≤ 672*Real.sqrt m*R := by
  have hm0 : 0 < m := by linarith
  have hs0 := Real.sqrt_pos.mpr hm0
  have hs := Real.sq_sqrt hm0.le
  have hs1 : 1 ≤ Real.sqrt m := by
    apply (Real.le_sqrt (by norm_num) hm0.le).mpr
    simpa using hm
  have hR0 : 0 ≤ R := (by positivity : 0 ≤ α^2*(a^2/96+b^2/(48*m))).trans hR
  have hscaled : α^2*(m*a^2+2*b^2) ≤ 96*m*R := by
    have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ 96*m by positivity)
    convert hh using 1 <;> field_simp <;> ring
  have hdiag : α^2*a^2 ≤ 96*R := by
    have hh := mul_le_mul_of_nonneg_left hR (show (0:ℝ) ≤ 96 by norm_num)
    have hn : 0 ≤ α^2*(b^2/(48*m)) := by positivity
    nlinarith
  have hcross : α^2*a*b ≤ 96*Real.sqrt m*R := by
    have hh := mul_nonneg (sq_nonneg α) (sq_nonneg (Real.sqrt m*a-b))
    have hrest : 0 ≤ α^2*b^2 := by positivity
    have htwice : 2*Real.sqrt m*(α^2*a*b) ≤ 96*m*R := by nlinarith [hscaled]
    apply (mul_le_mul_iff_right₀ hs0).mp
    have hnon : 0 ≤ α^2*a*b := by positivity
    nlinarith [htwice]
  refine ⟨hR0,hdiag,hcross,?_⟩
  have hd : 96*R ≤ 96*Real.sqrt m*R := by nlinarith
  nlinarith only [hdiag,hd,hcross]

/-- The two actual rectangles may be composed with the equal-diagonal
second-chaos estimate without paying a full factor m. -/
theorem rectangle_second_loss (α a b m R Rs Eref E Es C G K : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 1 ≤ m)
    (hcurv : α^2*(a^2/96+b^2/(48*m)) ≤ R)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hdef : Rs ≤ R+8*G*α^2*a*b)
    (hfree : Eref-Es ≤ C*Rs)
    (henergy : |E-Es| ≤ K*α^2*(a^2+6*a*b)) :
    Eref-E ≤ (C*(1+768*G*Real.sqrt m)+672*K*Real.sqrt m)*R := by
  obtain ⟨hR0,_,hcross,hrect⟩ :=
    refined_curvature_controls_rectangle α a b m R ha hb hm hcurv
  have hc := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 8*G by positivity)
  have hr : Rs ≤ (1+768*G*Real.sqrt m)*R := by nlinarith only [hdef,hc]
  have hce := mul_le_mul_of_nonneg_left hr hC
  have hk := mul_le_mul_of_nonneg_left hrect hK
  have hneg := neg_le_of_abs_le henergy
  nlinarith only [hfree,hce,hk,hneg]

lemma log_power_sqrt_ratio_bound (k : ℕ) (m r : ℝ)
    (hm : 1 ≤ m) (hl : 1 ≤ Real.log m) (hr : 0 ≤ r) (hrm : r ≤ 2/m) :
    r*(1+Real.log m)^k*Real.sqrt m ≤
      (2:ℝ)^(k+1)*(Real.log m)^k/m^(1/2:ℝ) := by
  have hm0 : 0 < m := by linarith
  have hL : 0 ≤ 1+Real.log m := by linarith
  have hl0 : 0 ≤ Real.log m := by linarith
  have hb : 1+Real.log m ≤ 2*Real.log m := by linarith
  have hpow := pow_le_pow_left₀ hL hb k
  have hs := Real.sq_sqrt hm0.le
  have hs0 := Real.sqrt_pos.mpr hm0
  have hx : r*(1+Real.log m)^k*Real.sqrt m ≤
      (2/m)*(2*Real.log m)^k*Real.sqrt m := by gcongr
  apply hx.trans_eq
  rw [←Real.sqrt_eq_rpow,mul_pow,pow_succ]
  field_simp
  nlinarith [hs]

/-- Any fixed power of log(m) times sqrt(m) is absorbed uniformly in the
entire voting interval r≤1/(m-1), with the dimension threshold first. -/
theorem eventually_uniform_polylog_sqrt_small (C ε : ℝ) (k : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀r : ℝ, 0 ≤ r → r ≤ 1/((n:ℝ)+1) →
      r*(C*(1+Real.log ((n:ℝ)+2))^k*Real.sqrt ((n:ℝ)+2)) < ε := by
  have ht : Tendsto (fun n:ℕ => (Real.log ((n:ℝ)+2))^k/((n:ℝ)+2)^(1/2:ℝ)) atTop (𝓝 0) := by
    convert ((isLittleO_log_rpow_rpow_atTop (k:ℝ) (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero).comp
      size_tendsto using 1
    funext n
    simp only [Function.comp_def,Real.rpow_natCast]
  have htC : Tendsto (fun n:ℕ => (C*2^(k+1))*((Real.log ((n:ℝ)+2))^k/((n:ℝ)+2)^(1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (C*2^(k+1))
  filter_upwards [htC.eventually (Iio_mem_nhds hε),
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1] with n hn hl
  intro r hr hrange
  have hm : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hr2 : r ≤ 2/((n:ℝ)+2) := hrange.trans ((div_le_div_iff₀ (by positivity) hm).mpr
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hb := mul_le_mul_of_nonneg_left (log_power_sqrt_ratio_bound k ((n:ℝ)+2) r
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hl hr hr2) hC
  apply lt_of_le_of_lt _ hn
  convert hb using 1 <;> ring

end NegativeVotingLocalRectangleAbsorption
