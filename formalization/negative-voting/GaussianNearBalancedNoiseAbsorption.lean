import GaussianLocalRectangleAbsorption

/-! One eventual threshold for all scalar coefficients in the actual local
noise comparison, uniformly over the entire voting interval. -/
noncomputable section
set_option maxHeartbeats 1800000
open Filter Set
open scoped Topology
namespace NegativeVotingNearBalancedNoiseAbsorption
open NegativeVotingLocalRectangleAbsorption

theorem eventually_uniform_local_coefficients
    (P₀ M₀ B₀ C₀ H₀:ℝ) (k:ℕ)
    (hP:0≤ P₀) (hM:0≤ M₀) (hB:0≤ B₀) (hC:0≤ C₀) (hH:0≤ H₀) :
    ∀ᶠ n:ℕ in atTop,∀r:ℝ,0≤ r → r≤1/((n:ℝ)+1) →
    let m:ℝ:=(n:ℝ)+2
    let L:=1+Real.log m
    let P:=P₀*m*L
    let M:=M₀*L^13
    let B:=B₀*L^k*Real.sqrt m
    let C:=C₀*L^10
    let H:=H₀*L^2
    r*H≤1/2 ∧ r*B≤1/8 ∧ r^2*Real.sqrt M≤1/16 ∧
    4*r^3*M*P≤1/8 ∧ C*r^2*P≤1/8 ∧ C*r^3≤1/16 := by
  filter_upwards [
    eventually_uniform_polylog_sqrt_small H₀ (1/2) 2 hH (by norm_num),
    eventually_uniform_polylog_sqrt_small B₀ (1/8) k hB (by norm_num),
    eventually_uniform_polylog_sqrt_small (1+M₀) (1/16) 7 (by positivity) (by norm_num),
    eventually_uniform_polylog_sqrt_small (8*M₀*P₀) (1/8) 14 (by positivity) (by norm_num),
    eventually_uniform_polylog_sqrt_small (2*C₀*P₀) (1/8) 11 (by positivity) (by norm_num),
    eventually_uniform_polylog_sqrt_small C₀ (1/16) 10 hC (by norm_num)]
    with n h₁ h₂ h₃ h₄ h₅ h₆
  intro r hr hrange
  dsimp only
  let m:ℝ:=(n:ℝ)+2
  let L:=1+Real.log m
  have hm:1≤ m:=by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hm0:0< m:=by linarith
  have hL:1≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hL0:0≤ L:=by linarith
  have hs:1≤ Real.sqrt m:=(Real.le_sqrt (by norm_num) hm0.le).mpr (by simpa using hm)
  have hr1:r≤1:=hrange.trans ((div_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hrm:r*m≤2:=by
    have hh:r*((n:ℝ)+1)≤1:=(le_div_iff₀ (by positivity)).mp hrange
    dsimp [m];nlinarith
  have hr2:r^2≤ r:=by nlinarith
  have hr3:r^3≤ r:=by
    have hh:=mul_le_mul_of_nonneg_left hr2 hr
    nlinarith
  have hr2m:r^2*m≤2*r:=by nlinarith [mul_le_mul_of_nonneg_left hrm hr]
  have hr3m:r^3*m≤2*r:=by
    have hh:=mul_le_mul_of_nonneg_left hrm (sq_nonneg r)
    nlinarith only [hh,hr2]
  have lift (a:ℝ) (ha:0≤a):r*a≤ r*(a*Real.sqrt m):=by
    calc
      r*a=r*(a*1):=by ring
      _≤ r*(a*Real.sqrt m):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs ha) hr
  have hroot:Real.sqrt (M₀*L^13)≤(1+M₀)*L^7:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hp:L^13≤ L^14:=pow_le_pow_right₀ hL (by omega)
    have hh:=mul_le_mul_of_nonneg_left hp hM
    have hh2:=mul_le_mul_of_nonneg_right (show M₀≤(1+M₀)^2 by nlinarith) (show 0≤ L^14 by positivity)
    nlinarith only [hh,hh2]
  refine ⟨?_,(h₂ r hr hrange).le,?_,?_,?_,?_⟩
  · exact (lift (H₀*L^2) (by positivity)).trans (h₁ r hr hrange).le
  · calc
      r^2*Real.sqrt (M₀*L^13)≤ r*((1+M₀)*L^7):=by gcongr
      _≤ r*((1+M₀)*L^7*Real.sqrt m):=lift _ (by positivity)
      _≤1/16:=(h₃ r hr hrange).le
  · have hh:=mul_le_mul_of_nonneg_left hr3m (show 0≤4*M₀*P₀*L^14 by positivity)
    calc
      4*r^3*(M₀*L^13)*(P₀*m*L)≤ r*(8*M₀*P₀*L^14):=by nlinarith only [hh]
      _≤ r*(8*M₀*P₀*L^14*Real.sqrt m):=lift _ (by positivity)
      _≤1/8:=(h₄ r hr hrange).le
  · have hh:=mul_le_mul_of_nonneg_left hr2m (show 0≤ C₀*P₀*L^11 by positivity)
    calc
      (C₀*L^10)*r^2*(P₀*m*L)≤ r*(2*C₀*P₀*L^11):=by nlinarith only [hh]
      _≤ r*(2*C₀*P₀*L^11*Real.sqrt m):=lift _ (by positivity)
      _≤1/8:=(h₅ r hr hrange).le
  · calc
      (C₀*L^10)*r^3≤ r*(C₀*L^10):=by nlinarith [mul_le_mul_of_nonneg_left hr3 (show 0≤ C₀*L^10 by positivity)]
      _≤ r*(C₀*L^10*Real.sqrt m):=lift _ (by positivity)
      _≤1/16:=(h₆ r hr hrange).le

end NegativeVotingNearBalancedNoiseAbsorption
