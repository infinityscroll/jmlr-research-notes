import GaussianHazardQuantileBounds
import GaussianHazardQuantileAsymptotics

/-! Scalar coefficient bounds for the literal whole-threshold hazard-moment
split. Constants are independent of the alphabet and all model coordinates. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingHazardUniformUpperCoefficients
open WeakSimplex NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianTail NegativeVotingHazardMomentEnvelope
  NegativeVotingHazardQuantileBounds NegativeVotingDensityMomentBounds
  NegativeVotingHazardQuantileAsymptotics

def lowMomentEnvelope (n : ℕ) (a : ℝ) (p q : ℕ) : ℝ :=
  lowCoefficient (n+2) (1-a) (a*upperQuantile n) ((1-4*a)*upperQuantile n) p*
    standardPolynomialMoment (p+q+1)*(1+a*upperQuantile n+(1+a))^(p+q+1)

def highMomentEnvelope (n : ℕ) (a lam : ℝ) (p q : ℕ) : ℝ :=
  highCoefficient (n+2) (1-a) (1+a) (a*upperQuantile n) ((1-4*a)*upperQuantile n) lam p*
    ((1+a)/(Real.sqrt lam*normalPDF 0))*standardPolynomialMoment q*
      (1+a*upperQuantile n+(1+a)/Real.sqrt lam)^q

def lowMomentConstant (p q : ℕ) : ℝ :=
  (2*r 0+4)^(p+1)*standardPolynomialMoment (p+q+1)*3^(p+q+1)

def highMomentConstant (lam : ℝ) (p q : ℕ) : ℝ :=
  (16*4^p*2^(p+2))*(2/(Real.sqrt lam*normalPDF 0))*
    standardPolynomialMoment q*(2+2/Real.sqrt lam)^q

lemma lowMomentConstant_nonneg (p q : ℕ) : 0 ≤ lowMomentConstant p q := by
  unfold lowMomentConstant
  positivity [r_pos 0,standardPolynomialMoment_nonneg (p+q+1)]

lemma highMomentConstant_nonneg (lam : ℝ) (hlam : 0 < lam) (p q : ℕ) :
    0 ≤ highMomentConstant lam p q := by
  unfold highMomentConstant
  positivity [normalPDF_pos 0,standardPolynomialMoment_nonneg q]

lemma linearHazardConstant_quantile (b a : ℝ) (hb : 0 ≤ b)
    (ha : 0 ≤ a) (ha1 : a ≤ 1/16) :
    linearHazardConstant (1-a) (a*b) ≤ (2*r 0+4)*(1+b) := by
  have hs : 0 < 1-a := by linarith
  have hs2 : (1/2:ℝ) ≤ 1-a := by linarith
  have hinv : r 0/(1-a) ≤ 2*r 0 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [r_pos 0]
  have hab : a*b ≤ b := by nlinarith
  have hsquare : (1/4:ℝ) ≤ (1-a)^2 := by nlinarith
  have hsecond : (1+a*b)/(1-a)^2 ≤ 4*(1+b) := by
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    have hh := mul_le_mul_of_nonneg_right hsquare (show 0 ≤ 4*(1+b) by positivity)
    nlinarith
  unfold linearHazardConstant
  nlinarith [mul_nonneg (r_pos 0).le hb]

lemma lowMomentEnvelope_le (n : ℕ) (hn : 0 < n) (hb : 1 ≤ upperQuantile n)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/16) (p q : ℕ) :
    lowMomentEnvelope n a p q ≤
      lowMomentConstant p q*((n:ℝ)+2)^p*(1+upperQuantile n)^(2*p+q+2)*
        Real.exp (-(1/2:ℝ)*Real.exp ((a/2)*(upperQuantile n)^2)) := by
  let b := upperQuantile n
  let m : ℝ := (n:ℝ)+2
  let C : ℝ := 2*r 0+4
  let E := Real.exp (-(1/2:ℝ)*Real.exp (a*b^2/2))
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hm : 0 ≤ m := by dsimp [m];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity [r_pos 0]
  have hs : 0 < 1-a := by linarith
  have hlin := linearHazardConstant_quantile b a hb0 ha.le ha1
  have hlin0 := linearHazardConstant_nonneg (1-a) (a*b) hs (mul_nonneg ha.le hb0)
  have hCDF := low_threshold_CDF_power n hn a ha ha1
  have hpre : lowCoefficient (n+2) (1-a) (a*b) ((1-4*a)*b) p ≤
      E*(C*(1+b))*(m*(C*(1+b)))^p := by
    unfold lowCoefficient
    norm_num only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
    exact mul_le_mul (mul_le_mul hCDF hlin hlin0 (Real.exp_pos _).le)
      (pow_le_pow_left₀ (mul_nonneg hm hlin0) (mul_le_mul_of_nonneg_left hlin hm) p)
      (pow_nonneg (mul_nonneg hm hlin0) p) (by positivity)
  have hbase : 1+a*b+(1+a) ≤ 3*(1+b) := by nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1+a*b+(1+a) by positivity) hbase (p+q+1)
  have hfull := mul_le_mul
    (mul_le_mul_of_nonneg_right hpre (standardPolynomialMoment_nonneg (p+q+1))) hpow
    (pow_nonneg (by positivity : (0:ℝ) ≤ 1+a*b+(1+a)) _)
    (by positivity [standardPolynomialMoment_nonneg (p+q+1)])
  change lowMomentEnvelope n a p q ≤ _ at hfull
  convert hfull using 1 <;>
    dsimp only [lowMomentConstant,C,E,b,m] <;>
    simp only [mul_pow,show 2*p=p+p by omega,pow_add,pow_one] <;>
    ring

lemma highCoefficient_quantile_le (n : ℕ) (hn : 0 < n) (hb : 1 ≤ upperQuantile n)
    (a lam : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1/16) (hlam0 : 0 ≤ lam)
    (p : ℕ) (hlam : lam ≤ (p:ℝ)+2) :
    highCoefficient (n+2) (1-a) (1+a) (a*upperQuantile n)
      ((1-4*a)*upperQuantile n) lam p ≤
      (16*4^p*2^(p+2))*(1+upperQuantile n)^(p+2)*
        ((n:ℝ)+2)^(-2+12*a*((p:ℝ)+2)+lam) := by
  let b := upperQuantile n
  let m : ℝ := (n:ℝ)+2
  let d := 12*a*((p:ℝ)+2)+lam
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hm : 0 < m := by dsimp [m];positivity
  have hs : 0 < 1-a := by linarith
  have hfour : 4/(1-a)^2 ≤ 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    nlinarith
  have htwo : 2*m/(1-a) ≤ 4*m := by
    apply (div_le_iff₀ hs).mpr
    have hh := mul_le_mul_of_nonneg_left ha1 hm.le
    nlinarith
  have hpre := mul_le_mul hfour
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*m/(1-a)) htwo p)
    (pow_nonneg (by positivity : (0:ℝ) ≤ 2*m/(1-a)) p) (by norm_num : (0:ℝ) ≤ 16)
  have hden := high_density_factor n hn hb a lam ha ha1 hlam0 (p+2) (by exact_mod_cast hlam)
  have hbound : highCoefficient (n+2) (1-a) (1+a) (a*b) ((1-4*a)*b) lam p ≤
      (16*(4*m)^p)*((2*b/m)^(p+2)*Real.exp (d*b^2/2)) := by
    have hx := mul_le_mul hpre hden (by positivity [normalPDF_pos 0]) (by positivity : (0:ℝ) ≤ 16*(4*m)^p)
    convert hx using 1 <;> dsimp only [highCoefficient,b,m,d] <;> push_cast <;> ring
  have hfactor : (16*(4*m)^p)*(2*b/m)^(p+2)=
      (16*4^p*2^(p+2))*b^(p+2)/m^2 := by
    simp only [mul_pow,div_pow,pow_add]
    field_simp
    <;> ring
  have hd : 0 ≤ d := by dsimp [d];positivity
  have hexp := quantile_exp_sq_half_le_rpow n hn d hd
  change Real.exp (d*b^2/2) ≤ m^d at hexp
  have hpoly := pow_le_pow_left₀ hb0 (show b ≤ 1+b by linarith) (p+2)
  have hproduct := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly (show 0 ≤ (16*4^p*2^(p+2))/m^2 by positivity))
    (Real.rpow_nonneg hm.le d)
  have hexpbound := mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ (16*4^p*2^(p+2))*b^(p+2)/m^2 by positivity)
  have hid : m^(-2+d)=m^d/m^2 := by
    rw [show (-2:ℝ)+d=d-2 by ring,Real.rpow_sub hm]
    norm_num only [Real.rpow_two]
  calc
    _ ≤ _ := hbound
    _ = ((16*4^p*2^(p+2))*b^(p+2)/m^2)*Real.exp (d*b^2/2) := by rw [←mul_assoc,hfactor]
    _ ≤ ((16*4^p*2^(p+2))*b^(p+2)/m^2)*m^d := hexpbound
    _ ≤ ((16*4^p*2^(p+2))*(1+b)^(p+2)/m^2)*m^d := by convert hproduct using 1 <;> ring
    _ = _ := by rw [show (-2+12*a*((p:ℝ)+2)+lam)=(-2+d) by dsimp [d];ring,hid];ring

lemma highMomentEnvelope_le (n : ℕ) (hn : 0 < n) (hb : 1 ≤ upperQuantile n)
    (a lam : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/16) (hlam0 : 0 < lam)
    (p q : ℕ) (hlam : lam ≤ (p:ℝ)+2) :
    highMomentEnvelope n a lam p q ≤
      highMomentConstant lam p q*((n:ℝ)+2)^(-2+12*a*((p:ℝ)+2)+lam)*
        (1+upperQuantile n)^(p+q+2) := by
  let b := upperQuantile n
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hden : 0 < Real.sqrt lam*normalPDF 0 := mul_pos (Real.sqrt_pos.mpr hlam0) (normalPDF_pos 0)
  have hcoef := highCoefficient_quantile_le n hn hb a lam ha.le ha1 hlam0.le p hlam
  have hS : (1+a)/(Real.sqrt lam*normalPDF 0) ≤ 2/(Real.sqrt lam*normalPDF 0) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have hab : a*b ≤ b := by nlinarith
  have hs : (1+a)/Real.sqrt lam ≤ 2/Real.sqrt lam :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg lam)
  have hbase : 1+a*b+(1+a)/Real.sqrt lam ≤ (2+2/Real.sqrt lam)*(1+b) := by
    nlinarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg lam),
      mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg lam)) hb0]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+a*b+(1+a)/Real.sqrt lam) hbase q
  have h1 := mul_le_mul hcoef hS (by positivity : (0:ℝ) ≤ (1+a)/(Real.sqrt lam*normalPDF 0))
    (by positivity : (0:ℝ) ≤ (16*4^p*2^(p+2))*(1+upperQuantile n)^(p+2)*((n:ℝ)+2)^(-2+12*a*((p:ℝ)+2)+lam))
  have h2 := mul_le_mul (mul_le_mul_of_nonneg_right h1 (standardPolynomialMoment_nonneg q)) hp
    (by positivity : (0:ℝ) ≤ (1+a*b+(1+a)/Real.sqrt lam)^q)
    (by positivity [standardPolynomialMoment_nonneg q])
  change highMomentEnvelope n a lam p q ≤ _ at h2
  convert h2 using 1 <;> dsimp only [highMomentConstant,b] <;>
    simp only [mul_pow,pow_add] <;> ring

end NegativeVotingHazardUniformUpperCoefficients
