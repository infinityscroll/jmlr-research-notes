import GaussianFanRetainedCoefficient

/-! Explicit numerical constants for the first positive-mass window. -/
noncomputable section
open scoped BigOperators
namespace NegativeVotingOptimizerConstants
open NegativeVotingFanRetained

def actualMassLower (x : ℝ) : ℝ := 1/(100*x)
def massLower (x : ℝ) : ℝ := 1/(200*x)
def edgeLower (x : ℝ) : ℝ := Real.sqrt (2*Real.pi)/(20000*x^2)
def edgeShape (x : ℝ) : ℝ := 2*Real.sqrt (2*Real.log x)+(Real.sqrt (2*Real.pi))⁻¹
def edgeUpper (x : ℝ) : ℝ := 4*edgeShape x/x
def retention (x : ℝ) : ℝ := 1/x^4
def coefficientConstant : ℝ := 40026*Real.exp 4+402
def mixedConstant : ℝ := 2949120000*Real.pi^2*coefficientConstant
def numericThreshold : ℕ := Nat.ceil (9600*Real.pi+3)

theorem scalar_positive (x : ℝ) (hx : 0< x) :
    0< massLower x ∧ 0< edgeLower x ∧ 0< edgeUpper x ∧ 0< retention x := by
  have hp : 0< Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
  have he : 0< edgeShape x := by unfold edgeShape; positivity
  dsimp [massLower,edgeLower,edgeUpper,retention]
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

theorem inverse_sqrt_two_pi_le_one : (Real.sqrt (2*Real.pi))⁻¹≤ 1 := by
  have hp : 1≤ Real.sqrt (2*Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [Real.pi_gt_three]
  exact inv_le_one_of_one_le₀ hp

theorem edgeShape_sq_le (x : ℝ) (hx : 1≤ x) :
    (edgeShape x)^2≤ 18*(1+Real.log x) := by
  have hl := Real.log_nonneg hx
  have hs := Real.sq_sqrt (show 0≤ 2*Real.log x by positivity)
  have hk0 : 0≤ (Real.sqrt (2*Real.pi))⁻¹ := by positivity
  have hk1 := inverse_sqrt_two_pi_le_one
  dsimp [edgeShape]
  nlinarith [sq_nonneg (2*Real.sqrt (2*Real.log x)-(Real.sqrt (2*Real.pi))⁻¹)]

theorem ceiling_log_bound (x : ℝ) (hx : 1≤ x) :
    retainedCoefficientCeiling (massLower x) (retention x) (edgeLower x)≤
      coefficientConstant*(1+Real.log x) := by
  have hx0 : 0< x := lt_of_lt_of_le zero_lt_one hx
  have hxne := ne_of_gt hx0
  have hs : 0< Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤ 2*Real.pi by positivity)
  have hlog := Real.log_nonneg hx
  have hp : 0≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have heq : 1/(Real.sqrt (2*Real.pi)*retention x*edgeLower x)=10000*x^6/Real.pi := by
    dsimp [retention,edgeLower]
    field_simp
    nlinarith [hs2]
  have hlog1 : Real.log (1/(Real.sqrt (2*Real.pi)*retention x*edgeLower x))≤ 10006*(1+Real.log x) := by
    rw [heq,Real.log_div (by positivity) Real.pi_ne_zero,
      Real.log_mul (by norm_num) (pow_ne_zero 6 hxne),Real.log_pow]
    have hc := Real.log_le_sub_one_of_pos (show (0:ℝ)< 10000 by norm_num)
    norm_num only [Nat.cast_ofNat,Int.cast_ofNat] at *
    nlinarith
  have heq2 : 1/massLower x=200*x := by dsimp [massLower]; field_simp
  have hlog2 : Real.log (1/massLower x)≤ 201*(1+Real.log x) := by
    rw [heq2,Real.log_mul (by norm_num) hxne]
    have hc := Real.log_le_sub_one_of_pos (show (0:ℝ)< 200 by norm_num)
    nlinarith
  have hm1 : max (Real.log (1/(Real.sqrt (2*Real.pi)*retention x*edgeLower x))) 0≤ 10006*(1+Real.log x) :=
    max_le hlog1 (by positivity)
  have hm2 : max (Real.log (1/massLower x)) 0≤ 201*(1+Real.log x) :=
    max_le hlog2 (by positivity)
  unfold retainedCoefficientCeiling coefficientConstant
  have he := Real.exp_pos 4
  nlinarith

theorem gap_inverse_formula (x : ℝ) (hx : 0< x) :
    (retainedGapCoefficient (massLower x) (edgeUpper x) 2)⁻¹=
      163840000*Real.pi^2*(edgeShape x)^2 := by
  have hshape : 0< edgeShape x := by unfold edgeShape; positivity
  unfold retainedGapCoefficient massLower edgeUpper
  field_simp
  <;> ring

theorem ceiling_gap_ratio_bound (x : ℝ) (hx : 1≤ x) :
    retainedCoefficientCeiling (massLower x) (retention x) (edgeLower x)/
      retainedGapCoefficient (massLower x) (edgeUpper x) 2≤ mixedConstant*(1+Real.log x)^2 := by
  have hx0 : 0< x := lt_of_lt_of_le zero_lt_one hx
  have hlog := Real.log_nonneg hx
  have hc := ceiling_log_bound x hx
  have hs := edgeShape_sq_le x hx
  have hC : 0≤ coefficientConstant := by unfold coefficientConstant; positivity
  have hK : 0≤ retainedCoefficientCeiling (massLower x) (retention x) (edgeLower x) := by
    unfold retainedCoefficientCeiling
    positivity
  rw [div_eq_mul_inv,gap_inverse_formula x hx0]
  calc
    _≤ (coefficientConstant*(1+Real.log x))*(163840000*Real.pi^2*(edgeShape x)^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _≤ (coefficientConstant*(1+Real.log x))*(163840000*Real.pi^2*(18*(1+Real.log x))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    _=mixedConstant*(1+Real.log x)^2 := by unfold mixedConstant; ring

theorem retention_threshold (x : ℝ) (hx : 9600*Real.pi+3≤ x) :
    retention x*x≤ massLower x/(4*Real.pi*edgeUpper x) := by
  have hx2 : 2≤ x := by linarith [Real.pi_pos]
  have hx1 : 1≤ x := by linarith
  have hx0 : 0< x := by linarith
  have hlog := Real.log_nonneg hx1
  have hlogx : Real.log x≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hs2 := Real.sq_sqrt (show 0≤ 2*Real.log x by positivity)
  have hs : Real.sqrt (2*Real.log x)≤ x := by nlinarith [Real.sqrt_nonneg (2*Real.log x)]
  have hshape : edgeShape x≤ 3*x := by
    dsimp [edgeShape]
    linarith [inverse_sqrt_two_pi_le_one]
  have hp : 0< edgeShape x := by unfold edgeShape; positivity
  have hlarge : 9600*Real.pi≤ x^2 := by nlinarith [Real.pi_pos]
  have hb : 3200*Real.pi*edgeShape x≤ x^3 := by
    have h1 := mul_le_mul_of_nonneg_left hshape (show 0≤ 3200*Real.pi by positivity)
    have h2 := mul_le_mul_of_nonneg_right hlarge (le_of_lt hx0)
    nlinarith
  have heq1 : retention x*x=1/x^3 := by dsimp [retention]; field_simp
  have heq2 : massLower x/(4*Real.pi*edgeUpper x)=1/(3200*Real.pi*edgeShape x) := by
    dsimp [massLower,edgeUpper]
    field_simp
    <;> ring
  rw [heq1,heq2]
  exact one_div_le_one_div_of_le (by positivity) hb

theorem numericThreshold_spec (m : ℕ) (hm : numericThreshold≤ m) :
    3≤ m ∧ retention (m:ℝ)*(m:ℝ)≤ massLower (m:ℝ)/(4*Real.pi*edgeUpper (m:ℝ)) ∧
    retainedCoefficientCeiling (massLower (m:ℝ)) (retention (m:ℝ)) (edgeLower (m:ℝ))/
      retainedGapCoefficient (massLower (m:ℝ)) (edgeUpper (m:ℝ)) 2≤ mixedConstant*(1+Real.log (m:ℝ))^2 := by
  have hn : 9600*Real.pi+3≤ (m:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hm3 : 3≤ m := by exact_mod_cast (show (3:ℝ)≤ (m:ℝ) by linarith [Real.pi_pos])
  exact ⟨hm3,retention_threshold (m:ℝ) hn,ceiling_gap_ratio_bound (m:ℝ) (by linarith [Real.pi_pos])⟩

theorem mixedConstant_pos : 0< mixedConstant := by unfold mixedConstant coefficientConstant; positivity

end NegativeVotingOptimizerConstants
