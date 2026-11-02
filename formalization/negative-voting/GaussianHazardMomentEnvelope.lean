import GaussianHazardThresholdBounds
import GaussianDensityMomentBounds

/-! Integrable whole-threshold moment envelopes for actual Gaussian hazards.
The product over all labels is retained in the low region. Both Gaussian
factors and every hazard power are retained in the high region. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
namespace NegativeVotingHazardMomentEnvelope
open WeakSimplex NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardPolynomialBounds NegativeVotingHazardIntegrability
  NegativeVotingHazardThresholdBounds NegativeVotingDensityMomentBounds
  NegativeVotingGaussianTail
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def maxHazard (σ h : V → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k=>gaussianHazard (σ k) (h k) x)

lemma continuous_maxHazard (σ h : V → ℝ) : Continuous (maxHazard σ h) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun k _=>continuous_gaussianHazard (σ k) (h k))

lemma maxHazard_nonneg (σ h : V → ℝ) (hσ : ∀ k,0 < σ k) (x : ℝ) :
    0 ≤ maxHazard σ h x := by
  let k : V := Classical.arbitrary V
  exact (gaussianHazard_pos (σ k) (h k) x (hσ k)).le.trans
    (Finset.le_sup' (fun k=>gaussianHazard (σ k) (h k) x) (Finset.mem_univ k))

def linearHazardConstant (s H : ℝ) : ℝ := r 0/s+(1+H)/s^2

lemma linearHazardConstant_nonneg (s H : ℝ) (hs : 0 < s) (hH : 0 ≤ H) :
    0 ≤ linearHazardConstant s H := by unfold linearHazardConstant;positivity [r_pos 0]

lemma uniform_hazard_polynomial (σ h x s H : ℝ) (hs : 0 < s) (hσ : s ≤ σ)
    (hH : 0 ≤ H) (hh : |h| ≤ H) :
    gaussianHazard σ h x ≤ linearHazardConstant s H*(1+|x|) := by
  refine (gaussianHazard_uniform_linear_growth σ h x s H hs hσ hh).trans ?_
  have h1 := mul_nonneg (div_nonneg (r_pos 0).le hs.le) (abs_nonneg x)
  have h2 := mul_nonneg (div_nonneg hH (sq_nonneg s)) (abs_nonneg x)
  have h3 : 0 ≤ 1/s^2 := by positivity
  apply sub_nonneg.mp
  unfold linearHazardConstant
  convert add_nonneg (add_nonneg h1 h2) h3 using 1 <;> ring

lemma maxHazard_polynomial (σ h : V → ℝ) (s H x : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hH : 0 ≤ H) (hh : ∀ k,|h k| ≤ H) :
    maxHazard σ h x ≤ linearHazardConstant s H*(1+|x|) :=
  Finset.sup'_le Finset.univ_nonempty _ fun k _=>
    uniform_hazard_polynomial (σ k) (h k) x s H hs (hσ k) hH (hh k)

lemma maxHazard_high (σ h : V → ℝ) (s S H x : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hS : ∀ k,σ k ≤ S) (hh : ∀ k,|h k| ≤ H) (hx : H ≤ x) :
    maxHazard σ h x ≤ 2*normalPDF ((x-H)/S)/s :=
  Finset.sup'_le Finset.univ_nonempty _ fun k _=>
    gaussianHazard_upper_box (σ k) (h k) x s S H hs (hσ k) (hS k) (hh k) hx

def momentDensity (σ h : V → ℝ) (p q : ℕ) (i j : V) (x : ℝ) : ℝ :=
  hazardPairDensity σ h x i j*((Fintype.card V:ℝ)*maxHazard σ h x)^p*(1+|x|)^q

lemma momentDensity_nonneg (σ h : V → ℝ) (hσ : ∀ k,0 < σ k)
    (p q : ℕ) (i j : V) (x : ℝ) : 0 ≤ momentDensity σ h p q i j x := by
  unfold momentDensity
  positivity [hazardPairDensity_nonneg σ h hσ x i j,maxHazard_nonneg σ h hσ x]

lemma integrable_momentDensity (σ h : V → ℝ) (s H : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hH : 0 ≤ H) (hh : ∀ k,|h k| ≤ H)
    (p q : ℕ) (i j : V) : Integrable (momentDensity σ h p q i j) volume := by
  have hp : ∀ k,0 < σ k := fun k=>hs.trans_le (hσ k)
  have hi := (integrable_hazardPairDensity_polynomial σ h hp i j (p+q)).const_mul
    (((Fintype.card V:ℝ)*linearHazardConstant s H)^p)
  apply hi.mono'
  · exact (((continuous_hazardPairDensity σ h i j).mul
      ((continuous_const.mul (continuous_maxHazard σ h)).pow p)).mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (momentDensity_nonneg σ h hp p q i j x)]
  have hm := mul_le_mul_of_nonneg_left (maxHazard_polynomial σ h s H x hs hσ hH hh)
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  have hm' := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (maxHazard_nonneg σ h hp x)) hm p
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm' (hazardPairDensity_nonneg σ h hp x i j))
    (by positivity : (0:ℝ) ≤ (1+|x|)^q)
  dsimp only [momentDensity]
  convert h1 using 1 <;> simp only [mul_pow,pow_add] <;> ring

lemma momentDensity_low (σ h : V → ℝ) (s H T x : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hH : 0 ≤ H) (hh : ∀ k,|h k| ≤ H)
    (hx : x ≤ T) (hT : 0 ≤ T+H) (p q : ℕ) (i j : V) :
    momentDensity σ h p q i j x ≤
      normalCDF ((T+H)/s)^(Fintype.card V-1)*linearHazardConstant s H*
        (((Fintype.card V:ℝ)*linearHazardConstant s H)^p)*
          (gaussianDensity (σ i) (h i) x*(1+|x|)^(p+q+1)) := by
  have hp : ∀ k,0 < σ k := fun k=>hs.trans_le (hσ k)
  have hc := linearHazardConstant_nonneg s H hs hH
  have hlow : hazardPairDensity σ h x i j ≤
      normalCDF ((T+H)/s)^(Fintype.card V-1)*gaussianDensity (σ i) (h i) x*
        (linearHazardConstant s H*(1+|x|)) := by
    have h0 := hazardPairDensity_low_threshold σ h s H T x hs hσ hh hx hT i j
    have hg := uniform_hazard_polynomial (σ j) (h j) x s H hs (hσ j) hH (hh j)
    have hpoly : r 0/s+(|x|+H)/s^2 ≤ linearHazardConstant s H*(1+|x|) := by
      have h1 := mul_nonneg (div_nonneg (r_pos 0).le hs.le) (abs_nonneg x)
      have h2 := mul_nonneg (div_nonneg hH (sq_nonneg s)) (abs_nonneg x)
      have h3 : 0 ≤ 1/s^2 := by positivity
      apply sub_nonneg.mp
      unfold linearHazardConstant
      convert add_nonneg (add_nonneg h1 h2) h3 using 1 <;> ring
    exact h0.trans (mul_le_mul_of_nonneg_left hpoly
      (mul_nonneg (pow_nonneg (normalCDF_pos _).le _) (gaussianDensity_pos _ _ _ (hp i)).le))
  have hm := mul_le_mul_of_nonneg_left (maxHazard_polynomial σ h s H x hs hσ hH hh)
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  have hm' := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (maxHazard_nonneg σ h hp x)) hm p
  have h1 := mul_le_mul hlow hm' (pow_nonneg (by positivity [maxHazard_nonneg σ h hp x]) _)
    (by positivity [normalCDF_pos ((T+H)/s),gaussianDensity_pos (σ i) (h i) x (hp i)])
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (1+|x|)^q)
  dsimp only [momentDensity]
  convert h2 using 1 <;> simp only [mul_pow,pow_add,pow_one] <;> ring

lemma normalPDF_pow_split (z a lam : ℝ) (k : ℕ) (ha : 0 ≤ a) (haz : a ≤ z)
    (hlam : lam ≤ k) :
    normalPDF z^k ≤ normalPDF 0^k*Real.exp (-((k:ℝ)-lam)*a^2/2)*
      Real.exp (-lam*z^2/2) := by
  rw [normalPDF_ratio 0 z,mul_pow]
  simp only [zero_pow (by norm_num : 2≠0),zero_sub,←Real.exp_nat_mul]
  have hsq := pow_le_pow_left₀ ha haz 2
  have hm := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hlam)
  have he : (k:ℝ)*(-z^2/2) ≤ -((k:ℝ)-lam)*a^2/2+(-lam*z^2/2) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (pow_nonneg (normalPDF_pos 0).le k)
  rw [Real.exp_add] at hh
  simpa only [mul_assoc] using hh

lemma momentDensity_high (σ h : V → ℝ) (s S H T x lam : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hS : ∀ k,σ k ≤ S) (hh : ∀ k,|h k| ≤ H)
    (hT : H ≤ T) (hx : T ≤ x) (p q : ℕ) (hlam : lam ≤ (p:ℝ)+2) (i j : V) :
    momentDensity σ h p q i j x ≤
      (4/s^2*(2*(Fintype.card V:ℝ)/s)^p*normalPDF 0^(p+2)*
        Real.exp (-((p:ℝ)+2-lam)*((T-H)/S)^2/2))*
        (Real.exp (-lam*((x-H)/S)^2/2)*(1+|x|)^q) := by
  have hp : ∀ k,0 < σ k := fun k=>hs.trans_le (hσ k)
  have hSp : 0 < S := (hp i).trans_le (hS i)
  have hxH := hT.trans hx
  have hρ := hazardPairDensity_high_threshold σ h s S H x hs hσ hS hh hxH i j
  have hm := mul_le_mul_of_nonneg_left (maxHazard_high σ h s S H x hs hσ hS hh hxH)
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  have hm' := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (maxHazard_nonneg σ h hp x)) hm p
  have h1 := mul_le_mul hρ hm' (pow_nonneg (by positivity [maxHazard_nonneg σ h hp x]) _) (by positivity)
  have he : hazardPairDensity σ h x i j*((Fintype.card V:ℝ)*maxHazard σ h x)^p ≤
      (4/s^2*(2*(Fintype.card V:ℝ)/s)^p)*normalPDF ((x-H)/S)^(p+2) := by
    convert h1 using 1 <;> simp only [mul_pow,pow_add] <;> ring
  have ha : 0 ≤ (T-H)/S := div_nonneg (sub_nonneg.mpr hT) hSp.le
  have haz : (T-H)/S ≤ (x-H)/S := div_le_div_of_nonneg_right (by linarith) hSp.le
  have hf := normalPDF_pow_split ((x-H)/S) ((T-H)/S) lam (p+2) ha haz (by exact_mod_cast hlam)
  have he2 := he.trans (mul_le_mul_of_nonneg_left hf (by positivity))
  have he3 := mul_le_mul_of_nonneg_right he2 (by positivity : (0:ℝ) ≤ (1+|x|)^q)
  dsimp only [momentDensity]
  convert he3 using 1 <;> push_cast <;> ring

def lowCoefficient (m : ℕ) (s H T : ℝ) (p : ℕ) : ℝ :=
  normalCDF ((T+H)/s)^(m-1)*linearHazardConstant s H*((m:ℝ)*linearHazardConstant s H)^p

def highCoefficient (m : ℕ) (s S H T lam : ℝ) (p : ℕ) : ℝ :=
  4/s^2*(2*(m:ℝ)/s)^p*normalPDF 0^(p+2)*
    Real.exp (-((p:ℝ)+2-lam)*((T-H)/S)^2/2)

lemma lowCoefficient_nonneg (m : ℕ) (s H T : ℝ) (p : ℕ) (hs : 0 < s) (hH : 0 ≤ H) :
    0 ≤ lowCoefficient m s H T p := by
  unfold lowCoefficient
  positivity [normalCDF_pos ((T+H)/s),linearHazardConstant_nonneg s H hs hH]

lemma highCoefficient_nonneg (m : ℕ) (s S H T lam : ℝ) (p : ℕ) (hs : 0 < s) :
    0 ≤ highCoefficient m s S H T lam p := by
  unfold highCoefficient
  positivity [normalPDF_pos 0]

theorem integral_momentDensity_low (σ h : V → ℝ) (s S H T : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hS : ∀ k,σ k ≤ S) (hH : 0 ≤ H) (hh : ∀ k,|h k| ≤ H)
    (hT : 0 ≤ T+H) (p q : ℕ) (i j : V) :
    (∫x in Iic T,momentDensity σ h p q i j x) ≤
      lowCoefficient (Fintype.card V) s H T p*standardPolynomialMoment (p+q+1)*
        (1+H+S)^(p+q+1) := by
  have hp : ∀ k,0 < σ k := fun k=>hs.trans_le (hσ k)
  let c := lowCoefficient (Fintype.card V) s H T p
  have hc : 0 ≤ c := lowCoefficient_nonneg _ _ _ _ _ hs hH
  have hi := (integrable_density_polynomial (σ i) (h i) 1 (hp i) (by norm_num) (p+q+1)).const_mul c
  have h1 : (∫x in Iic T,momentDensity σ h p q i j x) ≤
      ∫x in Iic T,c*(gaussianDensity (σ i) (h i) x*(1+|x|)^(p+q+1)) := by
    apply integral_mono_ae (integrable_momentDensity σ h s H hs hσ hH hh p q i j).integrableOn hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact momentDensity_low σ h s H T x hs hσ hH hh hx hT p q i j
  have h2 := setIntegral_le_integral (s:=Iic T) hi
    (ae_of_all _ fun x=>by positivity [gaussianDensity_pos (σ i) (h i) x (hp i)])
  have h3 := mul_le_mul_of_nonneg_left (density_polynomial_integral_le (σ i) (h i) (hp i) (p+q+1)) hc
  have h4 : (1+|h i|+σ i)^(p+q+1) ≤ (1+H+S)^(p+q+1) :=
    pow_le_pow_left₀ (by positivity [hp i]) (by linarith [hh i,hS i]) _
  have h12 := h1.trans h2
  rw [integral_const_mul] at h12
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hc (standardPolynomialMoment_nonneg (p+q+1)))
  exact h12.trans (h3.trans (by simpa only [mul_assoc,c] using h5))

theorem integral_momentDensity_high (σ h : V → ℝ) (s S H T lam : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hS : ∀ k,σ k ≤ S) (hH : 0 ≤ H) (hh : ∀ k,|h k| ≤ H)
    (hT : H ≤ T) (hlam0 : 0 < lam) (p q : ℕ) (hlam : lam ≤ (p:ℝ)+2) (i j : V) :
    (∫x in Ioi T,momentDensity σ h p q i j x) ≤
      highCoefficient (Fintype.card V) s S H T lam p*
        (S/(Real.sqrt lam*normalPDF 0))*standardPolynomialMoment q*
          (1+H+S/Real.sqrt lam)^q := by
  have hSp : 0 < S := (hs.trans_le (hσ i)).trans_le (hS i)
  let c := highCoefficient (Fintype.card V) s S H T lam p
  have hc : 0 ≤ c := highCoefficient_nonneg _ _ _ _ _ _ _ hs
  have hi := (integrable_gaussian_exp_kernel_polynomial S H lam hSp hlam0 q).const_mul c
  have h1 : (∫x in Ioi T,momentDensity σ h p q i j x) ≤
      ∫x in Ioi T,c*(Real.exp (-lam*((x-H)/S)^2/2)*(1+|x|)^q) := by
    apply integral_mono_ae (integrable_momentDensity σ h s H hs hσ hH hh p q i j).integrableOn hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact momentDensity_high σ h s S H T x lam hs hσ hS hh hT hx.le p q hlam i j
  have h2 := setIntegral_le_integral (s:=Ioi T) hi (ae_of_all _ fun x=>by positivity)
  have h12 := h1.trans h2
  rw [integral_const_mul] at h12
  have h3 := mul_le_mul_of_nonneg_left
    (gaussian_exp_kernel_polynomial_integral_le S H lam hSp hlam0 q) hc
  have h4 := h12.trans h3
  simpa only [abs_of_nonneg hH,mul_assoc,c] using h4

/-- Complete integral envelope across the entire real threshold line. Its
 constants are explicit; the subsequent alphabet-uniform asymptotic step is
 a separate obligation. -/
theorem integral_momentDensity_split (σ h : V → ℝ) (s S H T lam : ℝ) (hs : 0 < s)
    (hσ : ∀ k,s ≤ σ k) (hS : ∀ k,σ k ≤ S) (hH : 0 ≤ H) (hh : ∀ k,|h k| ≤ H)
    (hT : H ≤ T) (hlam0 : 0 < lam) (p q : ℕ) (hlam : lam ≤ (p:ℝ)+2) (i j : V) :
    (∫x,momentDensity σ h p q i j x) ≤
      lowCoefficient (Fintype.card V) s H T p*standardPolynomialMoment (p+q+1)*(1+H+S)^(p+q+1)+
      highCoefficient (Fintype.card V) s S H T lam p*(S/(Real.sqrt lam*normalPDF 0))*
        standardPolynomialMoment q*(1+H+S/Real.sqrt lam)^q := by
  have he := integral_add_compl (s:=Iic T) measurableSet_Iic
    (integrable_momentDensity σ h s H hs hσ hH hh p q i j)
  rw [compl_Iic] at he
  rw [←he]
  exact add_le_add (integral_momentDensity_low σ h s S H T hs hσ hS hH hh (by linarith) p q i j)
    (integral_momentDensity_high σ h s S H T lam hs hσ hS hH hh hT hlam0 p q hlam i j)

end NegativeVotingHazardMomentEnvelope
