import GaussianHazardIntegrability
import GaussianTailRatio

/-! Whole-threshold envelopes for the literal diagonal Gaussian pair density.
The lower-threshold estimate retains the product over every other label;
the positive-threshold estimate retains both Gaussian densities. These are
pointwise bounds, not yet a claim of uniform normalized rare-event moments. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
namespace NegativeVotingHazardThresholdBounds
open WeakSimplex NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardPolynomialBounds NegativeVotingHazardIntegrability
  NegativeVotingGaussianTail NegativeVotingMassCentroid NegativeVotingGaussianMaximum

lemma normalPDF_le_of_sq_le (x y : ℝ) (hxy : x^2 ≤ y^2) :
    normalPDF y ≤ normalPDF x := by
  rw [normalPDF_ratio x y]
  have he : Real.exp ((x^2-y^2)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simpa using mul_le_mul_of_nonneg_left he (normalPDF_pos x).le

lemma standardized_upper (σ h x s H T : ℝ) (hs : 0 < s) (hσ : s ≤ σ)
    (hh : |h| ≤ H) (hx : x ≤ T) (hT : 0 ≤ T+H) :
    (x-h)/σ ≤ (T+H)/s := by
  have hp : 0 < σ := hs.trans_le hσ
  apply (div_le_iff₀ hp).mpr
  have ha : x-h ≤ T+H := by linarith [(abs_le.mp hh).1]
  have hb := mul_le_mul_of_nonneg_left hσ (div_nonneg hT hs.le)
  have hc : (T+H)/s*s=T+H := by field_simp
  rw [hc] at hb
  exact ha.trans hb

lemma standardized_lower (σ h x S H T : ℝ) (hσ : 0 < σ) (hS : σ ≤ S)
    (hh : |h| ≤ H) (hx : T ≤ x) (hT : H ≤ T) :
    (T-H)/S ≤ (x-h)/σ := by
  have hp : 0 < S := hσ.trans_le hS
  apply (le_div_iff₀ hσ).mpr
  have hb := mul_le_mul_of_nonneg_left hS (div_nonneg (sub_nonneg.mpr hT) hp.le)
  have hc : (T-H)/S*S=T-H := by field_simp
  rw [hc] at hb
  exact hb.trans (by linarith [(abs_le.mp hh).2])

lemma gaussianCDF_upper_box (σ h x s H T : ℝ) (hs : 0 < s) (hσ : s ≤ σ)
    (hh : |h| ≤ H) (hx : x ≤ T) (hT : 0 ≤ T+H) :
    gaussianCDF σ h x ≤ normalCDF ((T+H)/s) :=
  strictMono_normalCDF.monotone (standardized_upper σ h x s H T hs hσ hh hx hT)

lemma gaussianCDF_lower_box (σ h x S H T : ℝ) (hσ : 0 < σ) (hS : σ ≤ S)
    (hh : |h| ≤ H) (hx : T ≤ x) (hT : H ≤ T) :
    normalCDF ((T-H)/S) ≤ gaussianCDF σ h x :=
  strictMono_normalCDF.monotone (standardized_lower σ h x S H T hσ hS hh hx hT)

lemma gaussianDensity_upper_box (σ h x s S H : ℝ) (hs : 0 < s)
    (hσ : s ≤ σ) (hS : σ ≤ S) (hh : |h| ≤ H) (hx : H ≤ x) :
    gaussianDensity σ h x ≤ normalPDF ((x-H)/S)/s := by
  have hp : 0 < σ := hs.trans_le hσ
  have hSp : 0 < S := hp.trans_le hS
  have hu := standardized_lower σ h x S H x hp hS hh le_rfl hx
  have h0 : 0 ≤ (x-H)/S := div_nonneg (sub_nonneg.mpr hx) hSp.le
  have hd := normalPDF_le_of_sq_le _ _ (pow_le_pow_left₀ h0 hu 2)
  exact (div_le_div_of_nonneg_right hd hp.le).trans
    (div_le_div_of_nonneg_left (normalPDF_pos _).le hs hσ)

lemma gaussianHazard_upper_box (σ h x s S H : ℝ) (hs : 0 < s)
    (hσ : s ≤ σ) (hS : σ ≤ S) (hh : |h| ≤ H) (hx : H ≤ x) :
    gaussianHazard σ h x ≤ 2*normalPDF ((x-H)/S)/s := by
  have hp : 0 < σ := hs.trans_le hσ
  have hcdf : (1/2:ℝ) ≤ gaussianCDF σ h x := by
    have h0 : 0 ≤ (x-h)/σ := div_nonneg (by linarith [(abs_le.mp hh).2]) hp.le
    change (1/2:ℝ) ≤ normalCDF ((x-h)/σ)
    simpa only [normalCDF_zero] using strictMono_normalCDF.monotone h0
  have hd := gaussianDensity_upper_box σ h x s S H hs hσ hS hh hx
  unfold gaussianHazard
  calc
    _ ≤ gaussianDensity σ h x/(1/2) :=
      div_le_div_of_nonneg_left (gaussianDensity_pos _ _ _ hp).le (by norm_num) hcdf
    _ ≤ (normalPDF ((x-H)/S)/s)/(1/2) := div_le_div_of_nonneg_right hd (by norm_num)
    _ = _ := by ring

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma hazardPairDensity_erase (σ h : V → ℝ) (x : ℝ) (i j : V) :
    hazardPairDensity σ h x i j=
      (∏k∈Finset.univ.erase i,gaussianCDF (σ k) (h k) x)*
        gaussianDensity (σ i) (h i) x*gaussianHazard (σ j) (h j) x := by
  unfold hazardPairDensity productCDF
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  unfold gaussianHazard
  field_simp [(gaussianCDF_pos (σ i) (h i) x).ne',
    (gaussianCDF_pos (σ j) (h j) x).ne']

/-- No label factor is discarded in the low-threshold CDF suppression. -/
lemma hazardPairDensity_low_threshold (σ h : V → ℝ) (s H T x : ℝ)
    (hs : 0 < s) (hσ : ∀ i,s ≤ σ i) (hh : ∀ i,|h i| ≤ H)
    (hx : x ≤ T) (hT : 0 ≤ T+H) (i j : V) :
    hazardPairDensity σ h x i j ≤ normalCDF ((T+H)/s)^(Fintype.card V-1)*
      gaussianDensity (σ i) (h i) x*(r 0/s+(|x|+H)/s^2) := by
  rw [hazardPairDensity_erase]
  have hprod : (∏k∈Finset.univ.erase i,gaussianCDF (σ k) (h k) x) ≤
      normalCDF ((T+H)/s)^(Fintype.card V-1) := by
    have hp := Finset.prod_le_prod₀ (s:=Finset.univ.erase i)
      (fun k _ => (gaussianCDF_pos (σ k) (h k) x).le)
      (fun k _ => gaussianCDF_upper_box (σ k) (h k) x s H T hs (hσ k) (hh k) hx hT)
    simpa using hp
  have hz : 0 ≤ H := (abs_nonneg _).trans (hh j)
  calc
    _ ≤ (normalCDF ((T+H)/s)^(Fintype.card V-1)*gaussianDensity (σ i) (h i) x)*
        gaussianHazard (σ j) (h j) x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (gaussianDensity_pos _ _ _ (hs.trans_le (hσ i))).le)
        (gaussianHazard_pos _ _ _ (hs.trans_le (hσ j))).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (gaussianHazard_uniform_linear_growth _ _ _ s H hs (hσ j) (hh j))
      (mul_nonneg (pow_nonneg (normalCDF_pos _).le _) (gaussianDensity_pos _ _ _ (hs.trans_le (hσ i))).le)

lemma cdf_power_exponential (y : ℝ) (k : ℕ) :
    normalCDF y^k ≤ Real.exp (-(k:ℝ)*normalCDF (-y)) := by
  have hb : normalCDF y ≤ Real.exp (-normalCDF (-y)) := by
    have hh := Real.add_one_le_exp (-normalCDF (-y))
    have he := normalCDF_neg y
    linarith
  have hp := pow_le_pow_left₀ (normalCDF_pos y).le hb k
  simpa only [←Real.exp_nat_mul,neg_mul,mul_neg] using hp

/-- Positive-threshold suppression retains two densities, including i=j. -/
lemma hazardPairDensity_high_threshold (σ h : V → ℝ) (s S H x : ℝ)
    (hs : 0 < s) (hσ : ∀ i,s ≤ σ i) (hS : ∀ i,σ i ≤ S)
    (hh : ∀ i,|h i| ≤ H) (hx : H ≤ x) (i j : V) :
    hazardPairDensity σ h x i j ≤ 4*(normalPDF ((x-H)/S))^2/s^2 := by
  have hp : productCDF σ h x ≤ 1 :=
    Finset.prod_le_one₀ (fun k _ => (gaussianCDF_pos _ _ _).le)
      (fun k _ => (normalCDF_lt_one _).le)
  have hi := gaussianHazard_upper_box (σ i) (h i) x s S H hs (hσ i) (hS i) (hh i) hx
  have hj := gaussianHazard_upper_box (σ j) (h j) x s S H hs (hσ j) (hS j) (hh j) hx
  have hh0 := mul_le_mul hp hi (gaussianHazard_pos _ _ _ (hs.trans_le (hσ i))).le (by norm_num : (0:ℝ) ≤ 1)
  have hh1 := mul_le_mul hh0 hj (gaussianHazard_pos _ _ _ (hs.trans_le (hσ j))).le
    (by positivity [normalPDF_pos ((x-H)/S)])
  change productCDF σ h x*gaussianHazard (σ i) (h i) x*gaussianHazard (σ j) (h j) x ≤ _
  convert hh1 using 1 <;> ring

lemma productCDF_lower_box (σ h : V → ℝ) (S H T x : ℝ)
    (hσ : ∀ i,0 < σ i) (hS : ∀ i,σ i ≤ S)
    (hh : ∀ i,|h i| ≤ H) (hx : T ≤ x) (hT : H ≤ T) :
    1-(Fintype.card V:ℝ)*normalCDF (-((T-H)/S)) ≤ productCDF σ h x := by
  have hprod : normalCDF ((T-H)/S)^(Fintype.card V) ≤ productCDF σ h x := by
    have hp := Finset.prod_le_prod₀ (s:=Finset.univ)
      (fun k _ => (normalCDF_pos ((T-H)/S)).le)
      (fun k _ => gaussianCDF_lower_box (σ k) (h k) x S H T (hσ k) (hS k) (hh k) hx hT)
    simpa only [Finset.prod_const,Finset.card_univ,productCDF] using hp
  have hp := one_add_mul_sub_le_pow (by linarith [normalCDF_pos ((T-H)/S)] : -1 ≤ normalCDF ((T-H)/S)) (Fintype.card V)
  have he := normalCDF_neg ((T-H)/S)
  have heq : 1+(Fintype.card V:ℝ)*(normalCDF ((T-H)/S)-1)=
      1-(Fintype.card V:ℝ)*normalCDF (-((T-H)/S)) := by rw [he];ring
  rw [heq] at hp
  exact hp.trans hprod

lemma gaussianDensity_lower_interval (σ h x s S H T U : ℝ) (hs : 0 < s)
    (hσ : s ≤ σ) (hS : σ ≤ S) (hh : |h| ≤ H) (hx : x∈Icc T U) (hT : H ≤ T) :
    normalPDF ((U+H)/s)/S ≤ gaussianDensity σ h x := by
  have hp : 0 < σ := hs.trans_le hσ
  have hSp : 0 < S := hp.trans_le hS
  have hH : 0 ≤ H := (abs_nonneg _).trans hh
  have hx0 : 0 ≤ x := hH.trans (hT.trans hx.1)
  have hU : 0 ≤ U+H := by linarith [hx.2]
  have hab : |(x-h)/σ| ≤ (U+H)/s := by
    rw [abs_div,abs_of_pos hp]
    calc
      _ ≤ (|x|+|h|)/σ := div_le_div_of_nonneg_right (by simpa using abs_sub_le x 0 h) hp.le
      _ ≤ (U+H)/σ := div_le_div_of_nonneg_right (by rw [abs_of_nonneg hx0];linarith [hx.2]) hp.le
      _ ≤ _ := div_le_div_of_nonneg_left hU hs hσ
  have hsquare : ((x-h)/σ)^2 ≤ ((U+H)/s)^2 := by
    have hz := pow_le_pow_left₀ (abs_nonneg ((x-h)/σ)) hab 2
    simpa only [sq_abs] using hz
  have hd := normalPDF_le_of_sq_le _ _ hsquare
  exact (div_le_div_of_nonneg_right hd hSp.le).trans
    (div_le_div_of_nonneg_left (normalPDF_pos _).le hp hS)

lemma gaussianDensity_le_hazard (σ h x : ℝ) (hσ : 0 < σ) :
    gaussianDensity σ h x ≤ gaussianHazard σ h x := by
  unfold gaussianHazard
  apply (le_div_iff₀ (gaussianCDF_pos _ _ _)).mpr
  have hh := mul_le_mul_of_nonneg_left (normalCDF_lt_one ((x-h)/σ)).le
    (gaussianDensity_pos σ h x hσ).le
  change gaussianDensity σ h x*normalCDF ((x-h)/σ) ≤ _
  simpa only [mul_one] using hh

lemma hazardPairDensity_lower_interval (σ h : V → ℝ) (s S H T U x : ℝ)
    (hs : 0 < s) (hσ : ∀ i,s ≤ σ i) (hS : ∀ i,σ i ≤ S)
    (hh : ∀ i,|h i| ≤ H) (hx : x∈Icc T U) (hT : H ≤ T)
    (htail : (Fintype.card V:ℝ)*normalCDF (-((T-H)/S)) ≤ 1/2) (i j : V) :
    (1/2:ℝ)*(normalPDF ((U+H)/s)/S)^2 ≤ hazardPairDensity σ h x i j := by
  have hSp : 0 < S := (hs.trans_le (hσ i)).trans_le (hS i)
  have hprod : (1/2:ℝ) ≤ productCDF σ h x := by
    have hp := productCDF_lower_box σ h S H T x (fun k => hs.trans_le (hσ k)) hS hh hx.1 hT
    linarith
  have hd (k:V) : normalPDF ((U+H)/s)/S ≤ gaussianHazard (σ k) (h k) x :=
    (gaussianDensity_lower_interval (σ k) (h k) x s S H T U hs (hσ k) (hS k) (hh k) hx hT).trans
      (gaussianDensity_le_hazard _ _ _ (hs.trans_le (hσ k)))
  have hz : 0 ≤ normalPDF ((U+H)/s)/S := div_nonneg (normalPDF_pos _).le hSp.le
  have h1 := mul_le_mul hprod (hd i) hz (productCDF_nonneg _ _ _)
  have h2 := mul_le_mul h1 (hd j) hz (mul_nonneg (productCDF_nonneg _ _ _)
    (gaussianHazard_pos _ _ _ (hs.trans_le (hσ i))).le)
  change _ ≤ productCDF σ h x*gaussianHazard (σ i) (h i) x*gaussianHazard (σ j) (h j) x
  convert h2 using 1 <;> ring

/-- A genuine positive lower bound for the full pair integral.  It includes
 the analytic diagonal and uses a literal interval, without normalization by
 a conjectural facet scale. -/
theorem integral_hazardPairDensity_lower (σ h : V → ℝ) (s S H T U : ℝ)
    (hs : 0 < s) (hσ : ∀ i,s ≤ σ i) (hS : ∀ i,σ i ≤ S)
    (hh : ∀ i,|h i| ≤ H) (hTU : T ≤ U) (hT : H ≤ T)
    (htail : (Fintype.card V:ℝ)*normalCDF (-((T-H)/S)) ≤ 1/2) (i j : V) :
    (U-T)/2*(normalPDF ((U+H)/s)/S)^2 ≤ ∫x,hazardPairDensity σ h x i j := by
  have hpos : ∀ k,0 < σ k := fun k => hs.trans_le (hσ k)
  have hi : Integrable (fun x=>hazardPairDensity σ h x i j) volume := by
    simpa only [pow_zero,mul_one] using integrable_hazardPairDensity_polynomial σ h hpos i j 0
  have hlo : (∫x in Icc T U,(1/2:ℝ)*(normalPDF ((U+H)/s)/S)^2) ≤
      ∫x in Icc T U,hazardPairDensity σ h x i j := by
    apply integral_mono_ae (integrable_const _) hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hazardPairDensity_lower_interval σ h s S H T U x hs hσ hS hh hx hT htail i j
  have ht := setIntegral_le_integral (s:=Icc T U) hi
    (ae_of_all _ fun x=>hazardPairDensity_nonneg σ h hpos x i j)
  have he : (∫x in Icc T U,(1/2:ℝ)*(normalPDF ((U+H)/s)/S)^2)=
      (U-T)/2*(normalPDF ((U+H)/s)/S)^2 := by
    rw [setIntegral_const,Real.volume_real_Icc_of_le hTU,smul_eq_mul]
    ring
  rw [he] at hlo
  exact hlo.trans ht

end NegativeVotingHazardThresholdBounds
