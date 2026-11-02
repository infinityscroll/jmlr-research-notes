import GaussianHazardQuantileBounds

/-! Uniform quantile-box coefficient bounds for the actual pair densities.
This file derives bounds from literal Gaussian integrals, including the
analytic diagonal, without assuming a normalized probability law. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical Topology
namespace NegativeVotingHazardUniformCoefficientBounds
open WeakSimplex NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianTail NegativeVotingHazardThresholdBounds
  NegativeVotingHazardMomentEnvelope NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardQuantileBounds NegativeVotingDensityMomentBounds

/-- A quantitative lower normalization on a literal high-threshold interval.
All variances and offsets range over the displayed coordinatewise box. -/
theorem integral_pair_quantile_lower (n : ℕ) (hn : 0 < n) (hb : 1 ≤ upperQuantile n)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/16)
    (σ h : Fin (n+2) → ℝ) (hs : ∀k,1-a ≤ σ k) (hS : ∀k,σ k ≤ 1+a)
    (hh : ∀k,|h k| ≤ a*upperQuantile n)
    (htail : Real.exp (-a*(upperQuantile n)^2) ≤ 1/2) (i j : Fin (n+2)) :
    a/(8*((n:ℝ)+2)^2)*Real.exp (-24*a*(upperQuantile n)^2) ≤
      ∫x,hazardPairDensity σ h x i j := by
  let b := upperQuantile n
  let m : ℝ := (n:ℝ)+2
  let T := (1+4*a)*b
  let U := (1+5*a)*b
  have hb0 : 0 < b := upperQuantile_pos hn
  have hm : 0 < m := by dsimp [m];positivity
  have hs0 : 0 < 1-a := by linarith
  have hS0 : 0 < 1+a := by positivity
  have hTU : T ≤ U := by dsimp [T,U];nlinarith
  have hTH : a*b ≤ T := by dsimp [T];nlinarith
  have ht : (Fintype.card (Fin (n+2)):ℝ)*normalCDF (-((T-a*b)/(1+a))) ≤ 1/2 := by
    have hh' := (upper_interval_tail n hn a ha ha1).trans htail
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,T,b] using hh'
  have hbase := integral_hazardPairDensity_lower σ h (1-a) (1+a) (a*b) T U
    hs0 hs hS hh hTU hTH ht i j
  have hu := upper_interval_standardized b a hb0.le ha.le ha1
  have hu0 : 0 ≤ (U+a*b)/(1-a) := by dsimp [U];positivity
  have hpdf : normalPDF ((1+8*a)*b) ≤ normalPDF ((U+a*b)/(1-a)) :=
    normalPDF_le_of_sq_le _ _ (pow_le_pow_left₀ hu0 hu 2)
  have hdiv : normalPDF ((1+8*a)*b)/2 ≤ normalPDF ((U+a*b)/(1-a))/(1+a) := by
    exact (div_le_div_of_nonneg_left (normalPDF_pos _).le hS0 (by linarith : 1+a ≤ 2)).trans
      (div_le_div_of_nonneg_right hpdf hS0.le)
  have hratio : normalPDF ((1+8*a)*b)=normalPDF b*Real.exp (-(8*a+32*a^2)*b^2) := by
    rw [normalPDF_ratio b ((1+8*a)*b)]
    congr 2
    ring
  have hD : b/(2*m)*Real.exp (-(8*a+32*a^2)*b^2) ≤
      normalPDF ((U+a*b)/(1-a))/(1+a) := by
    have hh' := mul_le_mul_of_nonneg_right (quantile_density_lower n hn) (Real.exp_pos (-(8*a+32*a^2)*b^2)).le
    have hd := div_le_div_of_nonneg_right hh' (by norm_num : (0:ℝ) ≤ 2)
    rw [hratio] at hdiv
    have hd' : b/(2*m)*Real.exp (-(8*a+32*a^2)*b^2) ≤
        normalPDF b*Real.exp (-(8*a+32*a^2)*b^2)/2 := by
      convert hd using 1 <;> dsimp only [b,m] <;> field_simp <;> ring
    exact hd'.trans hdiv
  have hD0 : 0 ≤ b/(2*m)*Real.exp (-(8*a+32*a^2)*b^2) := by positivity
  have hsq := pow_le_pow_left₀ hD0 hD 2
  have hpre : 0 ≤ (U-T)/2 := div_nonneg (sub_nonneg.mpr hTU) (by norm_num)
  have hlower := (mul_le_mul_of_nonneg_left hsq hpre).trans hbase
  have he : (U-T)/2*(b/(2*m)*Real.exp (-(8*a+32*a^2)*b^2))^2=
      (a*b^3/(8*m^2))*Real.exp (-(16*a+64*a^2)*b^2) := by
    dsimp [U,T]
    rw [mul_pow,←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have hexp : (2:ℝ)*(-(8*a+32*a^2)*b^2)=-(16*a+64*a^2)*b^2 := by ring
    rw [hexp]
    field_simp
    ring
  rw [he] at hlower
  have hb3 : 1 ≤ b^3 := one_le_pow₀ hb
  have helo : Real.exp (-24*a*b^2) ≤ Real.exp (-(16*a+64*a^2)*b^2) := by
    apply Real.exp_le_exp.mpr
    have hcoef : 16*a+64*a^2 ≤ 24*a := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    linarith
  have hcoef : a/(8*m^2) ≤ a*b^3/(8*m^2) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hfinal := mul_le_mul hcoef helo (Real.exp_pos _).le (by positivity)
  exact hfinal.trans hlower

end NegativeVotingHazardUniformCoefficientBounds
