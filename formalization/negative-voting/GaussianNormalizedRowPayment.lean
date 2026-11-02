import GaussianNormalizedDiagonalDeviation

/-! Actual row-payment conversion from the single explicit coefficient remainder.
The remainder is not assumed true without its future selected-path proof. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNormalizedRowPayment
open NegativeVoting NegativeVotingNormalizedDiagonalDeviation NegativeVotingDiagonalVarianceSupport
  NegativeVotingDiagonalSupportAlgebra NegativeVotingRegularHazardDerivative
  NegativeVotingRegularTieVariance NegativeVotingBalancedReference NegativeVotingFanValue
  NegativeVotingRegularCovarianceDeficit NegativeVotingGaussianMaximumMean
  NegativeVotingCentroidOptimization NegativeVotingOneRowRadialCloseness
  NegativeVotingGeometricMedianProxy NegativeVotingRayDeficit NegativeVotingCovarianceRadialNormalization
variable {n d e : ℕ}

lemma direction_variance_positive (hn : 0<n) (B : Fin (n+2)→FSC.Coord e)
    (hrows : ∀i,‖B i‖ ≤ 2*referenceScale n) (t : ℝ) (ht : 0 ≤ t) (htsmall : t ≤ 1/24)
    (i : Fin (n+2)) : 0<1+t*rowDirection n B i := by
  have hi: -12 ≤ rowDirection n B i := (abs_le.mp (rowDirection_abs_le hn B hrows i)).1
  have hp:=mul_le_mul_of_nonneg_left hi ht
  linarith

lemma direction_support_weight_bound (hn : 0<n) (B : Fin (n+2)→FSC.Coord e)
    (hrows : ∀i,‖B i‖ ≤ 2*referenceScale n) (t : ℝ) (ht : 0 ≤ t) (htsmall : t ≤ 1)
    (i : Fin (n+2)) :
    |diagonalSupportWeight (baseDiagonal n) (diagonalKappa n) t (rowDirection n B) i| ≤ 26 := by
  have hd:=baseDiagonal_bounds n
  have hk:=diagonalKappa_bounds hn
  have hx:=rowDirection_abs_le hn B hrows i
  have hp:(1+t)*diagonalKappa n ≤ 2 := by nlinarith
  have hk0:0 ≤ diagonalKappa n := by linarith [hk.1]
  have hd0:0 ≤ baseDiagonal n := by linarith [hd.1]
  have hp0:0 ≤ (1+t)*diagonalKappa n := mul_nonneg (by linarith) hk0
  unfold diagonalSupportWeight
  calc
    _ ≤ |2*baseDiagonal n|+|(1+t)*diagonalKappa n*rowDirection n B i| := abs_add_le _ _
    _ = 2*baseDiagonal n+((1+t)*diagonalKappa n)*|rowDirection n B i| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 2*baseDiagonal n),abs_mul,abs_of_nonneg hp0]
    _ ≤ 26 := by nlinarith [mul_le_mul hx hp hp0 (by norm_num : (0:ℝ) ≤ 12)]

/-- The covariance is the literal normalized covariance of the arbitrary centered
rows. Only the actual selected coefficient remainder is conditional. -/
theorem radial_payment_of_summed_remainder (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0)
    (henergy : rowEnergy B=referenceFirstWeight n)
    (hrows : ∀i,‖B i‖ ≤ 2*referenceScale n)
    (t E : ℝ) (ht : 0<t) (htsmall : t ≤ 1/24)
    (he : (∑i,|hazardCoefficient (varianceStdPath (rowDirection n B) t)
      (balancedVariancePath (rowDirection n B) t) i-
      (referenceScale n-referenceScale n*eta n*t*rowDirection n B i)|) ≤
      E*referenceScale n*t^2*(∑i,(rowDirection n B i)^2))
    (hsmall : 26*E*t ≤ 1/24) :
    radialError B (referenceRowRadius n) ≤ (96/t)*regularCovarianceDeficit n B := by
  have hgap:=actual_support_gap_of_summed_remainder hn b hP hG
    (normalizedRowCovariance n b B) (normalizedRowCovariance_psd b B)
    (rowDirection n B) (rowDirection_centered B henergy) t 26 E ht.le (by norm_num)
    (direction_variance_positive hn B hrows t ht.le htsmall)
    (by intro i; simpa only [baseDiagonal_eq,diagonalKappa] using normalized_row_diagonal hn b hG B hB i)
    (by intro i; simpa only [baseDiagonal_eq,diagonalKappa] using
      direction_support_weight_bound hn B hrows t ht.le (by linarith) i) he hsmall
  have hg:=mul_le_mul_of_nonneg_left hgap (referenceScale_pos n).le
  rw [←normalized_deficit_exact b hG B hB henergy] at hg
  have hr:=radialError_le_direction hn B
  have hh:=mul_le_mul_of_nonneg_left hr ht.le
  have hmul:t*radialError B (referenceRowRadius n) ≤ 96*regularCovarianceDeficit n B:=by nlinarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using hmul

/-- Exact radial normalization transfers any constant at least two without
loss. No small-deficit or rank hypothesis is needed for this algebraic step. -/
theorem radial_payment_transfer (B : Fin (n+2)→FSC.Coord e) (hW : 0<rowEnergy B)
    (C : ℝ) (hC : 2 ≤ C)
    (hpay : radialError (normalizedRows n B) (referenceRowRadius n) ≤
      C*regularCovarianceDeficit n (normalizedRows n B)) :
    radialError B (referenceRowRadius n) ≤ C*regularCovarianceDeficit n B := by
  rw [radialError_identity B hW,deficit_radial_identity B hW]
  have hh:=mul_le_mul_of_nonneg_left hpay (radialScale_pos B hW).le
  have hp:=mul_nonneg (sub_nonneg.mpr hC)
    (show 0 ≤ referenceFirstWeight n*(radialScale n B-1)^2 from
      mul_nonneg (referenceFirstWeight_pos n).le (sq_nonneg _))
  nlinarith

end NegativeVotingNormalizedRowPayment
