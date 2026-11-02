import GaussianDiagonalHazardTaylor
import GaussianNormalizedRowPayment
import GaussianGlobalCovarianceDeficit
import GaussianCompetitiveEqualRowProxy

/-! Actual uniform summed row payment. The Taylor, covariance support,
normalization and row exclusion inputs are all derived, not hypotheses. -/
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Classical Topology
universe u
namespace NegativeVotingActualRowPayment
open NegativeVoting NegativeVotingDiagonalHazardTaylor NegativeVotingNormalizedRowPayment
  NegativeVotingNormalizedDiagonalDeviation NegativeVotingGlobalCovarianceDeficit
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingBalancedReference
  NegativeVotingCentroidOptimization NegativeVotingRegularCovarianceDeficit
  NegativeVotingGaussianMaximumMean NegativeVotingOneRowRadialCloseness
  NegativeVotingGeometricMedianProxy NegativeVotingCovarianceRadialNormalization
  NegativeVotingCompetitiveEqualRowProxy NegativeVotingCompetitiveCovarianceTransfer
  NegativeVotingAssignmentCoordinateBridge NegativeVotingFractionalMass
  NegativeVotingCompetitiveDeficit NegativeVotingRegularScoreLaw
variable {n d e : ℕ}

lemma referenceRowRadius_le_referenceScale (n:ℕ) : referenceRowRadius n ≤ referenceScale n := by
  have ha:=referenceScale_pos n
  have hb:=referenceRowRadius_pos n
  have hsq:(referenceRowRadius n)^2 ≤ (referenceScale n)^2:=by
    rw [referenceRowRadius_sq]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).mpr
    nlinarith [sq_nonneg (referenceScale n)]
  nlinarith

/-- One threshold precedes every ambient dimension and every centered
fixed-energy row system with the indicated elementary norm cap. -/
theorem eventually_bounded_fixed_energy_row_payment (η:ℝ) (hη:0<η) :
    ∀ᶠ n:ℕ in atTop,∀ (e:ℕ) (B:Fin (n+2)→FSC.Coord e),
      (∑i,B i=0) → rowEnergy B=referenceFirstWeight n →
      (∀i,‖B i‖ ≤ 2*referenceScale n) →
      radialError B (referenceRowRadius n) ≤
        (96*((n:ℝ)+2)^(30*η))*regularCovarianceDeficit n B := by
  obtain ⟨a,ha,ha1,hTaylor⟩:=exists_uniform_hazard_taylor η 12 hη (by norm_num)
  have ht:Tendsto (fun n:ℕ=>((n:ℝ)+2)^(-30*η)) atTop (𝓝 0):=by
    simpa only [Function.comp_def,neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<30*η by positivity)).comp size_tendsto
  have he:Tendsto (fun n:ℕ=>26*((n:ℝ)+2)^(-10*η)) atTop (𝓝 0):=by
    simpa only [Function.comp_def,neg_mul,mul_zero] using
      ((tendsto_rpow_neg_atTop (show 0<10*η by positivity)).comp size_tendsto).const_mul 26
  filter_upwards [hTaylor,ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/24)),
    he.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/24)),eventually_gt_atTop (0:ℕ)] with n hT hts hes hn
  intro e B hB henergy hrows
  let m:ℝ:=(n:ℝ)+2
  have hm:0 < m:=by dsimp [m];positivity
  let t:ℝ:=m^(-30*η)
  have htpos:0<t:=Real.rpow_pos_of_pos hm _
  have herr:=hT.2 (rowDirection n B) (rowDirection_abs_le hn B hrows)
    (rowDirection_centered B henergy) t ⟨htpos.le,le_rfl⟩
  have hsmall:26*m^(20*η)*t ≤ 1/24:=by
    calc
      _ = 26*m^(-10*η):=by dsimp [t];rw [mul_assoc,←Real.rpow_add hm];congr 1;ring
      _ ≤ _:=hes.le
  have hb:=referenceBasis_spec n
  have hp:=radial_payment_of_summed_remainder hn (referenceBasis n) hb.2.2 hb.2.1
    B hB henergy hrows t (m^(20*η)) htpos hts.le herr hsmall
  have htinv:96/t=96*m^(30*η):=by
    dsimp [t]
    rw [show -30*η=-(30*η) by ring,Real.rpow_neg hm.le,div_inv_eq_mul]
  simpa only [htinv,m] using hp

/-- The norm cap is itself a consequence of the literal small deficit.
There is no diagonal, rank, or moment assumption in this endpoint. -/
theorem eventually_fixed_energy_row_payment (η C:ℝ) (hη:0<η) :
    ∀ᶠ n:ℕ in atTop,∀ (e:ℕ) (B:Fin (n+2)→FSC.Coord e),
      (∑i,B i=0) → rowEnergy B=referenceFirstWeight n →
      regularCovarianceDeficit n B ≤ C/((n:ℝ)+2)^2 →
      radialError B (referenceRowRadius n) ≤
        (96*((n:ℝ)+2)^(30*η))*regularCovarianceDeficit n B := by
  filter_upwards [eventually_bounded_fixed_energy_row_payment η hη,
    eventually_reference_rows_radially_close C] with n hpay hclose
  intro e B hB henergy hR
  apply hpay e B hB henergy
  intro i
  have hh:=(abs_lt.mp (hclose e B hB henergy hR i)).2
  have hb:=referenceRowRadius_le_referenceScale n
  have ha:=referenceScale_pos n
  linarith

/-- Exact normalization gives the same coefficient for arbitrary centered
near-reference-energy rows, including rank-deficient configurations. -/
theorem eventually_near_energy_row_payment (η:ℝ) (hη:0<η) :
    ∀ᶠ n:ℕ in atTop,∀ (e:ℕ) (B:Fin (n+2)→FSC.Coord e),
      (∑i,B i=0) →
      |rowEnergy B-referenceFirstWeight n| ≤ 256/((n:ℝ)+2)^2 →
      regularCovarianceDeficit n B ≤ 256/((n:ℝ)+2)^2 →
      radialError B (referenceRowRadius n) ≤
        (96*((n:ℝ)+2)^(30*η))*regularCovarianceDeficit n B := by
  filter_upwards [eventually_fixed_energy_row_payment η 512 hη,
    eventually_referenceFirstWeight_size_large 4096,eventually_gt_atTop (0:ℕ)] with n hpay hlarge hn
  intro e B hB hW hR
  let m:ℝ:=(n:ℝ)+2
  let w:=referenceFirstWeight n
  have hm:0 < m:=by dsimp [m];positivity
  have hm1:1 ≤ m:=by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hw:0<w:=referenceFirstWeight_pos n
  have hsmall:256/m^2<w/8:=by
    apply (div_lt_iff₀ (sq_pos_of_pos hm)).mpr
    change 4096<w*m at hlarge
    have hx:=mul_le_mul_of_nonneg_left hm1 (show 0 ≤ w*m by positivity)
    nlinarith
  have hWpos:0<rowEnergy B:=by
    change |rowEnergy B-w| ≤ 256/m^2 at hW
    have hh:=(abs_le.mp hW).1
    linarith
  have hs:1/2 ≤ radialScale n B:=radialScale_half_le hn B hB hWpos (hR.trans hsmall.le)
  have hnormR:regularCovarianceDeficit n (normalizedRows n B) ≤ 512/((n:ℝ)+2)^2:=by
    have hh:=(normalizedRows_deficit_le hn B hB hWpos hs).trans
      (mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 2))
    exact hh.trans_eq (by ring)
  have hnpay:=hpay e (normalizedRows n B) (normalizedRows_centered B hB)
    (normalizedRows_energy B hWpos) hnormR
  apply radial_payment_transfer B hWpos _ _ hnpay
  have hp:1 ≤ m^(30*η):=Real.one_le_rpow hm1 (by positivity)
  change 2 ≤ 96*m^(30*η)
  linarith

/-- Full competitor specialization. One alphabet threshold precedes the
ambient coordinates, reference, completed-measurable fractional rule and the
entire strictly negative voting interval. -/
theorem eventually_actual_competitive_row_payment (η:ℝ) (hη:0<η) :
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (Ref:Fin (n+2)→κ→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐx ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0<r) (hr:r ≤ 1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment Ref))
      (e:ℕ) (coord:FSC.Coord e≃ₗᵢ[ℝ]EuclideanSpace ℝ κ),
      radialError (centroidRows (coordinateRule coord f)) (referenceRowRadius n) ≤
        (96*((n:ℝ)+2)^(30*η))*regularCovarianceDeficit n (centroidRows (coordinateRule coord f)) := by
  filter_upwards [eventually_near_energy_row_payment η hη,
    eventually_uniform_actual_covariance_deficit_transfer,
    NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds] with n hpay hR hD
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp e coord
  have hm:(0:ℝ)<(n:ℝ)+2:=by positivity
  have hr2:r ≤ 2/((n:ℝ)+2):=hr.trans (by
    apply (div_le_div_iff₀ (by positivity) hm).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) n])
  apply hpay e (centroidRows (coordinateRule coord f))
    (centroidRows_sum_zero (assignmentMass f) _ (coordinateRule_feasible coord f hf hp))
  · change |centroidEnergy (coordinateRule coord f)-referenceFirstWeight n| ≤ _
    rw [coordinateRule_centroidEnergy coord f hf hp]
    have hh:=hD κ Ref hRef f hf hp r hr0.le hr hcomp
    have hbound:|assignmentFirstEnergy f-referenceFirstWeight n| ≤ 128*r/((n:ℝ)+2):=by
      apply (mul_le_mul_iff_right₀ hr0).mp
      have hx:=hh.2.2.1.trans hh.2.2.2
      simp only [div_eq_mul_inv] at hx ⊢
      nlinarith
    apply hbound.trans
    apply (div_le_div_iff₀ hm (sq_pos_of_pos hm)).mpr
    have hx:=(le_div_iff₀ hm).mp hr2
    nlinarith [mul_le_mul_of_nonneg_right hx hm.le]
  · have hh:=(hR κ Ref hRef f hf hp r hr0 hr hcomp e coord).2
    apply hh.trans
    apply (div_le_div_iff₀ hm (sq_pos_of_pos hm)).mpr
    have hx:=(le_div_iff₀ hm).mp hr2
    nlinarith [mul_le_mul_of_nonneg_right hx hm.le]

end NegativeVotingActualRowPayment
