import GaussianOneRowSymmetrization

/-! Literal radial closeness of every row at fixed reference energy. The
dimension threshold precedes the ambient dimension and the row system. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Classical RealInnerProductSpace Topology
namespace NegativeVotingOneRowRadialCloseness
open NegativeVoting NegativeVotingOneRowSymmetrization NegativeVotingOneRowRayExclusion
  NegativeVotingBalancedReference NegativeVotingGaussianMaximumMean
  NegativeVotingCenteredParseval NegativeVotingCentroidOptimization
  NegativeVotingRegularCovarianceDeficit NegativeVotingCovarianceRealization
  NegativeVotingFanValue NegativeVotingRayDeficit NegativeVotingCovarianceConcavity
  NegativeVotingGaussianMaximum NegativeVotingFanCovarianceValue
variable {n d e : ℕ}

def referenceRowRadius (n : ℕ) : ℝ := referenceScale n*Real.sqrt (((n:ℝ)+1)/((n:ℝ)+2))

theorem referenceRowRadius_pos (n : ℕ) : 0 < referenceRowRadius n :=
  mul_pos (referenceScale_pos n) (Real.sqrt_pos.mpr (by positivity))

theorem referenceRowRadius_sq (n : ℕ) :
    (referenceRowRadius n)^2=(referenceScale n)^2*((n:ℝ)+1)/((n:ℝ)+2) := by
  rw [referenceRowRadius,mul_pow,Real.sq_sqrt (by positivity)]
  ring

theorem referenceFirstWeight_scale (n : ℕ) :
    referenceFirstWeight n=(referenceScale n)^2*((n:ℝ)+1) := by
  unfold referenceFirstWeight referenceScale
  field_simp

theorem operatorValue_identity (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (p : Fin (n+2) → ℝ) :
    operatorValue b p (ContinuousLinearMap.id ℝ (FSC.Coord d))=optimizedValue b p := by
  unfold operatorValue
  have he : gramVelocity b (ContinuousLinearMap.id ℝ (FSC.Coord d))=Matrix.gram ℝ b := by
    ext i j
    simp only [gramVelocity,ContinuousLinearMap.id_apply,Matrix.gram_apply]
  rw [he,covarianceValue_gram]

/-- The reference scaling is exact, rather than an asymptotic replacement. -/
theorem actual_normalized_deficit (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2) → FSC.Coord e) (henergy : rowEnergy B=referenceFirstWeight n) :
    operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))-
      optimizedValue (fun i => (referenceScale n)⁻¹ • B i) (uniformMass n)=
        regularCovarianceDeficit n B/referenceScale n := by
  have ha : referenceScale n ≠ 0 := ne_of_gt (referenceScale_pos n)
  have hv := reference_scaled_value b hG
  rw [optimizedValue_smul_rows b (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
    (referenceScale n) (referenceScale_pos n).le] at hv
  rw [operatorValue_identity,optimizedValue_smul_rows B (uniformMass n) (uniformMass_pos n)
    (uniformMass_sum n) ((referenceScale n)⁻¹) (inv_nonneg.mpr (referenceScale_pos n).le)]
  unfold regularCovarianceDeficit
  rw [henergy,←hv]
  field_simp
  <;> ring

/-- Actual fixed-energy targets have uniformly nonzero, nearly equal row
lengths once their literal covariance deficit is below the explicit threshold. -/
theorem reference_rows_radially_close (hn : 0 < n)
    (B : Fin (n+2) → FSC.Coord e) (hB : ∑ i,B i=0)
    (henergy : rowEnergy B=referenceFirstWeight n)
    (hloss : regularCovarianceDeficit n B < referenceScale n/(16777216*Real.pi*((n:ℝ)+2)))
    (i : Fin (n+2)) : |‖B i‖-referenceRowRadius n| < referenceRowRadius n/256 := by
  let b := centeredParsevalBasis (n+2) (by omega)
  have hb := centeredParsevalBasis_spec (n+2) (by omega)
  have hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hb.2.1
  let U : Fin (n+2) → FSC.Coord e := fun j => (referenceScale n)⁻¹ • B j
  have hU : ∑ j,U j=0 := by rw [show (∑ j,U j)=(referenceScale n)⁻¹ • ∑ j,B j by simp [U,Finset.smul_sum],hB,smul_zero]
  have hUE : rowEnergy U=(n:ℝ)+1 := by
    have he : rowEnergy U=((referenceScale n)⁻¹)^2*rowEnergy B := by
      simp only [rowEnergy,U,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Finset.mul_sum]
    rw [he,henergy,referenceFirstWeight_scale]
    field_simp [ne_of_gt (referenceScale_pos n)]
  have hUL : operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord (n+2-1)))-
      optimizedValue U (uniformMass n) < 1/(16777216*Real.pi*((n:ℝ)+2)) := by
    rw [actual_normalized_deficit b hG B henergy]
    apply (div_lt_iff₀ (referenceScale_pos n)).mpr
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using hloss
  have hh := normalized_row_close_of_small_deficit hn b hG hb.2.2 U hU hUE hUL i
  have he : ((n:ℝ)+2)/((n:ℝ)+1)*‖U i‖^2=‖B i‖^2/(referenceRowRadius n)^2 := by
    simp only [U,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (referenceScale_pos n),mul_pow]
    rw [referenceRowRadius_sq]
    field_simp
  rw [he] at hh
  have hc := radial_close_of_square_close ‖B i‖ (referenceRowRadius n) (1/256)
    (norm_nonneg _) (referenceRowRadius_pos n) (by norm_num) hh
  simpa only [div_eq_mul_inv,one_mul] using hc

theorem eventually_referenceScale_size_large (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C < referenceScale n*((n:ℝ)+2) := by
  filter_upwards [upperQuantile_tendsto.eventually_gt_atTop (max C 1),
    eventually_scaledMaximum_mean_lower] with n hb hmean
  have hbpos : 0 < upperQuantile n := by linarith [le_max_right C 1]
  have hμ : upperQuantile n ≤ maximumMean n := by
    have hh : 0 ≤ upperQuantile n*(maximumMean n-upperQuantile n) := by linarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hbpos).mp hh)
  have ha : referenceScale n*((n:ℝ)+1)=maximumMean n := by
    unfold referenceScale
    field_simp
  have hmul : maximumMean n ≤ referenceScale n*((n:ℝ)+2) := by
    nlinarith [referenceScale_pos n]
  exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left C 1) hb) (hμ.trans hmul)

/-- Dimension-first uniform row exclusion. This is the weaker Cheeger route:
any fixed O(m^-2) actual deficit is sufficient, with no sharp profile input. -/
theorem eventually_reference_rows_radially_close (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (e : ℕ) (B : Fin (n+2) → FSC.Coord e),
      (∑ i,B i)=0 → rowEnergy B=referenceFirstWeight n →
      regularCovarianceDeficit n B ≤ C/((n:ℝ)+2)^2 →
      ∀ i,|‖B i‖-referenceRowRadius n| < referenceRowRadius n/256 := by
  filter_upwards [eventually_gt_atTop (0:ℕ),
    eventually_referenceScale_size_large (16777216*Real.pi*C)] with n hn hlarge
  intro e B hB henergy hdef i
  apply reference_rows_radially_close hn B hB henergy
  apply lt_of_le_of_lt hdef
  apply (div_lt_div_iff₀ (by positivity : 0 < ((n:ℝ)+2)^2)
    (by positivity : 0 < 16777216*Real.pi*((n:ℝ)+2))).mpr
  have hh := mul_lt_mul_of_pos_right hlarge (show 0 < (n:ℝ)+2 by positivity)
  nlinarith only [hh]

end NegativeVotingOneRowRadialCloseness
