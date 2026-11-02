import GaussianOneRowRadialCloseness
import GaussianGeometricMedianProxy

/-! Exact radial normalization of actual Gaussian row deficits. The scalar
normalization and radial-error identities include rank-deficient row systems. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Classical RealInnerProductSpace Topology
namespace NegativeVotingCovarianceRadialNormalization
open NegativeVoting NegativeVotingCentroidOptimization NegativeVotingBalancedReference
  NegativeVotingRegularCovarianceDeficit NegativeVotingRayDeficit NegativeVotingFanValue
  NegativeVotingOneRowRadialCloseness NegativeVotingGeometricMedianProxy
  NegativeVotingGaussianMaximumMean
variable {n e : ℕ}

def radialScale (n : ℕ) (B : Fin (n+2) → FSC.Coord e) : ℝ :=
  Real.sqrt (rowEnergy B/referenceFirstWeight n)

def normalizedRows (n : ℕ) (B : Fin (n+2) → FSC.Coord e) : Fin (n+2) → FSC.Coord e :=
  fun i => (radialScale n B)⁻¹ • B i

theorem referenceFirstWeight_pos (n : ℕ) : 0 < referenceFirstWeight n := by
  rw [referenceFirstWeight_scale]
  exact mul_pos (sq_pos_of_pos (referenceScale_pos n)) (by positivity)

theorem rowEnergy_smul (B : Fin (n+2) → FSC.Coord e) (s : ℝ) :
    rowEnergy (fun i => s • B i)=s^2*rowEnergy B := by
  simp only [rowEnergy,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Finset.mul_sum]

theorem radialScale_pos (B : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B) :
    0 < radialScale n B := Real.sqrt_pos.mpr (div_pos hW (referenceFirstWeight_pos n))

theorem radialScale_sq (B : Fin (n+2) → FSC.Coord e) :
    (radialScale n B)^2=rowEnergy B/referenceFirstWeight n :=
  Real.sq_sqrt (div_nonneg (rowEnergy_nonneg B) (referenceFirstWeight_pos n).le)

theorem normalizedRows_energy (B : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B) :
    rowEnergy (normalizedRows n B)=referenceFirstWeight n := by
  change rowEnergy (fun i => (radialScale n B)⁻¹ • B i)=_
  rw [rowEnergy_smul,inv_pow,radialScale_sq]
  field_simp [ne_of_gt hW,ne_of_gt (referenceFirstWeight_pos n)]

theorem normalizedRows_centered (B : Fin (n+2) → FSC.Coord e) (hB : ∑ i,B i=0) :
    ∑ i,normalizedRows n B i=0 := by simp [normalizedRows,←Finset.smul_sum,hB]

theorem radialScale_smul_normalized (B : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B) :
    (fun i => radialScale n B • normalizedRows n B i)=B := by
  funext i
  simp [normalizedRows,smul_smul,ne_of_gt (radialScale_pos B hW)]

/-- The true Gaussian optimization value is positively homogeneous. -/
theorem deficit_radial_identity (B : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B) :
    regularCovarianceDeficit n B=
      referenceFirstWeight n*(radialScale n B-1)^2/2+
        radialScale n B*regularCovarianceDeficit n (normalizedRows n B) := by
  have hv := optimizedValue_smul_rows (normalizedRows n B) (uniformMass n)
    (uniformMass_pos n) (uniformMass_sum n) (radialScale n B) (radialScale_pos B hW).le
  rw [radialScale_smul_normalized B hW] at hv
  have he : rowEnergy B=(radialScale n B)^2*referenceFirstWeight n := by
    rw [radialScale_sq]
    field_simp [ne_of_gt (referenceFirstWeight_pos n)]
  unfold regularCovarianceDeficit
  rw [normalizedRows_energy B hW,hv,he]
  ring

/-- A small actual covariance deficit forces the normalization away from zero. -/
theorem radialScale_half_le (hn : 0 < n) (B : Fin (n+2) → FSC.Coord e)
    (hB : ∑ i,B i=0) (hW : 0 < rowEnergy B)
    (hR : regularCovarianceDeficit n B ≤ referenceFirstWeight n/8) :
    1/2 ≤ radialScale n B := by
  have hpos := radialScale_pos B hW
  have hnon := regularCovarianceDeficit_nonneg hn _ (normalizedRows_centered B hB)
  have hid := deficit_radial_identity B hW
  have hw := referenceFirstWeight_pos n
  have hsq : (radialScale n B-1)^2 ≤ 1/4 := by
    nlinarith [mul_nonneg hpos.le hnon]
  nlinarith [sq_nonneg (radialScale n B)]

theorem normalizedRows_deficit_le (hn : 0 < n) (B : Fin (n+2) → FSC.Coord e)
    (hB : ∑ i,B i=0) (hW : 0 < rowEnergy B) (hs : 1/2 ≤ radialScale n B) :
    regularCovarianceDeficit n (normalizedRows n B) ≤ 2*regularCovarianceDeficit n B := by
  have hid := deficit_radial_identity B hW
  have hnon := regularCovarianceDeficit_nonneg hn _ (normalizedRows_centered B hB)
  have hp := mul_nonneg (referenceFirstWeight_pos n).le (sq_nonneg (radialScale n B-1))
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hnon]

theorem referenceRadius_energy (n : ℕ) :
    ((n:ℝ)+2)*(referenceRowRadius n)^2=referenceFirstWeight n := by
  rw [referenceRowRadius_sq,referenceFirstWeight_scale]
  field_simp

/-- Radial error itself has the same exact normalization, with no estimate. -/
theorem radialError_identity (B : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B) :
    radialError B (referenceRowRadius n)=
      referenceFirstWeight n*(radialScale n B-1)^2+
        radialScale n B*radialError (normalizedRows n B) (referenceRowRadius n) := by
  let C := normalizedRows n B
  let s := radialScale n B
  let β := referenceRowRadius n
  have hs : 0 < s := radialScale_pos B hW
  have hC : rowEnergy C=referenceFirstWeight n := normalizedRows_energy B hW
  have hB : B=(fun i => s • C i) := (radialScale_smul_normalized B hW).symm
  change radialError B β=referenceFirstWeight n*(s-1)^2+s*radialError C β
  conv_lhs => rw [hB]
  change (∑ i,(‖s • C i‖-β)^2)=referenceFirstWeight n*(s-1)^2+s*(∑ i,(‖C i‖-β)^2)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  have hpoly (i : Fin (n+2)) : (s*‖C i‖-β)^2=
      s*(‖C i‖-β)^2+(s^2-s)*‖C i‖^2+(1-s)*β^2 := by ring
  simp_rw [hpoly]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  change s*(∑ i,(‖C i‖-β)^2)+(s^2-s)*rowEnergy C+
    ((n:ℝ)+2)*((1-s)*β^2)=_
  rw [hC]
  have hβ : ((n:ℝ)+2)*β^2=referenceFirstWeight n := referenceRadius_energy n
  nlinarith only [hβ]

theorem normalization_distance (B : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B) :
    (∑ i,‖normalizedRows n B i-B i‖^2)=referenceFirstWeight n*(radialScale n B-1)^2 := by
  have hb (i) : normalizedRows n B i-B i=(1-radialScale n B) • normalizedRows n B i := by
    rw [←congrFun (radialScale_smul_normalized B hW) i]
    module
  simp_rw [hb,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [←Finset.mul_sum]
  change (1-radialScale n B)^2*rowEnergy (normalizedRows n B)=_
  rw [normalizedRows_energy B hW]
  ring

/-- Transfer of the geometric-median estimate to the original, unnormalized
rows. No covariance deficit or radial error is silently discarded. -/
theorem proxy_error_transfer (B Z : Fin (n+2) → FSC.Coord e) (hW : 0 < rowEnergy B)
    (hs : 1/2 ≤ radialScale n B)
    (hZ : (∑ i,‖Z i-normalizedRows n B i‖^2) ≤
      4096*radialError (normalizedRows n B) (referenceRowRadius n)) :
    (∑ i,‖Z i-B i‖^2) ≤ 16386*radialError B (referenceRowRadius n) := by
  have hrad := radialError_identity B hW
  have hnon : 0 ≤ radialError (normalizedRows n B) (referenceRowRadius n) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnormnon : 0 ≤ referenceFirstWeight n*(radialScale n B-1)^2 :=
    mul_nonneg (referenceFirstWeight_pos n).le (sq_nonneg _)
  have hradle : radialError (normalizedRows n B) (referenceRowRadius n) ≤
      2*radialError B (referenceRowRadius n) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hnon]
  have hdistle : (∑ i,‖normalizedRows n B i-B i‖^2) ≤ radialError B (referenceRowRadius n) := by
    rw [normalization_distance B hW]
    nlinarith [mul_nonneg (radialScale_pos B hW).le hnon]
  have hsum : (∑ i,‖Z i-B i‖^2) ≤
      2*(∑ i,‖Z i-normalizedRows n B i‖^2)+2*(∑ i,‖normalizedRows n B i-B i‖^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have ht : ‖Z i-B i‖ ≤ ‖Z i-normalizedRows n B i‖+‖normalizedRows n B i-B i‖ := by
      calc
        _ = ‖(Z i-normalizedRows n B i)+(normalizedRows n B i-B i)‖ := by congr 1; module
        _ ≤ _ := norm_add_le _ _
    nlinarith [sq_nonneg (‖Z i-normalizedRows n B i‖-‖normalizedRows n B i-B i‖),norm_nonneg (Z i-B i)]
  nlinarith

end NegativeVotingCovarianceRadialNormalization
