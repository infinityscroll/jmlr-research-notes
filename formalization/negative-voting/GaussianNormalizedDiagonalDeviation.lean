import GaussianDiagonalVarianceSupport
import GaussianCovarianceRadialNormalization

/-! Actual normalized row diagonals, their centered variance direction, and
the exact conversion between covariance support and row deficit. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNormalizedDiagonalDeviation
open NegativeVoting NegativeVotingCentroidOptimization NegativeVotingBalancedReference
  NegativeVotingRayDeficit NegativeVotingRegularCovarianceDeficit NegativeVotingOneRowSymmetrization
  NegativeVotingOneRowRadialCloseness NegativeVotingCovarianceConcavity NegativeVotingFanValue
  NegativeVotingDiagonalSupportAlgebra NegativeVotingGeometricMedianProxy
  NegativeVotingGaussianMaximumMean NegativeVotingCovarianceRealization
variable {n d e : ℕ}

def diagonalKappa (n : ℕ) : ℝ := 1-2/((n:ℝ)+2)
def baseDiagonal (n : ℕ) : ℝ := ((n:ℝ)+1)/((n:ℝ)+2)
def rowDirection (n : ℕ) (B : Fin (n+2)→FSC.Coord e) (i : Fin (n+2)) : ℝ :=
  (‖B i‖^2/(referenceScale n)^2-baseDiagonal n)/diagonalKappa n

lemma diagonalKappa_bounds (hn : 0<n) : (1/3:ℝ) ≤ diagonalKappa n ∧ diagonalKappa n ≤ 1 := by
  have hn':(1:ℝ) ≤ n:=by exact_mod_cast hn
  have hq:(2:ℝ)/((n:ℝ)+2) ≤ 2/3:=div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  unfold diagonalKappa
  constructor <;> linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) (show (0:ℝ) ≤ (n:ℝ)+2 by positivity)]

lemma baseDiagonal_bounds (n : ℕ) : (1/2:ℝ) ≤ baseDiagonal n ∧ baseDiagonal n ≤ 1 := by
  have hm:(0:ℝ)<(n:ℝ)+2:=by positivity
  unfold baseDiagonal
  constructor
  · apply (le_div_iff₀ hm).mpr;linarith [Nat.cast_nonneg (α:=ℝ) n]
  · apply (div_le_iff₀ hm).mpr;linarith

lemma baseDiagonal_eq (n : ℕ) : baseDiagonal n=1-1/((n:ℝ)+2) := by
  unfold baseDiagonal
  field_simp
  ring

lemma rowDirection_centered (B : Fin (n+2)→FSC.Coord e)
    (henergy : rowEnergy B=referenceFirstWeight n) : ∑i,rowDirection n B i=0 := by
  unfold rowDirection
  rw [←Finset.sum_div,Finset.sum_sub_distrib,←Finset.sum_div]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  change (rowEnergy B/(referenceScale n)^2-((n:ℝ)+2)*baseDiagonal n)/diagonalKappa n=0
  rw [henergy,referenceFirstWeight_scale]
  have ha:(referenceScale n)^2≠0:=pow_ne_zero 2 (referenceScale_pos n).ne'
  unfold baseDiagonal
  field_simp
  simp [(referenceScale_pos n).ne']

lemma normalized_row_diagonal (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0) (i : Fin (n+2)) :
    inner ℝ (b i) (normalizedRowCovariance n b B (b i))=
      baseDiagonal n+diagonalKappa n*rowDirection n B i := by
  have hp:=rowCovariance_pairing b (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) B hB i i
  have hk:diagonalKappa n≠0:=ne_of_gt (lt_of_lt_of_le (by norm_num) (diagonalKappa_bounds hn).1)
  unfold normalizedRowCovariance
  simp only [smul_apply,real_inner_smul_right]
  rw [hp,real_inner_self_eq_norm_sq]
  unfold rowDirection
  field_simp
  ring

lemma rowDirection_abs_le (hn : 0<n) (B : Fin (n+2)→FSC.Coord e)
    (hrows : ∀i,‖B i‖ ≤ 2*referenceScale n) (i : Fin (n+2)) :
    |rowDirection n B i| ≤ 12 := by
  have ha:=referenceScale_pos n
  have hx:0 ≤ ‖B i‖^2/(referenceScale n)^2:=by positivity
  have hxx:‖B i‖^2/(referenceScale n)^2 ≤ 4:=by
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith [hrows i,norm_nonneg (B i)]
  have hd:=baseDiagonal_bounds n
  have hk:=diagonalKappa_bounds hn
  have hp:0<diagonalKappa n:=by linarith
  have hb:|‖B i‖^2/(referenceScale n)^2-baseDiagonal n| ≤ 4:=by
    apply abs_le.mpr
    constructor <;> linarith
  unfold rowDirection
  rw [abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem normalized_deficit_exact (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0)
    (henergy : rowEnergy B=referenceFirstWeight n) :
    regularCovarianceDeficit n B=referenceScale n*
      (referenceScale n*((n:ℝ)+1)-operatorValue b (uniformMass n) (normalizedRowCovariance n b B)) := by
  have hv:=operatorValue_smul_square b (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
    (normalizedRowCovariance n b B) (normalizedRowCovariance_psd b B)
    (referenceScale n) (referenceScale_pos n).le
  rw [←rowCovariance_eq_scaled_normalized b B,
    rowCovariance_value b (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) B hB] at hv
  unfold regularCovarianceDeficit
  rw [henergy,hv,referenceFirstWeight_scale]
  ring

lemma radius_scalar_bound (α β x κ ξ : ℝ) (hα : 0<α) (hβ : 0<β) (hx : 0 ≤ x)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hβlo : α^2/2 ≤ β^2)
    (hdev : x^2-β^2=α^2*κ*ξ) : (x-β)^2 ≤ 2*α^2*ξ^2 := by
  have hfactor:(x^2-β^2)^2=(x-β)^2*(x+β)^2:=by ring
  have hmult:(x-β)^2*β^2 ≤ (x^2-β^2)^2:=by
    rw [hfactor]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [mul_nonneg hx hβ.le]
  have hk2:κ^2 ≤ 1:=by nlinarith
  have hbound:(x-β)^2*(α^2/2) ≤ α^4*ξ^2:=by
    have hh:=(mul_le_mul_of_nonneg_left hβlo (sq_nonneg (x-β))).trans hmult
    rw [hdev,mul_pow,mul_pow] at hh
    have hh2:=mul_le_mul_of_nonneg_left hk2 (show 0 ≤ α^4*ξ^2 by positivity)
    nlinarith
  nlinarith [sq_pos_of_pos hα]

theorem radialError_le_direction (hn : 0<n) (B : Fin (n+2)→FSC.Coord e) :
    radialError B (referenceRowRadius n) ≤ 2*(referenceScale n)^2*(∑i,(rowDirection n B i)^2) := by
  have ha:=referenceScale_pos n
  have hb:=referenceRowRadius_pos n
  have hk:=diagonalKappa_bounds hn
  have hκ:0<diagonalKappa n:=by linarith
  have hβ:(referenceRowRadius n)^2=(referenceScale n)^2*baseDiagonal n:=by
    simpa only [baseDiagonal,mul_div_assoc] using referenceRowRadius_sq n
  have hβlo:(referenceScale n)^2/2 ≤ (referenceRowRadius n)^2:=by
    rw [hβ]
    nlinarith [mul_le_mul_of_nonneg_left (baseDiagonal_bounds n).1 (sq_nonneg (referenceScale n))]
  have hdev (i:Fin (n+2)):‖B i‖^2-(referenceRowRadius n)^2=
      (referenceScale n)^2*diagonalKappa n*rowDirection n B i:=by
    rw [hβ]
    unfold rowDirection
    field_simp
  unfold radialError
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>radius_scalar_bound _ _ _ _ _ ha hb (norm_nonneg _)
    hκ.le hk.2 hβlo (hdev i)

end NegativeVotingNormalizedDiagonalDeviation
