import GaussianCovarianceMaximumUniqueness

/-! The actual regular-reference covariance deficit and its complete zero case,
including arbitrary rectangular row realizations and singular covariances. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularCovarianceDeficit
open NegativeVoting NegativeVotingCenteredParseval NegativeVotingCovarianceRealization
  NegativeVotingBalancedReference NegativeVotingBalancedMaximum
  NegativeVotingCovarianceMaximumUniqueness NegativeVotingCovarianceStrict
  NegativeVotingFanCovarianceValue NegativeVotingFanValue NegativeVotingPositiveCovariance
  NegativeVotingCentroidOptimization NegativeVotingGaussianMaximumMean
  NegativeVotingAssignmentDuality
variable {n d e : ℕ}

def regularCovarianceDeficit (n : ℕ) (B : Fin (n+2) → FSC.Coord e) : ℝ :=
  (referenceFirstWeight n+rowEnergy B)/2-optimizedValue B (uniformMass n)

theorem rowEnergy_eq_of_gram (B : Fin (n+2) → FSC.Coord d)
    (C : Fin (n+2) → FSC.Coord e) (hG : Matrix.gram ℝ B=Matrix.gram ℝ C) :
    rowEnergy B=rowEnergy C := by
  apply Finset.sum_congr rfl
  intro i _
  have hh := congrFun (congrFun hG i) i
  simpa only [Matrix.gram_apply,real_inner_self_eq_norm_sq] using hh

theorem regularCovarianceDeficit_eq_of_gram (B : Fin (n+2) → FSC.Coord d)
    (C : Fin (n+2) → FSC.Coord e) (hG : Matrix.gram ℝ B=Matrix.gram ℝ C) :
    regularCovarianceDeficit n B=regularCovarianceDeficit n C := by
  unfold regularCovarianceDeficit
  rw [rowEnergy_eq_of_gram B C hG,optimizedValue_eq_of_gram B C (fun i j=>congrFun (congrFun hG i) j) (uniformMass n)]

theorem rowCovariance_gram (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2) → FSC.Coord e) (hB : (∑ i,B i)=0) :
    gramVelocity b (rowCovariance b B)=Matrix.gram ℝ B := by
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  rw [rowCovariance,adjoint_factor_gram]
  simp_rw [reconstruction_row b B hG' hB]

theorem regularCovarianceDeficit_eq_covariance_gap
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin (n+2) → FSC.Coord e) (hB : (∑ i,B i)=0) :
    regularCovarianceDeficit n B=
      (referenceFirstWeight n-penalizedValue b (uniformMass n) (rowCovariance b B))/2 := by
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  rw [rowCovariance_objective b hG' hP B hB]
  unfold regularCovarianceDeficit rowObjective
  ring

theorem reference_scaled_energy
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) :
    rowEnergy (fun i=>referenceScale n • b i)=referenceFirstWeight n := by
  have ht := reference_covariance_trace b hG hP
  rw [←scalar_factor_square n d,parseval_square_trace b hP] at ht
  exact ht

theorem reference_scaled_value
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    optimizedValue (fun i=>referenceScale n • b i) (uniformMass n)=referenceFirstWeight n := by
  have hv := reference_covariance_value b hG
  rw [←scalar_factor_square n d,operatorValue_factor] at hv
  exact hv

theorem reference_scaled_deficit_zero
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) :
    regularCovarianceDeficit n (fun i=>referenceScale n • b i)=0 := by
  rw [regularCovarianceDeficit,reference_scaled_energy b hG hP,reference_scaled_value b hG]
  ring

/-- Nonnegativity uses the actual balanced Gaussian optimization theorem,
not a supplied covariance-maximum hypothesis. -/
theorem regularCovarianceDeficit_nonneg (hn : 0<n)
    (B : Fin (n+2) → FSC.Coord e) (hB : (∑ i,B i)=0) :
    0 ≤ regularCovarianceDeficit n B := by
  let b := centeredParsevalBasis (n+2) (by omega)
  have hb := centeredParsevalBasis_spec (n+2) (by omega)
  have hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hb.2.1
  rw [regularCovarianceDeficit_eq_covariance_gap b hG hb.2.2 B hB]
  exact div_nonneg (sub_nonneg.mpr (balanced_covariance_value_le hn b hG hb.2.2 _
    (rowCovariance_psd b B))) (by norm_num)

/-- A zero deficit is equivalent to the exact scaled regular Gram matrix,
in every ambient dimension; rank loss is included in the forward implication. -/
theorem regularCovarianceDeficit_zero_iff (hn : 0<n)
    (B : Fin (n+2) → FSC.Coord e) (hB : (∑ i,B i)=0) :
    regularCovarianceDeficit n B=0 ↔ ∀ i j,inner ℝ (B i) (B j)=
      (referenceScale n)^2*((if i=j then 1 else 0)-1/((n:ℝ)+2)) := by
  let b := centeredParsevalBasis (n+2) (by omega)
  have hb := centeredParsevalBasis_spec (n+2) (by omega)
  have hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hb.2.1
  constructor
  · intro hz
    have hv := regularCovarianceDeficit_eq_covariance_gap b hG hb.2.2 B hB
    have heq : penalizedValue b (uniformMass n) (rowCovariance b B)=referenceFirstWeight n := by
      linarith
    have hC := balanced_reference_unique hn b hG hb.2.2 (rowCovariance b B)
      (rowCovariance_psd b B) heq
    have he := rowCovariance_gram b hG B hB
    rw [hC] at he
    intro i j
    have hh := (congrFun (congrFun he i) j).symm
    change inner ℝ (B i) (B j)=inner ℝ (b i) ((referenceScale n)^2 • b j) at hh
    simpa only [real_inner_smul_right,hG] using hh
  · intro hreg
    have he : Matrix.gram ℝ B=Matrix.gram ℝ (fun i=>referenceScale n • b i) := by
      ext i j
      change inner ℝ (B i) (B j)=inner ℝ (referenceScale n • b i) (referenceScale n • b j)
      rw [hreg,real_inner_smul_left,real_inner_smul_right,hG]
      ring
    rw [regularCovarianceDeficit_eq_of_gram B _ he,reference_scaled_deficit_zero b hG hb.2.2]

theorem regularCovarianceDeficit_pos_iff (hn : 0<n)
    (B : Fin (n+2) → FSC.Coord e) (hB : (∑ i,B i)=0) :
    0 < regularCovarianceDeficit n B ↔ ∃ i j,inner ℝ (B i) (B j)≠
      (referenceScale n)^2*((if i=j then 1 else 0)-1/((n:ℝ)+2)) := by
  have h0 := regularCovarianceDeficit_nonneg hn B hB
  have he : (0 < regularCovarianceDeficit n B) ↔ regularCovarianceDeficit n B≠0 := by
    constructor
    · exact fun hh=>ne_of_gt hh
    · exact fun hh=>lt_of_le_of_ne h0 (Ne.symm hh)
  rw [he,ne_eq,regularCovarianceDeficit_zero_iff hn B hB]
  simp only [not_forall]

theorem centroid_regular_deficit_nonneg (hn : 0<n)
    (p : Fin (n+2) → ℝ) (f : FSC.Coord e → Fin (n+2) → ℝ) (hf : Feasible p f) :
    0 ≤ regularCovarianceDeficit n (centroidRows f) :=
  regularCovarianceDeficit_nonneg hn _ (centroidRows_sum_zero p f hf)

theorem centroid_regular_deficit_zero_iff (hn : 0<n)
    (p : Fin (n+2) → ℝ) (f : FSC.Coord e → Fin (n+2) → ℝ) (hf : Feasible p f) :
    regularCovarianceDeficit n (centroidRows f)=0 ↔ ∀ i j,
      inner ℝ (centroidRows f i) (centroidRows f j)=
        (referenceScale n)^2*((if i=j then 1 else 0)-1/((n:ℝ)+2)) :=
  regularCovarianceDeficit_zero_iff hn _ (centroidRows_sum_zero p f hf)

end NegativeVotingRegularCovarianceDeficit
