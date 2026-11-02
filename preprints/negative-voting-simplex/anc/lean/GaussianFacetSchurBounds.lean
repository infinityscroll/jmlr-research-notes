import GaussianFacetNormalExtension
import GaussianOperatorHSNorm

/-! Dimension-free perturbation estimates for the literal conditional mean
and positive normal extension of a transported Gaussian facet. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open scoped RealInnerProductSpace
namespace NegativeVotingFacetConditionalPlane
open NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl
  NegativeVotingOperatorHS InnerProductSpace
variable {d : ℕ}

def covarianceError (S : Ambient d ≃L[ℝ] Ambient d) : Ambient d →L[ℝ] Ambient d :=
  covariance S-ContinuousLinearMap.id ℝ (Ambient d)

def normalError (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) : Ambient d :=
  covarianceError S n

@[simp] theorem normalError_eq (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) :
    normalError S n=covariance S n-n := rfl

theorem covariance_normal_eq (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) :
    covariance S n=n+normalError S n := by rw [normalError_eq];abel

theorem normalError_norm_le (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) : ‖normalError S n‖ ≤ ‖covarianceError S‖ := by
  simpa only [normalError,hn,mul_one] using (covarianceError S).le_opNorm n

theorem normalVariance_sub_one (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) :
    normalVariance S n-1=inner ℝ n (normalError S n) := by
  rw [normalVariance,covariance_normal_eq,inner_add_right,real_inner_self_eq_norm_sq,hn]
  ring

theorem normalVariance_sub_one_abs_le (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) :
    |normalVariance S n-1| ≤ ‖normalError S n‖ := by
  rw [normalVariance_sub_one S n hn]
  simpa only [hn,one_mul] using abs_real_inner_le_norm n (normalError S n)

theorem normalVariance_near_bounds (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    1/2 ≤ normalVariance S n ∧ normalVariance S n ≤ 3/2 := by
  have hh := (normalVariance_sub_one_abs_le S n hn).trans
    ((normalError_norm_le S n hn).trans hE)
  exact ⟨by have hl := (abs_le.mp hh).1;linarith,
    by have hu := (abs_le.mp hh).2;linarith⟩

theorem normalVariance_inv_le_two (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    (normalVariance S n)⁻¹ ≤ 2 := by
  have hv := (normalVariance_near_bounds S n hn hE).1
  have hp : 0 < normalVariance S n := by linarith
  simpa only [one_div] using (one_div_le hp (by norm_num : (0:ℝ)<2)).2 hv

theorem covariance_normal_norm_le (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    ‖covariance S n‖ ≤ 3/2 := by
  rw [covariance_normal_eq]
  have hh := norm_add_le n (normalError S n)
  have he := (normalError_norm_le S n hn).trans hE
  rw [hn] at hh
  linarith

theorem normalVariance_inverse_difference (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    |1-(normalVariance S n)⁻¹| ≤ 2*‖normalError S n‖ := by
  have hp : 0 < normalVariance S n := by
    have hh := (normalVariance_near_bounds S n hn hE).1;linarith
  have he : 1-(normalVariance S n)⁻¹=
      (normalVariance S n-1)/normalVariance S n := by field_simp
  rw [he,abs_div,abs_of_pos hp]
  calc
    |normalVariance S n-1|/normalVariance S n ≤
        ‖normalError S n‖/normalVariance S n :=
      div_le_div_of_nonneg_right (normalVariance_sub_one_abs_le S n hn) hp.le
    _=(normalVariance S n)⁻¹*‖normalError S n‖ := by ring
    _ ≤ 2*‖normalError S n‖ :=
      mul_le_mul_of_nonneg_right (normalVariance_inv_le_two S n hn hE) (norm_nonneg _)

theorem conditionalMean_norm_le (S : Ambient d ≃L[ℝ] Ambient d)
    (n h : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    ‖conditionalMean S n h‖ ≤ 4*‖h‖ := by
  have hp : 0 < normalVariance S n := by
    have hh := (normalVariance_near_bounds S n hn hE).1;linarith
  have hi : |inner ℝ n h| ≤ ‖h‖ := by simpa only [hn,one_mul] using abs_real_inner_le_norm n h
  have hc : |inner ℝ n h/normalVariance S n| ≤ 2*‖h‖ := by
    rw [abs_div,abs_of_pos hp,div_eq_mul_inv]
    calc
      |inner ℝ n h| *(normalVariance S n)⁻¹ ≤ ‖h‖*2 :=
        mul_le_mul hi (normalVariance_inv_le_two S n hn hE) (inv_nonneg.mpr hp.le) (norm_nonneg _)
      _=2*‖h‖ := by ring
  calc
    ‖conditionalMean S n h‖ ≤ ‖h‖+|inner ℝ n h/normalVariance S n| *‖covariance S n‖ := by
      simpa only [conditionalMean,norm_smul,Real.norm_eq_abs] using
        norm_sub_le h ((inner ℝ n h/normalVariance S n) • covariance S n)
    _ ≤ ‖h‖+(2*‖h‖)*(3/2) := add_le_add le_rfl
      (mul_le_mul hc (covariance_normal_norm_le S n hn hE) (norm_nonneg _) (by positivity))
    _=4*‖h‖ := by ring

/-- A literal three-rank-one expansion; no matrix factorization is assumed. -/
theorem extendedCovariance_error_expansion (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) :
    extendedCovariance S n-ContinuousLinearMap.id ℝ (Ambient d)=
      covarianceError S+
        rankOne ℝ ((1-(normalVariance S n)⁻¹) • n) n-
        rankOne ℝ ((normalVariance S n)⁻¹ • normalError S n) (covariance S n)-
        rankOne ℝ ((normalVariance S n)⁻¹ • n) (normalError S n) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [extendedCovariance,schurCovariance,covarianceError,normalError_eq,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,rankOne_def,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,inner_sub_left]
  module

theorem extendedCovariance_HilbertSchmidt_le (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    operatorHilbertSchmidt (extendedCovariance S n-ContinuousLinearMap.id ℝ (Ambient d)) ≤
      8*operatorHilbertSchmidt (covarianceError S) := by
  have hp : 0 < normalVariance S n := by
    have hh := (normalVariance_near_bounds S n hn hE).1;linarith
  let T1 := rankOne ℝ ((1-(normalVariance S n)⁻¹) • n) n
  let T2 := rankOne ℝ ((normalVariance S n)⁻¹ • normalError S n) (covariance S n)
  let T3 := rankOne ℝ ((normalVariance S n)⁻¹ • n) (normalError S n)
  have h1 : operatorHilbertSchmidt T1 ≤ 2*‖normalError S n‖ := by
    simpa only [T1,operatorHilbertSchmidt_rankOne,norm_smul,Real.norm_eq_abs,hn,mul_one] using
      normalVariance_inverse_difference S n hn hE
  have h2 : operatorHilbertSchmidt T2 ≤ 3*‖normalError S n‖ := by
    dsimp only [T2]
    rw [operatorHilbertSchmidt_rankOne,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    calc
      (normalVariance S n)⁻¹*‖normalError S n‖*‖covariance S n‖ ≤
          (2*‖normalError S n‖)*(3/2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (normalVariance_inv_le_two S n hn hE)
          (norm_nonneg _)) (covariance_normal_norm_le S n hn hE) (norm_nonneg _) (by positivity)
      _=3*‖normalError S n‖ := by ring
  have h3 : operatorHilbertSchmidt T3 ≤ 2*‖normalError S n‖ := by
    dsimp only [T3]
    rw [operatorHilbertSchmidt_rankOne,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp),hn,mul_one]
    exact mul_le_mul_of_nonneg_right (normalVariance_inv_le_two S n hn hE) (norm_nonneg _)
  rw [extendedCovariance_error_expansion]
  change operatorHilbertSchmidt (covarianceError S+T1-T2-T3) ≤ _
  calc
    _ ≤ operatorHilbertSchmidt (covarianceError S+T1-T2)+operatorHilbertSchmidt T3 :=
      operatorHilbertSchmidt_sub_le _ _
    _ ≤ operatorHilbertSchmidt (covarianceError S+T1)+operatorHilbertSchmidt T2+
        operatorHilbertSchmidt T3 := add_le_add (operatorHilbertSchmidt_sub_le _ _) le_rfl
    _ ≤ operatorHilbertSchmidt (covarianceError S)+operatorHilbertSchmidt T1+
        operatorHilbertSchmidt T2+operatorHilbertSchmidt T3 :=
      add_le_add (add_le_add (operatorHilbertSchmidt_add_le _ _) le_rfl) le_rfl
    _ ≤ operatorHilbertSchmidt (covarianceError S)+7*‖normalError S n‖ := by linarith
    _ ≤ 8*operatorHilbertSchmidt (covarianceError S) := by
      have hh := (normalError_norm_le S n hn).trans (operator_norm_le_HilbertSchmidt _)
      linarith

end NegativeVotingFacetConditionalPlane
