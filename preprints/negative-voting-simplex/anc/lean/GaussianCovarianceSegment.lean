import GaussianCovariancePathRegularity
import GaussianProcrustesDistance

/-! A genuine smooth positive factor on an entire covariance segment, with
an actual inverse and a dimension-independent Hilbert--Schmidt velocity bound. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingCovarianceSegment
open NegativeVotingCovariancePath NegativeVotingProcrustes NegativeVotingPositiveCovariance
  NegativeVotingAffineNormControl NegativeVotingAffineLogMassBound NegativeVotingRayDeficit
variable {d : ℕ}

theorem factor_comp_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ (FSC.Coord d)) (ev : ι → ℝ) (t : ℝ)
    (ht : ∀ i,0 < 1+t*ev i) :
    (covarianceFactor e ev t).comp (factorDerivative e ev t)=(1/2:ℝ) • diagonal e ev := by
  rw [covarianceFactor,factorDerivative,diagonal_comp,←diagonal_smul]
  congr 1
  funext i
  have hs : 0 < Real.sqrt (1+t*ev i) := Real.sqrt_pos.mpr (ht i)
  field_simp

/-- The whole segment has a genuine positive symmetric square root. The
statement includes a neighborhood |t|<=2, so endpoint derivatives are ordinary
Fréchet derivatives, not only one-sided derivatives. -/
theorem exists_covariance_segment (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hH : H.toLinearMap.IsSymmetric) (hsize : ‖H‖ ≤ 1/8) :
    ∃ S V : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d,
      S 0=ContinuousLinearMap.id ℝ (FSC.Coord d) ∧
      (∀ t,S t∈psdCone) ∧
      ∀ t,|t| ≤ 2 →
        (S t).comp (S t)=ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H ∧
        HasDerivAt S (V t) t ∧ ContDiffAt ℝ 1 S t ∧
        ‖S t-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 2*‖H‖ ∧
        ∃ M : FSC.Coord d ≃L[ℝ] FSC.Coord d,
          M.toContinuousLinearMap=S t ∧ ‖M.symm.toContinuousLinearMap‖ ≤ 2 ∧
          V t=(1/2:ℝ) • M.symm.toContinuousLinearMap.comp H ∧
          operatorHilbertSchmidt (V t) ≤ operatorHilbertSchmidt H := by
  let e := hH.eigenvectorBasis (n:=Module.finrank ℝ (FSC.Coord d)) rfl
  let ev := hH.eigenvalues (n:=Module.finrank ℝ (FSC.Coord d)) rfl
  have heq : diagonal e ev=H := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change diagonal e ev (e i)=H (e i)
    rw [diagonal_basis]
    exact (hH.apply_eigenvectorBasis rfl i).symm
  have hev (i : Fin (Module.finrank ℝ (FSC.Coord d))) : |ev i| ≤ ‖H‖ := by
    have hh := H.le_opNorm (e i)
    have hi : H (e i)=ev i • e i := hH.apply_eigenvectorBasis rfl i
    rw [hi,norm_smul,Real.norm_eq_abs,e.orthonormal.norm_eq_one i,mul_one,mul_one] at hh
    exact hh
  let S := covarianceFactor e ev
  let V := factorDerivative e ev
  have hpsd (t : ℝ) : S t∈psdCone := by
    refine ⟨diagonal_symmetric e _,fun x=>?_⟩
    simpa only [real_inner_comm] using covarianceFactor_nonnegative e ev t x
  refine ⟨S,V,covarianceFactor_zero e ev,hpsd,?_⟩
  intro t ht
  have hcoeff (i : Fin (Module.finrank ℝ (FSC.Coord d))) : 0 < 1+t*ev i := by
    have hm := mul_le_mul ht (hev i) (abs_nonneg (ev i)) (by norm_num : (0:ℝ) ≤ 2)
    rw [←abs_mul] at hm
    have hn := neg_abs_le (t*ev i)
    nlinarith
  have hsq : (S t).comp (S t)=ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H := by
    simpa only [S,heq] using factor_square e ev t (fun i=>(hcoeff i).le)
  have hclose : ‖S t-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 2*‖H‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    have hh := psd_sqrt_pointwise_distance (S t) (hpsd t) x
    change ‖(S t-ContinuousLinearMap.id ℝ (FSC.Coord d)) x‖ ≤
      ‖((S t).comp (S t)-ContinuousLinearMap.id ℝ (FSC.Coord d)) x‖ at hh
    rw [hsq,add_sub_cancel_left] at hh
    have hb := (t • H).le_opNorm x
    rw [norm_smul,Real.norm_eq_abs] at hb
    have ht' := mul_le_mul_of_nonneg_right ht (norm_nonneg H)
    exact hh.trans (hb.trans (mul_le_mul_of_nonneg_right ht' (norm_nonneg x)))
  have hnear : ‖S t-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 1/2 := by linarith
  let M := nearIdentityEquiv (S t-ContinuousLinearMap.id ℝ (FSC.Coord d)) hnear 1 (by norm_num)
  have hM : M.toContinuousLinearMap=S t := by
    dsimp only [M]
    rw [nearIdentityEquiv_coe]
    unfold nearIdentityMap
    module
  have hMi : ‖M.symm.toContinuousLinearMap‖ ≤ 2 :=
    nearIdentity_inverse_norm_le _ hnear 1 (by norm_num)
  have hcomp : (S t).comp (V t)=(1/2:ℝ) • H := by
    simpa only [S,V,heq] using factor_comp_derivative e ev t hcoeff
  have hV : V t=(1/2:ℝ) • M.symm.toContinuousLinearMap.comp H := by
    apply ContinuousLinearMap.ext
    intro x
    apply M.injective
    have hh := congrArg (fun A : FSC.Coord d →L[ℝ] FSC.Coord d=>A x) hcomp
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply] at hh ⊢
    rw [ContinuousLinearEquiv.coe_coe,map_smul,M.apply_symm_apply]
    simpa only [←hM,ContinuousLinearEquiv.coe_coe] using hh
  have hHS : operatorHilbertSchmidt (V t) ≤ operatorHilbertSchmidt H := by
    rw [hV,operatorHilbertSchmidt_smul]
    have hh := (operatorHilbertSchmidt_comp_le M.symm.toContinuousLinearMap H).trans
      (mul_le_mul_of_nonneg_right hMi (operatorHilbertSchmidt_nonneg H))
    norm_num
    linarith
  exact ⟨hsq,hasDerivAt_covarianceFactor e ev t hcoeff,
    (NegativeVotingCovariancePath.contDiffAt_covarianceFactor e ev t hcoeff).of_le (by simp),hclose,M,hM,hMi,hV,hHS⟩

end NegativeVotingCovarianceSegment
