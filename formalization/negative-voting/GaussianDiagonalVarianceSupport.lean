import GaussianDiagonalSupportAlgebra
import GaussianRegularHazardDerivative

/-! The actual diagonal covariance support along the selected variance path,
with the exact remaining summed Taylor premise displayed. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingDiagonalVarianceSupport
open NegativeVotingDiagonalFrameRealization NegativeVotingDiagonalSupportAlgebra
  NegativeVotingRegularHazardDerivative NegativeVotingRegularTieVariance
  NegativeVotingCovarianceConcavity NegativeVotingPositiveCovariance
  NegativeVotingBalancedReference NegativeVotingDiagonalIntegratedLaplacian
variable {m d : ℕ} [NeZero m]

lemma frameOperator_diagonal_entry (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (v : Fin m→ℝ) (i : Fin m) :
    inner ℝ (b i) (frameOperator b v (b i))=v i*(1-2/(m:ℝ))+(∑k,v k)/(m:ℝ)^2 := by
  rw [frameOperator_pairing]
  have he (k:Fin m):v k*inner ℝ (b k) (b i)*inner ℝ (b k) (b i)=
      (if k=i then v i*(1-2/(m:ℝ)) else 0)+v k/(m:ℝ)^2:=by
    rw [hG]
    by_cases hki:k=i
    · subst k;simp only [ite_true];field_simp;ring
    · simp only [hki,ite_false];field_simp;ring
  simp_rw [he,Finset.sum_add_distrib,←Finset.sum_div]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem frameOperator_variance_diagonal (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (ξ : Fin m→ℝ) (hξ : ∑i,ξ i=0) (t : ℝ) (i : Fin m) :
    inner ℝ (b i) (frameOperator b (fun k=>1+t*ξ k) (b i))=
      1-1/(m:ℝ)+t*(1-2/(m:ℝ))*ξ i := by
  rw [frameOperator_diagonal_entry b hG]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,hξ,mul_zero,add_zero,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp
  ring

variable {n : ℕ}

/-- Every covariance and Gaussian integral here is literal. The sole analytic
error premise is the summed coefficient Taylor remainder, which is kept
explicit rather than identifying this conditional bound with row coercivity. -/
theorem actual_support_gap_of_summed_remainder (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈psdCone)
    (ξ : Fin (n+2)→ℝ) (hξ : ∑i,ξ i=0) (t U E : ℝ) (ht : 0 ≤ t) (hU : 0 ≤ U)
    (hvar : ∀i,0<1+t*ξ i)
    (hdiag : ∀i,inner ℝ (b i) (C (b i))=1-1/((n:ℝ)+2)+(1-2/((n:ℝ)+2))*ξ i)
    (hW : ∀i,|diagonalSupportWeight (1-1/((n:ℝ)+2)) (1-2/((n:ℝ)+2)) t ξ i| ≤ U)
    (he : (∑i,|hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i-
      (referenceScale n-referenceScale n*eta n*t*ξ i)|) ≤
      E*referenceScale n*t^2*(∑i,(ξ i)^2))
    (hsmall : U*E*t ≤ 1/24) :
    referenceScale n*t/48*(∑i,(ξ i)^2) ≤
      referenceScale n*((n:ℝ)+1)-operatorValue b (uniformMass n) C := by
  let e:Fin (n+2)→ℝ:=fun i=>hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i-
    (referenceScale n-referenceScale n*eta n*t*ξ i)
  have hσ:∀i,0<varianceStdPath ξ t i:=fun i=>Real.sqrt_pos.mpr (hvar i)
  have hbase:=covariance_le_diagonal_support b hP
    (by intro i j; simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hG i j) (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
    (varianceStdPath ξ t) hσ C hC
  have hsq: (fun k=>(varianceStdPath ξ t k)^2)=(fun k=>1+t*ξ k):=by
    funext k
    exact Real.sq_sqrt (hvar k).le
  rw [hsq] at hbase
  have hD:=frameOperator_variance_diagonal b
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) ξ hξ t
  have hsup:operatorValue b (uniformMass n) C ≤ (1/2:ℝ)*∑i,
      (referenceScale n-referenceScale n*eta n*t*ξ i+e i)*
        diagonalSupportWeight (1-1/((n:ℝ)+2)) (1-2/((n:ℝ)+2)) t ξ i := by
    refine hbase.trans_eq ?_
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hdiag,hD]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    have hmEq:uniformMass n=(fun _:Fin (n+2)=>((n:ℝ)+2)⁻¹):=by
      funext k;simp [uniformMass,one_div]
    rw [hmEq]
    change hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i*_ = (_+e i)*_
    dsimp only [e,diagonalSupportWeight]
    ring
  have hk:(1/3:ℝ) ≤ 1-2/((n:ℝ)+2):=by
    have hn':(1:ℝ) ≤ n:=by exact_mod_cast hn
    have hd:(0:ℝ)<(n:ℝ)+2:=by positivity
    have hh:(2:ℝ)/((n:ℝ)+2) ≤ 2/3:=div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hout:=covariance_gap_of_support_remainder (referenceScale n) (eta n)
    (1-1/((n:ℝ)+2)) (1-2/((n:ℝ)+2)) t U E (operatorValue b (uniformMass n) C)
    ξ e hξ (referenceScale_pos n).le (eta_bounds n hn).1 hk ht hU hW he hsmall hsup
  have hm:(1-1/((n:ℝ)+2))*(Fintype.card (Fin (n+2)):ℝ)=(n:ℝ)+1:=by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
    field_simp
    ring
  simpa only [mul_assoc,hm] using hout

end NegativeVotingDiagonalVarianceSupport
