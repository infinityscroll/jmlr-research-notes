import GaussianCovarianceDeficitRectangle

/-! Transport of positive covariance-factor distances to the actual selected
Gaussian second-energy rectangle. The result retains the product of the two
covariance errors and has no additive tail or desired energy-bound premise. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingCovarianceEnergyRectangle
open NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanQuadraticMoments
  NegativeVotingNearRegularEnergyRectangle NegativeVotingNearRegularEnergyComparison
  NegativeVotingCovarianceFactorDistance NegativeVotingCovarianceDeficitRectangle
  NegativeVotingProcrustes NegativeVotingRayDeficit NegativeVotingOperatorHS
  NegativeVotingPositiveCovariance NegativeVotingCapTail NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound
variable {n d : ℕ}

def factorEnergy (b : Fin (n+2)→FSC.Coord d) (α : ℝ)
    (S : FSC.Coord d→L[ℝ]FSC.Coord d) : ℝ :=
  let B:=fun i=>α•S (b i)
  secondEnergy B (selectedOffsets B (fun _=>(n+2:ℕ)⁻¹))

theorem rowSq_operator (b : Fin (n+2)→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (α : ℝ) :
    rowSq (fun i=>α•H (b i))=α^2*(operatorHilbertSchmidt H)^2 := by
  rw [parseval_operator_HilbertSchmidt_sq b hP]
  simp only [rowSq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Finset.mul_sum]

/-- An actual energy comparison for two covariance factors. The row-size
premises are operator distances, which the next theorem derives from the
two specified positive covariances. -/
theorem factorEnergy_rectangle_le (hn : 1 ≤ n)
    (b : Fin (n+2)→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (S T : FSC.Coord d→L[ℝ]FSC.Coord d)
    (a c α e : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hα : 0<α) (he : 0<e)
    (hT : operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ a)
    (hST : operatorHilbertSchmidt (S-T) ≤ c)
    (hsmall : a^2+c^2 ≤ 1/1024)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2) :
    |factorEnergy b α S-factorEnergy b α T| ≤
      energyComparisonCoefficient n α e (4*α^2*(a^2+c^2))*α^2*(c^2+6*a*c) := by
  let X:=fun i=>α•((T-ContinuousLinearMap.id ℝ (FSC.Coord d)) (b i))
  let V:=fun i=>α•((S-T) (b i))
  have hx : rowSq X ≤ α^2*a^2 := by
    rw [rowSq_operator b hP]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (operatorHilbertSchmidt_nonneg _) hT 2) (sq_nonneg _)
  have hv : rowSq V ≤ α^2*c^2 := by
    rw [rowSq_operator b hP]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (operatorHilbertSchmidt_nonneg _) hST 2) (sq_nonneg _)
  have hF : 4*α^2*(a^2+c^2) ≤ α^2/256:=by
    have hh:=mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4*α^2 by positivity)
    nlinarith only [hh]
  have hball : 4*(rowSq X+rowSq V) ≤ 4*α^2*(a^2+c^2):=by nlinarith only [hx,hv]
  have hh:=actual_rectangle_abs_le_of_rowSq hn b X V hG α e
    (4*α^2*(a^2+c^2)) hα he hF hscale hball
  have heT : α•b+X=(fun i=>α•T (b i)):=by
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,X,sub_apply,ContinuousLinearMap.id_apply]
    module
  have heS : α•b+(X+V)=(fun i=>α•S (b i)):=by
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,X,V,sub_apply,ContinuousLinearMap.id_apply]
    module
  simp only [energy,heT,heS] at hh
  change |factorEnergy b α S-factorEnergy b α T| ≤ _ at hh
  have hsx : Real.sqrt (rowSq X) ≤ α*a:=
    Real.sqrt_le_iff.mpr ⟨mul_nonneg hα.le ha,by nlinarith only [hx]⟩
  have hsv : Real.sqrt (rowSq V) ≤ α*c:=
    Real.sqrt_le_iff.mpr ⟨mul_nonneg hα.le hc,by nlinarith only [hv]⟩
  have hprod:=mul_le_mul hsx hsv (Real.sqrt_nonneg _) (mul_nonneg hα.le ha)
  have hbr : rowSq V+6*Real.sqrt (rowSq X)*Real.sqrt (rowSq V) ≤ α^2*(c^2+6*a*c):=by
    nlinarith only [hv,hprod]
  exact hh.trans ((mul_le_mul_of_nonneg_left hbr
    (energyComparisonCoefficient_nonneg n α e _ hα he)).trans_eq (by ring))

/-- Simultaneous positive factors for the original and projected covariance,
with the actual selected-fan second-energy comparison. All factor-distance
and local path hypotheses have been discharged from the covariance errors. -/
theorem exists_factors_actual_energy_rectangle (hn : 1 ≤ n)
    (b : Fin (n+2)→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (X V : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hX : X.toLinearMap.IsSymmetric) (hV : V.toLinearMap.IsSymmetric)
    (hsmall : (operatorHilbertSchmidt X)^2+(operatorHilbertSchmidt V)^2 ≤ 1/1024)
    (α e : ℝ) (hα : 0<α) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2) :
    ∃ S T : FSC.Coord d≃L[ℝ]FSC.Coord d,
      S.toContinuousLinearMap∈psdCone ∧ T.toContinuousLinearMap∈psdCone ∧
      S.toContinuousLinearMap.comp S.toContinuousLinearMap=
        ContinuousLinearMap.id ℝ (FSC.Coord d)+(X+V) ∧
      T.toContinuousLinearMap.comp T.toContinuousLinearMap=
        ContinuousLinearMap.id ℝ (FSC.Coord d)+X ∧
      |factorEnergy b α S.toContinuousLinearMap-factorEnergy b α T.toContinuousLinearMap| ≤
        energyComparisonCoefficient n α e
          (4*α^2*((operatorHilbertSchmidt X)^2+(operatorHilbertSchmidt V)^2))*α^2*
          ((operatorHilbertSchmidt V)^2+6*operatorHilbertSchmidt X*operatorHilbertSchmidt V) := by
  have hx0:=operatorHilbertSchmidt_nonneg X
  have hv0:=operatorHilbertSchmidt_nonneg V
  have hx : operatorHilbertSchmidt X ≤ 1/32:=by nlinarith [sq_nonneg (operatorHilbertSchmidt V)]
  have hv : operatorHilbertSchmidt V ≤ 1/32:=by nlinarith [sq_nonneg (operatorHilbertSchmidt X)]
  have htotal : operatorHilbertSchmidt (X+V) ≤ 1/8:=
    (operatorHilbertSchmidt_add_le X V).trans (by linarith)
  obtain ⟨S,hS,hSi,hSS,_,hnearS,hSpos⟩:=exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+(X+V))
    (identity_positive.1.add (hX.add hV)) (by simpa only [add_sub_cancel_left] using htotal)
  obtain ⟨T,hT,hTi,hTT,_,hnearT,hTpos⟩:=exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+X)
    (identity_positive.1.add hX) (by simpa only [add_sub_cancel_left] using hx.trans (by norm_num))
  have hdist:=positive_half_factor_distance S.toContinuousLinearMap T.toContinuousLinearMap
    hS.1 hT.1 hSpos hTpos
  rw [hSS,hTT] at hdist
  have hd : (ContinuousLinearMap.id ℝ (FSC.Coord d)+(X+V))-
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+X)=V:=by abel
  rw [hd] at hdist
  simp only [add_sub_cancel_left] at hnearT
  exact ⟨S,T,hS,hT,hSS,hTT,factorEnergy_rectangle_le hn b hP hG _ _
    _ _ α e hx0 hv0 hα he hnearT hdist hsmall hscale⟩

end NegativeVotingCovarianceEnergyRectangle
