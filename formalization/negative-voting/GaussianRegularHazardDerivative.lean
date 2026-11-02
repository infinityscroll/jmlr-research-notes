import GaussianHazardKernelPathDerivative
import GaussianRegularHazardCoefficient

/-! The actual selected balanced variance path has the exact regular
all-label hazard coefficient derivative. The analytic diagonal remains in
ell, and actual fixed-Gaussian domination justifies the integral derivative. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators ENNReal Classical Topology
namespace NegativeVotingRegularHazardDerivative
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalBalancedDerivative NegativeVotingHazardKernelDifferentiation
  NegativeVotingHazardKernelPathDerivative NegativeVotingRegularTieLaw
  NegativeVotingRegularTieVariance NegativeVotingRegularDiagonalBalance
  NegativeVotingRegularHazardCoefficient NegativeVotingFanSelectedOffsets
  NegativeVotingFanJacobian NegativeVotingDiagonalHazardQuadraticForm
  NegativeVotingBalancedReference
variable {n : ℕ}

theorem regular_standardized (n : ℕ) (i j : Fin (n+2)) (y : ℝ) :
    standardized (fun _=>1) (fun _=>0) i j y=y := by simp [standardized]

theorem regular_winnerKernel (n : ℕ) (i : Fin (n+2)) (y : ℝ) :
    winnerKernel (fun _=>1) (fun _=>0) i y=normalCDF y^(n+1) := by
  simp [winnerKernel,regular_standardized,Finset.card_erase_of_mem]

theorem regular_slope (n : ℕ) (ξ : Fin (n+2)→ℝ) (i j : Fin (n+2)) (y : ℝ) :
    linearSlope (fun _=>1) (fun _=>0) (fun k=>ξ k/2) (fun k=>-tieMean n*(ξ k/2)) i j 0*y+
      constantSlope (fun _=>1) (fun _=>0) (fun k=>ξ k/2) (fun k=>-tieMean n*(ξ k/2)) i j 0=
      (ξ i-ξ j)/2*(y-tieMean n) := by
  simp only [linearSlope,constantSlope,parameterLine_zero,one_pow,div_one,mul_one,zero_sub,sub_zero,zero_mul]
  ring

theorem regular_winnerKernelDerivative (n : ℕ) (ξ : Fin (n+2)→ℝ) (hξ : ∑k,ξ k=0)
    (i : Fin (n+2)) (y : ℝ) :
    winnerKernelDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2) (fun k=>-tieMean n*(ξ k/2)) i 0 y=
      normalCDF y^n*normalPDF y*(((n:ℝ)+2)*ξ i/2)*(y-tieMean n) := by
  unfold winnerKernelDerivative
  simp only [parameterLine_zero,regular_standardized,regular_slope]
  have he (j:Fin (n+2)) (hj:j∈Finset.univ.erase i) :
      (∏k∈(Finset.univ.erase i).erase j,normalCDF y)=normalCDF y^n:=by
    simp only [Finset.prod_const,Finset.card_erase_of_mem hj,
      Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
    congr 1
  have hsum : (∑j∈Finset.univ.erase i,(∏k∈(Finset.univ.erase i).erase j,normalCDF y)*normalPDF y*((ξ i-ξ j)/2*(y-tieMean n)))=
      ∑j∈Finset.univ.erase i,normalCDF y^n*normalPDF y*((ξ i-ξ j)/2*(y-tieMean n)):=by
    apply Finset.sum_congr rfl
    intro j hj
    rw [he j hj]
  rw [hsum]
  have ht (j:Fin (n+2)) : normalCDF y^n*normalPDF y*((ξ i-ξ j)/2*(y-tieMean n))=
      (normalCDF y^n*normalPDF y*(y-tieMean n)/2)*(ξ i-ξ j):=by ring
  simp_rw [ht]
  rw [←Finset.mul_sum]
  have hs : (∑j∈Finset.univ.erase i,(ξ i-ξ j))=((n:ℝ)+2)*ξ i:=by
    have hall : (∑j∈Finset.univ.erase i,(ξ i-ξ j))=∑j,(ξ i-ξ j):=by
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)];simp
    rw [hall,Finset.sum_sub_distrib,hξ,sub_zero]
    simp [Nat.cast_add,Nat.cast_ofNat]
  rw [hs]
  ring

theorem regular_pairKernelDerivative_density (n : ℕ) (ξ : Fin (n+2)→ℝ) (hξ : ∑k,ξ k=0)
    (i j : Fin (n+2)) (y : ℝ) :
    normalPDF y*pairKernelDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
      (fun k=>-tieMean n*(ξ k/2)) i j y=
      tieWeight n y*((((n:ℝ)+2)*r y*ξ i-H y*(ξ i-ξ j))*(y-tieMean n)/2-ξ j/2) := by
  rw [pairKernelDerivative,regular_winnerKernelDerivative n ξ hξ,regular_winnerKernel,
    regular_standardized,regular_slope]
  simp only [div_one,one_pow]
  unfold tieWeight r H
  rw [pow_succ]
  field_simp [(normalCDF_pos y).ne']
  ring

theorem regular_rowKernelDerivative_density (n : ℕ) (ξ : Fin (n+2)→ℝ) (hξ : ∑k,ξ k=0)
    (i : Fin (n+2)) (y : ℝ) :
    normalPDF y*(∑j,pairKernelDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
      (fun k=>-tieMean n*(ξ k/2)) i j y)=
      (((n:ℝ)+2)*ξ i/2)*(tieWeight n y*((-y+((n:ℝ)+1)*r y)*(y-tieMean n))) := by
  rw [Finset.mul_sum]
  simp_rw [regular_pairKernelDerivative_density n ξ hξ]
  have he (j:Fin (n+2)) : tieWeight n y*((((n:ℝ)+2)*r y*ξ i-H y*(ξ i-ξ j))*(y-tieMean n)/2-ξ j/2)=
      tieWeight n y*((((n:ℝ)+2)*r y-H y)*ξ i*(y-tieMean n)/2)+
      tieWeight n y*(H y*(y-tieMean n)-1)/2*ξ j:=by ring
  simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum,hξ,mul_zero,add_zero]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,H]
  ring

theorem regular_kernelSpeed_integral (n : ℕ) (hn : 0<n) :
    (∫y,tieWeight n y*((-y+((n:ℝ)+1)*r y)*(y-tieMean n)))= -2*tieMass n*eta n := by
  have hi:=tieWeight_ibp_zero n
  have hj:=tieWeight_ibp_one n
  have he : (fun y=>tieWeight n y*((-y+((n:ℝ)+1)*r y)*(y-tieMean n)))=
      fun y=>tieWeight n y*regularLogHazardSpeed n y+
        (tieWeight n y*(1-2*y^2+(n:ℝ)*(y*r y)))-
        tieMean n*(tieWeight n y*(-2*y+(n:ℝ)*r y)):=by
    funext y;unfold regularLogHazardSpeed;ring
  have h1 : Integrable (fun y=>tieWeight n y*regularLogHazardSpeed n y+
      tieWeight n y*(1-2*y^2+(n:ℝ)*(y*r y))) volume:=
    (regular_logHazard_weighted_integrable n).add (tieWeight_x_derivative_integrable n)
  rw [he,integral_sub h1 ((tieWeight_derivative_integrable n).const_mul _),
    integral_add (regular_logHazard_weighted_integrable n) (tieWeight_x_derivative_integrable n),integral_const_mul]
  have hz:=integral_eq_zero_of_hasDerivAt_of_integrable (tieWeight_hasDerivAt n)
    (tieWeight_derivative_integrable n) (tieWeight_integrable n)
  have hz1:=integral_eq_zero_of_hasDerivAt_of_integrable (tieWeight_x_hasDerivAt n)
    (tieWeight_x_derivative_integrable n) (weighted_x_integrable n)
  rw [hz,hz1,add_zero,mul_zero,sub_zero,regular_logHazard_integral n hn]

def varianceStdPath (ξ : Fin (n+2)→ℝ) (t : ℝ) (i : Fin (n+2)) : ℝ := Real.sqrt (1+t*ξ i)
def balancedVariancePath (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  selectedOffsets (diagonalRows (varianceStdPath ξ t)) (fun _=>((n:ℝ)+2)⁻¹)

@[simp] theorem varianceStdPath_zero (ξ : Fin (n+2)→ℝ) : varianceStdPath ξ 0=fun _=>1:=by
  funext i;simp [varianceStdPath]
@[simp] theorem balancedVariancePath_zero (ξ : Fin (n+2)→ℝ) : balancedVariancePath ξ 0=fun _=>0:=by
  unfold balancedVariancePath
  rw [varianceStdPath_zero,standard_selectedOffsets_zero]
  rfl

theorem varianceStdPath_contDiffAt (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) :
    ContDiffAt ℝ 1 (fun t=>varianceStdPath ξ t i) 0 := by
  unfold varianceStdPath
  fun_prop (disch:=norm_num)

theorem balancedVariancePath_contDiffAt (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) :
    ContDiffAt ℝ 1 (fun t=>balancedVariancePath ξ t i) 0 := by
  have hp : ∀i:Fin (n+2),0<((n:ℝ)+2)⁻¹:=by intro i;positivity
  have hs : (∑i:Fin (n+2),((n:ℝ)+2)⁻¹)=1:=by simp [Nat.cast_add,Nat.cast_ofNat];field_simp
  have hσ : ContDiffAt ℝ 1 (varianceStdPath ξ) 0:=contDiffAt_pi.mpr (varianceStdPath_contDiffAt ξ)
  have hf:=selected_diagonal_parameters_contDiffAt (fun _ : Fin (n+2)=>(1:ℝ)) (by intro k;norm_num)
    (fun _=>((n:ℝ)+2)⁻¹) hp hs
  have hf' : ContDiffAt ℝ 1 (fun a:Fin (n+2)→ℝ=>selectedOffsets (diagonalRows a) (fun _=>((n:ℝ)+2)⁻¹)) (varianceStdPath ξ 0):=by
    rw [varianceStdPath_zero];exact hf
  have hc:=hf'.comp 0 hσ
  have he:=((NegativeVotingFanInverse.centeredGauge (Fin (n+2))).subtypeL.contDiff.contDiffAt).comp 0 hc
  exact (contDiffAt_pi.mp he) i

theorem varianceStdPath_derivative (ξ : Fin (n+2)→ℝ) : pathDerivative (varianceStdPath ξ) 0=fun i=>ξ i/2 := by
  funext i
  have hp:HasDerivAt (fun t:ℝ=>1+t*ξ i) (ξ i) 0:=by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (ξ i)).const_add 1
  have hq:=(Real.hasDerivAt_sqrt (x:=1+(0:ℝ)*ξ i) (by norm_num)).comp 0 hp
  have hd:HasDerivAt (fun t=>varianceStdPath ξ t i) (ξ i/2) 0:=by
    convert hq using 1
    · rfl
    · norm_num;ring
  exact hd.deriv

theorem balancedVariancePath_derivative (ξ : Fin (n+2)→ℝ) (hξ:∑i,ξ i=0) :
    pathDerivative (balancedVariancePath ξ) 0=fun i=>-tieMean n*(ξ i/2) := by
  have hh:=standard_variance_selectedOffsets_hasDerivAt n ξ hξ
  have hco:=((NegativeVotingFanInverse.centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt).comp_hasDerivAt 0 hh
  have hpi:=hasDerivAt_pi.mp hco
  funext i
  exact (hpi i).deriv

theorem pairKernelDerivative_integrable (σ h ζ η : Fin (n+2)→ℝ) (i j : Fin (n+2)) :
    Integrable (pairKernelDerivative σ h ζ η i j) (gaussianReal 0 1) := by
  let A:=fun k=>|linearSlope σ h ζ η i k 0|
  let B:=fun k=>|constantSlope σ h ζ η i k 0|
  let R:=r 0+|σ i/σ j|+|(h i-h j)/σ j|
  let I:=|(σ j)⁻¹|
  let J:=|ζ j/(σ j)^2|
  let C:=((∑k∈Finset.univ.erase i,(A k+B k))*R*I+I*(A j+B j)+R*J)
  apply ((NegativeVotingDensityMomentBounds.integrable_standard_polynomial 2).const_mul C).mono' (by fun_prop)
  filter_upwards with y
  exact pairKernelDerivative_bound σ h ζ η i j y A B R I J (fun _=>le_rfl)
    (fun _=>le_rfl) le_rfl le_rfl le_rfl

theorem regular_rowKernelDerivative_integral (n : ℕ) (hn : 0<n) (ξ : Fin (n+2)→ℝ)
    (hξ : ∑i,ξ i=0) (i : Fin (n+2)) :
    (∑j,∫y,pairKernelDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
      (fun k=>-tieMean n*(ξ k/2)) i j y ∂gaussianReal 0 1)= -referenceScale n*eta n*ξ i := by
  rw [←integral_finset_sum Finset.univ (fun j _=>pairKernelDerivative_integrable _ _ _ _ i j)]
  have he:=gaussian_affine_integral 1 0 (by norm_num)
    (fun y=>∑j,pairKernelDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
      (fun k=>-tieMean n*(ξ k/2)) i j y)
  simp only [one_mul,add_zero,gaussianDensity,sub_zero,div_one] at he
  rw [he]
  simp_rw [regular_rowKernelDerivative_density n ξ hξ]
  rw [integral_const_mul,regular_kernelSpeed_integral n hn,tieMass_eq_referenceScale n hn]
  field_simp

/-- The literal all-label coefficient, including the analytic diagonal. -/
def hazardCoefficient (σ h : Fin (n+2)→ℝ) (i : Fin (n+2)) : ℝ :=
  ∑j,∫x,hazardPairDensity σ h x i j

theorem hazardCoefficient_regular (n : ℕ) (hn : 0<n) (i : Fin (n+2)) :
    hazardCoefficient (fun _=>1) (fun _=>0) i=referenceScale n := by
  unfold hazardCoefficient
  simp_rw [regular_hazardPairDensity]
  change (∑j:Fin (n+2),tieMass n)=referenceScale n
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  rw [tieMass_eq_referenceScale n hn]
  field_simp

/-- Exact regular coefficient derivative along the actual selected balancing
path. Integral differentiation, the balancing velocity and eta's range are
all derived; no derivative or local dominance is postulated. -/
theorem hazardCoefficient_balancedVariance_hasDerivAt (n : ℕ) (hn : 0<n)
    (ξ : Fin (n+2)→ℝ) (hξ : ∑i,ξ i=0) (i : Fin (n+2)) :
    HasDerivAt (fun t=>hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i)
      (-referenceScale n*eta n*ξ i) 0 := by
  have hd:=HasDerivAt.fun_sum (u:=Finset.univ) (fun j _=>hazardPairIntegral_hasDerivAt
    (varianceStdPath ξ) (balancedVariancePath ξ) 0 (varianceStdPath_contDiffAt ξ)
    (balancedVariancePath_contDiffAt ξ) (by intro k;simp [varianceStdPath]) i j)
  simp only [varianceStdPath_zero,balancedVariancePath_zero,varianceStdPath_derivative,
    balancedVariancePath_derivative ξ hξ] at hd
  rw [regular_rowKernelDerivative_integral n hn ξ hξ] at hd
  exact hd

theorem regular_coefficient_and_slope (n : ℕ) (hn : 0<n)
    (ξ : Fin (n+2)→ℝ) (hξ : ∑i,ξ i=0) (i : Fin (n+2)) :
    hazardCoefficient (varianceStdPath ξ 0) (balancedVariancePath ξ 0) i=referenceScale n ∧
    HasDerivAt (fun t=>hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i)
      (-referenceScale n*eta n*ξ i) 0 ∧ 1/4≤eta n ∧ eta n≤1/2 := by
  exact ⟨by simpa only [varianceStdPath_zero,balancedVariancePath_zero] using hazardCoefficient_regular n hn i,
    hazardCoefficient_balancedVariance_hasDerivAt n hn ξ hξ i,(eta_bounds n hn).1,(eta_bounds n hn).2⟩

end NegativeVotingRegularHazardDerivative
