import GaussianRegularDiagonalBalance
import GaussianDensityMomentBounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual diagonal pair integrals, including analytic diagonal entries,
are differentiated after conditioning on one fixed standard Gaussian. The
parameter derivatives are dominated by polynomial Gaussian growth. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators ENNReal Classical Topology
namespace NegativeVotingHazardKernelDifferentiation
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalBalancedDerivative NegativeVotingDiagonalFacetIntegral
  NegativeVotingHazardPolynomialBounds NegativeVotingHazardIntegrability
  NegativeVotingRegularTieLaw NegativeVotingDensityMomentBounds
variable {m : ℕ}

def pairKernel (σ h : Fin m→ℝ) (i j : Fin m) (y : ℝ) : ℝ :=
  winnerKernel σ h i y*(r (standardized σ h i j y)/σ j)

def pairKernelDerivative (σ h ζ η : Fin m→ℝ) (i j : Fin m) (y : ℝ) : ℝ :=
  winnerKernelDerivative σ h ζ η i 0 y*(r (standardized σ h i j y)/σ j)+
  winnerKernel σ h i y*((-r (standardized σ h i j y)*H (standardized σ h i j y))*
    (linearSlope σ h ζ η i j 0*y+constantSlope σ h ζ η i j 0)/σ j-
    r (standardized σ h i j y)*(ζ j/(σ j)^2))

theorem standardized_path_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ) (ζ η : Fin m→ℝ)
    (hσ : ∀k,HasDerivAt (fun s=>σ s k) (ζ k) t)
    (hh : ∀k,HasDerivAt (fun s=>h s k) (η k) t)
    (i j : Fin m) (y : ℝ) (hj : σ t j≠0) :
    HasDerivAt (fun s=>standardized (σ s) (h s) i j y)
      (linearSlope (σ t) (h t) ζ η i j 0*y+constantSlope (σ t) (h t) ζ η i j 0) t := by
  have hd:=(((hσ i).mul_const y).add (hh i) |>.sub (hh j)).div (hσ j) hj
  convert hd using 1
  · rfl
  · simp only [linearSlope,constantSlope,parameterLine_zero,Pi.add_apply,Pi.sub_apply]
    ring

theorem winnerKernel_path_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ) (ζ η : Fin m→ℝ)
    (hσ : ∀k,HasDerivAt (fun s=>σ s k) (ζ k) t)
    (hh : ∀k,HasDerivAt (fun s=>h s k) (η k) t)
    (hnz : ∀k,σ t k≠0) (i : Fin m) (y : ℝ) :
    HasDerivAt (fun s=>winnerKernel (σ s) (h s) i y)
      (winnerKernelDerivative (σ t) (h t) ζ η i 0 y) t := by
  have hd:=HasDerivAt.fun_finsetProd (u:=Finset.univ.erase i)
    (fun j hj=>(hasDerivAt_normalCDF _).comp t
      (standardized_path_hasDerivAt σ h t ζ η hσ hh i j y (hnz j)))
  convert hd using 1
  · rfl
  · simp only [winnerKernelDerivative,parameterLine_zero,Function.comp_def,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem pairKernel_path_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ) (ζ η : Fin m→ℝ)
    (hσ : ∀k,HasDerivAt (fun s=>σ s k) (ζ k) t)
    (hh : ∀k,HasDerivAt (fun s=>h s k) (η k) t)
    (hnz : ∀k,σ t k≠0) (i j : Fin m) (y : ℝ) :
    HasDerivAt (fun s=>pairKernel (σ s) (h s) i j y)
      (pairKernelDerivative (σ t) (h t) ζ η i j y) t := by
  have hz:=standardized_path_hasDerivAt σ h t ζ η hσ hh i j y (hnz j)
  have hr:=((hasDerivAt_r _).comp t hz).div (hσ j) (hnz j)
  have hd:=(winnerKernel_path_hasDerivAt σ h t ζ η hσ hh hnz i y).mul hr
  convert hd using 1
  · rfl
  · simp only [pairKernelDerivative,Function.comp_def,Pi.div_apply]
    field_simp [hnz j]

@[fun_prop] theorem pairKernel_continuous (σ h : Fin m→ℝ) (i j : Fin m) :
    Continuous (pairKernel σ h i j) := by
  unfold pairKernel
  exact (winnerKernel_continuous σ h i).mul ((r_continuous.comp (by unfold standardized;fun_prop)).div_const _)

@[fun_prop] theorem pairKernelDerivative_continuous (σ h ζ η : Fin m→ℝ) (i j : Fin m) :
    Continuous (pairKernelDerivative σ h ζ η i j) := by
  unfold pairKernelDerivative H
  have hr : Continuous (fun y=>r (standardized σ h i j y)):=r_continuous.comp (by unfold standardized;fun_prop)
  have hz : Continuous (fun y=>standardized σ h i j y):=by unfold standardized;fun_prop
  have hw:=winnerKernel_continuous σ h i
  have hwd:=winnerKernelDerivative_continuous σ h ζ η i 0
  fun_prop

theorem standardized_abs_le (σ h : Fin m→ℝ) (i j : Fin m) (y : ℝ) :
    |standardized σ h i j y|≤(|σ i/σ j|+|(h i-h j)/σ j|)*(1+|y|) := by
  have he : standardized σ h i j y=(σ i/σ j)*y+(h i-h j)/σ j:=by unfold standardized;ring
  rw [he]
  have hh:=(abs_add_le ((σ i/σ j)*y) ((h i-h j)/σ j))
  rw [abs_mul] at hh
  nlinarith [mul_nonneg (abs_nonneg ((h i-h j)/σ j)) (abs_nonneg y),abs_nonneg (σ i/σ j)]

theorem pairKernel_integrable (σ h : Fin m→ℝ) (i j : Fin m) :
    Integrable (pairKernel σ h i j) (gaussianReal 0 1) := by
  let R:=r 0+|σ i/σ j|+|(h i-h j)/σ j|
  apply ((integrable_standard_polynomial 1).const_mul (R*|(σ j)⁻¹|)).mono' (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs,pairKernel,abs_mul,abs_div,abs_of_pos (r_pos _)]
  have hw:=kernel_product_bounds σ h i (Finset.univ.erase i) y
  have hr : r (standardized σ h i j y)≤R*(1+|y|):=by
    have hh:=(normal_hazard_linear_growth _).trans (add_le_add (le_refl (r 0)) (standardized_abs_le σ h i j y))
    dsimp [R]
    nlinarith [mul_nonneg (r_pos 0).le (abs_nonneg y)]
  have hww : |winnerKernel σ h i y|≤1:=by rw [winnerKernel,abs_of_nonneg hw.1];exact hw.2
  have hh:=mul_le_mul hww (div_le_div_of_nonneg_right hr (abs_nonneg (σ j))) (by positivity [r_pos (standardized σ h i j y)]) (by norm_num)
  simp only [one_mul] at hh
  simpa only [pow_one,abs_inv,Pi.mul_apply,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,R] using hh

/-- Exact Gaussian substitution for every pair, including i=j. -/
theorem pair_integral_eq_kernel (σ h : Fin m→ℝ) (hσ : ∀k,0<σ k) (i j : Fin m) :
    (∫x,hazardPairDensity σ h x i j)=∫y,pairKernel σ h i j y ∂gaussianReal 0 1 := by
  let f:=fun x=>(∏k∈Finset.univ.erase i,gaussianCDF (σ k) (h k) x)*gaussianHazard (σ j) (h j) x
  have he (x:ℝ) : hazardPairDensity σ h x i j=gaussianDensity (σ i) (h i) x*f x:=by
    unfold hazardPairDensity productCDF gaussianHazard f
    rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    dsimp [gaussianHazard]
    field_simp [(gaussianCDF_pos (σ i) (h i) x).ne']
  simp_rw [he]
  rw [←gaussian_affine_integral (σ i) (h i) (hσ i)]
  apply integral_congr_ae
  filter_upwards with y
  dsimp [f,pairKernel,winnerKernel]
  rw [gaussianHazard_eq_scaled]
  rfl

/-- An explicit polynomial dominator for the fixed-Gaussian kernel derivative. -/
theorem pairKernelDerivative_bound (σ h ζ η : Fin m→ℝ) (i j : Fin m) (y : ℝ)
    (A B : Fin m→ℝ) (R I J : ℝ)
    (hA : ∀k,|linearSlope σ h ζ η i k 0|≤A k)
    (hB : ∀k,|constantSlope σ h ζ η i k 0|≤B k)
    (hR : r 0+|σ i/σ j|+|(h i-h j)/σ j|≤R)
    (hI : |(σ j)⁻¹|≤I) (hJ : |ζ j/(σ j)^2|≤J) :
    |pairKernelDerivative σ h ζ η i j y|≤
      ((∑k∈Finset.univ.erase i,(A k+B k))*R*I+I*(A j+B j)+R*J)*(1+|y|)^2 := by
  let P:=1+|y|
  let S:=∑k∈Finset.univ.erase i,(A k+B k)
  have hP : 1≤P:=by dsimp [P];linarith [abs_nonneg y]
  have hA0 k:0≤A k:=(abs_nonneg _).trans (hA k)
  have hB0 k:0≤B k:=(abs_nonneg _).trans (hB k)
  have hAj:=hA0 j
  have hBj:=hB0 j
  have hS:0≤S:=Finset.sum_nonneg fun k hk=>add_nonneg (hA0 k) (hB0 k)
  have hR0:0≤R:=(by positivity [r_pos 0] : 0≤r 0+|σ i/σ j|+|(h i-h j)/σ j|).trans hR
  have hI0:0≤I:=(abs_nonneg _).trans hI
  have hJ0:0≤J:=(abs_nonneg _).trans hJ
  have hr : |r (standardized σ h i j y)|≤R*P:=by
    rw [abs_of_pos (r_pos _)]
    have hh:=(normal_hazard_linear_growth _).trans (add_le_add (le_refl (r 0)) (standardized_abs_le σ h i j y))
    have hb:=mul_le_mul_of_nonneg_right hR (by linarith : 0≤P)
    dsimp [P] at hb ⊢
    nlinarith [mul_nonneg (r_pos 0).le (abs_nonneg y)]
  have hd : |linearSlope σ h ζ η i j 0*y+constantSlope σ h ζ η i j 0|≤(A j+B j)*P:=by
    have hx : |linearSlope σ h ζ η i j 0*y|≤A j*|y|:=by
      rw [abs_mul];exact mul_le_mul_of_nonneg_right (hA j) (abs_nonneg y)
    have hh:=(abs_add_le (linearSlope σ h ζ η i j 0*y) (constantSlope σ h ζ η i j 0)).trans (add_le_add hx (hB j))
    dsimp [P]
    nlinarith [mul_nonneg (hB0 j) (abs_nonneg y),hA0 j]
  have hw:|winnerKernel σ h i y|≤1:=by
    have hh:=kernel_product_bounds σ h i (Finset.univ.erase i) y
    rw [winnerKernel,abs_of_nonneg hh.1];exact hh.2
  have hwd:=winnerKernelDerivative_bound σ h ζ η i 0 y A B hA hB
  have hdr:|-r (standardized σ h i j y)*H (standardized σ h i j y)|≤1:=by
    simpa only [Real.norm_eq_abs] using normal_hazard_derivative_bound (standardized σ h i j y)
  have ht1:|winnerKernelDerivative σ h ζ η i 0 y*(r (standardized σ h i j y)/σ j)|≤S*P*(R*P*I):=by
    rw [abs_mul,div_eq_mul_inv,abs_mul]
    exact mul_le_mul hwd (mul_le_mul hr hI (abs_nonneg _) (by positivity)) (by positivity) (by positivity)
  have ht2:|(-r (standardized σ h i j y)*H (standardized σ h i j y))*
      (linearSlope σ h ζ η i j 0*y+constantSlope σ h ζ η i j 0)/σ j|≤(A j+B j)*P*I:=by
    rw [div_eq_mul_inv,abs_mul,abs_mul]
    exact (mul_le_mul (mul_le_mul hdr hd (abs_nonneg _) (by norm_num)) hI (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have ht3:|r (standardized σ h i j y)*(ζ j/(σ j)^2)|≤R*P*J:=by
    rw [abs_mul];exact mul_le_mul hr hJ (abs_nonneg _) (by positivity)
  have ht4:|winnerKernel σ h i y*((-r (standardized σ h i j y)*H (standardized σ h i j y))*
      (linearSlope σ h ζ η i j 0*y+constantSlope σ h ζ η i j 0)/σ j-r (standardized σ h i j y)*(ζ j/(σ j)^2))|≤
      (A j+B j)*P*I+R*P*J:=by
    rw [abs_mul]
    have hh:=(abs_sub _ _).trans (add_le_add ht2 ht3)
    exact (mul_le_mul hw hh (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hh:=(abs_add_le _ _).trans (add_le_add ht1 ht4)
  change |pairKernelDerivative σ h ζ η i j y|≤S*P*(R*P*I)+((A j+B j)*P*I+R*P*J) at hh
  have hlinear:0≤I*(A j+B j)+R*J:=by positivity
  have hp2:P≤P^2:=by nlinarith
  have hf:=mul_le_mul_of_nonneg_left hp2 hlinear
  dsimp [S,P] at *
  nlinarith

end NegativeVotingHazardKernelDifferentiation
