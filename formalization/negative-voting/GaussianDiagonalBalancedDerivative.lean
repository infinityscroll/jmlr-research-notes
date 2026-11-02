import GaussianDiagonalScoreRealization
import GaussianHazardIntegrability

/-! Actual first variations of the diagonal Gaussian winner law. Conditioning
on the winning standard normal coordinate keeps the integrating measure fixed;
local domination is linear Gaussian growth, not an assumed differentiability
of a formal threshold integral. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical Topology
namespace NegativeVotingDiagonalBalancedDerivative
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingDiagonalScoreRealization
  NegativeVotingFan NegativeVotingCapTail NegativeVotingFanJacobian
  NegativeVotingFanSelectedOffsets NegativeVotingHazardIntegrability
variable {n m : ℕ}

def parameterLine (a v : Fin m→ℝ) (t : ℝ) (i : Fin m) : ℝ := a i+t*v i
@[simp] theorem parameterLine_zero (a v : Fin m→ℝ) : parameterLine a v 0=a := by ext i;simp [parameterLine]

def standardized (σ h : Fin m→ℝ) (i j : Fin m) (y : ℝ) : ℝ := (σ i*y+h i-h j)/σ j

def linearSlope (σ h ζ η : Fin m→ℝ) (i j : Fin m) (t : ℝ) : ℝ :=
  (ζ i*parameterLine σ ζ t j-parameterLine σ ζ t i*ζ j)/(parameterLine σ ζ t j)^2

def constantSlope (σ h ζ η : Fin m→ℝ) (i j : Fin m) (t : ℝ) : ℝ :=
  ((η i-η j)*parameterLine σ ζ t j-
    (parameterLine h η t i-parameterLine h η t j)*ζ j)/(parameterLine σ ζ t j)^2

theorem standardized_hasDerivAt (σ h ζ η : Fin m→ℝ) (i j : Fin m) (y t : ℝ)
    (hσ : parameterLine σ ζ t j≠0) :
    HasDerivAt (fun s=>standardized (parameterLine σ ζ s) (parameterLine h η s) i j y)
      (linearSlope σ h ζ η i j t*y+constantSlope σ h ζ η i j t) t := by
  have hp (a v : Fin m→ℝ) (k : Fin m) : HasDerivAt (fun s=>parameterLine a v s k) (v k) t:=by
    simpa only [parameterLine,id_eq,one_mul] using ((hasDerivAt_id t).mul_const (v k)).const_add (a k)
  have hd:=(((hp σ ζ i).mul_const y).add (hp h η i) |>.sub (hp h η j)).div (hp σ ζ j) hσ
  convert hd using 1
  · rfl
  · dsimp [linearSlope,constantSlope]
    ring

def winnerKernel (σ h : Fin m→ℝ) (i : Fin m) (y : ℝ) : ℝ :=
  ∏j∈Finset.univ.erase i,normalCDF (standardized σ h i j y)

def winnerKernelDerivative (σ h ζ η : Fin m→ℝ) (i : Fin m) (t y : ℝ) : ℝ :=
  ∑j∈Finset.univ.erase i,
    (∏k∈(Finset.univ.erase i).erase j,
      normalCDF (standardized (parameterLine σ ζ t) (parameterLine h η t) i k y))*
    normalPDF (standardized (parameterLine σ ζ t) (parameterLine h η t) i j y)*
    (linearSlope σ h ζ η i j t*y+constantSlope σ h ζ η i j t)

theorem winnerKernel_hasDerivAt (σ h ζ η : Fin m→ℝ) (i : Fin m) (y t : ℝ)
    (hσ : ∀j,parameterLine σ ζ t j≠0) :
    HasDerivAt (fun s=>winnerKernel (parameterLine σ ζ s) (parameterLine h η s) i y)
      (winnerKernelDerivative σ h ζ η i t y) t := by
  have hh:=HasDerivAt.fun_finsetProd (u:=Finset.univ.erase i)
    (fun j hj=>(hasDerivAt_normalCDF _).comp t (standardized_hasDerivAt σ h ζ η i j y t (hσ j)))
  convert hh using 1
  · rfl
  · dsimp [winnerKernelDerivative]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem kernel_product_bounds (σ h : Fin m→ℝ) (i : Fin m) (s : Finset (Fin m)) (y : ℝ) :
    0≤(∏j∈s,normalCDF (standardized σ h i j y)) ∧
      (∏j∈s,normalCDF (standardized σ h i j y))≤1 :=
  ⟨Finset.prod_nonneg (fun j hj=>(normalCDF_pos _).le),
   Finset.prod_le_one₀ (fun j hj=>(normalCDF_pos _).le) (fun j hj=>(normalCDF_lt_one _).le)⟩

@[fun_prop] theorem winnerKernel_continuous (σ h : Fin m→ℝ) (i : Fin m) :
    Continuous (winnerKernel σ h i) := by
  unfold winnerKernel standardized
  exact continuous_finset_prod _ (fun j hj=>NegativeVotingMassCentroid.continuous_normalCDF.comp (by fun_prop))

@[fun_prop] theorem winnerKernelDerivative_continuous (σ h ζ η : Fin m→ℝ) (i : Fin m) (t : ℝ) :
    Continuous (winnerKernelDerivative σ h ζ η i t) := by
  unfold winnerKernelDerivative
  apply continuous_finset_sum
  intro j hj
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_finset_prod _ (fun k hk=>NegativeVotingMassCentroid.continuous_normalCDF.comp (by unfold standardized;fun_prop))
    · unfold normalPDF gaussianPDFReal standardized;fun_prop
  · fun_prop

theorem winnerKernel_integrable (σ h : Fin m→ℝ) (i : Fin m) :
    Integrable (winnerKernel σ h i) (gaussianReal 0 1) := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs,winnerKernel,abs_of_nonneg (kernel_product_bounds σ h i _ y).1]
  exact (kernel_product_bounds σ h i _ y).2

/-- Pointwise derivative domination uses only bounded scalar derivative
coefficients and the elementary 0≤CDF≤1, PDF≤1 bounds. -/
theorem winnerKernelDerivative_bound (σ h ζ η : Fin m→ℝ) (i : Fin m) (t y : ℝ)
    (A B : Fin m→ℝ) (hA : ∀j,|linearSlope σ h ζ η i j t|≤A j)
    (hB : ∀j,|constantSlope σ h ζ η i j t|≤B j) :
    |winnerKernelDerivative σ h ζ η i t y|≤
      (∑j∈Finset.univ.erase i,(A j+B j))*(1+|y|) := by
  unfold winnerKernelDerivative
  calc
    _≤∑j∈Finset.univ.erase i,
      |(∏k∈(Finset.univ.erase i).erase j,
        normalCDF (standardized (parameterLine σ ζ t) (parameterLine h η t) i k y))*
        normalPDF (standardized (parameterLine σ ζ t) (parameterLine h η t) i j y)*
        (linearSlope σ h ζ η i j t*y+constantSlope σ h ζ η i j t)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑j∈Finset.univ.erase i,(A j+B j)*(1+|y|):=by
      apply Finset.sum_le_sum
      intro j hj
      have hp:=kernel_product_bounds (parameterLine σ ζ t) (parameterLine h η t) i ((Finset.univ.erase i).erase j) y
      have hn:0≤normalPDF (standardized (parameterLine σ ζ t) (parameterLine h η t) i j y):=(normalPDF_pos _).le
      have hpdf:normalPDF (standardized (parameterLine σ ζ t) (parameterLine h η t) i j y)≤1:=
        (NegativeVotingMovingCap.normalPDF_le_zero _).trans NegativeVotingRegularFacetMean.normalPDF_zero_le_one
      have hab : |linearSlope σ h ζ η i j t*y+constantSlope σ h ζ η i j t|≤A j*|y|+B j:=by
        exact (abs_add_le _ _).trans (add_le_add (by rw [abs_mul];exact mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)) (hB j))
      have hA0:0≤A j:=(abs_nonneg _).trans (hA j)
      have hB0:0≤B j:=(abs_nonneg _).trans (hB j)
      rw [abs_mul,abs_mul,abs_of_nonneg hp.1,abs_of_nonneg hn]
      have hm:=mul_le_one₀ hp.2 hn hpdf
      calc
        _≤|linearSlope σ h ζ η i j t*y+constantSlope σ h ζ η i j t|:=mul_le_of_le_one_left (abs_nonneg _) hm
        _≤A j*|y|+B j:=hab
        _≤(A j+B j)*(1+|y|):=by nlinarith [mul_nonneg hB0 (abs_nonneg y)]
    _=_:=by rw [Finset.sum_mul]

/-- Continuity of the finitely many rational coefficients gives a genuine
neighborhood on which differentiation is dominated by linear Gaussian growth. -/
theorem exists_local_coefficients (σ h ζ η : Fin m→ℝ) (hσ : ∀j,0<σ j) (i : Fin m) :
    ∃s∈𝓝 (0:ℝ), ∀t∈s, (∀j,0<parameterLine σ ζ t j) ∧
      (∀j,|linearSlope σ h ζ η i j t|≤|linearSlope σ h ζ η i j 0|+1) ∧
      (∀j,|constantSlope σ h ζ η i j t|≤|constantSlope σ h ζ η i j 0|+1) := by
  have hp : ∀ᶠ t in 𝓝 (0:ℝ),∀j,0<parameterLine σ ζ t j := by
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun t=>parameterLine σ ζ t j) 0:=by unfold parameterLine;fun_prop
    exact hc.eventually (lt_mem_nhds (by simpa [parameterLine] using hσ j))
  have hA : ∀ᶠ t in 𝓝 (0:ℝ),∀j,|linearSlope σ h ζ η i j t|≤|linearSlope σ h ζ η i j 0|+1 := by
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (linearSlope σ h ζ η i j) 0:=by
      unfold linearSlope parameterLine
      fun_prop (disch:=simpa using pow_ne_zero 2 (hσ j).ne')
    exact (hc.abs.eventually (gt_mem_nhds (by linarith : |linearSlope σ h ζ η i j 0| < |linearSlope σ h ζ η i j 0|+1))).mono (fun t ht=>ht.le)
  have hB : ∀ᶠ t in 𝓝 (0:ℝ),∀j,|constantSlope σ h ζ η i j t|≤|constantSlope σ h ζ η i j 0|+1 := by
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (constantSlope σ h ζ η i j) 0:=by
      unfold constantSlope parameterLine
      fun_prop (disch:=simpa using pow_ne_zero 2 (hσ j).ne')
    exact (hc.abs.eventually (gt_mem_nhds (by linarith : |constantSlope σ h ζ η i j 0| < |constantSlope σ h ζ η i j 0|+1))).mono (fun t ht=>ht.le)
  exact ⟨_,hp.and (hA.and hB),fun t ht=>ht⟩

theorem winnerIntegral_hasDerivAt (σ h ζ η : Fin m→ℝ) (hσ : ∀j,0<σ j) (i : Fin m) :
    HasDerivAt (fun t=>∫y,winnerKernel (parameterLine σ ζ t) (parameterLine h η t) i y ∂gaussianReal 0 1)
      (∫y,winnerKernelDerivative σ h ζ η i 0 y ∂gaussianReal 0 1) 0 := by
  obtain ⟨s,hs,hbounds⟩:=exists_local_coefficients σ h ζ η hσ i
  let A:=fun j=>|linearSlope σ h ζ η i j 0|+1
  let B:=fun j=>|constantSlope σ h ζ η i j 0|+1
  let C:=∑j∈Finset.univ.erase i,(A j+B j)
  have habs : Integrable (fun y:ℝ=>|y|) (gaussianReal 0 1):=by
    simpa only [id_eq,Real.norm_eq_abs] using ((memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable (by norm_num)).norm
  have hdom : Integrable (fun y:ℝ=>C*(1+|y|)) (gaussianReal 0 1):=
    ((integrable_const 1).add habs).const_mul C
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=s) (bound:=fun y:ℝ=>C*(1+|y|))
    (F:=fun t y=>winnerKernel (parameterLine σ ζ t) (parameterLine h η t) i y)
    (F':=winnerKernelDerivative σ h ζ η i) hs
    (by filter_upwards with t;fun_prop) (winnerKernel_integrable _ _ i) (by fun_prop)
    ?_ hdom ?_).2
  · filter_upwards with y
    intro t ht
    simpa only [Real.norm_eq_abs,C,A,B] using winnerKernelDerivative_bound σ h ζ η i t y A B
      (hbounds t ht).2.1 (hbounds t ht).2.2
  · filter_upwards with y
    intro t ht
    exact winnerKernel_hasDerivAt σ h ζ η i y t (fun j=>((hbounds t ht).1 j).ne')

theorem mass_diagonal_eq_winnerKernel (σ h : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j) (i : Fin (n+1)) :
    mass (diagonalRows σ) h i=∫y,winnerKernel σ h i y ∂gaussianReal 0 1 := by
  rw [mass_diagonal_eq_winner_integral σ h hσ i,winner_integral_conditioned σ h hσ i]
  apply integral_congr_ae
  filter_upwards with y
  exact remainingProduct_eq_erase _ (fun j=>(gaussianCDF_pos _ _ _).ne') i

theorem mass_diagonal_affine_hasDerivAt_kernel (σ h ζ η : Fin (n+1)→ℝ)
    (hσ : ∀j,0<σ j) (i : Fin (n+1)) :
    HasDerivAt (fun t=>mass (diagonalRows (parameterLine σ ζ t)) (parameterLine h η t) i)
      (∫y,winnerKernelDerivative σ h ζ η i 0 y ∂gaussianReal 0 1) 0 := by
  apply (winnerIntegral_hasDerivAt σ h ζ η hσ i).congr_of_eventuallyEq
  obtain ⟨s,hs,hbounds⟩:=exists_local_coefficients σ h ζ η hσ i
  filter_upwards [hs] with t ht
  exact mass_diagonal_eq_winnerKernel _ _ (hbounds t ht).1 i

def derivativeTerm (σ h ζ η : Fin m→ℝ) (i j : Fin m) (y : ℝ) : ℝ :=
  otherProduct σ h i j (σ i*y+h i)*normalPDF (standardized σ h i j y)*
    (linearSlope σ h ζ η i j 0*y+constantSlope σ h ζ η i j 0)

theorem derivativeTerm_integrable (σ h ζ η : Fin m→ℝ) (i j : Fin m) :
    Integrable (derivativeTerm σ h ζ η i j) (gaussianReal 0 1) := by
  have hi : Integrable (fun y:ℝ=>linearSlope σ h ζ η i j 0*y+constantSlope σ h ζ η i j 0)
      (gaussianReal 0 1):=by
    exact (((memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable (by norm_num)).const_mul _).add (integrable_const _)
  apply hi.bdd_mul (c:=1)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (otherProduct_continuous σ h i j).comp (by fun_prop)
    · unfold standardized normalPDF gaussianPDFReal;fun_prop
  · filter_upwards with y
    have hp:=otherProduct_bounds σ h i j (σ i*y+h i)
    have hn:0≤normalPDF (standardized σ h i j y):=(normalPDF_pos _).le
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.1 hn)]
    exact mul_le_one₀ hp.2 hn ((NegativeVotingMovingCap.normalPDF_le_zero _).trans NegativeVotingRegularFacetMean.normalPDF_zero_le_one)

theorem derivativeTerm_eq_transport (σ h ζ η : Fin m→ℝ) (hσ : ∀j,0<σ j)
    (i j : Fin m) (y : ℝ) :
    derivativeTerm σ h ζ η i j y=
      gaussianDensity (σ j) (h j) (σ i*y+h i)*otherProduct σ h i j (σ i*y+h i)*
        (transportSpeed (σ i) (h i) (ζ i) (η i) (σ i*y+h i)-
          transportSpeed (σ j) (h j) (ζ j) (η j) (σ i*y+h i)) := by
  unfold derivativeTerm gaussianDensity standardized linearSlope constantSlope parameterLine transportSpeed
  simp only [zero_mul,add_zero]
  field_simp [(hσ i).ne',(hσ j).ne']
  ring

theorem winnerKernelDerivative_zero (σ h ζ η : Fin m→ℝ) (i : Fin m) (y : ℝ) :
    winnerKernelDerivative σ h ζ η i 0 y=∑j∈Finset.univ.erase i,derivativeTerm σ h ζ η i j y := by
  simp only [winnerKernelDerivative,parameterLine_zero,derivativeTerm,otherProduct,gaussianCDF,standardized]

def massFlux (σ h ζ η : Fin m→ℝ) (i : Fin m) : ℝ :=
  ∑j∈Finset.univ.erase i,∫x,hazardPairDensity σ h x i j*
    (transportSpeed (σ i) (h i) (ζ i) (η i) x-transportSpeed (σ j) (h j) (ζ j) (η j) x)

theorem kernelDerivative_integral_eq_massFlux (σ h ζ η : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (i : Fin (n+1)) :
    (∫y,winnerKernelDerivative σ h ζ η i 0 y ∂gaussianReal 0 1)=massFlux σ h ζ η i := by
  simp_rw [winnerKernelDerivative_zero]
  rw [integral_finset_sum _ (fun j hj=>derivativeTerm_integrable σ h ζ η i j)]
  unfold massFlux
  apply Finset.sum_congr rfl
  intro j hj
  have hij:i≠j:=Ne.symm (Finset.mem_erase.mp hj).1
  simp_rw [derivativeTerm_eq_transport σ h ζ η hσ i j]
  rw [gaussian_affine_integral (σ i) (h i) (hσ i)
    (fun x=>gaussianDensity (σ j) (h j) x*otherProduct σ h i j x*
      (transportSpeed (σ i) (h i) (ζ i) (η i) x-transportSpeed (σ j) (h j) (ζ j) (η j) x))]
  apply integral_congr_ae
  filter_upwards with x
  rw [hazardPairDensity_eq_product σ h i j hij x]
  ring

/-- Exact actual diagonal row/offset first variation. Every label is retained
and the physical threshold density is derived from the fixed Gaussian law. -/
theorem mass_diagonal_affine_hasDerivAt (σ h ζ η : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (i : Fin (n+1)) :
    HasDerivAt (fun t=>mass (diagonalRows (parameterLine σ ζ t)) (parameterLine h η t) i)
      (massFlux σ h ζ η i) 0 := by
  rw [←kernelDerivative_integral_eq_massFlux σ h ζ η hσ i]
  exact mass_diagonal_affine_hasDerivAt_kernel σ h ζ η hσ i

theorem diagonalRows_parameterLine (σ ζ : Fin m→ℝ) (t : ℝ) :
    diagonalRows (parameterLine σ ζ t)=diagonalRows σ+t • diagonalRows ζ := by
  ext i k
  by_cases hik:i=k
  · subst k
    simp [diagonalRows,parameterLine]
  · simp [diagonalRows,parameterLine,Pi.single,hik,Ne.symm hik,Function.update]

theorem diagonalRows_parameterLine_hasDerivAt (σ ζ : Fin m→ℝ) :
    HasDerivAt (fun t=>diagonalRows (parameterLine σ ζ t)) (diagonalRows ζ) 0 := by
  simp_rw [diagonalRows_parameterLine]
  simpa only [id_eq,one_smul] using
    ((hasDerivAt_id (0:ℝ)).smul_const (diagonalRows ζ)).const_add (diagonalRows σ)

theorem parameterLine_hasDerivAt (h η : Fin m→ℝ) :
    HasDerivAt (parameterLine h η) η 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [parameterLine,id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (η j)).const_add (h j)

/-- The threshold-flux integral is the actual joint mass derivative evaluated
on the literal diagonal row velocity and arbitrary offset velocity. -/
theorem jointMassDerivativeAt_diagonal (σ h ζ η : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (i : Fin (n+1)) :
    NegativeVotingFanJointMass.jointMassDerivativeAt (diagonalRows σ) h i (diagonalRows ζ,η)=
      massFlux σ h ζ η i := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  have hp:=(diagonalRows_parameterLine_hasDerivAt σ ζ).prodMk (parameterLine_hasDerivAt h η)
  have hD : HasFDerivAt (fun q : NegativeVotingFanScore.Parameters (n+1) (Fin (n+1))=>mass q.1 q.2 i)
      (NegativeVotingFanJointMass.jointMassDerivativeAt (diagonalRows σ) h i)
      (diagonalRows (parameterLine σ ζ 0),parameterLine h η 0):=by
    rw [parameterLine_zero,parameterLine_zero]
    exact NegativeVotingFanJointMass.hasFDerivAt_mass_joint_component (diagonalRows σ) h b hb hB i
  have hd:=hD.comp_hasDerivAt 0 hp
  exact hd.unique (mass_diagonal_affine_hasDerivAt σ h ζ η hσ i)

/-- The actual globally selected balancing offsets have a derivative along
every diagonal variance path; this uses the proved local mass inverse. -/
theorem selected_diagonal_contDiffAt (σ ζ : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    ContDiffAt ℝ 1 (fun t=>selectedOffsets (diagonalRows (parameterLine σ ζ t)) p) 0 := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  have hC:=selectedOffsets_joint_C1 (diagonalRows σ) b hb hB p hp hs
  have hP : ContDiffAt ℝ 1 (fun t:ℝ=>(diagonalRows (parameterLine σ ζ t),
      (0:NegativeVotingFanInverse.centeredGauge (Fin (n+1))))) 0:=by
    apply ContDiffAt.prodMk
    · simp_rw [diagonalRows_parameterLine]
      exact contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    · exact contDiffAt_const
  have hC' : ContDiffAt ℝ 1 (fun q:NegativeVotingFanJointInverse.JointCoordinates (n+1) (Fin (n+1))=>
      selectedOffsets q.1 (p+(q.2:Fin (n+1)→ℝ)))
      (diagonalRows (parameterLine σ ζ 0),(0:NegativeVotingFanInverse.centeredGauge (Fin (n+1)))):=by
    simpa only [parameterLine_zero] using hC
  simpa only [Function.comp_def,Submodule.coe_zero,add_zero] using hC'.comp (f:=fun t:ℝ=>(diagonalRows (parameterLine σ ζ t),(0:NegativeVotingFanInverse.centeredGauge (Fin (n+1))))) (0:ℝ) hP

/-- The actual balanced diagonal path obeys the full threshold-flux equation.
The derivative `k` is constructed from the selected offsets; no balancing
velocity or derivative formula is assumed. -/
theorem exists_selected_diagonal_derivative_flux (σ ζ : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    ∃k : NegativeVotingFanInverse.centeredGauge (Fin (n+1)),
      HasDerivAt (fun t=>selectedOffsets (diagonalRows (parameterLine σ ζ t)) p) k 0 ∧
      ∀i,massFlux σ (selectedOffsets (diagonalRows σ) p) ζ k i=0 := by
  let f:=fun t:ℝ=>selectedOffsets (diagonalRows (parameterLine σ ζ t)) p
  have hf : DifferentiableAt ℝ f 0:=(selected_diagonal_contDiffAt σ ζ hσ p hp hs).differentiableAt (by norm_num)
  let k : NegativeVotingFanInverse.centeredGauge (Fin (n+1)):=deriv f (0:ℝ)
  refine ⟨k,hf.hasDerivAt,?_⟩
  intro i
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  have hco:HasDerivAt (fun t=>(f t:Fin (n+1)→ℝ)) (k:Fin (n+1)→ℝ) 0:=by
    exact (NegativeVotingFanInverse.centeredGauge (Fin (n+1))).subtypeL.hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt
  have hD : HasFDerivAt (fun q:NegativeVotingFanScore.Parameters (n+1) (Fin (n+1))=>mass q.1 q.2 i)
      (NegativeVotingFanJointMass.jointMassDerivativeAt (diagonalRows σ) (selectedOffsets (diagonalRows σ) p) i)
      (diagonalRows (parameterLine σ ζ 0),(f 0:Fin (n+1)→ℝ)):=by
    simp only [f,parameterLine_zero]
    exact NegativeVotingFanJointMass.hasFDerivAt_mass_joint_component _ _ b hb hB i
  have hd:=hD.comp_hasDerivAt 0 ((diagonalRows_parameterLine_hasDerivAt σ ζ).prodMk hco)
  rw [jointMassDerivativeAt_diagonal σ _ ζ _ hσ i] at hd
  have hconst : HasDerivAt (fun t:ℝ=>p i) (massFlux σ (selectedOffsets (diagonalRows σ) p) ζ k i) 0:=by
    apply hd.congr_of_eventuallyEq
    have hnear : ∀ᶠ t in 𝓝 (0:ℝ),∀j,0<parameterLine σ ζ t j:=by
      rw [Filter.eventually_all]
      intro j
      have hc:ContinuousAt (fun t=>parameterLine σ ζ t j) 0:=by unfold parameterLine;fun_prop
      exact hc.eventually (lt_mem_nhds (by simpa [parameterLine] using hσ j))
    filter_upwards [hnear] with t ht
    exact (congrFun (selectedOffsets_mass _ (diagonalRows_injective _ ht) p hp hs) i).symm
  exact hconst.unique (hasDerivAt_const 0 (p i))

end NegativeVotingDiagonalBalancedDerivative
