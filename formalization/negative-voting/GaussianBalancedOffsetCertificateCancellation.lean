import GaussianGlobalTensorTransport
import GaussianFanSecondVariation
import GaussianBalancedOffsetComparison
import GaussianConditionedFacetGeneral
import GaussianBalancedMomentGeometry
import GaussianRegularTransportProducts

/-! Exact straight-offset cancellation for the literal Gaussian quadratic
certificate. Differentiating the tested cells directly avoids introducing
and separately estimating the cancelling terminal maximum derivatives. -/
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedOffsetCertificateCancellation
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanQuadraticMoments NegativeVotingSecondChaosFacetGradient
  NegativeVotingGlobalTensorTransport NegativeVotingFanHessian NegativeVotingCapTail
  NegativeVotingFanJacobian NegativeVotingWeightedFacet NegativeVotingFacetDegree
  NegativeVotingConditionedFacet NegativeVotingRegularTransportProducts
  NegativeVotingPolynomialFacetLogBound NegativeVotingBalancedMomentGeometry
  NegativeVotingDisintegration
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def scoreSquareSum (B : ι→FSC.Coord d) (h : ι→ℝ) : ℝ :=
  ∑i,∫x in winningCell B h i,(inner ℝ (B i) x)^2 ∂stdGaussian (FSC.Coord d)

theorem scoreSquare_growth (v x : FSC.Coord d) :
    |(inner ℝ v x)^2| ≤ ‖v‖^2*(1+‖x‖^2) := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh:=pow_le_pow_left₀ (abs_nonneg (inner ℝ v x)) (abs_real_inner_le_norm v x) 2
  rw [sq_abs] at hh
  nlinarith [sq_nonneg ‖v‖]

theorem scoreSquare_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ] (v : FSC.Coord d) :
    Integrable (fun x=>(inner ℝ v x)^2) μ := by
  have hh:=(IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) v
  convert hh.integrable_mul hh using 1
  funext x
  simp only [Pi.mul_apply,id_eq,sq]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem offset_square_gap_on_facet (B : ι→FSC.Coord d) (h : ι→ℝ)
    (t : ℝ) (i j : ι) (x : FSC.Coord d) (hx : x∈affineFacet B (t•h) i j) :
    ((inner ℝ (B i) x)^2-(inner ℝ (B j) x)^2)*(h i-h j)=
      -t*(h i-h j)^2*inner ℝ (B i+B j) x := by
  have hh:=hx.1
  simp only [affineScore,Pi.smul_apply,smul_eq_mul] at hh
  have he : inner ℝ (B i) x-inner ℝ (B j) x = -t*(h i-h j):=by linarith
  rw [sq_sub_sq,he]
  rw [inner_add_left]
  ring

/-- The first variation of the actual quadratic certificate, with its
offset factor exposed before taking absolute values. Ordered facets carry
the factor one half. No derivative identity is an assumption. -/
theorem hasDerivAt_scoreSquareSum_offset (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (t : ℝ) :
    HasDerivAt (fun s:ℝ=>scoreSquareSum B (s•h))
      (-t/2*∑i,∑j,(h i-h j)^2*
        surfaceIntegral B (t•h) i j (fun x=>inner ℝ (B i+B j) x)) t := by
  have hp : HasDerivAt (fun s:ℝ=>(B,s•h)) (0,h) t := by
    simpa only [one_smul,id_eq] using (hasDerivAt_const t B).prodMk ((hasDerivAt_id t).smul_const h)
  have hi i : HasDerivAt (fun s:ℝ=>
      ∫x in winningCell B (s•h) i,(inner ℝ (B i) x)^2 ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B (t•h) i (fun x=>(inner ℝ (B i) x)^2) (0,h)) t := by
    have hfi:=NegativeVotingFanQuadraticMoments.hasFDerivAt_testedCell B (t•h) σ hσ hlower i
      (fun x=>(inner ℝ (B i) x)^2) (by fun_prop) (‖B i‖^2) (sq_nonneg _)
      (scoreSquare_growth (B i))
    simpa only [Function.comp_def] using hfi.comp_hasDerivAt t hp
  have hd:=HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>hi i)
  change HasDerivAt (fun s:ℝ=>scoreSquareSum B (s•h)) _ t at hd
  apply hd.congr_deriv
  have he i := testedCellDerivative_apply_surface B (t•h) σ hσ hlower i
    (fun x=>(inner ℝ (B i) x)^2) (by fun_prop) (‖B i‖^2) (sq_nonneg _)
    (scoreSquare_growth (B i)) 0 h
  simp only [affineScore,Pi.zero_apply,inner_zero_left,zero_add] at he
  simp_rw [he]
  rw [surface_sum_label_gap B (t•h) (fun i x=>(inner ℝ (B i) x)^2)
    (fun i j _=>h i-h j) (fun i j _=>by ring) (fun i j k=>by
      let :=NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B (t•h) i j)
      exact (scoreSquare_integrable _ (B k)).mul_const _)]
  have heq i j : surfaceIntegral B (t•h) i j
      (fun x=>((inner ℝ (B i) x)^2-(inner ℝ (B j) x)^2)*(h i-h j))=
      (-t*(h i-h j)^2)*surfaceIntegral B (t•h) i j (fun x=>inner ℝ (B i+B j) x):=by
    rw [←surfaceIntegral_const_mul]
    unfold surfaceIntegral
    congr 1
    apply setIntegral_congr_fun (isClosed_affineFacet B (t•h) i j).measurableSet
    intro x hx
    exact offset_square_gap_on_facet B h t i j x hx
  simp_rw [heq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def offsetFirst (B : ι→FSC.Coord d) (h : ι→ℝ) (t : ℝ) : ℝ :=
  jointDerivative B (t•h) (0,h)

omit [DecidableEq ι] in
theorem hasDerivAt_offsetValue (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hB : Function.Injective B) (t : ℝ) :
    HasDerivAt (fun s:ℝ=>expectedMax B (s•h)) (offsetFirst B h t) t := by
  have hp : HasDerivAt (fun s:ℝ=>(B,s•h)) (0,h) t := by
    simpa only [one_smul,id_eq] using (hasDerivAt_const t B).prodMk ((hasDerivAt_id t).smul_const h)
  exact (hasFDerivAt_expectedMax_joint B hB (t•h)).comp_hasDerivAt t hp

theorem hasDerivAt_offsetFirst (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (t : ℝ) :
    HasDerivAt (offsetFirst B h) (quadraticForm B (t•h) 0 h) t := by
  have hp : HasDerivAt (fun s:ℝ=>(B,s•h)) (0,h) t := by
    simpa only [one_smul,id_eq] using (hasDerivAt_const t B).prodMk ((hasDerivAt_id t).smul_const h)
  have hh:=(hasFDerivAt_jointDerivative_apply B (t•h) σ hσ hlower 0 h).comp_hasDerivAt t hp
  change HasDerivAt (offsetFirst B h) (secondDerivative B (t•h) 0 h (0,h)) t at hh
  rwa [secondDerivative_apply_eq_mixedForm B 0 0 (t•h) h h σ hσ hlower,mixedForm_self] at hh

omit [DecidableEq ι] in
theorem offsetFirst_terminal_zero (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hcenter : ∑i,h i=0) (hbalanced : ∀i,mass B h i=(Fintype.card ι:ℝ)⁻¹) :
    offsetFirst B h 1=0 := by
  simp only [offsetFirst,one_smul,jointDerivative_apply,Pi.zero_apply,inner_zero_left,zero_add,hbalanced,
    ←Finset.mul_sum,hcenter,mul_zero]

/-- Scalar payment by the exact terminal offset minimization drop. This is
proved by differentiating `T+C(F-t F')`; no integral regularity is assumed. -/
theorem scalar_offset_upper (F F₁ T T₁ Q : ℝ→ℝ) (C : ℝ)
    (hF : ∀t,HasDerivAt F (F₁ t) t)
    (hF₁ : ∀t,HasDerivAt F₁ (Q t) t)
    (hT : ∀t,HasDerivAt T (T₁ t) t)
    (hterminal : F₁ 1=0)
    (hbound : ∀t∈Icc (0:ℝ) 1,T₁ t ≤ C*t*Q t) :
    T 1-T 0 ≤ C*(F 0-F 1) := by
  have hd t : HasDerivAt (fun s:ℝ=>T s+C*(F s-s*F₁ s)) (T₁ t-C*t*Q t) t:=by
    convert (hT t).add (((hF t).sub ((hasDerivAt_id t).mul (hF₁ t))).const_mul C) using 1
    · rfl
    · simp only [id_eq,one_mul];ring
  have ha:=antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 1)
    (fun t _=>(hd t).continuousAt.continuousWithinAt)
    (fun t _=>(hd t).differentiableAt.differentiableWithinAt)
    (fun t ht=>by rw [(hd t).deriv];linarith [hbound t (interior_subset ht)])
  have hh:=ha (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (1:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)≤1)
  simp only [hterminal,mul_zero,zero_mul,sub_zero] at hh
  linarith

theorem scalar_offset_payment (F F₁ T T₁ Q : ℝ→ℝ) (C : ℝ)
    (hF : ∀t,HasDerivAt F (F₁ t) t)
    (hF₁ : ∀t,HasDerivAt F₁ (Q t) t)
    (hT : ∀t,HasDerivAt T (T₁ t) t)
    (hterminal : F₁ 1=0)
    (hbound : ∀t∈Icc (0:ℝ) 1,|T₁ t| ≤ C*t*Q t) :
    |T 1-T 0| ≤ C*(F 0-F 1) := by
  have hu:=scalar_offset_upper F F₁ T T₁ Q C hF hF₁ hT hterminal
    (fun t ht=>(le_abs_self _).trans (hbound t ht))
  have hl:=scalar_offset_upper F F₁ (fun t=>-T t) (fun t=>-T₁ t) Q C hF hF₁
    (fun t=>(hT t).neg) hterminal (fun t ht=>(neg_le_abs _).trans (hbound t ht))
  apply abs_le.mpr
  constructor <;> linarith

/-- An actual surface first-moment bound pays the entire affine offset
correction by its actual value drop. The geometric surface bound remains
explicit; neither the final second-energy comparison nor its deficit is an
assumption. In particular no offset-independent additive tail is introduced. -/
theorem scoreSquareSum_offset_abs_le_drop (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (hcenter : ∑i,h i=0) (hbalanced : ∀i,mass B h i=(Fintype.card ι:ℝ)⁻¹)
    (C : ℝ)
    (hfacet : ∀t∈Icc (0:ℝ) 1,∀i j,
      |surfaceIntegral B (t•h) i j (fun x=>inner ℝ (B i+B j) x)| ≤
        C*facetWeight B (t•h) i j) :
    |scoreSquareSum B h-scoreSquareSum B 0| ≤ C*(expectedMax B 0-expectedMax B h) := by
  have hB : Function.Injective B:=fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hQ (t:ℝ) : quadraticForm B (t•h) 0 h=
      (1/2:ℝ)*∑i,∑j,facetWeight B (t•h) i j*(h i-h j)^2:=by
    unfold quadraticForm
    simp only [affineScore,Pi.zero_apply,inner_zero_left,zero_add,surfaceIntegral_const]
  have hh:=scalar_offset_payment
    (fun t:ℝ=>expectedMax B (t•h)) (offsetFirst B h)
    (fun t:ℝ=>scoreSquareSum B (t•h))
    (fun t:ℝ=>-t/2*∑i,∑j,(h i-h j)^2*
      surfaceIntegral B (t•h) i j (fun x=>inner ℝ (B i+B j) x))
    (fun t:ℝ=>quadraticForm B (t•h) 0 h) C
    (hasDerivAt_offsetValue B h hB) (hasDerivAt_offsetFirst B h σ hσ hlower)
    (hasDerivAt_scoreSquareSum_offset B h σ hσ hlower)
    (offsetFirst_terminal_zero B h hcenter hbalanced) (by
      intro t ht
      rw [abs_mul,abs_div,abs_neg,abs_of_nonneg ht.1,abs_of_pos (by norm_num : (0:ℝ)<2),hQ]
      have hsum : |∑i,∑j,(h i-h j)^2*surfaceIntegral B (t•h) i j (fun x=>inner ℝ (B i+B j) x)| ≤
          ∑i,∑j,(h i-h j)^2*(C*facetWeight B (t•h) i j):=by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hfacet t ht i j) (sq_nonneg _)
      calc
        _ ≤ t/2*(∑i,∑j,(h i-h j)^2*(C*facetWeight B (t•h) i j)):=
          mul_le_mul_of_nonneg_left hsum (div_nonneg ht.1 (by norm_num))
        _ = _ := by simp only [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
                    apply Finset.sum_congr rfl;intro j _;ring)
  simpa only [one_smul,zero_smul] using hh

/-- The conditioned-facet lower bound holds along the entire straight
offset segment, although its intermediate cell masses need not be balanced.
Only the terminal masses are used to obtain the offset bound. -/
theorem intrinsicProbability_lower_offset_segment
    (B : ι→FSC.Coord d) (hm : 3 ≤ Fintype.card ι)
    (σ D : ℝ) (hσ : 0<σ) (hD : 0<D)
    (hlower : CenteredSingularLowerBound B σ) (hrow : ∀i j,‖B i-B j‖ ≤ D)
    (hcond : D/σ ≤ 4) (h : ι→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,1/(2*(Fintype.card ι:ℝ)) ≤ mass B h i)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (i j : ι) (hij : i≠j) :
    (Fintype.card ι:ℝ)^(-4096:ℝ) ≤ intrinsicProbability B (t•h) i j := by
  let m : ℝ:=Fintype.card ι
  let E:=(6*(2*offsetRadius (V:=ι) D+unionRadius (V:=ι) D)^2+
    2*(offsetRadius (V:=ι) D)^2)/σ^2
  have hm3 : (3:ℝ) ≤ m:=by dsimp [m];exact_mod_cast hm
  have hmpos : 0 < m:=by linarith
  have hinj : Function.Injective B:=fun a b he=>by
    by_contra hab
    exact centered_singular_rows_ne B σ hσ hlower a b hab he
  have hoff k : |(t•h) k| ≤ offsetRadius (V:=ι) D:=by
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans
      (centered_offsets_le_of_cell_masses B h hinj D hD.le hrow hs hmass k)
  have hE : E ≤ 3584*Real.log m:=witness_exponent_le_log hm σ D hσ hD hcond
  have hp : (1/4:ℝ)*Real.exp (-E) ≤ intrinsicProbability B (t•h) i j:=by
    simpa only [E,neg_div] using
      NegativeVotingConditionedFacetGeneral.intrinsicProbability_exp_lower_uniform B hm σ D
        (offsetRadius (V:=ι) D) hσ hD (offsetRadius_nonneg D hD.le) hlower hrow (t•h) hoff i j hij
  have hquarter : Real.exp (-(2*Real.log m)) ≤ 1/4:=by
    have heq : Real.exp (-(2*Real.log m))=(m^2)⁻¹:=by
      have hlp : Real.log (m^2)=2*Real.log m:=Real.log_pow m 2
      rw [←hlp,Real.exp_neg,Real.exp_log (sq_pos_of_pos hmpos)]
    rw [heq]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4)
      (show (4:ℝ) ≤ m^2 by nlinarith)
  calc
    _ = Real.exp (-(4096*Real.log m)):=by rw [Real.rpow_def_of_pos hmpos];congr 1;ring
    _ ≤ Real.exp (-(2*Real.log m))*Real.exp (-E):=by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.log_nonneg (show 1 ≤ m by linarith)]
    _ ≤ (1/4:ℝ)*Real.exp (-E):=mul_le_mul_of_nonneg_right hquarter (Real.exp_pos _).le
    _ ≤ _:=hp

/-- Fully geometric logarithmic payment of the actual affine-offset
quadratic certificate. The deliberately loose fourth log power is sufficient
for local rigidity; all Gaussian facet premises have been discharged. -/
theorem scoreSquareSum_offset_log_le_drop
    (B : ι→FSC.Coord d) (hm : 3 ≤ Fintype.card ι)
    (σ R : ℝ) (hσ : 0<σ) (hR : 0<R)
    (hlower : CenteredSingularLowerBound B σ) (hrow : ∀i,‖B i‖ ≤ R)
    (hcond : 2*R/σ ≤ 4) (h : ι→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=(Fintype.card ι:ℝ)⁻¹) :
    |scoreSquareSum B h-scoreSquareSum B 0| ≤
      (32*R*quarticLogConstant 2*(1+Real.log (Fintype.card ι:ℝ))^4)*
        (expectedMax B 0-expectedMax B h) := by
  apply scoreSquareSum_offset_abs_le_drop B h σ hσ hlower hs hmass
  intro t ht i j
  by_cases hij : i=j
  · subst j
    simp [surfaceIntegral_diagonal,facetWeight_self]
  have hinj : Function.Injective B:=fun a b he=>by
    by_contra hab
    exact centered_singular_rows_ne B σ hσ hlower a b hab he
  have hm1 : (1:ℝ) ≤ Fintype.card ι:=by exact_mod_cast Fintype.card_pos
  have hmlower a : 1/(2*(Fintype.card ι:ℝ)) ≤ mass B h a:=by
    rw [hmass]
    have hc : (0:ℝ)<Fintype.card ι:=by positivity
    simp only [one_div]
    apply inv_anti₀ hc
    linarith
  have hprob:=intrinsicProbability_lower_offset_segment B hm σ (2*R) hσ (by positivity)
    hlower (fun a b=>(norm_sub_le _ _).trans (by linarith [hrow a,hrow b])) hcond h hs
    hmlower t ht i j hij
  have ha : |pairOffset B (t•h) i j| ≤ 2*Real.sqrt (1+Real.log (Fintype.card ι:ℝ)):=by
    have hb:=pairOffset_le_of_uniform_mass B h hinj (fun a=>(hmass a).ge) i j hij
    have heq : pairOffset B (t•h) i j=t*pairOffset B h i j:=by
      unfold pairOffset
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [heq,abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans hb
  have hh:=surface_three_scores_abs_le B (t•h) i j (hinj.ne hij)
    (B i+B j) 0 0 0 1 1 2 (Fintype.card ι) hm1 hprob ha
  simp only [linearScore,inner_zero_left,zero_add,mul_one,coefficientEnergy,norm_zero,
    zero_add,one_pow,add_zero] at hh
  norm_num only [show (0:ℝ)^2=0 by norm_num,add_zero,zero_add,Real.sqrt_one,
    Real.sqrt_sq (norm_nonneg _),mul_one] at hh
  have hBi : ‖B i+B j‖ ≤ 2*R:=(norm_add_le _ _).trans (by linarith [hrow i,hrow j])
  have hw : 0 ≤ facetWeight B (t•h) i j*quarticLogConstant 2*(1+Real.log (Fintype.card ι:ℝ))^4:=by
    positivity [facetWeight_nonneg B (t•h) i j,show 0 ≤ quarticLogConstant 2 by unfold quarticLogConstant;positivity]
  have hb:=mul_le_mul_of_nonneg_left hBi (mul_nonneg (by norm_num : (0:ℝ)≤16) hw)
  exact hh.trans (by nlinarith only [hb])

end NegativeVotingBalancedOffsetCertificateCancellation
