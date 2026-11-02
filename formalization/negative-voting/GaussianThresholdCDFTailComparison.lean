import GaussianThresholdCDFDerivative
import GaussianOrthantTraceAlgebra
import GaussianFanRetainedCoefficient
import GaussianSummedTaylorRemainder

/-! Actual Gaussian event tails and the finite CDF comparison along a
centered symmetric square-root path. The row cap is derived from the unit
endpoint rows. -/
noncomputable section
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingThresholdCDFTailComparison
open NegativeVotingThresholdCDFDerivative NegativeVotingThresholdFan
  NegativeVotingAffineNormControl NegativeVotingAffineLogMassBound
  NegativeVotingQuadraticBulkNorm NegativeVotingOrthantTraceAlgebra
  NegativeVotingFanRetained NegativeVotingGaussianTail WeakSimplex
  NegativeVotingSummedTaylorRemainder
variable {d:ℕ}

lemma gaussian_upper_halfspace_le (v:FSC.Coord d) (hv:‖v‖≤1)
    (t:ℝ) (ht:0≤t) :
    (stdGaussian (FSC.Coord d)).real {x|t< inner ℝ v x}≤Real.exp (-t^2/2) := by
  by_cases hz:v=0
  · subst v
    have he:({x:FSC.Coord d|t< inner ℝ (0:FSC.Coord d) x}:Set (FSC.Coord d))=∅:=by
      ext x;simp [not_lt.mpr ht]
    rw [he,measureReal_empty]
    positivity
  · have hn:0<‖v‖:=norm_pos_iff.mpr hz
    let w:FSC.Coord d:=‖v‖⁻¹•v
    have hw:‖w‖=1:=by simp [w,norm_smul,abs_of_pos (inv_pos.mpr hn),ne_of_gt hn]
    have he (x:FSC.Coord d):inner ℝ v x=‖v‖*inner ℝ w x:=by
      simp only [w,real_inner_smul_left]
      field_simp
    have hsub:{x:FSC.Coord d|t< inner ℝ v x}⊆{x|inner ℝ (-w) x≤ -t}:=by
      intro x hx
      change t< inner ℝ v x at hx
      rw [he] at hx
      have hq:0< inner ℝ w x:=by nlinarith
      change inner ℝ (-w) x≤ -t
      rw [inner_neg_left]
      nlinarith
    have hm:=(measureReal_mono hsub :
      (stdGaussian (FSC.Coord d)).real {x|t< inner ℝ v x}≤
      (stdGaussian (FSC.Coord d)).real {x|inner ℝ (-w) x≤ -t})
    simp only [Measure.real_def,gaussian_unit_lower_halfspace (-w) (by simpa using hw)] at hm
    exact hm.trans ((normalTail_le_half_exp t ht).trans (by nlinarith [Real.exp_pos (-t^2/2)]))

lemma gaussian_lower_halfspace_le (v:FSC.Coord d) (hv:‖v‖≤1)
    (t:ℝ) (ht:t≤0) :
    (stdGaussian (FSC.Coord d)).real {x|inner ℝ v x≤t}≤Real.exp (-t^2/2) := by
  by_cases ht0:t=0
  · subst t
    simpa only [zero_pow (by norm_num : 2≠0),neg_zero,zero_div,Real.exp_zero] using
      (measureReal_le_one : (stdGaussian (FSC.Coord d)).real {x|inner ℝ v x≤0}≤1)
  have htneg:t<0:=lt_of_le_of_ne ht ht0
  by_cases hz:v=0
  · subst v
    have he:({x:FSC.Coord d|inner ℝ (0:FSC.Coord d) x≤t}:Set (FSC.Coord d))=∅:=by
      ext x;simp [not_le.mpr htneg]
    rw [he,measureReal_empty]
    positivity
  · have hn:0<‖v‖:=norm_pos_iff.mpr hz
    let w:FSC.Coord d:=‖v‖⁻¹•v
    have hw:‖w‖=1:=by simp [w,norm_smul,abs_of_pos (inv_pos.mpr hn),ne_of_gt hn]
    have he (x:FSC.Coord d):inner ℝ v x=‖v‖*inner ℝ w x:=by
      simp only [w,real_inner_smul_left]
      field_simp
    have hsub':{x:FSC.Coord d|inner ℝ v x≤t}⊆{x|inner ℝ w x≤t}:=by
      intro x hx
      change inner ℝ v x≤t at hx
      rw [he] at hx
      have hq:inner ℝ w x<0:=by nlinarith
      change inner ℝ w x≤t
      nlinarith
    have hm:=(measureReal_mono hsub' :
      (stdGaussian (FSC.Coord d)).real {x|inner ℝ v x≤t}≤
      (stdGaussian (FSC.Coord d)).real {x|inner ℝ w x≤t})
    simp only [Measure.real_def,gaussian_unit_lower_halfspace w hw] at hm
    have hh:=normalTail_le_half_exp (-t) (by linarith)
    simp only [neg_neg,neg_sq] at hh
    exact hm.trans (hh.trans (by nlinarith [Real.exp_pos (-t^2/2)]))

lemma path_row_norm_le (F:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1)
    (s:ℝ) (hs:s∈Icc 0 1) (i:Fin d) :
    ‖(nearIdentityMap F s).adjoint (EuclideanSpace.basisFun (Fin d) ℝ i)‖≤1 := by
  let e:=EuclideanSpace.basisFun (Fin d) ℝ i
  have he:‖e‖=1:=(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one i
  have hr:‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint e‖=1:=by
    have hh:=hrow i
    nlinarith [norm_nonneg ((ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint e)]
  have hh:(nearIdentityMap F s).adjoint e=
      (1-s)•e+s•((ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint e):=by
    simp only [nearIdentityMap,map_add,map_smul,ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
      smul_add,sub_smul,one_smul]
    module
  rw [hh]
  calc
    _≤‖(1-s)•e‖+‖s•((ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint e)‖:=norm_add_le _ _
    _=1:=by rw [norm_smul,norm_smul,he,hr,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hs.2] : 0≤1-s),abs_of_nonneg hs.1];ring

lemma event_compl_tail (T:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hrow:∀i,‖T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ i)‖≤1)
    (t:ℝ) (ht:0≤t) :
    (stdGaussian (FSC.Coord d)).real (T ⁻¹' (orthant t))ᶜ≤(d:ℝ)*Real.exp (-t^2/2) := by
  have he:(T ⁻¹' (orthant t))ᶜ=⋃i:Fin d,{x|t< inner ℝ (T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ i)) x}:=by
    ext x
    simp only [Set.mem_compl_iff,Set.mem_preimage,orthant,Set.mem_setOf_eq,not_forall,
      not_le,Set.mem_iUnion,ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner]
  rw [he]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  have hh:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin d)))=>
    gaussian_upper_halfspace_le _ (hrow i) t ht)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh

lemma event_lower_tail (T:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hrow:∀i,‖T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ i)‖≤1)
    (a:Fin d) (t:ℝ) (ht:t≤0) :
    (stdGaussian (FSC.Coord d)).real (T ⁻¹' (orthant t))≤Real.exp (-t^2/2) := by
  have hsub:T ⁻¹' (orthant t)⊆{x|inner ℝ (T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ a)) x≤t}:=by
    intro x hx
    change inner ℝ (T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ a)) x≤t
    rw [ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner]
    exact hx a
  exact (measureReal_mono hsub).trans (gaussian_lower_halfspace_le _ (hrow a) t ht)

lemma sqrt_probability_tail {p:ℝ} (hp:0≤p) (t:ℝ)
    (h:p≤((d:ℝ)+1)^2*Real.exp (-t^2/2)) :
    Real.sqrt p≤((d:ℝ)+1)*Real.exp (-t^2/4) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  convert h using 1
  rw [mul_pow,←Real.exp_nat_mul]
  congr 2
  ring

lemma event_min_sqrt_tail (T:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hrow:∀i,‖T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ i)‖≤1)
    (a:Fin d) (t:ℝ) :
    Real.sqrt (min ((stdGaussian (FSC.Coord d)).real (T ⁻¹' (orthant t)))
      ((stdGaussian (FSC.Coord d)).real (T ⁻¹' (orthant t))ᶜ))≤
      ((d:ℝ)+1)*Real.exp (-t^2/4) := by
  apply sqrt_probability_tail (le_min measureReal_nonneg measureReal_nonneg)
  by_cases ht:0≤t
  · exact (min_le_right _ _).trans ((event_compl_tail T hrow t ht).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) d]) (Real.exp_pos _).le))
  · exact (min_le_left _ _).trans ((event_lower_tail T hrow a t (le_of_not_ge ht)).trans
      (by
        have hh:(1:ℝ)≤((d:ℝ)+1)^2:=by nlinarith [Nat.cast_nonneg (α:=ℝ) d]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (Real.exp_pos (-t^2/2)).le))

lemma cdfSecond_abs_tail (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:‖F‖≤1/2)
    (hFs:F.toLinearMap.IsSymmetric)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1)
    (a:Fin d) (t s:ℝ) (hs:s∈Icc 0 1) :
    |deriv (cdfFirst F t) s|≤580*(operatorHilbertSchmidt F)^2*((d:ℝ)+1)*Real.exp (-t^2/4) := by
  have hsa:|s|≤1:=by rw [abs_of_nonneg hs.1];exact hs.2
  have h₁:=cdfSecond_abs_le F hF hFs t s hsa
  have h₂:=cdfSecond_abs_le_compl F hF hFs t s hsa
  let p:ℝ:=(stdGaussian (FSC.Coord d)).real ((nearIdentityMap F s) ⁻¹' (orthant t))
  let q:ℝ:=(stdGaussian (FSC.Coord d)).real ((nearIdentityMap F s) ⁻¹' (orthant t))ᶜ
  have hm:|deriv (cdfFirst F t) s|≤580*(operatorHilbertSchmidt F)^2*Real.sqrt (min p q):=by
    rcases le_total p q with h|h
    · rw [min_eq_left h];exact h₁
    · rw [min_eq_right h];exact h₂
  have ht:=event_min_sqrt_tail (nearIdentityMap F s) (path_row_norm_le F hrow s hs) a t
  exact hm.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by ring))

lemma cdfFirst_zero_abs_tail (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:‖F‖≤1/2)
    (hFs:F.toLinearMap.IsSymmetric) (hones:F (ones d)=0)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1)
    (a b:Fin d) (hab:a≠b) (t:ℝ) :
    |cdfFirst F t 0|≤2*(operatorHilbertSchmidt F)^2*((d:ℝ)+1)*Real.exp (-t^2/4) := by
  rw [cdfFirst_zero_eq F hF t]
  have hs:=orthant_setIntegral_unit_rows_abs_le t a b hab F hFs hones hrow
  have ht:=event_min_sqrt_tail (ContinuousLinearMap.id ℝ (FSC.Coord d))
    (by intro i;simp only [ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply,
      (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one];exact le_rfl) a t
  exact hs.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by ring))

/-- Actual finite comparison, not an assumed CDF stability input. The
alphabet loss is only linear and the entire threshold dependence is Gaussian. -/
theorem cdfPath_endpoint_abs_le (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:‖F‖≤1/2)
    (hFs:F.toLinearMap.IsSymmetric) (hones:F (ones d)=0)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1)
    (a b:Fin d) (hab:a≠b) (t:ℝ) :
    |cdfPath F t 1-cdfPath F t 0|≤
      600*((d:ℝ)+1)*(operatorHilbertSchmidt F)^2*Real.exp (-t^2/4) := by
  have hfirst (s:ℝ) (hs:s∈Icc 0 1):HasDerivAt (cdfPath F t) (cdfFirst F t s) s:=
    cdfPath_hasDerivAt F hF t s (by rw [abs_of_nonneg hs.1];exact hs.2)
  have hsecond (s:ℝ) (hs:s∈Icc 0 1):HasDerivAt (cdfFirst F t) (deriv (cdfFirst F t) s) s:=
    (cdfFirst_hasDerivAt F hF hFs t s (by rw [abs_of_nonneg hs.1];exact hs.2)).differentiableAt.hasDerivAt
  have hr:=scalar_second_remainder_le (cdfPath F t) (cdfFirst F t) (deriv (cdfFirst F t)) 1
    (580*(operatorHilbertSchmidt F)^2*((d:ℝ)+1)*Real.exp (-t^2/4))
    (by norm_num) (by positivity) hfirst hsecond (cdfSecond_abs_tail F hF hFs hrow a t)
  have hi:=cdfFirst_zero_abs_tail F hF hFs hones hrow a b hab t
  have htri:|cdfPath F t 1-cdfPath F t 0|≤
      |cdfPath F t 1-cdfPath F t 0-cdfFirst F t 0|+|cdfFirst F t 0|:=by
    simpa only [sub_add_cancel] using abs_add_le
      (cdfPath F t 1-cdfPath F t 0-cdfFirst F t 0) (cdfFirst F t 0)
  simp only [one_mul,one_pow,mul_one] at hr
  have hpos:0≤((d:ℝ)+1)*(operatorHilbertSchmidt F)^2*Real.exp (-t^2/4):=by positivity
  nlinarith only [hr,hi,htri,hpos]

/-- Direct measure formulation for the endpoint Gaussian maximum CDFs. -/
theorem actual_CDF_difference_abs_le (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:‖F‖≤1/2)
    (hFs:F.toLinearMap.IsSymmetric) (hones:F (ones d)=0)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1)
    (a b:Fin d) (hab:a≠b) (t:ℝ) :
    |(stdGaussian (FSC.Coord d)).real
        ((ContinuousLinearMap.id ℝ (FSC.Coord d)+F) ⁻¹' (orthant t))-
      (stdGaussian (FSC.Coord d)).real (orthant t)|≤
      600*((d:ℝ)+1)*(operatorHilbertSchmidt F)^2*Real.exp (-t^2/4) := by
  have hh:=cdfPath_endpoint_abs_le F hF hFs hones hrow a b hab t
  rw [cdfPath_eq_measure F hF t 1 (by norm_num),cdfPath_eq_measure F hF t 0 (by norm_num)] at hh
  simpa [nearIdentityMap] using hh

end NegativeVotingThresholdCDFTailComparison
