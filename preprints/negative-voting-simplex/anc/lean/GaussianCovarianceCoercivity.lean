import GaussianCovarianceStrictConcavity

/-! Coercivity of the actual penalized covariance objective.  The row bound is
explicit: an arbitrary base affine basis is not silently treated as Parseval. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology
namespace NegativeVotingCovarianceCoercivity
open NegativeVotingPositiveCovariance NegativeVotingCovariancePath
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
  NegativeVotingFanCovarianceValue NegativeVotingFanValue NegativeVotingFan

section Operators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def operatorTrace (C : E →L[ℝ] E) : ℝ := LinearMap.trace ℝ E C.toLinearMap

theorem trace_nonneg {C : E →L[ℝ] E} (hC : C∈psdCone) : 0≤operatorTrace C := by
  classical
  rw [operatorTrace,LinearMap.trace_eq_sum_inner C.toLinearMap (stdOrthonormalBasis ℝ E)]
  exact Finset.sum_nonneg (fun i _ => hC.2 _)

theorem norm_le_trace {C : E →L[ℝ] E} (hC : C∈psdCone) : ‖C‖≤operatorTrace C := by
  classical
  let e := hC.1.eigenvectorBasis (n:=Module.finrank ℝ E) rfl
  let ev := hC.1.eigenvalues (n:=Module.finrank ℝ E) rfl
  have heq : diagonal e ev=C := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change diagonal e ev (e i)=C (e i)
    rw [diagonal_basis]
    exact (hC.1.apply_eigenvectorBasis rfl i).symm
  have hev (i) : 0≤ev i := by
    have hh:=hC.2 (e i)
    rw [←heq,diagonal_basis] at hh
    simpa only [real_inner_smul_right,e.inner_eq_ite,ite_true,mul_one] using hh
  have ht : operatorTrace C=∑ i,ev i := by
    rw [operatorTrace,LinearMap.trace_eq_sum_inner C.toLinearMap e]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ (e i) (C (e i))=ev i
    rw [←heq,diagonal_basis]
    simp only [real_inner_smul_right,e.inner_eq_ite,ite_true,mul_one]
  rw [ht,←heq]
  calc
    ‖diagonal e ev‖≤∑ i,‖ev i • InnerProductSpace.rankOne ℝ (e i) (e i)‖ :=
      norm_sum_le _ _
    _ =∑ i,ev i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hev i),e.norm_eq_one]

theorem continuous_operatorTrace : Continuous (operatorTrace (E:=E)) := by
  classical
  have he : operatorTrace (E:=E) = fun C =>
      ∑ i,inner ℝ ((stdOrthonormalBasis ℝ E) i) (C ((stdOrthonormalBasis ℝ E) i)) := by
    funext C
    exact LinearMap.trace_eq_sum_inner _ _
  rw [he]
  fun_prop

end Operators

section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_inner_sq (v : E) :
    (∫ x, (inner ℝ v x)^2 ∂stdGaussian E)=‖v‖^2 := by
  have hm : MemLp (innerSL ℝ v : E→ℝ) 2 (stdGaussian E) :=
    (innerSL ℝ v).comp_memLp' IsGaussian.memLp_two_id
  have hv := variance_dual_stdGaussian (innerSL ℝ v)
  rw [variance_eq_sub hm,integral_strongDual_stdGaussian,
    zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,innerSL_apply_norm] at hv
  simpa only [Pi.pow_apply,innerSL_apply_apply] using hv

theorem integral_norm_sq_eq_trace (R C : E →L[ℝ] E)
    (hR : R.toLinearMap.IsSymmetric) (hRC : R.comp R=C) :
    (∫ x, ‖R x‖^2 ∂stdGaussian E)=operatorTrace C := by
  classical
  let e:=stdOrthonormalBasis ℝ E
  have hm (i) : Integrable (fun x:E => (inner ℝ (e i) (R x))^2) (stdGaussian E) :=
    (((innerSL ℝ (e i)).comp R).comp_memLp' IsGaussian.memLp_two_id).integrable_sq
  have he (x:E) : ‖R x‖^2=∑ i,(inner ℝ (e i) (R x))^2 :=
    (e.sum_sq_inner_right (R x)).symm
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => hm i),operatorTrace,
    LinearMap.trace_eq_sum_inner C.toLinearMap e]
  apply Finset.sum_congr rfl
  intro i _
  have hfun : (fun x:E => inner ℝ (e i) (R x))=fun x=>inner ℝ (R (e i)) x := by
    funext x
    exact (hR _ _).symm
  have hpow : (fun x:E => (inner ℝ (e i) (R x))^2)=fun x=>(inner ℝ (R (e i)) x)^2 := by
    funext x
    rw [congrFun hfun x]
  rw [hpow,integral_inner_sq]
  calc
    ‖R (e i)‖^2=inner ℝ (R (e i)) (R (e i)) := (real_inner_self_eq_norm_sq _).symm
    _ =inner ℝ (e i) (R (R (e i))) := hR _ _
    _ =inner ℝ (e i) (C (e i)) := by rw [←ContinuousLinearMap.comp_apply,hRC]

theorem integral_norm_le_sqrt_trace (R C : E →L[ℝ] E)
    (hR : R.toLinearMap.IsSymmetric) (hRC : R.comp R=C) :
    (∫ x, ‖R x‖ ∂stdGaussian E)≤Real.sqrt (operatorTrace C) := by
  have hm : MemLp (fun x:E=>‖R x‖) 2 (stdGaussian E) :=
    (R.comp_memLp' IsGaussian.memLp_two_id).norm
  have hv:=variance_nonneg (X:=fun x:E=>‖R x‖) (μ:=stdGaussian E)
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply] at hv
  rw [integral_norm_sq_eq_trace R C hR hRC] at hv
  have ht : 0≤operatorTrace C := by
    rw [←integral_norm_sq_eq_trace R C hR hRC]
    exact integral_nonneg (fun x=>sq_nonneg _)
  have hn : 0≤∫ x:E, ‖R x‖ ∂stdGaussian E := integral_nonneg (fun x=>norm_nonneg _)
  nlinarith [Real.sqrt_nonneg (operatorTrace C),Real.sq_sqrt ht]

end Gaussian

variable {m d : ℕ} [NeZero m]

theorem operatorValue_le_basisNorm_sqrt_trace
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈pdCone) :
    operatorValue b p C ≤ ‖(b : Fin m→FSC.Coord d)‖*Real.sqrt (operatorTrace C) := by
  classical
  obtain ⟨R,hR,_,hRC⟩:=exists_positive_factor C hC
  have hval : operatorValue b p C=optimizedValue (fun i=>R (b i)) p := by
    unfold operatorValue
    rw [←factor_gram b C R hR hRC,covarianceValue_gram]
  have hmax (x:FSC.Coord d) : NegativeVoting.maxScore (scores (fun i=>R (b i)) 0 x)≤
      ‖(b : Fin m→FSC.Coord d)‖*‖R x‖ := by
    apply Finset.sup'_le
    intro i _
    simp only [scores,Pi.zero_apply,add_zero]
    calc
      inner ℝ (R (b i)) x = inner ℝ (b i) (R x) := hR _ _
      _ ≤ ‖b i‖*‖R x‖ := real_inner_le_norm _ _
      _ ≤ ‖(b : Fin m→FSC.Coord d)‖*‖R x‖ :=
        mul_le_mul_of_nonneg_right (norm_le_pi_norm _ i) (norm_nonneg _)
  have hi : Integrable (fun x:FSC.Coord d=>‖R x‖) (stdGaussian (FSC.Coord d)) :=
    (R.toContinuousLinearMap.comp_memLp' IsGaussian.memLp_two_id).norm.integrable (by norm_num)
  calc
    operatorValue b p C = optimizedValue (fun i=>R (b i)) p := hval
    _ ≤ potential (fun i=>R (b i)) p (0 : Fin m→ℝ) :=
      optimizedValue_le_potential _ p hp hs 0
    _ = expectedMax (fun i=>R (b i)) 0 := by simp [potential]
    _ ≤ ∫ x:FSC.Coord d, ‖(b : Fin m→FSC.Coord d)‖*‖R x‖ ∂stdGaussian (FSC.Coord d) :=
      integral_mono (max_integrable _ _) (hi.const_mul _) hmax
    _ = ‖(b : Fin m→FSC.Coord d)‖*∫ x:FSC.Coord d, ‖R x‖ ∂stdGaussian (FSC.Coord d) :=
      integral_const_mul _ _
    _ ≤ ‖(b : Fin m→FSC.Coord d)‖*Real.sqrt (operatorTrace C) :=
      mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_trace R.toContinuousLinearMap C hR hRC)
        (norm_nonneg _)

theorem penalizedValue_le_trace_cutoff
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈pdCone) :
    penalizedValue b p C ≤ 2*‖(b : Fin m→FSC.Coord d)‖^2-(1/2:ℝ)*operatorTrace C := by
  have hb:=operatorValue_le_basisNorm_sqrt_trace b p hp hs C hC
  have ht:=trace_nonneg (pdCone_subset_psdCone hC)
  have hsq:=sq_nonneg (Real.sqrt (operatorTrace C)-2*‖(b : Fin m→FSC.Coord d)‖)
  have hsqrt:=Real.sq_sqrt ht
  change 2*operatorValue b p C-operatorTrace C≤_
  nlinarith

end NegativeVotingCovarianceCoercivity
