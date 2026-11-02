import GaussianHazardKernelDifferentiation

/-! Genuine differentiation of actual pair-hazard integrals along C1 paths.
All local domination and differentiability premises are derived from C1 and
positive standard deviations, through a fixed standard Gaussian kernel. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators ENNReal Classical Topology
namespace NegativeVotingHazardKernelPathDerivative
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalBalancedDerivative
  NegativeVotingHazardKernelDifferentiation NegativeVotingDensityMomentBounds
variable {m : ℕ}

def pathDerivative (f : ℝ→Fin m→ℝ) (t : ℝ) (i : Fin m) : ℝ := deriv (fun s=>f s i) t

theorem pathDerivative_continuousAt (f : ℝ→Fin m→ℝ) (t : ℝ)
    (hf : ∀i,ContDiffAt ℝ 1 (fun s=>f s i) t) (i : Fin m) :
    ContinuousAt (fun s=>pathDerivative f s i) t :=
  ((hf i).derivWithin (m:=0) (by norm_num)).continuousAt

theorem eventually_path_hasDerivAt (f : ℝ→Fin m→ℝ) (t : ℝ)
    (hf : ∀i,ContDiffAt ℝ 1 (fun s=>f s i) t) :
    ∀ᶠ s in 𝓝 t,∀i,HasDerivAt (fun z=>f z i) (pathDerivative f s i) s := by
  rw [Filter.eventually_all]
  intro i
  filter_upwards [(hf i).eventually (by norm_num)] with s hs
  exact (hs.differentiableAt (by norm_num)).hasDerivAt

/-- One common neighborhood controls every scalar coefficient used by the
actual all-label derivative. Its constants may depend on the base path. -/
theorem exists_local_kernel_bounds (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀i,ContDiffAt ℝ 1 (fun s=>σ s i) t)
    (hh : ∀i,ContDiffAt ℝ 1 (fun s=>h s i) t)
    (hpos : ∀i,0<σ t i) (i j : Fin m) :
    ∃A B : Fin m→ℝ,∃R I J : ℝ,∃s∈𝓝 t,∀z∈s,
      (∀k,0<σ z k) ∧
      (∀k,HasDerivAt (fun q=>σ q k) (pathDerivative σ z k) z) ∧
      (∀k,HasDerivAt (fun q=>h q k) (pathDerivative h z k) z) ∧
      (∀k,|linearSlope (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i k 0|≤A k) ∧
      (∀k,|constantSlope (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i k 0|≤B k) ∧
      r 0+|σ z i/σ z j|+|(h z i-h z j)/σ z j|≤R ∧
      |(σ z j)⁻¹|≤I ∧ |pathDerivative σ z j/(σ z j)^2|≤J := by
  let A:=fun k=>|linearSlope (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) i k 0|+1
  let B:=fun k=>|constantSlope (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) i k 0|+1
  let R:=r 0+|σ t i/σ t j|+|(h t i-h t j)/σ t j|+1
  let I:=|(σ t j)⁻¹|+1
  let J:=|pathDerivative σ t j/(σ t j)^2|+1
  have hsC k:ContinuousAt (fun z=>σ z k) t:=(hσ k).continuousAt
  have hhC k:ContinuousAt (fun z=>h z k) t:=(hh k).continuousAt
  have hdσ k:=pathDerivative_continuousAt σ t hσ k
  have hdh k:=pathDerivative_continuousAt h t hh k
  have hp:∀ᶠ z in 𝓝 t,∀k,0<σ z k:=by
    rw [Filter.eventually_all]
    intro k
    exact (hsC k).eventually (lt_mem_nhds (hpos k))
  have hA:∀ᶠ z in 𝓝 t,∀k,|linearSlope (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i k 0|≤A k:=by
    rw [Filter.eventually_all]
    intro k
    have hc:ContinuousAt (fun z=>linearSlope (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i k 0) t:=by
      simp only [linearSlope,parameterLine_zero]
      fun_prop (disch:=exact pow_ne_zero 2 (hpos k).ne')
    exact (hc.abs.eventually (gt_mem_nhds (by dsimp [A];linarith))).mono (fun z hz=>hz.le)
  have hB:∀ᶠ z in 𝓝 t,∀k,|constantSlope (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i k 0|≤B k:=by
    rw [Filter.eventually_all]
    intro k
    have hc:ContinuousAt (fun z=>constantSlope (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i k 0) t:=by
      simp only [constantSlope,parameterLine_zero]
      fun_prop (disch:=exact pow_ne_zero 2 (hpos k).ne')
    exact (hc.abs.eventually (gt_mem_nhds (by dsimp [B];linarith))).mono (fun z hz=>hz.le)
  have hR:∀ᶠ z in 𝓝 t,r 0+|σ z i/σ z j|+|(h z i-h z j)/σ z j|≤R:=by
    have hc:ContinuousAt (fun z=>r 0+|σ z i/σ z j|+|(h z i-h z j)/σ z j|) t:=by
      fun_prop (disch:=exact (hpos j).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [R];linarith))).mono (fun z hz=>hz.le)
  have hI:∀ᶠ z in 𝓝 t,|(σ z j)⁻¹|≤I:=by
    have hc:ContinuousAt (fun z=>|(σ z j)⁻¹|) t:=by fun_prop (disch:=exact (hpos j).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [I];linarith))).mono (fun z hz=>hz.le)
  have hJ:∀ᶠ z in 𝓝 t,|pathDerivative σ z j/(σ z j)^2|≤J:=by
    have hc:ContinuousAt (fun z=>|pathDerivative σ z j/(σ z j)^2|) t:=by
      fun_prop (disch:=exact pow_ne_zero 2 (hpos j).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [J];linarith))).mono (fun z hz=>hz.le)
  refine ⟨A,B,R,I,J,_,?_,fun z hz=>hz⟩
  exact hp.and ((eventually_path_hasDerivAt σ t hσ).and ((eventually_path_hasDerivAt h t hh).and
    (hA.and (hB.and (hR.and (hI.and hJ))))))

theorem pairKernelIntegral_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀i,ContDiffAt ℝ 1 (fun s=>σ s i) t)
    (hh : ∀i,ContDiffAt ℝ 1 (fun s=>h s i) t)
    (hpos : ∀i,0<σ t i) (i j : Fin m) :
    HasDerivAt (fun z=>∫y,pairKernel (σ z) (h z) i j y ∂gaussianReal 0 1)
      (∫y,pairKernelDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) i j y ∂gaussianReal 0 1) t := by
  obtain ⟨A,B,R,I,J,s,hs,hbounds⟩:=exists_local_kernel_bounds σ h t hσ hh hpos i j
  let C:=((∑k∈Finset.univ.erase i,(A k+B k))*R*I+I*(A j+B j)+R*J)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=s) (bound:=fun y:ℝ=>C*(1+|y|)^2)
    (F:=fun z y=>pairKernel (σ z) (h z) i j y)
    (F':=fun z y=>pairKernelDerivative (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) i j y)
    hs (by filter_upwards with z;fun_prop) (pairKernel_integrable _ _ i j) (by fun_prop)
    ?_ ((integrable_standard_polynomial 2).const_mul C) ?_).2
  · filter_upwards with y
    intro z hz
    have hb:=hbounds z hz
    simpa only [Real.norm_eq_abs,C] using pairKernelDerivative_bound _ _ _ _ i j y A B R I J
      hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2
  · filter_upwards with y
    intro z hz
    have hb:=hbounds z hz
    exact pairKernel_path_hasDerivAt σ h z _ _ hb.2.1 hb.2.2.1 (fun k=>(hb.1 k).ne') i j y

/-- Actual threshold pair integral differentiation, with every analytic
coefficient and all local dominance supplied by the C1 path itself. -/
theorem hazardPairIntegral_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀i,ContDiffAt ℝ 1 (fun s=>σ s i) t)
    (hh : ∀i,ContDiffAt ℝ 1 (fun s=>h s i) t)
    (hpos : ∀i,0<σ t i) (i j : Fin m) :
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j)
      (∫y,pairKernelDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) i j y ∂gaussianReal 0 1) t := by
  apply (pairKernelIntegral_hasDerivAt σ h t hσ hh hpos i j).congr_of_eventuallyEq
  have hp:∀ᶠ z in 𝓝 t,∀k,0<σ z k:=by
    rw [Filter.eventually_all]
    intro k
    exact (hσ k).continuousAt.eventually (lt_mem_nhds (hpos k))
  filter_upwards [hp] with z hz
  exact pair_integral_eq_kernel (σ z) (h z) hz i j

end NegativeVotingHazardKernelPathDerivative
