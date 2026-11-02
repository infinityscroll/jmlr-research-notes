import GaussianHazardRawIntegralDerivative

/-! First raw derivatives of fixed polynomially bounded threshold tests.
Local domination is derived from the same actual positive Gaussian box. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators ENNReal Classical Topology
namespace NegativeVotingHazardPolynomialIntegralDerivative
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardPolynomialBounds
  NegativeVotingHazardIntegrability NegativeVotingDensityMomentBounds
  NegativeVotingHazardMomentEnvelope NegativeVotingHazardKernelPathDerivative
  NegativeVotingHazardRawIntegralDerivative
variable {m : ℕ}

theorem hazardPairPolynomialIntegral_integrable_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀k,ContDiffAt ℝ 1 (fun z=>σ z k) t)
    (hh : ∀k,ContDiffAt ℝ 1 (fun z=>h z k) t)
    (hpos : ∀k,0<σ t k) (i j : Fin m)
    (φ : ℝ→ℝ) (hφ : Continuous φ) (k : ℕ) (M : ℝ) (hM : 0≤M)
    (hφbound : ∀x,|φ x|≤M*(1+|x|)^k) :
    Integrable (fun x=>hazardPairDensity (σ t) (h t) x i j*
        hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*φ x) volume ∧
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j*φ x)
      (∫x,hazardPairDensity (σ t) (h t) x i j*
        hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*φ x) t := by
  letI : Nonempty (Fin m):=⟨i⟩
  obtain ⟨i₀,hi₀,hmin⟩:=Finset.exists_min_image Finset.univ (σ t) Finset.univ_nonempty
  let s:=σ t i₀/2
  let S:=(∑k,|σ t k|)+1
  let H₀:=(∑k,|h t k|)+1
  let B:=fun k=>transportSize (σ t k) (h t k) (pathDerivative σ t k) (pathDerivative h t k)+1
  let D:=fun k=>densitySize (σ t k) (h t k) (pathDerivative σ t k) (pathDerivative h t k)+1
  have hs:0<s:=by dsimp [s];exact half_pos (hpos i₀)
  have hS0:0<S:=by dsimp [S];positivity
  have hcσ k:ContinuousAt (fun z=>σ z k) t:=(hσ k).continuousAt
  have hch k:ContinuousAt (fun z=>h z k) t:=(hh k).continuousAt
  have hcdσ k:=pathDerivative_continuousAt σ t hσ k
  have hcdh k:=pathDerivative_continuousAt h t hh k
  have hlow:∀ᶠ z in 𝓝 t,∀k,s≤σ z k:=by
    rw [Filter.eventually_all]
    intro k
    have hk:=hmin k (Finset.mem_univ k)
    have hst:s<σ t k:=by dsimp [s];linarith [hpos i₀]
    exact ((hcσ k).eventually (lt_mem_nhds hst)).mono fun z hz=>hz.le
  have hupp:∀ᶠ z in 𝓝 t,∀k,σ z k≤S:=by
    rw [Filter.eventually_all]
    intro k
    have hk:|σ t k|≤∑l,|σ t l|:=Finset.single_le_sum (f:=fun l=>|σ t l|) (fun l _=>abs_nonneg _) (Finset.mem_univ k)
    have hst:σ t k<S:=by dsimp [S];linarith [le_abs_self (σ t k)]
    exact ((hcσ k).eventually (gt_mem_nhds hst)).mono fun z hz=>hz.le
  have hhoff:∀ᶠ z in 𝓝 t,∀k,|h z k|≤H₀:=by
    rw [Filter.eventually_all]
    intro k
    have hk:|h t k|≤∑l,|h t l|:=Finset.single_le_sum (f:=fun l=>|h t l|) (fun l _=>abs_nonneg _) (Finset.mem_univ k)
    have hst:|h t k|<H₀:=by dsimp [H₀];linarith
    exact ((hch k).abs.eventually (gt_mem_nhds hst)).mono fun z hz=>hz.le
  have hB:∀ᶠ z in 𝓝 t,∀k,transportSize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤B k:=by
    rw [Filter.eventually_all]
    intro k
    have hc:ContinuousAt (fun z=>transportSize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)) t:=by
      unfold transportSize
      fun_prop (disch:=exact (hpos k).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [B];linarith))).mono fun z hz=>hz.le
  have hD:∀ᶠ z in 𝓝 t,∀k,densitySize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤D k:=by
    rw [Filter.eventually_all]
    intro k
    have hc:ContinuousAt (fun z=>densitySize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)) t:=by
      unfold densitySize
      fun_prop (disch:=first | exact (hpos k).ne' | exact pow_ne_zero _ (hpos k).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [D];linarith))).mono fun z hz=>hz.le
  let G:={z | (∀k,s≤σ z k) ∧ (∀k,σ z k≤S) ∧ (∀k,|h z k|≤H₀) ∧
    (∀k,transportSize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤B k) ∧
    (∀k,densitySize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤D k) ∧
    (∀k,HasDerivAt (fun q=>σ q k) (pathDerivative σ z k) z) ∧
    (∀k,HasDerivAt (fun q=>h q k) (pathDerivative h z k) z)}
  have hG:G∈𝓝 t:=hlow.and (hupp.and (hhoff.and (hB.and (hD.and
    ((eventually_path_hasDerivAt σ t hσ).and (eventually_path_hasDerivAt h t hh))))))
  let C:=(normalPDF 0/s*Real.exp (H₀^2/(2*S^2)))*linearHazardConstant s H₀*
    (D i+D j+linearHazardConstant s H₀*(B i+B j+∑k,B k))
  have hbase:Integrable (fun x=>hazardPairDensity (σ t) (h t) x i j*φ x) volume:=by
    apply ((integrable_hazardPairDensity_polynomial (σ t) (h t) hpos i j k).const_mul M).mono'
      ((continuous_hazardPairDensity _ _ i j).mul hφ).aestronglyMeasurable
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hazardPairDensity_nonneg _ _ hpos x i j)]
    exact (mul_le_mul_of_nonneg_left (hφbound x) (hazardPairDensity_nonneg _ _ hpos x i j)).trans_eq (by ring)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=G) (bound:=fun x:ℝ=>(C*M)*(Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^(3+k)))
    (F:=fun z x=>hazardPairDensity (σ z) (h z) x i j*φ x)
    (F':=fun z x=>hazardPairDensity (σ z) (h z) x i j*
      hazardPairLogDerivative (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) x i j*φ x)
    hG (by filter_upwards with z;exact ((continuous_hazardPairDensity _ _ i j).mul hφ).aestronglyMeasurable)
    hbase (by exact (((continuous_hazardPairDensity _ _ i j).mul
      (hazardPairLogDerivative_continuous _ _ _ _ i j)).mul hφ).aestronglyMeasurable)
    ?_ ?_ ?_)
  · filter_upwards with x
    intro z hz
    have hb:=raw_derivative_box_bound (σ z) (h z) (pathDerivative σ z) (pathDerivative h z)
      s S H₀ x hs hz.1 hz.2.1 hz.2.2.1 B D hz.2.2.2.1 hz.2.2.2.2.1 i j
    change |hazardPairDensity (σ z) (h z) x i j*hazardPairLogDerivative (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) x i j|≤
      C*(Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^3) at hb
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul hb (hφbound x) (abs_nonneg _) ((abs_nonneg _).trans hb)).trans_eq (by rw [pow_add];ring)
  · have hi:Integrable (fun x:ℝ=>Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^(3+k)) volume:=by
      simpa only [sub_zero] using integrable_gaussian_exp_kernel_polynomial S 0 (1/2) hS0 (by norm_num) (3+k)
    exact hi.const_mul (C*M)
  · filter_upwards with x
    intro z hz
    exact (hazardPairDensity_hasDerivAt (fun k q=>σ q k) (fun k q=>h q k) z x
      (pathDerivative σ z) (pathDerivative h z) hz.2.2.2.2.2.1 hz.2.2.2.2.2.2 (fun k=>hs.trans_le (hz.1 k)) i j).mul_const (φ x)

theorem hazardPairPolynomialIntegral_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀k,ContDiffAt ℝ 1 (fun z=>σ z k) t)
    (hh : ∀k,ContDiffAt ℝ 1 (fun z=>h z k) t)
    (hpos : ∀k,0<σ t k) (i j : Fin m)
    (φ : ℝ→ℝ) (hφ : Continuous φ) (k : ℕ) (M : ℝ) (hM : 0≤M)
    (hφbound : ∀x,|φ x|≤M*(1+|x|)^k) :
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j*φ x)
      (∫x,hazardPairDensity (σ t) (h t) x i j*
        hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j*φ x) t :=
  (hazardPairPolynomialIntegral_integrable_hasDerivAt σ h t hσ hh hpos i j φ hφ k M hM hφbound).2

end NegativeVotingHazardPolynomialIntegralDerivative
