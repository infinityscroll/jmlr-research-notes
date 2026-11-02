import GaussianQuadraticMovingCap

/-! Actual joint moving-cap derivatives for quartic-growth Gaussian tests.
The normal domination and eighth moments are proved here; the literal
slabs, cap, and derivative operators remain the previously checked ones. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators Topology Interval NNReal ENNReal
namespace NegativeVotingQuarticMovingCap
open NegativeVotingMovingCap NegativeVotingDisintegration NegativeVotingFanScore NegativeVotingMovingSlab
variable {d : ℕ} {ι : Type*} [Fintype ι]

 theorem gaussian_norm_four_memLp_two (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    MemLp (fun x : E => ‖x‖^4) 2 (stdGaussian E) := by
  have hh := (IsGaussian.memLp_id (stdGaussian E) 8 (by norm_num)).norm
  haveI : ENNReal.HolderTriple (8:ℝ≥0∞) 8 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have hsq : MemLp (fun x:E=>‖x‖^2) 4 (stdGaussian E) := by
    simpa only [pow_two,Pi.mul_def,id_eq] using hh.mul hh
  haveI : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have hfour := hsq.mul (r:=2) hsq
  have he : (fun x:E=>‖x‖^2*‖x‖^2)=(fun x:E=>‖x‖^4) := by funext x; ring
  simpa only [Pi.mul_def,he] using hfour

 theorem fourth_mul_normalPDF_le (s : ℝ) :
    s^4*WeakSimplex.normalPDF s ≤ 8*WeakSimplex.normalPDF 0 := by
  have he := Real.pow_div_factorial_le_exp (s^2/2) (by positivity : 0 ≤ s^2/2) 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] at he
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(s^2)/2)).le
  have hx : Real.exp (s^2/2)*Real.exp (-(s^2)/2)=1 := by
    rw [←Real.exp_add,show s^2/2+(-(s^2)/2)=(0:ℝ) by ring,Real.exp_zero]
  rw [hx] at hh
  have hb : s^4*Real.exp (-(s^2)/2) ≤ 8 := by nlinarith
  rw [normalPDF_factor]
  nlinarith [mul_le_mul_of_nonneg_left hb (WeakSimplex.normalPDF_pos 0).le]

 theorem fourth_add_le (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    (a+b)^4≤8*a^4+8*b^4 := by
  have hh : (a+b)^2≤2*a^2+2*b^2 := by nlinarith [sq_nonneg (a-b)]
  have hs := (sq_le_sq₀ (sq_nonneg (a+b)) (by positivity : 0≤2*a^2+2*b^2)).mpr hh
  nlinarith [sq_nonneg (a^2-b^2)]

 theorem normal_density_test_bound (F : FSC.Coord d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C*(1+‖x‖^4)) (n : FSC.Coord d) (hn : ‖n‖=1)
    (y : tangentSpace n) (s : ℝ) :
    |WeakSimplex.normalPDF s * F ((y : FSC.Coord d)+s•n)| ≤
      73*C*WeakSimplex.normalPDF 0*(1+‖y‖^4) := by
  have hx : ‖(y : FSC.Coord d)+s•n‖ ≤ ‖y‖+|s| :=
    (norm_add_le _ _).trans (by simp [norm_smul,hn])
  have hx4 : ‖(y : FSC.Coord d)+s•n‖^4 ≤ 8*‖y‖^4+8*s^4 := by
    have hh := (pow_le_pow_left₀ (norm_nonneg _) hx 4).trans
      (fourth_add_le ‖y‖ |s| (norm_nonneg y) (abs_nonneg s))
    simpa only [Even.pow_abs (by decide : Even 4)] using hh
  rw [abs_mul,abs_of_pos (WeakSimplex.normalPDF_pos s)]
  calc
    _ ≤ WeakSimplex.normalPDF s*(C*(1+(8*‖y‖^4+8*s^4))) :=
      mul_le_mul_of_nonneg_left ((hF _).trans (mul_le_mul_of_nonneg_left (by linarith) hC))
        (WeakSimplex.normalPDF_pos s).le
    _ = C*((1+8*‖y‖^4)*WeakSimplex.normalPDF s+8*(s^4*WeakSimplex.normalPDF s)) := by ring
    _ ≤ C*((1+8*‖y‖^4)*WeakSimplex.normalPDF 0+8*(8*WeakSimplex.normalPDF 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (normalPDF_le_zero s) (by positivity))
        (mul_le_mul_of_nonneg_left (fourth_mul_normalPDF_le s) (by norm_num))) hC
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC (WeakSimplex.normalPDF_pos 0).le) (by positivity : 0≤‖y‖^4),mul_nonneg hC (WeakSimplex.normalPDF_pos 0).le]

 theorem quartic_growth_integrable (F : FSC.Coord d → ℝ) (hFm : Measurable F)
    (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) :
    Integrable F (stdGaussian (FSC.Coord d)) := by
  have hi := (gaussian_norm_four_memLp_two (FSC.Coord d)).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  exact (((integrable_const (1:ℝ)).add hi).const_mul C).mono'
    hFm.aestronglyMeasurable (Eventually.of_forall hF)

theorem slabIntegrand_bound (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) (p : Parameters d ι)
    (y : tangentSpace (w j)) (s : ℝ) :
    |slabIntegrand w b mask j F p y s| ≤ 73*C*WeakSimplex.normalPDF 0*(1+‖y‖^4) := by
  unfold slabIntegrand
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (restMask_abs_le _ _ _ _ _)).trans
    (normal_density_test_bound F C hC hF (w j) hw y s)

theorem hasFDerivAt_maskSlab (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (mask : ι → Bool) (j : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0≤C)
    (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) :
    HasFDerivAt (maskSlab w b mask j F) (maskSlabDerivative w b mask j F) (w,b) := by
  let μ := stdGaussian (tangentSpace (w j))
  let g := slabIntegrand w b mask j F
  let z : Parameters d ι → tangentSpace (w j) → ℝ := normalThreshold (w j) j
  let z' : tangentSpace (w j) → Parameters d ι →L[ℝ] ℝ :=
    fun y => constraintLinear ((y : FSC.Coord d)+b j•w j) j
  let K : tangentSpace (w j) → ℝ := fun y => 73*C*WeakSimplex.normalPDF 0*(1+‖y‖^4)
  let L : tangentSpace (w j) → ℝ := fun y => 2*(1+‖y‖+|b j|)
  have hgm (p : Parameters d ι) : Measurable (Function.uncurry (g p)) :=
    slabIntegrand_measurable w b mask j F hFc.measurable p
  have hzm (p : Parameters d ι) : Measurable (z p) := by
    change Measurable (fun y : tangentSpace (w j) =>
      (p.2 j-inner ℝ (p.1 j) (y:FSC.Coord d))/inner ℝ (p.1 j) (w j))
    fun_prop
  have hbase (y : tangentSpace (w j)) : z (w,b) y = b j :=
    normalThreshold_base w b j (hw j) y
  have hzd : ∀ᵐ y ∂μ, HasFDerivAt (fun p => z p y) (z' y) (w,b) :=
    Eventually.of_forall fun y => hasFDerivAt_normalThreshold w b j (hw j) y
  have hloc : ∀ᵐ y : tangentSpace (w j) ∂μ, ∃ ε > 0, ∀ p : Parameters d ι, ‖p-(w,b)‖ < ε →
      ∀ s, |s-b j| < ε →
        restMask (w,b) p mask j ((y : FSC.Coord d)+s•w j) =
          restMask (w,b) (w,b) mask j ((y : FSC.Coord d)+b j•w j) :=
    (ae_tangent_boundary_ne w hw b hb j).mono fun y hy => restMask_locally_constant w b mask j y hy
  have hfreeze : ∀ᵐ y : tangentSpace (w j) ∂μ, ∃ ε > 0, ∀ p : Parameters d ι, ‖p-(w,b)‖ < ε →
      ∀ s, |s-b j| < ε → g p y s = g (w,b) y s := by
    filter_upwards [hloc] with y hy
    obtain ⟨ε,hε,hf⟩ := hy
    refine ⟨ε,hε,fun p hp s hs => ?_⟩
    dsimp [g,slabIntegrand]
    rw [hf p hp s hs,hf (w,b) (by simpa using hε) s hs]
  have hcont : ∀ᵐ y : tangentSpace (w j) ∂μ, ContinuousAt (g (w,b) y) (b j) := by
    filter_upwards [hloc] with y hy
    obtain ⟨ε,hε,hf⟩ := hy
    have heq : (g (w,b) y) =ᶠ[𝓝 (b j)]
        (fun s => WeakSimplex.normalPDF s * F ((y : FSC.Coord d)+s•w j) *
          restMask (w,b) (w,b) mask j ((y : FSC.Coord d)+b j•w j)) := by
      have hs : ∀ᶠ s : ℝ in 𝓝 (b j), |s-b j| < ε := by
        change {s : ℝ | |s-b j| < ε} ∈ 𝓝 (b j)
        simpa only [Metric.ball,Real.dist_eq] using Metric.ball_mem_nhds (b j) hε
      filter_upwards [hs] with s hs
      dsimp [g,slabIntegrand]
      rw [hf (w,b) (by simpa using hε) s hs]
    apply ContinuousAt.congr_of_eventuallyEq _ heq
    exact ((WeakSimplex.hasDerivAt_normalPDF (b j)).continuousAt.mul
      (hFc.continuousAt.comp (by fun_prop))).mul continuousAt_const
  have hKi : MemLp K 2 μ := by
    exact ((memLp_const (1:ℝ)).add (gaussian_norm_four_memLp_two (tangentSpace (w j)))).const_mul
      (73*C*WeakSimplex.normalPDF 0)
  have hLi : MemLp L 2 μ := by
    exact (((memLp_const (1:ℝ)).add IsGaussian.memLp_two_id.norm).add
      (memLp_const |b j|)).const_mul 2
  have hint : Integrable (fun y => K y * L y) μ := hKi.integrable_mul hLi
  have hdm : AEStronglyMeasurable (fun y => g (w,b) y (b j) • z' y) μ := by
    apply Measurable.aestronglyMeasurable
    exact ((hgm (w,b)).comp (measurable_id.prodMk measurable_const)).smul
      ((constraintLinear_continuous j).measurable.comp (by fun_prop))
  exact hasFDerivAt_integral_moving_slab (μ := μ) g z (fun _ => b j) z' (w,b)
    (Metric.ball (w,b) (1/2)) (Metric.ball_mem_nhds _ (by norm_num)) K L hgm hzm
    measurable_const hbase hzd hcont hfreeze (fun y => by dsimp only [K]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (WeakSimplex.normalPDF_pos 0).le) (by positivity))
    (fun p _ y s => slabIntegrand_bound w b mask j (hw j) F C hC hF p y s)
    (fun p hp y => normalThreshold_displacement_bound w b j (hw j) p
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hp) y) hint hdm

theorem hasFDerivAt_singleChange_integral (w : ι → FSC.Coord d)
    (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (mask : ι → Bool) (j : ι) (F : FSC.Coord d → ℝ) (hFc : Continuous F)
    (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) :
    HasFDerivAt (fun p : Parameters d ι =>
      ∫ x, singleChange w b mask j F p x ∂stdGaussian (FSC.Coord d))
      (maskSlabDerivative w b mask j F) (w,b) := by
  apply (hasFDerivAt_maskSlab w hw b hb mask j F hFc C hC hF).congr_of_eventuallyEq
  have hh : ∀ᶠ p : Parameters d ι in 𝓝 (w,b), ‖p-(w,b)‖ < 1/2 := by
    change {p : Parameters d ι | ‖p-(w,b)‖ < 1/2} ∈ 𝓝 (w,b)
    simpa only [Metric.ball,dist_eq_norm] using
      Metric.ball_mem_nhds (w,b) (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hh] with p hp
  exact (maskSlab_eq_singleChange_integral w b mask j (hw j) F
    (quartic_growth_integrable F hFc.measurable C hC hF) p hp).symm

theorem hasFDerivAt_capTest (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (F : FSC.Coord d → ℝ)
    (hFc : Continuous F) (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) :
    HasFDerivAt (fun p : Parameters d ι => capTest p F) (capJointDerivative w b F) (w,b) := by
  classical
  have hs := HasFDerivAt.sum (u := Finset.univ) fun j _ =>
    hasFDerivAt_singleChange_integral w hw b hb (telescopeMask j) j F hFc C hC hF
  have hh := hs.const_add (capTest (w,b) F)
  have he : (fun p : Parameters d ι => capTest (w,b) F +
      ∑ j, ∫ x, singleChange w b (telescopeMask j) j F p x ∂stdGaussian (FSC.Coord d)) =
        fun p => capTest p F := by
    funext p
    have he := capTest_difference_eq_sum_singleChange w b F
      (quartic_growth_integrable F hFc.measurable C hC hF) p
    linarith
  simp only [Finset.sum_apply] at hh
  rw [he] at hh
  exact hh

theorem maskSlabDerivative_integrable (w : ι → FSC.Coord d) (b : ι → ℝ)
    (mask : ι → Bool) (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ)
    (hFc : Continuous F) (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) :
    Integrable (fun y : tangentSpace (w j) =>
      slabIntegrand w b mask j F (w,b) y (b j) •
        constraintLinear ((y : FSC.Coord d)+b j•w j) j)
      (stdGaussian (tangentSpace (w j))) := by
  let K := fun y : tangentSpace (w j) => 73*C*WeakSimplex.normalPDF 0*(1+‖y‖^4)
  let L := fun y : tangentSpace (w j) => 1+‖y‖+|b j|
  have hKi : MemLp K 2 (stdGaussian (tangentSpace (w j))) :=
    ((memLp_const (1:ℝ)).add (gaussian_norm_four_memLp_two (tangentSpace (w j)))).const_mul
      (73*C*WeakSimplex.normalPDF 0)
  have hLi : MemLp L 2 (stdGaussian (tangentSpace (w j))) :=
    ((memLp_const (1:ℝ)).add IsGaussian.memLp_two_id.norm).add (memLp_const |b j|)
  apply (hKi.integrable_mul hLi).mono'
  · apply Measurable.aestronglyMeasurable
    exact ((slabIntegrand_measurable w b mask j F hFc.measurable (w,b)).comp
      (measurable_id.prodMk measurable_const)).smul
      ((constraintLinear_continuous j).measurable.comp (by fun_prop))
  filter_upwards with y
  rw [norm_smul,Real.norm_eq_abs]
  have hx : ‖(y : FSC.Coord d)+b j•w j‖ ≤ ‖y‖+|b j| :=
    (norm_add_le _ _).trans (by simp [norm_smul,hw])
  apply mul_le_mul (slabIntegrand_bound w b mask j hw F C hC hF (w,b) y (b j))
  · exact (constraintLinear_norm_le _ j).trans (by change 1+‖(y:FSC.Coord d)+b j•w j‖ ≤ 1+‖y‖+|b j|; linarith)
  · exact norm_nonneg _
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (WeakSimplex.normalPDF_pos 0).le) (by positivity)

theorem maskSlabDerivative_apply (w : ι → FSC.Coord d) (b : ι → ℝ)
    (mask : ι → Bool) (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ)
    (hFc : Continuous F) (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖^4))
    (δ : Parameters d ι) :
    maskSlabDerivative w b mask j F δ = WeakSimplex.normalPDF (b j) *
      ∫ y in tangentFace w b j,
        F ((y : FSC.Coord d)+b j•w j) *
          (δ.2 j-inner ℝ (δ.1 j) ((y : FSC.Coord d)+b j•w j))
          ∂stdGaussian (tangentSpace (w j)) := by
  classical
  unfold maskSlabDerivative
  rw [ContinuousLinearMap.integral_apply (maskSlabDerivative_integrable w b mask j hw F hFc C hC hF),
    ← integral_indicator (tangentFace_measurable w b j),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,constraintLinear_apply,
    slabIntegrand,restMask,mixedParameters_base,tangentFace,Set.indicator_apply,Set.mem_setOf_eq]
  split_ifs <;> ring

theorem capJointDerivative_apply (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (F : FSC.Coord d → ℝ) (hFc : Continuous F)
    (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖^4)) (δ : Parameters d ι) :
    capJointDerivative w b F δ = ∑ j, WeakSimplex.normalPDF (b j) *
      ∫ y in tangentFace w b j,
        F ((y : FSC.Coord d)+b j•w j) *
          (δ.2 j-inner ℝ (δ.1 j) ((y : FSC.Coord d)+b j•w j))
          ∂stdGaussian (tangentSpace (w j)) := by
  classical
  unfold capJointDerivative
  simp only [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ =>
    maskSlabDerivative_apply w b (telescopeMask j) j (hw j) F hFc C hC hF δ

end NegativeVotingQuarticMovingCap
