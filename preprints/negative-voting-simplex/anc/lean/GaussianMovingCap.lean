import GaussianFanScoreHessian
import GaussianMovingSlab
import GaussianCapTelescoping

/-! Concrete Gaussian ingredients for differentiation of moving polyhedra. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators Topology Interval NNReal ENNReal

namespace NegativeVotingMovingCap
open NegativeVotingDisintegration NegativeVotingFanScore NegativeVotingMovingSlab
variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A positive inequality sign means that the point lies inside the halfspace. -/
def constraintLinear (x : FSC.Coord d) (j : ι) : Parameters d ι →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.snd ℝ (ι → FSC.Coord d) (ι → ℝ)) -
  (innerSL ℝ x).comp ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (ι → FSC.Coord d) (ι → ℝ)))

theorem constraintLinear_apply (x : FSC.Coord d) (j : ι) (p : Parameters d ι) :
    constraintLinear x j p = p.2 j - inner ℝ (p.1 j) x := by
  change p.2 j - inner ℝ x (p.1 j) = _
  rw [real_inner_comm x (p.1 j)]

def normalThreshold (n : FSC.Coord d) (j : ι) (p : Parameters d ι)
    (y : tangentSpace n) : ℝ :=
  (p.2 j - inner ℝ (p.1 j) (y : FSC.Coord d)) / inner ℝ (p.1 j) n

theorem inner_tangent (n : FSC.Coord d) (y : tangentSpace n) :
    inner ℝ n (y : FSC.Coord d) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property

theorem normalThreshold_base (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (hw : ‖w j‖ = 1) (y : tangentSpace (w j)) :
    normalThreshold (w j) j (w,b) y = b j := by
  simp [normalThreshold,inner_tangent,real_inner_self_eq_norm_sq,hw]

/-- The moving inequality has a derived rational normal threshold. -/
theorem hasFDerivAt_normalThreshold (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (hw : ‖w j‖ = 1) (y : tangentSpace (w j)) :
    HasFDerivAt (fun p : Parameters d ι => normalThreshold (w j) j p y)
      (constraintLinear ((y : FSC.Coord d) + b j • w j) j) (w,b) := by
  let den : Parameters d ι →L[ℝ] ℝ :=
    (innerSL ℝ (w j)).comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (ι → FSC.Coord d) (ι → ℝ)))
  have hden : den (w,b) = 1 := by
    change inner ℝ (w j) (w j) = 1
    simp [real_inner_self_eq_norm_sq,hw]
  have hnum : constraintLinear (y : FSC.Coord d) j (w,b) = b j := by
    rw [constraintLinear_apply,inner_tangent,sub_zero]
  have he : (fun p => normalThreshold (w j) j p y) =
      fun p => constraintLinear (y : FSC.Coord d) j p / den p := by
    funext p
    rw [constraintLinear_apply]
    unfold normalThreshold
    congr 1
    exact real_inner_comm _ _
  rw [he]
  have hInv := (hasDerivAt_inv (by rw [hden]; norm_num : den (w,b) ≠ 0)).comp_hasFDerivAt
    (w,b) den.hasFDerivAt
  have hd := (constraintLinear (y : FSC.Coord d) j).hasFDerivAt.mul hInv
  simp only [Pi.mul_apply,Function.comp_def,← div_eq_mul_inv] at hd
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp only [hden,hnum,one_smul,one_pow,inv_one,smul_sub,one_smul,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply,constraintLinear_apply]
  dsimp [den]
  simp only [inner_add_right,real_inner_smul_right]
  rw [real_inner_comm (w j) (p.1 j)]
  ring

theorem threshold_denominator_near (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (hw : ‖w j‖ = 1) (p : Parameters d ι) (hp : ‖p-(w,b)‖ < 1/2) :
    1/2 < inner ℝ (p.1 j) (w j) := by
  have he : inner ℝ (p.1 j) (w j) - 1 = inner ℝ (p.1 j-w j) (w j) := by
    rw [inner_sub_left,real_inner_self_eq_norm_sq,hw]
    norm_num
  have hnorm : ‖p.1 j-w j‖ ≤ ‖p-(w,b)‖ :=
    (norm_le_pi_norm (p.1-w) j).trans (by simpa using norm_fst_le (p-(w,b)))
  have hh := (abs_real_inner_le_norm (p.1 j-w j) (w j)).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg (w j)))
  rw [hw,mul_one,← he] at hh
  have hl := (abs_le.mp hh).1
  linarith

/-- A neighborhood uniform in the normal fiber gives a polynomial displacement bound. -/
theorem normalThreshold_displacement_bound (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (hw : ‖w j‖ = 1) (p : Parameters d ι) (hp : ‖p-(w,b)‖ < 1/2)
    (y : tangentSpace (w j)) :
    |normalThreshold (w j) j p y - b j| ≤
      (2 * (1 + ‖y‖ + |b j|)) * ‖p-(w,b)‖ := by
  let δ := p-(w,b)
  let x : FSC.Coord d := (y : FSC.Coord d) + b j • w j
  have hden := threshold_denominator_near w b j hw p hp
  have hnum : normalThreshold (w j) j p y - b j =
      (δ.2 j - inner ℝ (δ.1 j) x) / inner ℝ (p.1 j) (w j) := by
    unfold normalThreshold
    dsimp [δ,x]
    rw [div_sub' (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1/2) hden))]
    congr 1
    simp only [Prod.snd_sub,Prod.fst_sub,Pi.sub_apply,inner_sub_left,inner_add_right,
      real_inner_smul_right,inner_tangent,real_inner_self_eq_norm_sq,hw]
    ring
  have hx : ‖x‖ ≤ ‖y‖+|b j| := by
    exact (norm_add_le _ _).trans (by simp [norm_smul,hw])
  have hrow : ‖δ.1 j‖ ≤ ‖δ‖ := (norm_le_pi_norm δ.1 j).trans (norm_fst_le δ)
  have hoff : |δ.2 j| ≤ ‖δ‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm δ.2 j).trans (norm_snd_le δ)
  have hN : |δ.2 j-inner ℝ (δ.1 j) x| ≤ (1+‖y‖+|b j|)*‖δ‖ := by
    calc
      _ ≤ |δ.2 j| + |inner ℝ (δ.1 j) x| := abs_sub _ _
      _ ≤ ‖δ‖ + ‖δ‖ * (‖y‖+|b j|) :=
        add_le_add hoff ((abs_real_inner_le_norm _ _).trans (mul_le_mul hrow hx (norm_nonneg _) (norm_nonneg _)))
      _ = _ := by ring
  rw [hnum,abs_div,abs_of_pos (lt_trans (by norm_num : (0:ℝ)<1/2) hden)]
  apply (div_le_iff₀ (lt_trans (by norm_num : (0:ℝ)<1/2) hden)).2
  have hpos : 0 ≤ (1+‖y‖+|b j|)*‖δ‖ := by positivity
  nlinarith

/-- Exact Gaussian density factorization, with its actual value at zero. -/
theorem normalPDF_factor (s : ℝ) :
    WeakSimplex.normalPDF s = WeakSimplex.normalPDF 0 * Real.exp (-(s^2)/2) := by
  simp [WeakSimplex.normalPDF,gaussianPDFReal]

theorem normalPDF_le_zero (s : ℝ) :
    WeakSimplex.normalPDF s ≤ WeakSimplex.normalPDF 0 := by
  rw [normalPDF_factor]
  exact mul_le_of_le_one_right (WeakSimplex.normalPDF_pos 0).le
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg s]))

theorem abs_mul_normalPDF_le_zero (s : ℝ) :
    |s| * WeakSimplex.normalPDF s ≤ WeakSimplex.normalPDF 0 := by
  have hs : |s| ≤ Real.exp (s^2/2) := by
    have hh := Real.add_one_le_exp (s^2/2)
    nlinarith [sq_nonneg (|s|-1),sq_abs s]
  have he : |s| * Real.exp (-(s^2)/2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(s^2)/2)).le
    rw [← Real.exp_add] at this
    simpa only [show s^2/2 + (-(s^2)/2) = (0:ℝ) by ring,Real.exp_zero] using this
  rw [normalPDF_factor]
  calc
    _ = WeakSimplex.normalPDF 0 * (|s| * Real.exp (-(s^2)/2)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (WeakSimplex.normalPDF_pos 0).le he

/-- Multiplication by the normal Gaussian density turns linear test growth
into a bound independent of the normal coordinate. -/
theorem normal_density_test_bound (F : FSC.Coord d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C*(1+‖x‖)) (n : FSC.Coord d) (hn : ‖n‖=1)
    (y : tangentSpace n) (s : ℝ) :
    |WeakSimplex.normalPDF s * F ((y : FSC.Coord d)+s•n)| ≤
      C * WeakSimplex.normalPDF 0 * (2+‖y‖) := by
  have hx : ‖(y : FSC.Coord d)+s•n‖ ≤ ‖y‖+|s| :=
    (norm_add_le _ _).trans (by simp [norm_smul,hn])
  rw [abs_mul,abs_of_pos (WeakSimplex.normalPDF_pos s)]
  calc
    _ ≤ WeakSimplex.normalPDF s * (C*(1+(‖y‖+|s|))) :=
      mul_le_mul_of_nonneg_left ((hF _).trans (mul_le_mul_of_nonneg_left (by linarith) hC))
        (WeakSimplex.normalPDF_pos s).le
    _ = C*((1+‖y‖)*WeakSimplex.normalPDF s + |s| *WeakSimplex.normalPDF s) := by ring
    _ ≤ C*((1+‖y‖)*WeakSimplex.normalPDF 0 + WeakSimplex.normalPDF 0) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (normalPDF_le_zero s) (by positivity))
        (abs_mul_normalPDF_le_zero s)) hC
    _ = _ := by ring



/-- Other constraints may use either the new or the base parameter; this
covers every term in the exact finite telescoping decomposition. -/
def mixedParameters (base p : Parameters d ι) (mask : ι → Bool) : Parameters d ι :=
  (fun k => if mask k then p.1 k else base.1 k,
   fun k => if mask k then p.2 k else base.2 k)

def restMask (base p : Parameters d ι) (mask : ι → Bool) (j : ι)
    (x : FSC.Coord d) : ℝ := by
  classical
  exact if ∀ k, k ≠ j → inner ℝ ((mixedParameters base p mask).1 k) x ≤
    (mixedParameters base p mask).2 k then 1 else 0

theorem mixedParameters_base (base : Parameters d ι) (mask : ι → Bool) :
    mixedParameters base base mask = base := by
  ext k <;> simp [mixedParameters]

theorem restMask_abs_le (base p : Parameters d ι) (mask : ι → Bool) (j : ι)
    (x : FSC.Coord d) : |restMask base p mask j x| ≤ 1 := by
  classical
  unfold restMask
  split_ifs <;> norm_num

theorem restMask_measurable (base p : Parameters d ι) (mask : ι → Bool) (j : ι) :
    Measurable (restMask base p mask j) := by
  classical
  have hs : MeasurableSet {x : FSC.Coord d | ∀ k, k ≠ j →
      inner ℝ ((mixedParameters base p mask).1 k) x ≤ (mixedParameters base p mask).2 k} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (by fun_prop) measurable_const
  exact Measurable.ite hs measurable_const measurable_const

/-- The actual Gaussian tangent law gives zero mass to all other boundaries. -/
theorem ae_tangent_boundary_ne (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (j : ι) :
    ∀ᵐ y : tangentSpace (w j) ∂stdGaussian (tangentSpace (w j)), ∀ k, k ≠ j →
      inner ℝ (w k) ((y : FSC.Coord d)+b j • w j) ≠ b k := by
  classical
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k=j
  · exact Eventually.of_forall fun _ h => (h hk).elim
  rw [← gaussian_projection_map (tangentSpace (w j))]
  have hm : MeasurableSet {y : tangentSpace (w j) |
      inner ℝ (w k) ((y : FSC.Coord d)+b j•w j) ≠ b k} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  apply (ae_map_iff (by fun_prop) (by
    convert hm using 1
    ext y
    simp [hk])).2
  filter_upwards [FSC.ae_slice_boundary_ne w hw b hb j k hk] with x hx
  intro _
  simpa only [tangent_projection_formula (w j) (hw j),FSC.normalResidual_apply,add_comm] using hx

/-- Strict inequalities on a fixed facet give one joint neighborhood in all
score parameters and in the normal coordinate. -/
theorem restMask_locally_constant (w : ι → FSC.Coord d) (b : ι → ℝ)
    (mask : ι → Bool) (j : ι) (y : tangentSpace (w j))
    (hy : ∀ k, k ≠ j → inner ℝ (w k) ((y : FSC.Coord d)+b j • w j) ≠ b k) :
    ∃ ε > 0, ∀ p : Parameters d ι, ‖p-(w,b)‖ < ε → ∀ s : ℝ, |s-b j| < ε →
      restMask (w,b) p mask j ((y : FSC.Coord d)+s•w j) =
        restMask (w,b) (w,b) mask j ((y : FSC.Coord d)+b j•w j) := by
  classical
  let a : Parameters d ι × ℝ := ((w,b),b j)
  have heach (k : ι) : ∀ᶠ q : Parameters d ι × ℝ in 𝓝 a,
      (k ≠ j → inner ℝ ((mixedParameters (w,b) q.1 mask).1 k)
        ((y : FSC.Coord d)+q.2•w j) ≤ (mixedParameters (w,b) q.1 mask).2 k) ↔
      (k ≠ j → inner ℝ (w k) ((y : FSC.Coord d)+b j•w j) ≤ b k) := by
    by_cases hk : k=j
    · exact Eventually.of_forall fun _ => by simp [hk]
    have hc : ContinuousAt (fun q : Parameters d ι × ℝ =>
        inner ℝ ((mixedParameters (w,b) q.1 mask).1 k)
          ((y : FSC.Coord d)+q.2•w j)) a := by
      dsimp only [mixedParameters]
      split_ifs <;> fun_prop
    have hd : ContinuousAt (fun q : Parameters d ι × ℝ =>
        (mixedParameters (w,b) q.1 mask).2 k) a := by
      dsimp only [mixedParameters]
      split_ifs <;> fun_prop
    rcases lt_or_gt_of_ne (hy k hk) with h | h
    · have hh := hc.eventually_lt hd (by simpa [a,mixedParameters] using h)
      filter_upwards [hh] with q hq
      simp only [hq.le,h.le,implies_true]
    · have hh := hd.eventually_lt hc (by simpa [a,mixedParameters] using h)
      filter_upwards [hh] with q hq
      simp only [not_le.mpr hq,not_le.mpr h,hk,not_false_eq_true,true_implies]
  have hall := eventually_all.mpr heach
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨ε,hε,?_⟩
  intro p hp s hs
  have hq : ∀ k,
      (k ≠ j → inner ℝ ((mixedParameters (w,b) p mask).1 k)
        ((y : FSC.Coord d)+s•w j) ≤ (mixedParameters (w,b) p mask).2 k) ↔
      (k ≠ j → inner ℝ (w k) ((y : FSC.Coord d)+b j•w j) ≤ b k) := by
    have hmem : (p,s) ∈ Metric.ball a ε := by
      change max (dist p (w,b)) (dist s (b j)) < ε
      exact max_lt (by simpa only [dist_eq_norm] using hp) (by simpa only [Real.dist_eq] using hs)
    exact hball hmem
  unfold restMask
  rw [mixedParameters_base]
  congr 1
  exact propext (forall_congr' hq)

def slabIntegrand (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) (p : Parameters d ι)
    (y : tangentSpace (w j)) (s : ℝ) : ℝ :=
  WeakSimplex.normalPDF s * F ((y : FSC.Coord d)+s•w j) *
    restMask (w,b) p mask j ((y : FSC.Coord d)+s•w j)

theorem slabIntegrand_measurable (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) (hF : Measurable F) (p : Parameters d ι) :
    Measurable (Function.uncurry (slabIntegrand w b mask j F p)) := by
  unfold slabIntegrand Function.uncurry
  exact ((measurable_gaussianPDFReal 0 1).comp measurable_snd).mul
    (hF.comp (by fun_prop)) |>.mul ((restMask_measurable (w,b) p mask j).comp (by fun_prop))

theorem slabIntegrand_bound (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀ x, |F x|≤C*(1+‖x‖)) (p : Parameters d ι)
    (y : tangentSpace (w j)) (s : ℝ) :
    |slabIntegrand w b mask j F p y s| ≤ C*WeakSimplex.normalPDF 0*(2+‖y‖) := by
  unfold slabIntegrand
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (restMask_abs_le _ _ _ _ _)).trans
    (normal_density_test_bound F C hC hF (w j) hw y s)



theorem constraintLinear_continuous (j : ι) :
    Continuous (fun x : FSC.Coord d => constraintLinear x j) := by
  unfold constraintLinear
  fun_prop

def maskSlab (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) (p : Parameters d ι) : ℝ :=
  ∫ y : tangentSpace (w j),
    (∫ s in b j..normalThreshold (w j) j p y, slabIntegrand w b mask j F p y s)
      ∂stdGaussian (tangentSpace (w j))

def maskSlabDerivative (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∫ y : tangentSpace (w j),
    slabIntegrand w b mask j F (w,b) y (b j) •
      constraintLinear ((y : FSC.Coord d)+b j•w j) j
        ∂stdGaussian (tangentSpace (w j))

/-- All hypotheses of the moving-slab differentiation theorem are discharged
for actual Gaussian polyhedra, including moving other faces. -/
theorem hasFDerivAt_maskSlab (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (mask : ι → Bool) (j : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0≤C)
    (hF : ∀ x, |F x|≤C*(1+‖x‖)) :
    HasFDerivAt (maskSlab w b mask j F) (maskSlabDerivative w b mask j F) (w,b) := by
  let μ := stdGaussian (tangentSpace (w j))
  let g := slabIntegrand w b mask j F
  let z : Parameters d ι → tangentSpace (w j) → ℝ := normalThreshold (w j) j
  let z' : tangentSpace (w j) → Parameters d ι →L[ℝ] ℝ :=
    fun y => constraintLinear ((y : FSC.Coord d)+b j•w j) j
  let K : tangentSpace (w j) → ℝ := fun y => C*WeakSimplex.normalPDF 0*(2+‖y‖)
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
    exact ((memLp_const (2:ℝ)).add IsGaussian.memLp_two_id.norm).const_mul
      (C*WeakSimplex.normalPDF 0)
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
    measurable_const hbase hzd hcont hfreeze (fun y => mul_nonneg (mul_nonneg hC (WeakSimplex.normalPDF_pos 0).le) (by positivity))
    (fun p _ y s => slabIntegrand_bound w b mask j (hw j) F C hC hF p y s)
    (fun p hp y => normalThreshold_displacement_bound w b j (hw j) p
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hp) y) hint hdm



def halfspaceIndicator (p : Parameters d ι) (j : ι) : FSC.Coord d → ℝ :=
  {x | inner ℝ (p.1 j) x ≤ p.2 j}.indicator (fun _ => 1)

theorem halfspaceIndicator_measurable (p : Parameters d ι) (j : ι) :
    Measurable (halfspaceIndicator p j) := by
  apply measurable_const.indicator
  exact measurableSet_le (by fun_prop) measurable_const

theorem halfspaceIndicator_abs_le (p : Parameters d ι) (j : ι) (x : FSC.Coord d) :
    |halfspaceIndicator p j x| ≤ 1 := by
  classical
  unfold halfspaceIndicator
  by_cases hx : inner ℝ (p.1 j) x ≤ p.2 j <;> simp [hx]

theorem halfspaceIndicator_normal (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (hw : ‖w j‖=1) (p : Parameters d ι) (hp : ‖p-(w,b)‖ < 1/2)
    (y : tangentSpace (w j)) (s : ℝ) :
    halfspaceIndicator p j ((y : FSC.Coord d)+s•w j) =
      (Iic (normalThreshold (w j) j p y)).indicator (fun _ : ℝ => 1) s := by
  classical
  have hden : 0 < inner ℝ (p.1 j) (w j) :=
    lt_trans (by norm_num) (threshold_denominator_near w b j hw p hp)
  have he : inner ℝ (p.1 j) ((y : FSC.Coord d)+s•w j) ≤ p.2 j ↔
      s ≤ normalThreshold (w j) j p y := by
    rw [normalThreshold,le_div_iff₀ hden,inner_add_right,real_inner_smul_right]
    constructor <;> intro h <;> linarith
  simp only [halfspaceIndicator,Set.indicator_apply,Set.mem_setOf_eq,Set.mem_Iic,he]

theorem linear_growth_integrable (F : FSC.Coord d → ℝ) (hFm : Measurable F)
    (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖)) :
    Integrable F (stdGaussian (FSC.Coord d)) := by
  exact (((integrable_const (1:ℝ)).add IsGaussian.integrable_id.norm).const_mul C).mono'
    hFm.aestronglyMeasurable (Eventually.of_forall hF)

theorem rest_test_integrable (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) (hF : Integrable F (stdGaussian (FSC.Coord d)))
    (p : Parameters d ι) :
    Integrable (fun x => F x * restMask (w,b) p mask j x) (stdGaussian (FSC.Coord d)) := by
  simpa only [mul_comm] using hF.bdd_mul (c:=1)
    (restMask_measurable (w,b) p mask j).aestronglyMeasurable
    (Eventually.of_forall fun x => restMask_abs_le (w,b) p mask j x)

def singleChange (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) (p : Parameters d ι) (x : FSC.Coord d) : ℝ :=
  F x * restMask (w,b) p mask j x *
    (halfspaceIndicator p j x-halfspaceIndicator (w,b) j x)

theorem singleChange_integrable (w : ι → FSC.Coord d) (b : ι → ℝ) (mask : ι → Bool)
    (j : ι) (F : FSC.Coord d → ℝ) (hF : Integrable F (stdGaussian (FSC.Coord d)))
    (p : Parameters d ι) :
    Integrable (singleChange w b mask j F p) (stdGaussian (FSC.Coord d)) := by
  have hr := rest_test_integrable w b mask j F hF p
  apply (hr.bdd_mul (c:=2)
    ((halfspaceIndicator_measurable p j).sub (halfspaceIndicator_measurable (w,b) j)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)).congr (Eventually.of_forall fun x => by
      dsimp [singleChange]; ring)
  exact (abs_sub _ _).trans (by
    linarith [halfspaceIndicator_abs_le p j x,halfspaceIndicator_abs_le (w,b) j x])

/-- The slab is exactly the change of one actual halfspace inside the mixed
remaining constraints.  This equality uses genuine Gaussian disintegration. -/
theorem maskSlab_eq_singleChange_integral (w : ι → FSC.Coord d) (b : ι → ℝ)
    (mask : ι → Bool) (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ)
    (hF : Integrable F (stdGaussian (FSC.Coord d)))
    (p : Parameters d ι) (hp : ‖p-(w,b)‖ < 1/2) :
    maskSlab w b mask j F p = ∫ x, singleChange w b mask j F p x ∂stdGaussian (FSC.Coord d) := by
  let G : FSC.Coord d → ℝ := fun x => F x * restMask (w,b) p mask j x
  have hG := rest_test_integrable w b mask j F hF p
  have hGp := integrable_normalReconstruct (w j) hw G hG
  rw [integral_tangent_normal (w j) hw _ (singleChange_integrable w b mask j F hF p)]
  unfold maskSlab
  apply integral_congr_ae
  filter_upwards [hGp.prod_right_ae] with y hy
  have hgd : Integrable (fun s => slabIntegrand w b mask j F p y s) := by
    rw [gaussianReal_of_var_ne_zero (0:ℝ) (by norm_num)] at hy
    have hh := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Eventually.of_forall fun s => by exact ENNReal.ofReal_lt_top)).mp hy
    simpa only [toReal_gaussianPDF,smul_eq_mul,slabIntegrand,WeakSimplex.normalPDF,
      normalReconstruct,G,mul_assoc] using hh
  rw [← intervalIntegral.integral_Iic_sub_Iic hgd.integrableOn hgd.integrableOn]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  have hfun : (fun s : ℝ => gaussianPDFReal 0 1 s •
      singleChange w b mask j F p ((y : FSC.Coord d)+s•w j)) =
      fun s => (Iic (normalThreshold (w j) j p y)).indicator
          (fun s => slabIntegrand w b mask j F p y s) s -
        (Iic (b j)).indicator (fun s => slabIntegrand w b mask j F p y s) s := by
    funext s
    rw [singleChange,halfspaceIndicator_normal w b j hw p hp y s,
      halfspaceIndicator_normal w b j hw (w,b) (by simp) y s,normalThreshold_base w b j hw y]
    classical
    by_cases h₁ : s≤normalThreshold (w j) j p y <;> by_cases h₂ : s≤b j <;>
      simp [Set.indicator_apply,h₁,h₂,slabIntegrand,WeakSimplex.normalPDF,smul_eq_mul] <;> ring
  rw [hfun,integral_sub (hgd.indicator measurableSet_Iic) (hgd.indicator measurableSet_Iic),
    integral_indicator measurableSet_Iic,integral_indicator measurableSet_Iic]

/-- The derived Fréchet derivative of the actual mixed single-constraint
Gaussian integral, including its row movement. -/
theorem hasFDerivAt_singleChange_integral (w : ι → FSC.Coord d)
    (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (mask : ι → Bool) (j : ι) (F : FSC.Coord d → ℝ) (hFc : Continuous F)
    (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖)) :
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
    (linear_growth_integrable F hFc.measurable C hC hF) p hp).symm



/-- Each constraint is switched once, in the canonical finite enumeration. -/
def telescopeMask (j : ι) : ι → Bool :=
  fun k => decide ((Fintype.equivFin ι k).val < (Fintype.equivFin ι j).val)

def capTest (p : Parameters d ι) (F : FSC.Coord d → ℝ) : ℝ :=
  ∫ x in FSC.cap p.1 p.2, F x ∂stdGaussian (FSC.Coord d)

def capJointDerivative (w : ι → FSC.Coord d) (b : ι → ℝ)
    (F : FSC.Coord d → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∑ j, maskSlabDerivative w b (telescopeMask j) j F

theorem cap_indicator_difference (w : ι → FSC.Coord d) (b : ι → ℝ)
    (p : Parameters d ι) (x : FSC.Coord d) :
    (FSC.cap p.1 p.2).indicator (fun _ => (1:ℝ)) x -
      (FSC.cap w b).indicator (fun _ => (1:ℝ)) x =
    ∑ j, (halfspaceIndicator p j x-halfspaceIndicator (w,b) j x) *
      restMask (w,b) p (telescopeMask j) j x := by
  classical
  have hcap (q : Parameters d ι) :
      FSC.cap q.1 q.2 = ⋂ k, {x : FSC.Coord d | inner ℝ (q.1 k) x ≤ q.2 k} := by
    ext x
    simp [FSC.cap]
  rw [hcap p,hcap (w,b)]
  have ht := NegativeVotingCapTelescoping.cap_difference_as_moving_slabs_equiv
    (Fintype.equivFin ι) (fun k => {x : FSC.Coord d | inner ℝ (p.1 k) x ≤ p.2 k})
    (fun k => {x : FSC.Coord d | inner ℝ (w k) x ≤ b k}) x
  refine ht.trans ?_
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold restMask telescopeMask mixedParameters
  congr 1
  apply propext
  apply forall_congr'
  intro k
  by_cases hk : (Fintype.equivFin ι k).val < (Fintype.equivFin ι j).val <;> simp [hk]

theorem capTest_difference_eq_sum_singleChange (w : ι → FSC.Coord d) (b : ι → ℝ)
    (F : FSC.Coord d → ℝ) (hF : Integrable F (stdGaussian (FSC.Coord d)))
    (p : Parameters d ι) :
    capTest p F-capTest (w,b) F =
      ∑ j, ∫ x, singleChange w b (telescopeMask j) j F p x ∂stdGaussian (FSC.Coord d) := by
  classical
  unfold capTest
  rw [← integral_indicator (FSC.measurableSet_cap p.1 p.2),
    ← integral_indicator (FSC.measurableSet_cap w b),
    ← integral_sub (hF.indicator (FSC.measurableSet_cap p.1 p.2))
      (hF.indicator (FSC.measurableSet_cap w b)),
    ← integral_finsetSum Finset.univ
      (fun j _ => singleChange_integrable w b (telescopeMask j) j F hF p)]
  apply integral_congr_ae
  filter_upwards with x
  have hm (S : Set (FSC.Coord d)) : S.indicator F x = F x * S.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x ∈ S <;> simp [hx]
  rw [hm,hm,← mul_sub,cap_indicator_difference,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [singleChange]
  ring

/-- Actual joint Fréchet differentiation of a Gaussian polyhedral integral in
all normal vectors and all supports.  No facet formula is a hypothesis. -/
theorem hasFDerivAt_capTest (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (F : FSC.Coord d → ℝ)
    (hFc : Continuous F) (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖)) :
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
      (linear_growth_integrable F hFc.measurable C hC hF) p
    linarith
  simp only [Finset.sum_apply] at hh
  rw [he] at hh
  exact hh



theorem constraintLinear_norm_le (x : FSC.Coord d) (j : ι) :
    ‖constraintLinear x j‖ ≤ 1+‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [constraintLinear_apply,Real.norm_eq_abs]
  calc
    _ ≤ |p.2 j| + |inner ℝ (p.1 j) x| := abs_sub _ _
    _ ≤ ‖p‖ + ‖p‖*‖x‖ := by
      apply add_le_add
      · simpa only [Real.norm_eq_abs] using (norm_le_pi_norm p.2 j).trans (norm_snd_le p)
      · exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right ((norm_le_pi_norm p.1 j).trans (norm_fst_le p)) (norm_nonneg _))
    _ = _ := by ring

theorem maskSlabDerivative_integrable (w : ι → FSC.Coord d) (b : ι → ℝ)
    (mask : ι → Bool) (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ)
    (hFc : Continuous F) (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖)) :
    Integrable (fun y : tangentSpace (w j) =>
      slabIntegrand w b mask j F (w,b) y (b j) •
        constraintLinear ((y : FSC.Coord d)+b j•w j) j)
      (stdGaussian (tangentSpace (w j))) := by
  have hM : MemLp (fun y : tangentSpace (w j) => (1+|b j|)+‖y‖) 2
      (stdGaussian (tangentSpace (w j))) :=
    (memLp_const (1+|b j|)).add
      (IsGaussian.memLp_two_id (μ := stdGaussian (tangentSpace (w j)))).norm
  have hbound : Integrable (fun y : tangentSpace (w j) =>
      (C*WeakSimplex.normalPDF (b j))*((1+|b j|)+‖y‖)^2)
      (stdGaussian (tangentSpace (w j))) :=
    hM.integrable_sq.const_mul (C*WeakSimplex.normalPDF (b j))
  apply hbound.mono'
  · apply Measurable.aestronglyMeasurable
    exact ((slabIntegrand_measurable w b mask j F hFc.measurable (w,b)).comp
      (measurable_id.prodMk measurable_const)).smul
      ((constraintLinear_continuous j).measurable.comp (by fun_prop))
  filter_upwards with y
  let x : FSC.Coord d := (y : FSC.Coord d)+b j•w j
  have hx : ‖x‖ ≤ ‖y‖+|b j| := (norm_add_le _ _).trans (by simp [norm_smul,hw])
  have hg : |slabIntegrand w b mask j F (w,b) y (b j)| ≤
      WeakSimplex.normalPDF (b j)*C*(1+‖x‖) := by
    dsimp [slabIntegrand]
    rw [abs_mul,abs_mul,abs_of_pos (WeakSimplex.normalPDF_pos (b j))]
    have hp := mul_le_mul_of_nonneg_left (hF x) (WeakSimplex.normalPDF_pos (b j)).le
    exact (mul_le_of_le_one_right (mul_nonneg (WeakSimplex.normalPDF_pos _).le
      (abs_nonneg _)) (restMask_abs_le _ _ _ _ _)).trans (by simpa only [mul_assoc] using hp)
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ (WeakSimplex.normalPDF (b j)*C*(1+‖x‖))*(1+‖x‖) :=
      mul_le_mul hg (constraintLinear_norm_le x j) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (WeakSimplex.normalPDF_pos _).le hC) (by positivity))
    _ ≤ C*WeakSimplex.normalPDF (b j)*((1+|b j|)+‖y‖)^2 := by
      have hc : 0≤C*WeakSimplex.normalPDF (b j) := mul_nonneg hC (WeakSimplex.normalPDF_pos _).le
      have hs : (1+‖x‖)^2 ≤ ((1+|b j|)+‖y‖)^2 := by nlinarith [norm_nonneg x,norm_nonneg y,abs_nonneg (b j)]
      nlinarith [mul_le_mul_of_nonneg_left hs hc]

/-- The intrinsic Gaussian face, with all remaining inequalities imposed. -/
def tangentFace (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    Set (tangentSpace (w j)) :=
  {y | ∀ k, k ≠ j → inner ℝ (w k) ((y : FSC.Coord d)+b j•w j) ≤ b k}

theorem tangentFace_measurable (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    MeasurableSet (tangentFace w b j) := by
  unfold tangentFace
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (by fun_prop) measurable_const

/-- Explicit evaluation of the actual derivative: density times the literal
Gaussian face integral of test value times boundary velocity. -/
theorem maskSlabDerivative_apply (w : ι → FSC.Coord d) (b : ι → ℝ)
    (mask : ι → Bool) (j : ι) (hw : ‖w j‖=1) (F : FSC.Coord d → ℝ)
    (hFc : Continuous F) (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖))
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

/-- The full weighted-cap derivative is the sum over its actual Gaussian faces. -/
theorem capJointDerivative_apply (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (F : FSC.Coord d → ℝ) (hFc : Continuous F)
    (C : ℝ) (hC : 0≤C) (hF : ∀ x, |F x|≤C*(1+‖x‖)) (δ : Parameters d ι) :
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

end NegativeVotingMovingCap
