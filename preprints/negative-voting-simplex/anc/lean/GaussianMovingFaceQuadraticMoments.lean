import GaussianMovingFaceMoments

/-! Actual moving Gaussian slice integrals of quadratic-growth tests. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators Topology
namespace NegativeVotingMovingFaceQuadratic
open NegativeVotingMovingFaceMoments NegativeVotingFanScore
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def sliceTest (w : ι→FSC.Coord d) (b : ι→ℝ) (j : ι) (F : FSC.Coord d→ℝ) : ℝ :=
  ∫ x in {x | ∀ k,k≠j→inner ℝ (w k) x≤b k}, F x ∂FSC.sliceLaw (w j) (b j)

theorem sliceTest_eq_stdGaussian (w : ι→FSC.Coord d) (b : ι→ℝ) (j : ι)
    (F : FSC.Coord d→ℝ) (hF : Measurable F) :
    sliceTest w b j F=∫ y,(FSC.slicePreimage w b j).indicator
      (fun y=>F (slicePoint (w,b) j y)) y ∂stdGaussian (FSC.Coord d) := by
  have hs : MeasurableSet {x : FSC.Coord d | ∀ k,k≠j→inner ℝ (w k) x≤b k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k=>MeasurableSet.iInter fun _=>
      measurableSet_le (by fun_prop) measurable_const
  unfold sliceTest FSC.sliceLaw
  rw [setIntegral_map hs hF.aestronglyMeasurable (by fun_prop)]
  exact (integral_indicator (FSC.measurableSet_slicePreimage w b j)).symm

/-- Dominated convergence is discharged using the actual affine slice law,
its almost-everywhere stable face mask, and a fixed Gaussian quadratic dominator. -/
theorem continuousAt_sliceTest_quadratic_growth (w : ι→FSC.Coord d)
    (hw : ∀ k,‖w k‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b) (j : ι)
    (F : FSC.Coord d→ℝ) (hF : Continuous F) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ x,‖F x‖≤K*(1+‖x‖)^2) :
    ContinuousAt (fun p : Parameters d ι=>sliceTest p.1 p.2 j F) (w,b) := by
  change Tendsto _ _ _
  simp_rw [sliceTest_eq_stdGaussian _ _ _ F hF.measurable]
  let A:ℝ:=|b j|+1
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y : FSC.Coord d=>K*(1+2*A+5*‖y‖)^2)
  · apply Eventually.of_forall
    intro p
    apply Measurable.aestronglyMeasurable
    exact (hF.measurable.comp (by unfold slicePoint;fun_prop)).indicator
      (FSC.measurableSet_slicePreimage p.1 p.2 j)
  · have hn : ∀ᶠ p : Parameters d ι in 𝓝 (w,b),‖p.1 j‖<2 :=
      (show ContinuousAt (fun p : Parameters d ι=>‖p.1 j‖) (w,b) by fun_prop).eventually_lt
        continuousAt_const (by simpa only [hw j] using (by norm_num : (1:ℝ)<2))
    have ha : ∀ᶠ p : Parameters d ι in 𝓝 (w,b),|p.2 j|<A :=
      (show ContinuousAt (fun p : Parameters d ι=>|p.2 j|) (w,b) by fun_prop).eventually_lt
        continuousAt_const (by dsimp [A];linarith)
    filter_upwards [hn,ha] with p hp hpa
    apply Eventually.of_forall
    intro y
    by_cases hy:y∈FSC.slicePreimage p.1 p.2 j
    · simp only [Set.indicator_of_mem hy]
      have hx:=slicePoint_norm_bound p j A hp.le hpa.le y
      apply (hbound _).trans
      apply mul_le_mul_of_nonneg_left _ hK
      apply pow_le_pow_left₀ (by positivity)
      linarith
    · simp only [Set.indicator_of_notMem hy,norm_zero]
      exact mul_nonneg hK (sq_nonneg _)
  · have hid : MemLp (fun y : FSC.Coord d=>y) 2 (stdGaussian (FSC.Coord d)) :=
      IsGaussian.memLp_two_id
    have hconst : MemLp (fun _ : FSC.Coord d=>1+2*A) 2 (stdGaussian (FSC.Coord d)) :=
      memLp_const _
    have hm : MemLp (fun y : FSC.Coord d=>1+2*A+5*‖y‖) 2 (stdGaussian (FSC.Coord d)) :=
      hconst.add (hid.norm.const_mul (5:ℝ))
    exact hm.integrable_sq.const_mul K
  · filter_upwards [ae_eventually_slicePreimage_iff w hw b hb j] with y hy
    have hc : ContinuousAt (fun p : Parameters d ι=>F (slicePoint p j y)) (w,b) :=
      hF.continuousAt.comp (by unfold slicePoint;fun_prop)
    have he : (fun p : Parameters d ι=>(FSC.slicePreimage p.1 p.2 j).indicator
        (fun y=>F (slicePoint p j y)) y)=ᶠ[𝓝 (w,b)]
        (fun p=>(FSC.slicePreimage w b j).indicator (fun y=>F (slicePoint p j y)) y) := by
      filter_upwards [hy] with p hp
      by_cases hmem:y∈FSC.slicePreimage w b j
      · simp [hmem,hp.mpr hmem]
      · have hn:y∉FSC.slicePreimage p.1 p.2 j:=fun hm=>hmem (hp.mp hm)
        simp [hmem,hn]
    apply Filter.Tendsto.congr' he.symm
    by_cases hmem:y∈FSC.slicePreimage w b j
    · simpa only [Set.indicator_of_mem hmem] using hc.tendsto
    · simp only [Set.indicator_of_notMem hmem]
      exact tendsto_const_nhds

theorem affine_abs_bound (u x : FSC.Coord d) (a : ℝ) :
    |inner ℝ u x+a|≤(‖u‖+|a|)*(1+‖x‖) := by
  have hh:=abs_add_le (inner ℝ u x) a
  have hi:=abs_real_inner_le_norm u x
  nlinarith [norm_nonneg u,norm_nonneg x,abs_nonneg a,mul_nonneg (abs_nonneg a) (norm_nonneg x)]

/-- The literal affine-product face tests occurring in the full Hessian are
jointly continuous as all normal vectors and thresholds move. -/
theorem continuousAt_slice_affine_product (w : ι→FSC.Coord d)
    (hw : ∀ k,‖w k‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b) (j : ι)
    (u v : FSC.Coord d) (a c : ℝ) :
    ContinuousAt (fun p : Parameters d ι=>sliceTest p.1 p.2 j
      (fun x=>(inner ℝ u x+a)*(inner ℝ v x+c))) (w,b) := by
  apply continuousAt_sliceTest_quadratic_growth w hw b hb j _ (by fun_prop)
    ((‖u‖+|a|)*(‖v‖+|c|)) (by positivity)
  intro x
  rw [Real.norm_eq_abs,abs_mul]
  calc
    _ ≤ ((‖u‖+|a|)*(1+‖x‖))*((‖v‖+|c|)*(1+‖x‖)) :=
      mul_le_mul (affine_abs_bound u x a) (affine_abs_bound v x c) (abs_nonneg _) (by positivity)
    _ = _ := by ring

end NegativeVotingMovingFaceQuadratic
