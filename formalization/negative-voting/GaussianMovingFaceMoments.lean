import GaussianFanMovingCells

/-! Joint continuity of actual Gaussian face masses and first moments.
The moving plane is realized as an affine image of one fixed ambient Gaussian.
Boundary masks stabilize almost everywhere by the proved no-coincidence lemma. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators Topology

namespace NegativeVotingMovingFaceMoments
open NegativeVotingFanScore
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A common ambient Gaussian sample realizes every moving affine slice. -/
def slicePoint (p : Parameters d ι) (j : ι) (y : FSC.Coord d) : FSC.Coord d :=
  p.2 j • p.1 j + (y - inner ℝ (p.1 j) y • p.1 j)

/-- Away from null intersections with the other listed hyperplanes, every
remaining inequality has locally constant truth value as all normals and
supports vary. The base no-coincidence premise is the only regularity input. -/
theorem ae_eventually_slicePreimage_iff (w : ι → FSC.Coord d)
    (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b) (j : ι) :
    ∀ᵐ y ∂stdGaussian (FSC.Coord d), ∀ᶠ p : Parameters d ι in 𝓝 (w,b),
      y ∈ FSC.slicePreimage p.1 p.2 j ↔ y ∈ FSC.slicePreimage w b j := by
  have ha : ∀ᵐ y ∂stdGaussian (FSC.Coord d), ∀ k, k ≠ j →
      inner ℝ (w k) (slicePoint (w,b) j y) ≠ b k := by
    apply ae_all_iff.mpr
    intro k
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ h => (h hkj).elim
    · exact (FSC.ae_slice_boundary_ne w hw b hb j k hkj).mono fun _ h _ => h
  filter_upwards [ha] with y hy
  have he : ∀ k, ∀ᶠ p : Parameters d ι in 𝓝 (w,b),
      (k ≠ j → inner ℝ (p.1 k) (slicePoint p j y) ≤ p.2 k) ↔
      (k ≠ j → inner ℝ (w k) (slicePoint (w,b) j y) ≤ b k) := by
    intro k
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ => by simp [hkj]
    · have hc : ContinuousAt (fun p : Parameters d ι =>
          inner ℝ (p.1 k) (slicePoint p j y)) (w,b) := by
        unfold slicePoint
        fun_prop
      have hd : ContinuousAt (fun p : Parameters d ι => p.2 k) (w,b) := by fun_prop
      rcases lt_or_gt_of_ne (hy k hkj) with h | h
      · filter_upwards [hc.eventually_lt hd h] with p hp
        simp only [hp.le, h.le]
      · filter_upwards [hd.eventually_lt hc h] with p hp
        simp only [not_le.mpr hp, not_le.mpr h]
  filter_upwards [eventually_all.mpr he] with p hp
  exact forall_congr' hp

/-- Actual slice probabilities are jointly continuous in normals and
supports at unit, noncoincident base parameters. -/
theorem continuousAt_sliceMass_joint (w : ι → FSC.Coord d)
    (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b) (j : ι) :
    ContinuousAt (fun p : Parameters d ι => FSC.sliceMass p.1 p.2 j) (w,b) := by
  simp_rw [FSC.sliceMass_eq_stdGaussian]
  have ht : Tendsto (fun p : Parameters d ι =>
      stdGaussian (FSC.Coord d) (FSC.slicePreimage p.1 p.2 j)) (𝓝 (w,b))
      (𝓝 (stdGaussian (FSC.Coord d) (FSC.slicePreimage w b j))) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 (w,b))
      (FSC.measurableSet_slicePreimage w b j)
      (fun p : Parameters d ι => FSC.measurableSet_slicePreimage p.1 p.2 j)
    exact ae_eventually_slicePreimage_iff w hw b hb j
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp ht

/-- The actual unnormalized first moment of the pinned face. -/
def sliceFirstMoment (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) : FSC.Coord d :=
  ∫ x in {x | ∀ k, k ≠ j → inner ℝ (w k) x ≤ b k}, x ∂FSC.sliceLaw (w j) (b j)

/-- The slice first moment uses a literal ambient Gaussian integral, with
its actual moving constraint mask and actual affine slice realization. -/
theorem sliceFirstMoment_eq_stdGaussian (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    sliceFirstMoment w b j = ∫ y,
      (FSC.slicePreimage w b j).indicator (slicePoint (w,b) j) y
      ∂stdGaussian (FSC.Coord d) := by
  have hs : MeasurableSet {x : FSC.Coord d | ∀ k, k ≠ j → inner ℝ (w k) x ≤ b k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (by fun_prop) measurable_const
  unfold sliceFirstMoment FSC.sliceLaw
  rw [setIntegral_map hs
    (show AEStronglyMeasurable (fun x : FSC.Coord d => x) _ from measurable_id.aestronglyMeasurable)
    (by fun_prop)]
  exact (integral_indicator (FSC.measurableSet_slicePreimage w b j)).symm

/-- Explicit local polynomial dominator for the moving slice realization. -/
theorem slicePoint_norm_bound (p : Parameters d ι) (j : ι) (A : ℝ)
    (hn : ‖p.1 j‖ ≤ 2) (ha : |p.2 j| ≤ A) (y : FSC.Coord d) :
    ‖slicePoint p j y‖ ≤ 2*A+5*‖y‖ := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hinner : |inner ℝ (p.1 j) y| ≤ 2*‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hsmul : ‖inner ℝ (p.1 j) y • p.1 j‖ ≤ 4*‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (2*‖y‖)*2 := mul_le_mul hinner hn (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hshift : ‖p.2 j • p.1 j‖ ≤ 2*A := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ A*2 := mul_le_mul ha hn (norm_nonneg _) hA
      _ = _ := by ring
  unfold slicePoint
  calc
    _ ≤ ‖p.2 j • p.1 j‖ + ‖y-inner ℝ (p.1 j) y • p.1 j‖ := norm_add_le _ _
    _ ≤ 2*A + (‖y‖+4*‖y‖) := add_le_add hshift ((norm_sub_le _ _).trans (add_le_add le_rfl hsmul))
    _ = _ := by ring

/-- The actual face first moment is jointly continuous. A fixed ambient
Gaussian and the explicit linear dominator discharge dominated convergence. -/
theorem continuousAt_sliceFirstMoment_joint (w : ι → FSC.Coord d)
    (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b) (j : ι) :
    ContinuousAt (fun p : Parameters d ι => sliceFirstMoment p.1 p.2 j) (w,b) := by
  change Tendsto _ _ _
  simp_rw [sliceFirstMoment_eq_stdGaussian]
  apply tendsto_integral_filter_of_dominated_convergence (fun y : FSC.Coord d =>
    2*(|b j|+1)+5*‖y‖)
  · apply Eventually.of_forall
    intro p
    apply Measurable.aestronglyMeasurable
    exact (by unfold slicePoint; fun_prop : Measurable (slicePoint p j)).indicator
      (FSC.measurableSet_slicePreimage p.1 p.2 j)
  · have hn : ∀ᶠ p : Parameters d ι in 𝓝 (w,b), ‖p.1 j‖ < 2 :=
      (show ContinuousAt (fun p : Parameters d ι => ‖p.1 j‖) (w,b) by fun_prop).eventually_lt
        continuousAt_const (by simpa only [hw j] using (by norm_num : (1:ℝ)<2))
    have ha : ∀ᶠ p : Parameters d ι in 𝓝 (w,b), |p.2 j| < |b j|+1 :=
      (show ContinuousAt (fun p : Parameters d ι => |p.2 j|) (w,b) by fun_prop).eventually_lt
        continuousAt_const (by linarith)
    filter_upwards [hn,ha] with p hp hpa
    apply Eventually.of_forall
    intro y
    by_cases hy : y ∈ FSC.slicePreimage p.1 p.2 j
    · simpa only [Set.indicator_of_mem hy] using slicePoint_norm_bound p j (|b j|+1) hp.le hpa.le y
    · simp only [Set.indicator_of_notMem hy, norm_zero]
      positivity
  · exact (integrable_const _).add (IsGaussian.integrable_id.norm.const_mul 5)
  · filter_upwards [ae_eventually_slicePreimage_iff w hw b hb j] with y hy
    have hc : ContinuousAt (fun p : Parameters d ι => slicePoint p j y) (w,b) := by
      unfold slicePoint
      fun_prop
    have he : (fun p : Parameters d ι => (FSC.slicePreimage p.1 p.2 j).indicator (slicePoint p j) y)
        =ᶠ[𝓝 (w,b)] (fun p => (FSC.slicePreimage w b j).indicator (slicePoint p j) y) := by
      filter_upwards [hy] with p hp
      by_cases hmem : y ∈ FSC.slicePreimage w b j
      · simp [hmem,hp.mpr hmem]
      · have hn : y ∉ FSC.slicePreimage p.1 p.2 j := fun hm => hmem (hp.mp hm)
        simp [hmem,hn]
    apply Filter.Tendsto.congr' he.symm
    by_cases hmem : y ∈ FSC.slicePreimage w b j
    · simpa only [Set.indicator_of_mem hmem] using hc.tendsto
    · simp only [Set.indicator_of_notMem hmem]
      exact tendsto_const_nhds

end NegativeVotingMovingFaceMoments
