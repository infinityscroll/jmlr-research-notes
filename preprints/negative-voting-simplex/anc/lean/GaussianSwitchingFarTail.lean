import GaussianFanCover

/-! Actual switching reward beyond one normal unit, controlled by a genuine
L32 moment on the ambient Gaussian space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Classical ENNReal
namespace NegativeVotingSwitchingFarTail
open NegativeVotingFan

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem orderedReward_far_bound (s v : V → ℝ) (i j : V) (θ ell : ℝ)
    (hθ : 0 ≤ θ) (hell : 0 < ell) (hgap : ell ≤ s i-s j) :
    orderedReward s v θ i j ≤ (θ^32/ell^31)*|v i+v j|^32 := by
  have hz : 1 ≤ (s i-s j)/ell := (le_div_iff₀ hell).mpr (by simpa only [one_mul] using hgap)
  have hb := NegativeVotingCapTail.far_reward_pointwise (v i+v j) ((s i-s j)/ell) θ ell hθ hell hz
  have he : ell*((s i-s j)/ell)=s i-s j := by field_simp
  simpa only [NegativeVotingSmallCap.fibreReward,he,orderedReward] using hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def farCell (B : V → E) (h : V → ℝ) (i j : V) (ell : ℝ) : Set E :=
  affineCell B h i ∩ {x | ell ≤ affineScore B h i x-affineScore B h j x}

theorem measurableSet_farCell (B : V → E) (h : V → ℝ) (i j : V) (ell : ℝ) :
    MeasurableSet (farCell B h i j ell) := by
  apply (isClosed_affineCell B h i).measurableSet.inter
  exact (isClosed_le continuous_const (by unfold affineScore; fun_prop)).measurableSet

def farCellReward (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) : E → ℝ :=
  (farCell B h i j ell).indicator
    (fun x => orderedReward (fun k => affineScore B h k x) (v x) θ i j)

theorem farCellReward_nonneg (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (x : E) :
    0 ≤ farCellReward B h i j v θ ell x := by
  by_cases hx : x ∈ farCell B h i j ell
  · simp only [farCellReward,Set.indicator_of_mem hx,orderedReward]
    exact le_max_right _ _
  · simp only [farCellReward,Set.indicator_of_notMem hx,le_refl]

theorem farCellReward_le_power (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (hθ : 0 ≤ θ) (hell : 0 < ell) (x : E) :
    farCellReward B h i j v θ ell x ≤ (θ^32/ell^31)*|v x i+v x j|^32 := by
  by_cases hx : x ∈ farCell B h i j ell
  · simpa only [farCellReward,Set.indicator_of_mem hx] using
      orderedReward_far_bound (fun k => affineScore B h k x) (v x) i j θ ell hθ hell hx.2
  · simp only [farCellReward,Set.indicator_of_notMem hx]
    positivity

/-- Ambient integrability is derived, and the literal far-cell reward is
bounded without a conditional-face probability premise. -/
theorem integral_farCellReward_bound (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (hθ : 0 ≤ θ) (hell : 0 < ell)
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E)) :
    Integrable (farCellReward B h i j v θ ell) (stdGaussian E) ∧
    (∫ x, farCellReward B h i j v θ ell x ∂stdGaussian E) ≤
      (θ^32/ell^31)*(∫ x, |v x i+v x j|^32 ∂stdGaussian E) := by
  have hm : AEStronglyMeasurable
      (fun x => orderedReward (fun k => affineScore B h k x) (v x) θ i j) (stdGaussian E) := by
    unfold orderedReward
    have hg : Measurable (fun x => affineScore B h i x-affineScore B h j x) := by
      have : Continuous (fun x => affineScore B h i x-affineScore B h j x) := by
        unfold affineScore
        fun_prop
      exact this.measurable
    exact (((aemeasurable_const.mul hv.aestronglyMeasurable.aemeasurable).sub hg.aemeasurable).max
      aemeasurable_const).aestronglyMeasurable
  have hfm : AEStronglyMeasurable (farCellReward B h i j v θ ell) (stdGaussian E) :=
    hm.indicator (measurableSet_farCell B h i j ell)
  have hpower : Integrable (fun x => |v x i+v x j|^32) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs] using hv.integrable_norm_pow'
  have hmajor := hpower.const_mul (θ^32/ell^31)
  have hfi : Integrable (farCellReward B h i j v θ ell) (stdGaussian E) := by
    apply hmajor.mono' hfm
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (farCellReward_nonneg B h i j v θ ell x)]
    exact farCellReward_le_power B h i j v θ ell hθ hell x
  refine ⟨hfi,?_⟩
  have hb := integral_mono_ae hfi hmajor
    (Eventually.of_forall (farCellReward_le_power B h i j v θ ell hθ hell))
  simpa only [integral_const_mul] using hb

end NegativeVotingSwitchingFarTail
