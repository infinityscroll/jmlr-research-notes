import GaussianFacetDisintegration
import GaussianSmallCap

/-! Actual old-cell normal fibres. The main term is charged to the true
winning facet; a non-facet projection is charged only to the geometric
third-label escape event. No minimum switching amplitude is imposed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace BigOperators Classical
namespace NegativeVotingSwitchingFibre
open NegativeVotingFan NegativeVotingSmallCap

section Scalar

def gaussianReward (u : ℝ → ℝ) (a θ ell z : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (a+z) * fibreReward (θ*u z) ell z

theorem gaussianReward_nonneg (u : ℝ → ℝ) (a θ ell z : ℝ) :
    0 ≤ gaussianReward u a θ ell z :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (le_max_right _ _)

theorem gaussianReward_continuousOn (u : ℝ → ℝ) (a θ ell : ℝ)
    (hu : ContinuousOn u (Icc 0 1)) :
    ContinuousOn (gaussianReward u a θ ell) (Icc 0 1) := by
  unfold gaussianReward fibreReward
  have hd : Continuous (fun z : ℝ => gaussianPDFReal 0 1 (a+z)) := by
    unfold gaussianPDFReal
    fun_prop
  exact hd.continuousOn.mul (((continuousOn_const.mul hu).sub
    (continuousOn_const.mul continuousOn_id)).sup continuousOn_const)

theorem restricted_reward_integrable (u : ℝ → ℝ) (a θ ell : ℝ)
    (hu : ContinuousOn u (Icc 0 1)) (S : Set ℝ) (hS : MeasurableSet S) :
    IntervalIntegrable (S.indicator (gaussianReward u a θ ell)) volume 0 1 := by
  have hi : IntervalIntegrable (gaussianReward u a θ ell) volume 0 1 :=
    (gaussianReward_continuousOn u a θ ell hu).intervalIntegrable_of_Icc
    (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨hi.1.indicator hS,hi.2.indicator hS⟩

theorem restricted_reward_le_full (u : ℝ → ℝ) (a θ ell : ℝ)
    (hu : ContinuousOn u (Icc 0 1)) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ z in (0:ℝ)..1, S.indicator (gaussianReward u a θ ell) z) ≤
      ∫ z in (0:ℝ)..1, gaussianReward u a θ ell z := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (restricted_reward_integrable u a θ ell hu S hS)
    ((gaussianReward_continuousOn u a θ ell hu).intervalIntegrable_of_Icc (by norm_num))
  intro z hz
  by_cases hs : z ∈ S
  · simp only [Set.indicator_of_mem hs]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hs]
    exact gaussianReward_nonneg u a θ ell z

theorem restricted_reward_zero (u : ℝ → ℝ) (a θ M ell : ℝ)
    (hθ : 0 ≤ θ) (hell : 0 < ell) (S : Set ℝ)
    (hsup : ∀ z ∈ Icc (0:ℝ) 1, u z ≤ M)
    (hempty : ∀ z ∈ Icc (0:ℝ) (θ*M/ell), z ∉ S) :
    (∫ z in (0:ℝ)..1, S.indicator (gaussianReward u a θ ell) z) = 0 := by
  calc
    _ = ∫ z in (0:ℝ)..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro z hz
      by_cases hc : z ≤ θ*M/ell
      · exact Set.indicator_of_notMem (hempty z ⟨hz.1.le,hc⟩) _
      · have he := fibreReward_zero_past_cutoff u θ M ell z hθ hell
          (hsup z ⟨hz.1.le,hz.2.le⟩) (le_of_not_ge hc)
        by_cases hs : z ∈ S <;> simp [hs,gaussianReward,he]
    _ = 0 := by simp

end Scalar

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V]

def cellFibreSet (B : V → E) (h : V → ℝ) (i : V) (p n : E) : Set ℝ :=
  {z | p+z • n ∈ affineCell B h i}

theorem measurableSet_cellFibreSet (B : V → E) (h : V → ℝ) (i : V) (p n : E) :
    MeasurableSet (cellFibreSet B h i p n) := by
  exact ((isClosed_affineCell B h i).preimage (by fun_prop)).measurableSet

def unitCellReward (B : V → E) (h : V → ℝ) (i : V) (p n : E)
    (u : ℝ → ℝ) (a θ ell : ℝ) : ℝ :=
  ∫ z in (0:ℝ)..1, (cellFibreSet B h i p n).indicator (gaussianReward u a θ ell) z

/-- The true facet and the actual short escape event account for every
nonzero good-fibre contribution. The cubic error is independent of any
assumed lower bound on θ. -/
theorem good_unit_cell_reward (B : V → E) (h : V → ℝ) (i j : V)
    (p n : E) (y : ((ℝ ∙ (B i-B j))ᗮ))
    (u : ℝ → ℝ) (a θ M ell : ℝ)
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hell : 0 < ell)
    (hη1 : θ*M/ell ≤ 1) (hsmall : (1+|a|)*(θ*M/ell) ≤ 1/2)
    (hu : ContinuousOn u (Icc 0 1))
    (hsup : ∀ z ∈ Icc (0:ℝ) 1, u z ≤ M)
    (hlip : ∀ z ∈ Icc (0:ℝ) (θ*M/ell), |u z-u 0| ≤ M*z) :
    unitCellReward B h i (p+(y:E)) n u a θ ell ≤
      (if p+(y:E) ∈ affineFacet B h i j then
        gaussianPDFReal 0 1 a * (θ*max (u 0) 0)^2/(2*ell) else 0) +
      (if y ∈ projectedEscape B h i j p n (θ*M/ell) then
        gaussianPDFReal 0 1 a * (θ*M)^2/(2*ell) else 0) +
      gaussianPDFReal 0 1 a*(2+|a|)*θ^3*M^3/ell^2 := by
  have hpdf : 0 ≤ gaussianPDFReal 0 1 a := gaussianPDFReal_nonneg _ _ _
  have he0 : 0 ≤ gaussianPDFReal 0 1 a*(2+|a|)*θ^3*M^3/ell^2 := by positivity
  have hm0 : 0 ≤ gaussianPDFReal 0 1 a*(θ*M)^2/(2*ell) := by positivity
  have hu0 : max (u 0) 0 ≤ M := max_le (hsup 0 ⟨le_rfl,by norm_num⟩) hM
  have hupper := sub_le_iff_le_add.mp (le_of_abs_le
    (gaussian_unit_fibre_cubic u a θ M ell hθ hM hell hη1 hsmall hu hsup hlip))
  simp only [←mul_div_assoc] at hupper
  have hb := (restricted_reward_le_full u a θ ell hu (cellFibreSet B h i (p+(y:E)) n)
    (measurableSet_cellFibreSet B h i (p+(y:E)) n)).trans hupper
  change unitCellReward B h i (p+(y:E)) n u a θ ell ≤ _ at hb
  by_cases hf : p+(y:E) ∈ affineFacet B h i j
  · simp only [hf,ite_true]
    have hr : 0 ≤ if y ∈ projectedEscape B h i j p n (θ*M/ell) then
        gaussianPDFReal 0 1 a*(θ*M)^2/(2*ell) else 0 := by split_ifs <;> positivity
    linarith
  · simp only [hf,ite_false,zero_add]
    by_cases hx : y ∈ projectedEscape B h i j p n (θ*M/ell)
    · simp only [hx,ite_true]
      have hs : (θ*max (u 0) 0)^2 ≤ (θ*M)^2 :=
        pow_le_pow_left₀ (mul_nonneg hθ (le_max_right _ _))
          (mul_le_mul_of_nonneg_left hu0 hθ) 2
      have ht := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs hpdf) (by positivity : 0 ≤ 2*ell)
      linarith
    · simp only [hx,ite_false,zero_add]
      have hz := restricted_reward_zero u a θ M ell hθ hell
        (cellFibreSet B h i (p+(y:E)) n) hsup (by
          intro z hz hcell
          apply hx
          exact ⟨hf,z,hz.1,hz.2,hcell⟩)
      change unitCellReward B h i (p+(y:E)) n u a θ ell = 0 at hz
      rw [hz]
      exact he0

/-- This is the literal affine ordered switching reward, with its exact
normal slope. The forcing may vary with the ambient point. -/
theorem gaussianReward_eq_ordered (B : V → E) (h : V → ℝ) (i j : V)
    (p : E) (v : E → V → ℝ) (a θ z : ℝ)
    (hp : affineScore B h i p=affineScore B h j p) :
    gaussianReward (fun s => v (p+s • pairNormal B i j) i+
      v (p+s • pairNormal B i j) j) a θ ‖B i-B j‖ z =
    gaussianPDFReal 0 1 (a+z) *
      orderedReward (fun k => affineScore B h k (p+z • pairNormal B i j))
        (v (p+z • pairNormal B i j)) θ i j := by
  rw [orderedReward_along_pairNormal B h _ θ i j p z hp]
  rfl

end Geometry
end NegativeVotingSwitchingFibre
