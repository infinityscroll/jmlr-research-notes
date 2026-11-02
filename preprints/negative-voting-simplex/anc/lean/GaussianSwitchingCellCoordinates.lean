import GaussianSwitchingFarTail
import GaussianSwitchingFibreIntegration
import GaussianWeightedFacetEnergy

/-! Literal ambient-cell switching integrals and their pair-normal coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Classical ENNReal
namespace NegativeVotingSwitchingCell
open NegativeVotingFan NegativeVotingSmallCap NegativeVotingSwitchingFarTail
  NegativeVotingSwitchingFibre NegativeVotingSwitchingFibreIntegration
  NegativeVotingWeightedFacet NegativeVotingDisintegration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V]

def cellReward (B : V → E) (h : V → ℝ) (i j : V) (v : E → V → ℝ) (θ : ℝ) : E → ℝ :=
  (affineCell B h i).indicator (fun x =>
    orderedReward (fun k => affineScore B h k x) (v x) θ i j)

def nearCellReward (B : V → E) (h : V → ℝ) (i j : V) (v : E → V → ℝ) (θ ell : ℝ) : E → ℝ :=
  {x | affineScore B h i x-affineScore B h j x ≤ ell}.indicator (cellReward B h i j v θ)

theorem nearCellReward_of_le (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (x : E)
    (hx : affineScore B h i x-affineScore B h j x ≤ ell) :
    nearCellReward B h i j v θ ell x=cellReward B h i j v θ x := by
  exact Set.indicator_of_mem (show x ∈ {y : E | affineScore B h i y-affineScore B h j y ≤ ell} from hx) _

theorem nearCellReward_of_not_le (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (x : E)
    (hx : ¬affineScore B h i x-affineScore B h j x ≤ ell) :
    nearCellReward B h i j v θ ell x=0 := by
  exact Set.indicator_of_notMem (show x ∉ {y : E | affineScore B h i y-affineScore B h j y ≤ ell} from hx) _

theorem cellReward_nonneg (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ : ℝ) (x : E) : 0 ≤ cellReward B h i j v θ x := by
  by_cases hx : x ∈ affineCell B h i
  · simp only [cellReward,Set.indicator_of_mem hx,orderedReward]
    exact le_max_right _ _
  · simp only [cellReward,Set.indicator_of_notMem hx,le_refl]

theorem cellReward_le_absolute_forcing (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (x : E) :
    cellReward B h i j v θ x ≤ θ*|v x i+v x j| := by
  by_cases hx : x ∈ affineCell B h i
  · simp only [cellReward,Set.indicator_of_mem hx,orderedReward]
    have hg : 0 ≤ affineScore B h i x-affineScore B h j x := sub_nonneg.mpr (hx j)
    have hu := mul_le_mul_of_nonneg_left (le_abs_self (v x i+v x j)) hθ
    exact max_le (by linarith) (mul_nonneg hθ (abs_nonneg _))
  · simp only [cellReward,Set.indicator_of_notMem hx]
    positivity

theorem cellReward_integrable (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E)) :
    Integrable (cellReward B h i j v θ) (stdGaussian E) := by
  have hg : AEStronglyMeasurable (fun x => affineScore B h i x-affineScore B h j x) (stdGaussian E) := by
    have : Continuous (fun x => affineScore B h i x-affineScore B h j x) := by
      unfold affineScore
      fun_prop
    exact this.aestronglyMeasurable
  have hr : AEStronglyMeasurable (fun x =>
      orderedReward (fun k => affineScore B h k x) (v x) θ i j) (stdGaussian E) :=
    ((hv.aestronglyMeasurable.const_mul θ).sub hg).sup aestronglyMeasurable_const
  have hm : AEStronglyMeasurable (cellReward B h i j v θ) (stdGaussian E) :=
    hr.indicator (isClosed_affineCell B h i).measurableSet
  have hd : Integrable (fun x => θ*|v x i+v x j|) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs] using (hv.norm.integrable (by norm_num)).const_mul θ
  apply hd.mono' hm
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (cellReward_nonneg B h i j v θ x)]
  exact cellReward_le_absolute_forcing B h i j v θ hθ x

theorem nearCellReward_integrable (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (hθ : 0 ≤ θ)
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E)) :
    Integrable (nearCellReward B h i j v θ ell) (stdGaussian E) := by
  apply (cellReward_integrable B h i j v θ hθ hv).indicator
  exact (isClosed_le (by unfold affineScore; fun_prop) continuous_const).measurableSet

theorem cellReward_le_near_add_far (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (x : E) :
    cellReward B h i j v θ x ≤ nearCellReward B h i j v θ ell x+
      farCellReward B h i j v θ ell x := by
  by_cases hc : x ∈ affineCell B h i
  · by_cases hn : affineScore B h i x-affineScore B h j x ≤ ell
    · rw [nearCellReward_of_le B h i j v θ ell x hn]
      linarith [farCellReward_nonneg B h i j v θ ell x]
    · have hf : x ∈ farCell B h i j ell := ⟨hc,(lt_of_not_ge hn).le⟩
      rw [nearCellReward_of_not_le B h i j v θ ell x hn]
      simp only [cellReward,Set.indicator_of_mem hc,farCellReward,
        Set.indicator_of_mem hf,zero_add,le_refl]
  · have he : cellReward B h i j v θ x=0 := Set.indicator_of_notMem hc _
    have hn : nearCellReward B h i j v θ ell x=0 := by
      by_cases hh : affineScore B h i x-affineScore B h j x ≤ ell
      · rw [nearCellReward_of_le B h i j v θ ell x hh,he]
      · exact nearCellReward_of_not_le B h i j v θ ell x hh
    rw [he,hn,zero_add]
    exact farCellReward_nonneg B h i j v θ ell x


/-- The full cell integral is reduced to its unit normal part and a literal
ambient L32 tail. -/
theorem integral_cellReward_le_near_add_power (B : V → E) (h : V → ℝ) (i j : V)
    (v : E → V → ℝ) (θ ell : ℝ) (hθ : 0 ≤ θ) (hell : 0 < ell)
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E)) :
    (∫ x,cellReward B h i j v θ x ∂stdGaussian E) ≤
      (∫ x,nearCellReward B h i j v θ ell x ∂stdGaussian E)+
      (θ^32/ell^31)*(∫ x,|v x i+v x j|^32 ∂stdGaussian E) := by
  have hn := nearCellReward_integrable B h i j v θ ell hθ hv
  obtain ⟨hf,hfb⟩ := integral_farCellReward_bound B h i j v θ ell hθ hell hv
  have hb := integral_mono_ae (g := fun x => nearCellReward B h i j v θ ell x+
    farCellReward B h i j v θ ell x) (cellReward_integrable B h i j v θ hθ hv)
      (hn.add hf) (Eventually.of_forall (cellReward_le_near_add_far B h i j v θ ell))
  rw [integral_add hn hf] at hb
  linarith

/-- The normalized and unnormalized comparison directions have the same
literal tangent subspace. -/
theorem tangentSpace_pairNormal (B : V → E) (i j : V) (hij : B i ≠ B j) :
    tangentSpace (pairNormal B i j)=(ℝ ∙ (B i-B j))ᗮ := by
  have hn : ‖B i-B j‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  unfold tangentSpace pairNormal
  rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn))]

/-- The actual near-cell integrand has exactly the interval [0,1] in its
normal coordinate. No tie-null hypothesis is inserted. -/
theorem nearCellReward_normal_integrand (B : V → E) (h : V → ℝ) (i j : V)
    (hij : B i ≠ B j) (v : E → V → ℝ) (θ a : ℝ) (p : E)
    (hp : affineScore B h i p=affineScore B h j p) (z : ℝ) :
    gaussianPDFReal 0 1 (a+z)*
      nearCellReward B h i j v θ ‖B i-B j‖ (p+z • pairNormal B i j) =
    (Icc (0:ℝ) 1).indicator
      ((cellFibreSet B h i p (pairNormal B i j)).indicator
        (gaussianReward (fun s => v (p+s • pairNormal B i j) i+
          v (p+s • pairNormal B i j) j) a θ ‖B i-B j‖)) z := by
  have hell : 0 < ‖B i-B j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hij)
  have hgap := affine_gap_along_pairNormal B h i j p z hp
  by_cases hc : p+z • pairNormal B i j ∈ affineCell B h i
  · have hz0 : 0 ≤ z := by
      apply (mul_le_mul_iff_right₀ hell).mp
      have hg := sub_nonneg.mpr (hc j)
      simpa only [hgap,mul_zero] using hg
    have hc' : z ∈ cellFibreSet B h i p (pairNormal B i j) := hc
    by_cases hz1 : z ≤ 1
    · have hn : affineScore B h i (p+z • pairNormal B i j)-
          affineScore B h j (p+z • pairNormal B i j) ≤ ‖B i-B j‖ := by
        rw [hgap]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hz1 hell.le
      have hz : z ∈ Icc (0:ℝ) 1 := ⟨hz0,hz1⟩
      simp only [Set.indicator_of_mem hz,Set.indicator_of_mem hc']
      rw [nearCellReward_of_le B h i j v θ ‖B i-B j‖ _ hn]
      simp only [cellReward,Set.indicator_of_mem hc]
      rw [orderedReward_along_pairNormal B h _ θ i j p z hp]
      rfl
    · have hn : ¬affineScore B h i (p+z • pairNormal B i j)-
          affineScore B h j (p+z • pairNormal B i j) ≤ ‖B i-B j‖ := by
        rw [hgap]
        intro he
        exact hz1 ((mul_le_mul_iff_right₀ hell).mp (by simpa only [mul_one] using he))
      have hz : z ∉ Icc (0:ℝ) 1 := fun he => hz1 he.2
      rw [nearCellReward_of_not_le B h i j v θ ‖B i-B j‖ _ hn,mul_zero,Set.indicator_of_notMem hz]
  · have hc' : z ∉ cellFibreSet B h i p (pairNormal B i j) := hc
    have he : cellReward B h i j v θ (p+z • pairNormal B i j)=0 := Set.indicator_of_notMem hc _
    have hnear : nearCellReward B h i j v θ ‖B i-B j‖ (p+z • pairNormal B i j)=0 := by
      by_cases hn : affineScore B h i (p+z • pairNormal B i j)-
        affineScore B h j (p+z • pairNormal B i j) ≤ ‖B i-B j‖
      · rw [nearCellReward_of_le B h i j v θ ‖B i-B j‖ _ hn,he]
      · exact nearCellReward_of_not_le B h i j v θ ‖B i-B j‖ _ hn
    rw [hnear,mul_zero]
    by_cases hz : z ∈ Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hz,Set.indicator_of_notMem hc']
    · rw [Set.indicator_of_notMem hz]


/-- Exact Gaussian disintegration of the actual near-cell reward. Endpoint
sets disappear through the one-dimensional Lebesgue integral identity. -/
theorem integral_nearCellReward_pair_normal (B : V → E) (h : V → ℝ) (i j : V)
    (hij : B i ≠ B j) (v : E → V → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E)) :
    (∫ x,nearCellReward B h i j v θ ‖B i-B j‖ x ∂stdGaussian E)=
      ∫ y : tangentSpace (pairNormal B i j),
        unitCellReward B h i (facetChart B h i j y) (pairNormal B i j)
          (fun z => v (facetChart B h i j y+z • pairNormal B i j) i+
            v (facetChart B h i j y+z • pairNormal B i j) j)
          (pairOffset B h i j) θ ‖B i-B j‖ ∂stdGaussian _ := by
  rw [integral_shifted_pair_plane (pairNormal B i j) (pairNormal_norm B i j hij)
    (pairOffset B h i j) _ (nearCellReward_integrable B h i j v θ ‖B i-B j‖ hθ hv)]
  apply integral_congr_ae
  filter_upwards with y
  have he (z : ℝ) : (y:E)+(pairOffset B h i j+z) • pairNormal B i j=
      facetChart B h i j y+z • pairNormal B i j := by
    simp only [facetChart,add_smul,add_assoc]
  simp_rw [he]
  have heq : (fun z : ℝ => gaussianPDFReal 0 1 (pairOffset B h i j+z)*
      nearCellReward B h i j v θ ‖B i-B j‖ (facetChart B h i j y+z • pairNormal B i j))=
      (Icc (0:ℝ) 1).indicator
        ((cellFibreSet B h i (facetChart B h i j y) (pairNormal B i j)).indicator
          (gaussianReward (fun z => v (facetChart B h i j y+z • pairNormal B i j) i+
            v (facetChart B h i j y+z • pairNormal B i j) j)
            (pairOffset B h i j) θ ‖B i-B j‖)) := by
    funext z
    exact nearCellReward_normal_integrand B h i j hij v θ (pairOffset B h i j)
      (facetChart B h i j y) (facetChart_on_pair_plane B h i j hij y) z
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm

/-- The same actual integral in the unnormalized edge-tangent convention
used by the third-label Gaussian escape bound. -/
theorem integral_nearCellReward_edge_normal (B : V → E) (h : V → ℝ) (i j : V)
    (hij : B i ≠ B j) (v : E → V → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E)) :
    (∫ x,nearCellReward B h i j v θ ‖B i-B j‖ x ∂stdGaussian E)=
      ∫ y : ((ℝ ∙ (B i-B j))ᗮ),
        unitCellReward B h i (pairOffset B h i j • pairNormal B i j+(y:E)) (pairNormal B i j)
          (fun z => v (pairOffset B h i j • pairNormal B i j+(y:E)+z • pairNormal B i j) i+
            v (pairOffset B h i j • pairNormal B i j+(y:E)+z • pairNormal B i j) j)
          (pairOffset B h i j) θ ‖B i-B j‖ ∂stdGaussian _ := by
  have hh := integral_nearCellReward_pair_normal B h i j hij v θ hθ hv
  simp only [facetChart] at hh
  rw [tangentSpace_pairNormal B i j hij] at hh
  simpa only [add_comm] using hh

end NegativeVotingSwitchingCell
