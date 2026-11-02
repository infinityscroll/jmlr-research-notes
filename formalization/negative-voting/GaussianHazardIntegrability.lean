import GaussianHazardPolynomialBounds

/-! Finite polynomial moments of the actual threshold hazard densities.
These justify finite-parameter Gaussian integrability, not the quantitative
rare-event estimates uniform in the number of labels. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical NNReal ENNReal
namespace NegativeVotingHazardIntegrability
open WeakSimplex NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardPolynomialBounds

def varianceOfStd (σ : ℝ) : ℝ≥0 := ⟨σ^2,sq_nonneg σ⟩

lemma density_eq_gaussianPDFReal (σ h x : ℝ) (hσ : 0 < σ) :
    gaussianDensity σ h x=gaussianPDFReal h (varianceOfStd σ) x := by
  have hv : (varianceOfStd σ:ℝ)=σ^2 := rfl
  unfold gaussianDensity normalPDF gaussianPDFReal
  rw [hv]
  simp only [NNReal.coe_one,mul_one,sub_zero]
  rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*Real.pi),Real.sqrt_sq hσ.le]
  field_simp

lemma integrable_density_polynomial (σ h C : ℝ) (hσ : 0 < σ) (hC : 0 ≤ C) (k : ℕ) :
    Integrable (fun x:ℝ=>gaussianDensity σ h x*(C+|x|)^k) volume := by
  have hv : varianceOfStd σ ≠ 0 := by
    intro hz
    have hh := congrArg (fun z:ℝ≥0=>(z:ℝ)) hz
    change σ^2=0 at hh
    exact hσ.ne' (sq_eq_zero_iff.mp hh)
  have hm : MemLp (fun x:ℝ=>C+|x|) (k:ℝ≥0∞) (gaussianReal h (varianceOfStd σ)) := by
    have hm0 := (memLp_id_gaussianReal' (μ:=h) (v:=varianceOfStd σ) k (by simp)).norm
    simp only [id_eq,Real.norm_eq_abs] at hm0
    convert (memLp_const C).add hm0 using 1
  have hi : Integrable (fun x:ℝ=>(C+|x|)^k) (gaussianReal h (varianceOfStd σ)) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (add_nonneg hC (abs_nonneg _))] using hm.integrable_norm_pow'
  rw [gaussianReal_of_var_ne_zero h hv,
    integrable_withDensity_iff (measurable_gaussianPDF h (varianceOfStd σ))
      (ae_of_all _ fun _=>gaussianPDF_lt_top)] at hi
  simpa only [density_eq_gaussianPDFReal σ h _ hσ,gaussianPDF,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),mul_comm] using hi

lemma continuous_gaussianCDF (σ h : ℝ) : Continuous (gaussianCDF σ h) := by
  have hc : Continuous normalCDF := continuous_iff_continuousAt.mpr fun x=>(hasDerivAt_normalCDF x).continuousAt
  exact hc.comp (by fun_prop)

lemma continuous_gaussianDensity (σ h : ℝ) : Continuous (gaussianDensity σ h) := by
  have hc : Continuous normalPDF := continuous_iff_continuousAt.mpr fun x=>(hasDerivAt_normalPDF x).continuousAt
  exact (hc.comp (by fun_prop)).div_const σ

lemma continuous_gaussianHazard (σ h : ℝ) : Continuous (gaussianHazard σ h) :=
  (continuous_gaussianDensity σ h).div (continuous_gaussianCDF σ h) fun x=>(gaussianCDF_pos _ _ _).ne'

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma continuous_hazardPairDensity (σ h : V → ℝ) (i j : V) :
    Continuous (fun x=>hazardPairDensity σ h x i j) := by
  exact ((continuous_finset_prod _ (fun k _=>continuous_gaussianCDF (σ k) (h k))).mul
    (continuous_gaussianHazard (σ i) (h i))).mul (continuous_gaussianHazard (σ j) (h j))

/-- All finite moments of an actual pair density, including the analytic
 diagonal, are integrable under only positive standard deviations. -/
theorem integrable_hazardPairDensity_polynomial (σ h : V → ℝ) (hσ : ∀ i,0 < σ i)
    (i j : V) (k : ℕ) :
    Integrable (fun x:ℝ=>hazardPairDensity σ h x i j*(1+|x|)^k) volume := by
  let C : ℝ := r 0/σ j+(1+|h j|)/(σ j)^2
  have hC : 0 ≤ C := by dsimp [C];positivity [r_pos 0,hσ j]
  have hbound (x:ℝ) : gaussianHazard (σ j) (h j) x ≤ C*(1+|x|) := by
    refine (gaussianHazard_linear_growth (σ j) (h j) x (hσ j)).trans ?_
    have h1 : 0 ≤ r 0/σ j := div_nonneg (r_pos 0).le (hσ j).le
    have h2 : 0 ≤ |h j|/(σ j)^2 := div_nonneg (abs_nonneg _) (sq_nonneg _)
    dsimp [C]
    have h3 := mul_nonneg h1 (abs_nonneg x)
    have h4 := mul_nonneg h2 (abs_nonneg x)
    have h5 : 0 ≤ 1/(σ j)^2 := by positivity
    apply sub_nonneg.mp
    convert add_nonneg (add_nonneg h3 h4) h5 using 1 <;> ring
  have hi := (integrable_density_polynomial (σ i) (h i) 1 (hσ i) (by norm_num) (k+1)).const_mul C
  apply hi.mono'
    (((continuous_hazardPairDensity σ h i j).mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards with x
  change ‖hazardPairDensity σ h x i j*(1+|x|)^k‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hazardPairDensity_nonneg σ h hσ x i j) (by positivity))]
  calc
    _ ≤ (gaussianDensity (σ i) (h i) x*gaussianHazard (σ j) (h j) x)*(1+|x|)^k :=
      mul_le_mul_of_nonneg_right (hazardPairDensity_le_density_hazard σ h hσ x i j) (by positivity)
    _ ≤ (gaussianDensity (σ i) (h i) x*(C*(1+|x|)))*(1+|x|)^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound x)
        (gaussianDensity_pos _ _ _ (hσ i)).le) (by positivity)
    _ = _ := by rw [pow_succ];ring

end NegativeVotingHazardIntegrability
