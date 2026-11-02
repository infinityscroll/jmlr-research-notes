import NegativeVoting.RegularSimplexMoments
import GaussianMassCentroid
import WeakSimplexConjectureLean.Normal.Mills

/-! Actual maxima of independent standard Gaussians: distribution, moments,
and finite tail bounds for competitive mass localization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianMaximum
open NegativeVoting WeakSimplex NegativeVotingMassCentroid
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def maximum (x : ι → ℝ) : ℝ := maxScore x

theorem maximum_measurable : Measurable (maximum : (ι → ℝ) → ℝ) :=
  measurable_finite_max id Finset.univ Finset.univ_nonempty (fun i _ => measurable_pi_apply i)

theorem maximum_integrable : Integrable (maximum : (ι → ℝ) → ℝ) (standardGaussian ι) :=
  integrable_finite_max _ id Finset.univ Finset.univ_nonempty
    (fun i _ => gaussian_product_coordinate_integrable (fun _ => 0) (fun _ => 1) i)

private theorem memLp_finite_max {Ω κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) (s : Ω → κ → ℝ) (p : ℝ≥0∞) (t : Finset κ) (hne : t.Nonempty)
    (hs : ∀ i ∈ t, MemLp (fun x => s x i) p μ) :
    MemLp (fun x => t.sup' hne (s x)) p μ := by
  induction t using Finset.induction_on with
  | empty => simp at hne
  | @insert a t ha ih =>
    by_cases ht : t.Nonempty
    · have hi := ih ht (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      have hai := hs a (Finset.mem_insert_self a t)
      simpa only [Finset.sup'_insert ht,Pi.sup_def] using hai.sup hi
    · have hempty : t=∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      simpa using hs a (Finset.mem_singleton_self a)

theorem maximum_memLp_two : MemLp (maximum : (ι → ℝ) → ℝ) 2 (standardGaussian ι) := by
  apply memLp_finite_max _ id 2 Finset.univ Finset.univ_nonempty
  intro i _
  exact (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : ι => gaussianReal 0 1) i)

theorem maximum_square_integrable :
    Integrable (fun x : ι → ℝ => maximum x ^ 2) (standardGaussian ι) :=
  maximum_memLp_two.integrable_sq

/-- This is the actual product-Gaussian law, not a hypothesized distribution. -/
theorem maximum_cdf (t : ℝ) :
    (standardGaussian ι).real {x | maximum x ≤ t}=normalCDF t ^ Fintype.card ι := by
  have he : {x : ι → ℝ | maximum x ≤ t}=Set.pi Set.univ (fun _ : ι => Set.Iic t) := by
    ext x
    simp [maximum,maxScore,Finset.sup'_le_iff]
    rfl
  rw [he,measureReal_def,standardGaussian,Measure.pi_pi]
  simp only [← normalCDF_eq_measure_Iic,Finset.prod_const,Finset.card_univ,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal (normalCDF_pos t).le]

theorem maximum_survival (t : ℝ) :
    (standardGaussian ι).real {x | t < maximum x}=1-normalCDF t ^ Fintype.card ι := by
  have he : {x : ι → ℝ | t < maximum x}=({x : ι → ℝ | maximum x ≤ t})ᶜ := by
    ext x
    simp
  rw [he,probReal_compl_eq_one_sub (measurableSet_le maximum_measurable measurable_const),maximum_cdf]

/-- Elementary finite Bernoulli bound used for the actual Gaussian union. -/
theorem one_sub_pow_le_mul (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    1-(1-q)^n ≤ (n:ℝ)*q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (1-q)]
    have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hq1)
    have hn : 0 ≤ (n:ℝ)*q^2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg q)
    push_cast
    nlinarith

/-- The two-term finite Bonferroni estimate is proved algebraically. -/
theorem one_sub_pow_ge_two_terms (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (n:ℝ)*q-((n:ℝ)*((n:ℝ)-1)/2)*q^2 ≤ 1-(1-q)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hq1)
    have hc : 0 ≤ (n:ℝ)*((n:ℝ)-1) := by
      cases n with
      | zero => norm_num
      | succ n => norm_num; positivity
    have hn := mul_nonneg hc (pow_nonneg hq 3)
    rw [pow_succ (1-q)]
    push_cast
    nlinarith

/-- Actual maximum survival is bounded above by the first union term and
below by its two-term Bonferroni truncation. -/
theorem maximum_survival_bounds (t : ℝ) :
    (Fintype.card ι:ℝ)*normalCDF (-t)-((Fintype.card ι:ℝ)*normalCDF (-t))^2/2 ≤
      (standardGaussian ι).real {x | t < maximum x} ∧
    (standardGaussian ι).real {x | t < maximum x} ≤
      (Fintype.card ι:ℝ)*normalCDF (-t) := by
  have hc : normalCDF t=1-normalCDF (-t) := by linarith [normalCDF_neg t]
  rw [maximum_survival,hc]
  have hq := (normalCDF_pos (-t)).le
  have hq1 := (normalCDF_lt_one (-t)).le
  constructor
  · have h := one_sub_pow_ge_two_terms (Fintype.card ι) (normalCDF (-t)) hq hq1
    have hn : 0 ≤ (Fintype.card ι:ℝ)*normalCDF (-t)^2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    nlinarith
  · exact one_sub_pow_le_mul _ _ hq hq1

/-- Mean and upper 1/(n+2) threshold for an actual n+2-coordinate Gaussian. -/
def maximumMean (n : ℕ) : ℝ := ∫ x : Fin (n+2) → ℝ, maximum x ∂standardGaussian (Fin (n+2))
def upperQuantile (n : ℕ) : ℝ := -normalQuantile (1/((n:ℝ)+2))

/-- The threshold has exactly the specified actual Gaussian upper-tail mass. -/
theorem upperQuantile_tail (n : ℕ) : normalCDF (-upperQuantile n)=1/((n:ℝ)+2) := by
  have hp : 0 < 1/((n:ℝ)+2) := by positivity
  have hp1 : 1/((n:ℝ)+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  simpa only [upperQuantile,neg_neg] using normalCDF_normalQuantile hp hp1

theorem normalCDF_zero : normalCDF 0=1/2 := by
  have h := normalCDF_neg 0
  simp only [neg_zero] at h
  linarith

theorem upperQuantile_pos {n : ℕ} (hn : 0 < n) : 0 < upperQuantile n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp : 1/((n:ℝ)+2) < 1/2 := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  rw [← upperQuantile_tail n,← normalCDF_zero] at hp
  have hb := strictMono_normalCDF.lt_iff_lt.mp hp
  linarith

/-- Quantile divergence is derived from the actual CDF inverse. -/
theorem upperQuantile_tendsto : Tendsto upperQuantile atTop atTop := by
  have hp : Tendsto (fun n : ℕ => 1/((n:ℝ)+2)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [hp.eventually (gt_mem_nhds (normalCDF_pos (-a)))] with n hn
  rw [← upperQuantile_tail n] at hn
  have hb := strictMono_normalCDF.lt_iff_lt.mp hn
  linarith

def scaledMaximum (n : ℕ) (x : Fin (n+2) → ℝ) : ℝ :=
  upperQuantile n*(maximum x-upperQuantile n)

theorem scaledMaximum_memLp_two (n : ℕ) :
    MemLp (scaledMaximum n) 2 (standardGaussian (Fin (n+2))) :=
  (maximum_memLp_two.sub (memLp_const (upperQuantile n))).const_mul (upperQuantile n)

theorem scaledMaximum_integrable (n : ℕ) :
    Integrable (scaledMaximum n) (standardGaussian (Fin (n+2))) :=
  (maximum_integrable.sub (integrable_const (upperQuantile n))).const_mul (upperQuantile n)

theorem scaledMaximum_mean (n : ℕ) :
    (∫ x, scaledMaximum n x ∂standardGaussian (Fin (n+2)))=
      upperQuantile n*(maximumMean n-upperQuantile n) := by
  unfold scaledMaximum maximumMean
  rw [integral_const_mul,integral_sub maximum_integrable (integrable_const _)]
  simp

end NegativeVotingGaussianMaximum
