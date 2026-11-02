import GaussianSoftPolyhedron

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace
open OAI.GaussianPropeller.Quantile OAI.GaussianPropeller.HeatConvolution
  OAI.GaussianPropeller.EhrhardSmooth

namespace NegativeVotingEhrhard

section Approximation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {J : Type*} [Fintype J]

/-- The genuine closed intersection of finitely many affine halfspaces. -/
def closedPolyhedron (w : J → E) (b : J → ℝ) : Set E :=
  {x | ∀ j, inner ℝ (w j) x ≤ b j}

/-- The smooth approximation grows to +infinity on the entire closed polyhedron,
including its boundary, and to -infinity outside it. -/
def polyApprox (w : J → E) (b : J → ℝ) (n : ℕ) (x : E) : ℝ :=
  softPolyhedron (n : ℝ) ((n : ℝ) ^ 2) w b x

theorem softPolyhedron_inside_lower (a R : ℝ) (hR : 0 ≤ R)
    (w : J → E) (b : J → ℝ) (x : E) (hx : x ∈ closedPolyhedron w b) :
    a - (Fintype.card J : ℝ) * Real.log 2 ≤ softPolyhedron a R w b x := by
  have hs : (∑ j, softplus (penaltyArgument R (w j) (b j) x)) ≤
      (Fintype.card J : ℝ) * Real.log 2 := by
    calc
      _ ≤ ∑ _j : J, Real.log 2 := Finset.sum_le_sum (fun j _ =>
        softplus_le_log_two_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hR (sub_nonpos.mpr (hx j))))
      _ = _ := by simp
  dsimp only [softPolyhedron]
  linarith

theorem softPolyhedron_le_single_violation (a R : ℝ) (w : J → E) (b : J → ℝ)
    (x : E) (j : J) :
    softPolyhedron a R w b x ≤ a - R * (inner ℝ (w j) x - b j) := by
  have hs : softplus (penaltyArgument R (w j) (b j) x) ≤
      ∑ i, softplus (penaltyArgument R (w i) (b i) x) :=
    Finset.single_le_sum (fun i _ => softplus_nonneg (penaltyArgument R (w i) (b i) x)) (Finset.mem_univ j)
  have hp := self_le_softplus (penaltyArgument R (w j) (b j) x)
  dsimp only [softPolyhedron, penaltyArgument] at *
  linarith

theorem polyApprox_tendsto_atTop_inside (w : J → E) (b : J → ℝ) (x : E)
    (hx : x ∈ closedPolyhedron w b) :
    Tendsto (fun n : ℕ => polyApprox w b n x) atTop atTop := by
  apply tendsto_atTop_mono
    (fun n : ℕ => softPolyhedron_inside_lower (n : ℝ) ((n : ℝ)^2) (sq_nonneg _) w b x hx)
  apply tendsto_atTop.2
  intro B
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop
    (B + (Fintype.card J : ℝ) * Real.log 2)] with n hn
  linarith

theorem polyApprox_tendsto_atBot_outside (w : J → E) (b : J → ℝ) (x : E)
    (hx : x ∉ closedPolyhedron w b) :
    Tendsto (fun n : ℕ => polyApprox w b n x) atTop atBot := by
  obtain ⟨j, hj⟩ := not_forall.mp hx
  have hd : 0 < inner ℝ (w j) x - b j := sub_pos.mpr (lt_of_not_ge hj)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 / (inner ℝ (w j) x - b j) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hbound : ∀ᶠ n : ℕ in atTop, polyApprox w b n x ≤ -(n : ℝ) := by
    filter_upwards [hlarge] with n hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnδ : 2 ≤ (n : ℝ) * (inner ℝ (w j) x - b j) := (div_le_iff₀ hd).mp hn
    have hs := softPolyhedron_le_single_violation (n : ℝ) ((n : ℝ)^2) w b x j
    change polyApprox w b n x ≤ (n : ℝ) - (n : ℝ)^2 * (inner ℝ (w j) x - b j) at hs
    have hp := mul_le_mul_of_nonneg_left hnδ hn0
    nlinarith
  exact tendsto_atBot_mono' atTop hbound
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

/-- Pointwise convergence at every point, including degenerate or coincident
facets. No Gaussian boundary-nullness hypothesis is needed. -/
theorem polyApprox_cdf_tendsto_indicator (w : J → E) (b : J → ℝ) (x : E) :
    Tendsto (fun n : ℕ => Φ (polyApprox w b n x)) atTop
      (𝓝 ((closedPolyhedron w b).indicator (1 : E → ℝ) x)) := by
  by_cases hx : x ∈ closedPolyhedron w b
  · rw [Set.indicator_of_mem hx]
    exact tendsto_Φ_atTop.comp (polyApprox_tendsto_atTop_inside w b x hx)
  · rw [Set.indicator_of_notMem hx]
    exact tendsto_Φ_atBot.comp (polyApprox_tendsto_atBot_outside w b x hx)

end Approximation

section Gaussian
variable {ι J : Type*} [Fintype ι] [Fintype J]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

/-- Actual translated Gaussian mass γ(C-x), written as its indicator integral. -/
def translatedPolyhedronMass (w : J → E) (b : J → ℝ) (x : E) : ℝ :=
  ∫ z, (closedPolyhedron w b).indicator (1 : E → ℝ) (x + z) ∂γ

theorem measurableSet_closedPolyhedron (w : J → E) (b : J → ℝ) :
    MeasurableSet (closedPolyhedron w b) := by
  change MeasurableSet {x | ∀ j, inner ℝ (w j) x ≤ b j}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop) measurable_const

/-- The definition is exactly the Gaussian probability of the translated finite
intersection of inequalities, expressed in real rather than ENNReal form. -/
theorem translatedPolyhedronMass_eq_measure (w : J → E) (b : J → ℝ) (x : E) :
    translatedPolyhedronMass w b x =
      (γ {z | ∀ j, inner ℝ (w j) z ≤ b j - inner ℝ (w j) x}).toReal := by
  have hs : MeasurableSet {z : E | ∀ j, inner ℝ (w j) z ≤ b j - inner ℝ (w j) x} :=
    measurableSet_closedPolyhedron w (fun j => b j - inner ℝ (w j) x)
  have heq : (fun z : E => (closedPolyhedron w b).indicator (1 : E → ℝ) (x + z)) =
      {z : E | ∀ j, inner ℝ (w j) z ≤ b j - inner ℝ (w j) x}.indicator (1 : E → ℝ) := by
    funext z
    have hm : x + z ∈ closedPolyhedron w b ↔
        z ∈ {z : E | ∀ j, inner ℝ (w j) z ≤ b j - inner ℝ (w j) x} := by
      simp only [closedPolyhedron, mem_ofPred_eq, inner_add_right]
      constructor <;> intro h j <;> linarith [h j]
    by_cases hz : x + z ∈ closedPolyhedron w b
    · simp [hz, hm.mp hz]
    · simp [hz, mt hm.mpr hz]
  unfold translatedPolyhedronMass
  rw [heq, integral_indicator_one hs]
  rfl

/-- Dominated convergence of the actual Gaussian heat integrals. -/
theorem polyApprox_heat_tendsto_mass (w : J → E) (b : J → ℝ) (x : E) :
    Tendsto (fun n : ℕ => heat (fun y => Φ (polyApprox w b n y)) 1 x) atTop
      (𝓝 (translatedPolyhedronMass w b x)) := by
  have hc (n : ℕ) : Continuous (polyApprox w b n) :=
    continuous_iff_continuousAt.mpr
      (fun y => (softPolyhedron_fderiv (n : ℝ) ((n : ℝ)^2) w b y).continuousAt)
  have hh := tendsto_integral_of_dominated_convergence (μ := γ) (bound := fun _ : E => (1 : ℝ))
    (F := fun n z => Φ (polyApprox w b n (x + z)))
    (f := fun z => (closedPolyhedron w b).indicator (1 : E → ℝ) (x + z))
    (fun n => ((continuous_Φ.comp (hc n)).comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => ae_of_all _ (fun z => OAI.GaussianPropeller.SmoothCDF.cdf_bound (polyApprox w b n) (x+z)))
    (ae_of_all _ (fun z => polyApprox_cdf_tendsto_indicator w b (x+z)))
  simpa only [heat, Real.sqrt_one, one_smul, translatedPolyhedronMass] using hh

/-- Quantile continuity is used only at a nondegenerate actual mass. -/
theorem polyApprox_qheat_tendsto_quantile (w : J → E) (b : J → ℝ) (x : E)
    (hm : translatedPolyhedronMass w b x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => qheat (polyApprox w b n) 1 x) atTop
      (𝓝 (q (translatedPolyhedronMass w b x))) := by
  exact (continuousAt_q hm).tendsto.comp (polyApprox_heat_tendsto_mass w b x)

/-- Ehrhard concavity of the actual translated Gaussian polyhedron mass.
The only nondegeneracy condition is that the actual masses lie in (0,1), where
the Gaussian inverse CDF is finite. Concavity itself is derived by approximation. -/
theorem quantile_translatedPolyhedronMass_concave (w : J → E) (b : J → ℝ)
    (hm : ∀ x, translatedPolyhedronMass w b x ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ univ (fun x => q (translatedPolyhedronMass w b x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b' ha hb hab
  have hleft := ((polyApprox_qheat_tendsto_quantile w b x (hm x)).const_mul a).add
    ((polyApprox_qheat_tendsto_quantile w b y (hm y)).const_mul b')
  have hright := polyApprox_qheat_tendsto_quantile w b (a • x + b' • y) (hm _)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards with n
  exact (qheat_softPolyhedron_concave (n : ℝ) ((n : ℝ)^2) (sq_nonneg _) w b 1
    (by norm_num)).2 hx hy ha hb hab

/-- Translation changes the actual standard Gaussian by an everywhere positive
density, so every positive-measure set remains positive under translation. -/
theorem gaussian_translate_mass_pos (v : E) (S : Set E) (hp : 0 < (γ S).toReal) :
    0 < (((γ).map (fun z => z + v)) S).toReal := by
  have hac : γ ≪ (γ).map (fun z => z + v) := by
    rw [OAI.GaussianPropeller.Translation.stdGaussian_map_add]
    apply withDensity_absolutelyContinuous' (by fun_prop)
    exact ae_of_all _ (fun x => by positivity)
  have h0 : γ S ≠ 0 := (ENNReal.toReal_pos_iff.mp hp).1.ne'
  apply ENNReal.toReal_pos
  · intro h
    exact h0 (hac h)
  · exact measure_ne_top _ _

theorem translatedPolyhedronMass_eq_map (w : J → E) (b : J → ℝ) (x : E) :
    translatedPolyhedronMass w b x =
      (((γ).map (fun z => z + x)) (closedPolyhedron w b)).toReal := by
  rw [translatedPolyhedronMass_eq_measure,
    Measure.map_apply (by fun_prop) (measurableSet_closedPolyhedron w b)]
  apply congrArg (fun S : Set E => (γ S).toReal)
  ext z
  simp only [closedPolyhedron, mem_ofPred_eq, mem_preimage, inner_add_right]
  constructor <;> intro h j <;> linarith [h j]

/-- It suffices to check the original polyhedron's mass once: all translated
masses are then strictly between zero and one. -/
theorem translatedPolyhedronMass_mem (w : J → E) (b : J → ℝ)
    (hp : (γ (closedPolyhedron w b)).toReal ∈ Ioo (0 : ℝ) 1) (x : E) :
    translatedPolyhedronMass w b x ∈ Ioo (0 : ℝ) 1 := by
  have hs := measurableSet_closedPolyhedron w b
  have hcomp : 0 < (γ (closedPolyhedron w b)ᶜ).toReal := by
    change 0 < (γ).real (closedPolyhedron w b)ᶜ
    rw [measureReal_compl hs, probReal_univ]
    exact sub_pos.mpr hp.2
  have hpos := gaussian_translate_mass_pos x (closedPolyhedron w b) hp.1
  have hposcomp := gaussian_translate_mass_pos x (closedPolyhedron w b)ᶜ hcomp
  have hsum := measureReal_add_measureReal_compl (μ := (γ).map (fun z => z+x)) hs
  rw [probReal_univ] at hsum
  rw [translatedPolyhedronMass_eq_map]
  constructor
  · exact hpos
  · change _ < (1 : ℝ)
    change (((γ).map (fun z => z+x)) (closedPolyhedron w b)).toReal +
      (((γ).map (fun z => z+x)) (closedPolyhedron w b)ᶜ).toReal = 1 at hsum
    linarith

/-- Actual Ehrhard concavity for every nontrivial finite Gaussian polyhedron.
No smoothness, bounded-gradient, approximation, or translated-mass hypothesis
remains: all are derived from the finite halfspace description and 0<γ(C)<1. -/
theorem gaussian_polyhedron_ehrhard_concave (w : J → E) (b : J → ℝ)
    (hp : (γ (closedPolyhedron w b)).toReal ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ univ (fun x => q (translatedPolyhedronMass w b x)) :=
  quantile_translatedPolyhedronMass_concave w b (translatedPolyhedronMass_mem w b hp)

end Gaussian
end NegativeVotingEhrhard
