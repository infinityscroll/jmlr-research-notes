import GaussianFanMassJacobian

/-!
Joint differentiation of the actual Gaussian expected maximum.  The score
and offset parameters are differentiated inside the Gaussian integral using
an integrable Lipschitz bound and the proved Gaussian tie-nullness theorem.
No moving-boundary or Hessian formula is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators Topology

namespace NegativeVotingFanScore
open NegativeVotingFan
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

abbrev Parameters (d : ℕ) (ι : Type*) := (ι → FSC.Coord d) × (ι → ℝ)

def centroid (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) : FSC.Coord d :=
  ∫ x, weights B h x i • x ∂stdGaussian (FSC.Coord d)

theorem centroid_integrable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Integrable (fun x => weights B h x i • x) (stdGaussian (FSC.Coord d)) := by
  apply IsGaussian.integrable_id.bdd_smul 1 (weights_measurable B h i).aestronglyMeasurable
  filter_upwards with x
  have hp := weights_simplex B h x
  have hi : weights B h x i ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hp.1 i)] using hi

/-- Evaluation of a parameter increment against one actual affine score. -/
def scoreLinear (x : FSC.Coord d) (i : ι) : Parameters d ι →L[ℝ] ℝ :=
  (innerSL ℝ x).comp ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (ι → FSC.Coord d) (ι → ℝ))) +
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (ι → FSC.Coord d) (ι → ℝ))

theorem scoreLinear_apply (x : FSC.Coord d) (i : ι) (p : Parameters d ι) :
    scoreLinear x i p = inner ℝ (p.1 i) x + p.2 i := by
  change inner ℝ x (p.1 i) + p.2 i = _
  rw [real_inner_comm x (p.1 i)]

def jointDerivative (B : ι → FSC.Coord d) (h : ι → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∫ x, ∑ i, weights B h x i • scoreLinear x i ∂stdGaussian (FSC.Coord d)

theorem scoreLinear_continuous (i : ι) :
    Continuous (fun x : FSC.Coord d => scoreLinear x i) := by
  unfold scoreLinear
  fun_prop

theorem score_parameter_bound (p q : Parameters d ι) (x : FSC.Coord d) :
    ‖scores p.1 p.2 x - scores q.1 q.2 x‖ ≤ (‖x‖ + 1) * ‖p - q‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  change |inner ℝ (p.1 i) x + p.2 i - (inner ℝ (q.1 i) x + q.2 i)| ≤ _
  have he : inner ℝ (p.1 i) x + p.2 i - (inner ℝ (q.1 i) x + q.2 i) =
      inner ℝ ((p.1 - q.1) i) x + (p.2 - q.2) i := by
    simp only [Pi.sub_apply, inner_sub_left]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ ((p.1 - q.1) i) x| + |(p.2 - q.2) i| := abs_add_le _ _
    _ ≤ ‖p.1 - q.1‖ * ‖x‖ + ‖p.2 - q.2‖ := by
      exact add_le_add ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ i) (norm_nonneg _)))
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (p.2 - q.2) i)
    _ ≤ ‖p - q‖ * ‖x‖ + ‖p - q‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_right (by simpa using norm_fst_le (p-q)) (norm_nonneg _))
        (by simpa using norm_snd_le (p-q))
    _ = _ := by ring

theorem max_score_joint_bound (p q : Parameters d ι) (x : FSC.Coord d) :
    ‖NegativeVoting.maxScore (scores p.1 p.2 x) -
      NegativeVoting.maxScore (scores q.1 q.2 x)‖ ≤ (‖x‖ + 1) * ‖p - q‖ :=
  (maxScore_sub_bound _ _).trans (score_parameter_bound p q x)

theorem hasFDerivAt_max_score_joint (p : Parameters d ι) (x : FSC.Coord d)
    (hp : Function.Injective (scores p.1 p.2 x)) :
    HasFDerivAt (fun q : Parameters d ι => NegativeVoting.maxScore (scores q.1 q.2 x))
      (∑ i, weights p.1 p.2 x i • scoreLinear x i) p := by
  classical
  let a := NegativeVoting.chosenWinner (scores p.1 p.2 x)
  have ha (i : ι) (hi : i ≠ a) : scores p.1 p.2 x i < scores p.1 p.2 x a :=
    lt_of_le_of_ne (NegativeVoting.chosenWinner_max _ i) (fun he => hi (hp he))
  have hall : ∀ᶠ q : Parameters d ι in 𝓝 p,
      ∀ i, scores q.1 q.2 x i ≤ scores q.1 q.2 x a := by
    apply eventually_all.mpr
    intro i
    by_cases hi : i = a
    · subst i
      exact Eventually.of_forall fun _ => le_rfl
    have hc : ContinuousAt (fun q : Parameters d ι => scores q.1 q.2 x i) p := by
      unfold scores
      fun_prop
    have hd : ContinuousAt (fun q : Parameters d ι => scores q.1 q.2 x a) p := by
      unfold scores
      fun_prop
    exact (hc.eventually_lt hd (ha i hi)).mono fun _ hh => hh.le
  have heq : (fun q : Parameters d ι => NegativeVoting.maxScore (scores q.1 q.2 x))
      =ᶠ[𝓝 p] (fun q => scoreLinear x a q) := by
    filter_upwards [hall] with q hq
    rw [scoreLinear_apply]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => hq i)
    · exact Finset.le_sup' (f := scores q.1 q.2 x) (Finset.mem_univ a)
  have hw := NegativeVoting.maxWeights_eq_indicator_of_strict_max (scores p.1 p.2 x) a ha
  have he : (∑ i, weights p.1 p.2 x i • scoreLinear x i) = scoreLinear x a := by
    simp only [weights, hw]
    simp
  rw [he]
  exact (scoreLinear x a).hasFDerivAt.congr_of_eventuallyEq heq

/-- The full Fréchet derivative in all rows and offsets, for distinct rows. -/
theorem hasFDerivAt_expectedMax_joint (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) :
    HasFDerivAt (fun p : Parameters d ι => expectedMax p.1 p.2)
      (jointDerivative B h) (B, h) := by
  classical
  let F : Parameters d ι → FSC.Coord d → ℝ :=
    fun p x => NegativeVoting.maxScore (scores p.1 p.2 x)
  let D : FSC.Coord d → Parameters d ι →L[ℝ] ℝ :=
    fun x => ∑ i, weights B h x i • scoreLinear x i
  have hm : AEStronglyMeasurable D (stdGaussian (FSC.Coord d)) := by
    apply Measurable.aestronglyMeasurable
    exact Finset.measurable_sum Finset.univ fun i _ =>
      (weights_measurable B h i).smul (scoreLinear_continuous i).measurable
  have hd : ∀ᵐ x ∂stdGaussian (FSC.Coord d), HasFDerivAt (fun p => F p x) (D x) (B, h) := by
    filter_upwards [ae_scores_injective B hB h] with x hx
    exact hasFDerivAt_max_score_joint (B, h) x hx
  have hb : Integrable (fun x : FSC.Coord d => ‖x‖ + 1) (stdGaussian (FSC.Coord d)) :=
    IsGaussian.integrable_id.norm.add (integrable_const _)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := stdGaussian (FSC.Coord d)) (F := F) (F' := D) (bound := fun x => ‖x‖ + 1)
    (s := Set.univ) (x₀ := (B,h)) (by simp)
    (fun p _ => (max_integrable p.1 p.2).aestronglyMeasurable)
    (max_integrable B h) hm
    (Eventually.of_forall fun x p _ => max_score_joint_bound p (B,h) x) hb hd).2



theorem scoreLinear_norm_le (x : FSC.Coord d) (i : ι) :
    ‖scoreLinear x i‖ ≤ ‖x‖ + 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  have hc := norm_le_pi_norm (scores p.1 p.2 x - scores (0 : ι → FSC.Coord d) 0 x) i
  have hb := score_parameter_bound p (0 : Parameters d ι) x
  rw [sub_zero] at hb
  simpa [scores, scoreLinear_apply] using hc.trans hb

theorem scoreLinear_integrable (i : ι) :
    Integrable (fun x : FSC.Coord d => scoreLinear x i) (stdGaussian (FSC.Coord d)) := by
  exact (IsGaussian.integrable_id.norm.add (integrable_const (1 : ℝ))).mono'
    (scoreLinear_continuous i).aestronglyMeasurable
    (Eventually.of_forall fun x => scoreLinear_norm_le x i)

theorem weighted_scoreLinear_integrable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Integrable (fun x => weights B h x i • scoreLinear x i) (stdGaussian (FSC.Coord d)) := by
  apply (scoreLinear_integrable i).bdd_smul 1 (weights_measurable B h i).aestronglyMeasurable
  filter_upwards with x
  have hp := weights_simplex B h x
  have hi : weights B h x i ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hp.1 i)] using hi

theorem jointDerivative_apply (B D : ι → FSC.Coord d) (h v : ι → ℝ) :
    jointDerivative B h (D,v) =
      ∑ i, (inner ℝ (D i) (centroid B h i) + mass B h i * v i) := by
  classical
  have hi := fun i (_ : i ∈ Finset.univ) => weighted_scoreLinear_integrable B h i
  unfold jointDerivative
  rw [integral_finsetSum Finset.univ hi]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.integral_apply (hi i (Finset.mem_univ i))]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, scoreLinear_apply, mul_add]
  have hinner : Integrable (fun x => weights B h x i * inner ℝ (D i) x)
      (stdGaussian (FSC.Coord d)) := by
    simpa only [real_inner_smul_right] using (centroid_integrable B h i).const_inner (𝕜 := ℝ) (D i)
  rw [integral_add hinner ((weights_integrable B h i).mul_const (v i)), integral_mul_const]
  congr 1
  simpa only [real_inner_smul_right, centroid] using
    integral_inner (𝕜 := ℝ) (centroid_integrable B h i) (D i)

/-- Actual simultaneous row/offset directional derivative, written using
Gaussian cell centroids and masses rather than an uninterpreted derivative. -/
theorem hasDerivAt_expectedMax_joint_line (B D : ι → FSC.Coord d)
    (hB : Function.Injective B) (h v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => expectedMax (B + t • D) (h + t • v))
      (∑ i, (inner ℝ (D i) (centroid B h i) + mass B h i * v i)) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (B,h) + t • (D,v)) (D,v) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (D,v)).const_add (B,h)
  have hg : HasFDerivAt (fun p : Parameters d ι => expectedMax p.1 p.2)
      (jointDerivative B h) ((B,h) + (0:ℝ) • (D,v)) := by
    simpa using hasFDerivAt_expectedMax_joint B hB h
  have hh := hg.comp_hasDerivAt 0 hp
  change HasDerivAt (fun t : ℝ => expectedMax (B + t • D) (h + t • v))
    (jointDerivative B h (D,v)) 0 at hh
  exact hh.congr_deriv (jointDerivative_apply B D h v)

end NegativeVotingFanScore
