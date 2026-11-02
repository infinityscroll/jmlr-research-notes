import GaussianFanMassBase

/-! The actual Gaussian fan masses are the derivatives of its convex dual.
Distinct sites imply tie-nullness for every fixed offset vector. Differentiation
uses a global Lipschitz bound, not a common neighborhood of unique winners. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace BigOperators Topology

namespace NegativeVotingFan
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

theorem weights_measurable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Measurable (fun x => weights B h x i) := by
  apply NegativeVoting.measurable_maxWeights
  intro j
  unfold scores
  fun_prop

theorem weights_simplex (B : ι → FSC.Coord d) (h : ι → ℝ) (x : FSC.Coord d) :
    NegativeVoting.SimplexWeights (weights B h x) :=
  NegativeVoting.maxWeights_simplex _

theorem weights_integrable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Integrable (fun x => weights B h x i) (stdGaussian (FSC.Coord d)) := by
  classical
  have he := NegativeVoting.integrable_weighted_score (stdGaussian (FSC.Coord d))
    (weights B h) (fun _ _ => (1 : ℝ)) i
    (Eventually.of_forall (weights_simplex B h))
    (weights_measurable B h i).aemeasurable (integrable_const _)
  simpa using he

theorem mass_sum (B : ι → FSC.Coord d) (h : ι → ℝ) : ∑ i, mass B h i = 1 := by
  classical
  unfold mass
  rw [← integral_finsetSum Finset.univ (fun i _ => weights_integrable B h i)]
  have he : (fun x => ∑ i, weights B h x i) = fun _ : FSC.Coord d => (1 : ℝ) :=
    funext (fun x => (weights_simplex B h x).2)
  rw [he]
  simp

theorem ae_scores_injective (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), Function.Injective (scores B h x) := by
  classical
  change ∀ᵐ x ∂stdGaussian (FSC.Coord d), ∀ i j, scores B h x i = scores B h x j → i = j
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Eventually.of_forall (fun _ _ => hij)
  have hn : B i - B j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hB he))
  filter_upwards [FSC.ae_inner_ne (B i - B j) hn (h j - h i)] with x hx
  intro he
  exfalso
  apply hx
  rw [inner_sub_left]
  unfold scores at he
  linarith

theorem hasDerivAt_maxScore_direction (s v : ι → ℝ) (hs : Function.Injective s) :
    HasDerivAt (fun t : ℝ => NegativeVoting.maxScore (fun i => s i + t * v i))
      (∑ i, NegativeVoting.maxWeights s i * v i) 0 := by
  classical
  let a := NegativeVoting.chosenWinner s
  have ha (i : ι) (hi : i ≠ a) : s i < s a := by
    have hl := NegativeVoting.chosenWinner_max s i
    exact lt_of_le_of_ne hl (fun he => hi (hs he))
  have heach (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, s i + t * v i ≤ s a + t * v a := by
    by_cases hi : i = a
    · subst i
      exact Eventually.of_forall (fun _ => le_rfl)
    have hc : ContinuousAt (fun t : ℝ => s i + t * v i) 0 := by fun_prop
    have hd : ContinuousAt (fun t : ℝ => s a + t * v a) 0 := by fun_prop
    exact (hc.eventually_lt hd (by simpa using ha i hi)).mono (fun _ hh => le_of_lt hh)
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, s i + t * v i ≤ s a + t * v a :=
    eventually_all.mpr heach
  have heq : (fun t : ℝ => NegativeVoting.maxScore (fun i => s i + t * v i)) =ᶠ[𝓝 0]
      (fun t : ℝ => s a + t * v a) := by
    filter_upwards [hall] with t ht
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => ht i)
    · exact Finset.le_sup' (f := fun i => s i + t * v i) (Finset.mem_univ a)
  have hd : HasDerivAt (fun t : ℝ => s a + t * v a) (v a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v a)).const_add (s a)
  have hw := NegativeVoting.maxWeights_eq_indicator_of_strict_max s a ha
  have hsum : (∑ i, NegativeVoting.maxWeights s i * v i) = v a := by
    simp_rw [hw]
    simp
  rw [hsum]
  exact hd.congr_of_eventuallyEq heq

theorem max_score_line_lipschitz (B : ι → FSC.Coord d) (h v : ι → ℝ)
    (x : FSC.Coord d) :
    LipschitzWith ‖v‖₊ (fun t : ℝ =>
      NegativeVoting.maxScore (scores B (fun i => h i + t * v i) x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro t q
  have he : (fun i => h i + t * v i) - (fun i => h i + q * v i) = (t - q) • v := by
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb := max_score_offset_bound B (fun i => h i + t * v i)
    (fun i => h i + q * v i) x
  rw [he, norm_smul] at hb
  simpa only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, mul_comm] using hb

theorem hasDerivAt_expectedMax (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => expectedMax B (fun i => h i + t * v i))
      (∑ i, mass B h i * v i) 0 := by
  classical
  let F : ℝ → FSC.Coord d → ℝ := fun t x =>
    NegativeVoting.maxScore (scores B (fun i => h i + t * v i) x)
  let D : FSC.Coord d → ℝ := fun x => ∑ i, weights B h x i * v i
  have hm : AEStronglyMeasurable D (stdGaussian (FSC.Coord d)) :=
    (Finset.measurable_sum Finset.univ (fun i _ =>
      (weights_measurable B h i).mul_const (v i))).aestronglyMeasurable
  have hd : ∀ᵐ x ∂stdGaussian (FSC.Coord d), HasDerivAt (fun t => F t x) (D x) 0 := by
    filter_upwards [ae_scores_injective B hB h] with x hx
    have he : (fun t => F t x) =
        (fun t : ℝ => NegativeVoting.maxScore (fun i => scores B h x i + t * v i)) := by
      funext t
      dsimp only [F]
      congr 1
      funext i
      dsimp [F, scores]
      ring
    rw [he]
    exact hasDerivAt_maxScore_direction (scores B h x) v hx
  have hf0 : Integrable (F 0) (stdGaussian (FSC.Coord d)) := by
    simpa [F] using max_integrable B h
  have hl : ∀ᵐ x ∂stdGaussian (FSC.Coord d),
      LipschitzOnWith (Real.nnabs ‖v‖) (fun t => F t x) Set.univ := by
    filter_upwards with x
    have hn : Real.nnabs ‖v‖ = ‖v‖₊ := by
      apply NNReal.coe_injective
      simp
    rw [hn]
    exact (max_score_line_lipschitz B h v x).lipschitzOnWith
  have hdiff := (hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := stdGaussian (FSC.Coord d)) (F := F) (F' := D) (bound := fun _ => ‖v‖)
    (s := Set.univ) (x₀ := (0 : ℝ)) (by simp)
    (Eventually.of_forall (fun t => (max_integrable B _).aestronglyMeasurable))
    hf0 hm hl (integrable_const _) hd).2
  have hDi : (∫ x, D x ∂stdGaussian (FSC.Coord d)) = ∑ i, mass B h i * v i := by
    unfold D
    rw [integral_finsetSum Finset.univ (fun i _ => (weights_integrable B h i).mul_const (v i))]
    simp only [integral_mul_const, mass]
  rw [hDi] at hdiff
  exact hdiff

theorem hasDerivAt_potential (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (p h v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => potential B p (fun i => h i + t * v i))
      (∑ i, (mass B h i - p i) * v i) 0 := by
  have hi (i : ι) : HasDerivAt (fun t : ℝ => p i * (h i + t * v i)) (p i * v i) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (h i)).const_mul (p i)
  have hl := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have hd := (hasDerivAt_expectedMax B hB h v).sub hl
  have he : (∑ i, mass B h i * v i) - (∑ i, p i * v i) =
      ∑ i, (mass B h i - p i) * v i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact hd.congr_deriv he

end NegativeVotingFan
