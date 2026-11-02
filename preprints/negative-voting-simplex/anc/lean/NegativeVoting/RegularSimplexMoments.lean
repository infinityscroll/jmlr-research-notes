import NegativeVoting.RegularSimplex
import NegativeVoting.NoiseStability
import NegativeVoting.GaussianCentroid

/-!
# Actual Gaussian masses of regular-simplex references

An ambient orthogonal reflection realizes each label transposition. Gaussian
invariance and the exact permutation equivariance of tie weights then prove
balancing of the implemented reference assignment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NegativeVoting
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

theorem maxScore_perm {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (e : Equiv.Perm ι) : maxScore (fun i => s (e i)) = maxScore s := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => Finset.le_sup' s (Finset.mem_univ (e i)))
  · apply Finset.sup'_le
    intro i _
    have h := Finset.le_sup' (fun j => s (e j)) (Finset.mem_univ (e.symm i))
    simpa only [maxScore, Equiv.apply_symm_apply] using h

theorem maxMultiplicity_perm {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (e : Equiv.Perm ι) :
    maxMultiplicity (fun i => s (e i)) = maxMultiplicity s := by
  classical
  simp only [maxMultiplicity, maxIndicator, maxScore_perm]
  exact Equiv.sum_comp e (fun i => if s i = maxScore s then (1 : ℝ) else 0)

theorem maxWeights_perm {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (e : Equiv.Perm ι) (i : ι) :
    maxWeights (fun j => s (e j)) i = maxWeights s (e i) := by
  simp only [maxWeights, maxIndicator, maxScore_perm, maxMultiplicity_perm]

theorem maxWeights_score_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) : (∑ i, maxWeights s i * s i) = maxScore s := by
  classical
  have hterm (i : ι) : maxWeights s i * s i = maxWeights s i * maxScore s := by
    by_cases hi : s i = maxScore s
    · rw [hi]
    · simp [maxWeights, maxIndicator, hi]
  simp_rw [hterm]
  rw [← Finset.sum_mul, (maxWeights_simplex s).2, one_mul]

variable {κ : Type*} [Fintype κ] {m : ℕ} [Nonempty (Fin m)]

theorem regularAssignment_integrable (rows : Fin m → κ → ℝ) (i : Fin m) :
    Integrable (fun x => regularAssignment rows x i) (standardGaussian κ) := by
  apply (integrable_const (1 : ℝ)).mono'
    (regularAssignment_measurable rows i).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg ((regularAssignment_simplex rows x).1 i)]
  exact simplex_weight_le_one _ (regularAssignment_simplex rows x) i

/-- The actual product Gaussian integral agrees with its Euclidean-space
representation, whose orthogonal invariance is available in mathlib. -/
theorem integral_standardGaussian_eq_euclidean (g : (κ → ℝ) → ℝ) :
    (∫ x, g x ∂standardGaussian κ) =
      ∫ x : EuclideanSpace ℝ κ, g x.ofLp ∂stdGaussian (EuclideanSpace ℝ κ) := by
  let e := (PiLp.homeomorph 2 (fun _ : κ => ℝ)).symm.toMeasurableEquiv
  have hp : MeasurePreserving e (standardGaussian κ)
      (stdGaussian (EuclideanSpace ℝ κ)) := by
    constructor
    · exact e.measurable
    · exact map_pi_eq_stdGaussian
  exact hp.integral_comp' (fun x => g x.ofLp)

/-- An ambient orthogonal reflection gives equality of the actual
label-weighted score observables. No exchangeability premise is assumed. -/
theorem regularAssignment_score_observable_eq (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (i j : Fin m) (g : ℝ → ℝ) :
    (∫ x, regularAssignment rows x i * g (∑ k, rows i k * x k) ∂standardGaussian κ) =
      ∫ x, regularAssignment rows x j * g (∑ k, rows j k * x k) ∂standardGaussian κ := by
  classical
  let r (k : Fin m) : EuclideanSpace ℝ κ := WithLp.toLp 2 (rows k)
  have hdot (k : Fin m) (x : EuclideanSpace ℝ κ) :
      inner ℝ (r k) x = ∑ l, rows k l * x l := by
    rw [PiLp.inner_apply]
    simp only [r, Real.inner_apply]
  have hgram (k l : Fin m) :
      inner ℝ (r k) (r l) = (if k = l then 1 else 0) - 1 / (m : ℝ) := by
    rw [hdot]
    exact hrows k l
  have hn : ‖r i‖ = ‖r j‖ := by
    have hi := hgram i i
    have hj := hgram j j
    rw [real_inner_self_eq_norm_sq] at hi hj
    simp only [ite_true] at hi hj
    nlinarith [norm_nonneg (r i), norm_nonneg (r j)]
  let R := (ℝ ∙ (r i - r j))ᗮ.reflection
  have hRi : R (r i) = r j := Submodule.reflection_sub hn
  have hRj : R (r j) = r i := by
    rw [← hRi]
    exact Submodule.reflection_reflection _ _
  have hR (k : Fin m) : R (r k) = r (Equiv.swap i j k) := by
    by_cases hki : k = i
    · subst k
      simpa using hRi
    · by_cases hkj : k = j
      · subst k
        simpa using hRj
      · have hk : r k ∈ (ℝ ∙ (r i - r j))ᗮ := by
          rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right,
            hgram, hgram]
          simp [hki, hkj]
        simpa [Equiv.swap_apply_of_ne_of_ne hki hkj] using
          Submodule.reflection_mem_subspace_eq_self hk
  have hscore (x : EuclideanSpace ℝ κ) (k : Fin m) :
      (∑ l, rows k l * (R x) l) = ∑ l, rows (Equiv.swap i j k) l * x l := by
    rw [← hdot, ← hdot]
    calc
      inner ℝ (r k) (R x) = inner ℝ (R (r k)) x := by
        simpa only [R, Submodule.reflection_symm] using (R.inner_map_eq_flip (r k) x).symm
      _ = _ := by rw [hR]
  have hw (x : EuclideanSpace ℝ κ) :
      regularAssignment rows (R x).ofLp i = regularAssignment rows x.ofLp j := by
    change maxWeights (fun k => ∑ l, rows k l * (R x) l) i = _
    simp_rw [hscore]
    simpa only [regularAssignment, Equiv.swap_apply_left] using
      maxWeights_perm (fun k => ∑ l, rows k l * x l) (Equiv.swap i j) i
  have hobs (x : EuclideanSpace ℝ κ) :
      regularAssignment rows (R x).ofLp i * g (∑ k, rows i k * (R x) k) =
        regularAssignment rows x.ofLp j * g (∑ k, rows j k * x k) := by
    rw [hw, hscore, Equiv.swap_apply_left]
  rw [integral_standardGaussian_eq_euclidean, integral_standardGaussian_eq_euclidean]
  have hp : MeasurePreserving R (stdGaussian (EuclideanSpace ℝ κ))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨R.continuous.measurable, stdGaussian_map R⟩
  calc
    (∫ x : EuclideanSpace ℝ κ, regularAssignment rows x.ofLp i *
        g (∑ k, rows i k * x k) ∂stdGaussian _) =
        ∫ x : EuclideanSpace ℝ κ, regularAssignment rows (R x).ofLp i *
          g (∑ k, rows i k * (R x) k) ∂stdGaussian _ :=
      (hp.integral_comp R.toHomeomorph.measurableEmbedding _).symm
    _ = _ := by simp only [hobs]

theorem regularAssignment_mass_eq (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (i j : Fin m) :
    (∫ x, regularAssignment rows x i ∂standardGaussian κ) =
      ∫ x, regularAssignment rows x j ∂standardGaussian κ := by
  simpa only [mul_one] using regularAssignment_score_observable_eq rows hrows i j (fun _ => 1)

/-- A regular-simplex reference is exactly balanced under the actual finite
product standard Gaussian, including the implemented convention on ties. -/
theorem regularAssignment_mass (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (i : Fin m) :
    (∫ x, regularAssignment rows x i ∂standardGaussian κ) = 1 / (m : ℝ) := by
  have hmpos : 0 < m := Fin.pos_iff_nonempty.mpr inferInstance
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hsum : (∑ k, ∫ x, regularAssignment rows x k ∂standardGaussian κ) = 1 := by
    rw [← integral_finsetSum Finset.univ (fun k _ => regularAssignment_integrable rows k)]
    simp only [(regularAssignment_simplex rows _).2]
    simp
  have heq (k : Fin m) := regularAssignment_mass_eq rows hrows k i
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply (eq_div_iff hmne).mpr
  nlinarith

theorem regularAssignment_weighted_score_integrable (rows : Fin m → κ → ℝ) (i : Fin m) :
    Integrable (fun x => regularAssignment rows x i * (∑ k, rows i k * x k))
      (standardGaussian κ) := by
  classical
  exact integrable_weighted_score (standardGaussian κ) (regularAssignment rows)
    (fun x i => ∑ k, rows i k * x k) i
    (Filter.Eventually.of_forall (regularAssignment_simplex rows))
    (regularAssignment_measurable rows i).aemeasurable
    (gaussian_linear_score_integrable (fun _ => 0) (fun _ => 1) (rows i))

/-- Each label contributes exactly one m-th of the expected winning score. -/
theorem regularAssignment_selected_score (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (i : Fin m) :
    (∫ x, regularAssignment rows x i * (∑ k, rows i k * x k) ∂standardGaussian κ) =
      (∫ x, maxScore (fun j => ∑ k, rows j k * x k) ∂standardGaussian κ) / (m : ℝ) := by
  have hmpos : 0 < m := Fin.pos_iff_nonempty.mpr inferInstance
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hsum :
      (∑ j, ∫ x, regularAssignment rows x j * (∑ k, rows j k * x k) ∂standardGaussian κ) =
        ∫ x, maxScore (fun j => ∑ k, rows j k * x k) ∂standardGaussian κ := by
    rw [← integral_finsetSum Finset.univ
      (fun j _ => regularAssignment_weighted_score_integrable rows j)]
    apply integral_congr_ae
    filter_upwards with x
    exact maxWeights_score_identity (fun j => ∑ k, rows j k * x k)
  have heq (j : Fin m) :
      (∫ x, regularAssignment rows x j * (∑ k, rows j k * x k) ∂standardGaussian κ) =
        ∫ x, regularAssignment rows x i * (∑ k, rows i k * x k) ∂standardGaussian κ :=
    regularAssignment_score_observable_eq rows hrows j i id
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply (eq_div_iff hmne).mpr
  nlinarith

/-- The reference centroid's projection on its own score row has the exact
expected-maximum normalization. This does not assert the full vector direction. -/
theorem regularAssignment_centroid_projection (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (i : Fin m) :
    (∑ k, rows i k *
      gaussianCentroid (fun _ => 0) (fun _ => 1) (regularAssignment rows) i k) =
      (∫ x, maxScore (fun j => ∑ k, rows j k * x k) ∂standardGaussian κ) / (m : ℝ) := by
  classical
  have hint (k : κ) : Integrable (fun x => regularAssignment rows x i * x k)
      (standardGaussian κ) :=
    integrable_weighted_score (standardGaussian κ) (regularAssignment rows)
      (fun x _ => x k) i (Filter.Eventually.of_forall (regularAssignment_simplex rows))
      (regularAssignment_measurable rows i).aemeasurable
      (gaussian_product_coordinate_integrable (fun _ => 0) (fun _ => 1) k)
  calc
    _ = ∫ x, ∑ k, rows i k * (regularAssignment rows x i * x k)
        ∂standardGaussian κ := by
      rw [integral_finsetSum Finset.univ (fun k _ => (hint k).const_mul (rows i k))]
      simp only [integral_const_mul, gaussianCentroid, standardGaussian]
    _ = ∫ x, regularAssignment rows x i * (∑ k, rows i k * x k)
        ∂standardGaussian κ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := regularAssignment_selected_score rows hrows i

end NegativeVoting
