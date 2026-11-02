import Mathlib
import NegativeVoting.Integrability
import NegativeVoting.GaussianRouting

/-! Genuine Gaussian integrability facts used by finite linear-score routing. -/

namespace NegativeVoting

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- The exponential of every real multiple of a Gaussian is integrable,
including the zero-variance (Dirac) case. -/
theorem gaussian_exp_integrable (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianReal μ v) := by
  exact integrable_exp_mul_gaussianReal t

/-- The Gaussian identity random variable is integrable, proved by exponential
moment domination rather than assumed as a routing input. -/
theorem gaussian_id_integrable (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x) (gaussianReal μ v) := by
  have hplus : Integrable (fun x : ℝ => Real.exp x) (gaussianReal μ v) := by
    simpa using gaussian_exp_integrable μ v 1
  have hminus : Integrable (fun x : ℝ => Real.exp (-x)) (gaussianReal μ v) := by
    simpa using gaussian_exp_integrable μ v (-1)
  apply (hplus.add hminus).mono' measurable_id.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  change |x| ≤ Real.exp x + Real.exp (-x)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have he := Real.add_one_le_exp x
    have hp := Real.exp_pos (-x)
    linarith
  · rw [abs_of_nonpos hx]
    have he := Real.add_one_le_exp (-x)
    have hp := Real.exp_pos x
    linarith

/-- A coordinate of a finite product of Gaussian probability measures has the
specified Gaussian marginal law. -/
theorem gaussian_product_coordinate_law {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : κ → ℝ) (v : κ → ℝ≥0) (j : κ) :
    (Measure.pi (fun i => gaussianReal (μ i) (v i))).map
      (fun x : κ → ℝ => x j) = gaussianReal (μ j) (v j) := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply j) hs]
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  simp [Function.update_apply, apply_ite]

/-- Every coordinate is integrable under the actual finite product Gaussian. -/
theorem gaussian_product_coordinate_integrable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : κ → ℝ) (v : κ → ℝ≥0) (j : κ) :
    Integrable (fun x : κ → ℝ => x j) (Measure.pi (fun i => gaussianReal (μ i) (v i))) := by
  have h : Integrable (fun x : ℝ => x)
      ((Measure.pi (fun i => gaussianReal (μ i) (v i))).map (fun x : κ → ℝ => x j)) := by
    rw [gaussian_product_coordinate_law]
    exact gaussian_id_integrable (μ j) (v j)
  exact h.comp_measurable (measurable_pi_apply j)

/-- Every finite linear score is integrable under a finite product Gaussian. -/
theorem gaussian_linear_score_integrable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : κ → ℝ) (v : κ → ℝ≥0) (a : κ → ℝ) :
    Integrable (fun x : κ → ℝ => ∑ j, a j * x j)
      (Measure.pi (fun i => gaussianReal (μ i) (v i))) := by
  exact integrable_finsetSum Finset.univ (fun j _ =>
    (gaussian_product_coordinate_integrable μ v j).const_mul (a j))

/-- The maximum of finitely many linear Gaussian scores is integrable without
assuming an integrability premise for the maximum itself. -/
theorem gaussian_linear_max_integrable {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : κ → ℝ) (v : κ → ℝ≥0) (a : ι → κ → ℝ) :
    Integrable (fun x : κ → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, a i j * x j))
      (Measure.pi (fun i => gaussianReal (μ i) (v i))) := by
  exact integrable_finite_max _ _ Finset.univ Finset.univ_nonempty
    (fun i _ => gaussian_linear_score_integrable μ v (a i))

/-- Rigidity for actual Gaussian linear-score routing with integrability proved
from the measure and measurable simplex weights. No no-tie or integrability
hypothesis is hidden in this statement. -/
theorem ae_gaussian_routing_rigidity_from_zero_loss {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (hvariance : ∀ j, variances j ≠ 0)
    (rows : ι → Fin (n + 1) → ℝ) (hrows : Function.Injective rows)
    (p : (Fin (n + 1) → ℝ) → ι → ℝ) (winner : (Fin (n + 1) → ℝ) → ι)
    (hp : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i)
      (Measure.pi (fun j => gaussianReal (means j) (variances j))))
    (hmax : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∀ i, linearScore (rows i) x ≤ linearScore (rows (winner x)) x)
    (hzero : ∫ x, routingLoss (p x) (fun i => linearScore (rows i) x) (winner x)
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j)) = 0) :
    ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∀ i, p x i = if i = winner x then 1 else 0 := by
  apply ae_gaussian_routing_rigidity means variances hvariance rows hrows
    p winner hp hmax ?_ hzero
  apply integrable_routing_loss _ p (fun x i => linearScore (rows i) x) winner hp hpmeas
    (fun i => gaussian_linear_score_integrable means variances (rows i)) hmax

/-- A canonical (classically chosen) maximizing label of a nonempty finite score
vector. No measurability of this label map is needed for the following theorem. -/
noncomputable def chosenWinner {ι : Type*} [Fintype ι] [Nonempty ι] (scores : ι → ℝ) : ι := by
  classical
  exact (Finset.exists_max_image Finset.univ scores Finset.univ_nonempty).choose

/-- The chosen label maximizes the actual score vector at every point. -/
theorem chosenWinner_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (scores : ι → ℝ) (i : ι) : scores i ≤ scores (chosenWinner scores) := by
  classical
  exact (Finset.exists_max_image Finset.univ scores Finset.univ_nonempty).choose_spec.2
    i (Finset.mem_univ i)

/-- The selected score is exactly the finite maximum. -/
theorem finite_max_eq_chosenWinner {ι : Type*} [Fintype ι] [Nonempty ι]
    (scores : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty scores = scores (chosenWinner scores) := by
  classical
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => chosenWinner_max scores i)
  · exact Finset.le_sup' scores (Finset.mem_univ (chosenWinner scores))

/-- Concrete Gaussian zero-gap rigidity. The premise uses the actual finite
maximum of distinct linear scores. Neither a winning selector, no-tie property,
nor routing-loss integrability is assumed: all three are derived.

The remaining zero-gap premise is a first-moment equality, not the unformalized
full-noise Gaussian simplex comparison. -/
theorem ae_gaussian_indicator_of_zero_maximum_gap {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (hvariance : ∀ j, variances j ≠ 0)
    (rows : ι → Fin (n + 1) → ℝ) (hrows : Function.Injective rows)
    (p : (Fin (n + 1) → ℝ) → ι → ℝ)
    (hp : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i)
      (Measure.pi (fun j => gaussianReal (means j) (variances j))))
    (hzero : ∫ x,
      (Finset.univ.sup' Finset.univ_nonempty (fun i => linearScore (rows i) x) -
        ∑ i, p x i * linearScore (rows i) x)
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j)) = 0) :
    ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∃! t, (∀ i, p x i = if i = t then 1 else 0) ∧
        (∀ i, i ≠ t → linearScore (rows i) x < linearScore (rows t) x) := by
  let winner := fun x => chosenWinner (fun i => linearScore (rows i) x)
  have hmax : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∀ i, linearScore (rows i) x ≤ linearScore (rows (winner x)) x :=
    Filter.Eventually.of_forall (fun x i => chosenWinner_max (fun k => linearScore (rows k) x) i)
  have hloss : ∫ x, routingLoss (p x) (fun i => linearScore (rows i) x) (winner x)
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j)) = 0 := by
    simpa only [routingLoss, finite_max_eq_chosenWinner, winner] using hzero
  have hpure := ae_gaussian_routing_rigidity_from_zero_loss means variances hvariance
    rows hrows p winner hp hpmeas hmax hloss
  filter_upwards [hpure, ae_gaussian_scores_injective means variances hvariance rows hrows]
    with x hpx hinj
  have hstrict : ∀ i, i ≠ winner x → linearScore (rows i) x < linearScore (rows (winner x)) x := by
    intro i hi
    exact lt_of_le_of_ne (chosenWinner_max (fun k => linearScore (rows k) x) i) (fun h => hi (hinj h))
  refine ⟨winner x, ⟨hpx, hstrict⟩, ?_⟩
  intro t ht
  by_contra hne
  have h1 := hstrict t hne
  have h2 := ht.2 (winner x) (Ne.symm hne)
  linarith

end NegativeVoting
