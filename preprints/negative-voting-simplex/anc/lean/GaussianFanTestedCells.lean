import GaussianFanScoreHessian

/-! Tested Gaussian winning cells. The weight/cell equality is derived from
actual Gaussian tie-nullness, and is valid for Bochner integrals even without
an integrability assumption. Affine tests are separately proved integrable
and evaluated through the actual centroid and mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators

namespace NegativeVotingFanTestedCells
open NegativeVotingFan NegativeVotingFanScore
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- At almost every Gaussian point, a winner weight is the indicator of its
literal closed winning cell. Distinct rows discharge tie-nullness. -/
theorem weights_eq_winningCell_indicator_ae (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (i : ι) :
    (fun x => weights B h x i) =ᵐ[stdGaussian (FSC.Coord d)]
      (winningCell B h i).indicator (fun _ => (1 : ℝ)) := by
  classical
  filter_upwards [ae_scores_injective B hB h] with x hx
  let a := NegativeVoting.chosenWinner (scores B h x)
  have ha (j : ι) (hj : j ≠ a) : scores B h x j < scores B h x a :=
    lt_of_le_of_ne (NegativeVoting.chosenWinner_max (scores B h x) j)
      (fun he => hj (hx he))
  have hw : weights B h x i = if i = a then 1 else 0 :=
    NegativeVoting.maxWeights_eq_indicator_of_strict_max (scores B h x) a ha i
  by_cases hi : i = a
  · have hmem : x ∈ winningCell B h i := by
      subst i
      exact fun j => NegativeVoting.chosenWinner_max (scores B h x) j
    rw [hw]
    simp only [ite_eq_left hi, Set.indicator_of_mem hmem]
  · have hnot : x ∉ winningCell B h i := by
      intro hmem
      exact not_le_of_gt (ha i hi) (hmem a)
    rw [hw]
    simp [hi, hnot]

section Bochner
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The same actual indicator equality for an arbitrary vector-valued test. -/
theorem weights_smul_eq_winningCell_indicator_ae (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (i : ι) (F : FSC.Coord d → V) :
    (fun x => weights B h x i • F x) =ᵐ[stdGaussian (FSC.Coord d)]
      (winningCell B h i).indicator F := by
  classical
  filter_upwards [weights_eq_winningCell_indicator_ae B hB h i] with x hx
  rw [hx]
  by_cases hmem : x ∈ winningCell B h i <;> simp [hmem]

/-- Actual equality of Bochner integrals. Integrability is not an input:
AE equality and the measurable-cell indicator identity handle both cases. -/
theorem integral_weights_smul_eq_cell (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (i : ι) (F : FSC.Coord d → V) :
    (∫ x, weights B h x i • F x ∂stdGaussian (FSC.Coord d)) =
      ∫ x in winningCell B h i, F x ∂stdGaussian (FSC.Coord d) := by
  rw [integral_congr_ae (weights_smul_eq_winningCell_indicator_ae B hB h i F),
    integral_indicator (winningCell_measurable B h i)]

end Bochner

/-- Scalar form for use in moving-cell differentiation. -/
theorem integral_weights_mul_eq_cell (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (i : ι) (F : FSC.Coord d → ℝ) :
    (∫ x, weights B h x i * F x ∂stdGaussian (FSC.Coord d)) =
      ∫ x in winningCell B h i, F x ∂stdGaussian (FSC.Coord d) := by
  simpa only [smul_eq_mul] using integral_weights_smul_eq_cell B hB h i F

/-- The centroid already used by the joint score derivative is literally
the unnormalized first moment of the actual winning cell. -/
theorem centroid_eq_cell_integral (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (i : ι) :
    centroid B h i = ∫ x in winningCell B h i, x ∂stdGaussian (FSC.Coord d) := by
  exact integral_weights_smul_eq_cell B hB h i id

/-- All affine tests are genuinely Gaussian-integrable. -/
theorem affine_test_integrable (D : FSC.Coord d) (v : ℝ) :
    Integrable (fun x : FSC.Coord d => inner ℝ D x + v) (stdGaussian (FSC.Coord d)) := by
  exact (IsGaussian.integrable_id.const_inner (𝕜 := ℝ) D).add (integrable_const v)

/-- The weighted affine test is integrable even before using distinctness. -/
theorem weighted_affine_test_integrable (B : ι → FSC.Coord d)
    (h : ι → ℝ) (i : ι) (D : FSC.Coord d) (v : ℝ) :
    Integrable (fun x => weights B h x i * (inner ℝ D x + v))
      (stdGaussian (FSC.Coord d)) := by
  classical
  exact NegativeVoting.integrable_weighted_score (stdGaussian (FSC.Coord d))
    (weights B h) (fun x _ => inner ℝ D x + v) i
    (Eventually.of_forall (weights_simplex B h))
    (weights_measurable B h i).aemeasurable (affine_test_integrable D v)

/-- Evaluation of the integrable affine test through the actual centroid
and mass. This also holds for tied rows with their fractional winner weights. -/
theorem integral_weighted_affine_test (B : ι → FSC.Coord d)
    (h : ι → ℝ) (i : ι) (D : FSC.Coord d) (v : ℝ) :
    (∫ x, weights B h x i * (inner ℝ D x + v) ∂stdGaussian (FSC.Coord d)) =
      inner ℝ D (centroid B h i) + v * mass B h i := by
  have hinner : Integrable (fun x => weights B h x i * inner ℝ D x)
      (stdGaussian (FSC.Coord d)) := by
    simpa only [real_inner_smul_right] using (centroid_integrable B h i).const_inner (𝕜 := ℝ) D
  simp_rw [mul_add]
  rw [integral_add hinner ((weights_integrable B h i).mul_const v), integral_mul_const,
    mul_comm v (mass B h i)]
  congr 1
  simpa only [real_inner_smul_right, centroid] using
    integral_inner (𝕜 := ℝ) (centroid_integrable B h i) D

/-- Exact affine test on the literal cell, with its actual first moment. -/
theorem integral_cell_affine_test (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (i : ι) (D : FSC.Coord d) (v : ℝ) :
    (∫ x in winningCell B h i, inner ℝ D x + v ∂stdGaussian (FSC.Coord d)) =
      inner ℝ D (centroid B h i) + v * mass B h i := by
  rw [← integral_weights_mul_eq_cell B hB h i]
  exact integral_weighted_affine_test B h i D v

/-- The actual joint derivative of the expected maximum is a sum of
integrals over the literal moving cells. This is the input needed to
subsequently differentiate the first derivative by a moving-boundary formula. -/
theorem jointDerivative_eq_cell_affine_tests (B : ι → FSC.Coord d)
    (hB : Function.Injective B) (h : ι → ℝ) (D : ι → FSC.Coord d) (v : ι → ℝ) :
    jointDerivative B h (D, v) =
      ∑ i, ∫ x in winningCell B h i, inner ℝ (D i) x + v i ∂stdGaussian (FSC.Coord d) := by
  rw [jointDerivative_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_cell_affine_test B hB h i, mul_comm (v i) (mass B h i)]

end NegativeVotingFanTestedCells
