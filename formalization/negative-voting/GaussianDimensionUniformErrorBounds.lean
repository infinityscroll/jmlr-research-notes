import GaussianSmoothErrorTube

/-!
# Dimension-first uniformity for the actual error and its normal tube

These companion statements choose the natural-number threshold before the
ambient dimension.  The earlier smallness estimates are used unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical ENNReal

namespace NegativeVotingDimensionUniformErrorBounds
open NegativeVotingRegularPairCoefficient NegativeVotingRegularFacetRange
  NegativeVotingSmoothErrorMoment NegativeVotingSmoothErrorNormalDerivative NegativeVotingSmoothErrorTube

theorem exists_dimension_uniform_error_moments (A : ℝ) (hA : 1 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B : Fin (n + 2) → FSC.Coord d), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a b : Fin (n + 2) → ℝ) (D r : ℝ), 0 ≤ D →
      (∀ i, (a i) ^ 2 ≤ D * logScale n) → (∀ i, |b i| ≤ 1) →
      0 < r → r ≤ 1 / ((n : ℝ) + 1) →
      MemLp (fun x : FSC.Coord d => smoothPairError n r
        (fun i => a i + inner ℝ (B i) x) / r)
        (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ∧
      eLpNorm (fun x : FSC.Coord d => smoothPairError n r
        (fun i => a i + inner ℝ (B i) x) / r)
        (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ≤
        ENNReal.ofReal (momentConstant A * logScale n * Real.sqrt (logScale n)) *
          ENNReal.ofReal (Real.exp (1 + D / 4)) ∧
      MemLp (fun x : FSC.Coord d => smoothPairDirectional n r
        (fun i => a i + inner ℝ (B i) x) b / r)
        (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ∧
      eLpNorm (fun x : FSC.Coord d => smoothPairDirectional n r
        (fun i => a i + inner ℝ (B i) x) b / r)
        (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ≤
        ENNReal.ofReal (derivativeMomentConstant A * logScale n * Real.sqrt (logScale n)) *
          ENNReal.ofReal (Real.exp (1 + D / 4)) := by
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold A hA0
  refine ⟨N, ?_⟩
  intro n hn d B hv a b D r hD ha hb hr hrange
  obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
  have hL := logScale_one_le n
  have hqL : logScale n ≤ A * logScale n := by nlinarith
  have hq : 1 ≤ A * logScale n := hL.trans hqL
  have hs : 2560 * rangeFacetConstant * r * (A * logScale n) * (logScale n) ^ 2 ≤ 1 := by
    convert hsmall using 1
    ring
  exact ⟨smoothPairError_div_memLp n B hv a A r (A * logScale n) hA0 hr hrhalf hq le_rfl hrL hs,
    smoothPairError_div_norm_le n B hv a A D r (A * logScale n) hA0 hD ha hr hrhalf hqL le_rfl hrL hs,
    smoothPairDirectional_div_memLp n B hv a b hb A r (A * logScale n) hA0 hr hrhalf hq le_rfl hrL hs,
    smoothPairDirectional_div_norm_le n B hv a b hb A D r (A * logScale n)
      hA0 hD ha hr hrhalf hqL le_rfl hrL hs⟩

/-- The score slopes may be independent of the Gaussian-space rows, as
required by normal coordinates on an actual tangent plane. -/
theorem exists_dimension_uniform_error_tube (A : ℝ) (hA : 2 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B : Fin (n + 2) → FSC.Coord d), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a : Fin (n + 2) → ℝ) (D : ℝ), 0 ≤ D →
      (∀ i, (a i) ^ 2 ≤ D * logScale n) →
      ∃ W : FSC.Coord d → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧
        MemLp W (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ∧
        eLpNorm W (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ≤
          ENNReal.ofReal (tubeConstant A * logScale n * Real.sqrt (logScale n)) *
            ENNReal.ofReal (Real.exp (1 + (2 * D + 2) / 4)) ∧
        ∀ r : ℝ, 0 < r → r ≤ 1 / ((n : ℝ) + 1) →
          ∀ b : Fin (n + 2) → ℝ, (∀ i, |b i| ≤ 1) → ∀ x : FSC.Coord d,
          ContinuousOn (fun t : ℝ => smoothPairError n r
            (fun i => a i + inner ℝ (B i) x + t * b i) / r) (Icc 0 1) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            |smoothPairError n r (fun i => a i + inner ℝ (B i) x + t * b i)| / r ≤ W x ∧
            |deriv (fun s : ℝ => smoothPairError n r
              (fun i => a i + inner ℝ (B i) x + s * b i)) t| / r ≤ W x ∧
            |smoothPairError n r (fun i => a i + inner ℝ (B i) x + t * b i) -
              smoothPairError n r (fun i => a i + inner ℝ (B i) x)| / r ≤ W x * t := by
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold A hA0
  refine ⟨N, ?_⟩
  intro n hn d B hv a D hD ha
  have hL := logScale_one_le n
  have hq : 2 * logScale n ≤ A * logScale n := by nlinarith
  have hq0 : 0 < A * logScale n := by nlinarith
  refine ⟨tubeEnvelope n A (A * logScale n) B a, measurable_tubeEnvelope n A _ B a,
    ?_, tubeEnvelope_memLp n A _ hq0 B hv a, tubeEnvelope_norm_le n A D _ hA0 hD hq B hv a ha, ?_⟩
  · intro x
    rw [tubeEnvelope_eq_scalar]
    exact scalarTubeEnvelope_nonneg n A _ hA0 _
  · intro r hr hrange b hb x
    obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
    have hs : 2560 * rangeFacetConstant * r * (A * logScale n) * (logScale n) ^ 2 ≤ 1 := by
      convert hsmall using 1
      ring
    let u := fun i => a i + inner ℝ (B i) x
    have hpath (t : ℝ) := hasDerivAt_smoothPairError n r u b t
    constructor
    · intro t ht
      exact ((hpath t).div_const r).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hpath t).deriv, tubeEnvelope_eq_scalar]
      have hc := scalar_tube_control n A r (A * logScale n) hA0 hr hrhalf
        (by nlinarith) le_rfl hrL hs u b hb t ht
      exact ⟨hc.1, hc.2, scalar_tube_increment n A r (A * logScale n) hA0 hr hrhalf
        (by nlinarith) le_rfl hrL hs u b hb t ht⟩

end NegativeVotingDimensionUniformErrorBounds
