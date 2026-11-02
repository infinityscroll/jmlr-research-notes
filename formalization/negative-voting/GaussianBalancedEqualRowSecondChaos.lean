import GaussianBalancedOffsetCertificateCancellation
import GaussianEqualRowRegularCoefficient
import GaussianRegularCovarianceDeficit

/-! The actual balanced equal-row quadratic certificate and its exact
offset payment. The free-maximum deficit-relative estimate is an explicit
intermediate premise below; this module does not assert that estimate. No
fixed additive tail is introduced, including at zero covariance deficit. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedEqualRowSecondChaos
open NegativeVoting NegativeVotingModern NegativeVotingFan NegativeVotingFanScore
  NegativeVotingFanTestedCells NegativeVotingFanQuadraticMoments
  NegativeVotingBalancedOffsetCertificateCancellation NegativeVotingEqualRowQuadraticCertificate
  NegativeVotingEqualRowRoutingComparison NegativeVotingEqualRowRegularCoefficient
  NegativeVotingEqualRowMaximumLaw NegativeVotingEqualRowMaximumComparison
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumSecondMoment
  NegativeVotingBalancedReference NegativeVotingFanValue NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingRegularCovarianceDeficit NegativeVotingCentroidOptimization
  NegativeVotingPolynomialFacetLogBound NegativeVotingConditionalSecondMoment
  NegativeVotingGaussianMaximumLocalization NegativeVotingGaussianMaximumMean
  NegativeVotingExteriorReference OAI.MinUncut.GaussianHermite
variable {n d : ℕ}

theorem expectedMax_zero_eq_rowMaximum (B : Fin (n+2) → FSC.Coord d) :
    expectedMax B 0 = ∫ x,rowMaximum B x ∂standardGaussian (Fin d) := by
  have hh := (gaussian_toLp_measurePreserving d).integral_comp'
    (fun x : FSC.Coord d => maxScore (scores B 0 x))
  change (∫ x,maxScore (scores B 0 (MeasurableEquiv.toLp 2 (Fin d→ℝ) x))
    ∂standardGaussian (Fin d))=expectedMax B 0 at hh
  rw [←hh]
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg maxScore
  funext i
  change inner ℝ (B i) (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)+0=∑j,B i j*x j
  simp only [add_zero,PiLp.inner_apply,Real.inner_apply]
  rfl

/-- Literal cell square integrals are precisely the coordinate test used by
the sharp tensor certificate; this includes the actual tie-null transport. -/
theorem scoreSquareSum_eq_weightedRowSquare
    (B : Fin (n+2) → FSC.Coord d) (hB : Function.Injective B) (h : Fin (n+2)→ℝ) :
    scoreSquareSum B h =
      ∫ x,weightedRowSquare (fun i j=>B i j)
        (fun y=>weights B h (MeasurableEquiv.toLp 2 (Fin d→ℝ) y)) x
        ∂standardGaussian (Fin d) := by
  have hi i : Integrable (fun x : FSC.Coord d=>weights B h x i*(inner ℝ (B i) x)^2)
      (stdGaussian (FSC.Coord d)) :=
    integrable_weighted_score _ (weights B h) (fun x _=>(inner ℝ (B i) x)^2) i
      (Filter.Eventually.of_forall (weights_simplex B h))
      (weights_measurable B h i).aemeasurable (scoreSquare_integrable _ (B i))
  have hh := (gaussian_toLp_measurePreserving d).integral_comp'
    (fun x : FSC.Coord d=>∑i,weights B h x i*(inner ℝ (B i) x)^2)
  rw [integral_finsetSum _ (fun i _=>hi i)] at hh
  simp_rw [integral_weights_mul_eq_cell B hB h] at hh
  change _=scoreSquareSum B h at hh
  rw [←hh]
  apply integral_congr_ae
  filter_upwards with x
  simp only [weightedRowSquare,PiLp.inner_apply,Real.inner_apply]
  rfl

theorem actual_equal_row_certificate
    (hn : 0 < n) (B : Fin (n+2) → FSC.Coord d) (hB : Function.Injective B)
    (α : ℝ) (hα : 0 < α)
    (hrow : ∀i,‖B i‖^2=α^2*(1-1/((n+2:ℕ):ℝ))) (hcenter : ∑i,B i=0)
    (h : Fin (n+2)→ℝ) :
    (max (scoreSquareSum B h-α^2*(1-1/((n+2:ℕ):ℝ))) 0)^2 /
      (2*regularDenominator (n+2) α) ≤ secondEnergy B h := by
  rw [scoreSquareSum_eq_weightedRowSquare B hB h,secondEnergy_eq_actual_chaos B hB h]
  apply ae_simplex_equal_row_certificate_euclidean (by omega) B α hα hrow hcenter
  · intro i
    exact ((weights_measurable B h i).comp (MeasurableEquiv.toLp 2 (Fin d→ℝ)).measurable).aemeasurable
  · exact Filter.Eventually.of_forall (fun x=>(weights_simplex B h _).1)
  · exact Filter.Eventually.of_forall (fun x=>(weights_simplex B h _).2)

theorem uniform_optimizedValue_eq_expectedMax
    (B : Fin (n+2) → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (h : Fin (n+2)→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹) :
    optimizedValue B (uniformMass n)=expectedMax B h := by
  have he := optimizedValue_eq_of_mass B (uniformMass n) σ hσ hlower
    (uniformMass_pos n) (uniformMass_sum n) ⟨h,hs⟩ (by
      funext i
      simp only [hmass,uniformMass,one_div,Nat.cast_add,Nat.cast_ofNat])
  simpa only [potential,uniformMass,Finset.mul_sum,←Finset.mul_sum,hs,mul_zero,sub_zero]
    using he

theorem balanced_drop_nonneg
    (B : Fin (n+2) → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (h : Fin (n+2)→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹) :
    0 ≤ expectedMax B 0-expectedMax B h := by
  have hh := optimizedValue_le_potential B (uniformMass n)
    (fun i=>(uniformMass_pos n i).le) (uniformMass_sum n) 0
  rw [uniform_optimizedValue_eq_expectedMax B σ hσ hlower h hs hmass] at hh
  simpa only [potential,ZeroMemClass.coe_zero,Pi.zero_apply,mul_zero,Finset.sum_const_zero,
    sub_zero,sub_nonneg] using hh

theorem equal_row_free_mean_le (B : Fin (n+2) → FSC.Coord d)
    (α : ℝ) (hα : 0 < α)
    (hrow : ∀i,‖B i‖^2=α^2*(1-1/((n+2:ℕ):ℝ))) :
    expectedMax B 0 ≤ α*maximumMean n := by
  rw [expectedMax_zero_eq_rowMaximum]
  exact (equal_row_maximum_comparison B α hα
    (fun i=>by simpa only [real_inner_self_eq_norm_sq] using hrow i) 0 (by norm_num)).1

/-- The only undischargeable premise here is the displayed free-maximum
moment estimate. The offset error is derived from actual geometry and is
paid by the same balanced mean deficit, not by an additive remainder. -/
theorem balanced_test_deficit_of_free_bound
    (hn : 0 < n) (B : Fin (n+2) → FSC.Coord d) (α σ K : ℝ)
    (hα : 0 < α) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀i,‖B i‖^2=α^2*(1-1/((n+2:ℕ):ℝ))) (hcond : 2*α/σ ≤ 4)
    (h : Fin (n+2)→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹)
    (hfree : α^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-scoreSquareSum B 0 ≤
      K*α*(α*maximumMean n-expectedMax B h)) :
    regularQuadraticTestValue (n+2) α-
      (scoreSquareSum B h-α^2*(1-1/((n+2:ℕ):ℝ))) ≤
      α*(K+32*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4)*
        (α*maximumMean n-expectedMax B h) := by
  have hr i : ‖B i‖ ≤ α := by
    apply (sq_le_sq₀ (norm_nonneg _) hα.le).mp
    rw [hrow]
    have hc : 0 ≤ 1/((n+2:ℕ):ℝ) := by positivity
    nlinarith [sq_nonneg α]
  have hoff := scoreSquareSum_offset_log_le_drop B (by simp;omega) σ α hσ hα
    hlower hr hcond h hs (by simpa only [Fintype.card_fin] using hmass)
  simp only [Fintype.card_fin] at hoff
  have hmean := equal_row_free_mean_le B α hα hrow
  have hK : 0 ≤ 32*α*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4 := by
    positivity [show 0 ≤ quarticLogConstant 2 by unfold quarticLogConstant;positivity]
  have hpay := mul_le_mul_of_nonneg_left
    (show expectedMax B 0-expectedMax B h ≤ α*maximumMean n-expectedMax B h by linarith) hK
  have ha := (abs_le.mp hoff).1
  rw [regular_test_value_eq]
  nlinarith only [hfree,hpay,ha]

/-- Sharp denominator conversion. In particular the right side vanishes
exactly when the actual balanced mean deficit vanishes. -/
theorem actual_secondEnergy_lower_of_free_bound
    (hn : 0 < n) (B : Fin (n+2) → FSC.Coord d) (α σ K : ℝ)
    (hα : 0 < α) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀i,‖B i‖^2=α^2*(1-1/((n+2:ℕ):ℝ))) (hcenter : ∑i,B i=0)
    (hcond : 2*α/σ ≤ 4) (hM : 1 ≤ maximumSecondMoment n)
    (h : Fin (n+2)→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹)
    (hfree : α^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-scoreSquareSum B 0 ≤
      K*α*(α*maximumMean n-expectedMax B h)) :
    referenceSecondWeight n-
      (regularQuadraticTestValue (n+2) α/regularDenominator (n+2) α)*
        (α*(K+32*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4)*
          (α*maximumMean n-expectedMax B h)) ≤ secondEnergy B h := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hd := balanced_test_deficit_of_free_bound hn B α σ K hα hσ hlower hrow hcond h hs hmass hfree
  have hc := actual_equal_row_certificate hn B hinj α hα hrow hcenter h
  have hp := positive_square_tangent _ _ _ hd
  have hD := regularDenominator_pos (by omega : 3 ≤ n+2) α hα
  have hS : 0 ≤ regularQuadraticTestValue (n+2) α := by
    rw [regular_test_value_eq]
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hM)
  rw [max_eq_left hS] at hp
  rw [←regular_certificate_square_eq hn α hα]
  apply (mul_le_mul_iff_right₀ (show 0<2*regularDenominator (n+2) α by positivity)).mp
  rw [mul_comm (2*regularDenominator (n+2) α) (_-_)]
  rw [quadratic_fraction_identity _ _ _ hD.ne']
  have hc' := (div_le_iff₀ (show 0<2*regularDenominator (n+2) α by positivity)).mp hc
  nlinarith only [hp,hc']

theorem certificate_linear_coefficient_le (m M α L : ℝ)
    (hm : 4 ≤ m) (hL : 1 ≤ L) (hM0 : 1 ≤ M) (hM : M ≤ 5*L)
    (hα : 0 < α) (hscale : L/m^2 ≤ α^2) :
    ((α^2*(M-1))/(α^4*(m-1)*(m-2)/m))*α ≤ 15*L := by
  let A := (α^2*(M-1))/(α^4*(m-1)*(m-2)/m)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [show 0 ≤ M-1 by linarith,show 0 < m-1 by linarith,
      show 0 < m-2 by linarith,show 0 < m by linarith]
  have hroot := Real.sq_sqrt (show 0 ≤ 256*L by positivity)
  have hT : 16 ≤ Real.sqrt (256*L) := by
    nlinarith [Real.sqrt_nonneg (256*L)]
  have hc := (routing_coefficients_bound m M α L hm hL hM0 hM hα hscale).1
  change A*(2*α*Real.sqrt (256*L)) ≤ 480*L at hc
  have hl := mul_le_mul_of_nonneg_left hT (show 0 ≤ A*(2*α) by positivity)
  change A*α ≤ 15*L
  nlinarith only [hc,hl]

/-- Conditional free-moment composition with an explicit polynomial-log
coefficient, independent of ambient dimension and with no fixed tail. -/
theorem actual_secondEnergy_polylog_lower_of_free_bound
    (hn : 2 ≤ n) (B : Fin (n+2) → FSC.Coord d) (α σ K : ℝ)
    (hα : 0 < α) (hσ : 0 < σ) (hK : 0 ≤ K)
    (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀i,‖B i‖^2=α^2*(1-1/((n+2:ℕ):ℝ))) (hcenter : ∑i,B i=0)
    (hcond : 2*α/σ ≤ 4) (hM0 : 1 ≤ maximumSecondMoment n)
    (hM : maximumSecondMoment n ≤ 5*(1+Real.log ((n+2:ℕ):ℝ)))
    (hscale : (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)^2 ≤ α^2)
    (h : Fin (n+2)→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹)
    (hfree : α^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-scoreSquareSum B 0 ≤
      K*α*(α*maximumMean n-expectedMax B h)) :
    referenceSecondWeight n-
      (15*(1+Real.log ((n+2:ℕ):ℝ))*
        (K+32*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4))*
          (α*maximumMean n-expectedMax B h) ≤ secondEnergy B h := by
  have hraw := actual_secondEnergy_lower_of_free_bound (by omega) B α σ K hα hσ
    hlower hrow hcenter hcond hM0 h hs hmass hfree
  have hL : 1 ≤ 1+Real.log ((n+2:ℕ):ℝ) := by
    have hh := Real.log_nonneg (show 1 ≤ ((n+2:ℕ):ℝ) by exact_mod_cast (show 1 ≤ n+2 by omega))
    linarith
  have hcoef := certificate_linear_coefficient_le ((n+2:ℕ):ℝ) (maximumSecondMoment n) α
    (1+Real.log ((n+2:ℕ):ℝ)) (by exact_mod_cast (show 4 ≤ n+2 by omega)) hL hM0 hM hα hscale
  have hΔ : 0 ≤ α*maximumMean n-expectedMax B h := by
    have h1 := equal_row_free_mean_le B α hα hrow
    have h2 := balanced_drop_nonneg B σ hσ hlower h hs hmass
    linarith
  have htotal : 0 ≤ K+32*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4 := by
    positivity [show 0 ≤ quarticLogConstant 2 by unfold quarticLogConstant;positivity]
  have hp := mul_le_mul_of_nonneg_right hcoef (mul_nonneg htotal hΔ)
  rw [regular_test_value_eq] at hraw
  unfold regularDenominator at hraw
  nlinarith only [hraw,hp]

/-- At the prescribed reference radius, equal row norms make the exact
covariance remainder equal the balanced mean deficit. No covariance
representation, trace-zero assumption or supplied value identity is used. -/
theorem regular_deficit_eq_balanced_gap_of_equal_rows
    (B : Fin (n+2) → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀i,‖B i‖^2=(referenceScale n)^2*(1-1/((n+2:ℕ):ℝ)))
    (h : Fin (n+2)→ℝ) (hs : ∑i,h i=0)
    (hmass : ∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹) :
    regularCovarianceDeficit n B=referenceScale n*maximumMean n-expectedMax B h := by
  have hm0 : (n:ℝ)+2 ≠ 0 := by positivity
  have hn0 : (n:ℝ)+1 ≠ 0 := by positivity
  have henergy : rowEnergy B=referenceFirstWeight n := by
    unfold rowEnergy
    simp_rw [hrow]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold referenceScale referenceFirstWeight
    push_cast
    field_simp
    <;> ring
  have href : referenceFirstWeight n=referenceScale n*maximumMean n := by
    unfold referenceFirstWeight referenceScale
    ring
  rw [regularCovarianceDeficit,henergy,
    uniform_optimizedValue_eq_expectedMax B σ hσ hlower h hs hmass,href]
  ring

/-- A dimension-first conditional endpoint: all actual offset, certificate
and scale inputs are discharged. Only the displayed deficit-relative free
moment bound remains for the separately implemented maximum-tail module. -/
theorem eventually_reference_secondEnergy_lower_of_free_bound :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (B : Fin (n+2)→FSC.Coord d)
      (σ K : ℝ), 0 < σ → 0 ≤ K → CenteredSingularLowerBound B σ →
      (∀i,‖B i‖^2=(referenceScale n)^2*(1-1/((n+2:ℕ):ℝ))) →
      (∑i,B i=0) → 2*referenceScale n/σ ≤ 4 →
      ∀ (h : Fin (n+2)→ℝ), (∑i,h i=0) →
        (∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹) →
        (referenceScale n)^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-scoreSquareSum B 0 ≤
          K*referenceScale n*regularCovarianceDeficit n B →
        referenceSecondWeight n-
          (15*(1+Real.log ((n+2:ℕ):ℝ))*
            (K+32*quarticLogConstant 2*(1+Real.log ((n+2:ℕ):ℝ))^4))*
              regularCovarianceDeficit n B ≤ secondEnergy B h := by
  filter_upwards [eventually_ge_atTop (2:ℕ),eventually_maximumSecondMoment_ge_one,
    eventually_maximum_second_moment_log_bound,eventually_reference_scale_bounds]
      with n hn hM0 hM hscale
  intro d B σ K hσ hK hlower hrow hcenter hcond h hs hmass hfree
  have he := regular_deficit_eq_balanced_gap_of_equal_rows B σ hσ hlower hrow h hs hmass
  rw [he] at hfree ⊢
  apply actual_secondEnergy_polylog_lower_of_free_bound hn B (referenceScale n) σ K
    (referenceScale_pos n) hσ hK hlower hrow hcenter hcond hM0
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using (show maximumSecondMoment n ≤
      5*(1+Real.log ((n:ℝ)+2)) by linarith)
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale.1
  · exact hs
  · exact hmass
  · exact hfree

end NegativeVotingBalancedEqualRowSecondChaos
