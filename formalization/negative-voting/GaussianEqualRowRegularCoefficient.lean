import GaussianEqualRowRoutingComparison
import GaussianRegularSecondGap
import GaussianExteriorReferenceBounds

/-! The sharp equal-row quadratic certificate has exactly the actual regular
second-chaos coefficient. The frozen Gaussian cutoff leaves only the literal
first-moment proxy loss and an explicit scalar tail. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace Topology
namespace NegativeVotingEqualRowRegularCoefficient
open NegativeVoting NegativeVotingModern NegativeVotingEqualRowQuadraticCertificate
  NegativeVotingEqualRowRoutingComparison NegativeVotingGaussianMaximumSecondMoment
  NegativeVotingGaussianMaximumLocalization NegativeVotingRegularSecondGap
  NegativeVotingRegularMaximum NegativeVotingBalancedReference NegativeVotingExteriorReference
  NegativeVotingGaussianMaximumMean OAI.MinUncut.GaussianHermite
variable {n d : ℕ}

theorem regular_test_value_eq (n : ℕ) (α : ℝ) :
    regularQuadraticTestValue (n+2) α=α^2*(maximumSecondMoment n-1) := rfl

/-- Exact matching of the sharp denominator with the already proved actual
regular tensor norm. This equality itself does not require positivity of S. -/
theorem regular_certificate_square_eq (hn : 0 < n) (α : ℝ) (hα : 0 < α) :
    (regularQuadraticTestValue (n+2) α)^2/(2*regularDenominator (n+2) α)=
      referenceSecondWeight n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [regular_test_value_eq]
  unfold regularDenominator referenceSecondWeight
  push_cast
  rw [show (n:ℝ)+2-1=(n:ℝ)+1 by ring,show (n:ℝ)+2-2=(n:ℝ) by ring]
  field_simp [ne_of_gt hnR,ne_of_gt hα,show (n:ℝ)+1 ≠ 0 by positivity]
  <;> ring

theorem regular_certificate_positive_square_eq (hn : 0 < n) (α : ℝ) (hα : 0 < α)
    (hM : 1 ≤ maximumSecondMoment n) :
    (max (regularQuadraticTestValue (n+2) α) 0)^2/(2*regularDenominator (n+2) α)=
      referenceSecondWeight n := by
  have hS : 0 ≤ regularQuadraticTestValue (n+2) α := by
    rw [regular_test_value_eq]
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hM)
  rw [max_eq_left hS]
  exact regular_certificate_square_eq hn α hα

theorem eventually_maximumSecondMoment_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ maximumSecondMoment n := by
  filter_upwards [eventually_maximum_mean_sq_ge_one] with n hn
  have hv : 0 ≤ maximumVariance n := variance_nonneg _ _
  rw [maximumVariance_eq_second_sub_mean_sq] at hv
  linarith

/-- The threshold is independent of alpha and of the target ambient space. -/
theorem eventually_regular_certificate_actual :
    ∀ᶠ n : ℕ in atTop, ∀ α : ℝ, 0 < α →
      (max (regularQuadraticTestValue (n+2) α) 0)^2/(2*regularDenominator (n+2) α)=
        chaosEnergy (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) 2 := by
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximumSecondMoment_ge_one] with n hn hM
  intro α hα
  rw [canonical_chaosEnergy_two n hn]
  exact regular_certificate_positive_square_eq hn α hα hM

theorem fixed_cutoff_tail (L : ℝ) (hL : 0 ≤ L) :
    Real.exp (-(Real.sqrt (256*L))^2/16)=Real.exp (-16*L) := by
  rw [Real.sq_sqrt (by positivity)]
  congr 1
  ring

/-- A fully explicit coefficient bound at the frozen cutoff sqrt(256 L).
The scale lower bound is the actual reference-scale bound used later. -/
theorem routing_coefficients_bound (m M α L : ℝ) (hm : 4 ≤ m) (hL : 1 ≤ L)
    (hM0 : 1 ≤ M) (hM : M ≤ 5*L) (hα : 0 < α) (hscale : L/m^2 ≤ α^2) :
    let A := (α^2*(M-1))/(α^4*(m-1)*(m-2)/m)
    A*(2*α*Real.sqrt (256*L)) ≤ 480*L ∧ A*(144*α^2*m) ≤ 2160*L := by
  dsimp only
  let A := (α^2*(M-1))/(α^4*(m-1)*(m-2)/m)
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hm2 : 0 < m-2 := by linarith
  have hden : 0 < (m-1)*(m-2) := mul_pos hm1 hm2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hratio : m^2 ≤ 3*((m-1)*(m-2)) := by nlinarith
  have hid : (A*α^2*m)*((m-1)*(m-2))=m^2*(M-1) := by
    dsimp [A]
    field_simp
    <;> ring
  have hr : A*α^2*m ≤ 15*L := by
    apply (mul_le_mul_iff_right₀ hden).mp
    rw [mul_comm ((m-1)*(m-2)) (A*α^2*m),mul_comm ((m-1)*(m-2)) (15*L)]
    rw [hid]
    have h1 := mul_le_mul_of_nonneg_left (show M-1 ≤ 5*L by linarith) (sq_nonneg m)
    have h2 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 5*L by linarith)
    nlinarith only [h1,h2]
  have hscale' : L ≤ α^2*m^2 := (div_le_iff₀ (sq_pos_of_pos hm0)).mp hscale
  have hT : Real.sqrt (256*L) ≤ 16*α*m := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith [hscale']⟩
  constructor
  · have hh := mul_le_mul_of_nonneg_left hT (show 0 ≤ A*(2*α) by positivity)
    change A*(2*α*Real.sqrt (256*L)) ≤ 480*L
    nlinarith only [hh,hr]
  · change A*(144*α^2*m) ≤ 2160*L
    nlinarith only [hr]

/-- Actual regular second-chaos comparison for every centered equal-row
proxy. The scalar cutoff is fixed and the first-moment loss is not replaced
by any unproved row-payment estimate. -/
theorem equal_row_actual_second_chaos_lower (hn : 2 ≤ n)
    (Z : Fin (n+2) → FSC.Coord d) (α L : ℝ) (hα : 0 < α) (hL : 1 ≤ L)
    (hM0 : 1 ≤ maximumSecondMoment n) (hM : maximumSecondMoment n ≤ 5*L)
    (hscale : L/((n:ℝ)+2)^2 ≤ α^2)
    (hZ : ∀ i,‖Z i‖^2=α^2*(1-1/((n:ℝ)+2))) (hcenter : ∑ i,Z i=0)
    (f : (Fin d → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x => f x i) (standardGaussian (Fin d)))
    (h0 : ∀ᵐ x ∂standardGaussian (Fin d),∀ i,0 ≤ f x i)
    (hs : ∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) :
    referenceSecondWeight n-480*L*proxyLoss Z f α-2160*L*Real.exp (-16*L) ≤ chaosEnergy f 2 := by
  have hn0 : 0 < n := by omega
  have hm : 3 ≤ n+2 := by omega
  have hZ' : ∀ i,‖Z i‖^2=α^2*(1-1/((n+2:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hZ
  have hf2 i : MemLp (fun x => f x i) 2 (standardGaussian (Fin d)) := by
    refine MemLp.of_bound (hf i).aestronglyMeasurable 1 ?_
    filter_upwards [h0,hs] with x hx0 hxsum
    rw [Real.norm_eq_abs,abs_of_nonneg (hx0 i)]
    exact (Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ i)).trans_eq hxsum
  have hp := proxyLoss_nonneg Z α hα hZ' f hf2 h0 hs
  have hraw := equal_row_second_chaos_proxy_lower hm Z α hα hZ' hcenter f hf h0 hs
    (Real.sqrt (256*L)) (Real.sqrt_nonneg _)
  rw [regular_certificate_positive_square_eq hn0 α hα hM0,fixed_cutoff_tail L (by linarith)] at hraw
  have hS : 0 ≤ regularQuadraticTestValue (n+2) α := by
    rw [regular_test_value_eq]
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hM0)
  rw [max_eq_left hS] at hraw
  have hcoef := routing_coefficients_bound ((n:ℝ)+2) (maximumSecondMoment n) α L
    (by exact_mod_cast (show 4 ≤ n+2 by omega)) hL hM0 hM hα hscale
  dsimp only at hcoef
  have hlin := mul_le_mul_of_nonneg_right hcoef.1 hp
  have htail := mul_le_mul_of_nonneg_right hcoef.2 (Real.exp_pos (-16*L)).le
  rw [regular_test_value_eq] at hraw
  unfold regularDenominator at hraw
  simp only [Nat.cast_add,Nat.cast_ofNat] at hraw
  change _ ≤ chaosEnergy f 2
  have he1 : (n:ℝ)+2-1=(n:ℝ)+1 := by ring
  have he2 : (n:ℝ)+2-2=(n:ℝ) := by ring
  nlinarith only [hraw,hlin,htail]

theorem eventually_equal_row_actual_second_chaos_lower :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (Z : Fin (n+2) → FSC.Coord d),
      (∀ i,‖Z i‖^2=(referenceScale n)^2*(1-1/((n:ℝ)+2))) → (∑ i,Z i)=0 →
      ∀ (f : (Fin d → ℝ) → Fin (n+2) → ℝ),
        (∀ i,AEMeasurable (fun x => f x i) (standardGaussian (Fin d))) →
        (∀ᵐ x ∂standardGaussian (Fin d),∀ i,0 ≤ f x i) →
        (∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) →
      referenceSecondWeight n-480*(1+Real.log ((n:ℝ)+2))*proxyLoss Z f (referenceScale n)-
        2160*(1+Real.log ((n:ℝ)+2))*Real.exp (-16*(1+Real.log ((n:ℝ)+2))) ≤ chaosEnergy f 2 := by
  filter_upwards [eventually_ge_atTop (2:ℕ),eventually_maximumSecondMoment_ge_one,
    eventually_maximum_second_moment_log_bound,eventually_reference_scale_bounds] with n hn hM0 hM hscale
  intro d Z hZ hc f hf h0 hs
  have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact equal_row_actual_second_chaos_lower hn Z (referenceScale n) (1+Real.log ((n:ℝ)+2))
    (referenceScale_pos n) (by linarith) hM0 (by linarith) hscale.1 hZ hc f hf h0 hs

end NegativeVotingEqualRowRegularCoefficient
