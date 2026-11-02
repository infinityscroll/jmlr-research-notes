import GaussianFanCovarianceEnvelope
import GaussianFanOptimizedValue
import GaussianFanJointInverse

/-! The covariance Hessian of the actual optimized Gaussian value.
The spectral factor, centered offsets, their C1 regularity and the optimized
value identity are all constructed from the stated model hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingOptimizedCovariance
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanJointMass
  NegativeVotingFanJointInverse NegativeVotingFanValue NegativeVotingFanScore
  NegativeVotingFanEnvelope NegativeVotingFanCovarianceEnvelope
  NegativeVotingCovariancePath NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Exact actual optimized-value covariance Hessian. There is no supplied
offset curve, inverse, differential identity or optimization premise. -/
theorem exists_optimized_covariance_hessian
    (B : ι → FSC.Coord d) (p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    ∃ h₀ : centeredGauge ι, mass B h₀ = p ∧
    ∃ S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d,
      S 0 = ContinuousLinearMap.id ℝ (FSC.Coord d) ∧
      (∀ t, (S t).toLinearMap.IsSymmetric) ∧
      (∀ t x, 0 ≤ inner ℝ (S t x) x) ∧
      (∀ᶠ t : ℝ in 𝓝 0, (S t).comp (S t) =
        ContinuousLinearMap.id ℝ (FSC.Coord d) + t • H) ∧
      ContDiffAt ℝ ⊤ S 0 ∧
      HasDerivAt (deriv (fun t : ℝ => optimizedValue (rowsOfOperator B (S t)) p))
        (covarianceHessianValue B h₀ H) 0 := by
  obtain ⟨b, ⟨hb,hbm⟩, _⟩ :=
    existsUnique_offsets_with_prescribed_masses B σ hσ hlower p hp hs
  let h₀ : centeredGauge ι := ⟨b,hb⟩
  obtain ⟨S,hS0,hSsym,hSpos,hSsquare,hS1,hS2,hSsmooth,hSneighborhood⟩ :=
    exists_smooth_local_covariance_factor H hH
  let R : ℝ → ι → FSC.Coord d := fun t => rowsOfOperator B (S t)
  have hR0 : R 0 = B := by simp [R,hS0]
  have hR : ContDiffAt ℝ 1 R 0 :=
    (rowsOfOperator B).contDiff.contDiffAt.comp 0 (hSsmooth.of_le le_top)
  have hlower0 : CenteredSingularLowerBound (R 0) σ := by rwa [hR0]
  obtain ⟨a,ha0,haC1,hacenter,ham⟩ :=
    exists_C1_offsets_along_rows R h₀ σ hσ hlower0 hR
  have hm : ∀ᶠ t : ℝ in 𝓝 0, mass (R t) (a t) = p := by
    simpa only [hR0,h₀,hbm] using ham
  have ha : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt a (deriv a t) t := by
    filter_upwards [haC1.eventually (by decide)] with t ht
    exact ht.differentiableAt_one.hasDerivAt
  have hd := hasDerivAt_deriv_covariance_potential_canonical B b p σ hσ hlower
    H hH S a hS0 ha0 hS1 hS2 hSneighborhood ha hm
  have hparam : ContinuousAt (fun t : ℝ => (R t,a t)) 0 :=
    hR.continuousAt.prodMk haC1.continuousAt
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, CenteredSingularLowerBound (R t) (σ/2) :=
    hparam.tendsto.eventually (by
      simpa only [hR0,ha0,h₀] using
        eventually_centeredSingularLowerBound B b σ hσ hlower)
  have heq : (fun t : ℝ => optimizedValue (R t) p) =ᶠ[𝓝 0]
      (fun t : ℝ => potential (R t) p (a t)) := by
    filter_upwards [hm,hnear] with t hmt hlt
    exact optimizedValue_eq_of_mass (R t) p (σ/2) (by positivity) hlt
      hp hs ⟨a t,hacenter t⟩ hmt
  refine ⟨h₀,hbm,S,hS0,hSsym,hSpos,hSsquare,hSsmooth,?_⟩
  exact hd.congr_of_eventuallyEq heq.deriv

end NegativeVotingOptimizedCovariance
