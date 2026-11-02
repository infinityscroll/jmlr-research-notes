import GaussianFanGradientDerivative
import GaussianFanCentroidBoundary

/-! Actual envelope derivatives along prescribed-mass Gaussian fan paths.
Only the row path needs a second derivative: offset second derivatives cancel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace NegativeVotingFanEnvelope
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanGradient
  NegativeVotingFanHessian NegativeVotingCapTail NegativeVotingFacetDegree
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

abbrev Rows (d : ℕ) (ι : Type*) := ι → FSC.Coord d

def rowLift : Rows d ι →L[ℝ] Parameters d ι :=
  (ContinuousLinearMap.id ℝ (Rows d ι)).prod (0 : Rows d ι →L[ℝ] (ι → ℝ))

@[simp] theorem rowLift_apply (D : Rows d ι) : rowLift D = (D,0) := rfl

def offsetFunctional (p : ι → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∑ i, p i • (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd ℝ (Rows d ι) (ι → ℝ))

@[simp] theorem offsetFunctional_apply (p : ι → ℝ) (u : Parameters d ι) :
    offsetFunctional p u = ∑ i, p i * u.2 i := by
  simp [offsetFunctional]

theorem hasFDerivAt_potential_joint (B : Rows d ι) (h p : ι → ℝ)
    (hB : Function.Injective B) :
    HasFDerivAt (fun q : Parameters d ι => potential q.1 p q.2)
      (jointDerivative B h - offsetFunctional p) (B,h) := by
  have hd := (hasFDerivAt_expectedMax_joint B hB h).sub
    (offsetFunctional (d := d) p).hasFDerivAt
  change HasFDerivAt (fun q : Parameters d ι => expectedMax q.1 q.2 - offsetFunctional p q)
    (jointDerivative B h - offsetFunctional p) (B,h) at hd
  simpa only [potential, offsetFunctional_apply] using hd

/-- At the actual prescribed masses the first derivative contains no offset term. -/
theorem potential_derivative_at_prescribed_mass (B : Rows d ι) (h p : ι → ℝ)
    (hm : mass B h = p) (u : Parameters d ι) :
    (jointDerivative B h - offsetFunctional (d := d) p : Parameters d ι →L[ℝ] ℝ) u = jointDerivative B h (u.1,0) := by
  rw [ContinuousLinearMap.sub_apply, offsetFunctional_apply,
    jointDerivative_apply, jointDerivative_apply]
  simp [hm, Finset.sum_add_distrib]

/-- The actual mass-preserving path annihilates every pure-offset Hessian test. -/
theorem hessian_offset_zero_of_mass_path (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (q : ℝ → Parameters d ι) (u : Parameters d ι)
    (hq0 : q 0 = (B,h)) (hq : HasDerivAt q u 0)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (q t).1 (q t).2 = p) (k : ι → ℝ) :
    jointHessian B h u (0,k) = 0 := by
  have hd : HasFDerivAt (fun z : Parameters d ι => jointDerivative z.1 z.2)
      (jointHessian B h) (q 0) := by
    simpa only [hq0] using hasFDerivAt_jointGradient B h σ hσ hlower
  have hp := (hd.comp_hasDerivAt 0 hq).clm_apply (hasDerivAt_const (0:ℝ) (0,k))
  have hp' : HasDerivAt (fun t : ℝ => jointDerivative (q t).1 (q t).2 (0,k))
      (jointHessian B h u (0,k)) 0 := by simpa using hp
  have hz : HasDerivAt (fun t : ℝ => jointDerivative (q t).1 (q t).2 (0,k)) 0 0 := by
    apply (hasDerivAt_const (0:ℝ) (∑ i, p i*k i)).congr_of_eventuallyEq
    filter_upwards [hm] with t ht
    simp [jointDerivative_apply, ht]
  exact hp'.unique hz

/-- The mass constraint turns the row-only second derivative into the full
square-facet form along the same single offset path. -/
theorem hessian_row_eq_quadratic_of_mass_path (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (q : ℝ → Parameters d ι) (u : Parameters d ι)
    (hq0 : q 0 = (B,h)) (hq : HasDerivAt q u 0)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (q t).1 (q t).2 = p) :
    jointHessian B h u (u.1,0) = quadraticForm B h u.1 u.2 := by
  have hz := hessian_offset_zero_of_mass_path B h p σ hσ hlower q u hq0 hq hm u.2
  have he : (u.1, (0 : ι → ℝ)) + (0,u.2) = u := by ext <;> simp
  have hs := (jointHessian B h u).map_add (u.1,0) (0,u.2)
  rw [he, hz, add_zero] at hs
  rw [← hs, jointHessian_apply B h σ hσ hlower]
  exact mixedForm_self B u.1 h u.2

/-- Actual second envelope derivative. Local prescribed masses and first
path derivatives suffice for offsets; only the row velocity is differentiated. -/
theorem hasDerivAt_deriv_potential_path (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (q q' : ℝ → Parameters d ι) (A : Rows d ι)
    (hq0 : q 0 = (B,h))
    (hq : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt q (q' t) t)
    (hm : ∀ᶠ t : ℝ in 𝓝 0, mass (q t).1 (q t).2 = p)
    (hrows : HasDerivAt (fun t : ℝ => (q' t).1) A 0) :
    HasDerivAt (deriv (fun t : ℝ => potential (q t).1 p (q t).2))
      (quadraticForm B h (q' 0).1 (q' 0).2 + jointDerivative B h (A,0)) 0 := by
  have hq_at : HasDerivAt q (q' 0) 0 := hq.self_of_nhds
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, Function.Injective (q t).1 :=
    hq_at.continuousAt.tendsto.eventually (by
      simpa only [hq0] using eventually_injective_rows B hB h)
  have heq : deriv (fun t : ℝ => potential (q t).1 p (q t).2) =ᶠ[𝓝 0]
      (fun t => jointDerivative (q t).1 (q t).2 ((q' t).1,0)) := by
    filter_upwards [hq, hm, hnear] with t ht hmt hBt
    have hd := (hasFDerivAt_potential_joint (q t).1 (q t).2 p hBt).comp_hasDerivAt t ht
    exact hd.deriv.trans (potential_derivative_at_prescribed_mass (q t).1 (q t).2 p hmt (q' t))
  have hd : HasFDerivAt (fun z : Parameters d ι => jointDerivative z.1 z.2)
      (jointHessian B h) (q 0) := by
    simpa only [hq0] using hasFDerivAt_jointGradient B h σ hσ hlower
  have hr : HasDerivAt (fun t : ℝ => ((q' t).1,(0 : ι → ℝ))) (A,0) 0 :=
    rowLift.hasFDerivAt.comp_hasDerivAt 0 hrows
  have hg := (hd.comp_hasDerivAt 0 hq_at).clm_apply hr
  have hh : HasDerivAt
      (fun t : ℝ => jointDerivative (q t).1 (q t).2 ((q' t).1,0))
      (quadraticForm B h (q' 0).1 (q' 0).2 + jointDerivative B h (A,0)) 0 := by
    simpa only [Function.comp_def, hq0,
      hessian_row_eq_quadratic_of_mass_path B h p σ hσ hlower q (q' 0) hq0 hq_at hm]
      using hg
  exact hh.congr_of_eventuallyEq heq

end NegativeVotingFanEnvelope
