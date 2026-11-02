import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Coordinate slice derivatives and product-domain smoothness. -/

noncomputable section

open Filter
open scoped Topology

namespace FSC

/-- The derivative assembled from the two scalar coordinate partials. -/
def prodGradient (p q : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  p • ContinuousLinearMap.fst ℝ ℝ ℝ + q • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem prodGradient_apply (p q : ℝ) (h : ℝ × ℝ) :
    prodGradient p q h = p * h.1 + q * h.2 := rfl

private theorem scalar_hasFDerivAt {f : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt f d x) :
    HasFDerivAt f (d • ContinuousLinearMap.id ℝ ℝ) x := by
  convert! hd.hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [mul_comm]

/-- Continuous coordinate partials at the base give the actual product-domain derivative. -/
theorem hasFDerivAt_prod_of_partials {f p q : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hp : ∀ᶠ y in 𝓝 x, HasDerivAt (fun a : ℝ ↦ f (a, y.2)) (p y) y.1)
    (hq : ∀ᶠ y in 𝓝 x, HasDerivAt (fun b : ℝ ↦ f (y.1, b)) (q y) y.2)
    (hcp : ContinuousAt p x) (hcq : ContinuousAt q x) :
    HasFDerivAt f (prodGradient (p x) (q x)) x := by
  have hp' : ∀ᶠ y in 𝓝 x,
      HasFDerivAt (fun a : ℝ ↦ f (a, y.2)) (p y • ContinuousLinearMap.id ℝ ℝ) y.1 :=
    hp.mono fun _ hy ↦ scalar_hasFDerivAt hy
  have hq' : ∀ᶠ y in 𝓝 x,
      HasFDerivAt (fun b : ℝ ↦ f (y.1, b)) (q y • ContinuousLinearMap.id ℝ ℝ) y.2 :=
    hq.mono fun _ hy ↦ scalar_hasFDerivAt hy
  have hc0 : ContinuousAt (fun y : ℝ × ℝ ↦ p y • ContinuousLinearMap.id ℝ ℝ) x :=
    hcp.smul continuousAt_const
  have hc1 : ContinuousAt (fun y : ℝ × ℝ ↦ q y • ContinuousLinearMap.id ℝ ℝ) x :=
    hcq.smul continuousAt_const
  have h := hasStrictFDerivAt_uncurry_coprod (f := fun a b : ℝ ↦ f (a, b))
    (f₁ := fun a b ↦ p (a, b) • ContinuousLinearMap.id ℝ ℝ)
    (f₂ := fun a b ↦ q (a, b) • ContinuousLinearMap.id ℝ ℝ)
    hp' hq' hc0 hc1
  apply h.hasFDerivAt.congr_fderiv
  change (p x • ContinuousLinearMap.id ℝ ℝ).coprod
    (q x • ContinuousLinearMap.id ℝ ℝ) = prodGradient (p x) (q x)
  apply ContinuousLinearMap.ext
  intro z
  simp [prodGradient]

/-- A global consumer convenient for explicit bivariate Gaussian slice formulas. -/
theorem hasFDerivAt_prod_of_partials_global {f p q : ℝ × ℝ → ℝ}
    (hp : ∀ y, HasDerivAt (fun a : ℝ ↦ f (a, y.2)) (p y) y.1)
    (hq : ∀ y, HasDerivAt (fun b : ℝ ↦ f (y.1, b)) (q y) y.2)
    (hcp : Continuous p) (hcq : Continuous q) (x : ℝ × ℝ) :
    HasFDerivAt f (prodGradient (p x) (q x)) x :=
  hasFDerivAt_prod_of_partials (Eventually.of_forall hp) (Eventually.of_forall hq)
    hcp.continuousAt hcq.continuousAt

/-- Continuous partial fields make the bivariate function C1. -/
theorem contDiff_one_prod_of_partials {f p q : ℝ × ℝ → ℝ}
    (hp : ∀ y, HasDerivAt (fun a : ℝ ↦ f (a, y.2)) (p y) y.1)
    (hq : ∀ y, HasDerivAt (fun b : ℝ ↦ f (y.1, b)) (q y) y.2)
    (hcp : Continuous p) (hcq : Continuous q) : ContDiff ℝ 1 f := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ prodGradient (p x) (q x), ?_,
    hasFDerivAt_prod_of_partials_global hp hq hcp hcq⟩
  exact (hcp.smul continuous_const).add (hcq.smul continuous_const)

/-- C1 partial fields make the bivariate function C2. -/
theorem contDiff_two_prod_of_partials {f p q : ℝ × ℝ → ℝ}
    (hp : ∀ y, HasDerivAt (fun a : ℝ ↦ f (a, y.2)) (p y) y.1)
    (hq : ∀ y, HasDerivAt (fun b : ℝ ↦ f (y.1, b)) (q y) y.2)
    (hcp : ContDiff ℝ 1 p) (hcq : ContDiff ℝ 1 q) : ContDiff ℝ 2 f := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ prodGradient (p x) (q x), ?_,
    hasFDerivAt_prod_of_partials_global hp hq hcp.continuous hcq.continuous⟩
  exact (hcp.smul contDiff_const).add (hcq.smul contDiff_const)

end FSC
