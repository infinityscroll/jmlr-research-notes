import GaussianPolyhedronEhrhard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Filter
open scoped Topology
open OAI.GaussianPropeller.Quantile

namespace NegativeVotingEhrhard

/-- Differentiating the Gaussian inverse-CDF transform twice. This calculus
lemma exposes the exact density factor needed for the covariance correction. -/
theorem quantile_curve_second_derivative (p g : ℝ → ℝ) (c : ℝ)
    (hp : ∀ t, p t ∈ Ioo (0 : ℝ) 1)
    (hdp : ∀ t, HasDerivAt p (g t) t) (hdg : HasDerivAt g c 0) :
    HasDerivAt (fun t => (φ (q (p t)))⁻¹ * g t)
      ((φ (q (p 0)))⁻¹ * c + q (p 0) * ((φ (q (p 0)))⁻¹)^2 * (g 0)^2) 0 := by
  have hq := (hasDerivAt_q (hp 0)).comp 0 (hdp 0)
  have hφ := (hasDerivAt_φ (q (p 0))).comp 0 hq
  have hi := hφ.inv (φ_pos (q (p 0))).ne'
  convert hi.mul hdg using 1
  · rfl
  · simp only [Function.comp_def, Pi.inv_apply]
    field_simp [(φ_pos (q (p 0))).ne']
    ring

/-- Exact scalar curvature consequence of genuine Ehrhard concavity. The
conclusion is written without division, with the strictly positive Gaussian
density multiplying the second derivative. -/
theorem ehrhard_curve_curvature (p g : ℝ → ℝ) (c : ℝ)
    (hp : ∀ t, p t ∈ Ioo (0 : ℝ) 1)
    (hdp : ∀ t, HasDerivAt p (g t) t) (hdg : HasDerivAt g c 0)
    (hconc : ConcaveOn ℝ univ (fun t => q (p t))) :
    φ (q (p 0)) * c + q (p 0) * (g 0)^2 ≤ 0 := by
  have hq (t : ℝ) : HasDerivAt (fun s => q (p s)) ((φ (q (p t)))⁻¹ * g t) t :=
    (hasDerivAt_q (hp t)).comp t (hdp t)
  have hanti : Antitone (deriv (fun t => q (p t))) := by
    intro s t hst
    exact hconc.antitoneOn_deriv (fun u _ => (hq u).differentiableAt)
      (mem_univ s) (mem_univ t) hst
  have hderiv : deriv (fun t => q (p t)) = (fun t => (φ (q (p t)))⁻¹ * g t) :=
    funext (fun t => (hq t).deriv)
  rw [hderiv] at hanti
  have hh := hanti.deriv_nonpos (x := (0 : ℝ))
  rw [(quantile_curve_second_derivative p g c hp hdp hdg).deriv] at hh
  have hφ : φ (q (p 0)) ≠ 0 := (φ_pos (q (p 0))).ne'
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (φ (q (p 0)))) hh
  have heq : (φ (q (p 0))) ^ 2 *
      ((φ (q (p 0)))⁻¹ * c + q (p 0) * ((φ (q (p 0)))⁻¹)^2 * (g 0)^2) =
      φ (q (p 0)) * c + q (p 0) * (g 0)^2 := by
    field_simp
  rwa [heq] at hm

end NegativeVotingEhrhard
