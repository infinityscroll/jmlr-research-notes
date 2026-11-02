import GaussianPolynomialHermiteDegree
import GaussianWeightedFacetEnergy

/-! Actual polynomial traces and their restriction to measurable Gaussian face events. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open NegativeVotingProjection NegativeVotingFiniteHermite NegativeVotingPolynomialDegree
open NegativeVotingSmoothingComposition NegativeVotingNormalTrace GaussianFin
open scoped BigOperators ENNReal Classical

namespace NegativeVotingPolynomialFacetTrace

/-- Restriction Hölder with a variable finite exponent, including q=2. -/
theorem set_integral_sq_le_lq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (F : Set X) (q : ℝ) (hq : 2 ≤ q)
    {v : X → ℝ} (hv : MemLp v (ENNReal.ofReal q) μ) :
    (∫ x in F, (v x)^2 ∂μ) ≤
      (μ F).toReal ^ (1-2/q) * (eLpNorm v (ENNReal.ofReal q) μ).toReal ^ 2 := by
  have hq0 : 0 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hexp : 0 ≤ (1/2 : ℝ) - q⁻¹ := by
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq
    norm_num only [invOf_eq_inv, inv_div, div_one] at hh
    linarith
  have hq2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq
  have hv2 : MemLp v 2 (μ.restrict F) := (hv.restrict F).mono_exponent hq2
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq2
    (hv.restrict F).aestronglyMeasurable
  have hb := hh.trans (mul_le_mul'
    (eLpNorm_mono_measure v (Measure.restrict_le_self (μ := μ) (s := F))) le_rfl)
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hq0,
    Measure.restrict_apply_univ, one_div] at hb
  have hfin : eLpNorm v (ENNReal.ofReal q) μ *
      μ F ^ ((1/2 : ℝ) - q⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top hv.eLpNorm_ne_top
      (ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hexp (measure_ne_top μ F)))
  have hr := ENNReal.toReal_mono hfin hb
  rw [eLpNorm_two_eq_sqrt_integral_sq hv2,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow] at hr
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
  rw [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)), mul_pow] at hp
  have he : ((μ F).toReal ^ ((1/2:ℝ)-q⁻¹)) ^ 2 = (μ F).toReal ^ (1-2/q) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1
    field_simp [ne_of_gt hqpos]
  rw [he] at hp
  simpa only [mul_comm] using hp

theorem polynomial_memLp {κ : Type*} [Fintype κ] {k : ℕ}
    {f : (κ → ℝ) → ℝ} (hf : f ∈ polynomialSpace k) : MemLp f 2 (γpi κ) := by
  obtain ⟨c,rfl⟩ := exists_normalized_expansion hf
  exact hermiteSum_memLp _ _

theorem polynomial_continuous {κ : Type*} [Fintype κ] {k : ℕ}
    {f : (κ → ℝ) → ℝ} (hf : f ∈ polynomialSpace k) : Continuous f := by
  obtain ⟨c,rfl⟩ := exists_normalized_expansion hf
  exact hermiteSum_continuous _ _

theorem polynomial_normal_trace_lq {n k : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : f ∈ polynomialSpace k) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ) :
    eLpNorm (fun x => normalLift f (x,a)) (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a) * (τ^k)⁻¹) *
        eLpNorm f 2 (γFin (n+1)) := by
  obtain ⟨c,rfl⟩ := exists_normalized_expansion hf
  apply hermiteSum_normal_trace_lq _ c k _ τ hτ hτ1 a
  intro b hb
  have hh := (mem_lowerModes_iff _ _).mp hb
  omega

theorem polynomial_normal_trace_memLp {n k : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : f ∈ polynomialSpace k) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ) :
    MemLp (fun x => normalLift f (x,a)) (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) := by
  exact (polynomial_normal_trace_lq hf τ hτ hτ1 a).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (polynomial_memLp hf))

/-- Actual face-event trace with no assumed Gaussian spectral representation. -/
theorem polynomial_face_integral_sq {n k : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : f ∈ polynomialSpace k) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (a : ℝ) (F : Set (Fin n → ℝ)) :
    (∫ x in F, normalLift f (x,a)^2 ∂γFin n) ≤
      ((γFin n) F).toReal ^ (1-2/(1+(τ^2)⁻¹)) *
        (Real.sqrt (normalRowSquare τ a) * (τ^k)⁻¹)^2 *
          ∫ x, f x^2 ∂γFin (n+1) := by
  have hq : 2 ≤ 1+(τ^2)⁻¹ := by
    have hsq : 0 < τ^2 := sq_pos_of_pos hτ
    have hs1 : τ^2 ≤ 1 := by nlinarith
    have := one_le_inv₀ hsq |>.mpr hs1
    linarith
  have ht := set_integral_sq_le_lq F _ hq (polynomial_normal_trace_memLp hf τ hτ hτ1 a)
  have hb := polynomial_normal_trace_lq hf τ hτ hτ1 a
  have hf2 : MemLp f 2 (γFin (n+1)) := polynomial_memLp hf
  have hn := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf2.eLpNorm_ne_top) hb
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by positivity)),
    eLpNorm_two_eq_sqrt_integral_sq hf2,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hn
  have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg hn 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hs
  exact ht.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- Finite sums of actual affine products; these include every quadratic and quartic score test. -/
def affineProductSum {κ ι ν : Type*} [Fintype κ] (S : Finset ι) (T : ι → Finset ν)
    (w : ι → ℝ) (l : ι → ν → κ → ℝ) (c : ι → ν → ℝ) (x : κ → ℝ) : ℝ :=
  ∑ i ∈ S, w i * ∏ j ∈ T i, affineFunction (l i j) (c i j) x

theorem affineProductSum_mem {κ ι ν : Type*} [Fintype κ] (S : Finset ι) (T : ι → Finset ν)
    (w : ι → ℝ) (l : ι → ν → κ → ℝ) (c : ι → ν → ℝ)
    (k : ℕ) (hk : ∀ i ∈ S, (T i).card ≤ k) :
    affineProductSum S T w l c ∈ polynomialSpace k := by
  have hh := (polynomialSpace (κ := κ) k).sum_mem (fun i hi =>
    (polynomialSpace k).smul_mem (w i)
      (polynomialSpace_mono (hk i hi) (affine_product_mem (T i) (l i) (c i))))
  convert hh using 1
  ext x
  simp only [affineProductSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Degree-four endpoint with the degree cutoff derived from its affine factors. -/
theorem quartic_affine_product_face_integral_sq {n : ℕ} {ι ν : Type*}
    (S : Finset ι) (T : ι → Finset ν) (w : ι → ℝ)
    (l : ι → ν → Fin (n+1) → ℝ) (c : ι → ν → ℝ)
    (hdegree : ∀ i ∈ S, (T i).card ≤ 4)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ) (F : Set (Fin n → ℝ)) :
    (∫ x in F, normalLift (affineProductSum S T w l c) (x,a)^2 ∂γFin n) ≤
      ((γFin n) F).toReal ^ (1-2/(1+(τ^2)⁻¹)) *
        (Real.sqrt (normalRowSquare τ a) * (τ^4)⁻¹)^2 *
          ∫ x, (affineProductSum S T w l c x)^2 ∂γFin (n+1) :=
  polynomial_face_integral_sq (affineProductSum_mem S T w l c 4 hdegree) τ hτ hτ1 a F

end NegativeVotingPolynomialFacetTrace
