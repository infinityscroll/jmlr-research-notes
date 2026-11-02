import GaussianLowModeProjection

/-!
Actual signed OU residual moments.  The affine-fan input below is measured in
its genuine Gaussian L² norm.  This does not assert the stronger score-distance
Lipschitz estimate furnished in the paper by boundary trace and path integration.
All label estimates are componentwise, so no reverse mixed-norm inequality is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open NegativeVotingHypercontractivity NegativeVotingSmoothingComposition
open NegativeVotingProjection NegativeVotingAffine OAI.MinUncut.GaussianHermite
open scoped ENNReal BigOperators

namespace NegativeVotingOUResidualMoment

theorem gaussian_neg_measurePreserving (n : ℕ) :
    MeasurePreserving (fun x : Fin n → ℝ => -x) (γFin n) (γFin n) := by
  have h1 : MeasurePreserving (fun x : ℝ => -x) Gaussian1D.γ Gaussian1D.γ := by
    refine ⟨measurable_neg, ?_⟩
    simpa [Gaussian1D.γ] using (gaussianReal_map_neg (μ := 0) (v := 1))
  exact measurePreserving_pi _ _ (fun _ => h1)

/-- Negative correlation is output reflection, exactly at raw integral level. -/
theorem gaussianAverage_neg (ρ : ℝ) (f : (Fin n → ℝ) → ℝ) :
    gaussianAverage (-ρ) f = fun x => gaussianAverage ρ f (-x) := by
  funext x
  unfold gaussianAverage
  congr 1
  funext y
  congr 1
  funext j
  simp only [Pi.neg_apply, neg_sq]
  ring

theorem gaussianAverage_neg_eLpNorm {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) (p : ℝ≥0∞) :
    eLpNorm (gaussianAverage (-ρ) f) p (γFin n) =
      eLpNorm (gaussianAverage ρ f) p (γFin n) := by
  rw [gaussianAverage_neg]
  exact eLpNorm_comp_measurePreserving
    (gaussianAverage_memLp_two hρ hρ1 f hf).aestronglyMeasurable
    (gaussian_neg_measurePreserving n)

theorem highModes_sub (k : ℕ) (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (γFin n)) (hg : MemLp g 2 (γFin n)) :
    highModes k (f - g) = highModes k f - highModes k g := by
  classical
  have hc (a : Fin n → ℕ) : coeff (f - g) a = coeff f a - coeff g a :=
    coeff_sub hf hg a
  funext x
  simp only [highModes, removeModes, projectModes, Pi.sub_apply, hc,
    sub_mul, Finset.sum_sub_distrib]
  ring

/-- Linearity of the genuine raw OU integral, valid AE for arbitrary L² inputs. -/
theorem gaussianAverage_sub_ae {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f g : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n))
    (hg : MemLp g 2 (γFin n)) :
    gaussianAverage ρ (f - g) =ᵐ[γFin n] gaussianAverage ρ f - gaussianAverage ρ g := by
  let t := -Real.log ρ
  have ht : 0 ≤ t := (neg_pos.mpr (Real.log_neg hρ hρ1)).le
  have hf' := (ouSemigroupFinLp_coeFn_ae t ht (hf.toLp f)).trans
    (ouSemigroupFin_ae_eq_of_aeEq t ht hf.coeFn_toLp)
  have hg' := (ouSemigroupFinLp_coeFn_ae t ht (hg.toLp g)).trans
    (ouSemigroupFin_ae_eq_of_aeEq t ht hg.coeFn_toLp)
  have hsub : ((hf.toLp f - hg.toLp g : Lp ℝ 2 (γFin n)) : (Fin n → ℝ) → ℝ)
      =ᵐ[γFin n] f - g :=
    (Lp.coeFn_sub _ _).trans (hf.coeFn_toLp.sub hg.coeFn_toLp)
  have hs := (ouSemigroupFinLp_coeFn_ae t ht (hf.toLp f - hg.toLp g)).trans
    (ouSemigroupFin_ae_eq_of_aeEq t ht hsub)
  have hout := (Lp.coeFn_sub (ouSemigroupFinLp t (hf.toLp f))
    (ouSemigroupFinLp t (hg.toLp g))).trans (hf'.sub hg')
  rw [map_sub] at hs
  simpa only [gaussianAverage_eq_ouSemigroupFin ρ hρ, t] using hs.symm.trans hout

theorem gaussianAverage_neg_sub_ae {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f g : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n))
    (hg : MemLp g 2 (γFin n)) :
    gaussianAverage (-ρ) (f - g) =ᵐ[γFin n]
      gaussianAverage (-ρ) f - gaussianAverage (-ρ) g := by
  have h := (gaussian_neg_measurePreserving n).quasiMeasurePreserving.ae
    (gaussianAverage_sub_ae hρ hρ1 f g hf hg)
  simp only [gaussianAverage_neg]
  exact h

/-- The high-mode difference really is the difference of the two smoothed
potentials.  No assumed spectral representative or factorization occurs. -/
theorem negative_highModes_difference_ae {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (k : ℕ) (f g : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n))
    (hg : MemLp g 2 (γFin n)) :
    gaussianAverage (-ρ) (highModes k (f - g)) =ᵐ[γFin n]
      gaussianAverage (-ρ) (highModes k f) - gaussianAverage (-ρ) (highModes k g) := by
  rw [highModes_sub k f g hf hg]
  exact gaussianAverage_neg_sub_ae hρ hρ1 _ _ (highModes_memLp k f hf) (highModes_memLp k g hg)

/-- High-mode decay is preserved at the actual negative voting correlation. -/
theorem negative_highModes_lq_bound {τ σ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    eLpNorm (gaussianAverage (-(τ * σ)) (highModes k f))
      (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
        ENNReal.ofReal (σ ^ k) * eLpNorm f 2 (γFin n) := by
  have hprod : τ * σ < 1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  rw [gaussianAverage_neg_eLpNorm (mul_pos hτ hσ) hprod _ (highModes_memLp k f hf)]
  exact (gaussianAverage_highChaos_lq_bound hτ hτ1 hσ hσ1 _
    (highModes_memLp k f hf) k (highModes_coeff_vanish k f hf)).trans
      (mul_le_mul' le_rfl (highModes_eLpNorm_le k f hf))

/-- Literal normalized residual at r=(τ σ)².  The second input already has
Hermite degrees at least three, as does the odd smoothed input in the paper. -/
def normalizedResidual (τ σ : ℝ) (f u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (gaussianAverage (-((τ * σ) ^ 2)) (highModes 2 f) x -
    gaussianAverage (τ * σ) u x) / (τ * σ) ^ 2

/-- The exact generic bound has an L² difference input, not a score distance.
It supplies r/τ² and sqrt(r)/τ³ after normalization, without a spurious 1/r. -/
theorem normalizedResidual_lq_bound {τ σ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f u : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n))
    (hu : MemLp u 2 (γFin n))
    (hu3 : ∀ a, degree a < 3 → coeff u a = 0) :
    MemLp (normalizedResidual τ σ f u) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ∧
    eLpNorm (normalizedResidual τ σ f u) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (σ ^ 2) * eLpNorm f 2 (γFin n) +
        ENNReal.ofReal (σ / τ ^ 2) * eLpNorm u 2 (γFin n) := by
  let p : ℝ≥0∞ := ENNReal.ofReal (1 + (τ ^ 2)⁻¹)
  have hp : 1 ≤ p := by
    have hh : (1 : ℝ) ≤ 1 + (τ ^ 2)⁻¹ := by
      have : 0 ≤ (τ ^ 2)⁻¹ := by positivity
      linarith
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hs : 0 < τ * σ ^ 2 := mul_pos hτ (sq_pos_of_pos hσ)
  have hs1 : τ * σ ^ 2 < 1 := by
    have hsq : σ ^ 2 < 1 := by nlinarith
    exact (mul_lt_mul_of_pos_left hsq hτ).trans (by simpa using hτ1)
  have hfq := negative_highModes_lq_bound hτ hτ1 hs hs1 2 f hf
  have hfactor : τ * (τ * σ ^ 2) = (τ * σ) ^ 2 := by ring
  rw [hfactor] at hfq
  have huq := gaussianAverage_highChaos_lq_bound hτ hτ1 hσ hσ1 u hu 3 hu3
  have hfm : MemLp (gaussianAverage (-((τ * σ) ^ 2)) (highModes 2 f)) p (γFin n) :=
    hfq.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  have hum : MemLp (gaussianAverage (τ * σ) u) p (γFin n) :=
    huq.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu)
  have hm := (hfm.sub hum).const_mul ((τ * σ) ^ 2)⁻¹
  have heq : normalizedResidual τ σ f u =
      ((τ * σ) ^ 2)⁻¹ • (fun x =>
        gaussianAverage (-((τ * σ) ^ 2)) (highModes 2 f) x - gaussianAverage (τ * σ) u x) := by
    funext x
    simp only [normalizedResidual, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨by simpa only [heq, Pi.smul_def, smul_eq_mul, Pi.sub_apply, p] using hm, ?_⟩
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hadd := eLpNorm_sub_le (f := gaussianAverage (-((τ * σ) ^ 2)) (highModes 2 f))
    (g := gaussianAverage (τ * σ) u) (μ := γFin n) hp
  refine (mul_le_mul' le_rfl (hadd.trans (add_le_add hfq huq))).trans_eq ?_
  rw [mul_add, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _))]
  have ha : ((τ * σ) ^ 2)⁻¹ * (τ * σ ^ 2) ^ 2 = σ ^ 2 := by
    field_simp [ne_of_gt hτ, ne_of_gt hσ]
  have hb : ((τ * σ) ^ 2)⁻¹ * σ ^ 3 = σ / τ ^ 2 := by
    field_simp [ne_of_gt hτ, ne_of_gt hσ]
  rw [ha, hb]

/-- Componentwise hypercontractivity gives the stronger ℓ²(Lq) norm.  This
is not an inference from an Lq(ℓ²) bound. -/
theorem sum_gaussianAverage_lq_norm_sq_le {ι : Type*} [Fintype ι] {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (f : ι → (Fin n → ℝ) → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (γFin n)) :
    ∑ i, (eLpNorm (gaussianAverage τ (f i))
      (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n)).toReal ^ 2 ≤
        ∑ i, (eLpNorm (f i) 2 (γFin n)).toReal ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  have h := memLp_gaussian_average_l2_to_lq τ hτ hτ1 (f i) (hf i)
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (ne_of_lt (hf i)) h) 2

/-- The actual residual has a labelwise squared-norm bound with no alphabet
factor.  Obtaining score-distance control of the first input is a separate
geometric boundary/path theorem, not a premise hidden in this endpoint. -/
theorem sum_normalizedResidual_lq_norm_sq_le {ι : Type*} [Fintype ι]
    {τ σ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f u : ι → (Fin n → ℝ) → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (γFin n)) (hu : ∀ i, MemLp (u i) 2 (γFin n))
    (hu3 : ∀ i a, degree a < 3 → coeff (u i) a = 0) :
    ∑ i, (eLpNorm (normalizedResidual τ σ (f i) (u i))
      (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n)).toReal ^ 2 ≤
      2 * σ ^ 4 * ∑ i, (eLpNorm (f i) 2 (γFin n)).toReal ^ 2 +
        2 * (σ / τ ^ 2) ^ 2 * ∑ i, (eLpNorm (u i) 2 (γFin n)).toReal ^ 2 := by
  have hi (i : ι) :
      (eLpNorm (normalizedResidual τ σ (f i) (u i))
        (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n)).toReal ^ 2 ≤
        2 * σ ^ 4 * (eLpNorm (f i) 2 (γFin n)).toReal ^ 2 +
          2 * (σ / τ ^ 2) ^ 2 * (eLpNorm (u i) 2 (γFin n)).toReal ^ 2 := by
    have h := (normalizedResidual_lq_bound hτ hτ1 hσ hσ1 (f i) (u i)
      (hf i) (hu i) (hu3 i)).2
    have hfin : ENNReal.ofReal (σ ^ 2) * eLpNorm (f i) 2 (γFin n) +
        ENNReal.ofReal (σ / τ ^ 2) * eLpNorm (u i) 2 (γFin n) ≠ ∞ := by
      exact ne_of_lt (ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf i),
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu i)⟩)
    have hr := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_add
      (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf i)))
      (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu i))), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (div_nonneg hσ.le (sq_nonneg _))] at hr
    have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg hr 2
    refine (hs.trans (add_sq_le (a := σ ^ 2 * (eLpNorm (f i) 2 (γFin n)).toReal)
      (b := (σ / τ ^ 2) * (eLpNorm (u i) 2 (γFin n)).toReal))).trans_eq ?_
    ring
  calc
    _ ≤ ∑ i, (2 * σ ^ 4 * (eLpNorm (f i) 2 (γFin n)).toReal ^ 2 +
        2 * (σ / τ ^ 2) ^ 2 * (eLpNorm (u i) 2 (γFin n)).toReal ^ 2) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end NegativeVotingOUResidualMoment
