import NegativeVoting.GaussianSpectral
import NegativeVoting.GaussianCentroid

/-!
# Actual signed Gaussian comparison with the retained centroid square

The identities below are derived from the concrete Hermite basis and Gaussian
noise integral. They do not prove the geometric cap estimate or the main simplex
theorem. In the affine application `f` is the actual rule and `g` is its affine
reference; their centroid matrices need not agree.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite NegativeVotingModern
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingAffine

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

def difference (f g : (κ → ℝ) → ι → ℝ) : (κ → ℝ) → ι → ℝ :=
  fun x i => f x i - g x i

def chaosCrossEnergy (f g : (κ → ℝ) → ι → ℝ) (k : ℕ) : ℝ :=
  ∑' a : {a : κ → ℕ // degree a = k},
    ∑ i, coeff (fun x => f x i) a.1 * coeff (fun x => g x i) a.1

theorem coeff_sub {F G : (κ → ℝ) → ℝ}
    (hF : MemLp F 2 (γpi κ)) (hG : MemLp G 2 (γpi κ)) (a : κ → ℕ) :
    coeff (fun x => F x - G x) a = coeff F a - coeff G a := by
  unfold coeff
  simp_rw [mul_sub]
  exact integral_sub ((memLp_psi a).integrable_mul hF)
    ((memLp_psi a).integrable_mul hG)

theorem coefficient_cross_summable {F G : (κ → ℝ) → ℝ}
    (hF : MemLp F 2 (γpi κ)) (hG : MemLp G 2 (γpi κ)) :
    Summable (fun a : κ → ℕ => coeff F a * coeff G a) := by
  have h := productHermiteBasis.summable_inner_mul_inner (hF.toLp F) (hG.toLp G)
  apply h.congr
  intro a
  rw [real_inner_comm, hermite_basis_coefficient hF, hermite_basis_coefficient hG]

theorem label_cross_summable (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γpi κ))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γpi κ)) :
    Summable (fun a : κ → ℕ => ∑ i,
      coeff (fun x => f x i) a * coeff (fun x => g x i) a) := by
  exact summable_sum (fun i _ => coefficient_cross_summable (hf i) (hg i))

theorem chaosCrossEnergy_summable (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γpi κ))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γpi κ)) :
    Summable (chaosCrossEnergy f g) := by
  have h := ((label_cross_summable f g hf hg).hasSum.tsum_fiberwise degree).summable
  change Summable (fun k : ℕ => ∑' a : {a : κ → ℕ // degree a = k},
    ∑ i, coeff (fun x => f x i) a.1 * coeff (fun x => g x i) a.1) at h
  exact h

/-- Exact quadratic polarization in each actual Hermite degree. -/
theorem chaosEnergy_difference_identity (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γpi κ))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γpi κ)) (k : ℕ) :
    chaosEnergy f k - chaosEnergy g k =
      2 * chaosCrossEnergy (difference f g) g k + chaosEnergy (difference f g) k := by
  have hv (i : ι) : MemLp (fun x => difference f g x i) 2 (γpi κ) := (hf i).sub (hg i)
  have hE (F : (κ → ℝ) → ι → ℝ)
      (hF : ∀ i, MemLp (fun x => F x i) 2 (γpi κ)) :
      Summable (fun a : {a : κ → ℕ // degree a = k} => labelCoefficientEnergy F a.1) := by
    have hs := label_cross_summable F F hF hF
    have ht := hs.comp_injective (show Function.Injective
      (fun a : {a : κ → ℕ // degree a = k} => a.1) from Subtype.val_injective)
    change Summable (fun a : {a : κ → ℕ // degree a = k} =>
      ∑ i, coeff (fun x => F x i) a.1 * coeff (fun x => F x i) a.1) at ht
    simpa only [labelCoefficientEnergy, pow_two] using ht
  have hc := (label_cross_summable (difference f g) g hv hg).comp_injective
    (show Function.Injective (fun a : {a : κ → ℕ // degree a = k} => a.1) from
      Subtype.val_injective)
  change Summable (fun a : {a : κ → ℕ // degree a = k} =>
    ∑ i, coeff (fun x => difference f g x i) a.1 * coeff (fun x => g x i) a.1) at hc
  unfold chaosEnergy chaosCrossEnergy
  rw [← (hE f hf).tsum_sub (hE g hg), ← tsum_mul_left,
    ← (hc.mul_left 2).tsum_add (hE (difference f g) hv)]
  apply tsum_congr
  intro a
  simp only [labelCoefficientEnergy, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show coeff (fun x => difference f g x i) a.1 =
      coeff (fun x => f x i) a.1 - coeff (fun x => g x i) a.1 from coeff_sub (hf i) (hg i) a.1]
  ring

theorem signed_series_summable (A : ℕ → ℝ) (hA : Summable A)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) : Summable (fun k => ρ ^ k * A k) := by
  apply Summable.of_norm_bounded hA.norm
  intro k
  rw [norm_mul, Real.norm_eq_abs, abs_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg ρ) hρ)

def signedCrossTail (r : ℝ) (f g : (κ → ℝ) → ι → ℝ) : ℝ :=
  ∑' k : ℕ, (-r) ^ (k + 2) * chaosCrossEnergy f g (k + 2)

def evenResidual (r : ℝ) (v : (κ → ℝ) → ι → ℝ) : ℝ :=
  r ^ 2 * ∑' k : ℕ, r ^ (2 * k) * chaosEnergy v (2 * k + 2)

def oddResidual (r : ℝ) (v : (κ → ℝ) → ι → ℝ) : ℝ :=
  r ^ 3 * ∑' k : ℕ, r ^ (2 * k) * chaosEnergy v (2 * k + 3)

theorem evenResidual_nonneg (r : ℝ) (hr : 0 ≤ r) (v : (κ → ℝ) → ι → ℝ) :
    0 ≤ evenResidual r v :=
  mul_nonneg (sq_nonneg _) (tsum_nonneg (fun _ =>
    mul_nonneg (pow_nonneg hr _) (chaosEnergy_nonneg v _)))

theorem oddResidual_nonneg (r : ℝ) (hr : 0 ≤ r) (v : (κ → ℝ) → ι → ℝ) :
    0 ≤ oddResidual r v :=
  mul_nonneg (pow_nonneg hr _) (tsum_nonneg (fun _ =>
    mul_nonneg (pow_nonneg hr _) (chaosEnergy_nonneg v _)))

/-- The complete residual tail retains its even positive and odd negative signs. -/
theorem signed_tail_even_odd (r : ℝ) (hr : |r| ≤ 1)
    (v : (κ → ℝ) → ι → ℝ) (hv : Summable (chaosEnergy v)) :
    (∑' k : ℕ, (-r) ^ (k + 2) * chaosEnergy v (k + 2)) =
      evenResidual r v - oddResidual r v := by
  have hs := hv.comp_injective
    (show Function.Injective (fun k : ℕ => k + 2) from fun _ _ h => Nat.add_right_cancel h)
  have he := NegativeVoting.negative_chaos_series_even_odd
    (fun k => chaosEnergy v (k + 2)) (fun _ => chaosEnergy_nonneg v _) hs r hr
  calc
    _ = r ^ 2 * ∑' k : ℕ, (-r) ^ k * chaosEnergy v (k + 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [pow_add]
      ring
    _ = _ := by
      rw [he]
      unfold evenResidual oddResidual
      have ho : (∑' k : ℕ, r ^ (2 * k + 1) * chaosEnergy v (2 * k + 1 + 2)) =
          r * ∑' k : ℕ, r ^ (2 * k) * chaosEnergy v (2 * k + 3) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro k
        rw [pow_add, pow_one]
        rw [show 2 * k + 1 + 2 = 2 * k + 3 by omega]
        ring
      rw [ho]
      ring

/-- Actual Gaussian noise spectral expansion for measurable L2 components. -/
theorem actual_noise_spectral (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) :
    NegativeVoting.gaussianNoiseStability ρ f = ∑' k, ρ ^ k * chaosEnergy f k := by
  have hnonneg : 0 ≤ 1 - ρ ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one ρ).mpr hρ)
  have hρs : ρ ^ 2 + (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hnonneg]
    ring
  exact (gaussian_label_chaos_hasSum ρ (Real.sqrt (1 - ρ ^ 2)) hρs f hf hf2).tsum_eq.symm

theorem signed_series_split_two (A : ℕ → ℝ) (hA : Summable A)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    (∑' k, ρ ^ k * A k) = A 0 + ρ * A 1 + ∑' k, ρ ^ (k + 2) * A (k + 2) := by
  have h := (signed_series_summable A hA ρ hρ).sum_add_tsum_nat_add 2
  simpa [Finset.sum_range_succ, pow_zero, pow_one, add_assoc] using h.symm

theorem signed_tail_polarization (r : ℝ) (hr : |r| ≤ 1)
    (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hg : ∀ i, Measurable (fun x => g x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ))
    (hg2 : ∀ i, MemLp (fun x => g x i) 2 (γpi κ)) :
    (∑' k, (-r) ^ (k + 2) * chaosEnergy f (k + 2)) -
      (∑' k, (-r) ^ (k + 2) * chaosEnergy g (k + 2)) =
      2 * signedCrossTail r (difference f g) g +
        (∑' k, (-r) ^ (k + 2) * chaosEnergy (difference f g) (k + 2)) := by
  have hv (i : ι) : Measurable (fun x => difference f g x i) := (hf i).sub (hg i)
  have hv2 (i : ι) : MemLp (fun x => difference f g x i) 2 (γpi κ) := (hf2 i).sub (hg2 i)
  have hneg : |-r| ≤ 1 := by simpa using hr
  have hshift (A : ℕ → ℝ) (hA : Summable A) :
      Summable (fun k => (-r) ^ (k + 2) * A (k + 2)) := by
    exact (signed_series_summable A hA (-r) hneg).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hF := hshift _ (chaos_energy_hasSum f hf hf2).summable
  have hG := hshift _ (chaos_energy_hasSum g hg hg2).summable
  have hV := hshift _ (chaos_energy_hasSum (difference f g) hv hv2).summable
  have hC := hshift _ (chaosCrossEnergy_summable (difference f g) g hv2 hg2)
  unfold signedCrossTail
  rw [← hF.tsum_sub hG, ← tsum_mul_left, ← (hC.mul_left 2).tsum_add hV]
  apply tsum_congr
  intro k
  rw [← mul_sub, chaosEnergy_difference_identity f g hf2 hg2]
  ring

def momentMatrix (f : (κ → ℝ) → ι → ℝ) (i : ι) (j : κ) : ℝ :=
  ∫ x, x j * f x i ∂γpi κ

/-- In the affine application this is <B,M-B>, with B the ACTUAL centroid. -/
def centroidRouting (f g : (κ → ℝ) → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, momentMatrix f i j * (momentMatrix g i j - momentMatrix f i j)

def centroidResidual (f g : (κ → ℝ) → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (momentMatrix g i j - momentMatrix f i j) ^ 2

theorem centroidResidual_nonneg (f g : (κ → ℝ) → ι → ℝ) :
    0 ≤ centroidResidual f g :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem first_energy_retained_square (f g : (κ → ℝ) → ι → ℝ) :
    chaosEnergy g 1 - chaosEnergy f 1 = 2 * centroidRouting f g + centroidResidual f g := by
  rw [chaosEnergy_one, chaosEnergy_one]
  unfold centroidRouting centroidResidual momentMatrix
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact comparison for the actual Gaussian objective, including the complete
signed residual, with no affine optimality or noise representation assumed. -/
theorem actual_reference_difference (r : ℝ) (hr : |r| ≤ 1)
    (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hg : ∀ i, Measurable (fun x => g x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ))
    (hg2 : ∀ i, MemLp (fun x => g x i) 2 (γpi κ))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ) :
    NegativeVoting.gaussianNoiseStability (-r) f - NegativeVoting.gaussianNoiseStability (-r) g =
      r * (2 * centroidRouting f g + centroidResidual f g) +
      2 * signedCrossTail r (difference f g) g +
      evenResidual r (difference f g) - oddResidual r (difference f g) := by
  have hneg : |-r| ≤ 1 := by simpa using hr
  have hF := (chaos_energy_hasSum f hf hf2).summable
  have hG := (chaos_energy_hasSum g hg hg2).summable
  have hv (i : ι) : Measurable (fun x => difference f g x i) := (hf i).sub (hg i)
  have hv2 (i : ι) : MemLp (fun x => difference f g x i) 2 (γpi κ) := (hf2 i).sub (hg2 i)
  have hV := (chaos_energy_hasSum (difference f g) hv hv2).summable
  have hzero : chaosEnergy f 0 = chaosEnergy g 0 := by
    rw [chaosEnergy_zero, chaosEnergy_zero]
    simp_rw [hmass]
  have htail := signed_tail_polarization r hr f g hf hg hf2 hg2
  rw [signed_tail_even_odd r hr (difference f g) hV] at htail
  have hfirst := first_energy_retained_square f g
  rw [actual_noise_spectral (-r) hneg f hf hf2, actual_noise_spectral (-r) hneg g hg hg2,
    signed_series_split_two _ hF (-r) hneg, signed_series_split_two _ hG (-r) hneg]
  rw [hzero]
  have hfirstScaled := congrArg (fun x : ℝ => r * x) hfirst
  nlinarith only [htail, hfirstScaled]

/-- The simplex hypotheses derive every L2 premise needed by the identity. -/
theorem simplex_actual_reference_difference (r : ℝ) (hr : |r| ≤ 1)
    (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hg : ∀ i, Measurable (fun x => g x i))
    (hfs : ∀ x, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ x, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ) :
    NegativeVoting.gaussianNoiseStability (-r) f - NegativeVoting.gaussianNoiseStability (-r) g =
      r * (2 * centroidRouting f g + centroidResidual f g) +
      2 * signedCrossTail r (difference f g) g +
      evenResidual r (difference f g) - oddResidual r (difference f g) := by
  exact actual_reference_difference r hr f g hf hg
    (simplex_component_memLp f hf (fun x => (hfs x).1) (fun x => (hfs x).2))
    (simplex_component_memLp g hg (fun x => (hgs x).1) (fun x => (hgs x).2)) hmass

/-- The precise routing bracket which still needs the geometric cap estimate.
Its cross term is the actual high-degree Hermite coefficient pairing, and its
negative residual is the entire odd degree >=3 energy. -/
def routingBracket (r : ℝ) (f g : (κ → ℝ) → ι → ℝ) : ℝ :=
  r * centroidRouting f g + signedCrossTail r (difference f g) g -
    oddResidual r (difference f g)

/-- The only dropped quantity is the nonnegative even residual. In particular,
the positive centroid-residual square is retained with coefficient r. -/
theorem simplex_actual_reference_lower_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1)
    (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hg : ∀ i, Measurable (fun x => g x i))
    (hfs : ∀ x, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ x, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ) :
    r * centroidResidual f g + oddResidual r (difference f g) + 2 * routingBracket r f g ≤
      NegativeVoting.gaussianNoiseStability (-r) f - NegativeVoting.gaussianNoiseStability (-r) g := by
  have h := simplex_actual_reference_difference r (by simpa [abs_of_nonneg hr0] using hr)
    f g hf hg hfs hgs hmass
  have he := evenResidual_nonneg r hr0 (difference f g)
  unfold routingBracket
  linarith

/-- The same identity for the completed-measure admissible class in MainGoal.
No L2, chaos convergence, or spectral representation is assumed. -/
theorem ae_simplex_actual_reference_difference [Nonempty ι]
    (r : ℝ) (hr : |r| ≤ 1) (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (NegativeVoting.standardGaussian κ))
    (hg : ∀ i, AEMeasurable (fun x => g x i) (NegativeVoting.standardGaussian κ))
    (hfs : ∀ᵐ x ∂NegativeVoting.standardGaussian κ, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ᵐ x ∂NegativeVoting.standardGaussian κ, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ) :
    NegativeVoting.gaussianNoiseStability (-r) f - NegativeVoting.gaussianNoiseStability (-r) g =
      r * (2 * centroidRouting f g + centroidResidual f g) +
      2 * signedCrossTail r (difference f g) g +
      evenResidual r (difference f g) - oddResidual r (difference f g) := by
  obtain ⟨F, hF, hFs, hfF, hfv⟩ := NegativeVoting.gaussian_simplex_representative f hf hfs
  obtain ⟨G, hG, hGs, hgG, hgv⟩ := NegativeVoting.gaussian_simplex_representative g hg hgs
  have mass_congr (a b : (κ → ℝ) → ι → ℝ)
      (hab : a =ᵐ[NegativeVoting.standardGaussian κ] b) (i : ι) :
      (∫ x, a x i ∂γpi κ) = ∫ x, b x i ∂γpi κ :=
    integral_congr_ae (hab.mono (fun _ h => congrFun h i))
  have hmassFG (i : ι) : (∫ x, F x i ∂γpi κ) = ∫ x, G x i ∂γpi κ := by
    rw [← mass_congr f F hfF i, ← mass_congr g G hgG i, hmass i]
  have hmom (a b : (κ → ℝ) → ι → ℝ)
      (hab : a =ᵐ[NegativeVoting.standardGaussian κ] b) : momentMatrix a = momentMatrix b := by
    funext i j
    apply integral_congr_ae
    filter_upwards [hab] with x hx
    rw [hx]
  have hroute : centroidRouting f g = centroidRouting F G := by
    unfold centroidRouting
    rw [hmom f F hfF, hmom g G hgG]
  have hres : centroidResidual f g = centroidResidual F G := by
    unfold centroidResidual
    rw [hmom f F hfF, hmom g G hgG]
  have hv : difference f g =ᵐ[NegativeVoting.standardGaussian κ] difference F G := by
    filter_upwards [hfF, hgG] with x hx hy
    exact congrArg₂ (fun a b : ι → ℝ => fun i => a i - b i) hx hy
  have hcross : signedCrossTail r (difference f g) g = signedCrossTail r (difference F G) G := by
    unfold signedCrossTail chaosCrossEnergy
    apply tsum_congr
    intro k
    congr 1
    apply tsum_congr
    intro a
    apply Finset.sum_congr rfl
    intro i _
    rw [NegativeVoting.gaussian_hermite_coefficient_congr_ae _ _ hv i a.1,
      NegativeVoting.gaussian_hermite_coefficient_congr_ae _ _ hgG i a.1]
  have heven : evenResidual r (difference f g) = evenResidual r (difference F G) := by
    unfold evenResidual
    congr 1
    apply tsum_congr
    intro k
    rw [NegativeVoting.gaussian_chaosEnergy_congr_ae _ _ hv]
  have hodd : oddResidual r (difference f g) = oddResidual r (difference F G) := by
    unfold oddResidual
    congr 1
    apply tsum_congr
    intro k
    rw [NegativeVoting.gaussian_chaosEnergy_congr_ae _ _ hv]
  have hneg : |-r| ≤ 1 := by simpa using hr
  rw [hfv (-r) hneg, hgv (-r) hneg, hroute, hres, hcross, heven, hodd]
  exact simplex_actual_reference_difference r hr F G hF hG hFs hGs hmassFG

/-- Actual-to-reference inequality for arbitrary a.e. measurable fractional
rules with equal masses. Its right-hand bracket is defined from actual
coefficients and centroid integrals; no geometric cap bound is presumed. -/
theorem ae_simplex_actual_reference_lower_bound [Nonempty ι]
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1) (f g : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (NegativeVoting.standardGaussian κ))
    (hg : ∀ i, AEMeasurable (fun x => g x i) (NegativeVoting.standardGaussian κ))
    (hfs : ∀ᵐ x ∂NegativeVoting.standardGaussian κ, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ᵐ x ∂NegativeVoting.standardGaussian κ, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ) :
    r * centroidResidual f g + oddResidual r (difference f g) + 2 * routingBracket r f g ≤
      NegativeVoting.gaussianNoiseStability (-r) f - NegativeVoting.gaussianNoiseStability (-r) g := by
  have h := ae_simplex_actual_reference_difference r (by simpa [abs_of_nonneg hr0] using hr)
    f g hf hg hfs hgs hmass
  have he := evenResidual_nonneg r hr0 (difference f g)
  unfold routingBracket
  linarith

/-- Affine scores used by the mass-matching reference. -/
def affineScores (B : ι → κ → ℝ) (h : ι → ℝ) (x : κ → ℝ) (i : ι) : ℝ :=
  (∑ j, B i j * x j) + h i

theorem integrable_affineScores (B : ι → κ → ℝ) (h : ι → ℝ) (i : ι) :
    Integrable (fun x => affineScores B h x i) (γpi κ) := by
  classical
  exact (NegativeVoting.gaussian_linear_score_integrable (fun _ => 0) (fun _ => 1) (B i)).add
    (integrable_const (h i))

theorem integrable_affine_mixture (B : ι → κ → ℝ) (h : ι → ℝ)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (hfs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (f x)) :
    Integrable (fun x => ∑ i, f x i * affineScores B h x i) (γpi κ) := by
  classical
  exact NegativeVoting.integrable_score_mixture _ f (affineScores B h) hfs hf
    (fun i => integrable_affineScores B h i)

/-- Affine expected scores pair with actual centroid integrals and label masses.
The offset contribution is explicit, so mass matching can cancel it exactly. -/
theorem affine_score_integral (B : ι → κ → ℝ) (h : ι → ℝ)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (hfs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (f x)) :
    (∫ x, ∑ i, f x i * affineScores B h x i ∂γpi κ) =
      (∑ i, ∑ j, B i j * momentMatrix f i j) +
        ∑ i, h i * (∫ x, f x i ∂γpi κ) := by
  classical
  have hi (i : ι) : Integrable (fun x => f x i) (γpi κ) := by
    apply Integrable.of_mem_Icc 0 1 (hf i)
    filter_upwards [hfs] with x hx
    exact ⟨hx.1 i, NegativeVoting.simplex_weight_le_one (f x) hx i⟩
  have hlin : Integrable (fun x => ∑ i, f x i * (∑ j, B i j * x j)) (γpi κ) :=
    NegativeVoting.integrable_score_mixture _ f (fun x i => ∑ j, B i j * x j) hfs hf
      (fun i => NegativeVoting.gaussian_linear_score_integrable (fun _ => 0) (fun _ => 1) (B i))
  have hoff := integrable_finsetSum Finset.univ (fun i _ => (hi i).mul_const (h i))
  simp_rw [affineScores, mul_add, Finset.sum_add_distrib]
  rw [integral_add hlin hoff]
  have hpair := NegativeVoting.gaussian_centroid_pairing (fun _ : κ => 0) (fun _ => 1)
    f B hfs hf
  have hmom : NegativeVoting.gaussianCentroid (fun _ : κ => 0) (fun _ => 1) f = momentMatrix f := by
    funext i j
    apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _
  rw [hmom] at hpair
  rw [hpair, integral_finsetSum Finset.univ (fun i _ => (hi i).mul_const (h i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const, mul_comm]

/-- Equal masses cancel ALL affine offsets. The remaining score improvement
is exactly <B,M-B>, with B the actual centroid of f and M that of g. -/
theorem centroidRouting_eq_affine_integral (f g : (κ → ℝ) → ι → ℝ) (h : ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (hg : ∀ i, AEMeasurable (fun x => g x i) (γpi κ))
    (hfs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ) :
    centroidRouting f g = ∫ x,
      ((∑ i, g x i * affineScores (momentMatrix f) h x i) -
        ∑ i, f x i * affineScores (momentMatrix f) h x i) ∂γpi κ := by
  rw [integral_sub (integrable_affine_mixture _ h g hg hgs)
    (integrable_affine_mixture _ h f hf hfs),
    affine_score_integral _ h g hg hgs, affine_score_integral _ h f hf hfs]
  simp_rw [hmass]
  unfold centroidRouting
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Genuine affine routing loss is integrable without a hypothesis about the
selector's measurability; it equals a difference of integrable score mixtures. -/
theorem centroidRouting_eq_routingLoss [Nonempty ι] [DecidableEq ι]
    (f g : (κ → ℝ) → ι → ℝ) (h : ι → ℝ) (winner : (κ → ℝ) → ι)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (hg : ∀ i, AEMeasurable (fun x => g x i) (γpi κ))
    (hfs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ)
    (hroute : ∀ᵐ x ∂γpi κ, ∀ i, g x i = if i = winner x then 1 else 0) :
    centroidRouting f g = ∫ x,
      NegativeVoting.routingLoss (f x) (affineScores (momentMatrix f) h x) (winner x) ∂γpi κ := by
  classical
  rw [centroidRouting_eq_affine_integral f g h hf hg hfs hgs hmass]
  apply integral_congr_ae
  filter_upwards [hroute] with x hx
  simp only [NegativeVoting.routingLoss, hx]
  simp

/-- Integrability of the genuine affine routing loss follows from Gaussian
score integrability and the maximizer property, even for an arbitrary selector. -/
theorem integrable_centroid_affine_routingLoss [Nonempty ι]
    (f : (κ → ℝ) → ι → ℝ) (h : ι → ℝ) (winner : (κ → ℝ) → ι)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (hfs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (f x))
    (hmax : ∀ᵐ x ∂γpi κ, ∀ i,
      affineScores (momentMatrix f) h x i ≤ affineScores (momentMatrix f) h x (winner x)) :
    Integrable (fun x => NegativeVoting.routingLoss (f x)
      (affineScores (momentMatrix f) h x) (winner x)) (γpi κ) := by
  classical
  exact NegativeVoting.integrable_routing_loss _ f (affineScores (momentMatrix f) h)
    winner hfs hf (fun i => integrable_affineScores _ h i) hmax

/-- A mass-matching affine reference has nonnegative genuine routing loss.
The reference's existence and its maximizer property are explicit geometric
premises; nonnegativity and integrability are proved from them. -/
theorem centroidRouting_nonneg_of_affine_maximizer [Nonempty ι] [DecidableEq ι]
    (f g : (κ → ℝ) → ι → ℝ) (h : ι → ℝ) (winner : (κ → ℝ) → ι)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (hg : ∀ i, AEMeasurable (fun x => g x i) (γpi κ))
    (hfs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (f x))
    (hgs : ∀ᵐ x ∂γpi κ, NegativeVoting.SimplexWeights (g x))
    (hmass : ∀ i, (∫ x, f x i ∂γpi κ) = ∫ x, g x i ∂γpi κ)
    (hroute : ∀ᵐ x ∂γpi κ, ∀ i, g x i = if i = winner x then 1 else 0)
    (hmax : ∀ᵐ x ∂γpi κ, ∀ i,
      affineScores (momentMatrix f) h x i ≤ affineScores (momentMatrix f) h x (winner x)) :
    0 ≤ centroidRouting f g := by
  classical
  rw [centroidRouting_eq_routingLoss f g h winner hf hg hfs hgs hmass hroute]
  apply integral_nonneg_of_ae
  filter_upwards [hfs, hmax] with x hx hm
  exact NegativeVoting.routingLoss_nonneg _ _ _ hx hm

end NegativeVotingAffine
