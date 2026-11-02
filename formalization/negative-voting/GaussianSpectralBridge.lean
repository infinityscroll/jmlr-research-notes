import SlowEquilibration.GaussianNoiseL2

/-!
# Actual Gaussian coupling and its signed Hermite series

This file uses the concrete Gaussian Hermite basis and actual Gaussian noise
operator from the attributed upstream development. The spectral representation
is proved from their kernel-checkable basis and coefficient theorems, rather
than assumed as an interface. Negative correlations retain their odd-degree
signs throughout.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open SlowEquilibration.GaussianMaximalCorrelation
open scoped BigOperators RealInnerProductSpace

namespace NegativeVotingModern

variable {κ : Type*} [Fintype κ]

theorem hermite_basis_coefficient {Q : (κ → ℝ) → ℝ}
    (hQ : MemLp Q 2 (γpi κ)) (a : κ → ℕ) :
    inner ℝ (productHermiteBasis a) (hQ.toLp Q) = coeff Q a := by
  simp only [productHermiteBasis, HilbertBasis.coe_mkOfOrthogonalEqBot,
    psiVec, integral_inner_toLp, coeff]

/-- Parseval applied to the actual Gaussian noise operator. This theorem
allows either sign of rho; the only correlation hypothesis is rho²+s²=1. -/
theorem gaussian_noise_pairing_spectral_hasSum (ρ s : ℝ)
    (hρs : ρ ^ 2 + s ^ 2 = 1) {Q : (κ → ℝ) → ℝ}
    (hQ : Measurable Q) (hQ2 : MemLp Q 2 (γpi κ)) :
    HasSum (fun a : κ → ℕ => ρ ^ degree a * (coeff Q a) ^ 2)
      (∫ x, Q x * noise ρ s Q x ∂γpi κ) := by
  have hN := memLp_noise_L2 ρ s hρs hQ hQ2
  have hp := productHermiteBasis.hasSum_inner_mul_inner
    (hQ2.toLp Q) (hN.toLp (noise ρ s Q))
  have heq : (fun a : κ → ℕ => inner ℝ (hQ2.toLp Q) (productHermiteBasis a) *
      inner ℝ (productHermiteBasis a) (hN.toLp (noise ρ s Q))) =
      fun a => ρ ^ degree a * (coeff Q a) ^ 2 := by
    funext a
    rw [real_inner_comm, hermite_basis_coefficient hQ2,
      hermite_basis_coefficient hN, noise_coefficient_L2 ρ s hρs hQ hQ2]
    ring
  rw [heq, integral_inner_toLp] at hp
  exact hp

/-- Full infinite signed expansion of the concrete two-input Gaussian
coupling integral. Summability is included in HasSum, not assumed. -/
theorem gaussian_coupling_spectral_hasSum (ρ s : ℝ)
    (hρs : ρ ^ 2 + s ^ 2 = 1) {Q : (κ → ℝ) → ℝ}
    (hQ : Measurable Q) (hQ2 : MemLp Q 2 (γpi κ)) :
    HasSum (fun a : κ → ℕ => ρ ^ degree a * (coeff Q a) ^ 2)
      (∫ z : (κ → ℝ) × (κ → ℝ), Q z.1 * Q (ρ • z.1 + s • z.2)
        ∂(γpi κ).prod (γpi κ)) := by
  have hi : Integrable (fun z : (κ → ℝ) × (κ → ℝ) =>
      Q z.1 * Q (ρ • z.1 + s • z.2)) ((γpi κ).prod (γpi κ)) :=
    (hQ2.comp_fst (γpi κ)).integrable_mul (coupled_memLp ρ s hρs hQ2)
  have heq : (∫ z : (κ → ℝ) × (κ → ℝ), Q z.1 * Q (ρ • z.1 + s • z.2)
      ∂(γpi κ).prod (γpi κ)) = ∫ x, Q x * noise ρ s Q x ∂γpi κ := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [] with x
    exact integral_const_mul _ _
  rw [heq]
  exact gaussian_noise_pairing_spectral_hasSum ρ s hρs hQ hQ2

/-- Parseval energy is the actual Gaussian square integral. -/
theorem gaussian_coefficient_energy_hasSum {Q : (κ → ℝ) → ℝ}
    (hQ : Measurable Q) (hQ2 : MemLp Q 2 (γpi κ)) :
    HasSum (fun a : κ → ℕ => (coeff Q a) ^ 2)
      (∫ x, (Q x) ^ 2 ∂γpi κ) := by
  simpa [noise, pow_two] using
    gaussian_noise_pairing_spectral_hasSum 1 0 (by norm_num) hQ hQ2

variable {ι : Type*} [Fintype ι]

def labelCoefficientEnergy (f : (κ → ℝ) → ι → ℝ) (a : κ → ℕ) : ℝ :=
  ∑ i, (coeff (fun x => f x i) a) ^ 2

def chaosEnergy (f : (κ → ℝ) → ι → ℝ) (k : ℕ) : ℝ :=
  ∑' a : {a : κ → ℕ // degree a = k}, labelCoefficientEnergy f a.1

theorem labelCoefficientEnergy_nonneg (f : (κ → ℝ) → ι → ℝ) (a : κ → ℕ) :
    0 ≤ labelCoefficientEnergy f a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem chaosEnergy_nonneg (f : (κ → ℝ) → ι → ℝ) (k : ℕ) :
    0 ≤ chaosEnergy f k :=
  tsum_nonneg (fun _ => labelCoefficientEnergy_nonneg f _)

theorem degree_zero_iff (a : κ → ℕ) : degree a = 0 ↔ a = 0 := by
  classical
  constructor
  · intro ha
    funext j
    have hj := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset κ)) => Nat.zero_le (a i))
      (Finset.mem_univ j)
    change a j ≤ degree a at hj
    rw [ha] at hj
    exact Nat.le_zero.mp hj
  · rintro rfl
    simp [degree]

theorem coefficient_zero_degree (Q : (κ → ℝ) → ℝ) :
    coeff Q (0 : κ → ℕ) = ∫ x, Q x ∂γpi κ := by
  simp [coeff, psi, H]

/-- Degree-zero energy is exactly the sum of squared label masses. -/
theorem chaosEnergy_zero (f : (κ → ℝ) → ι → ℝ) :
    chaosEnergy f 0 = ∑ i, (∫ x, f x i ∂γpi κ) ^ 2 := by
  let a0 : {a : κ → ℕ // degree a = 0} := ⟨0, (degree_zero_iff _).mpr rfl⟩
  let : Unique {a : κ → ℕ // degree a = 0} :=
    { default := a0
      uniq := fun a => Subtype.ext ((degree_zero_iff a.1).mp a.2) }
  rw [chaosEnergy, (hasSum_unique
    (fun a : {a : κ → ℕ // degree a = 0} => labelCoefficientEnergy f a.1)).tsum_eq]
  change labelCoefficientEnergy f 0 = _
  simp only [labelCoefficientEnergy, coefficient_zero_degree]

theorem degree_single_one [DecidableEq κ] (j : κ) :
    degree (Pi.single j (1 : ℕ)) = 1 := by
  simp [degree, Pi.single_apply]

theorem degree_one_iff [DecidableEq κ] (a : κ → ℕ) :
    degree a = 1 ↔ ∃ j, a = Pi.single j 1 := by
  constructor
  · intro ha
    have hsum : (Finsupp.equivFunOnFinite.symm a).sum (fun _ n => n) = 1 := by
      rw [Finsupp.equivFunOnFinite_symm_sum]
      exact ha
    obtain ⟨j, hj⟩ := (Finsupp.sum_eq_one_iff _).mp hsum
    refine ⟨j, ?_⟩
    simpa only [Equiv.apply_symm_apply, Finsupp.equivFunOnFinite_single] using
      congrArg Finsupp.equivFunOnFinite hj
  · rintro ⟨j, rfl⟩
    exact degree_single_one j

def degreeOneEquiv [DecidableEq κ] : κ ≃ {a : κ → ℕ // degree a = 1} :=
  Equiv.ofBijective (fun j => ⟨Pi.single j 1, degree_single_one j⟩) (by
    constructor
    · intro j k hjk
      by_contra hne
      have h := congrFun (congrArg Subtype.val hjk) j
      simp [hne] at h
    · intro a
      obtain ⟨j, hj⟩ := (degree_one_iff a.1).mp a.2
      exact ⟨j, Subtype.ext hj.symm⟩)

theorem coefficient_single_degree [DecidableEq κ]
    (Q : (κ → ℝ) → ℝ) (j : κ) :
    coeff Q (Pi.single j 1) = ∫ x, x j * Q x ∂γpi κ := by
  have hpsi (x : κ → ℝ) : psi (Pi.single j 1) x = x j := by
    unfold psi
    rw [Finset.prod_eq_single j]
    · simp [H, he_one]
    · intro k _ hkj
      simp [hkj, H]
    · simp
  simp only [coeff, hpsi]

/-- Degree-one energy is exactly the squared Euclidean norm of the
Gaussian centroid matrix. This connects the signed first chaos to the
centroid deficit used in the negative-voting proof. -/
theorem chaosEnergy_one (f : (κ → ℝ) → ι → ℝ) :
    chaosEnergy f 1 = ∑ i, ∑ j, (∫ x, x j * f x i ∂γpi κ) ^ 2 := by
  classical
  rw [chaosEnergy, ← (degreeOneEquiv (κ := κ)).tsum_eq
    (fun a => labelCoefficientEnergy f a.1), tsum_fintype]
  change (∑ j, labelCoefficientEnergy f (Pi.single j 1)) = _
  simp only [labelCoefficientEnergy, coefficient_single_degree]
  exact Finset.sum_comm

theorem label_coefficient_energy_hasSum (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) :
    HasSum (labelCoefficientEnergy f) (∑ i, ∫ x, (f x i) ^ 2 ∂γpi κ) := by
  exact hasSum_sum (fun i _ => gaussian_coefficient_energy_hasSum (hf i) (hf2 i))

/-- Grouping by total Hermite degree preserves the actual finite energy. -/
theorem chaos_energy_hasSum (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) :
    HasSum (chaosEnergy f) (∑ i, ∫ x, (f x i) ^ 2 ∂γpi κ) := by
  have h := (label_coefficient_energy_hasSum f hf hf2).tsum_fiberwise degree
  change HasSum (fun k : ℕ => ∑' a : {a : κ → ℕ // degree a = k},
    labelCoefficientEnergy f a.1) _ at h
  exact h

/-- Every finite-dimensional fractional assignment has a signed Hermite
series for its actual Gaussian coupling integral. This first statement
requires only measurable L² components, and so is stronger than the
simplex-valued specialization. -/
theorem gaussian_label_coupling_spectral_hasSum (ρ s : ℝ)
    (hρs : ρ ^ 2 + s ^ 2 = 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) :
    HasSum (fun a : κ → ℕ => ρ ^ degree a * labelCoefficientEnergy f a)
      (∫ z : (κ → ℝ) × (κ → ℝ), ∑ i, f z.1 i * f (ρ • z.1 + s • z.2) i
        ∂(γpi κ).prod (γpi κ)) := by
  have hi (i : ι) : Integrable (fun z : (κ → ℝ) × (κ → ℝ) =>
      f z.1 i * f (ρ • z.1 + s • z.2) i) ((γpi κ).prod (γpi κ)) :=
    ((hf2 i).comp_fst (γpi κ)).integrable_mul (coupled_memLp ρ s hρs (hf2 i))
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  have hh := hasSum_sum (s := Finset.univ)
    (fun i _ => gaussian_coupling_spectral_hasSum ρ s hρs (hf i) (hf2 i))
  simpa only [labelCoefficientEnergy, Finset.mul_sum] using hh

/-- The complete signed series indexed by chaos degree. In particular,
negative rho has negative odd-degree contributions. -/
theorem gaussian_label_chaos_hasSum (ρ s : ℝ)
    (hρs : ρ ^ 2 + s ^ 2 = 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hf2 : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) :
    HasSum (fun k : ℕ => ρ ^ k * chaosEnergy f k)
      (∫ z : (κ → ℝ) × (κ → ℝ), ∑ i, f z.1 i * f (ρ • z.1 + s • z.2) i
        ∂(γpi κ).prod (γpi κ)) := by
  have hh := (gaussian_label_coupling_spectral_hasSum ρ s hρs f hf hf2).tsum_fiberwise degree
  have heq : (fun k : ℕ => ∑' a : degree ⁻¹' {k},
      ρ ^ degree a.1 * labelCoefficientEnergy f a.1) =
      fun k => ρ ^ k * chaosEnergy f k := by
    funext k
    change (∑' a : {a : κ → ℕ // degree a = k},
      ρ ^ degree a.1 * labelCoefficientEnergy f a.1) = _
    calc
      (∑' a : {a : κ → ℕ // degree a = k},
          ρ ^ degree a.1 * labelCoefficientEnergy f a.1) =
          ∑' a : {a : κ → ℕ // degree a = k},
            ρ ^ k * labelCoefficientEnergy f a.1 :=
        tsum_congr (fun a => by rw [a.property])
      _ = _ := tsum_mul_left
  rw [heq] at hh
  exact hh

theorem simplex_component_memLp (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (h0 : ∀ x i, 0 ≤ f x i) (hsum : ∀ x, ∑ i, f x i = 1) (i : ι) :
    MemLp (fun x => f x i) 2 (γpi κ) := by
  classical
  refine MemLp.of_bound (hf i).aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 x i)]
  calc
    f x i ≤ ∑ j, f x j := Finset.single_le_sum (fun j _ => h0 x j) (Finset.mem_univ i)
    _ = 1 := hsum x

/-- The total chaos energy of a fractional assignment is at most one,
proved from Parseval and the pointwise simplex constraints. -/
theorem simplex_chaos_energy_le_one (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (h0 : ∀ x i, 0 ≤ f x i) (hsum : ∀ x, ∑ i, f x i = 1) :
    (∑' k, chaosEnergy f k) ≤ 1 := by
  classical
  have hf2 := simplex_component_memLp f hf h0 hsum
  rw [(chaos_energy_hasSum f hf hf2).tsum_eq,
    ← integral_finsetSum Finset.univ (fun i _ => (hf2 i).integrable_sq)]
  have hpoint (x : κ → ℝ) : ∑ i, (f x i) ^ 2 ≤ 1 := by
    calc
      ∑ i, (f x i) ^ 2 ≤ ∑ i, f x i := by
        apply Finset.sum_le_sum
        intro i _
        have hle : f x i ≤ 1 :=
          (Finset.single_le_sum (fun j _ => h0 x j) (Finset.mem_univ i)).trans_eq (hsum x)
        nlinarith [mul_nonneg (h0 x i) (sub_nonneg.mpr hle)]
      _ = 1 := hsum x
  have hint : Integrable (fun x => ∑ i, (f x i) ^ 2) (γpi κ) :=
    integrable_finsetSum _ (fun i _ => (hf2 i).integrable_sq)
  simpa using integral_mono hint (integrable_const (1 : ℝ)) hpoint

/-- Exact signed spectral representation of the same concrete coupling
used in the negative-voting theorem. No spectral representation, finite
energy bound, or component L² hypothesis is assumed. -/
theorem actual_simplex_noise_stability_spectral (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (h0 : ∀ x i, 0 ≤ f x i) (hsum : ∀ x, ∑ i, f x i = 1) :
    (∫ z : (κ → ℝ) × (κ → ℝ), ∑ i, f z.1 i *
        f (fun j => ρ * z.1 j + Real.sqrt (1 - ρ ^ 2) * z.2 j) i
      ∂(γpi κ).prod (γpi κ)) =
      ∑' k : ℕ, ρ ^ k * chaosEnergy f k := by
  have hnonneg : 0 ≤ 1 - ρ ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one ρ).mpr hρ)
  have hρs : ρ ^ 2 + (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hnonneg]
    ring
  exact (gaussian_label_chaos_hasSum ρ (Real.sqrt (1 - ρ ^ 2)) hρs f hf
    (simplex_component_memLp f hf h0 hsum)).tsum_eq.symm

/-- Absolute convergence of the actual signed noise series follows from
the proved finite nonnegative chaos energy, for either sign of rho. -/
theorem actual_simplex_noise_series_absolutely_summable (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (h0 : ∀ x i, 0 ≤ f x i) (hsum : ∀ x, ∑ i, f x i = 1) :
    Summable (fun k : ℕ => ‖ρ ^ k * chaosEnergy f k‖) := by
  have henergy := (chaos_energy_hasSum f hf (simplex_component_memLp f hf h0 hsum)).summable
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ henergy
  intro k
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (chaosEnergy_nonneg f k)]
  exact mul_le_of_le_one_left (chaosEnergy_nonneg f k)
    (pow_le_one₀ (abs_nonneg ρ) hρ)

end NegativeVotingModern
