import GaussianSpectralBridge

/-!
# Actual second Gaussian chaos and the quadratic moment tensor

The normalized Hermite coefficients are those of the concrete Gaussian
basis. Diagonal sqrt(2) factors and off-diagonal multiplicities are explicit.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators

namespace NegativeVotingModern

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def quadraticCoordinate (j k : κ) (x : κ → ℝ) : ℝ :=
  x j * x k - if j = k then 1 else 0

def quadraticMoment (Q : (κ → ℝ) → ℝ) (j k : κ) : ℝ :=
  ∫ x, Q x * quadraticCoordinate j k x ∂γpi κ

omit [Fintype κ] in
theorem quadraticCoordinate_symm (j k : κ) (x : κ → ℝ) :
    quadraticCoordinate j k x = quadraticCoordinate k j x := by
  simp only [quadraticCoordinate]
  by_cases h : j = k
  · subst k
    rfl
  · simp [h, Ne.symm h, mul_comm]

theorem quadraticMoment_symm (Q : (κ → ℝ) → ℝ) (j k : κ) :
    quadraticMoment Q j k = quadraticMoment Q k j := by
  simp only [quadraticMoment, quadraticCoordinate_symm j k]

theorem quadraticCoordinate_memLp (j k : κ) :
    MemLp (quadraticCoordinate j k) 2 (γpi κ) := by
  have h := memLp_mvpoly (MvPolynomial.X j * MvPolynomial.X k -
    if j = k then (1 : MvPolynomial κ ℝ) else 0)
  have heq : (fun x : κ → ℝ => MvPolynomial.eval x
      (MvPolynomial.X j * MvPolynomial.X k -
        if j = k then (1 : MvPolynomial κ ℝ) else 0)) = quadraticCoordinate j k := by
    funext x
    simp only [quadraticCoordinate, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, apply_ite, map_one, map_zero]
    by_cases hjk : j = k <;> simp [hjk]
  rwa [heq] at h

theorem quadratic_moment_integrable {Q : (κ → ℝ) → ℝ}
    (hQ : MemLp Q 2 (γpi κ)) (j k : κ) :
    Integrable (fun x => Q x * quadraticCoordinate j k x) (γpi κ) :=
  hQ.integrable_mul (quadraticCoordinate_memLp j k)

def degreeTwoEquiv : Sym2 κ ≃ {a : κ → ℕ // degree a = 2} :=
  (Sym2.equivSym κ).trans (Sym.equivNatSumOfFintype κ 2)

theorem degreeTwoEquiv_pair (j k : κ) :
    (degreeTwoEquiv (Sym2.mk j k)).1 = Pi.single j 1 + Pi.single k 1 := by
  funext l
  change ((j ::ₘ k ::ₘ (0 : Multiset κ)).count l) = _
  simp only [Multiset.count_cons, Multiset.count_zero, Pi.add_apply, Pi.single_apply]
  simp [eq_comm, add_comm]

theorem normalized_hermite_two (x : ℝ) :
    H 2 x = (x ^ 2 - 1) / Real.sqrt 2 := by
  have h := he_recurrence 0 x
  simp only [he_zero, he_one, Nat.cast_zero, zero_add, one_mul] at h
  simp only [H, h]
  norm_num
  ring

theorem psi_single_two (j : κ) (x : κ → ℝ) :
    psi (Pi.single j 2) x = quadraticCoordinate j j x / Real.sqrt 2 := by
  unfold psi
  rw [Finset.prod_eq_single j]
  · simp only [Pi.single_eq_same, normalized_hermite_two, quadraticCoordinate, ite_true]
    rw [pow_two]
  · intro k _ hkj
    simp [hkj, H]
  · simp

theorem psi_two_distinct (j k : κ) (hjk : j ≠ k) (x : κ → ℝ) :
    psi (Pi.single j 1 + Pi.single k 1) x = quadraticCoordinate j k x := by
  have hs : (Pi.single j 1 + Pi.single k 1 : κ → ℕ) =
      fun l => if l = j then 1 else if l = k then 1 else 0 := by
    funext l
    by_cases hlj : l = j <;> by_cases hlk : l = k <;>
      simp_all
  rw [hs]
  unfold psi
  have hh (l : κ) : H (if l = j then 1 else if l = k then 1 else 0) (x l) =
      (if l = j then x l else 1) * (if l = k then x l else 1) := by
    by_cases hlj : l = j <;> by_cases hlk : l = k <;>
      simp_all [H, he_one]
  simp only [hh, Finset.prod_mul_distrib]
  simp [quadraticCoordinate, hjk]

theorem coefficient_degreeTwo_pair (Q : (κ → ℝ) → ℝ) (j k : κ) :
    coeff Q (degreeTwoEquiv (Sym2.mk j k)).1 =
      if j = k then quadraticMoment Q j k / Real.sqrt 2
      else quadraticMoment Q j k := by
  rw [degreeTwoEquiv_pair]
  split_ifs with hjk
  · subst k
    have hs : (Pi.single j 1 + Pi.single j 1 : κ → ℕ) = Pi.single j 2 := by
      funext l
      by_cases hlj : l = j <;> simp [hlj]
    rw [hs]
    simp only [coeff, psi_single_two, div_mul_eq_mul_div, integral_div, quadraticMoment]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  · simp only [coeff, psi_two_distinct j k hjk, quadraticMoment]
    apply integral_congr_ae
    filter_upwards with x
    ring

theorem coefficient_degreeTwo_pair_sq (Q : (κ → ℝ) → ℝ) (j k : κ) :
    (coeff Q (degreeTwoEquiv (Sym2.mk j k)).1) ^ 2 =
      if j = k then (quadraticMoment Q j k) ^ 2 / 2
      else (quadraticMoment Q j k) ^ 2 := by
  rw [coefficient_degreeTwo_pair]
  split_ifs
  · rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · rfl

/-- Exact diagonal/off-diagonal multiplicities for a real symmetric tensor. -/
theorem symmetric_upper_triangle_half [LinearOrder κ] (q : κ → κ → ℝ)
    (hq : ∀ j k, q j k = q k j) :
    (∑ p : {p : κ × κ // p.1 ≤ p.2},
      if p.1.1 = p.1.2 then (q p.1.1 p.1.2) ^ 2 / 2
      else (q p.1.1 p.1.2) ^ 2) =
      (1 / 2 : ℝ) * ∑ j, ∑ k, (q j k) ^ 2 := by
  let F (j k : κ) : ℝ :=
    if j ≤ k then (if j = k then (q j k) ^ 2 / 2 else (q j k) ^ 2) else 0
  have hpair (j k : κ) : F j k + F k j = (q j k) ^ 2 := by
    by_cases hjk : j = k
    · subst k
      simp only [F, le_refl, ite_true]
      ring
    · by_cases hle : j ≤ k
      · have hrev : ¬ k ≤ j := fun h => hjk (le_antisymm hle h)
        simp [F, hjk, hle, hrev]
      · have hrev : k ≤ j := le_of_not_ge hle
        simp [F, Ne.symm hjk, hle, hrev, hq k j]
  have hsum : 2 * (∑ j, ∑ k, F j k) = ∑ j, ∑ k, (q j k) ^ 2 := by
    calc
      _ = (∑ j, ∑ k, F j k) + ∑ j, ∑ k, F k j := by
        rw [Finset.sum_comm (f := fun j k => F k j)]
        ring
      _ = ∑ j, ∑ k, (F j k + F k j) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by simp only [hpair]
  have hsub :
      (∑ p : {p : κ × κ // p.1 ≤ p.2},
        if p.1.1 = p.1.2 then (q p.1.1 p.1.2) ^ 2 / 2
        else (q p.1.1 p.1.2) ^ 2) = ∑ j, ∑ k, F j k := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : κ × κ => p.1 ≤ p.2))
      (by simp) (fun p : κ × κ =>
        if p.1 = p.2 then (q p.1 p.2) ^ 2 / 2 else (q p.1 p.2) ^ 2)]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hsub]
  linarith

variable {ι : Type*} [Fintype ι]

/-- The second-chaos energy is half the squared Frobenius norm of the
actual centered quadratic Gaussian moments, summed over output labels. -/
theorem chaosEnergy_two [LinearOrder κ] (f : (κ → ℝ) → ι → ℝ) :
    chaosEnergy f 2 = (1 / 2 : ℝ) *
      ∑ i, ∑ j, ∑ k, (quadraticMoment (fun x => f x i) j k) ^ 2 := by
  let e : {p : κ × κ // p.1 ≤ p.2} ≃ {a : κ → ℕ // degree a = 2} :=
    Sym2.sortEquiv.symm.trans degreeTwoEquiv
  calc
    chaosEnergy f 2 = ∑ p : {p : κ × κ // p.1 ≤ p.2},
        ∑ i, (coeff (fun x => f x i) (e p).1) ^ 2 := by
      rw [chaosEnergy, ← Equiv.tsum_eq e, tsum_fintype]
      rfl
    _ = ∑ p : {p : κ × κ // p.1 ≤ p.2}, ∑ i,
        if p.1.1 = p.1.2 then (quadraticMoment (fun x => f x i) p.1.1 p.1.2) ^ 2 / 2
        else (quadraticMoment (fun x => f x i) p.1.1 p.1.2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      exact coefficient_degreeTwo_pair_sq (fun x => f x i) p.1.1 p.1.2
    _ = ∑ i, ∑ p : {p : κ × κ // p.1 ≤ p.2},
        if p.1.1 = p.1.2 then (quadraticMoment (fun x => f x i) p.1.1 p.1.2) ^ 2 / 2
        else (quadraticMoment (fun x => f x i) p.1.1 p.1.2) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ i, (1 / 2 : ℝ) *
        ∑ j, ∑ k, (quadraticMoment (fun x => f x i) j k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact symmetric_upper_triangle_half _ (quadraticMoment_symm (fun x => f x i))
    _ = _ := by rw [Finset.mul_sum]

/-- The actual Gaussian pairing with a finite quadratic test tensor. -/
def quadraticTestPairing (f : (κ → ℝ) → ι → ℝ) (T : ι → κ → κ → ℝ) : ℝ :=
  ∫ x, ∑ i, ∑ j, ∑ k,
    T i j k * (f x i * quadraticCoordinate j k x) ∂γpi κ

theorem quadratic_test_pairing_eq (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) (T : ι → κ → κ → ℝ) :
    quadraticTestPairing f T =
      ∑ i, ∑ j, ∑ k, T i j k * quadraticMoment (fun x => f x i) j k := by
  have hterm (i : ι) (j k : κ) : Integrable
      (fun x => T i j k * (f x i * quadraticCoordinate j k x)) (γpi κ) :=
    (quadratic_moment_integrable (hf i) j k).const_mul _
  have hinner (i : ι) (j : κ) : Integrable
      (fun x => ∑ k, T i j k * (f x i * quadraticCoordinate j k x)) (γpi κ) :=
    integrable_finsetSum _ (fun k _ => hterm i j k)
  have hmiddle (i : ι) : Integrable
      (fun x => ∑ j, ∑ k, T i j k * (f x i * quadraticCoordinate j k x)) (γpi κ) :=
    integrable_finsetSum _ (fun j _ => hinner i j)
  rw [quadraticTestPairing, integral_finsetSum Finset.univ (fun i _ => hmiddle i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hinner i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hterm i j k)]
  simp only [integral_const_mul, quadraticMoment]

/-- Cauchy--Schwarz applied to the actual second-chaos moment tensor. -/
theorem quadratic_moment_tensor_cauchy [LinearOrder κ]
    (f : (κ → ℝ) → ι → ℝ) (T : ι → κ → κ → ℝ) :
    (∑ i, ∑ j, ∑ k, T i j k * quadraticMoment (fun x => f x i) j k) ^ 2 ≤
      2 * chaosEnergy f 2 * (∑ i, ∑ j, ∑ k, (T i j k) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × κ × κ))
    (fun p => T p.1 p.2.1 p.2.2)
    (fun p => quadraticMoment (fun x => f x p.1) p.2.1 p.2.2)
  simp only [Fintype.sum_prod_type] at h
  rw [chaosEnergy_two]
  convert h using 1
  ring

theorem quadratic_test_pairing_bound [LinearOrder κ]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) (T : ι → κ → κ → ℝ) :
    (quadraticTestPairing f T) ^ 2 ≤
      2 * chaosEnergy f 2 * (∑ i, ∑ j, ∑ k, (T i j k) ^ 2) := by
  rw [quadratic_test_pairing_eq f hf]
  exact quadratic_moment_tensor_cauchy f T

/-- A quadratic test tensor certifies a lower bound on the actual
second Gaussian chaos, with its exact factor of two. -/
theorem quadratic_test_tensor_certificate [LinearOrder κ]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γpi κ)) (T : ι → κ → κ → ℝ)
    (hT : 0 < ∑ i, ∑ j, ∑ k, (T i j k) ^ 2) :
    (quadraticTestPairing f T) ^ 2 / (2 * ∑ i, ∑ j, ∑ k, (T i j k) ^ 2) ≤
      chaosEnergy f 2 := by
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hT)).mpr
  convert quadratic_test_pairing_bound f hf T using 1
  ring

/-- No extra moment assumption is needed for a measurable fractional
Gaussian assignment; the simplex bounds imply the required L² membership. -/
theorem ae_simplex_quadratic_test_tensor_certificate [LinearOrder κ]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (γpi κ))
    (h0 : ∀ᵐ x ∂γpi κ, ∀ i, 0 ≤ f x i)
    (hsum : ∀ᵐ x ∂γpi κ, ∑ i, f x i = 1)
    (T : ι → κ → κ → ℝ)
    (hT : 0 < ∑ i, ∑ j, ∑ k, (T i j k) ^ 2) :
    (quadraticTestPairing f T) ^ 2 / (2 * ∑ i, ∑ j, ∑ k, (T i j k) ^ 2) ≤
      chaosEnergy f 2 := by
  classical
  have hf2 (i : ι) : MemLp (fun x => f x i) 2 (γpi κ) := by
    refine MemLp.of_bound (hf i).aestronglyMeasurable 1 ?_
    filter_upwards [h0, hsum] with x hx0 hxsum
    rw [Real.norm_eq_abs, abs_of_nonneg (hx0 i)]
    calc
      f x i ≤ ∑ j, f x j :=
        Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ i)
      _ = 1 := hxsum
  exact quadratic_test_tensor_certificate f hf2 T hT

end NegativeVotingModern
