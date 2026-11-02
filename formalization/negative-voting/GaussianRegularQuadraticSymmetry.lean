import GaussianRegularQuadraticGeometry

/-! Actual Gaussian permutation symmetry and the distinguished quadratic moment. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingRegularQuadratic
open NegativeVotingRegularMaximum NegativeVoting NegativeVotingModern
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumSecondMoment
  OAI.MinUncut.GaussianHermite

/-- Coordinate relabeling preserves the actual product Gaussian and all three
indices of the implemented centered moment tensor. -/
theorem moment_perm (n : ℕ) (e : Equiv.Perm (Fin (n+2))) (i a c : Fin (n+2)) :
    moment n (e i) (e a) (e c)=moment n i a c := by
  let T := MeasurableEquiv.piCongrLeft (fun _ : Fin (n+2) => ℝ) e.symm
  have hp : MeasurePreserving T (γpi (Fin (n+2))) (γpi (Fin (n+2))) :=
    measurePreserving_piCongrLeft (μ := fun _ : Fin (n+2) => gaussianReal 0 1) e.symm
  have hT (x : Fin (n+2) → ℝ) (j : Fin (n+2)) : T x j=x (e j) := by
    simpa only [T,Equiv.symm_apply_apply] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (n+2) => ℝ) e.symm x (e j)
  have hw (x : Fin (n+2) → ℝ) : maxWeights (T x) i=maxWeights x (e i) := by
    have he : T x=(fun j => x (e j)) := funext (hT x)
    rw [he]
    exact maxWeights_perm x e i
  have hq (x : Fin (n+2) → ℝ) : quadraticCoordinate a c (T x)=quadraticCoordinate (e a) (e c) x := by
    unfold quadraticCoordinate
    rw [hT,hT]
    simp only [e.injective.eq_iff]
  have h := hp.integral_comp' (fun x => maxWeights x i*quadraticCoordinate a c x)
  change (∫ x, maxWeights (T x) i*quadraticCoordinate a c (T x) ∂γpi (Fin (n+2)))=
    ∫ x, maxWeights x i*quadraticCoordinate a c x ∂γpi (Fin (n+2)) at h
  simp_rw [hw,hq] at h
  exact h

theorem moment_distinguished_eq (n : ℕ) (i j : Fin (n+2)) :
    moment n i i i=moment n j j j := by
  simpa only [Equiv.swap_apply_left] using (moment_perm n (Equiv.swap i j) i i i).symm

theorem moment_swap_invariant (n : ℕ) (i a b : Fin (n+2)) (ha : a ≠ i) (hb : b ≠ i)
    (j k : Fin (n+2)) :
    moment n i (Equiv.swap a b j) (Equiv.swap a b k)=moment n i j k := by
  simpa only [Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm] using
    moment_perm n (Equiv.swap a b) i j k

/-- Every maximizer carries the same observable, including the tie convention. -/
theorem maxWeights_observable {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (g : ℝ → ℝ) : (∑ i, maxWeights s i*g (s i))=g (maxScore s) := by
  have he (i : ι) : maxWeights s i*g (s i)=maxWeights s i*g (maxScore s) := by
    by_cases hi : s i=maxScore s
    · rw [hi]
    · simp [maxWeights,maxIndicator,hi]
  simp_rw [he]
  rw [← Finset.sum_mul,(maxWeights_simplex s).2,one_mul]

theorem canonical_component_memLp (n : ℕ) (i : Fin (n+2)) :
    MemLp (fun x : Fin (n+2) → ℝ => maxWeights x i) 2 (γpi (Fin (n+2))) := by
  exact simplex_component_memLp (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)
    (fun j => measurable_maxWeights id (fun k => measurable_pi_apply k) j)
    (fun x => (maxWeights_simplex x).1) (fun x => (maxWeights_simplex x).2) i

/-- The tensor's distinguished entry is obtained from the actual maximum
second moment by summing the tested selection identity. -/
theorem moment_distinguished (n : ℕ) (i : Fin (n+2)) :
    moment n i i i=(maximumSecondMoment n-1)/((n:ℝ)+2) := by
  have he (x : Fin (n+2) → ℝ) :
      (∑ j, maxWeights x j*quadraticCoordinate j j x)=maximum x^2-1 := by
    simpa [quadraticCoordinate,pow_two,maximum] using
      maxWeights_observable x (fun u => u*u-1)
  have hsum : (∑ j : Fin (n+2), moment n j j j)=maximumSecondMoment n-1 := by
    unfold moment quadraticMoment
    rw [← integral_finsetSum Finset.univ (fun j _ => quadratic_moment_integrable (canonical_component_memLp n j) j j)]
    simp_rw [he]
    change (∫ x, maximum x^2-1 ∂standardGaussian (Fin (n+2)))=maximumSecondMoment n-1
    rw [integral_sub maximum_square_integrable (integrable_const _)]
    simp [maximumSecondMoment]
  have hdiag (j : Fin (n+2)) := moment_distinguished_eq n j i
  simp_rw [hdiag] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat] at hsum
  apply (eq_div_iff (by positivity)).mpr
  nlinarith

end NegativeVotingRegularQuadratic
