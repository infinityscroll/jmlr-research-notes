import GaussianFanCycleCoefficients

/-! The actual Gaussian A-B cycle factorization, with ordered-simplex normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem alternatingTetrahedron_zero_of_repeat (tau : V → V → V → V → ℝ)
    (htau : AlternatingTetrahedron tau) (a j k l : V)
    (hr : a=j ∨ a=k ∨ a=l ∨ j=k ∨ j=l ∨ k=l) : tau a j k l = 0 := by
  have hfirst (a k l : V) : tau a a k l = 0 := by
    have he := htau.1 a a k l
    linarith
  have hmiddle (a j l : V) : tau a j j l = 0 := by
    have he := htau.2.1 a j j l
    linarith
  have hskip (a j l : V) : tau a j a l = 0 := by
    have he := htau.2.1 a j a l
    rw [hfirst] at he
    linarith
  rcases hr with he|he|he|he|he|he
  · subst j; exact hfirst a k l
  · subst k; exact hskip a j l
  · subst l
    have hx := htau.2.2 a j k a
    rw [hskip] at hx
    linarith
  · subst k; exact hmiddle a j l
  · subst l
    have hx := htau.2.2 a j k j
    rw [hmiddle] at hx
    linarith
  · subst l
    have hx := htau.2.2 a j k k
    linarith

/-- The outside mean coefficient is valid after multiplication by any alternating
four-chain, because repeated-face contributions vanish identically. -/
theorem tetrahedron_times_actual_mean (b : AffineBasis V ℝ E) (h : V → ℝ)
    (tau : V → V → V → V → ℝ) (htau : AlternatingTetrahedron tau) (k a j l : V) :
    tau k a j l * cycleMean b h a j l (barycentricOutwardVector b k) =
      tau k a j l * cycleTriangleWeight b h a j l * cycleTetrahedronWeight b h k a j l := by
  by_cases hd : k≠a ∧ k≠j ∧ k≠l ∧ a≠j ∧ a≠l ∧ j≠l
  · rcases hd with ⟨hka,hkj,hkl,haj,hal,hjl⟩
    rw [cycleMean_barycentric_outside b h a j l k haj hal.symm hjl.symm hka hkj hkl,
      cycleTetrahedronWeight_swap_last b h a j l k,
      cycleTetrahedronWeight_swap_middle b h a j k l,
      cycleTetrahedronWeight_swap_first b h a k j l]
    ring
  · have hr : k=a ∨ k=j ∨ k=l ∨ a=j ∨ a=l ∨ j=l := by tauto
    rw [alternatingTetrahedron_zero_of_repeat tau htau k a j l hr]
    simp

theorem actual_mean_weighted_triangle_alternating (b : AffineBasis V ℝ E) (h : V → ℝ)
    (eta : V → V → V → ℝ) (heta : AlternatingTriangle eta) (k : V) :
    AlternatingTriangle (fun a j l => eta a j l *
      cycleMean b h a j l (barycentricOutwardVector b k)) := by
  constructor
  · intro a j l
    change eta a j l * cycleMean b h a j l _ = -(eta j a l * cycleMean b h j a l _)
    rw [heta.1 a j l,cycleMean_swap_first b h a j l]
    ring
  · intro a j l
    change eta a j l * cycleMean b h a j l _ = eta j l a * cycleMean b h j l a _
    rw [heta.2 a j l,cycleMean_cyclic b h a j l]

theorem triangleCoboundary_cyclic_edges (rho : V → V → V → ℝ)
    (hrho : AlternatingTriangle rho) (k a j l : V) :
    rho k a j+rho k j l+rho k l a = rho a j l-triangleCoboundary rho k a j l := by
  rw [triangleCoboundary,alternatingTriangle_swap_last rho hrho k l a]
  ring

theorem cycleA_sub_cycleB_reorder (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) :
    cycleA b h lam eta-cycleB b h lam eta =
      (1/2:ℝ) * ∑ k, ∑ a, ∑ j, ∑ l,
        (eta l a j * cycleMean b h l a j (barycentricOutwardVector b k)) *
          (cycleTriangleWeight b h k a j * lam k a j) := by
  rw [cycleA_sub_cycleB]
  congr 1
  calc
    _ = ∑ a, ∑ k, ∑ j, ∑ l,
      lam k a j * eta l a j * cycleTriangleWeight b h k a j *
        cycleMean b h l a j (barycentricOutwardVector b k) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ a, ∑ j, ∑ l,
      lam k a j * eta l a j * cycleTriangleWeight b h k a j *
        cycleMean b h l a j (barycentricOutwardVector b k) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- The factor3 is the literal average over the three edges of each ordered triangle. -/
theorem actual_cycle_pairing_average (b : AffineBasis V ℝ E) (h : V → ℝ)
    (rho eta : V → V → V → ℝ) (hrho : AlternatingTriangle rho)
    (heta : AlternatingTriangle eta) :
    3*(∑ k, ∑ a, ∑ j, ∑ l,
      (eta l a j * cycleMean b h l a j (barycentricOutwardVector b k))*rho k a j) =
    ∑ k, ∑ a, ∑ j, ∑ l,
      eta a j l * cycleMean b h a j l (barycentricOutwardVector b k) *
        (rho a j l-triangleCoboundary rho k a j l) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have ha := full_triangle_pairing_eq_three
    (fun a j l => eta a j l * cycleMean b h a j l (barycentricOutwardVector b k))
    (actual_mean_weighted_triangle_alternating b h eta heta k) (fun a j => rho k a j)
  simp only [triangleBoundary,Finset.sum_mul] at ha
  calc
    _ = ∑ a, ∑ j, ∑ l,
      eta a j l * cycleMean b h a j l (barycentricOutwardVector b k) *
        (rho k a j+rho k j l+rho k l a) := ha.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [triangleCoboundary_cyclic_edges rho hrho k a j l]

/-- Actual Gaussian centering and reciprocal-height means turn the cyclic average
into the genuine tetrahedron boundary pairing. -/
theorem actual_cycle_pairing_collapse (b : AffineBasis V ℝ E) (h : V → ℝ)
    (rho eta : V → V → V → ℝ) (hrho : AlternatingTriangle rho) :
    (∑ k, ∑ a, ∑ j, ∑ l,
      eta a j l * cycleMean b h a j l (barycentricOutwardVector b k) *
        (rho a j l-triangleCoboundary rho k a j l)) =
    -(∑ a, ∑ j, ∑ l, (cycleTriangleWeight b h a j l * eta a j l) *
      tetrahedronBoundary (fun k a j l => cycleTetrahedronWeight b h k a j l *
        triangleCoboundary rho k a j l) a j l) := by
  rw [sum_four_rotate (fun k a j l =>
    eta a j l * cycleMean b h a j l (barycentricOutwardVector b k) *
      (rho a j l-triangleCoboundary rho k a j l))]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have hm : (∑ k, cycleMean b h a j l (barycentricOutwardVector b k)) = 0 :=
    sum_stratumMeanPairing_barycentric b h {a,j,l} a
  have he (k : V) :
      eta a j l * cycleMean b h a j l (barycentricOutwardVector b k) *
        (rho a j l-triangleCoboundary rho k a j l) =
      (eta a j l*rho a j l)*cycleMean b h a j l (barycentricOutwardVector b k)-
        eta a j l*(triangleCoboundary rho k a j l *
          cycleMean b h a j l (barycentricOutwardVector b k)) := by ring
  simp_rw [he,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hm,mul_zero,zero_sub]
  have hc (k : V) : triangleCoboundary rho k a j l *
      cycleMean b h a j l (barycentricOutwardVector b k) =
    cycleTriangleWeight b h a j l *
      (cycleTetrahedronWeight b h k a j l*triangleCoboundary rho k a j l) := by
    rw [tetrahedron_times_actual_mean b h (triangleCoboundary rho)
      (triangleCoboundary_alternating rho hrho) k a j l]
    ring
  simp_rw [hc,← Finset.mul_sum]
  unfold tetrahedronBoundary
  ring

/-- Exact Gaussian finite-fan factorization. No covariance-concavity or Hodge
identity is assumed: all coefficients are actual Gaussian stratum means. -/
theorem actual_fan_cycle_factorization (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) (hlam : AlternatingTriangle lam)
    (heta : AlternatingTriangle eta) :
    cycleA b h lam eta-cycleB b h lam eta = cycleFactorizationRHS b h lam eta := by
  let rho := fun a j k => cycleTriangleWeight b h a j k * lam a j k
  let sigma := fun a j k => cycleTriangleWeight b h a j k * eta a j k
  let tau := fun a j k l => cycleTetrahedronWeight b h a j k l * triangleCoboundary rho a j k l
  have hrho : AlternatingTriangle rho := cycle_weighted_triangle_alternating b h lam hlam
  have hsigma : AlternatingTriangle sigma := cycle_weighted_triangle_alternating b h eta heta
  have htau : AlternatingTetrahedron tau := cycle_weighted_tetrahedron_alternating b h
    (triangleCoboundary rho) (triangleCoboundary_alternating rho hrho)
  have h0 := cycleA_sub_cycleB_reorder b h lam eta
  have h1 := actual_cycle_pairing_average b h rho eta hrho heta
  have h2 := actual_cycle_pairing_collapse b h rho eta hrho
  have h3 := triangle_tetrahedron_adjoint sigma hsigma tau htau
  change cycleA b h lam eta-cycleB b h lam eta =
    -(1/24:ℝ) * ∑ a, ∑ j, ∑ k, ∑ l,
      tau a j k l * triangleCoboundary sigma a j k l
  change cycleA b h lam eta-cycleB b h lam eta =
    (1/2:ℝ) * ∑ k, ∑ a, ∑ j, ∑ l,
      (eta l a j * cycleMean b h l a j (barycentricOutwardVector b k))*rho k a j at h0
  change (∑ k, ∑ a, ∑ j, ∑ l,
      eta a j l * cycleMean b h a j l (barycentricOutwardVector b k) *
        (rho a j l-triangleCoboundary rho k a j l)) =
    -(∑ a, ∑ j, ∑ l, sigma a j l * tetrahedronBoundary tau a j l) at h2
  linarith

end NegativeVotingFanCycle
