import GaussianRegularSpectatorRepresentation

/-! Coordinate-free integral representation and actual orthogonal covariance
of Gaussian cell quadratic tests. Both Hermite centering terms are retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical RealInnerProductSpace

namespace NegativeVotingQuadraticMomentIsometry
open NegativeVotingFan NegativeVotingFanQuadraticMoments
  NegativeVotingSecondChaosFacetGradient NegativeVotingRegularQuadraticRepresentation
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def quadraticKernel (x y : FSC.Coord d) : ℝ :=
  (inner ℝ x y)^2-‖x‖^2-‖y‖^2+(d:ℝ)

theorem tensorTest_pairing (x y : FSC.Coord d) :
    (∑ j,∑ k,tensorTest j k y*tensorTest j k x)=quadraticKernel x y := by
  have he (j k : Fin d) : tensorTest j k y*tensorTest j k x=
      x j*x k*(y j*y k)-(if j=k then (x j)^2 else 0)-
        (if j=k then (y j)^2 else 0)+(if j=k then 1 else 0) := by
    by_cases hjk : j=k
    · subst k
      simp only [tensorTest,ite_true]
      ring
    · simp only [tensorTest,if_neg hjk]
      ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [rank_one_form]
  simp only [quadraticKernel,PiLp.inner_apply,Real.inner_apply,
    EuclideanSpace.real_norm_sq_eq]

/-- The actual centered tensor test is an integral of an orthogonally
invariant kernel over its literal Gaussian winning cell. -/
theorem quadraticLabelTest_eq_kernel_integral (B : ι→FSC.Coord d)
    (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    quadraticLabelTest B h i x=
      ∫ y in winningCell B h i,quadraticKernel x y ∂stdGaussian (FSC.Coord d) := by
  simp_rw [←tensorTest_pairing]
  rw [integral_finsetSum Finset.univ (fun j _=>integrable_finsetSum Finset.univ
    (fun k _=>((tensorTest_memLp (stdGaussian (FSC.Coord d)) j k).integrable
      (by norm_num)).mul_const (tensorTest j k x) |>.restrict))]
  unfold quadraticLabelTest
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _=>
    ((tensorTest_memLp (stdGaussian (FSC.Coord d)) j k).integrable
      (by norm_num)).mul_const (tensorTest j k x) |>.restrict)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const]
  rfl

theorem quadraticKernel_isometry (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (x y : FSC.Coord d) : quadraticKernel (T x) (T y)=quadraticKernel x y := by
  simp only [quadraticKernel,T.inner_map_map,T.norm_map]

theorem winningCell_isometry_mem (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    T x∈winningCell (fun j=>T (B j)) h i ↔ x∈winningCell B h i := by
  simp only [winningCell,Set.mem_setOf_eq,scores,T.inner_map_map]

/-- Exact covariance for every literal Gaussian cell, including arbitrary
offsets and no rank or injectivity assumption on its row family. -/
theorem quadraticLabelTest_isometry (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    quadraticLabelTest (fun j=>T (B j)) h i (T x)=quadraticLabelTest B h i x := by
  rw [quadraticLabelTest_eq_kernel_integral,quadraticLabelTest_eq_kernel_integral]
  have hp : MeasurePreserving T (stdGaussian (FSC.Coord d)) (stdGaussian (FSC.Coord d)) :=
    ⟨T.continuous.measurable,stdGaussian_map T⟩
  have hh := hp.integral_comp T.toHomeomorph.measurableEmbedding ((winningCell (fun j=>T (B j)) h i).indicator
    (quadraticKernel (T x)))
  have he : (fun y=>(winningCell (fun j=>T (B j)) h i).indicator
      (quadraticKernel (T x)) (T y))=
      (winningCell B h i).indicator (quadraticKernel x) := by
    funext y
    by_cases hy : y∈winningCell B h i
    · have hTy := (winningCell_isometry_mem T B h i y).mpr hy
      simp only [Set.indicator_of_mem hy,Set.indicator_of_mem hTy,quadraticKernel_isometry]
    · have hTy : T y∉winningCell (fun j=>T (B j)) h i :=
        fun h=>hy ((winningCell_isometry_mem T B _ i y).mp h)
      simp only [Set.indicator_of_notMem hy,Set.indicator_of_notMem hTy]
  change (∫ y,(winningCell (fun j=>T (B j)) h i).indicator
    (quadraticKernel (T x)) (T y) ∂stdGaussian (FSC.Coord d))=_ at hh
  rw [he,integral_indicator (winningCell_measurable B h i),
    integral_indicator (winningCell_measurable (fun j=>T (B j)) h i)] at hh
  exact hh.symm

theorem quadraticLabelTest_isometry_symm (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    quadraticLabelTest (fun j=>T (B j)) h i x=quadraticLabelTest B h i (T.symm x) := by
  simpa only [T.apply_symm_apply] using quadraticLabelTest_isometry T B h i (T.symm x)

open NegativeVotingRegularSpectatorRepresentation

/-- Actual moment covariance gives the canonical tensor formula after any
explicit ambient orthogonal change of coordinates. -/
theorem isometricEmbedded_quadraticLabelTest_difference {n s : ℕ}
    (e : Fin (n+2)⊕Fin s≃Fin d) (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (hn : 1 ≤ n) (i j : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest (fun k=>T (embeddedCanonicalRows e k)) (fun _=>0) i x-
        quadraticLabelTest (fun k=>T (embeddedCanonicalRows e k)) (fun _=>0) j x=
      momentCoefficient n*((inner ℝ (T (embeddedCanonicalRows e i)) x)^2-
        (inner ℝ (T (embeddedCanonicalRows e j)) x)^2) := by
  rw [quadraticLabelTest_isometry_symm,quadraticLabelTest_isometry_symm,
    embeddedCanonicalRows_quadraticLabelTest_difference e hn]
  have hi (k : Fin (n+2)) : inner ℝ (embeddedCanonicalRows e k) (T.symm x)=
      inner ℝ (T (embeddedCanonicalRows e k)) x := by
    rw [←T.inner_map_map, T.apply_symm_apply]
  simp only [hi]

end NegativeVotingQuadraticMomentIsometry
