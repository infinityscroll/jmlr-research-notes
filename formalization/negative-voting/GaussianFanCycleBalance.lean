import GaussianFanCycleFactorization

/-! Actual Gaussian weighted cycle representatives and their exact energy balance. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem cycleA_eq_cycleB_of_actual_gauge (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) (hlam : AlternatingTriangle lam)
    (heta : AlternatingTriangle eta)
    (hg : ∀ a j k l, cycleWeightedCoboundary b h lam a j k l = 0) :
    cycleA b h lam eta = cycleB b h lam eta := by
  have he := actual_fan_cycle_factorization b h lam eta hlam heta
  have hz : cycleFactorizationRHS b h lam eta = 0 := by
    simp [cycleFactorizationRHS,hg]
  rw [hz] at he
  linarith

/-- A genuinely constructed positive-weight gauge for every actual edge cycle.
Its B energy is exactly the inverse-weight edge energy, with no supplied gauge. -/
theorem exists_actual_gaussian_cycle_balance (b : AffineBasis V ℝ E) (h : V → ℝ)
    (r : V) (j : V → V → ℝ) (hj : AlternatingEdge j)
    (hcycle : ∀ a, edgeBoundary j a = 0) :
    ∃ lam : V → V → V → ℝ, AlternatingTriangle lam ∧ triangleBoundary lam = j ∧
      (∀ a k l t, cycleWeightedCoboundary b h lam a k l t = 0) ∧
      cycleB b h lam lam = (1/2:ℝ)*∑ a, ∑ k, (j a k)^2/cycleEdgeWeight b h a k := by
  obtain ⟨lam,hlam,hfill,hg⟩ := exists_weighted_cycle_gauge_components r j hj hcycle
    (cycleTriangleWeight b h) (cycleTriangleWeight_pos b h)
    (cycleTriangleWeight_swap_first b h) (cycleTriangleWeight_cyclic b h)
  change ∀ a k l t, cycleWeightedCoboundary b h lam a k l t = 0 at hg
  refine ⟨lam,hlam,hfill,hg,?_⟩
  rw [← cycleA_eq_cycleB_of_actual_gauge b h lam lam hlam hlam hg,cycleA,hfill]
  simp only [pow_two]

end NegativeVotingFanCycle
