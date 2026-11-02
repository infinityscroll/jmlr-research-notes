import GaussianRegularQuadraticRepresentation
import GaussianRegularFacetCancellation

/-! Current-facet cancellation for the actual Gaussian quadratic label tests
of the centered canonical regular allocation. The reference tensor is
identified by its Gaussian integral, rather than supplied as a hypothesis. -/
noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace

namespace NegativeVotingCanonicalRegularFacetCancellation
open NegativeVotingFan NegativeVotingSecondChaosFacetGradient
  NegativeVotingRegularQuadraticRepresentation NegativeVotingRegularFacetCancellation

/-- The actual Gaussian score difference is the explicit regular jump. -/
theorem actualJump_eq_regularJump (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin (n+2)) (x : FSC.Coord (n+2)) :
    quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) i x-
        quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) j x=
      regularJump (canonicalEuclideanRows n) (momentCoefficient n) i j x :=
  canonicalEuclideanRows_quadraticLabelTest_difference n hn i j x

/-- The exact error factor holds on the current perturbed facet, with an
arbitrary nonzero reference scale. -/
theorem actualJump_on_current_facet (n : ℕ) (hn : 1 ≤ n)
    (B : Fin (n+2)→FSC.Coord (n+2)) (h : Fin (n+2)→ℝ)
    (α : ℝ) (hα : α≠0) (i j : Fin (n+2)) (x : FSC.Coord (n+2))
    (hx : x∈affineFacet B h i j) :
    quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) i x-
        quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) j x=
      -(momentCoefficient n/α)*errorGap B (canonicalEuclideanRows n) h α i j x*
        (inner ℝ (canonicalEuclideanRows n i) x+
          inner ℝ (canonicalEuclideanRows n j) x) := by
  rw [actualJump_eq_regularJump n hn]
  exact regularJump_on_facet B (canonicalEuclideanRows n) h α (momentCoefficient n)
    hα i j x hx

/-- Directional differentiation of the actual moment test is justified
before using its pointwise facet cancellation. -/
theorem hasDerivAt_actualJump_line (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin (n+2)) (x V : FSC.Coord (n+2)) :
    HasDerivAt (fun t : ℝ=>
      quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) i (x+t • V)-
        quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) j (x+t • V))
      (2*momentCoefficient n*
        (inner ℝ (canonicalEuclideanRows n i) x*inner ℝ (canonicalEuclideanRows n i) V-
          inner ℝ (canonicalEuclideanRows n j) x*inner ℝ (canonicalEuclideanRows n j) V)) 0 := by
  simp_rw [actualJump_eq_regularJump n hn]
  exact hasDerivAt_regularJump_line (canonicalEuclideanRows n) (momentCoefficient n) i j x V

/-- Material identity for the actual Gaussian reference test, with the
negative transport convention `inner (B_i-B_j) V=-ℓ`. -/
theorem hasDerivAt_actualJump_material_on_current_facet (n : ℕ) (hn : 1 ≤ n)
    (B : Fin (n+2)→FSC.Coord (n+2)) (h : Fin (n+2)→ℝ)
    (α ℓ : ℝ) (hα : α≠0) (i j : Fin (n+2)) (x V : FSC.Coord (n+2))
    (hx : x∈affineFacet B h i j) (hV : inner ℝ (B i-B j) V= -ℓ) :
    HasDerivAt (fun t : ℝ=>
      quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) i (x+t • V)-
        quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) j (x+t • V))
      (-(momentCoefficient n/α)*
        ((inner ℝ (canonicalEuclideanRows n i) x+inner ℝ (canonicalEuclideanRows n j) x)*ℓ+
          (inner ℝ (canonicalEuclideanRows n i) x+inner ℝ (canonicalEuclideanRows n j) x)*
            inner ℝ (rowError B (canonicalEuclideanRows n) α i-
              rowError B (canonicalEuclideanRows n) α j) V+
          errorGap B (canonicalEuclideanRows n) h α i j x*
            inner ℝ (canonicalEuclideanRows n i+canonicalEuclideanRows n j) V)) 0 := by
  have hd := hasDerivAt_actualJump_line n hn i j x V
  rw [regularJump_material_on_facet B (canonicalEuclideanRows n) h α
    (momentCoefficient n) ℓ hα i j x V hx hV] at hd
  exact hd

end NegativeVotingCanonicalRegularFacetCancellation
