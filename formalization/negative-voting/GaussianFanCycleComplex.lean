import Mathlib

/-! Concrete finite-simplex cycle boundaries and cone fillings.
These are genuine finite identities, independent of Gaussian covariance or
Hodge estimates. Alternating arrays encode oriented simplex coefficients. -/
noncomputable section
open scoped BigOperators

namespace NegativeVotingFanCycle
variable {V : Type*} [Fintype V] [DecidableEq V]

def AlternatingEdge (j : V → V → ℝ) : Prop := ∀ a b, j a b = -j b a

def AlternatingTriangle (lam : V → V → V → ℝ) : Prop :=
  (∀ a b c, lam a b c = -lam b a c) ∧ (∀ a b c, lam a b c = lam b c a)

def AlternatingTetrahedron (τ : V → V → V → V → ℝ) : Prop :=
  (∀ a b c d, τ a b c d = -τ b a c d) ∧
  (∀ a b c d, τ a b c d = -τ a c b d) ∧
  (∀ a b c d, τ a b c d = -τ a b d c)

def edgeBoundary (j : V → V → ℝ) (a : V) : ℝ := ∑ k, j k a

def triangleBoundary (lam : V → V → V → ℝ) (a b : V) : ℝ := ∑ k, lam k a b

def tetrahedronBoundary (τ : V → V → V → V → ℝ) (a b c : V) : ℝ :=
  ∑ k, τ k a b c

def vertexDelta (r a : V) : ℝ := if a = r then 1 else 0

def coneEdge (r : V) (j : V → V → ℝ) (a b c : V) : ℝ :=
  vertexDelta r a * j b c - vertexDelta r b * j a c + vertexDelta r c * j a b

def coneTriangle (r : V) (lam : V → V → V → ℝ) (a b c d : V) : ℝ :=
  vertexDelta r a * lam b c d - vertexDelta r b * lam a c d +
    vertexDelta r c * lam a b d - vertexDelta r d * lam a b c

theorem alternatingTriangle_swap_last (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (a b c : V) : lam a b c = -lam a c b := by
  calc
    lam a b c = lam c a b := (hlam.2 c a b).symm
    _ = -lam a c b := hlam.1 c a b

theorem coneEdge_alternating (r : V) (j : V → V → ℝ) (hj : AlternatingEdge j) :
    AlternatingTriangle (coneEdge r j) := by
  constructor
  · intro a b c
    unfold coneEdge
    rw [hj b a]
    ring
  · intro a b c
    unfold coneEdge
    rw [hj c a, hj b a]
    ring

theorem coneTriangle_alternating (r : V) (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) : AlternatingTetrahedron (coneTriangle r lam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    unfold coneTriangle
    rw [hlam.1 b a d, hlam.1 b a c]
    ring
  · intro a b c d
    unfold coneTriangle
    rw [hlam.1 c b d, alternatingTriangle_swap_last lam hlam a c b]
    ring
  · intro a b c d
    unfold coneTriangle
    rw [alternatingTriangle_swap_last lam hlam b d c,
      alternatingTriangle_swap_last lam hlam a d c]
    ring

/-- Explicit cone homotopy in edge degree. -/
theorem triangleBoundary_coneEdge (r : V) (j : V → V → ℝ) (a b : V) :
    triangleBoundary (coneEdge r j) a b = j a b -
      vertexDelta r a * edgeBoundary j b + vertexDelta r b * edgeBoundary j a := by
  simp [triangleBoundary, coneEdge, edgeBoundary, vertexDelta, ite_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Explicit cone homotopy in triangle degree. -/
theorem tetrahedronBoundary_coneTriangle (r : V) (lam : V → V → V → ℝ) (a b c : V) :
    tetrahedronBoundary (coneTriangle r lam) a b c = lam a b c -
      vertexDelta r a * triangleBoundary lam b c + vertexDelta r b * triangleBoundary lam a c -
        vertexDelta r c * triangleBoundary lam a b := by
  simp [tetrahedronBoundary, coneTriangle, triangleBoundary, vertexDelta, ite_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem double_sum_zero_of_skew (f : V → V → ℝ) (hf : ∀ a b, f a b = -f b a) :
    (∑ a, ∑ b, f a b) = 0 := by
  have he : (∑ a, ∑ b, f a b) = -(∑ a, ∑ b, f a b) := by
    calc
      _ = ∑ b, ∑ a, f a b := Finset.sum_comm
      _ = ∑ b, ∑ a, -f b a := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a _
        exact hf a b
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

theorem triangleBoundary_alternating (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) : AlternatingEdge (triangleBoundary lam) := by
  intro a b
  unfold triangleBoundary
  simp_rw [alternatingTriangle_swap_last lam hlam _ a b, Finset.sum_neg_distrib]

theorem tetrahedronBoundary_alternating (τ : V → V → V → V → ℝ)
    (hτ : AlternatingTetrahedron τ) : AlternatingTriangle (tetrahedronBoundary τ) := by
  constructor
  · intro a b c
    unfold tetrahedronBoundary
    simp_rw [hτ.2.1 _ a b c, Finset.sum_neg_distrib]
  · intro a b c
    unfold tetrahedronBoundary
    apply Finset.sum_congr rfl
    intro k _
    have h1 := hτ.2.1 k a b c
    have h2 := hτ.2.2 k b a c
    linarith

theorem edgeBoundary_triangleBoundary (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (a : V) : edgeBoundary (triangleBoundary lam) a = 0 := by
  exact double_sum_zero_of_skew (fun b k => lam k b a) (fun b k => hlam.1 k b a)

theorem triangleBoundary_tetrahedronBoundary (τ : V → V → V → V → ℝ)
    (hτ : AlternatingTetrahedron τ) (a b : V) :
    triangleBoundary (tetrahedronBoundary τ) a b = 0 := by
  exact double_sum_zero_of_skew (fun c k => τ k c a b) (fun c k => hτ.1 k c a b)

/-- Every literal divergence-free oriented edge flow has a triangle filling. -/
theorem exists_triangle_filling (r : V) (j : V → V → ℝ) (hj : AlternatingEdge j)
    (hcycle : ∀ a, edgeBoundary j a = 0) :
    ∃ lam : V → V → V → ℝ, AlternatingTriangle lam ∧ triangleBoundary lam = j := by
  refine ⟨coneEdge r j, coneEdge_alternating r j hj, ?_⟩
  funext a b
  rw [triangleBoundary_coneEdge, hcycle, hcycle]
  ring

/-- Every boundary-zero triangle chain is a tetrahedron boundary, with an
explicit cone witness. No topological or exactness premise is assumed. -/
theorem exists_tetrahedron_filling (r : V) (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (hcycle : ∀ a b, triangleBoundary lam a b = 0) :
    ∃ τ : V → V → V → V → ℝ, AlternatingTetrahedron τ ∧ tetrahedronBoundary τ = lam := by
  refine ⟨coneTriangle r lam, coneTriangle_alternating r lam hlam, ?_⟩
  funext a b c
  rw [tetrahedronBoundary_coneTriangle, hcycle, hcycle, hcycle]
  ring

theorem sum_triple_rotate (f : V → V → V → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ b, ∑ c, f c a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Triangle-wise subtraction of a common vector has zero total cycle pairing.
Cyclic invariance of the actual triangle mean, not a cancellation premise,
is the only requirement on the triangle-indexed vectors. -/
theorem triangle_potential_telescopes (lam : V → V → V → ℝ)
    (hlam : ∀ a b c, lam a b c = lam b c a)
    (g : V → V → V → E) (hg : ∀ a b c, g a b c = g b c a) (z : V → E) :
    (∑ a, ∑ b, ∑ c, lam a b c * inner ℝ (z a - z b) (g a b c)) = 0 := by
  let U := ∑ a, ∑ b, ∑ c, lam a b c * inner ℝ (z a - z b) (g a b c)
  let T := ∑ a, ∑ b, ∑ c, lam a b c * inner ℝ (z b - z c) (g a b c)
  let W := ∑ a, ∑ b, ∑ c, lam a b c * inner ℝ (z c - z a) (g a b c)
  have hUW : U = W := by
    unfold U W
    rw [sum_triple_rotate (fun a b c => lam a b c * inner ℝ (z a - z b) (g a b c))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [hlam c a b, hg c a b]
  have hWT : W = T := by
    unfold W T
    rw [sum_triple_rotate (fun a b c => lam a b c * inner ℝ (z c - z a) (g a b c))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [hlam c a b, hg c a b]
  have hsum : U + T + W = 0 := by
    unfold U T W
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    simp only [inner_sub_left]
    ring
  change U = 0
  linarith

/-- The literal boundary pairing equals the sum of facet/triangle mean
*differences*. This is the cross-term identity needed by the residual-energy
argument, with no assumed Gaussian matrix factorization or covariance bound. -/
theorem boundary_pairing_mean_differences (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam)
    (m : V → V → E) (g : V → V → V → E)
    (hg : ∀ a b c, g a b c = g b c a) (z : V → E) :
    (∑ a, ∑ b, triangleBoundary lam a b * inner ℝ (z a - z b) (m a b)) =
      ∑ a, ∑ b, ∑ c, lam c a b * inner ℝ (z a - z b) (m a b - g c a b) := by
  have hz : (∑ a, ∑ b, ∑ c, lam c a b * inner ℝ (z a - z b) (g c a b)) = 0 := by
    calc
      _ = ∑ a, ∑ b, ∑ c, lam a b c * inner ℝ (z a - z b) (g a b c) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        rw [hlam.2 c a b, hg c a b]
      _ = 0 := triangle_potential_telescopes lam hlam.2 g hg z
  unfold triangleBoundary
  simp_rw [Finset.sum_mul, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  rw [hz, sub_zero]

end InnerProduct
end NegativeVotingFanCycle
