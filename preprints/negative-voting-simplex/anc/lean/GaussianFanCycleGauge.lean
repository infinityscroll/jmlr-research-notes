import GaussianFanCycleComplex
import NegativeVoting.WeightedGauge

/-! Concrete weighted gauges for the actual finite-simplex boundary maps.
The triangle pairing uses D/6 on every ordered triple, matching an unoriented
triangle energy when D is invariant under vertex permutations. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace NegativeVotingFanCycle
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev EdgeSpace (V : Type*) [Fintype V] := EuclideanSpace ℝ (V × V)
abbrev TriangleSpace (V : Type*) [Fintype V] := EuclideanSpace ℝ (V × V × V)
abbrev TetrahedronSpace (V : Type*) [Fintype V] := EuclideanSpace ℝ (V × V × V × V)

def asTriangle (u : TriangleSpace V) (a b c : V) : ℝ := u (a,b,c)
def asTetrahedron (u : TetrahedronSpace V) (a b c d : V) : ℝ := u (a,b,c,d)
def fromTriangle (lam : V → V → V → ℝ) : TriangleSpace V :=
  WithLp.toLp 2 (fun t => lam t.1 t.2.1 t.2.2)
def fromTetrahedron (τ : V → V → V → V → ℝ) : TetrahedronSpace V :=
  WithLp.toLp 2 (fun t => τ t.1 t.2.1 t.2.2.1 t.2.2.2)

theorem alternatingTriangle_add (f g : V → V → V → ℝ)
    (hf : AlternatingTriangle f) (hg : AlternatingTriangle g) :
    AlternatingTriangle (f + g) := by
  constructor
  · intro a b c
    change f a b c + g a b c = -(f b a c + g b a c)
    rw [hf.1 a b c, hg.1 a b c]
    ring
  · intro a b c
    change f a b c + g a b c = f b c a + g b c a
    rw [hf.2 a b c, hg.2 a b c]

/-- The domain of the third boundary is the actual alternating tetrahedron
chain subspace, not an assumed chain relation between arbitrary operators. -/
def tetrahedronChains : Submodule ℝ (TetrahedronSpace V) where
  carrier := {u | AlternatingTetrahedron (asTetrahedron (u : TetrahedronSpace V))}
  zero_mem' := by
    change AlternatingTetrahedron (fun _ _ _ _ => (0 : ℝ))
    simp [AlternatingTetrahedron]
  add_mem' := by
    intro u v hu hv
    refine ⟨?_, ?_, ?_⟩ <;> intro a b c d
    · change u (a,b,c,d) + v (a,b,c,d) = -(u (b,a,c,d) + v (b,a,c,d))
      have h1 := hu.1 a b c d
      have h2 := hv.1 a b c d
      change u (a,b,c,d) = -u (b,a,c,d) at h1
      change v (a,b,c,d) = -v (b,a,c,d) at h2
      rw [h1,h2]
      ring
    · change u (a,b,c,d) + v (a,b,c,d) = -(u (a,c,b,d) + v (a,c,b,d))
      have h1 := hu.2.1 a b c d
      have h2 := hv.2.1 a b c d
      change u (a,b,c,d) = -u (a,c,b,d) at h1
      change v (a,b,c,d) = -v (a,c,b,d) at h2
      rw [h1,h2]
      ring
    · change u (a,b,c,d) + v (a,b,c,d) = -(u (a,b,d,c) + v (a,b,d,c))
      have h1 := hu.2.2 a b c d
      have h2 := hv.2.2 a b c d
      change u (a,b,c,d) = -u (a,b,d,c) at h1
      change v (a,b,c,d) = -v (a,b,d,c) at h2
      rw [h1,h2]
      ring
  smul_mem' := by
    intro r u hu
    refine ⟨?_, ?_, ?_⟩ <;> intro a b c d
    · change r * u (a,b,c,d) = -(r * u (b,a,c,d))
      have h := hu.1 a b c d
      change u (a,b,c,d) = -u (b,a,c,d) at h
      rw [h]
      ring
    · change r * u (a,b,c,d) = -(r * u (a,c,b,d))
      have h := hu.2.1 a b c d
      change u (a,b,c,d) = -u (a,c,b,d) at h
      rw [h]
      ring
    · change r * u (a,b,c,d) = -(r * u (a,b,d,c))
      have h := hu.2.2 a b c d
      change u (a,b,c,d) = -u (a,b,d,c) at h
      rw [h]
      ring

def triangleBoundaryLinear : TriangleSpace V →ₗ[ℝ] EdgeSpace V where
  toFun u := WithLp.toLp 2 (fun ab => triangleBoundary (asTriangle u) ab.1 ab.2)
  map_add' u v := by
    ext ab
    rcases ab with ⟨a,b⟩
    change (∑ k, (u (k,a,b) + v (k,a,b))) = (∑ k, u (k,a,b)) + ∑ k, v (k,a,b)
    exact Finset.sum_add_distrib
  map_smul' r u := by
    ext ab
    rcases ab with ⟨a,b⟩
    change (∑ k, r * u (k,a,b)) = r * ∑ k, u (k,a,b)
    exact (Finset.mul_sum _ _ _).symm

def tetrahedronBoundaryLinear : tetrahedronChains (V := V) →ₗ[ℝ] TriangleSpace V where
  toFun u := fromTriangle (tetrahedronBoundary (asTetrahedron (u : TetrahedronSpace V)))
  map_add' u v := by
    ext abc
    rcases abc with ⟨a,b,c⟩
    change (∑ k, ((u : TetrahedronSpace V) (k,a,b,c) + (v : TetrahedronSpace V) (k,a,b,c))) =
      (∑ k, (u : TetrahedronSpace V) (k,a,b,c)) + ∑ k, (v : TetrahedronSpace V) (k,a,b,c)
    exact Finset.sum_add_distrib
  map_smul' r u := by
    ext abc
    rcases abc with ⟨a,b,c⟩
    change (∑ k, r * (u : TetrahedronSpace V) (k,a,b,c)) = r * ∑ k, (u : TetrahedronSpace V) (k,a,b,c)
    exact (Finset.mul_sum _ _ _).symm

theorem boundaryLinear_comp_zero :
    (triangleBoundaryLinear (V := V)).comp tetrahedronBoundaryLinear = 0 := by
  ext u ab
  rcases ab with ⟨a,b⟩
  change triangleBoundary (tetrahedronBoundary (asTetrahedron (u : TetrahedronSpace V))) a b = 0
  exact triangleBoundary_tetrahedronBoundary (asTetrahedron (u : TetrahedronSpace V)) u.property a b

section CoordinateScaling
variable {T : Type*} [Fintype T]

def positiveDiagonalEquiv (s : T → ℝ) (hs : ∀ t, s t ≠ 0) :
    EuclideanSpace ℝ T ≃L[ℝ] EuclideanSpace ℝ T :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun u => WithLp.toLp 2 (fun t => s t * u t)
    invFun := fun u => WithLp.toLp 2 (fun t => u t / s t)
    left_inv := by
      intro u
      ext t
      change (s t * u t) / s t = u t
      field_simp [hs t]
    right_inv := by
      intro u
      ext t
      change s t * (u t / s t) = u t
      field_simp [hs t]
    map_add' := by
      intro u v
      ext t
      change s t * (u t + v t) = s t * u t + s t * v t
      ring
    map_smul' := by
      intro r u
      ext t
      change s t * (r * u t) = r * (s t * u t)
      ring }
end CoordinateScaling

def normalizedTrianglePairing (D : V → V → V → ℝ)
    (f g : V → V → V → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, (D a b c / 6) * f a b c * g a b c

def triangleWeightEquiv (D : V → V → V → ℝ) (hD : ∀ a b c, 0 < D a b c) :
    TriangleSpace V ≃L[ℝ] TriangleSpace V :=
  positiveDiagonalEquiv (fun t : V × V × V => Real.sqrt (D t.1 t.2.1 t.2.2 / 6))
    (fun t => (Real.sqrt_pos.2 (div_pos (hD t.1 t.2.1 t.2.2) (by norm_num))).ne')

theorem triangleWeightEquiv_inner (D : V → V → V → ℝ) (hD : ∀ a b c, 0 < D a b c)
    (u v : TriangleSpace V) :
    inner ℝ (triangleWeightEquiv D hD u) (triangleWeightEquiv D hD v) =
      normalizedTrianglePairing D (asTriangle u) (asTriangle v) := by
  rw [PiLp.inner_apply]
  change (∑ t : V × V × V,
    (Real.sqrt (D t.1 t.2.1 t.2.2 / 6) * v t) *
      (Real.sqrt (D t.1 t.2.1 t.2.2 / 6) * u t)) = _
  calc
    _ = ∑ t : V × V × V, (D t.1 t.2.1 t.2.2 / 6) * u t * v t := by
      apply Finset.sum_congr rfl
      intro t _
      have hs := Real.sq_sqrt (show 0 ≤ D t.1 t.2.1 t.2.2 / 6 from
        le_of_lt (div_pos (hD t.1 t.2.1 t.2.2) (by norm_num)))
      calc
        _ = (Real.sqrt (D t.1 t.2.1 t.2.2 / 6))^2 * u t * v t := by ring
        _ = _ := by rw [hs]
    _ = _ := by simp [normalizedTrianglePairing, asTriangle, Fintype.sum_prod_type]

/-- Actual finite-simplex weighted cycle gauge. The boundary relation, filling,
alternating subspaces and positive weighted inner product are all constructed.
For symmetric physical weights, the D/6 pairing is the manuscript's
unoriented-triangle pairing. No Gaussian factorization is assumed. -/
theorem exists_concrete_weighted_cycle_gauge (r : V) (j : V → V → ℝ)
    (hj : AlternatingEdge j) (hcycle : ∀ a, edgeBoundary j a = 0)
    (D : V → V → V → ℝ) (hD : ∀ a b c, 0 < D a b c) :
    ∃ lam : V → V → V → ℝ, AlternatingTriangle lam ∧ triangleBoundary lam = j ∧
      ∀ τ : V → V → V → V → ℝ, AlternatingTetrahedron τ →
        normalizedTrianglePairing D lam (tetrahedronBoundary τ) = 0 := by
  let u := fromTriangle (coneEdge r j)
  let S := LinearMap.range (tetrahedronBoundaryLinear (V := V))
  obtain ⟨v, hv, horth⟩ := NegativeVoting.exists_weighted_orthogonal_gauge S
    (triangleWeightEquiv D hD) u
  obtain ⟨τ, hτ⟩ := hv
  have hb : triangleBoundaryLinear (v - u) = 0 := by
    rw [← hτ]
    exact congrArg (fun L : tetrahedronChains (V := V) →ₗ[ℝ] EdgeSpace V => L τ)
      (boundaryLinear_comp_zero (V := V))
  have hbu : triangleBoundaryLinear v = triangleBoundaryLinear u := by
    simpa only [map_sub, sub_eq_zero] using hb
  have haltdiff : AlternatingTriangle (asTriangle (tetrahedronBoundaryLinear τ)) :=
    tetrahedronBoundary_alternating (asTetrahedron (τ : TetrahedronSpace V)) τ.property
  have hdecomp : asTriangle v = asTriangle (tetrahedronBoundaryLinear τ) + asTriangle u := by
    funext a b c
    have h := congrArg (fun q : TriangleSpace V => q (a,b,c)) hτ
    change tetrahedronBoundaryLinear τ (a,b,c) = v (a,b,c) - u (a,b,c) at h
    change v (a,b,c) = tetrahedronBoundaryLinear τ (a,b,c) + u (a,b,c)
    linarith
  refine ⟨asTriangle v, ?_, ?_, ?_⟩
  · rw [hdecomp]
    exact alternatingTriangle_add _ _ haltdiff (coneEdge_alternating r j hj)
  · funext a b
    have h := congrArg (fun q : EdgeSpace V => q (a,b)) hbu
    change triangleBoundary (asTriangle v) a b = triangleBoundary (coneEdge r j) a b at h
    rw [triangleBoundary_coneEdge, hcycle, hcycle] at h
    simpa using h
  · intro σ hσ
    let q : tetrahedronChains (V := V) := ⟨fromTetrahedron σ, hσ⟩
    have hq := horth (tetrahedronBoundaryLinear q) ⟨q,rfl⟩
    rw [triangleWeightEquiv_inner] at hq
    exact hq

/-- The full three-edge triangle sum is three times the distinguished-edge
sum. This records the factor that disappears if ordered tuples are confused
with unoriented triangles. -/
theorem full_triangle_pairing_eq_three (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (c : V → V → ℝ) :
    (∑ a, ∑ b, ∑ k, lam a b k * (c a b + c b k + c k a)) =
      3 * ∑ a, ∑ b, triangleBoundary lam a b * c a b := by
  let S := ∑ a, ∑ b, ∑ k, lam a b k * c a b
  have h1 : (∑ a, ∑ b, ∑ k, lam a b k * c b k) = S := by
    rw [sum_triple_rotate (fun a b k => lam a b k * c b k)]
    unfold S
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro k _
    rw [hlam.2 k a b]
  have h2 : (∑ a, ∑ b, ∑ k, lam a b k * c k a) = S := by
    calc
      _ = ∑ a, ∑ b, ∑ k, lam a b k * c b k := by
        rw [sum_triple_rotate (fun a b k => lam a b k * c k a)]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro k _
        rw [hlam.2 k a b]
      _ = S := h1
  have he : (∑ a, ∑ b, triangleBoundary lam a b * c a b) = S := by
    unfold triangleBoundary S
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro k _
    rw [hlam.2 k a b]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [h1,h2,he]
  change S + S + S = 3*S
  ring

theorem normalized_boundary_pairing (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (c : V → V → ℝ) :
    (1/6 : ℝ) * (∑ a, ∑ b, ∑ k, lam a b k * (c a b + c b k + c k a)) =
      (1/2 : ℝ) * ∑ a, ∑ b, triangleBoundary lam a b * c a b := by
  rw [full_triangle_pairing_eq_three lam hlam c]
  ring

def triangleCoboundary (f : V → V → V → ℝ) (a b c d : V) : ℝ :=
  f b c d - f a c d + f a b d - f a b c

theorem triangleCoboundary_alternating (f : V → V → V → ℝ)
    (hf : AlternatingTriangle f) : AlternatingTetrahedron (triangleCoboundary f) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a b c d
  · unfold triangleCoboundary
    rw [hf.1 b a d, hf.1 b a c]
    ring
  · unfold triangleCoboundary
    rw [hf.1 c b d, alternatingTriangle_swap_last f hf a c b]
    ring
  · unfold triangleCoboundary
    rw [alternatingTriangle_swap_last f hf b d c,
      alternatingTriangle_swap_last f hf a d c]
    ring

theorem tetrahedron_rotate (τ : V → V → V → V → ℝ)
    (hτ : AlternatingTetrahedron τ) (a b c d : V) : τ d a b c = -τ a b c d := by
  have h1 := hτ.1 d a b c
  have h2 := hτ.2.1 a d b c
  have h3 := hτ.2.2 a b d c
  linarith

theorem sum_four_rotate (f : V → V → V → V → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f d a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]

/-- Exact adjunction normalization: each ordered tetrahedron has four faces.
With normalized triangle/tetrahedron pairings this becomes1/6 versus1/24. -/
theorem triangle_tetrahedron_adjoint (f : V → V → V → ℝ)
    (hf : AlternatingTriangle f) (τ : V → V → V → V → ℝ)
    (hτ : AlternatingTetrahedron τ) :
    4 * (∑ a, ∑ b, ∑ c, f a b c * tetrahedronBoundary τ a b c) =
      ∑ a, ∑ b, ∑ c, ∑ d, τ a b c d * triangleCoboundary f a b c d := by
  let S0 := ∑ a, ∑ b, ∑ c, ∑ d, τ a b c d * f b c d
  let S1 := ∑ a, ∑ b, ∑ c, ∑ d, τ a b c d * f a c d
  let S2 := ∑ a, ∑ b, ∑ c, ∑ d, τ a b c d * f a b d
  let S3 := ∑ a, ∑ b, ∑ c, ∑ d, τ a b c d * f a b c
  have h03 : S0 = -S3 := by
    unfold S0 S3
    rw [sum_four_rotate (fun a b c d => τ a b c d * f b c d)]
    have he (a b c d : V) : τ d a b c * f a b c = -(τ a b c d * f a b c) := by
      rw [tetrahedron_rotate τ hτ]
      ring
    simp_rw [he, Finset.sum_neg_distrib]
  have h32 : S3 = -S2 := by
    unfold S3 S2
    rw [sum_four_rotate (fun a b c d => τ a b c d * f a b c)]
    have he (a b c d : V) : τ d a b c * f d a b = -(τ a b c d * f a b d) := by
      rw [tetrahedron_rotate τ hτ, hf.2 d a b]
      ring
    simp_rw [he, Finset.sum_neg_distrib]
  have h21 : S2 = -S1 := by
    unfold S2 S1
    rw [sum_four_rotate (fun a b c d => τ a b c d * f a b d)]
    have he (a b c d : V) : τ d a b c * f d a c = -(τ a b c d * f a c d) := by
      rw [tetrahedron_rotate τ hτ, hf.2 d a c]
      ring
    simp_rw [he, Finset.sum_neg_distrib]
  have hp : (∑ a, ∑ b, ∑ c, f a b c * tetrahedronBoundary τ a b c) = S0 := by
    unfold S0 tetrahedronBoundary
    rw [sum_four_rotate (fun a b c d => τ a b c d * f b c d)]
    simp_rw [Finset.mul_sum, mul_comm]
  have hs : (∑ a, ∑ b, ∑ c, ∑ d, τ a b c d * triangleCoboundary f a b c d) =
      S0 - S1 + S2 - S3 := by
    unfold triangleCoboundary S0 S1 S2 S3
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hp,hs]
  linarith

/-- The concrete gauge has the exact signed-face component equation
partial3^T D lam=0. Both tuple normalization factors are derived above. -/
theorem exists_weighted_cycle_gauge_components (r : V) (j : V → V → ℝ)
    (hj : AlternatingEdge j) (hcycle : ∀ a, edgeBoundary j a = 0)
    (D : V → V → V → ℝ) (hD : ∀ a b c, 0 < D a b c)
    (hDswap : ∀ a b c, D a b c = D b a c)
    (hDcycle : ∀ a b c, D a b c = D b c a) :
    ∃ lam : V → V → V → ℝ, AlternatingTriangle lam ∧ triangleBoundary lam = j ∧
      ∀ a b c d, triangleCoboundary (fun i k l => D i k l * lam i k l) a b c d = 0 := by
  obtain ⟨lam, hlam, hfill, horth⟩ := exists_concrete_weighted_cycle_gauge r j hj hcycle D hD
  let f : V → V → V → ℝ := fun a b c => D a b c * lam a b c
  have hf : AlternatingTriangle f := by
    constructor
    · intro a b c
      unfold f
      rw [hDswap a b c, hlam.1 a b c]
      ring
    · intro a b c
      unfold f
      rw [hDcycle a b c, hlam.2 a b c]
  let τ := triangleCoboundary f
  have hτ : AlternatingTetrahedron τ := triangleCoboundary_alternating f hf
  have ho := horth τ hτ
  have hp : (∑ a, ∑ b, ∑ c, f a b c * tetrahedronBoundary τ a b c) = 0 := by
    calc
      _ = 6 * normalizedTrianglePairing D lam (tetrahedronBoundary τ) := by
        unfold normalizedTrianglePairing f
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = 0 := by rw [ho,mul_zero]
  have hs := triangle_tetrahedron_adjoint f hf τ hτ
  rw [hp,mul_zero] at hs
  have hsq : (∑ t : V × V × V × V, (τ t.1 t.2.1 t.2.2.1 t.2.2.2)^2) = 0 := by
    simpa only [Fintype.sum_prod_type, τ, pow_two] using hs.symm
  refine ⟨lam, hlam, hfill, ?_⟩
  intro a b c d
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t (_ : t ∈ Finset.univ) => sq_nonneg (τ t.1 t.2.1 t.2.2.1 t.2.2.2))).mp
      hsq (a,b,c,d) (Finset.mem_univ _)
  exact sq_eq_zero_iff.mp ht

end NegativeVotingFanCycle
