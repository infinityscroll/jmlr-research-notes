import Mathlib
import GaussianCovariancePath
import GaussianFanCovarianceValue

/-! Concrete positive covariance factors and congruence transport. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Matrix
namespace NegativeVotingPositiveCovariance
open NegativeVotingCovariancePath NegativeVotingFanCovarianceValue
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def psdCone : Set (E →L[ℝ] E) :=
  {C | C.toLinearMap.IsSymmetric ∧ ∀ x, 0 ≤ inner ℝ x (C x)}
def pdCone : Set (E →L[ℝ] E) :=
  {C | C.toLinearMap.IsSymmetric ∧ ∀ x, x ≠ 0 → 0 < inner ℝ x (C x)}

theorem pdCone_subset_psdCone : pdCone (E:=E) ⊆ psdCone := by
  intro C hC
  refine ⟨hC.1,fun x => ?_⟩
  by_cases hx : x=0
  · simp [hx]
  · exact (hC.2 x hx).le

theorem psdCone_convex : Convex ℝ (psdCone (E:=E)) := by
  intro C hC D hD a b ha hb hab
  refine ⟨(hC.1.smul (by rfl : starRingEnd ℝ a = a)).add
    (hD.1.smul (by rfl : starRingEnd ℝ b = b)),fun x => ?_⟩
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    inner_add_right,real_inner_smul_right]
  exact add_nonneg (mul_nonneg ha (hC.2 x)) (mul_nonneg hb (hD.2 x))

theorem pdCone_convex : Convex ℝ (pdCone (E:=E)) := by
  intro C hC D hD a b ha hb hab
  refine ⟨(hC.1.smul (by rfl : starRingEnd ℝ a = a)).add
    (hD.1.smul (by rfl : starRingEnd ℝ b = b)),fun x hx => ?_⟩
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    inner_add_right,real_inner_smul_right]
  by_cases hapos : 0<a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos (hC.2 x hx))
      (mul_nonneg hb (hD.2 x hx).le)
  · have hbpos : 0<b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hC.2 x hx).le)
      (mul_pos hbpos (hD.2 x hx))

theorem regularize_positive {C : E →L[ℝ] E} (hC : C∈psdCone) {ε:ℝ} (hε:0<ε) :
    C+ε•ContinuousLinearMap.id ℝ E ∈ pdCone := by
  refine ⟨hC.1.add (LinearMap.IsSymmetric.smul (by rfl) (fun x y => rfl)),fun x hx => ?_⟩
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,inner_add_right,real_inner_smul_right]
  exact add_pos_of_nonneg_of_pos (hC.2 x) (mul_pos hε (real_inner_self_pos.mpr hx))

/-- A genuine invertible symmetric square root, with a symmetric inverse. -/
theorem exists_positive_factor (C : E →L[ℝ] E) (hC : C∈pdCone) :
    ∃ R : E ≃L[ℝ] E,
      R.toLinearMap.IsSymmetric ∧ R.symm.toLinearMap.IsSymmetric ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=C := by
  classical
  let e := hC.1.eigenvectorBasis (n:=Module.finrank ℝ E) rfl
  let ev := hC.1.eigenvalues (n:=Module.finrank ℝ E) rfl
  have heq : diagonal e ev = C := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change diagonal e ev (e i)=C (e i)
    rw [diagonal_basis]
    exact (hC.1.apply_eigenvectorBasis rfl i).symm
  have hev (i) : 0<ev i := by
    have hn : e i≠0 := by
      intro hh
      have hh' := e.norm_eq_one i
      rw [hh,norm_zero] at hh'
      norm_num at hh'
    have hp := hC.2 (e i) hn
    rw [←heq,diagonal_basis] at hp
    simpa only [real_inner_smul_right,e.inner_eq_ite,ite_true,mul_one] using hp
  let R := diagonal e (fun i => Real.sqrt (ev i))
  let Q := diagonal e (fun i => (Real.sqrt (ev i))⁻¹)
  have hn (i) : Real.sqrt (ev i)≠0 := ne_of_gt (Real.sqrt_pos.2 (hev i))
  have hRQ : R.comp Q=ContinuousLinearMap.id ℝ E := by
    dsimp [R,Q]
    rw [diagonal_comp]
    simp only [mul_inv_cancel₀ (hn _)]
    exact diagonal_one e
  have hQR : Q.comp R=ContinuousLinearMap.id ℝ E := by
    dsimp [R,Q]
    rw [diagonal_comp]
    simp only [inv_mul_cancel₀ (hn _)]
    exact diagonal_one e
  let T := ContinuousLinearEquiv.equivOfInverse' R Q hRQ hQR
  refine ⟨T,diagonal_symmetric e _,diagonal_symmetric e _,?_⟩
  change R.comp R=C
  dsimp [R]
  rw [diagonal_comp,←heq]
  congr 1
  funext i
  simpa only [←sq] using Real.sq_sqrt (hev i).le

/-- Transport of a genuine affine basis by an invertible linear map. -/
def mappedBasis {ι : Type*} (b : AffineBasis ι ℝ E) (R : E ≃L[ℝ] E) : AffineBasis ι ℝ E where
  toFun := R ∘ b
  ind' := b.ind.map' R.toLinearMap.toAffineMap R.injective
  tot' := by
    have hh := AffineMap.span_eq_top_of_surjective R.toLinearMap.toAffineMap R.surjective b.tot
    have he : (R.toLinearMap.toAffineMap : E → E)=(R : E → E) := by
      funext x
      rfl
    rw [he] at hh
    simpa only [Set.range_comp] using hh

@[simp] theorem mappedBasis_apply {ι : Type*} (b : AffineBasis ι ℝ E)
    (R : E ≃L[ℝ] E) (i : ι) : mappedBasis b R i=R (b i) := rfl

theorem symmetric_conjugate (Q D : E →L[ℝ] E)
    (hQ:Q.toLinearMap.IsSymmetric) (hD:D.toLinearMap.IsSymmetric) :
    (Q.comp (D.comp Q)).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (Q (D (Q x))) y=inner ℝ x (Q (D (Q y)))
  calc
    _ = inner ℝ (D (Q x)) (Q y) := hQ _ _
    _ = inner ℝ (Q x) (D (Q y)) := hD _ _
    _ = _ := hQ _ _

variable {m d : ℕ}

/-- Operator covariance acts on the literal label Gram matrix. -/
theorem gramVelocity_posSemidef (B : Fin m → FSC.Coord d)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC:C∈psdCone) :
    (gramVelocity B C).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,gramVelocity]
    exact (real_inner_comm _ _).trans (hC.1 (B i) (B j))
  · intro x
    have he : star x ⬝ᵥ (gramVelocity B C *ᵥ x) =
        inner ℝ (∑ i, x i • B i) (C (∑ j, x j • B j)) := by
      rw [map_sum,sum_inner]
      simp only [dotProduct,Matrix.mulVec,gramVelocity,Pi.star_apply,star_trivial,
        map_smul,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact hC.2 _

theorem factor_gram (B : Fin m → FSC.Coord d)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR:R.toLinearMap.IsSymmetric) (hRC:R.toContinuousLinearMap.comp R.toContinuousLinearMap=C) :
    Matrix.gram ℝ (fun i => R (B i))=gramVelocity B C := by
  ext i j
  change inner ℝ (R (B i)) (R (B j))=inner ℝ (B i) (C (B j))
  calc
    _ = inner ℝ (B i) (R (R (B j))) := hR _ _
    _ = _ := congrArg (fun A : FSC.Coord d →L[ℝ] FSC.Coord d => inner ℝ (B i) (A (B j))) hRC

theorem conjugate_gramVelocity (B : Fin m → FSC.Coord d)
    (D : FSC.Coord d →L[ℝ] FSC.Coord d) (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR:R.toLinearMap.IsSymmetric) :
    gramVelocity (fun i => R (B i))
      (R.symm.toContinuousLinearMap.comp (D.comp R.symm.toContinuousLinearMap))=
      gramVelocity B D := by
  ext i j
  change inner ℝ (R (B i)) (R.symm (D (R.symm (R (B j)))))=inner ℝ (B i) (D (B j))
  calc
    _ = inner ℝ (B i) (R (R.symm (D (R.symm (R (B j)))))) := hR _ _
    _ = _ := by rw [R.symm_apply_apply,R.apply_symm_apply]

end NegativeVotingPositiveCovariance
