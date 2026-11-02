import GaussianQuadraticMomentIsometry
import GaussianQuadraticMomentPadding
import GaussianProcrustesDistance

/-! Actual quadratic score representation for any equal-Gram regular row
family. Exact Gaussian padding also covers the minimal ambient dimension. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Classical RealInnerProductSpace

namespace NegativeVotingRegularOrbitRepresentation
open NegativeVotingProcrustes NegativeVotingQuadraticMomentIsometry
  NegativeVotingRegularSpectatorRepresentation NegativeVotingRegularQuadraticRepresentation
  NegativeVotingSecondChaosFacetGradient NegativeVotingQuadraticMomentPadding

section EqualGram
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowCombination (R : ι→FSC.Coord d) : (ι→ℝ)→ₗ[ℝ]FSC.Coord d where
  toFun q:=∑ i,q i • R i
  map_add' q p:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c q:=by simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul,
    RingHom.id_apply]

theorem rowCombination_single (R : ι→FSC.Coord d) (i : ι) :
    rowCombination R (Pi.single i 1)=R i := by
  simp [rowCombination,Pi.single_apply]

/-- Equal Gram data produce an actual ambient orthogonal equivalence, even
when the row span is proper. -/
theorem exists_orthogonal_of_equal_gram (R B : ι→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=inner ℝ (B i) (B j)) :
    ∃T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d,∀i,T (R i)=B i := by
  have hn (q : ι→ℝ) : ‖rowCombination R q‖=‖rowCombination B q‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq]
    simp only [rowCombination,LinearMap.coe_mk,AddHom.coe_mk,sum_inner,inner_sum,
      real_inner_smul_left,real_inner_smul_right,hG]
  obtain ⟨U,hU⟩:=exists_isometry_of_equal_norms (rowCombination R) (rowCombination B) hn
  refine ⟨U.toLinearIsometryEquiv rfl,?_⟩
  intro i
  simpa only [LinearIsometry.coe_toLinearIsometryEquiv,rowCombination_single] using
    hU (Pi.single i 1)

end EqualGram

section Embedded
variable {n s d : ℕ} (e : Fin (n+2)⊕Fin s≃Fin d)

theorem embeddedUnitRows_gram (i j : Fin (n+2)) :
    inner ℝ (embeddedUnitRows e i) (embeddedUnitRows e j)=(if i=j then 1 else 0) := by
  rw [embeddedUnitRows_inner]
  simp [embeddedUnitRows,e.injective.eq_iff,eq_comm]

theorem embeddedCanonicalRows_gram (i j : Fin (n+2)) :
    inner ℝ (embeddedCanonicalRows e i) (embeddedCanonicalRows e j)=
      (if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
  have hm : ((n+2:ℕ):ℝ)≠0 := by positivity
  simp only [embeddedCanonicalRows,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum,embeddedUnitRows_gram]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp
  ring

include e in
/-- This endpoint uses only the actual regular Gram matrix and an explicit
coordinate capacity certificate. The isometry is constructed, not assumed. -/
theorem regular_quadraticLabelTest_difference_of_embedding (hn : 1 ≤ n)
    (B : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (i j : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest B (fun _=>0) i x-quadraticLabelTest B (fun _=>0) j x=
      momentCoefficient n*((inner ℝ (B i) x)^2-(inner ℝ (B j) x)^2) := by
  obtain ⟨T,hT⟩:=exists_orthogonal_of_equal_gram (embeddedCanonicalRows e) B
    (fun a b=>(embeddedCanonicalRows_gram e a b).trans (hG a b).symm)
  have hh:=isometricEmbedded_quadraticLabelTest_difference e T hn i j x
  simpa only [hT] using hh

end Embedded

/-- Every regular realization with at least `m` ambient dimensions has the
actual canonical Gaussian quadratic score gap. The minimal `m-1` ambient
dimension is intentionally not covered by this statement. -/
theorem regular_quadraticLabelTest_difference {n d : ℕ} (hn : 1 ≤ n)
    (hd : n+2 ≤ d) (B : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (i j : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest B (fun _=>0) i x-quadraticLabelTest B (fun _=>0) j x=
      momentCoefficient n*((inner ℝ (B i) x)^2-(inner ℝ (B j) x)^2) := by
  let s:=d-(n+2)
  have hc : Fintype.card (Fin (n+2)⊕Fin s)=Fintype.card (Fin d) := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    dsimp [s]
    omega
  let e : Fin (n+2)⊕Fin s≃Fin d:=Fintype.equivOfCardEq hc
  exact regular_quadraticLabelTest_difference_of_embedding e hn B hG i j x

/-- Actual Gaussian regular-label score gaps in every finite ambient
dimension. Padding and its exact moment pullback discharge the dimension
restriction of the intermediate orbit theorem. -/
theorem regular_quadraticLabelTest_difference_all_dimensions {n d : ℕ} (hn : 1 ≤ n)
    (B : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (i j : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest B (fun _=>0) i x-quadraticLabelTest B (fun _=>0) j x=
      momentCoefficient n*((inner ℝ (B i) x)^2-(inner ℝ (B j) x)^2) := by
  let e : Fin d⊕Fin (n+2)≃Fin (d+(n+2)):=finSumFinEquiv
  let C : Fin (n+2)→FSC.Coord (d+(n+2)):=fun i=>padVector e (B i)
  have hC (a b : Fin (n+2)) : inner ℝ (C a) (C b)=
      (if a=b then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    dsimp [C]
    rw [padVector_inner_padVector,hG]
  have hh:=regular_quadraticLabelTest_difference hn (by omega : n+2 ≤ d+(n+2))
    C hC i j (padVector e x)
  simpa only [C,quadraticLabelTest_padVector_at_padVector,padVector_inner_padVector] using hh

open NegativeVotingFan NegativeVotingRegularFacetCancellation

/-- Equation (12) for the actual Gaussian reference labels, any regular
realization, and the current perturbed affine facet. -/
theorem actual_regularJump_on_current_facet {n d : ℕ} (hn : 1 ≤ n)
    (R B : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (h : Fin (n+2)→ℝ) (α : ℝ) (hα : α≠0) (i j : Fin (n+2)) (x : FSC.Coord d)
    (hx : x∈affineFacet B h i j) :
    quadraticLabelTest R (fun _=>0) i x-quadraticLabelTest R (fun _=>0) j x=
      -(momentCoefficient n/α)*errorGap B R h α i j x*
        (inner ℝ (R i) x+inner ℝ (R j) x) := by
  rw [regular_quadraticLabelTest_difference_all_dimensions hn R hG]
  exact regularJump_on_facet B R h α (momentCoefficient n) hα i j x hx

/-- Equation (18) as an actual directional derivative of the Gaussian
reference-label difference. No ambient-dimensional or full-span hypothesis
and no inverse-lift bound enter this cancellation. -/
theorem hasDerivAt_actual_regularJump_material {n d : ℕ} (hn : 1 ≤ n)
    (R B : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (h : Fin (n+2)→ℝ) (α ℓ : ℝ) (hα : α≠0) (i j : Fin (n+2)) (x V : FSC.Coord d)
    (hx : x∈affineFacet B h i j) (hV : inner ℝ (B i-B j) V= -ℓ) :
    HasDerivAt (fun t : ℝ=>
      quadraticLabelTest R (fun _=>0) i (x+t • V)-
        quadraticLabelTest R (fun _=>0) j (x+t • V))
      (-(momentCoefficient n/α)*
        ((inner ℝ (R i) x+inner ℝ (R j) x)*ℓ+
          (inner ℝ (R i) x+inner ℝ (R j) x)*inner ℝ (rowError B R α i-rowError B R α j) V+
          errorGap B R h α i j x*inner ℝ (R i+R j) V)) 0 := by
  have he : (fun t : ℝ=>quadraticLabelTest R (fun _=>0) i (x+t • V)-
      quadraticLabelTest R (fun _=>0) j (x+t • V))=
      (fun t : ℝ=>regularJump R (momentCoefficient n) i j (x+t • V)) := by
    funext t
    exact regular_quadraticLabelTest_difference_all_dimensions hn R hG i j (x+t • V)
  rw [he]
  have hd:=hasDerivAt_regularJump_line R (momentCoefficient n) i j x V
  rw [regularJump_material_on_facet B R h α (momentCoefficient n) ℓ hα i j x V hx hV] at hd
  exact hd

end NegativeVotingRegularOrbitRepresentation
