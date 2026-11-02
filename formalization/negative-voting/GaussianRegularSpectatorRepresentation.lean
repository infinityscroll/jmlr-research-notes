import GaussianRegularQuadraticRepresentation
import GaussianRegularFacetCancellation

/-! Product-Gaussian cancellation of all spectator components of the actual
canonical regular quadratic tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical RealInnerProductSpace

namespace NegativeVotingRegularSpectatorRepresentation
open NegativeVoting NegativeVotingModern NegativeVotingRegularMaximum
  NegativeVotingRegularQuadratic NegativeVotingRegularQuadraticRepresentation
  OAI.MinUncut.GaussianHermite

section Product
variable {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq κ] [DecidableEq ν]

theorem gaussian_sum_integral (f : (κ⊕ν→ℝ)→ℝ) :
    (∫ x,f x ∂γpi (κ⊕ν))=
      ∫ p,f (Sum.elim p.1 p.2) ∂(γpi κ).prod (γpi ν) := by
  have h := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : κ⊕ν=>gaussianReal 0 1)).integral_comp' f
  exact h.symm

theorem psi_integral_zero (a : κ→ℕ) (ha : a≠0) :
    (∫ x,psi a x ∂γpi κ)=0 := by
  have hz (x : κ→ℝ) : psi (0 : κ→ℕ) x=1 := by simp [psi,H]
  have hh := psi_product a 0
  simpa only [hz,mul_one,if_neg ha] using hh

theorem quadraticCoordinate_integral_zero (a b : κ) :
    (∫ x,quadraticCoordinate a b x ∂γpi κ)=0 := by
  by_cases hab : a=b
  · subst b
    have hn : (Pi.single a 2 : κ→ℕ)≠0 := by
      intro h
      have hh := congrFun h a
      simp at hh
    have hh := psi_integral_zero (Pi.single a 2) hn
    simp only [psi_single_two,integral_div] at hh
    exact (div_eq_zero_iff).mp hh |>.resolve_right (by positivity)
  · have hn : (Pi.single a 1+Pi.single b 1 : κ→ℕ)≠0 := by
      intro h
      have hh := congrFun h a
      simp [hab,Ne.symm hab] at hh
    simpa only [psi_two_distinct a b hab] using
      psi_integral_zero (Pi.single a 1+Pi.single b 1) hn

def liftWeight (f : (κ→ℝ)→ℝ) (x : κ⊕ν→ℝ) : ℝ := f (fun a=>x (.inl a))

theorem quadraticMoment_lift_inl (f : (κ→ℝ)→ℝ) (a b : κ) :
    quadraticMoment (liftWeight (ν:=ν) f) (.inl a) (.inl b)=quadraticMoment f a b := by
  unfold quadraticMoment
  rw [gaussian_sum_integral]
  have he (p : (κ→ℝ)×(ν→ℝ)) :
      liftWeight f (Sum.elim p.1 p.2)*quadraticCoordinate (.inl a) (.inl b) (Sum.elim p.1 p.2)=
        (f p.1*quadraticCoordinate a b p.1)*1 := by
    simp [liftWeight,quadraticCoordinate]
  simp_rw [he]
  rw [integral_prod_mul (fun y : κ→ℝ=>f y*quadraticCoordinate a b y) (fun _ : ν→ℝ=>(1:ℝ))]
  simp

theorem quadraticMoment_lift_mixed (f : (κ→ℝ)→ℝ) (a : κ) (b : ν) :
    quadraticMoment (liftWeight f) (.inl a) (.inr b)=0 := by
  unfold quadraticMoment
  rw [gaussian_sum_integral]
  have he (p : (κ→ℝ)×(ν→ℝ)) :
      liftWeight f (Sum.elim p.1 p.2)*quadraticCoordinate (.inl a) (.inr b) (Sum.elim p.1 p.2)=
        (f p.1*p.1 a)*p.2 b := by
    simp [liftWeight,quadraticCoordinate,mul_assoc]
  simp_rw [he]
  rw [integral_prod_mul (fun y : κ→ℝ=>f y*y a) (fun y : ν→ℝ=>y b),
    standardGaussian_coordinate_integral]
  simp

theorem quadraticMoment_lift_inr (f : (κ→ℝ)→ℝ) (a b : ν) :
    quadraticMoment (liftWeight f) (.inr a) (.inr b)=0 := by
  unfold quadraticMoment
  rw [gaussian_sum_integral]
  have he (p : (κ→ℝ)×(ν→ℝ)) :
      liftWeight f (Sum.elim p.1 p.2)*quadraticCoordinate (.inr a) (.inr b) (Sum.elim p.1 p.2)=
        f p.1*quadraticCoordinate a b p.2 := by
    simp [liftWeight,quadraticCoordinate]
  simp_rw [he]
  rw [integral_prod_mul,quadraticCoordinate_integral_zero]
  simp

/-- The exact Gaussian centered tensor of a function independent of the
spectator variables has only its original main-main block. -/
theorem quadraticMoment_lift (f : (κ→ℝ)→ℝ) (a b : κ⊕ν) :
    quadraticMoment (liftWeight f) a b=
      match a,b with
      | .inl a,.inl b=>quadraticMoment f a b
      | _,_=>0 := by
  cases a with
  | inl a=>cases b with
    | inl b=>exact quadraticMoment_lift_inl f a b
    | inr b=>exact quadraticMoment_lift_mixed f a b
  | inr a=>cases b with
    | inl b=>rw [quadraticMoment_symm];exact quadraticMoment_lift_mixed f b a
    | inr b=>exact quadraticMoment_lift_inr f a b

theorem quadraticMoment_reindex (e : κ≃ν) (f : (κ→ℝ)→ℝ) (a b : κ) :
    quadraticMoment (fun y : ν→ℝ=>f (fun k=>y (e k))) (e a) (e b)=
      quadraticMoment f a b := by
  let T := MeasurableEquiv.piCongrLeft (fun _ : κ=>ℝ) e.symm
  have hp : MeasurePreserving T (γpi ν) (γpi κ) :=
    measurePreserving_piCongrLeft (μ:=fun _ : κ=>gaussianReal 0 1) e.symm
  have hT (x : ν→ℝ) (j : κ) : T x j=x (e j) := by
    simpa only [T,Equiv.symm_apply_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : κ=>ℝ) e.symm x (e j)
  have hh := hp.integral_comp' (fun y=>f y*quadraticCoordinate a b y)
  change (∫ x,f (T x)*quadraticCoordinate a b (T x) ∂γpi ν)=quadraticMoment f a b at hh
  have he (x : ν→ℝ) : T x=(fun j=>x (e j)) := funext (hT x)
  simp only [he,quadraticCoordinate] at hh
  simpa only [quadraticMoment,quadraticCoordinate,e.injective.eq_iff] using hh

end Product

def spectatorMomentScore (n s : ℕ) (i : Fin (n+2))
    (x : Fin (n+2)⊕Fin s→ℝ) : ℝ :=
  ∑ a,∑ b,quadraticMoment (liftWeight (fun y=>maxWeights y i)) a b*
    quadraticCoordinate a b x

theorem spectatorMomentScore_eq (n s : ℕ) (i : Fin (n+2))
    (x : Fin (n+2)⊕Fin s→ℝ) :
    spectatorMomentScore n s i x=momentScore n i (fun a=>x (.inl a)) := by
  simp only [spectatorMomentScore,Fintype.sum_sum_type,quadraticMoment_lift,
    zero_mul,Finset.sum_const_zero,add_zero]
  simp only [momentScore,NegativeVotingRegularQuadratic.moment,quadraticCoordinate,
    Sum.inl.injEq]

theorem spectatorMomentScore_difference (n s : ℕ) (hn : 1 ≤ n)
    (i j : Fin (n+2)) (x : Fin (n+2)⊕Fin s→ℝ) :
    spectatorMomentScore n s i x-spectatorMomentScore n s j x=
      momentCoefficient n*((x (.inl i)-(∑ a,x (.inl a))/((n+2:ℕ):ℝ))^2-
        (x (.inl j)-(∑ a,x (.inl a))/((n+2:ℕ):ℝ))^2) := by
  rw [spectatorMomentScore_eq,spectatorMomentScore_eq]
  exact momentScore_difference n hn i j (fun a=>x (.inl a))

open NegativeVotingFan NegativeVotingFanQuadraticMoments
  NegativeVotingSecondChaosFacetGradient NegativeVotingFanTestedCells

section Ambient
variable {n s d : ℕ} (e : Fin (n+2)⊕Fin s≃Fin d)

def embeddedUnitRows (i : Fin (n+2)) : FSC.Coord d := EuclideanSpace.single (e (.inl i)) 1

theorem embeddedUnitRows_inner (i : Fin (n+2)) (x : FSC.Coord d) :
    inner ℝ (embeddedUnitRows e i) x=x (e (.inl i)) := by
  simp [embeddedUnitRows,EuclideanSpace.inner_single_left]

theorem embeddedUnitRows_injective : Function.Injective (embeddedUnitRows e) := by
  intro i j hij
  by_contra hne
  have he : e (.inl i)≠e (.inl j) := fun h=>hne (Sum.inl.inj (e.injective h))
  have hh := congrArg (fun x : FSC.Coord d=>x (e (.inl i))) hij
  simp [embeddedUnitRows,Pi.single_apply,he,Ne.symm he] at hh

theorem embeddedUnitRows_weights (i : Fin (n+2)) (x : FSC.Coord d) :
    weights (embeddedUnitRows e) (fun _=>0) x i=
      maxWeights (fun a=>x (e (.inl a))) i := by
  have hs : scores (embeddedUnitRows e) (fun _=>0) x=
      (fun a=>x (e (.inl a))) := by
    funext a
    simp only [scores,embeddedUnitRows_inner,add_zero]
  rw [weights,hs]

/-- Literal winning-cell tensor after a product-Gaussian split and an exact
finite coordinate reindexing. -/
theorem embeddedUnitRows_secondMomentTensor (i : Fin (n+2))
    (a b : Fin (n+2)⊕Fin s) :
    secondMomentTensor (embeddedUnitRows e) (fun _=>0) i (e a) (e b)=
      quadraticMoment (liftWeight (fun y=>maxWeights y i)) a b := by
  rw [←quadraticMoment_reindex e]
  unfold quadraticMoment
  change _=∫ x,maxWeights (fun j=>x (e (.inl j))) i*quadraticCoordinate (e a) (e b) x
    ∂standardGaussian (Fin d)
  rw [integral_standardGaussian_eq_euclidean]
  simp only [quadraticCoordinate]
  simp_rw [←embeddedUnitRows_weights e]
  rw [integral_weights_mul_eq_cell _ (embeddedUnitRows_injective e)]
  rfl

theorem embeddedUnitRows_quadraticLabelTest (i : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest (embeddedUnitRows e) (fun _=>0) i x=
      spectatorMomentScore n s i (fun a=>x (e a)) := by
  unfold quadraticLabelTest
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rw [embeddedUnitRows_secondMomentTensor]
  simp only [tensorTest,quadraticCoordinate,e.injective.eq_iff]

def embeddedCanonicalRows (i : Fin (n+2)) : FSC.Coord d :=
  embeddedUnitRows e i-(1/((n+2:ℕ):ℝ)) • ∑ j,embeddedUnitRows e j

theorem embeddedCanonicalRows_inner (i : Fin (n+2)) (x : FSC.Coord d) :
    inner ℝ (embeddedCanonicalRows e i) x=
      x (e (.inl i))-(∑ a,x (e (.inl a)))/((n+2:ℕ):ℝ) := by
  simp only [embeddedCanonicalRows,inner_sub_left,real_inner_smul_left,sum_inner,
    embeddedUnitRows_inner]
  ring

theorem embeddedCanonicalRows_winningCell (i : Fin (n+2)) :
    winningCell (embeddedCanonicalRows e) (fun _=>0) i=
      winningCell (embeddedUnitRows e) (fun _=>0) i := by
  ext x
  simp only [winningCell,Set.mem_setOf_eq,scores,add_zero,embeddedCanonicalRows_inner,
    embeddedUnitRows_inner,sub_le_sub_iff_right]

theorem embeddedCanonicalRows_quadraticLabelTest (i : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) i x=
      spectatorMomentScore n s i (fun a=>x (e a)) := by
  rw [←embeddedUnitRows_quadraticLabelTest e]
  simp only [quadraticLabelTest,secondMomentTensor,embeddedCanonicalRows_winningCell]

/-- Actual canonical regular score gaps in every finite spectator dimension,
including zero spectators. All cross/spectator tensor entries were integrated
out, rather than inferred merely from the distribution of the score vector. -/
theorem embeddedCanonicalRows_quadraticLabelTest_difference (hn : 1 ≤ n)
    (i j : Fin (n+2)) (x : FSC.Coord d) :
    quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) i x-
        quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) j x=
      momentCoefficient n*((inner ℝ (embeddedCanonicalRows e i) x)^2-
        (inner ℝ (embeddedCanonicalRows e j) x)^2) := by
  rw [embeddedCanonicalRows_quadraticLabelTest,embeddedCanonicalRows_quadraticLabelTest,
    embeddedCanonicalRows_inner,embeddedCanonicalRows_inner]
  exact spectatorMomentScore_difference n s hn i j (fun a=>x (e a))

open NegativeVotingRegularFacetCancellation

/-- The actual spectator-extended Gaussian test retains the current-facet
error factor, in the full ambient space. -/
theorem embedded_actualJump_on_current_facet (hn : 1 ≤ n)
    (B : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (α : ℝ) (hα : α≠0) (i j : Fin (n+2)) (x : FSC.Coord d)
    (hx : x∈affineFacet B h i j) :
    quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) i x-
        quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) j x=
      -(momentCoefficient n/α)*errorGap B (embeddedCanonicalRows e) h α i j x*
        (inner ℝ (embeddedCanonicalRows e i) x+inner ℝ (embeddedCanonicalRows e j) x) := by
  rw [embeddedCanonicalRows_quadraticLabelTest_difference e hn]
  exact regularJump_on_facet B (embeddedCanonicalRows e) h α (momentCoefficient n)
    hα i j x hx

/-- The material derivative identity also retains every spectator component
of the ambient velocity. No projection of that velocity is assumed. -/
theorem hasDerivAt_embedded_actualJump_material (hn : 1 ≤ n)
    (B : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (α ℓ : ℝ) (hα : α≠0) (i j : Fin (n+2)) (x V : FSC.Coord d)
    (hx : x∈affineFacet B h i j) (hV : inner ℝ (B i-B j) V= -ℓ) :
    HasDerivAt (fun t : ℝ=>
      quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) i (x+t • V)-
        quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) j (x+t • V))
      (-(momentCoefficient n/α)*
        ((inner ℝ (embeddedCanonicalRows e i) x+inner ℝ (embeddedCanonicalRows e j) x)*ℓ+
          (inner ℝ (embeddedCanonicalRows e i) x+inner ℝ (embeddedCanonicalRows e j) x)*
            inner ℝ (rowError B (embeddedCanonicalRows e) α i-
              rowError B (embeddedCanonicalRows e) α j) V+
          errorGap B (embeddedCanonicalRows e) h α i j x*
            inner ℝ (embeddedCanonicalRows e i+embeddedCanonicalRows e j) V)) 0 := by
  have he : (fun t : ℝ=>
      quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) i (x+t • V)-
        quadraticLabelTest (embeddedCanonicalRows e) (fun _=>0) j (x+t • V))=
      (fun t : ℝ=>regularJump (embeddedCanonicalRows e) (momentCoefficient n) i j (x+t • V)) := by
    funext t
    exact embeddedCanonicalRows_quadraticLabelTest_difference e hn i j (x+t • V)
  rw [he]
  have hd := hasDerivAt_regularJump_line (embeddedCanonicalRows e) (momentCoefficient n) i j x V
  rw [regularJump_material_on_facet B (embeddedCanonicalRows e) h α
    (momentCoefficient n) ℓ hα i j x V hx hV] at hd
  exact hd

end Ambient

end NegativeVotingRegularSpectatorRepresentation
