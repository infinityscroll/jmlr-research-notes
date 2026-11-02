import GaussianQuadraticTensorBulkNorm
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Actual permutation symmetry of centered Gaussian coordinate moments on
equal-threshold orthants and their complements. No covariance estimate is
assumed in this symmetry statement. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingOrthantTraceCancellation
variable {d:ℕ}

def permute (p:Equiv.Perm (Fin d)) : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p

def permutationInvariant (S:Set (FSC.Coord d)) : Prop :=
  ∀p:Equiv.Perm (Fin d),(permute p) ⁻¹' S=S

def orthant (d:ℕ) (t:ℝ) : Set (FSC.Coord d) := {x|∀i,x i ≤ t}

def centeredMoment (S:Set (FSC.Coord d)) (i j:Fin d) : ℝ :=
  ∫x in S,(x i*x j-(if i=j then 1 else 0)) ∂stdGaussian (FSC.Coord d)

lemma measurableSet_orthant (d:ℕ) (t:ℝ) : MeasurableSet (orthant d t) := by
  unfold orthant
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i=>measurableSet_le (by fun_prop) measurable_const

lemma orthant_permutationInvariant (d:ℕ) (t:ℝ) : permutationInvariant (orthant d t) := by
  intro p
  ext x
  change (∀i,x (p.symm i) ≤ t) ↔ ∀i,x i ≤ t
  constructor
  · intro h i;simpa only [Equiv.symm_apply_apply] using h (p i)
  · intro h i;exact h (p.symm i)

lemma permutationInvariant_compl (S:Set (FSC.Coord d)) (hS:permutationInvariant S) :
    permutationInvariant Sᶜ := by
  intro p
  rw [Set.preimage_compl,hS p]

lemma centeredMoment_permute (S:Set (FSC.Coord d)) (hS:MeasurableSet S)
    (hinv:permutationInvariant S) (p:Equiv.Perm (Fin d)) (i j:Fin d) :
    centeredMoment S (p i) (p j)=centeredMoment S i j := by
  unfold centeredMoment
  conv_lhs => rw [←stdGaussian_map (permute p)]
  rw [setIntegral_map hS (by fun_prop) (permute p).continuous.measurable.aemeasurable,hinv p]
  apply integral_congr_ae
  filter_upwards with x
  change x (p.symm (p i))*x (p.symm (p j))-(if p i=p j then 1 else 0)=_
  simp only [Equiv.symm_apply_apply,Equiv.apply_eq_iff_eq]

lemma exists_perm_pair {V:Type*} [DecidableEq V] (a b i j:V) (hab:a≠b) (hij:i≠j) :
    ∃p:Equiv.Perm V,p a=i ∧ p b=j := by
  let e:=Equiv.swap a i
  have ha:e a=i:=Equiv.swap_apply_left a i
  have hb:e b≠i:=by rw [←ha];exact fun h=>hab (e.injective h).symm
  let p:=e.trans (Equiv.swap (e b) j)
  refine ⟨p,?_,?_⟩
  · change Equiv.swap (e b) j (e a)=i
    rw [ha]
    exact Equiv.swap_apply_of_ne_of_ne hb.symm hij
  · change Equiv.swap (e b) j (e b)=j
    exact Equiv.swap_apply_left _ _

lemma centeredMoment_diagonal (S:Set (FSC.Coord d)) (hS:MeasurableSet S)
    (hinv:permutationInvariant S) (a i:Fin d) : centeredMoment S i i=centeredMoment S a a := by
  have hh:=centeredMoment_permute S hS hinv (Equiv.swap a i) a a
  simpa only [Equiv.swap_apply_left] using hh

lemma centeredMoment_offDiagonal (S:Set (FSC.Coord d)) (hS:MeasurableSet S)
    (hinv:permutationInvariant S) (a b:Fin d) (hab:a≠b) (i j:Fin d) (hij:i≠j) :
    centeredMoment S i j=centeredMoment S a b := by
  obtain ⟨p,hpa,hpb⟩:=exists_perm_pair a b i j hab hij
  have hh:=centeredMoment_permute S hS hinv p a b
  simpa only [hpa,hpb] using hh

/-- The complete actual centered-moment matrix has two scalar entries. -/
theorem centeredMoment_two_values (S:Set (FSC.Coord d)) (hS:MeasurableSet S)
    (hinv:permutationInvariant S) (a b:Fin d) (hab:a≠b) (i j:Fin d) :
    centeredMoment S i j=
      if i=j then centeredMoment S a a else centeredMoment S a b := by
  by_cases hij:i=j
  · subst j;simpa only [ite_true] using centeredMoment_diagonal S hS hinv a i
  · rw [if_neg hij];exact centeredMoment_offDiagonal S hS hinv a b hab i j hij

theorem orthant_centeredMoment_two_values (t:ℝ) (a b:Fin d) (hab:a≠b) (i j:Fin d) :
    centeredMoment (orthant d t) i j=
      if i=j then centeredMoment (orthant d t) a a else centeredMoment (orthant d t) a b :=
  centeredMoment_two_values _ (measurableSet_orthant d t) (orthant_permutationInvariant d t) a b hab i j

theorem orthant_compl_centeredMoment_two_values (t:ℝ) (a b:Fin d) (hab:a≠b) (i j:Fin d) :
    centeredMoment (orthant d t)ᶜ i j=
      if i=j then centeredMoment (orthant d t)ᶜ a a else centeredMoment (orthant d t)ᶜ a b :=
  centeredMoment_two_values _ (measurableSet_orthant d t).compl
    (permutationInvariant_compl _ (orthant_permutationInvariant d t)) a b hab i j

end NegativeVotingOrthantTraceCancellation
