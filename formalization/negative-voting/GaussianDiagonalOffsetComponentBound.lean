import GaussianDiagonalBalanceEquation
import GaussianCompleteGraphComponentInverse

/-! Weighted component estimates for actual diagonal balancing derivatives.
The only analytic inputs are explicitly displayed literal pair-integral
bounds, to be supplied by the whole-threshold moment theorem. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
namespace NegativeVotingDiagonalOffsetComponentBound
open NegativeVotingDiagonalBalanceEquation NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardPolynomialBounds NegativeVotingHazardIntegrability
  NegativeVotingCompleteGraphComponentInverse

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The artificial diagonal cancels out of the physical Laplacian exactly. -/
theorem off_diagonal_component_bound (w : V → V → ℝ)
    (hsym : ∀ i j,w i j=w j i) (a u : ℝ) (ha : 0 < a) (hau : a ≤ u)
    (hlower : ∀ i j,i≠j → a/(Fintype.card V:ℝ) ≤ w i j)
    (hupper : ∀ i j,i≠j → w i j ≤ u/(Fintype.card V:ℝ))
    (v b : V → ℝ) (hv : ∑i,v i=0) (heq : ∀ i,(∑j,w i j*(v i-v j))=b i) (i : V) :
    |v i| ≤ |b i|/a+u/(a^2*(Fintype.card V:ℝ))*(∑j,|b j|) := by
  let w' : V → V → ℝ := fun i j=>if i=j then a/(Fintype.card V:ℝ) else w i j
  have hsym' : ∀ i j,w' i j=w' j i := by
    intro i j
    by_cases hij:i=j
    · subst j;rfl
    · simp only [w',hij,Ne.symm hij,ite_false,hsym i j]
  have hlo : ∀ i j,a/(Fintype.card V:ℝ) ≤ w' i j := by
    intro i j
    by_cases hij:i=j
    · simp [w',hij]
    · simpa only [w',hij,ite_false] using hlower i j hij
  have hup : ∀ i j,w' i j ≤ u/(Fintype.card V:ℝ) := by
    intro i j
    by_cases hij:i=j
    · simp only [w',hij,ite_true]
      exact div_le_div_of_nonneg_right hau (Nat.cast_nonneg _)
    · simpa only [w',hij,ite_false] using hupper i j hij
  have heq' : ∀ i,(∑j,w' i j*(v i-v j))=b i := by
    intro i
    rw [←heq i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:i=j <;> simp [w',hij]
  exact centered_laplacian_component_bound w' hsym' a u ha hlo hup v b hv heq' i

def meanAbs (ξ : V → ℝ) : ℝ := (∑i,|ξ i|)/(Fintype.card V:ℝ)

lemma meanAbs_nonneg (ξ : V → ℝ) : 0 ≤ meanAbs ξ := by
  unfold meanAbs
  positivity

/-- A source with coordinate-plus-average structure preserves that structure
under the genuine complete-graph inverse; no label-count loss appears. -/
theorem weighted_source_component_bound (w : V → V → ℝ)
    (hsym : ∀ i j,w i j=w j i) (a u B : ℝ) (ha : 0 < a) (hau : a ≤ u) (hB : 0 ≤ B)
    (hlower : ∀ i j,i≠j → a/(Fintype.card V:ℝ) ≤ w i j)
    (hupper : ∀ i j,i≠j → w i j ≤ u/(Fintype.card V:ℝ))
    (v b ξ : V → ℝ) (hv : ∑i,v i=0) (heq : ∀ i,(∑j,w i j*(v i-v j))=b i)
    (hb : ∀ i,|b i| ≤ B*(|ξ i|+meanAbs ξ)) (i : V) :
    |v i| ≤ B/a*(1+2*u/a)*(|ξ i|+meanAbs ξ) := by
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hu : 0 ≤ u := ha.le.trans hau
  have hs : (∑j,|b j|) ≤ 2*B*(∑j,|ξ j|) := by
    have hh := Finset.sum_le_sum fun j (_:j∈Finset.univ)=>hb j
    refine hh.trans_eq ?_
    rw [←Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    unfold meanAbs
    field_simp
    ring
  have hc := off_diagonal_component_bound w hsym a u ha hau hlower hupper v b hv heq i
  have h1 := add_le_add (div_le_div_of_nonneg_right (hb i) ha.le)
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ u/(a^2*(Fintype.card V:ℝ))))
  have h2 : B*(|ξ i|+meanAbs ξ)/a+u/(a^2*(Fintype.card V:ℝ))*(2*B*(∑j,|ξ j|)) ≤
      B/a*(1+2*u/a)*(|ξ i|+meanAbs ξ) := by
    have hn : 0 ≤ 2*u*B/a^2*|ξ i| := by positivity
    apply sub_nonneg.mp
    convert hn using 1 <;> unfold meanAbs <;> field_simp <;> ring
  exact hc.trans (h1.trans h2)

variable {m : ℕ}

lemma varianceSpeed_abs_le (σ h ζ ξ : Fin m→ℝ) (c H : ℝ) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hz : ∀k,|ζ k/σ k| ≤ c*|ξ k|) (hh : ∀k,|h k| ≤ H) (i : Fin m) (x : ℝ) :
    |varianceSpeed σ h ζ i x| ≤ c*(1+H)*|ξ i| *(1+|x|) := by
  have hs : |x-h i| ≤ (1+H)*(1+|x|) := by
    have ha : |x-h i| ≤ |x|+|h i| := by simpa using abs_sub_le x 0 (h i)
    nlinarith [hh i,abs_nonneg x,mul_nonneg hH (abs_nonneg x)]
  unfold varianceSpeed
  rw [abs_mul]
  have h1 := mul_le_mul (hz i) hs (abs_nonneg _) (mul_nonneg hc (abs_nonneg _))
  convert h1 using 1 <;> ring

/-- Actual variance forcing, with all pair integrals and every competing label
retained. The raw first-moment bound is explicit. -/
theorem varianceForcing_component_le (σ h ζ ξ : Fin m→ℝ) (hσ : ∀k,0 < σ k)
    (c H M : ℝ) (hc : 0 ≤ c) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hz : ∀k,|ζ k/σ k| ≤ c*|ξ k|) (hh : ∀k,|h k| ≤ H)
    (hmom : ∀i j,i≠j → (∫x,hazardPairDensity σ h x i j*(1+|x|)) ≤ M) (i : Fin m) :
    |varianceForcing σ h ζ i| ≤ c*(1+H)*M*((m:ℝ)*|ξ i|+∑j,|ξ j|) := by
  have hpair (j:Fin m) (hij:i≠j) :
      |∫x,hazardPairDensity σ h x i j*(varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x)| ≤
        c*(1+H)*(|ξ i|+|ξ j|)*M := by
    have hi := integrable_variancePair σ h ζ hσ i j
    have henv := (integrable_hazardPairDensity_polynomial σ h hσ i j 1).const_mul
      (c*(1+H)*(|ξ i|+|ξ j|))
    have hab (x:ℝ) : |varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x| ≤
        c*(1+H)*(|ξ i|+|ξ j|)*(1+|x|) := by
      have ha : |varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x| ≤
          |varianceSpeed σ h ζ i x|+|varianceSpeed σ h ζ j x| := by
        simpa using abs_sub_le (varianceSpeed σ h ζ i x) 0 (varianceSpeed σ h ζ j x)
      have hb := add_le_add (varianceSpeed_abs_le σ h ζ ξ c H hc hH hz hh i x)
        (varianceSpeed_abs_le σ h ζ ξ c H hc hH hz hh j x)
      exact ha.trans (by convert hb using 1 <;> ring)
    have hn := norm_integral_le_integral_norm (μ:=volume) (f:=fun x=>hazardPairDensity σ h x i j*
      (varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x))
    rw [Real.norm_eq_abs] at hn
    have hb : (∫x,‖hazardPairDensity σ h x i j*(varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x)‖) ≤
        c*(1+H)*(|ξ i|+|ξ j|)*(∫x,hazardPairDensity σ h x i j*(1+|x|)) := by
      rw [←integral_const_mul]
      apply integral_mono hi.norm
        (by simpa only [pow_one] using henv)
      intro x
      dsimp only
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hazardPairDensity_nonneg σ h hσ x i j)]
      have h1 := mul_le_mul_of_nonneg_left (hab x) (hazardPairDensity_nonneg σ h hσ x i j)
      convert h1 using 1 <;> ring
    exact hn.trans (hb.trans (mul_le_mul_of_nonneg_left (hmom i j hij) (by positivity)))
  unfold varianceForcing
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsum := Finset.sum_le_sum (s:=Finset.univ.erase i) (fun j hj=>hpair j (Ne.symm (Finset.mem_erase.mp hj).1))
  have hfull : (∑j∈Finset.univ.erase i,c*(1+H)*(|ξ i|+|ξ j|)*M) ≤
      ∑j,c*(1+H)*(|ξ i|+|ξ j|)*M :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _=>by positivity)
  refine hsum.trans (hfull.trans_eq ?_)
  rw [←Finset.sum_mul,←Finset.mul_sum,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end NegativeVotingDiagonalOffsetComponentBound
