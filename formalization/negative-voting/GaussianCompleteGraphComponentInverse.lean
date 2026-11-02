import GaussianBoundedRowGraph

/-! A componentwise inverse estimate for a complete weighted Laplacian.
The proof first obtains L1 contraction after removing a constant complete
 graph, then uses the individual row equation. L1 contraction alone would
 not give the componentwise bound required for balanced-offset derivatives. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace NegativeVotingCompleteGraphComponentInverse
open NegativeVotingBoundedRowGraph
variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

def signedUnit (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma signedUnit_mul_self (x : ℝ) : signedUnit x*x=|x| := by
  unfold signedUnit
  split_ifs with hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_neg (lt_of_not_ge hx)]

lemma signedUnit_mul_le_abs (x y : ℝ) : signedUnit x*y ≤ |y| := by
  unfold signedUnit
  split_ifs <;> simp only [one_mul,neg_mul,neg_one_mul]
  · exact le_abs_self y
  · exact neg_le_abs y

lemma signedUnit_monotone_product (x y : ℝ) :
    0 ≤ (x-y)*(signedUnit x-signedUnit y) := by
  unfold signedUnit
  split_ifs <;> norm_num <;> linarith

lemma signed_pairing_nonneg (w : V → V → ℝ) (hw : ∀ i j,0 ≤ w i j)
    (hsym : ∀ i j,w i j=w j i) (v : V → ℝ) :
    0 ≤ ∑i,signedUnit (v i)*(∑j,w i j*(v i-v j)) := by
  rw [scalar_edge_pairing w hsym]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>
    Finset.sum_nonneg fun j _=>by
      simpa only [mul_assoc] using mul_nonneg (hw i j) (signedUnit_monotone_product (v i) (v j)))

lemma complete_graph_equation (v : V → ℝ) (hv : ∑i,v i=0) (a : ℝ) (i : V) :
    (∑j,a/(Fintype.card V:ℝ)*(v i-v j))=a*v i := by
  simp_rw [mul_sub,Finset.sum_sub_distrib,←Finset.mul_sum,hv]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_zero,sub_zero]
  have hm : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The inverse has an L1 bound with no cardinality loss. -/
theorem centered_laplacian_l1_bound (w : V → V → ℝ)
    (hsym : ∀ i j,w i j=w j i) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ i j,a/(Fintype.card V:ℝ) ≤ w i j)
    (v b : V → ℝ) (hv : ∑i,v i=0)
    (heq : ∀ i,(∑j,w i j*(v i-v j))=b i) :
    a*(∑i,|v i|) ≤ ∑i,|b i| := by
  let k : V → V → ℝ := fun i j=>w i j-a/(Fintype.card V:ℝ)
  have hk : ∀ i j,0 ≤ k i j := fun i j=>sub_nonneg.mpr (hlower i j)
  have hks : ∀ i j,k i j=k j i := by intro i j; dsimp [k];rw [hsym i j]
  have hdec (i : V) : b i=a*v i+∑j,k i j*(v i-v j) := by
    rw [←heq i,←complete_graph_equation v hv a i,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [k]
    ring
  have hpair := signed_pairing_nonneg k hk hks v
  have hp : (∑i,signedUnit (v i)*b i)=a*(∑i,|v i|)+
      ∑i,signedUnit (v i)*(∑j,k i j*(v i-v j)) := by
    simp_rw [hdec,mul_add,Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = a*(signedUnit (v i)*v i) := by ring
      _ = _ := by rw [signedUnit_mul_self]
  have hb : (∑i,signedUnit (v i)*b i) ≤ ∑i,|b i| :=
    Finset.sum_le_sum fun i _=>signedUnit_mul_le_abs _ _
  linarith

/-- A pointwise inverse estimate: the local source plus its average L1 size.
The complete-graph lower bound alone gives the L1 term; the upper bound is
used only in the individual row equation. -/
theorem centered_laplacian_component_bound (w : V → V → ℝ)
    (hsym : ∀ i j,w i j=w j i) (a u : ℝ) (ha : 0 < a)
    (hlower : ∀ i j,a/(Fintype.card V:ℝ) ≤ w i j)
    (hupper : ∀ i j,w i j ≤ u/(Fintype.card V:ℝ))
    (v b : V → ℝ) (hv : ∑i,v i=0)
    (heq : ∀ i,(∑j,w i j*(v i-v j))=b i) (i : V) :
    |v i| ≤ |b i|/a+u/(a^2*(Fintype.card V:ℝ))*(∑j,|b j|) := by
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hw : ∀ i j,0 ≤ w i j := fun i j=>(by positivity : (0:ℝ) ≤ a/(Fintype.card V:ℝ)).trans (hlower i j)
  have hu : 0 ≤ u := by
    have hh := (hw i i).trans (hupper i i)
    simpa only [zero_mul] using (le_div_iff₀ hm).mp hh
  have hdegree : a ≤ ∑j,w i j := by
    have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=>hlower i j)
    simpa [nsmul_eq_mul, mul_div_cancel₀, hm.ne'] using hh
  have hrow : (∑j,w i j)*v i=b i+∑j,w i j*v j := by
    have hh := heq i
    simp_rw [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul] at hh
    linarith
  have hlocal : a*|v i| ≤ |b i|+u/(Fintype.card V:ℝ)*(∑j,|v j|) := by
    calc
      _ ≤ (∑j,w i j)*|v i| := mul_le_mul_of_nonneg_right hdegree (abs_nonneg _)
      _ = |(∑j,w i j)*v i| := by rw [abs_mul,abs_of_nonneg (Finset.sum_nonneg fun j _=>hw i j)]
      _ = |b i+∑j,w i j*v j| := by rw [hrow]
      _ ≤ |b i|+|∑j,w i j*v j| := abs_add_le _ _
      _ ≤ |b i|+∑j,|w i j*v j| := add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := by
        rw [Finset.mul_sum]
        gcongr with j
        rw [abs_mul,abs_of_nonneg (hw i j)]
        exact mul_le_mul_of_nonneg_right (hupper i j) (abs_nonneg _)
  have hL := centered_laplacian_l1_bound w hsym a ha hlower v b hv heq
  have hL' : (∑j,|v j|) ≤ (∑j,|b j|)/a := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hL)
  have hh := hlocal.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hL'
    (by positivity : (0:ℝ) ≤ u/(Fintype.card V:ℝ))))
  have hdiv : |v i| ≤ (|b i|+u/(Fintype.card V:ℝ)*((∑j,|b j|)/a))/a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hh)
  convert hdiv using 1 <;> field_simp <;> ring

end NegativeVotingCompleteGraphComponentInverse
