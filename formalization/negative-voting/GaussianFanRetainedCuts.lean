import GaussianFiniteGraphCoarea
import GaussianFanCheeger

/-! Quantitative deletion of small actual Gaussian facets, with explicit
mass, edge-length, and threshold constants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NegativeVotingFiniteGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance : (p : Prop) → Decidable p := Classical.propDecidable

def retainedWeight (w : V → V → ℝ) (τ : ℝ) (i j : V) : ℝ :=
  if τ ≤ w i j then w i j else 0

theorem retainedWeight_nonneg (w : V → V → ℝ) (hw : ∀i j,0 ≤ w i j)
    (τ : ℝ) (i j : V) : 0 ≤ retainedWeight w τ i j := by
  unfold retainedWeight
  split_ifs
  · exact hw i j
  · norm_num

theorem retainedWeight_le (w : V → V → ℝ) (hw : ∀i j,0 ≤ w i j)
    (τ : ℝ) (i j : V) : retainedWeight w τ i j ≤ w i j := by
  unfold retainedWeight
  split_ifs <;> simp_all


theorem retained_degree_le (w : V → V → ℝ) (hw : ∀i j,0 ≤ w i j)
    (τ D : ℝ) (hd : ∀i, (∑j,w i j) ≤ D) (i : V) :
    (∑j,retainedWeight w τ i j) ≤ D :=
  (Finset.sum_le_sum (fun j _ => retainedWeight_le w hw τ i j)).trans (hd i)

theorem retainedWeight_symm (w : V → V → ℝ) (hs : ∀i j,w i j=w j i)
    (τ : ℝ) (i j : V) : retainedWeight w τ i j=retainedWeight w τ j i := by
  simp only [retainedWeight,hs i j]

theorem weight_le_retained_add (w : V → V → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (i j : V) :
    w i j ≤ retainedWeight w τ i j+τ := by
  unfold retainedWeight
  split_ifs with ht
  · linarith
  · simpa using (le_of_lt (lt_of_not_ge ht))

theorem cut_deletion_loss (w : V → V → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (S : Finset V) :
    cutWeight w S ≤ cutWeight (retainedWeight w τ) S+τ*(S.card:ℝ)*(Sᶜ.card:ℝ) := by
  calc
    _  ≤  ∑i∈S,∑j∈Sᶜ,(retainedWeight w τ i j+τ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => weight_le_retained_add w τ hτ i j))
    _ = _ := by simp [cutWeight,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul];ring

theorem retained_cut_expansion (w : V → V → ℝ) (κ τ : ℝ) (hτ : 0 ≤ τ)
    (hc : ∀S : Finset V,κ*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ cutWeight w S) (S : Finset V) :
    (κ-τ*(Fintype.card V:ℝ))*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ 
      cutWeight (retainedWeight w τ) S := by
  have hh := cut_deletion_loss w τ hτ S
  have hb := mul_le_mul_of_nonneg_left (cut_count_le_card_mul_min S) hτ
  have he := hc S
  nlinarith

theorem retained_cut_expansion_half (w : V → V → ℝ) (κ τ : ℝ) (hτ : 0 ≤ τ)
    (hc : ∀S : Finset V,κ*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ cutWeight w S)
    (ht : τ*(Fintype.card V:ℝ) ≤ κ/2) (S : Finset V) :
    (κ/2)*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ cutWeight (retainedWeight w τ) S := by
  have he := retained_cut_expansion w κ τ hτ hc S
  have hs : 0 ≤ min (S.card:ℝ) (Sᶜ.card:ℝ) := by positivity
  nlinarith

end NegativeVotingFiniteGraph
namespace NegativeVotingFanRetained
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanBoundary NegativeVotingFiniteGraph
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
local instance : (p : Prop) → Decidable p := Classical.propDecidable

theorem sum_on_finset (S : Finset V) (f : V → ℝ)
    [Fintype {i : V // i∈(S:Set V)}] :
    (∑i : {i : V // i∈(S:Set V)}, f i)=∑i∈S,f i :=
  (Finset.sum_subtype S (fun _ => Iff.rfl) f).symm

theorem sum_on_compl_finset (S : Finset V) (f : V → ℝ)
    [Fintype {i : V // i∈(S:Set V)ᶜ}] :
    (∑i : {i : V // i∈(S:Set V)ᶜ}, f i)=∑i∈Sᶜ,f i :=
  (Finset.sum_subtype Sᶜ (fun _ => by simp) f).symm

theorem double_sum_on_finset (S : Finset V) (w : V → V → ℝ)
    [Fintype {i : V // i∈(S:Set V)}] [Fintype {j : V // j∈(S:Set V)ᶜ}] :
    (∑i : {i : V // i∈(S:Set V)}, ∑j : {j : V // j∈(S:Set V)ᶜ}, w i j)=
      cutWeight w S := by
  rw [sum_on_finset S (fun i => ∑j : {j : V // j∈(S:Set V)ᶜ}, w i j)]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_on_compl_finset S (w i)

/-- A lower bound on actual cell masses and upper bound on actual edge lengths
produce a combinatorial cut constant p0/(2πL), with no expansion premise. -/
theorem gaussian_cut_expansion (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (p0 L : ℝ) (hp0 : 0 ≤ p0) (hL : 0<L)
    (hmass : ∀i,p0 ≤ mass B h i) (hedge : ∀i j,i≠j→‖B i-B j‖ ≤ L)
    (S : Finset V) :
    (p0/(2*Real.pi*L))*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ cutWeight (facetWeight B h) S := by
  have hh := gaussian_cut_jacobian_conductance B h hinj (S:Set V)
  simp only [sum_on_finset] at hh
  let w : V → V → ℝ := fun i j => ‖B i-B j‖*facetWeight B h i j
  have hew (i j : V) : ‖B i-B j‖*facetWeight B h i j=w i j := rfl
  simp_rw [hew] at hh
  simp only [double_sum_on_finset] at hh
  have htotal : (∑i∈S,mass B h i)+(∑i∈Sᶜ,mass B h i)=1 := by
    rw [Finset.sum_add_sum_compl,mass_sum]
  have hm (T : Finset V) : p0*(T.card:ℝ) ≤ ∑i∈T,mass B h i := by
    calc
      _ = ∑i∈T,p0 := by simp [Finset.sum_const,nsmul_eq_mul];ring
      _  ≤  _ := Finset.sum_le_sum (fun i _ => hmass i)
  have hmin : p0*min (S.card:ℝ) (Sᶜ.card:ℝ)  ≤ 
      min (∑i∈S,mass B h i) (1-∑i∈S,mass B h i) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hp0).trans (hm S)
    · have hc : (1-∑i∈S,mass B h i)=∑i∈Sᶜ,mass B h i := by linarith
      rw [hc]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hp0).trans (hm Sᶜ)
  have hs : (∑i∈S,∑j∈Sᶜ,‖B i-B j‖*facetWeight B h i j)  ≤ 
      L*cutWeight (facetWeight B h) S := by
    calc
      _  ≤  ∑i∈S,∑j∈Sᶜ,L*facetWeight B h i j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right (hedge i j _) (facetWeight_nonneg B h i j)
        intro hij
        subst j
        exact (Finset.mem_compl.mp hj) hi
      _ = _ := by simp only [cutWeight,Finset.mul_sum]
  have hf := (hmin.trans hh).trans (mul_le_mul_of_nonneg_left hs (by positivity))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0<2*Real.pi*L by positivity)).mpr
  nlinarith

/-- Deleting actual Gaussian facets below τ loses at most half the proven
cut constant whenever τ*m ≤ p0/(4πL). -/
theorem gaussian_retained_cut_expansion (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (p0 L τ : ℝ) (hp0 : 0 ≤ p0) (hL : 0<L) (hτ : 0 ≤ τ)
    (hmass : ∀i,p0 ≤ mass B h i) (hedge : ∀i j,i≠j→‖B i-B j‖ ≤ L)
    (ht : τ*(Fintype.card V:ℝ) ≤ (p0/(2*Real.pi*L))/2) (S : Finset V) :
    ((p0/(2*Real.pi*L))/2)*min (S.card:ℝ) (Sᶜ.card:ℝ) ≤ 
      cutWeight (retainedWeight (facetWeight B h) τ) S :=
  retained_cut_expansion_half (facetWeight B h) _ τ hτ
    (gaussian_cut_expansion B h hinj p0 L hp0 hL hmass hedge) ht S

end NegativeVotingFanRetained
