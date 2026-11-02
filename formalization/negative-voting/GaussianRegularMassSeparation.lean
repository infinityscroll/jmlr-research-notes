import GaussianRegularFacetGaussianLower
import GaussianRegularMassSymmetry
import GaussianCenteredParsevalBasis

/-! Quantitative separation of actual regular Gaussian winning probabilities,
from the actual Gaussian mass Jacobian and global facet-weight envelope. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingRegularMassSeparation
open NegativeVotingRegularFacetGaussianLower NegativeVotingRegularMassSymmetry
  NegativeVotingFacetConditionalPlane NegativeVotingBalancedReference
  NegativeVotingFan NegativeVotingFanJacobian NegativeVotingCenteredParseval

section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]
def pairVelocity (i j : V) (Δ : ℝ) (k : V) : ℝ :=
  if k=i then Δ/2 else if k=j then -Δ/2 else 0

theorem laplacian_pair_lower (w : V → V → ℝ) (a Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hw : ∀ k l, k ≠ l → a ≤ w k l) (i j : V) (hij : i ≠ j) :
    (Fintype.card V : ℝ)*a*Δ ≤
      (∑ k, w i k*(pairVelocity i j Δ i-pairVelocity i j Δ k))-
      (∑ k, w j k*(pairVelocity i j Δ j-pairVelocity i j Δ k)) := by
  have hp (k : V) : a*Δ ≤
      w i k*(pairVelocity i j Δ i-pairVelocity i j Δ k)-
      w j k*(pairVelocity i j Δ j-pairVelocity i j Δ k) := by
    by_cases hki : k=i
    · subst k
      have hh := mul_le_mul_of_nonneg_right (hw j i hij.symm) hΔ
      simp only [pairVelocity,ite_true,if_neg hij,if_neg hij.symm]
      nlinarith
    · by_cases hkj : k=j
      · subst k
        have hh := mul_le_mul_of_nonneg_right (hw i j hij) hΔ
        simp only [pairVelocity,ite_true,if_neg hij,if_neg hij.symm]
        nlinarith
      · have hh1 := mul_le_mul_of_nonneg_right (hw i k (Ne.symm hki)) hΔ
        have hh2 := mul_le_mul_of_nonneg_right (hw j k (Ne.symm hkj)) hΔ
        simp only [pairVelocity,ite_true,if_neg hij,if_neg hij.symm,if_neg hki,if_neg hkj]
        nlinarith
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hp k)
  simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_assoc] using hs
end Finite

variable {n d : ℕ}

def pairComponent (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2))
    (h : FSC.Coord d) : FSC.Coord d :=
  (inner ℝ (B i-B j) h/2) • (B i-B j)

def pairPath (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2))
    (h : FSC.Coord d) (t : ℝ) : FSC.Coord d :=
  h-pairComponent B i j h+t • pairComponent B i j h

theorem regular_edge_inner (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) : inner ℝ (B i-B j) (B i-B j)=2 := by
  simp only [inner_sub_left,inner_sub_right,hG,ite_true,if_neg hij,if_neg hij.symm]
  ring

theorem pairPath_norm_sq (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) (h : FSC.Coord d) (t : ℝ) :
    ‖pairPath B i j h t‖^2 = ‖h‖^2+(t^2-1)*(inner ℝ (B i-B j) h)^2/2 := by
  unfold pairPath pairComponent
  generalize heq : B i-B j=e
  have he : inner ℝ e e=2 := by rw [← heq];exact regular_edge_inner B hG i j hij
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq h]
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,he,real_inner_comm h e]
  ring

theorem pairPath_norm_le (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) (h : FSC.Coord d) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖pairPath B i j h t‖ ≤ ‖h‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pairPath_norm_sq B hG i j hij]
  have hs : t^2 ≤ 1 := by
    nlinarith [ht.2,mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs)
    (sq_nonneg (inner ℝ (B i-B j) h))]

theorem pairComponent_scores (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) (h : FSC.Coord d) (k : Fin (n+2)) :
    inner ℝ (B k) (pairComponent B i j h) = pairVelocity i j (inner ℝ (B i-B j) h) k := by
  rw [pairComponent,real_inner_smul_right,inner_sub_right,hG,hG]
  by_cases hki : k=i <;> by_cases hkj : k=j <;>
    simp [pairVelocity,hki,hkj] <;> grind

theorem pairPath_zero_equal_scores (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) (h : FSC.Coord d) :
    scoreOffsets B (pairPath B i j h 0) i=scoreOffsets B (pairPath B i j h 0) j := by
  simp only [scoreOffsets,pairPath,zero_smul,add_zero,inner_sub_right,
    pairComponent_scores B hG i j hij h,pairVelocity,ite_true,if_neg hij.symm]
  simp only [inner_sub_left]
  ring

theorem pairPath_scores_hasDerivAt (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) (h : FSC.Coord d) (t : ℝ) :
    HasDerivAt (fun s => scoreOffsets B (pairPath B i j h s))
      (pairVelocity i j (inner ℝ (B i-B j) h)) t := by
  apply hasDerivAt_pi.mpr
  intro k
  have he : (fun s : ℝ => scoreOffsets B (pairPath B i j h s) k) =
      (fun s : ℝ => (inner ℝ (B k) h-inner ℝ (B k) (pairComponent B i j h))+
        s*pairVelocity i j (inner ℝ (B i-B j) h) k) := by
    funext s
    simp only [scoreOffsets,pairPath,inner_add_right,inner_sub_right,
      real_inner_smul_right,pairComponent_scores B hG i j hij h]
  rw [he]
  simpa only [zero_add,one_mul,Pi.add_apply,id_eq] using
    (hasDerivAt_const t (inner ℝ (B k) h-inner ℝ (B k) (pairComponent B i j h))).fun_add
      ((hasDerivAt_id t).mul_const (pairVelocity i j (inner ℝ (B i-B j) h) k))

def pairMassDifference (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2))
    (h : FSC.Coord d) (t : ℝ) : ℝ :=
  mass B (scoreOffsets B (pairPath B i j h t)) i-
    mass B (scoreOffsets B (pairPath B i j h t)) j

def pairMassDerivative (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2))
    (h : FSC.Coord d) (t : ℝ) : ℝ :=
  massDerivative B (scoreOffsets B (pairPath B i j h t)) i
    (pairVelocity i j (inner ℝ (B i-B j) h))-
  massDerivative B (scoreOffsets B (pairPath B i j h t)) j
    (pairVelocity i j (inner ℝ (B i-B j) h))

theorem pairMassDifference_hasDerivAt (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i ≠ j) (h : FSC.Coord d) (t : ℝ) :
    HasDerivAt (pairMassDifference B i j h) (pairMassDerivative B i j h t) t := by
  have hG' : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hlower := centered_singular_one B hG'
  have hpath := pairPath_scores_hasDerivAt B hG i j hij h t
  have hi := (hasFDerivAt_mass B 1 (by norm_num) hlower
    (scoreOffsets B (pairPath B i j h t)) i).comp_hasDerivAt t hpath
  have hj := (hasFDerivAt_mass B 1 (by norm_num) hlower
    (scoreOffsets B (pairPath B i j h t)) j).comp_hasDerivAt t hpath
  exact hi.sub hj

theorem pairMassDerivative_lower (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i ≠ j)
    (hgap : 0 ≤ inner ℝ (B i-B j) h) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    referenceScale n * Real.exp (-1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*‖h‖^2)*
      inner ℝ (B i-B j) h ≤ pairMassDerivative B i j h t := by
  let L := 1+Real.log ((n:ℝ)+2)
  let κ := Real.exp (-1-facetGaussianConstant*L*‖h‖^2)
  let w0 := (referenceScale n/((n:ℝ)+2))*κ
  have hL : 0 ≤ L := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    dsimp [L]
    linarith
  have hw0 : 0 ≤ referenceScale n/((n:ℝ)+2) :=
    (div_pos (referenceScale_pos n) (by positivity)).le
  have hw (k l : Fin (n+2)) (hkl : k ≠ l) :
      w0 ≤ facetWeight B (scoreOffsets B (pairPath B i j h t)) k l := by
    have hh := regular_shifted_facet_gaussian_lower hn hmean B hG (pairPath B i j h t) k l hkl
    have hnorm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (pairPath_norm_le B hG i j hij h t ht)
    have hmul := mul_le_mul_of_nonneg_left hnorm (mul_nonneg facetGaussianConstant_pos.le hL)
    have he : -1-facetGaussianConstant*L*‖h‖^2 ≤
        -1-facetGaussianConstant*L*‖pairPath B i j h t‖^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hw0).trans hh
  have hlower := centered_singular_one B
    (show ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hG)
  have hh := laplacian_pair_lower (facetWeight B (scoreOffsets B (pairPath B i j h t)))
    w0 (inner ℝ (B i-B j) h) hgap hw i j hij
  unfold pairMassDerivative
  rw [massDerivative_apply B 1 (by norm_num) hlower,
    massDerivative_apply B 1 (by norm_num) hlower]
  have hc : (Fintype.card (Fin (n+2)) : ℝ)*w0*inner ℝ (B i-B j) h =
      referenceScale n*κ*inner ℝ (B i-B j) h := by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,w0]
    field_simp
    <;> ring
  rw [hc] at hh
  exact hh

/-- Literal Gaussian mass separation, with no Jacobian or facet lower-bound
premise. The midpoint symmetry and all path derivatives are proved. -/
theorem regular_mass_separation (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i ≠ j)
    (hgap : 0 ≤ inner ℝ (B i-B j) h) :
    referenceScale n * Real.exp (-1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*‖h‖^2)*
      inner ℝ (B i-B j) h ≤ mass B (scoreOffsets B h) i-mass B (scoreOffsets B h) j := by
  have hcont : ContinuousOn (pairMassDifference B i j h) (Icc (0:ℝ) 1) :=
    fun t _ => (pairMassDifference_hasDerivAt B hG i j hij h t).continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (pairMassDifference B i j h)
    (pairMassDerivative B i j h) (by norm_num : (0:ℝ) < 1) hcont
    (fun t _ => pairMassDifference_hasDerivAt B hG i j hij h t)
  have hzero : pairMassDifference B i j h 0=0 := by
    apply sub_eq_zero.mpr
    exact regular_mass_eq_of_offset_eq B (1/((n:ℝ)+2)) hG
      (scoreOffsets B (pairPath B i j h 0)) i j (pairPath_zero_equal_scores B hG i j hij h)
  have hh := (pairMassDerivative_lower hn hmean B hG h i j hij hgap t ⟨ht.1.le,ht.2.le⟩).trans_eq he
  rw [hzero] at hh
  simpa only [sub_zero,div_one,pairMassDifference,pairPath,one_smul,sub_add_cancel] using hh

end NegativeVotingRegularMassSeparation
