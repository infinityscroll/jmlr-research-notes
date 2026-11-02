import GaussianRegularFacetRangeGeometry
import GaussianRegularMassSeparation

/-! Score range is unchanged by sign and scales linearly; the actual regular
pair-midpoint path never increases it. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetRange
open NegativeVoting NegativeVotingBalancedReference NegativeVotingFacetConditionalPlane
  NegativeVotingRegularMassSeparation NegativeVotingFan

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem utilityRange_le_of_between (u : ι → ℝ) (a b : ℝ)
    (hu : ∀i,u i∈Icc a b) : utilityRange u ≤ b-a := by
  have hlo : maxScore (fun i => -u i) ≤ -a :=
    Finset.sup'_le _ _ (fun i _ => by linarith [(hu i).1])
  have hhi : maxScore u ≤ b := Finset.sup'_le _ _ (fun i _ => (hu i).2)
  unfold utilityRange
  linarith

theorem utilityRange_neg (u : ι → ℝ) : utilityRange (fun i => -u i)=utilityRange u := by
  simp only [utilityRange,neg_neg,add_comm]

theorem utilityRange_mul_pos (u : ι → ℝ) (a : ℝ) (ha : 0<a) :
    utilityRange (fun i => a*u i)=a*utilityRange u := by
  have he : (fun i => -(a*u i))=(fun i => a*(-u i)) := by funext i;ring
  rw [utilityRange,maxScore_mul_pos u a ha,he,maxScore_mul_pos (fun i => -u i) a ha,
    utilityRange,mul_add]

theorem utilityRange_neg_mul_pos (u : ι → ℝ) (a : ℝ) (ha : 0<a) :
    utilityRange (fun i => -a*u i)=a*utilityRange u := by
  have he : (fun i => -a*u i)=(fun i => -(a*u i)) := by funext i;ring
  rw [he,utilityRange_neg,utilityRange_mul_pos u a ha]

end Finite

private theorem pair_interpolation_mem_Icc (u v a b t : ℝ)
    (hu : u∈Icc a b) (hv : v∈Icc a b) (ht : t∈Icc (0:ℝ) 1) :
    (u+v)/2+t*(u-v)/2∈Icc a b := by
  have hp : 0 ≤ (1+t)/2 := by linarith [ht.1]
  have hm : 0 ≤ (1-t)/2 := by linarith [ht.2]
  have hlo1 := mul_le_mul_of_nonneg_left hu.1 hp
  have hlo2 := mul_le_mul_of_nonneg_left hv.1 hm
  have hhi1 := mul_le_mul_of_nonneg_left hu.2 hp
  have hhi2 := mul_le_mul_of_nonneg_left hv.2 hm
  exact ⟨by nlinarith,by nlinarith⟩

variable {n d : ℕ}

theorem pairPath_score_coordinate (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (h : FSC.Coord d) (t : ℝ) (k : Fin (n+2)) :
    scoreOffsets B (pairPath B i j h t) k=scoreOffsets B h k+
      (t-1)*pairVelocity i j (inner ℝ (B i-B j) h) k := by
  simp only [scoreOffsets,pairPath,inner_add_right,inner_sub_right,real_inner_smul_right,
    pairComponent_scores B hG i j hij h]
  ring

theorem pairPath_scores_between (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (h : FSC.Coord d) (t a b : ℝ)
    (ht : t∈Icc (0:ℝ) 1) (hh : ∀k,scoreOffsets B h k∈Icc a b) (k : Fin (n+2)) :
    scoreOffsets B (pairPath B i j h t) k∈Icc a b := by
  rw [pairPath_score_coordinate B hG i j hij h t k]
  by_cases hki : k=i
  · subst k
    have hc := pair_interpolation_mem_Icc _ _ a b t (hh i) (hh j) ht
    simp only [pairVelocity,ite_true,inner_sub_left,scoreOffsets] at hc ⊢
    convert hc using 1 <;> ring
  by_cases hkj : k=j
  · subst k
    have hc := pair_interpolation_mem_Icc _ _ a b t (hh j) (hh i) ht
    simp only [pairVelocity,if_neg (Ne.symm hij),ite_true,inner_sub_left,scoreOffsets] at hc ⊢
    convert hc using 1 <;> ring
  · simpa only [pairVelocity,if_neg hki,if_neg hkj,mul_zero,add_zero] using hh k

/-- The actual two-label interpolation stays in the original utility range. -/
theorem pairPath_utilityRange_le (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (h : FSC.Coord d) (t : ℝ)
    (ht : t∈Icc (0:ℝ) 1) :
    utilityRange (scoreOffsets B (pairPath B i j h t)) ≤ utilityRange (scoreOffsets B h) := by
  let u := scoreOffsets B h
  have hu (k : Fin (n+2)) : u k∈Icc (-maxScore (fun l => -u l)) (maxScore u) := by
    have hn : -u k ≤ maxScore (fun l => -u l) :=
      Finset.le_sup' (fun l => -u l) (Finset.mem_univ k)
    exact ⟨by linarith,Finset.le_sup' u (Finset.mem_univ k)⟩
  have hp := utilityRange_le_of_between (scoreOffsets B (pairPath B i j h t)) _ _
    (pairPath_scores_between B hG i j hij h t _ _ ht hu)
  simpa only [utilityRange,sub_neg_eq_add,u] using hp

end NegativeVotingRegularFacetRange
