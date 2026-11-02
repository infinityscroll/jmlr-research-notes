import GaussianOneRowRayExclusion
import GaussianRegularQuadraticRepresentation
import GaussianRegularScoreProjection
import Mathlib.Analysis.Convex.Jensen

/-! Actual fixed-label covariance symmetrization. The averaging is over a
finite stabilizer and includes singular covariance matrices. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators Classical RealInnerProductSpace
namespace NegativeVotingOneRowSymmetrization
open NegativeVoting NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
  NegativeVotingCovarianceRealization NegativeVotingCovarianceConcavity
  NegativeVotingPositiveCovariance NegativeVotingFanCovarianceValue
  NegativeVotingCenteredParseval NegativeVotingCovarianceCoercivity
  NegativeVotingOneRowCovarianceRay NegativeVotingOneRowRayExclusion
  NegativeVotingRegularQuadraticRepresentation NegativeVotingCentroidOptimization
  NegativeVotingRegularScoreProjection
  NegativeVotingCovarianceOptimizerDegree
variable {m d e : ℕ} [NeZero m]

theorem potential_permute (B : Fin m → FSC.Coord d) (p h : Fin m → ℝ)
    (π : Equiv.Perm (Fin m)) :
    potential (fun j => B (π j)) (fun j => p (π j)) (fun j => h (π j))=potential B p h := by
  unfold potential expectedMax
  have he : (fun x : FSC.Coord d => maxScore (scores (fun j => B (π j)) (fun j => h (π j)) x))=
      (fun x => maxScore (scores B h x)) := by
    funext x
    exact maxScore_perm (scores B h x) π
  rw [he,Equiv.sum_comp π (fun j => p j*h j)]

theorem optimizedValue_permute (B : Fin m → FSC.Coord d) (p : Fin m → ℝ)
    (π : Equiv.Perm (Fin m)) :
    optimizedValue (fun j => B (π j)) (fun j => p (π j))=optimizedValue B p := by
  unfold optimizedValue
  congr 1
  ext y
  constructor
  · rintro ⟨h,rfl⟩
    let k : centeredGauge (Fin m) := ⟨fun j => (h : Fin m → ℝ) (π.symm j),by
      change ∑ j,(h : Fin m → ℝ) (π.symm j)=0
      rw [Equiv.sum_comp]
      exact h.property⟩
    refine ⟨k,?_⟩
    have hh := potential_permute B p k π
    simpa only [k,Equiv.symm_apply_apply] using hh.symm
  · rintro ⟨h,rfl⟩
    let k : centeredGauge (Fin m) := ⟨fun j => (h : Fin m → ℝ) (π j),by
      change ∑ j,(h : Fin m → ℝ) (π j)=0
      rw [Equiv.sum_comp]
      exact h.property⟩
    exact ⟨k,potential_permute B p h π⟩

abbrev LabelStabilizer (i : Fin m) := MulAction.stabilizer (Equiv.Perm (Fin m)) i

def averagedCovariance (b : Fin m → FSC.Coord d) (B : Fin m → FSC.Coord e) (i : Fin m) :
    FSC.Coord d →L[ℝ] FSC.Coord d :=
  (Fintype.card (LabelStabilizer i):ℝ)⁻¹ •
    ∑ π : LabelStabilizer i,rowCovariance b (fun j => B (π.val j))

theorem stabilizer_card_pos (i : Fin m) : 0 < (Fintype.card (LabelStabilizer i):ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem rowCovariance_pairing (b : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0) (j k : Fin m) :
    inner ℝ (b j) (rowCovariance b B (b k))=inner ℝ (B j) (B k) := by
  unfold rowCovariance
  change inner ℝ (b j) ((reconstruction b B).adjoint (reconstruction b B (b k)))=_
  rw [ContinuousLinearMap.adjoint_inner_right,reconstruction_row b B hG hB,
    reconstruction_row b B hG hB]

theorem averagedCovariance_pairing (b : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0) (i j k : Fin m) :
    inner ℝ (b j) (averagedCovariance b B i (b k))=
      (Fintype.card (LabelStabilizer i):ℝ)⁻¹ *
        ∑ π : LabelStabilizer i,inner ℝ (B (π.val j)) (B (π.val k)) := by
  simp only [averagedCovariance,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    real_inner_smul_right,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  apply rowCovariance_pairing b hG
  rw [Equiv.sum_comp π.val,hB]

theorem averagedCovariance_value_ge (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0) (i : Fin m) :
    optimizedValue B (fun _ => 1/(m:ℝ)) ≤
      operatorValue b (fun _ => 1/(m:ℝ)) (averagedCovariance b B i) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast NeZero.pos m
  have hp : ∀ j : Fin m,0 < (1/(m:ℝ)) := fun _ => by positivity
  have hs : (∑ _ : Fin m,1/(m:ℝ))=1 := by simp [ne_of_gt hm0]
  have hsum : (∑ _ : LabelStabilizer i,(Fintype.card (LabelStabilizer i):ℝ)⁻¹)=1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt (stabilizer_card_pos i))
  have hh := (operatorValue_concaveOn_psd b (fun _ => 1/(m:ℝ)) hp hs).le_map_sum
    (t := Finset.univ) (w := fun _ : LabelStabilizer i => (Fintype.card (LabelStabilizer i):ℝ)⁻¹)
    (p := fun π : LabelStabilizer i => rowCovariance b (fun j => B (π.val j)))
    (fun _ _ => by positivity) (by simpa using hsum) (fun π _ => rowCovariance_psd b _)
  have hv (π : LabelStabilizer i) :
      operatorValue b (fun _ => 1/(m:ℝ)) (rowCovariance b (fun j => B (π.val j)))=
        optimizedValue B (fun _ => 1/(m:ℝ)) := by
    rw [rowCovariance_value b hG _ (by rw [Equiv.sum_comp π.val,hB])]
    exact optimizedValue_permute B (fun _ => 1/(m:ℝ)) π.val
  simp only [hv,smul_eq_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have he : (Fintype.card (LabelStabilizer i):ℝ)*
      ((Fintype.card (LabelStabilizer i):ℝ)⁻¹*optimizedValue B (fun _ => 1/(m:ℝ)))=
        optimizedValue B (fun _ => 1/(m:ℝ)) := by
    rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt (stabilizer_card_pos i)),one_mul]
  rw [he] at hh
  simpa only [averagedCovariance,Finset.smul_sum] using hh

theorem averagedCovariance_invariant (b : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0) (i : Fin m)
    (τ : LabelStabilizer i) (j k : Fin m) :
    inner ℝ (b (τ.val j)) (averagedCovariance b B i (b (τ.val k)))=
      inner ℝ (b j) (averagedCovariance b B i (b k)) := by
  rw [averagedCovariance_pairing b hG B hB,averagedCovariance_pairing b hG B hB]
  congr 1
  let f : LabelStabilizer i → ℝ := fun π => inner ℝ (B (π.val j)) (B (π.val k))
  change (∑ π : LabelStabilizer i,f (π*τ))=∑ π : LabelStabilizer i,f π
  exact Equiv.sum_comp (Equiv.mulRight τ) f

theorem averagedCovariance_diagonal (b : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0) (i : Fin m) :
    inner ℝ (b i) (averagedCovariance b B i (b i))=‖B i‖^2 := by
  rw [averagedCovariance_pairing b hG B hB]
  have he (π : LabelStabilizer i) : π.val i=i := π.property
  simp only [he,real_inner_self_eq_norm_sq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (ne_of_gt (stabilizer_card_pos i)),one_mul]

theorem averagedCovariance_trace (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0) (i : Fin m) :
    operatorTrace (averagedCovariance b B i)=rowEnergy B := by
  rw [operatorTrace,parseval_trace b hP]
  simp_rw [averagedCovariance_pairing b hG B hB,real_inner_self_eq_norm_sq]
  rw [←Finset.mul_sum,Finset.sum_comm]
  have he (π : LabelStabilizer i) : (∑ j,‖B (π.val j)‖^2)=rowEnergy B :=
    Equiv.sum_comp π.val (fun j => ‖B j‖^2)
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (ne_of_gt (stabilizer_card_pos i)),one_mul]

theorem averagedCovariance_symmetric (b : Fin m → FSC.Coord d)
    (B : Fin m → FSC.Coord e) (i : Fin m) :
    (averagedCovariance b B i).toLinearMap.IsSymmetric := by
  have hh : (∑ π : LabelStabilizer i,rowCovariance b (fun j => B (π.val j))).toLinearMap.IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.sum_apply,sum_inner,inner_sum]
    apply Finset.sum_congr rfl
    intro π _
    exact (rowCovariance_psd b (fun j => B (π.val j))).1 x y
  exact hh.smul (by rfl)

theorem operator_eq_of_frame_pairings (b : Fin m → FSC.Coord d)
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d)
    (h : ∀ j k,inner ℝ (b j) (C (b k))=inner ℝ (b j) (D (b k))) : C=D := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  conv_lhs => rw [←hP y,←hP x]
  conv_rhs => rw [←hP y,←hP x]
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,h]

/-- The averaged covariance is exactly the one-row ray at the preserved
normalized squared row length. -/
theorem averagedCovariance_eq_oneRow (hm : 3 ≤ m)
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0)
    (henergy : rowEnergy B=(m:ℝ)-1) (i : Fin m) :
    averagedCovariance b B i=oneRowCovariance b i ((m:ℝ)/((m:ℝ)-1)*‖B i‖^2) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by linarith
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  have hm2 : (m:ℝ)-2 ≠ 0 := by linarith
  let C := averagedCovariance b B i
  let I := ContinuousLinearMap.id ℝ (FSC.Coord d)
  let q : Fin m → Fin m → ℝ := fun j k => inner ℝ (b j) ((C-I) (b k))
  have hsym : ∀ j k,q j k=q k j := by
    intro j k
    have hh := ((averagedCovariance_symmetric b B i).sub
      (show I.toLinearMap.IsSymmetric from fun x y => rfl)) (b j) (b k)
    change inner ℝ ((C-I) (b j)) (b k)=inner ℝ (b j) ((C-I) (b k)) at hh
    dsimp [q]
    rw [←hh,real_inner_comm]
  have hrow : ∀ j,∑ k,q j k=0 := by
    intro j
    simp only [q,←inner_sum,←map_sum,regular_rows_sum_zero b hG,map_zero,inner_zero_right]
  have htrace : ∑ j,q j j=0 := by
    rw [show (∑ j,q j j)=operatorTrace (C-I) from (parseval_trace b hP (C-I)).symm]
    have hc : operatorTrace C=(m:ℝ)-1 := (averagedCovariance_trace b hG hP B hB i).trans henergy
    have hi : operatorTrace I=(m:ℝ)-1 := by
      rw [operatorTrace,parseval_trace b hP]
      simp only [I,ContinuousLinearMap.id_apply,hG,eq_self_iff_true,ite_true,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
    simpa only [operatorTrace,ContinuousLinearMap.toLinearMap_sub,map_sub,hc,hi,sub_self] using
      (show operatorTrace C-operatorTrace I=0 by rw [hc,hi]; ring)
  have hinv : ∀ a c,a≠i → c≠i → ∀ j k,q (Equiv.swap a c j) (Equiv.swap a c k)=q j k := by
    intro a c ha hc j k
    let τ : LabelStabilizer i := ⟨Equiv.swap a c,by
      change Equiv.swap a c i=i
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hc)⟩
    have hh := averagedCovariance_invariant b hG B hB i τ j k
    dsimp [q,C,I] at *
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_sub_right,hG,
      (Equiv.swap a c).injective.eq_iff]
    exact congrArg (fun z : ℝ => z-((if j=k then 1 else 0)-1/(m:ℝ))) hh
  have hqi : q i i=‖B i‖^2-(1-1/(m:ℝ)) := by
    dsimp [q,C,I]
    rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_sub_right,
      averagedCovariance_diagonal b hG B hB,hG]
    simp
  apply operator_eq_of_frame_pairings b hP
  intro j k
  have hh := entries_of_stabilizer hm i q hsym hrow htrace hinv j k
  rw [hqi] at hh
  dsimp [q,I] at hh
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_sub_right,hG] at hh
  change inner ℝ (b j) (C (b k))=_
  simp only [oneRowCovariance,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_add_right,
    real_inner_smul_right,inner_sub_right,rowProjector,rankOne_apply,hG]
  unfold centeredCoordinate at hh
  unfold transverseCoefficient
  rw [sub_eq_iff_eq_add] at hh
  rw [show (if i=j then (1:ℝ) else 0)=(if j=i then 1 else 0) by simp only [eq_comm]] at hh
  rw [hh]
  field_simp
  <;> ring

theorem normalized_row_parameter_mem (hm : 3 ≤ m)
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0)
    (henergy : rowEnergy B=(m:ℝ)-1) (i : Fin m) :
    (m:ℝ)/((m:ℝ)-1)*‖B i‖^2 ∈ Icc (0:ℝ) ((m:ℝ)-1) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hm1 : (0:ℝ) < (m:ℝ)-1 := by linarith
  constructor
  · positivity
  let C := rowCovariance b B
  have ht : operatorTrace C=(m:ℝ)-1 := (rowCovariance_trace b hG hP B hB).trans henergy
  have hC : ‖C‖ ≤ (m:ℝ)-1 := by
    rw [←ht]
    exact norm_le_trace (rowCovariance_psd b B)
  have hnorm : ‖b i‖^2=1-1/(m:ℝ) := by
    rw [←real_inner_self_eq_norm_sq,hG]
    simp
  have hb : ‖B i‖^2 ≤ ((m:ℝ)-1)*(1-1/(m:ℝ)) := by
    rw [←real_inner_self_eq_norm_sq,←rowCovariance_pairing b hG B hB i i]
    calc
      inner ℝ (b i) (C (b i)) ≤ ‖b i‖ * ‖C (b i)‖ := real_inner_le_norm _ _
      _ ≤ ‖b i‖*(‖C‖*‖b i‖) := mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _)
      _ = ‖C‖*‖b i‖^2 := by ring
      _ ≤ ((m:ℝ)-1)*‖b i‖^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
      _ = _ := by rw [hnorm]
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (m:ℝ)/((m:ℝ)-1) by positivity)
  have he : (m:ℝ)/((m:ℝ)-1)*(((m:ℝ)-1)*(1-1/(m:ℝ)))=(m:ℝ)-1 := by
    field_simp
    <;> ring
  simpa only [he] using hh

theorem oneRowValue_dominates (hm : 3 ≤ m)
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin m → FSC.Coord e) (hB : ∑ i,B i=0)
    (henergy : rowEnergy B=(m:ℝ)-1) (i : Fin m) :
    optimizedValue B (fun _ => 1/(m:ℝ)) ≤
      operatorValue b (fun _ => 1/(m:ℝ))
        (oneRowCovariance b i ((m:ℝ)/((m:ℝ)-1)*‖B i‖^2)) := by
  rw [←averagedCovariance_eq_oneRow hm b hG hP B hB henergy i]
  exact averagedCovariance_value_ge b hG B hB i

omit [NeZero m] in
/-- Literal squared row-length control for every centered rectangular target,
without any rank or row nonvanishing premise. -/
theorem normalized_row_close_of_small_deficit (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin (n+2) → FSC.Coord e) (hB : ∑ i,B i=0)
    (henergy : rowEnergy B=(n:ℝ)+1)
    (hloss : operatorValue b (NegativeVotingBalancedReference.uniformMass n)
        (ContinuousLinearMap.id ℝ (FSC.Coord d))-
      optimizedValue B (NegativeVotingBalancedReference.uniformMass n) <
        1/(16777216*Real.pi*((n:ℝ)+2))) (i : Fin (n+2)) :
    |((n:ℝ)+2)/((n:ℝ)+1)*‖B i‖^2-1| < 1/256 := by
  have hm : 3 ≤ n+2 := by omega
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have he : rowEnergy B=((n+2:ℕ):ℝ)-1 := by push_cast; linarith
  have ha := normalized_row_parameter_mem hm b hG' hP B hB he i
  have hv := oneRowValue_dominates hm b hG' hP B hB he i
  have hid : ((n+2:ℕ):ℝ)-1=(n:ℝ)+1 := by push_cast; ring
  rw [hid] at ha hv
  simp only [Nat.cast_add,Nat.cast_ofNat] at ha hv
  apply oneRowValue_small_deficit hn b hG hP i _ ha
  exact lt_of_le_of_lt (sub_le_sub_left hv _) hloss

end NegativeVotingOneRowSymmetrization
