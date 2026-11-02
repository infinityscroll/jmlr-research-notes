import GaussianExteriorRoutingMargin
import GaussianGlobalCovarianceDeficit

/-! Exact regular routing loss from centroid geometry and approximation of the
literal regular-orbit infimum. No orbit-minimizer assumption is used. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingExteriorRoutingGeometry
open NegativeVoting NegativeVotingFan NegativeVotingFanValue NegativeVotingAssignmentDuality
  NegativeVotingCentroidOptimization NegativeVotingBalancedReference NegativeVotingExteriorOrbit
  NegativeVotingProcrustes NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingExteriorRoutingMargin NegativeVotingRegularReferenceNormalization
variable {n d e : ℕ}

theorem scaled_regular_normalized_gram (R:Fin (n+2)→FSC.Coord e) (hR:ScaledRegularGram n R) :
    ∀i j,inner ℝ (((referenceScale n)⁻¹•R) i) (((referenceScale n)⁻¹•R) j)=
      (if i=j then 1 else 0)-1/((n:ℝ)+2) := by
  intro i j
  simp only [Pi.smul_apply,real_inner_smul_left,real_inner_smul_right]
  rw [hR i j]
  field_simp [ne_of_gt (referenceScale_pos n)]

theorem scaled_regular_expectedMax (R:Fin (n+2)→FSC.Coord e) (hR:ScaledRegularGram n R) :
    expectedMax R 0=referenceFirstWeight n := by
  let U := (referenceScale n)⁻¹•R
  have hU := scaled_regular_normalized_gram R hR
  have heq : R=(referenceScale n)•U := by
    simp only [U,smul_smul,mul_inv_cancel₀ (ne_of_gt (referenceScale_pos n)),one_smul]
  have he : expectedMax R 0=referenceScale n*expectedMax U 0 := by
    rw [heq]
    unfold expectedMax
    have hp (x:FSC.Coord e) : maxScore (scores (referenceScale n•U) 0 x)=
        referenceScale n*maxScore (scores U 0 x) := by
      have hs : scores (referenceScale n•U) 0 x=(fun i=>referenceScale n*scores U 0 x i) := by
        funext i
        simp only [scores,Pi.smul_apply,real_inner_smul_left,Pi.zero_apply,add_zero]
      rw [hs]
      exact maxScore_mul_pos _ _ (referenceScale_pos n)
    simp_rw [hp]
    exact integral_const_mul _ _
  rw [he,regular_fan_expectedMax U hU]
  unfold referenceScale referenceFirstWeight
  field_simp

/-- The actual integrated score loss is an exact square completion. -/
theorem regular_routing_loss_square_completion (R:Fin (n+2)→FSC.Coord e)
    (hR:ScaledRegularGram n R) (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ)
    (hf:Feasible p f) :
    2*(∫x,fanScoreLoss R f x ∂stdGaussian (FSC.Coord e))=
      referenceFirstWeight n-centroidEnergy f+rowEnergy (R-centroidRows f) := by
  have he : (∫x,fanScoreLoss R f x ∂stdGaussian (FSC.Coord e))=
      expectedMax R 0-assignmentValue R f := by
    have hmax : Integrable (fun x=>maxScore (scores R 0 x)) (stdGaussian (FSC.Coord e)) := by
      apply integrable_finite_max _ _ Finset.univ Finset.univ_nonempty
      intro i _
      convert IsGaussian.integrable_dual (stdGaussian (FSC.Coord e)) (innerSL ℝ (R i)) using 1
      funext x
      simp only [scores,Pi.zero_apply,add_zero,innerSL_apply_apply]
    have hmix := assignmentValue_integrable R p f hf
    change (∫x,maxScore (scores R 0 x)-(∑i,f x i*scores R 0 x i) ∂stdGaussian (FSC.Coord e))=_
    simp only [scores,Pi.zero_apply,add_zero] at hmax ⊢
    exact integral_sub hmax hmix
  rw [he,scaled_regular_expectedMax R hR]
  have hh := assignment_square_completion R p f hf
  rw [scaled_regular_row_energy R hR] at hh
  linarith

/-- Existence of an orbit element at any strict upper bound on the orbit
infimum. The regular orbit is nonempty in every admissible ambient dimension. -/
theorem exists_regular_rows_near_infimum
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hde:d≤e) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0)
    (r:ℝ) (hr:regularOrbitDistance n B < r) :
    ∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
      Real.sqrt (rowEnergy (R-B)) < r := by
  obtain ⟨R,hR,hbound⟩ := exists_regular_rows_with_distance_bound b hG hP hde B hB
  let S:Set ℝ := {a|∃T:Fin (n+2)→FSC.Coord e,ScaledRegularGram n T ∧
    a=Real.sqrt (∑i,‖B i-T i‖^2)}
  have hS:S.Nonempty := ⟨_,R,hR,rfl⟩
  obtain ⟨a,⟨T,hT,ha⟩,har⟩ := exists_lt_of_csInf_lt hS hr
  refine ⟨T,hT,?_⟩
  rw [ha] at har
  simpa only [rowEnergy,Pi.sub_apply,norm_sub_rev] using har

/-- Exterior centroid distance gives a concrete regular comparison rule and
an upper bound on its literal routing loss. All references are chosen before
applying the mismatch or signed-tail estimates. -/
theorem exists_regular_routing_loss_bound
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x) (hde:d≤e)
    (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ) (hf:Feasible p f)
    (J A L:ℝ) (hJ:0 ≤ J) (hA:0 ≤ A) (hL:1 ≤ L)
    (hdef:referenceFirstWeight n-centroidEnergy f ≤ J)
    (hd:0 < regularOrbitDistance n (centroidRows f))
    (hdist:(regularOrbitDistance n (centroidRows f))^2 ≤
      A*(((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*L*J) :
    ∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
      (∫x,fanScoreLoss R f x ∂stdGaussian (FSC.Coord e)) ≤
        (1+2*A)*(((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*L*J := by
  obtain ⟨R,hR,hclose⟩ := exists_regular_rows_near_infimum b hG hP hde (centroidRows f)
    (centroidRows_sum_zero p f hf) (2*regularOrbitDistance n (centroidRows f)) (by linarith)
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hclose.le 2
  rw [Real.sq_sqrt (rowEnergy_nonneg _)] at hsq
  have hE : rowEnergy (R-centroidRows f) ≤
      4*A*(((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*L*J := by nlinarith
  have hid := regular_routing_loss_square_completion R hR p f hf
  have hm : (1:ℝ) ≤ (n:ℝ)+2 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hs : 1 ≤ Real.sqrt ((n:ℝ)+2) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hmul : 1 ≤ (((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm hs) hL
  have hJmul := mul_le_mul_of_nonneg_right hmul hJ
  refine ⟨R,hR,?_⟩
  nlinarith


/-- A concrete regular reference realizes the exterior mismatch bound. -/
theorem exists_regular_mismatch_bound
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x) (hde:d≤e)
    (hscale:Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n)
    (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ) (hf:Feasible p f)
    (J A L:ℝ) (hJ:0 ≤ J) (hA:0 ≤ A) (hL:1 ≤ L)
    (hdef:referenceFirstWeight n-centroidEnergy f ≤ J)
    (hd:0 < regularOrbitDistance n (centroidRows f))
    (hdist:(regularOrbitDistance n (centroidRows f))^2 ≤
      A*(((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*L*J) :
    ∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
      (∫x,mismatch R f x ∂stdGaussian (FSC.Coord e)) ≤
        2*(regularMarginConstant+1)*Real.sqrt ((1+2*A)*
          ((n:ℝ)+2)^2*Real.sqrt ((n:ℝ)+2)*L*J) := by
  obtain ⟨R,hR,hcost⟩ := exists_regular_routing_loss_bound b hG hP hde p f hf
    J A L hJ hA hL hdef hd hdist
  let U := (referenceScale n)⁻¹•R
  have hU : ∀i j,inner ℝ (U i) (U j)=
      (if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using scaled_regular_normalized_gram R hR
  have heq : (referenceScale n)•U=R := by
    simp only [U,smul_smul,mul_inv_cancel₀ (ne_of_gt (referenceScale_pos n)),one_smul]
  have hmismatch := regular_mismatch_integral_sqrt (by omega) U hU (referenceScale n)
    (referenceScale_pos n) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale) f hf.1 hf.2.1
  rw [heq] at hmismatch
  simp only [Nat.cast_add,Nat.cast_ofNat] at hmismatch
  have hrad : ((n:ℝ)+2)*(∫x,fanScoreLoss R f x ∂stdGaussian (FSC.Coord e)) ≤
      (1+2*A)*((n:ℝ)+2)^2*Real.sqrt ((n:ℝ)+2)*L*J := by
    convert mul_le_mul_of_nonneg_left hcost (show 0 ≤ (n:ℝ)+2 by positivity) using 1 <;> ring
  refine ⟨R,hR,hmismatch.trans ?_⟩
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad)
  linarith [regularMarginConstant_ge_one]

end NegativeVotingExteriorRoutingGeometry
