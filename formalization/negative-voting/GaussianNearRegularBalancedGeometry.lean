import GaussianBalancedMomentGeometry
import GaussianConditionedFacetGeneral
import GaussianCenteredParsevalBasis

/-! Explicit geometry of the actual uniformly balanced row segment in a
Frobenius ball around a scaled regular Gram family, in any ambient dimension. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNearRegularBalancedGeometry
open NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingWeightedFacet NegativeVotingDisintegration
  NegativeVotingFanJacobian NegativeVotingBalancedMomentGeometry
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingFanQuadraticMoments
  NegativeVotingPolynomialFacetLogBound NegativeVotingCenteredParseval
variable {d m : ℕ} [NeZero m]

theorem weighted_sum_norm_sq_le (D : Fin m→FSC.Coord d) (c : Fin m→ℝ) :
    ‖∑ i,c i • D i‖^2 ≤ (∑ i,c i^2)*(∑ i,‖D i‖^2) := by
  have hn : ‖∑ i,c i • D i‖ ≤ ∑ i,|c i| *‖D i‖ := by
    simpa only [norm_smul,Real.norm_eq_abs] using norm_sum_le (s:=Finset.univ) (fun i=>c i • D i)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i=>|c i|) (fun i=>‖D i‖)
  simp only [sq_abs] at hc
  exact hs.trans hc

theorem regular_scaled_singular
    (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ)) (α : ℝ) :
    CenteredSingularLowerBound (α • R) α := by
  intro c hc
  have he : (∑ i,c i • (α • R) i)=α • (∑ i,c i • R i) := by
    simp only [Pi.smul_apply,smul_comm (c _),Finset.smul_sum]
  rw [he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,weighted_norm_sq R hG,hc]
  simp

/-- Frobenius perturbations preserve the centered singular bound without a
factor depending on the number of rows. -/
theorem singular_of_frobenius_close
    (B D : Fin m→FSC.Coord d) (α : ℝ) (hα : 0<α)
    (hB : CenteredSingularLowerBound B α)
    (hD : ∑ i,‖D i‖^2 ≤ α^2/256) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    CenteredSingularLowerBound (B+t•D) (α/2) := by
  intro c hc
  let q := Real.sqrt (∑ i,c i^2)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2=∑ i,c i^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _=>sq_nonneg _)
  have hb : α*q ≤ ‖∑ i,c i • B i‖ := by
    apply (sq_le_sq₀ (mul_nonneg hα.le hq) (norm_nonneg _)).mp
    rw [mul_pow,hq2]
    exact hB c hc
  have hd : ‖∑ i,c i • D i‖ ≤ α/16*q := by
    have hs := (weighted_sum_norm_sq_le D c).trans
      (mul_le_mul_of_nonneg_left hD (Finset.sum_nonneg fun i _=>sq_nonneg _))
    rw [←hq2] at hs
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity : 0 ≤ α/16) hq)).mp
    convert hs using 1 <;> ring
  have he : (∑ i,c i • (B+t•D) i)=(∑ i,c i • B i)+t•(∑ i,c i • D i) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_add,Finset.sum_add_distrib,
      smul_comm (c _),Finset.smul_sum]
  have htD : ‖t•(∑ i,c i • D i)‖ ≤ α/16*q := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left hd ht.1).trans
      (by nlinarith [mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (mul_nonneg (by positivity : 0 ≤ α/16) hq)])
  have htri := norm_sub_le (∑ i,c i • (B+t•D) i) (t•(∑ i,c i • D i))
  have heq : (∑ i,c i • (B+t•D) i)-t•(∑ i,c i • D i)=∑ i,c i • B i := by rw [he]; abel
  rw [heq] at htri
  have hn : α/2*q ≤ ‖∑ i,c i • (B+t•D) i‖ := by nlinarith
  have hh := pow_le_pow_left₀ (mul_nonneg (by positivity : 0 ≤ α/2) hq) hn 2
  simpa only [mul_pow,hq2] using hh

theorem row_perturbation_norm_le
    (D : Fin m→FSC.Coord d) (α : ℝ) (hα : 0<α)
    (hD : ∑ i,‖D i‖^2 ≤ α^2/256) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (i : Fin m) :
    ‖(t•D) i‖ ≤ α/16 := by
  have hi := (Finset.single_le_sum (fun j _=>sq_nonneg ‖D j‖) (Finset.mem_univ i)).trans hD
  have hn : ‖D i‖ ≤ α/16 := by nlinarith [norm_nonneg (D i)]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_left hn ht.1).trans (by nlinarith [ht.2])

theorem regular_row_norm_le
    (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ)) (i : Fin m) :
    ‖R i‖ ≤ 1 := by
  have hi := hG i i
  rw [real_inner_self_eq_norm_sq] at hi
  simp only [ite_true] at hi
  nlinarith [one_div_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) m),norm_nonneg (R i)]

theorem inner_perturbation_bound (a b u v : FSC.Coord d) (α : ℝ) (hα : 0<α)
    (ha : ‖a‖ ≤ α) (hb : ‖b‖ ≤ α) (hu : ‖u‖ ≤ α/16) (hv : ‖v‖ ≤ α/16) :
    |inner ℝ (a+u) (b+v)-inner ℝ a b| ≤ α^2/6 := by
  have he : inner ℝ (a+u) (b+v)-inner ℝ a b=
      inner ℝ a v+inner ℝ u b+inner ℝ u v := by
    simp only [inner_add_left,inner_add_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ a v|+|inner ℝ u b|+|inner ℝ u v| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖a‖*‖v‖+‖u‖*‖b‖+‖u‖*‖v‖ :=
      add_le_add (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
        (abs_real_inner_le_norm _ _)
    _ ≤ α*(α/16)+(α/16)*α+(α/16)*(α/16) :=
      add_le_add (add_le_add (mul_le_mul ha hv (norm_nonneg _) hα.le)
        (mul_le_mul hu hb (norm_nonneg _) (by positivity)))
        (mul_le_mul hu hv (norm_nonneg _) (by positivity))
    _ ≤ _ := by nlinarith [sq_nonneg α]

/-- All geometric Gram and edge premises hold throughout the actual row
segment, with explicit constants and no ambient spanning premise. -/
theorem segment_geometry
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    CenteredSingularLowerBound (α•R+t•D) (α/2) ∧
    (∀ i,α^2/2 ≤ inner ℝ ((α•R+t•D) i) ((α•R+t•D) i)) ∧
    (∀ i,inner ℝ ((α•R+t•D) i) ((α•R+t•D) i) ≤ 2*α^2) ∧
    (∀ i j,i≠j→inner ℝ ((α•R+t•D) i) ((α•R+t•D) j) ≤ α^2/4) ∧
    (∀ i j,‖(α•R+t•D) i-(α•R+t•D) j‖ ≤ 2*α) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmi : 0 ≤ (m:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg m)
  have hmi3 : (m:ℝ)⁻¹ ≤ 1/3 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hmR
  have hr (i : Fin m) : ‖(α•R) i‖ ≤ α := by
    simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hα,mul_one] using
      mul_le_mul_of_nonneg_left (regular_row_norm_le R hG i) hα.le
  have he (i j : Fin m) :
      |inner ℝ ((α•R+t•D) i) ((α•R+t•D) j)-α^2*inner ℝ (R i) (R j)| ≤ α^2/6 := by
    simpa only [Pi.add_apply,Pi.smul_apply,real_inner_smul_left,real_inner_smul_right,pow_two,
      mul_assoc] using inner_perturbation_bound ((α•R) i) ((α•R) j) ((t•D) i) ((t•D) j)
      α hα (hr i) (hr j) (row_perturbation_norm_le D α hα hD t ht i)
      (row_perturbation_norm_le D α hα hD t ht j)
  refine ⟨singular_of_frobenius_close _ D α hα (regular_scaled_singular R hG α) hD t ht,?_,?_,?_,?_⟩
  · intro i
    have hh := (abs_le.mp (he i i)).1
    rw [hG] at hh
    simp only [ite_true,one_div] at hh
    nlinarith [mul_le_mul_of_nonneg_left hmi3 (sq_nonneg α)]
  · intro i
    have hh := (abs_le.mp (he i i)).2
    rw [hG] at hh
    simp only [ite_true,one_div] at hh
    nlinarith [mul_nonneg (sq_nonneg α) hmi]
  · intro i j hij
    have hh := (abs_le.mp (he i j)).2
    rw [hG] at hh
    simp only [if_neg hij,zero_sub,one_div] at hh
    nlinarith [mul_nonneg (sq_nonneg α) hmi]
  · intro i j
    have hbase : ‖(α•R) i-(α•R) j‖ ≤ 3*α/2 := by
      by_cases hij : i=j
      · subst j; simpa using (show (0:ℝ) ≤ 3*α/2 by positivity)
      have hh : ‖R i-R j‖^2=2 := by
        rw [norm_sub_sq_real,←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,
          hG i i,hG j j,hG i j]
        simp only [ite_true,if_neg hij]
        ring
      have hn : ‖R i-R j‖ ≤ 3/2 := by nlinarith [norm_nonneg (R i-R j)]
      simp only [Pi.smul_apply,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hα]
      nlinarith [mul_le_mul_of_nonneg_left hn hα.le]
    have htri : ‖(α•R+t•D) i-(α•R+t•D) j‖ ≤
        ‖(α•R) i-(α•R) j‖+‖(t•D) i‖+‖(t•D) j‖ := by
      have heq : (α•R+t•D) i-(α•R+t•D) j=
          ((α•R) i-(α•R) j)+(t•D) i-(t•D) j := by simp only [Pi.add_apply]; abel
      rw [heq]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    linarith [row_perturbation_norm_le D α hα hD t ht i,
      row_perturbation_norm_le D α hα hD t ht j]

/-- The polynomial probability premise follows from the actual selected
uniform masses throughout the row segment. -/
theorem selected_segment_probability
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (i j : Fin m) (hij : i≠j) :
    (m:ℝ)^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal (α•R+t•D) i j))
        (intrinsicFacet (α•R+t•D) (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) i j)).toReal := by
  let B := α•R+t•D
  let h := selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t
  have hg := segment_geometry hm R D hG α hα hD t ht
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B (α/2) (by positivity) hg.1 i j hij he
  have hmass (l : Fin m) : mass B h l=(m:ℝ)⁻¹ := by
    simpa only [Fintype.card_fin,h,selectedRowOffsets,B] using congrFun (selected_uniform_mass B hinj) l
  have hmass' (l : Fin m) : 1/(2*(Fintype.card (Fin m):ℝ)) ≤ mass B h l := by
    rw [hmass,Fintype.card_fin]
    have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    simpa only [one_div] using one_div_le_one_div_of_le hmpos
      (show (m:ℝ) ≤ 2*m by linarith)
  have hs : ∑ l,h l=0 := (selectedOffsets B (fun _=>(m:ℝ)⁻¹)).property
  have hb := NegativeVotingConditionedFacetGeneral.intrinsicProbability_polynomial_lower
    B (by simpa only [Fintype.card_fin] using hm) (α/2) (2*α) (by positivity)
    (by positivity) hg.1 hg.2.2.2.2 (by field_simp; linarith) h hs hmass' i j hij
  simpa only [Fintype.card_fin,NegativeVotingConditionedFacet.intrinsicProbability] using hb

/-- At the regular score scale, exact selected masses and the near-regular
Gram bounds imply uniform actual weighted facet degree. -/
theorem selected_segment_degree
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0<e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (i : Fin m) :
    (∑ j∈Finset.univ.erase i,facetWeight (α•R+t•D)
      (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) i j) ≤
      32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e := by
  let B := α•R+t•D
  let h := selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t
  have hg := segment_geometry hm R D hG α hα hD t ht
  have hinj : Function.Injective B := fun i j heq=>by
    by_contra hij
    exact centered_singular_rows_ne B (α/2) (by positivity) hg.1 i j hij heq
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hl : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg hm1
  have hmass : (stdGaussian (FSC.Coord d) (affineCell B h i)).toReal ≤ 1/(m:ℝ) := by
    have hh := congrFun (selected_uniform_mass B hinj) i
    rw [mass_eq_winningCell B hinj] at hh
    simpa only [Measure.real,Fintype.card_fin,one_div,winningCell,affineCell,scores,affineScore,h,selectedRowOffsets,B] using hh.le
  have hh := intrinsicWeightedDegree_uniform_of_gram B h (α/2) α (by positivity) hα
    hg.1 i e m (1+Real.log (m:ℝ)) 1 he hm1 (by linarith) (by linarith)
    (by norm_num) hscale (hg.2.1 i) hg.2.2.1 (fun j hij=>hg.2.2.2.1 j i hij) hmass
  simpa only [intrinsicWeightedDegree,facetWeight,one_mul] using hh

/-- Full actual balanced second-moment comparison in an explicit regular
Frobenius neighborhood. All cell-mass, conditioning, facet-probability,
normal-offset, degree and balanced edge-energy premises are derived. -/
theorem near_regular_selected_moment_difference_sq_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0<e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (v : FSC.Coord d) :
    (∑ i,∑ j,∑ k,
      (secondMomentTensor (α•R+D) (selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹)) i j k-
       secondMomentTensor (α•R) (selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹)) i j k)^2) ≤
      16*(32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)^2*
        (quarticLogConstant 2)^2*(1+Real.log (m:ℝ))^8*∑ i,‖D i-v‖^2 := by
  have hb := selected_uniform_moment_difference_sq_le (α•R) D (α/2) (by positivity)
    (fun t ht=>(segment_geometry hm R D hG α hα hD t ht).1)
    (32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e) (by positivity)
    (fun t ht i j hij=>by
      simpa only [Fintype.card_fin] using
        selected_segment_probability hm R D hG α hα hD t ⟨ht.1,ht.2.le⟩ i j hij)
    (fun t ht i=>by
      simpa only [Fintype.card_fin] using
        selected_segment_degree hm R D hG α hα hD e he hscale t ⟨ht.1,ht.2.le⟩ i) v
  simpa only [Fintype.card_fin] using hb

end NegativeVotingNearRegularBalancedGeometry
