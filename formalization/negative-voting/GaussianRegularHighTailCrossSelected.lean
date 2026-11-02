import GaussianRegularHighTailCrossPath
import GaussianNearRegularNormalizedBounds

/-! Actual uniformly balanced near-regular specialization of the regular
high-tail cross comparison. All facet probabilities, offsets, degrees and
both path coefficient energies are derived from the row neighborhood. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularHighTailCrossSelected
open NegativeVotingRegularHighTailCrossPath NegativeVotingRegularHighTailCrossAggregation
  NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanScore
  NegativeVotingFanCanonicalOffset NegativeVotingFanJacobian
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularGraphGap
  NegativeVotingNearRegularNormalizedBounds NegativeVotingBalancedOffsetComparison
  NegativeVotingRegularTransportBound NegativeVotingRegularReferenceNormalization
  NegativeVotingPathSmoothedComparison NegativeVotingCapTail NegativeVotingFacetDegree
  NegativeVotingDisintegration NegativeVotingWeightedFacet NegativeVotingPolynomialFacetLogBound
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingBalancedMomentComparison
variable {d m : ℕ} [NeZero m]

theorem scaled_row_energy_le (D : Fin m→FSC.Coord d) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (∑ i,‖(t•D) i‖^2) ≤ ∑ i,‖D i‖^2 := by
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  have hh : 0 ≤ ‖D i‖ := norm_nonneg _
  exact pow_le_pow_left₀ (mul_nonneg ht.1 hh)
    (by simpa using mul_le_mul_of_nonneg_right ht.2 hh) 2

theorem selected_segment_offset_coefficient_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (∑ i,(selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t i)^2) ≤
      offsetCoefficient m α e*∑ i,‖D i‖^2 := by
  have hc : 0 ≤ offsetCoefficient m α e := by
    unfold offsetCoefficient quarticLogConstant
    positivity [degreeBound_pos e he,nearGap_pos (m:=m) α e hα he]
  have hh := selected_offset_sq_le hm R (t•D) hG α hα
    ((scaled_row_energy_le D t ht).trans hD) e he hscale 0
  simp only [sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (scaled_row_energy_le D t ht) hc)

theorem selected_segment_velocity_coefficient_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (∑ i,(canonicalOffsetVariation (α•R+t•D)
      (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) D i)^2) ≤
      offsetCoefficient m α e*∑ i,‖D i‖^2 := by
  have hh := canonicalOffset_norm_sq_log_le (α•R+t•D) D
    (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) (α/2) (by positivity)
    (segment_geometry hm R D hG α hα hD t ht).1
    (nearGap m α e) (nearGap_pos α e hα he)
    (selected_segment_graph_gap hm R D hG α hα hD e he hscale t ht)
    2 (m:ℝ) (degreeBound e) (by exact_mod_cast (show 1 ≤ m by omega))
    (selected_segment_probability hm R D hG α hα hD t ht)
    (by
      intro i j hij
      have ha := selected_endpoint_pairOffset hm R (t•D) hG α hα
        ((scaled_row_energy_le D t ht).trans hD) i j hij
      exact ha)
    (selected_segment_degree_all hm R D hG α hα hD e he hscale t ht) 0
  simpa only [offsetCoefficient,sub_zero] using hh

/-- No geometric or analytic cross-term coefficient is assumed. The explicit
coefficient retains the rare regular-label factor `1/m` and the cubic
high-chaos factor `σ^3`. -/
theorem near_regular_selected_cross_abs_le
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hdim : 2 ≤ Module.finrank ℝ (FSC.Coord d))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (τ σ q : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (hqlog : 4096*Real.log (m:ℝ) ≤ q)
    (hτlog : τ^2*(1+Real.log (m:ℝ)) ≤ 1) :
    |testedFan (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
        (regularTailPotential R τ σ)-
      testedFan (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
        (regularTailPotential R τ σ)| ≤
      32*Real.exp 1*degreeBound e*Real.sqrt (quarticLogConstant 2*(1+Real.log (m:ℝ))^4)*
        ((8*τ*Real.exp 2)*(2*σ^3*(Real.exp 1/(m:ℝ)))/α)*
          (1+offsetCoefficient m α e)*(∑ i,‖D i‖^2) := by
  let p : ℝ→Parameters d (Fin m) := fun t=>
    (α•R+t•D,selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t)
  let p' : ℝ→Parameters d (Fin m) := fun t=>
    (D,canonicalOffsetVariation (p t).1 (p t).2 D)
  let E := (1+offsetCoefficient m α e)*(∑ i,‖D i‖^2)
  have hc : 0 ≤ offsetCoefficient m α e := by
    unfold offsetCoefficient quarticLogConstant
    positivity [degreeBound_pos e he,nearGap_pos (m:=m) α e hα he]
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hL : 0 ≤ 1+Real.log (m:ℝ) := by positivity [Real.log_nonneg hmR]
  have hpos : (0:ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hlower t (ht: t∈Icc (0:ℝ) 1) := (segment_geometry hm R D hG α hα hD t ht).1
  have hp t (ht: t∈Icc (0:ℝ) 1) : HasDerivAt p (p' t) t := by
    have hoff := selectedRowOffsets_hasDerivAt (α•R) D t (α/2) (by positivity) (hlower t ht)
      (fun _=>(m:ℝ)⁻¹) (fun _=>inv_pos.mpr hpos) (by simp [ne_of_gt hpos])
    have hrow : HasDerivAt (fun s:ℝ=>α•R+s•D) D t := by
      simpa using ((hasDerivAt_id t).smul_const D).const_add (α•R)
    exact hrow.prodMk hoff
  have ha t (ht: t∈Icc (0:ℝ) 1) i j (hij:i≠j) :
      |pairOffset (p t).1 (p t).2 i j| ≤ 2*Real.sqrt (1+Real.log (m:ℝ)) :=
    selected_endpoint_pairOffset hm R (t•D) hG α hα ((scaled_row_energy_le D t ht).trans hD) i j hij
  have hnorm t (ht: t∈Icc (0:ℝ) 1) i j (hij:i≠j) :
      quotientNormFactor τ q (pairOffset (p t).1 (p t).2 i j) ≤ 8*τ*Real.exp 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (ha t ht i j hij) 2
    simp only [sq_abs,mul_pow,Real.sq_sqrt hL] at hs
    convert quotientNormFactor_log_le τ q (pairOffset (p t).1 (p t).2 i j)
      2 (1+Real.log (m:ℝ)) hτ hq hL hτlog hs
      using 1 <;> norm_num
  have herr t (ht: t∈Ico (0:ℝ) 1) :
      rowScoreEnergy (fun i=>(p t).1 i-α•R i) (p t).2 0 0 ≤ E := by
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have ho := selected_segment_offset_coefficient_le hm R D hG α hα hD e he hscale t ht'
    have hr := scaled_row_energy_le D t ht'
    have heq : (fun i=>(p t).1 i-α•R i)=t•D := by funext i;dsimp [p];abel
    rw [heq]
    dsimp only [rowScoreEnergy]
    simp only [sub_zero]
    dsimp only [E]
    nlinarith only [hr,ho]
  have hvel t (ht: t∈Ico (0:ℝ) 1) : rowScoreEnergy (p' t).1 (p' t).2 0 0 ≤ E := by
    have ho := selected_segment_velocity_coefficient_le hm R D hG α hα hD e he hscale t ⟨ht.1,ht.2.le⟩
    dsimp only [rowScoreEnergy,p']
    simp only [sub_zero]
    dsimp only [E]
    nlinarith only [ho]
  have hh := regular_path_cross_abs_le p p' hp (α/2) (by positivity) hlower R hG hdim
    α τ σ q 2 1 (8*τ*Real.exp 2) (degreeBound e) E E hα hτ hτ1 hσ hσ1 hq hqt
    (by nlinarith only [hτlog,sq_nonneg τ]) (by positivity) (degreeBound_pos e he).le hE hE
    (fun t ht i=>selected_segment_degree_all hm R D hG α hα hD e he hscale t ht i)
    (fun t ht=>selected_segment_probability hm R D hG α hα hD t ht)
    (fun t ht i j hij=>probability_log_le_of_power _ (m:ℝ) q hmR
      (selected_segment_probability hm R D hG α hα hD t ht i j hij) hqlog)
    ha hnorm (fun _=>0) (fun _=>0) (fun _=>0) (fun _=>0) herr hvel
  have hs : Real.sqrt E*Real.sqrt E=E := Real.mul_self_sqrt hE
  simp only [mul_assoc] at hh
  rw [hs] at hh
  simpa only [p,selectedRowOffsets,zero_smul,one_smul,add_zero,E,mul_assoc] using hh

end NegativeVotingRegularHighTailCrossSelected
