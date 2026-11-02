import GaussianLocalOrbitDeficitPayment
import GaussianCovarianceRadialNormalization
import GaussianRegularScoreProjection
import GaussianSecondEnergyCovarianceLaw

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingNormalizedLocalGeometry
open NegativeVoting NegativeVotingCentroidOptimization NegativeVotingBalancedReference
  NegativeVotingRegularCovarianceDeficit NegativeVotingCovarianceRadialNormalization
  NegativeVotingProcrustes NegativeVotingGlobalCovarianceDeficit
  NegativeVotingRegularScoreProjection NegativeVotingCenteredParseval
  NegativeVotingExteriorRoutingGeometry NegativeVotingExteriorOrbit
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl
  NegativeVotingRayDeficit NegativeVotingExteriorReference NegativeVotingGaussianMaximumSecondMoment
variable {n d e m : ℕ}

lemma row_distance_identity (B U : Fin m→FSC.Coord e) :
    (∑i,‖B i-U i‖^2)= (∑i,‖B i‖^2)+(∑i,‖U i‖^2)-2*(∑i,inner ℝ (B i) (U i)) := by
  simp_rw [norm_sub_sq_real]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]
  ring

lemma row_inner_le (B U : Fin m→FSC.Coord e) :
    (∑i,inner ℝ (B i) (U i)) ≤ Real.sqrt (∑i,‖B i‖^2)*Real.sqrt (∑i,‖U i‖^2) := by
  exact (Finset.sum_le_sum fun i _=>real_inner_le_norm (B i) (U i)).trans
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i=>‖B i‖) (fun i=>‖U i‖))

lemma normalization_error_le_distance (B U : Fin (n+2)→FSC.Coord e)
    (hW : 0 < rowEnergy B) (hU : ScaledRegularGram n U) :
    (∑i,‖normalizedRows n B i-B i‖^2) ≤ rowEnergy (B-U) := by
  rw [normalization_distance B hW]
  have hw := referenceFirstWeight_pos n
  have henergy := scaled_regular_row_energy U hU
  have hdist := row_distance_identity B U
  have hinner := row_inner_le B U
  change rowEnergy (B-U)=rowEnergy B+rowEnergy U-2*(∑i,inner ℝ (B i) (U i)) at hdist
  change (∑i,inner ℝ (B i) (U i)) ≤ Real.sqrt (rowEnergy B)*Real.sqrt (rowEnergy U) at hinner
  rw [henergy] at hdist hinner
  have hscale : radialScale n B=Real.sqrt (rowEnergy B)/Real.sqrt (referenceFirstWeight n) := by
    exact Real.sqrt_div hW.le (referenceFirstWeight n)
  have hsW := Real.sq_sqrt hW.le
  have hsw := Real.sq_sqrt hw.le
  have hsp := Real.sqrt_pos.mpr hw
  rw [hscale]
  have heq : referenceFirstWeight n*(Real.sqrt (rowEnergy B)/Real.sqrt (referenceFirstWeight n)-1)^2=
      rowEnergy B+referenceFirstWeight n-2*Real.sqrt (rowEnergy B)*Real.sqrt (referenceFirstWeight n) := by
    apply (mul_right_cancel₀ (ne_of_gt hw))
    calc
      _ = referenceFirstWeight n*(Real.sqrt (rowEnergy B)-Real.sqrt (referenceFirstWeight n))^2 := by
        field_simp
        nlinarith [hsw]
      _ = _ := by nlinarith [hsW,hsw]
  rw [heq]
  linarith

lemma normalized_distance_le_four (B U : Fin (n+2)→FSC.Coord e)
    (hW : 0 < rowEnergy B) (hU : ScaledRegularGram n U) :
    rowEnergy (normalizedRows n B-U) ≤ 4*rowEnergy (B-U) := by
  have hn := normalization_error_le_distance B U hW hU
  have ht : rowEnergy (normalizedRows n B-U) ≤
      2*(∑i,‖normalizedRows n B i-B i‖^2)+2*rowEnergy (B-U) := by
    simp only [rowEnergy,Pi.sub_apply,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := norm_sub_le (normalizedRows n B i-B i) (U i-B i)
    have he : (normalizedRows n B i-B i)-(U i-B i)=normalizedRows n B i-U i := by abel
    rw [he,norm_sub_rev (U i)] at hh
    nlinarith [norm_nonneg (normalizedRows n B i-U i),sq_nonneg (‖normalizedRows n B i-B i‖-‖B i-U i‖)]
  linarith

lemma regular_analysis_sq_le [NeZero m] (U : Fin m→FSC.Coord e)
    (hG : ∀i j,inner ℝ (U i) (U j)=(if i=j then 1 else 0)-1/(m:ℝ)) (x:FSC.Coord e) :
    (∑i,(inner ℝ (U i) x)^2) ≤ ‖x‖^2 := by
  rw [←frame_norm_sq U hG x]
  exact pow_le_pow_left₀ (norm_nonneg _) (frame_norm_le U hG x) 2

lemma gram_perturbation_sq_le [NeZero m] (U D : Fin m→FSC.Coord e)
    (hG : ∀i j,inner ℝ (U i) (U j)=(if i=j then 1 else 0)-1/(m:ℝ)) :
    (∑i,∑j,(inner ℝ ((U+D) i) ((U+D) j)-inner ℝ (U i) (U j))^2) ≤
      6*(∑i,‖D i‖^2)+3*(∑i,‖D i‖^2)^2 := by
  have hc : (∑i,∑j,(inner ℝ (U i) (D j))^2) ≤ ∑j,‖D j‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _=>regular_analysis_sq_le U hG (D j)
  have hc' : (∑i,∑j,(inner ℝ (D i) (U j))^2) ≤ ∑i,‖D i‖^2 := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [real_inner_comm (D i)] using regular_analysis_sq_le U hG (D i)
  have hd : (∑i,∑j,(inner ℝ (D i) (D j))^2) ≤ (∑i,‖D i‖^2)^2 := by
    calc
      _ ≤ ∑i,∑j,‖D i‖^2*‖D j‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (D i) (D j)) 2
        simpa only [sq_abs,mul_pow] using hh
      _ = _ := by simp only [←Finset.mul_sum,←Finset.sum_mul,pow_two]
  have hp : (∑i,∑j,(inner ℝ ((U+D) i) ((U+D) j)-inner ℝ (U i) (U j))^2) ≤
      3*(∑i,∑j,(inner ℝ (U i) (D j))^2)+
      3*(∑i,∑j,(inner ℝ (D i) (U j))^2)+
      3*(∑i,∑j,(inner ℝ (D i) (D j))^2) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simp only [Pi.add_apply,inner_add_left,inner_add_right]
    nlinarith [sq_nonneg (inner ℝ (U i) (D j)-inner ℝ (D i) (U j)),
      sq_nonneg (inner ℝ (U i) (D j)-inner ℝ (D i) (D j)),
      sq_nonneg (inner ℝ (D i) (U j)-inner ℝ (D i) (D j))]
  linarith


lemma covariance_defect_sq_le_distance
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (B U:Fin (n+2)→FSC.Coord e) (hB:∑i,B i=0) (hU:ScaledRegularGram n U) :
    (operatorHilbertSchmidt (normalizedRowCovariance n b B-
      ContinuousLinearMap.id ℝ (FSC.Coord d)))^2 ≤
      6*(rowEnergy (B-U)/(referenceScale n)^2)+
        3*(rowEnergy (B-U)/(referenceScale n)^2)^2 := by
  let α:=referenceScale n
  have hα:0 < α:=referenceScale_pos n
  let V:Fin (n+2)→FSC.Coord e:=α⁻¹•U
  let D:Fin (n+2)→FSC.Coord e:=α⁻¹•(B-U)
  have hVG:∀i j,inner ℝ (V i) (V j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [V,α,Nat.cast_add,Nat.cast_ofNat] using scaled_regular_normalized_gram U hU
  have hrows:V+D=α⁻¹•B:=by dsimp [V,D];module
  have hsum:(∑i,‖D i‖^2)=rowEnergy (B-U)/α^2:=by
    simp only [D,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      ←Finset.mul_sum,inv_pow]
    unfold rowEnergy
    ring
  have hh:=gram_perturbation_sq_le V D hVG
  rw [hrows,hsum] at hh
  rw [normalized_Gram_defect_identity b hG hP B hB]
  convert hh using 1
  congr 1
  funext i
  congr 1
  funext j
  rw [hVG]
  simp only [Pi.smul_apply,real_inner_smul_left,real_inner_smul_right,Nat.cast_add,Nat.cast_ofNat]
  dsimp [α]
  field_simp


/-- The literal radial normalization of every centered row system in the
2/m regular ball has a small intrinsic covariance, dimension uniformly. -/
theorem eventually_normalized_local_data :
    ∀ᶠ n:ℕ in atTop, ∀(e:ℕ) (B U:Fin (n+2)→FSC.Coord e),
      (∑i,B i)=0 → ScaledRegularGram n U → rowEnergy (B-U) ≤ 4/((n:ℝ)+2)^2 →
      0 < rowEnergy B ∧ 1/2 ≤ radialScale n B ∧
      regularCovarianceDeficit n (normalizedRows n B) ≤ 2*regularCovarianceDeficit n B ∧
      (operatorHilbertSchmidt (normalizedRowCovariance n (referenceBasis n) (normalizedRows n B)-
        ContinuousLinearMap.id ℝ (FSC.Coord (n+2-1))))^2 ≤ 1/1024 ∧
      NegativeVotingFanQuadraticMoments.secondEnergy (normalizedRows n B)
        (NegativeVotingFanSelectedOffsets.selectedOffsets (normalizedRows n B) (uniformMass n))=
      NegativeVotingFanQuadraticMoments.secondEnergy B
        (NegativeVotingFanSelectedOffsets.selectedOffsets B (uniformMass n)) := by
  filter_upwards [eventually_reference_scale_bounds,eventually_gt_atTop (0:ℕ),
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1048576] with n hscale hn hlog
  intro e B U hB hU hF
  simp only [Function.comp_def] at hlog
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  let α:ℝ:=referenceScale n
  have hm:0 < m:=by dsimp [m];positivity
  have hα:0 < α:=referenceScale_pos n
  have hL:1048576 ≤ L:=by dsimp [L,m];linarith
  have hscale':L/m^2 ≤ α^2:=hscale.1
  have hFsmall:rowEnergy (B-U) ≤ α^2/256:=by
    apply hF.trans
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 256)).mpr
    calc
      _ = 1024/m^2:=by dsimp [m];ring
      _ ≤ L/m^2:=div_le_div_of_nonneg_right (by linarith) (sq_nonneg m)
      _ ≤ _:=hscale'
  have hw:0 < referenceFirstWeight n:=referenceFirstWeight_pos n
  have hαw:α^2 ≤ referenceFirstWeight n:=by
    rw [←reference_energy_scale]
    dsimp [α]
    have hn0:0 ≤ (n:ℝ):=Nat.cast_nonneg n
    nlinarith [mul_nonneg (sq_nonneg (referenceScale n)) hn0]
  have hW:0 < rowEnergy B:=by
    by_contra hh
    have hz:rowEnergy B=0:=le_antisymm (le_of_not_gt hh) (rowEnergy_nonneg B)
    have hB0:B=0:=(NegativeVotingCentroidOptimization.rowEnergy_sub_zero_iff B 0).mp (by simpa using hz)
    have he:rowEnergy (B-U)=referenceFirstWeight n:=by
      rw [hB0]
      have he:rowEnergy ((0:Fin (n+2)→FSC.Coord e)-U)=rowEnergy U:=by
        simp only [zero_sub,rowEnergy,Pi.neg_apply,norm_neg]
      rw [he,scaled_regular_row_energy U hU]
    rw [he] at hFsmall
    nlinarith [sq_pos_of_pos hα]
  have hnorm:=normalization_error_le_distance B U hW hU
  rw [normalization_distance B hW] at hnorm
  have hs:1/2 ≤ radialScale n B:=by
    have hh:referenceFirstWeight n*(radialScale n B-1)^2 ≤ referenceFirstWeight n/4:=by linarith
    have hh':(radialScale n B-1)^2 ≤ 1/4:=by nlinarith
    nlinarith
  have hdist:rowEnergy (normalizedRows n B-U) ≤ 16/m^2:=by
    have hh:=normalized_distance_le_four B U hW hU
    have hh':=mul_le_mul_of_nonneg_left hF (by norm_num : (0:ℝ) ≤ 4)
    convert hh.trans hh' using 1 <;> dsimp [m] <;> ring
  have hratio:rowEnergy (normalizedRows n B-U)/α^2 ≤ 1/65536:=by
    calc
      _ ≤ (16/m^2)/α^2:=div_le_div_of_nonneg_right hdist (sq_nonneg α)
      _ ≤ (16/m^2)/(L/m^2):=div_le_div_of_nonneg_left (by positivity) (by positivity) hscale'
      _ = 16/L:=by field_simp
      _ ≤ 1/65536:=(div_le_iff₀ (by positivity : 0 < L)).mpr (by linarith)
  have hb:=referenceBasis_spec n
  have hc:=covariance_defect_sq_le_distance (referenceBasis n) hb.2.1 hb.2.2
    (normalizedRows n B) U (normalizedRows_centered B hB) hU
  have hcsmall:(operatorHilbertSchmidt (normalizedRowCovariance n (referenceBasis n) (normalizedRows n B)-
      ContinuousLinearMap.id ℝ (FSC.Coord (n+2-1))))^2 ≤ 1/1024:=by
    have hrat0:0 ≤ rowEnergy (normalizedRows n B-U)/α^2:=div_nonneg (rowEnergy_nonneg _) (sq_nonneg α)
    have hrat2:=pow_le_pow_left₀ hrat0 hratio 2
    change _ ≤ 6*(rowEnergy (normalizedRows n B-U)/α^2)+3*(rowEnergy (normalizedRows n B-U)/α^2)^2 at hc
    nlinarith only [hc,hratio,hrat2]
  refine ⟨hW,hs,normalizedRows_deficit_le hn B hB hW hs,hcsmall,?_⟩
  let V:Fin (n+2)→FSC.Coord e:=α⁻¹•U
  have hVG:∀i j,inner ℝ (V i) (V j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [V,α,Nat.cast_add,Nat.cast_ofNat] using scaled_regular_normalized_gram U hU
  have hUV:α•V=U:=by dsimp [V];simp [smul_smul,hα.ne']
  have hsing:=NegativeVotingNearRegularBalancedGeometry.singular_of_frobenius_close U (B-U) α hα
    (by rw [←hUV];exact NegativeVotingNearRegularBalancedGeometry.regular_scaled_singular V hVG α)
    (by simpa only [rowEnergy,Pi.sub_apply] using hFsmall) 1 (by norm_num)
  have hsing':NegativeVotingCapTail.CenteredSingularLowerBound B (α/2):=by
    simpa only [one_smul,add_sub_cancel] using hsing
  have he:=NegativeVotingSecondEnergyCovarianceLaw.selected_secondEnergy_scaled B (α/2)
    (by positivity) hsing' (radialScale n B)⁻¹ (inv_pos.mpr (radialScale_pos B hW))
    (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
  exact he

end NegativeVotingNormalizedLocalGeometry
